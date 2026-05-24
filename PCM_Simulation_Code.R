ptm <- proc.time()
# Needed libraries
library(survival)
library(MASS)
library(e1071)
library(pROC)
library(caTools)
library(rpart)
library(neuralnet)
library(randomForest)
library(xgboost)
library(splines)



.eps <- 1e-9

smsurv <- function(Time, Status, X, beta, w, model) {
  death_point <- sort(unique(subset(Time, Status == 1)))
  
  # Handle case with no death points
  if (length(death_point) == 0) {
    return(list(survival = rep(1, length(Time))))
  }
  
  # Ensure beta has the correct length
  if(is.null(beta) || length(beta) < (ncol(X) - 1)) {
    beta <- c(beta, rep(0, (ncol(X) - 1) - length(beta)))
  }
  
  if (model == 'ph') coxexp <- exp(beta %*% t(X[, -1, drop = FALSE]))
  
  lambda <- numeric()
  event <- numeric()
  
  for (i in 1:length(death_point)) {
    event[i] <- sum(Status * as.numeric(Time == death_point[i]))
    if (model == 'ph') temp <- sum(as.numeric(Time >= death_point[i]) * w * drop(coxexp))
    if (model == 'aft') temp <- sum(as.numeric(Time >= death_point[i]) * w)
    
    # Avoid division by zero
    if (!is.na(temp) && temp > .eps) {
      lambda[i] <- event[i] / temp
    } else {
      lambda[i] <- 0
    }
  }
  
  
  
  HHazard <- sapply(Time, function(t) {
    if (t < min(death_point)) return(0)
    if (t > max(death_point)) return(Inf)
    sum(lambda[death_point <= t])
  })
  
  
  
  survival <- exp(-HHazard)
  survival <- pmin(pmax(survival, .eps), 1 - .eps)      # Clamp survival probabilities to a safe range [eps, 1-eps]
  return(list(survival = survival))
}

# data.Pois function
data.Pois <- function(n, alpha, beta, delta, setting) {
  n_betas_needed <- ifelse(setting %in% 1:2, 2, 10)
  beta <- c(beta, rep(0, max(0, n_betas_needed - length(beta))))[1:n_betas_needed]
  
  # Generate Z covariates
  if (setting == 3) {
    p <- 10
    Sigma <- matrix(0, nrow = p, ncol = p)
    for (i in 1:p) for (j in 1:p) Sigma[i, j] <- 0.8^abs(i - j)
    Z <- mvrnorm(n = n, mu = rep(0, p), Sigma = Sigma)
    Z <- as.data.frame(Z)
    names(Z) <- paste0("z", 1:10)
  } else {
    Z <- data.frame(z1 = rnorm(n), z2 = rnorm(n))
  }
  
  
  
  z <- as.matrix(Z)
  piz = rep(NA,n)  # this is the uncured probability pi(z)
  # Calculate uncured probability (pi(z))
  if(setting==1){
    piz = (exp(0.3-(5*Z$z1)-(3*Z$z2)))/(1+exp(0.3-(5*Z$z1)-(3*Z$z2)))
  }
  
  if(setting==2){
    piz = (exp(0.5+(4*Z$z1*Z$z1)-(2*Z$z2*Z$z2))/(1+exp(0.5+(4*Z$z1*Z$z1)-(2*Z$z2*Z$z2))))
  }
  
  #if(setting==3){
  # piz = exp(-exp(0.3-(5*cos(Z$z1))-(3*sin(Z$z2))))
  
  #} 
  
  if (setting == 3) {
    piz <- exp(-exp(
      (-0.8 * (Z$z1 * Z$z2)) + (1.1 * (Z$z2 * Z$z4)) + (0.5 * Z$z3) + (0.2 * ((Z$z7)^2)) - (1.3 * sin(Z$z5 * Z$z6)) +
        (1.9 * cos(Z$z7 * Z$z8)) - (1.5 * exp(Z$z5 * Z$z6 * Z$z7)) - (1.6 * Z$z7 * Z$z8 * Z$z9 * Z$z10) +
        (0.8 * Z$z6 * Z$z7 * ((Z$z8)^2) * ((Z$z9)^2)) + (1.8^cos(Z$z5 * Z$z6 * Z$z7 * Z$z8 * Z$z9)) +
        (1.2 * (abs(Z$z6 * Z$z7 * Z$z8 * Z$z9 * Z$z10)^0.5)) - 1.2
    ))
  } 
  piz[piz==0] = .Machine$double.eps
  
  if (setting == 3) {
    x <- as.matrix(Z[, 1:5])
    eta <- x %*% beta[1:5]
  } else {
    eta <- z %*% beta
  }
  
  eta <- pmin(pmax(eta, -20), 20) # Clamp eta to prevent extreme values in exp(eta)
  # Simulate survival times
  C = rexp(n,rate=delta) # censoring times
  U = runif(n,0,1) # event times
  Y = rep(NA,n)
  D = rep(NA,n)
  J = rep(NA,n)
  Sp = rep(NA,n) # overall survival function
  S1 = rep(NA,n) # susceptible survival function
  S = rep(NA,n) # survival function of the promotion times
  J  <- as.integer(U > (1 - piz))
  
  
  T1 <- rep(Inf, n)
  idxS <- which(J == 1)
  if (length(idxS) > 0) {
    U1 <- runif(length(idxS), min = 1 - piz[idxS], max = 1)   # your original mapping
    scale_weib <- (exp(eta[idxS]))^(-1/alpha)
    T1[idxS] <- stats::qweibull((log(U1) / log(1 - piz[idxS])), shape = alpha, scale = scale_weib)
  }
  
 
  scale_all <- (exp(eta))^(-1/alpha)
  Ustar     <- runif(n)                                  # independent of J
  T_star    <- stats::qweibull(Ustar, shape = alpha, scale = scale_all)
  
  # Choose tau as a fixed quantile of the marginal T* (same for everyone)
  q_admin <- 0.90         # median gives ~50% admin censoring among susceptibles
  tau     <- as.numeric(stats::quantile(T_star, probs = q_admin, names = FALSE))
  
  # Single, common, non-informative censoring distribution for all subjects
  C <- stats::runif(n, min = 0, max = tau)
  
  # --- observed time and status (unchanged logic) ---
  Y <- ifelse(J == 1, pmin(C, T1), C)
  D <- ifelse(J == 1 & (T1 <= C), 1, 0)
  
  
  Sp = (1-piz)^(1-exp(-((Y/((exp(eta)^(-1/alpha)))^alpha))))
  S1 = (Sp-(1-piz))/pmax(piz, 1e-9)
  S = exp(-((Y/((exp(eta)^(-1/alpha)))^alpha)))
  
  return(data.frame(Y, D, Z, J, uncure = piz, S1, Sp, S))
}

#LOGIT
em.logit.Pois <- function(Time, Status, Time1, Status1,
                          X, X1, Z, Z1,
                          b, beta, s0, s01,
                          emmax, eps) {
  
  n <- length(Status)
  s <- s0
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    
    uncureprob <- as.vector(plogis(Z %*% b))
    uncurepred <- as.vector(plogis(Z1 %*% b))
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival<-drop(s^(exp((X[, -1, drop = FALSE]%*%(beta))))) # survival function of the progression times
    survival1<-drop(s1^(exp(X1[, -1, drop = FALSE]%*%(beta))))
    
    uncureprob_safe <- pmin(pmax(uncureprob, 1e-9), 1-1e-9)
   
    M <- Status - (survival * log(pmax(1 - uncureprob, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - uncurepred, 1e-6)))
    
    Q1 <- function(par) {
      bb <- par
      uncure1 <- matrix(exp((bb)%*%t(Z))/(1+exp((bb)%*%t(Z))),ncol=1)
      loglik <- sum(M*log(-log(1-uncure1))) + sum(log(1-uncure1))
      return(-loglik)
    }
    
    update_b <- try(optim(par = b, fn = Q1, method = "Nelder-Mead")$par, silent = TRUE)
    if (inherits(update_b, "try-error")) {
      warning("Optimization for b failed. Using previous values.")
      
    }
    
    # Using a local dataframe to ensure 'offset' and 'subset' align correctly with matrices
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-8)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(logM)"))
    
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    if (!inherits(cox_fit, "try-error")) {
      update_beta <- as.numeric(cox_fit$coefficients)
    } else {
      update_beta <- beta
    }
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    convergence <- sum(c(update_b-b,update_beta-beta,mean(update_s)-mean(s))^2) #If the parameters haven’t changed much, we stop.
    
    b <- update_b
    beta <- update_beta
    s <- update_s
    s1 <- update_s1
    
    i <- i + 1
  }
  
  eta  <- as.vector(X[, -1, drop = FALSE] %*% beta)
  eta1 <- as.vector(X1[, -1, drop = FALSE] %*% beta)
  
  final_survival  <- drop(s ^ exp(eta))
  final_survival1 <- drop(s1 ^ exp(eta1))
  
  UN <- as.vector(plogis(Z %*% b))
  PRED <- as.vector(plogis(Z1 %*% b))
  
  Sp = (1 - UN)^(1 - final_survival)
  Sp.pred = (1 - PRED)^(1 - final_survival1)
  S1 = (Sp - (1 - UN)) / pmax(UN, 1e-9)
  S1.pred = (Sp.pred - (1 - PRED)) / pmax(PRED, 1e-9)
  
  return(list(b = b,
              latencyfit = beta,
              UN = UN,
              PRED = PRED,
              Sp = Sp,
              Sp.pred = Sp.pred,
              S1 = S1,
              S1.pred = S1.pred,
              s0 = s,
              s01 = s1,
              S = final_survival,
              S.pred = final_survival1,
              tau = convergence))
  
  
}

smcure.logit.Pois <- function(setting = NULL, formula = NULL, cureform = NULL,
                              offset = NULL, data, testdata,
                              na.action = na.omit, Var = T,
                              emmax = 1000, eps = 1e-3, nboot = 100) {
  call <- match.call()
  
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  
  
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  if (!inherits(Y, "Surv")) stop("Response must be a survival object")
  
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  
  Z <- model.matrix(cureform, data)
  Z1 <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, nb)
  beta <- rep(0.5, nbeta)
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  out.data <- basehaz(coxfit_train, centered = FALSE)
  S0_grid <- exp(-out.data$hazard)
  t_grid  <- out.data$time
  
  idx_tr <- pmax(1, findInterval(Time, t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid))
  
  s0_init  <- S0_grid[idx_tr]
  s01_init <- S0_grid[idx_te]
  
  emfit <- em.logit.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1, b, beta, s0_init, s01_init, emmax, eps)
  
  beta.est <- emfit$latencyfit
  b.est <- emfit$b
  UN <- emfit$UN
  PRED <- emfit$PRED
  
  if (Var) {
    n <- nrow(data)
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (i in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Correctly resample s0 to match bootstrapped observations
      s0_b <- s0_init[boot_idx]
      
      bootfit <- try(em.logit.Pois(
        Y_b[, 1], Y_b[, 2], Time1, Status1,
        X_b, X1, Z_b, Z1,
        b.est, beta.est,
        s0_b, s01_init,
        emmax, eps
      ), silent = TRUE)
      
      if (!inherits(bootfit, "try-error")) {
        latency_boot[i, ] <- bootfit$latencyfit
        uncure_boot[i, ] <- as.vector(bootfit$UN)
      }
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    lower_uncure <- pmax(0, as.vector(UN) - 1.96 * uncure_sd)
    upper_uncure <- pmin(1, as.vector(UN) + 1.96 * uncure_sd)
  }
  
  fit <- list()
  class(fit) <- c("smcure.logit.Pois")
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure <- lower_uncure
    fit$upper_uncure <- upper_uncure
  }
  
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN <- UN
  fit$PRED <- PRED
  fit$b <- b.est
  fit$Sp <- emfit$Sp
  fit$Sp.pred <- emfit$Sp.pred
  fit$S1 <- emfit$S1
  fit$S1.pred <- emfit$S1.pred
  fit$s0 <- emfit$s0
  fit$s01 <- emfit$s01
  fit$S <- emfit$S
  fit$S.pred <- emfit$S.pred
  fit$tau <- emfit$tau
  
  return(fit)
}














# SUPPORT VECTOR MACHINE
em.svm.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,uncureprob, uncurepred,
                        b, beta, s0, s01, 
                        emmax, eps, best_params) { 
  n <- length(Status)
  m <- length(Status1)
  
  s <- s0
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps & i <= emmax) {
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    UN   <- as.numeric(uncureprob)
    PRED <- as.numeric(uncurepred)
    
    # clamp
    UN   <- pmin(pmax(UN, 1e-9), 1 - 1e-9)
    PRED <- pmin(pmax(PRED, 1e-9), 1 - 1e-9)
    
    
    survival<-drop(s^(exp((X[, -1, drop = FALSE]%*%(beta))))) # survival function of the progression times
    survival1<-drop(s1^(exp(X1[, -1, drop = FALSE]%*%(beta))))
    
    # uncureprob_safe <- pmin(pmax(uncureprob, 1e-9), 1-1e-9)
    w <- Status + (1-Status)*(1-((1-UN)^(survival)))
    
    # Corrected M and M1 calculations
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    K <- 5
    # Ensure V_matrix is correctly sized for n
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w, each = K)), nrow = n, byrow = TRUE)
    V_matrix <- V_matrix * 2 - 1
    
    cure_preds <- matrix(NA, nrow = n, ncol = K)
    pred_preds <- matrix(NA, nrow = m, ncol = K)
    
    for (k in 1:K) {
      yk <- as.factor(V_matrix[, k])
      
      if (length(levels(yk)) < 2) {
        # Fill based on single level present
        val <- if(levels(yk)[1] == "1") 1 else 0
        cure_preds[, k] <- val
        pred_preds[, k] <- val
        next
      }
      
      # SVM fitting on scaled covariates Z (training)
      mod <- svm(Z[, -1, drop = FALSE], yk, gamma = best_params$gamma, cost = best_params$cost, probability = TRUE)
      
      probs_train <- attr(predict(mod, Z[, -1, drop = FALSE], probability = TRUE), "probabilities")
      probs_test <- attr(predict(mod, Z1[, -1, drop = FALSE], probability = TRUE), "probabilities")
      
      if ("1" %in% colnames(probs_train)) {
        cure_preds[, k] <- probs_train[, "1"]
      } else {
        cure_preds[, k] <- 0 
      }
      
      if ("1" %in% colnames(probs_test)) {
        pred_preds[, k] <- probs_test[, "1"]
      } else {
        pred_preds[, k] <- 0
      }
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred <- rowMeans(pred_preds, na.rm = TRUE)
    
    
    
    
    
    # M-step for beta using training weights M
    cox_fit <- coxph(Surv(Time, Status) ~ X[, -1, drop = FALSE] + offset(log(pmax(M, 1e-6))),  subset = M != 0,method = "breslow")
    
    update_beta <- cox_fit$coefficients
    
    # Update baseline survival for both train and test
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    # Fix convergence check dimensions
    convergence <- sum(c(update_beta - beta, mean(update_s) - mean(s))^2)
    
    
    UN <- update_cureb
    PRED <- update_pred
    beta <- update_beta
    s <- update_s
    s1 <- update_s1
    
    
    i <- i + 1
  }
  
  eta  <- as.vector(X[, -1, drop = FALSE]  %*% beta)
  eta1 <- as.vector(X1[, -1, drop = FALSE] %*% beta)
  
  survival  <- drop(s  ^ exp(eta))
  survival1 <- drop(s1 ^ exp(eta1))
  
  
  Sp = (1-UN)^(1-survival) # survival prob. of the population
  Sp.pred = (1-PRED)^(1-survival1) 
  S1 = (Sp-(1-UN))/UN # survival prob. of the susceptible group
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  
  
  em.svm.Pois <-list(latencyfit = beta,b = b, UN = UN,PRED = PRED,
                     Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = survival1,
                     s0 = s, S = survival, tau = convergence,
                     gam = best_params$gamma, cost = best_params$cost, iterations = i)
}


smcure.svm.Pois <- function(setting = NULL, formula, cureform, offset = NULL, data, testdata,
                            na.action = na.omit, Var = T, emmax = 1000, eps = 1e-3, nboot = 100) {
  
  call <- match.call()
  
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  
  
  
  n <- dim(data)[1] 
  m <- dim(testdata)[1]
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  if (!inherits(Y, "Surv")) stop("Response must be a survival object")
  
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  
  Z <- model.matrix(cureform, data)
  Z1 <- model.matrix(cureform, testdata)
  Z_matrix =Z
  
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, ncol(Z))
  beta <- rep(0.5, nbeta)
  
  # --- SVM Hyperparameter Tuning (using original Status as proxy labels) ----
  w <- Status
  nw <- as.factor(w * 2 - 1)
  
  Z_scaled_values <- scale(Z[, -1, drop = FALSE])
  Z_scaled_df <- as.data.frame(Z_scaled_values)
  
  center_vals <- attr(Z_scaled_values, "scaled:center")
  scale_vals <- attr(Z_scaled_values, "scaled:scale")
  
  Z1_scaled_df <- as.data.frame(scale(Z1[, -1, drop = FALSE], center = center_vals, scale = scale_vals))
  
  tune_data <- cbind(nw, Z_scaled_df)
  
  obj <- tune(svm, nw ~ ., data = tune_data, 
              ranges = list(
                gamma = 10^(-6:-4), 
                cost = 10^(4:6)   
              ), 
              tunecontrol = tune.control(sampling = "cross", cross = 10))
  best_params <- obj$best.parameters
  
  # --- More robust GLM-based initialization for starting probabilities ---
  # Using GLM on Status provides a better starting point for the EM algorithm.
  glm_data_train <- data.frame(Status = Status, Z[, -1, drop = FALSE])
  glm_init <- tryCatch(
    glm(Status ~ ., data = glm_data_train, family = binomial()),
    error = function(e) { NULL }
  )
  
  if (is.null(glm_init)) {
    # Fallback if GLM fails
    uncureprob <- rep(mean(Status), n)
    uncurepred <- rep(mean(Status), m)
  } else {
    uncureprob <- predict(glm_init, type = "response")
    uncurepred <- predict(glm_init, newdata = data.frame(Z1[, -1, drop = FALSE]), type = "response")
  }
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data$hazard)
  t_grid  <- out.data$time
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1$hazard)
  t_grid1  <- out.data1$time
  
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  
  s0  <- S0_grid[idx_tr]   # length(Time)
  s01 <- S01_grid[idx_te]   # length(Time1)
  
  if(any(is.na(s0))) s0[is.na(s0)] <- min(s0, na.rm = TRUE)
  if(any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  
  emfit <- em.svm.Pois(
    Time = Time, Status = Status,
    Time1 = Time1, Status1 = Status1,
    X = X, X1 = X1,
    Z = Z, Z1 = Z1,uncureprob = uncureprob,
    uncurepred = uncurepred,
    b = b, beta = beta,
    s0 = s0, s01 = s01,
    emmax = emmax, eps = eps,
    best_params = best_params
  )
  
  beta.est = emfit$latencyfit
  b.est = emfit$b
  UN<-emfit$UN
  PRED<-emfit$PRED
  Sp = emfit$Sp
  Sp.pred = emfit$Sp.pred
  S1 = emfit$S1
  S1.pred = emfit$S1.pred
  s0 = emfit$s0
  s01 = emfit$s01
  S = emfit$S
  S.pred = emfit$S.pred
  conv = emfit$tau
  
  if (Var) {
    # --- Bootstrap for latency coefficients and uncure probabilities (SVM EM) ---
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    # Stratified bootstrap indices on TRAIN
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (i in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      
      # Rebuild TRAIN design matrices from the same formulas
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      if (!inherits(Y_b, "Surv")) stop("Response must be a survival object")
      
      Time_b   <- Y_b[, 1]
      Status_b <- Y_b[, 2]
      
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Recompute baseline survival for bootstrap TRAIN at bootstrap times
      coxfit_b  <- coxph(Surv(Time_b, Status_b) ~ 1)
      s0_fit_b  <- survfit(coxfit_b)
      s0_b      <- summary(s0_fit_b, times = Time_b, extend = TRUE)$surv
      if (any(is.na(s0_b))) s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      
      # Initialize uncure probs for the bootstrap EM (GLM fallback)
      glm_b <- tryCatch(
        glm(Status_b ~ ., data = data.frame(Status_b = Status_b, Z_b[, -1, drop = FALSE]), family = binomial()),
        error = function(e) NULL
      )
      
      if (is.null(glm_b)) {
        uncure_b0 <- rep(mean(Status_b), length(Status_b))
        uncure_10 <- rep(mean(Status_b), m)
      } else {
        uncure_b0 <- as.numeric(predict(glm_b, type = "response"))
        uncure_10 <- as.numeric(predict(glm_b, newdata = data.frame(Z1[, -1, drop = FALSE]), type = "response"))
      }
      
      # Fit EM on bootstrap TRAIN; keep TEST fixed
      bootfit <- em.svm.Pois(
        Time_b, Status_b, Time1, Status1,
        X_b, X1, Z_b, Z1,
        uncure_b0, uncure_10,
        b.est, beta.est,
        s0 = s0_b, s01 = s01,
        emmax, eps,
        best_params 
      )
      
      latency_boot[i, ] <- bootfit$latencyfit
      # NOTE: length is n (same as bootstrap TRAIN size)
      uncure_boot[i, ]  <- as.numeric(bootfit$UN)
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    lower_uncure <- as.numeric(emfit$UN) - 1.96 * uncure_sd
    upper_uncure <- as.numeric(emfit$UN) + 1.96 * uncure_sd
    
    # clamp to [0, 1]
    lower_uncure <- pmax(0, lower_uncure)
    upper_uncure <- pmin(1, upper_uncure)
  }
  fit<-list()
  class(fit) <- c("smcure.svm.Pois")
  
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure}
  cat(" done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  fit$b <- b.est
  fit$Sp = Sp
  fit$Sp.pred = Sp.pred
  fit$S1 = S1
  fit$S1.pred = S1.pred
  fit$s0 = s0
  fit$s01 = s01
  fit$S = S
  fit$S.pred = S.pred
  fit$tau = conv
  fit
  return(emfit)
}










# DECISION TREE
em.dt.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                       uncureprob, uncurepred, beta, s0, s01,
                       emmax, eps, best_params) { 
  n <- length(Status)
  m <- length(Status1)
  
  s <- s0
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps & i <= emmax) {
    
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival<-drop(s^(exp((X[, -1, drop = FALSE]%*%(beta))))) # survival function of the progression times
    survival1<-drop(s1^(exp(X1[, -1, drop = FALSE]%*%(beta))))
    
    # Decision tree incidence: use current probability vectors (initialized in wrapper)
    UN   <- pmin(pmax(as.numeric(uncureprob), 1e-9), 1 - 1e-9)
    PRED <- pmin(pmax(as.numeric(uncurepred), 1e-9), 1 - 1e-9)
    
    
    
    
    w <- Status + (1-Status)*(1-((1-UN)^(survival))) 
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w, each = K)), nrow = n, byrow = TRUE)
    
    cure_preds <- matrix(NA, nrow = n, ncol = K)
    pred_preds <- matrix(NA, nrow = length(Status1), ncol = K)
    
    for (k in 1:K) {
      yk <- as.factor(V_matrix[, k])
      yk <- factor(V_matrix[, k], levels = c(0,1), labels = c("cured","uncured"))
      
      mod_data <- data.frame(Z[, -1, drop = FALSE])
      mod_data$yk <- yk
      
      mod <- rpart(yk ~ ., data = mod_data, method = "class", control = rpart.control(cp = best_params$cp))
      
      probs_train <- predict(mod, newdata = as.data.frame(Z[, -1, drop = FALSE]), type = "prob")
      probs_test <- predict(mod, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")
      
      cure_preds[, k] <- probs_train[, "uncured"]
      pred_preds[, k] <- probs_test[, "uncured"]
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred  <- rowMeans(pred_preds, na.rm = TRUE)
    if (all(is.na(update_cureb))) update_cureb <- uncureprob
    if (all(is.na(update_pred)))  update_pred  <- uncurepred
    update_cureb <- pmin(pmax(update_cureb, 1e-6), 1 - 1e-6)
    update_pred  <- pmin(pmax(update_pred,  1e-6), 1 - 1e-6)
    
    # Using a local dataframe to ensure 'offset' and 'subset' align correctly with matrices
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-8)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(logM)"))
    
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    if (!inherits(cox_fit, "try-error")) {
      update_beta <- as.numeric(cox_fit$coefficients)
    } else {
      update_beta <- beta
    }
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    convergence <- sum(c(update_beta-beta,mean(update_cureb)-mean(uncureprob),mean(update_s)-mean(s))^2)
    
    UN <- update_cureb
    PRED <- update_pred
    beta <- update_beta 
    s <- update_s
    s1 <- update_s1
    
    i <- i + 1
  }
  
  
  eta  <- as.vector(X[, -1, drop = FALSE]  %*% beta)
  eta1 <- as.vector(X1[, -1, drop = FALSE] %*% beta)
  
  survival  <- drop(s  ^ exp(eta))
  survival1 <- drop(s1 ^ exp(eta1))
  
  Sp = (1-UN)^(1-survival) # survival prob. of the population
  Sp.pred = (1-PRED)^(1-survival1) 
  S1 = (Sp-(1-UN))/UN # survival prob. of the susceptible group
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  em.dt.Pois <-list(latencyfit = beta, UN = UN,PRED = PRED,
                    Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = survival1,
                    s0 = s, S = survival, tau = convergence, cp = best_params$cp)
  
  
  
}

smcure.dt.Pois <- function(setting = NULL, formula, cureform, offset = NULL, data, testdata,
                           na.action = na.omit, Var =F, emmax = 1000, eps = 1e-3, nboot = 100) {
  call <- match.call()
  
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  
  
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  if (!inherits(Y, "Surv")) stop("Response must be a survival object")
  
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  
  Z <- model.matrix(cureform, data)
  Z1 <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, ncol(Z))
  beta <- rep(0.5, nbeta)
  
  # --- Pre-tuning of Decision Tree (pure rpart, 10-fold CV; no caret) ---
  nw <- factor(Status, levels = c(0,1), labels = c("cured","uncured"))
  Zdt <- as.data.frame(Z[, -1, drop = FALSE])
  K <- 10; set.seed(1)
  pos <- which(nw == "uncured"); neg <- which(nw == "cured")
  fpos <- split(sample(pos), rep(1:K, length.out = length(pos)))
  fneg <- split(sample(neg), rep(1:K, length.out = length(neg)))
  folds <- lapply(1:K, function(k) sort(c(fpos[[k]], fneg[[k]])))
  auc_fast <- function(y, p){ y <- as.integer(y=="uncured"); n1<-sum(y==1); n0<-sum(y==0); if(n1==0||n0==0) return(NA_real_); r<-rank(p,ties.method="average"); (sum(r[y==1]) - n1*(n1+1)/2)/(n1*n0) }
  cp_grid <- c(0.001, 0.01, 0.05, 0.1)
  aucs <- rep(NA_real_, length(cp_grid))
  for (i_cp in seq_along(cp_grid)){
    y_all <- c(); p_all <- c()
    for (k in 1:K){
      vl <- folds[[k]]; tr <- setdiff(seq_len(nrow(Zdt)), vl)
      if (length(unique(nw[tr]))<2 || length(unique(nw[vl]))<2) next
      fit <- try(rpart::rpart(nw ~ ., data = data.frame(Zdt, nw = nw)[tr,], method = "class", control = rpart::rpart.control(cp = cp_grid[i_cp])), silent = TRUE)
      if (inherits(fit, "try-error")) next
      pv <- try(predict(fit, newdata = Zdt[vl, , drop = FALSE], type = "prob")[, "uncured"], silent = TRUE)
      if (inherits(pv, "try-error")) next
      y_all <- c(y_all, nw[vl]); p_all <- c(p_all, pv)
    }
    aucs[i_cp] <- if (length(y_all)>1) auc_fast(y_all, p_all) else NA_real_
  }
  best_cp <- if (all(is.na(aucs))) 0.01 else cp_grid[which.max(aucs)]
  best_params <- list(cp = best_cp)
  
  initial_mod <- rpart::rpart(nw ~ ., data = data.frame(Zdt, nw = nw), method = "class", control = rpart::rpart.control(cp = best_params$cp))
  
  uncureprob <- predict(initial_mod, newdata = as.data.frame(Z[, -1, drop = FALSE]), type = "prob")[, "uncured"]
  uncurepred <- predict(initial_mod, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")[, "uncured"]
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  
  
  
  
  
  # Proper baseline survival initialization using stepfun
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  out.data <- basehaz(coxfit_train, centered = FALSE)
  s0_init <- stepfun(out.data$time, c(1, exp(-out.data$hazard)))(Time)
  
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  out.data1 <- basehaz(coxfit_test, centered = FALSE)
  s01_init <- stepfun(out.data1$time, c(1, exp(-out.data1$hazard)))(Time1)
  
  emfit <- em.dt.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1,
                      uncureprob, uncurepred, beta = rep(0, nbeta),
                      s0 = s0_init, s01 = s01_init, emmax = emmax, eps = eps,
                      best_params = best_params)
  
  
  
  
  beta.est = emfit$latencyfit
  #b.est = emfit$b
  UN<-emfit$UN
  PRED<-emfit$PRED
  Sp = emfit$Sp
  Sp.pred = emfit$Sp.pred
  S1 = emfit$S1
  S1.pred = emfit$S1.pred
  s0 = emfit$s0
  s01 = emfit$s01
  S = emfit$S
  S.pred = emfit$S.pred
  conv = emfit$tau
  
  
  if (Var) {
    # --- Bootstrap for latency coefficients and uncure probabilities (DT EM) ---
    n <- length(Status)
    
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    # Stratified bootstrap indices on TRAIN
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (i in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      
      # Rebuild TRAIN design matrices from the same formulas
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      if (!inherits(Y_b, "Surv")) stop("Response must be a survival object")
      
      Time_b   <- Y_b[, 1]
      Status_b <- Y_b[, 2]
      
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Refit initial DT on bootstrap TRAIN to initialize uncure probs
      nw_b  <- factor(Status_b, levels = c(0,1), labels = c("cured","uncured"))
      Zdt_b <- as.data.frame(Z_b[, -1, drop = FALSE])
      
      init_mod_b <- try(
        rpart::rpart(nw_b ~ ., data = data.frame(Zdt_b, nw_b = nw_b), method = "class",
                     control = rpart::rpart.control(cp = best_params$cp)),
        silent = TRUE
      )
      
      if (inherits(init_mod_b, "try-error")) {
        uncureprob_b <- rep(mean(Status_b), length(Status_b))
        uncurepred_b <- rep(mean(Status_b), length(Status1))
      } else {
        pr_tr <- try(predict(init_mod_b, newdata = as.data.frame(Z_b[, -1, drop = FALSE]), type = "prob"), silent = TRUE)
        pr_te <- try(predict(init_mod_b, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob"), silent = TRUE)
        
        if (inherits(pr_tr, "try-error") || is.null(pr_tr)) {
          uncureprob_b <- rep(mean(Status_b), length(Status_b))
        } else {
          uncureprob_b <- pr_tr[, "uncured"]
        }
        
        if (inherits(pr_te, "try-error") || is.null(pr_te)) {
          uncurepred_b <- rep(mean(Status_b), length(Status1))
        } else {
          uncurepred_b <- pr_te[, "uncured"]
        }
      }
      
      uncureprob_b <- pmin(pmax(uncureprob_b, 1e-6), 1 - 1e-6)
      uncurepred_b <- pmin(pmax(uncurepred_b, 1e-6), 1 - 1e-6)
      
      # Baseline survival init (keep your basehaz style)
      coxfit_b <- coxph(Surv(Time_b, Status_b) ~ 1)
      out_b    <- basehaz(coxfit_b)
      s0_b     <- exp(-out_b[, 1])
      
      # Fit EM on bootstrap TRAIN; keep TEST fixed
      bootfit <- em.dt.Pois(
        Time_b, Status_b, Time1, Status1,
        X_b, X1, Z_b, Z1,
        uncureprob_b, uncurepred_b,
        beta = emfit$latencyfit,
        s0 = s0_b, s01 = s01,
        emmax = emmax, eps = eps,
        best_params = best_params
      )
      
      latency_boot[i, ] <- bootfit$latencyfit
      uncure_boot[i, ]  <- as.numeric(bootfit$UN)
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    lower_uncure <- as.numeric(emfit$UN) - 1.96 * uncure_sd
    upper_uncure <- as.numeric(emfit$UN) + 1.96 * uncure_sd
    
    # clamp to [0, 1]
    lower_uncure <- pmax(0, lower_uncure)
    upper_uncure <- pmin(1, upper_uncure)
  }
  fit<-list()
  class(fit) <- c("smcure.dt.Pois")
  
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure}
  cat(" done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  #fit$b <- b.est
  fit$Sp = Sp
  fit$Sp.pred = Sp.pred
  fit$S1 = S1
  fit$S1.pred = S1.pred
  fit$s0 = s0
  fit$s01 = s01
  fit$S = S
  fit$S.pred = S.pred
  fit$tau = conv
  fit
  return(fit)
}







# RANDOM FOREST (RF)
em.rf.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                       uncureprob, uncurepred, beta, s0, s01,
                       emmax, eps, best_params) { 
  n <- length(Status)
  m <- length(Status1)
  
  s <- s0
  # test-side baseline handled after EM using TRAIN baseline only (no leakage)
  s1 <- s01
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps & i <= emmax) {
    
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival<-drop(s^(exp((X[, -1, drop = FALSE]%*%(beta))))) # survival function of the progression times
    survival1<-drop(s1^(exp(X1[, -1, drop = FALSE]%*%(beta))))
    
    # Decision tree incidence: use current probability vectors (initialized in wrapper)
    UN   <- pmin(pmax(as.numeric(uncureprob), 1e-9), 1 - 1e-9)
    PRED <- pmin(pmax(as.numeric(uncurepred), 1e-9), 1 - 1e-9)
    
    
    
    
    w <- Status + (1-Status)*(1-((1-UN)^(survival))) 
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    # no test-side M1 inside EM
    
    K <- 5
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w, each = K)), nrow = n, byrow = TRUE)
    
    cure_preds <- matrix(NA_real_, nrow = n,               ncol = K)
    pred_preds <- matrix(NA_real_, nrow = length(Status1), ncol = K)
    
    for (k in 1:K) {
      yk <- factor(V_matrix[, k], levels = c(0, 1), labels = c("cured", "uncured"))
      mod_data <- data.frame(Z[, -1, drop = FALSE])
      mod_data$yk <- yk
      
      # stratified subsampling to reduce memorization
      cls_k <- table(yk)
      ss_k  <- pmax(1L, floor(0.5 * cls_k))  # 50% per class without replacement
      rf_fit <- randomForest::randomForest(
        yk ~ ., data = mod_data,
        ntree = best_params$ntree,
        mtry  = best_params$mtry,
        nodesize = 40,
        maxnodes = 8,
        replace = FALSE,
        sampsize = ss_k
      )
      
      probs_train <- predict(rf_fit, newdata = as.data.frame(Z[,  -1, drop = FALSE]), type = "prob")
      probs_test  <- predict(rf_fit, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")
      
      cure_preds[, k] <- probs_train[, "uncured"]
      pred_preds[, k] <- probs_test[,  "uncured"]
    }
    
    update_cureb <- rowMeans(cure_preds, na.rm = TRUE)
    update_pred  <- rowMeans(pred_preds, na.rm = TRUE)
    
    # Using a local dataframe to ensure 'offset' and 'subset' align correctly with matrices
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-8)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(logM)"))
    
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    if (!inherits(cox_fit, "try-error")) {
      update_beta <- as.numeric(cox_fit$coefficients)
    } else {
      update_beta <- beta
    }
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    # no test-side survival update inside EM
    
    convergence <- sum(c(update_beta - beta,
                         mean(update_cureb) - mean(uncureprob),
                         mean(update_s)    - mean(s))^2)
    
    UN <- update_cureb
    PRED <- update_pred
    beta <- update_beta 
    s <- update_s
    s1 <- update_s1
    
    i <- i + 1
  }
  
  eta  <- as.vector(X[, -1, drop = FALSE]  %*% beta)
  eta1 <- as.vector(X1[, -1, drop = FALSE] %*% beta)
  
  survival  <- drop(s  ^ exp(eta))
  survival1 <- drop(s1 ^ exp(eta1))
  
  Sp = (1-UN)^(1-survival) # survival prob. of the population
  Sp.pred = (1-PRED)^(1-survival1) 
  S1 = (Sp-(1-UN))/UN # survival prob. of the susceptible group
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  em.rf.Pois <-list(latencyfit = beta, UN = UN,PRED = PRED,
                    Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = survival1,
                    s0 = s, S = survival, tau = convergence,
                    ntree = best_params$ntree, mtry = best_params$mtry)
}

smcure.rf.Pois <- function(setting = NULL, formula, cureform, offset = NULL, data, testdata,
                           na.action = na.omit, Var = T, emmax = 1000, eps = 1e-3,
                           ntree_grid = c(100,200, 500), mtry_grid = NULL, nboot = 100) {
  call <- match.call()
  
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  if (!inherits(Y, "Surv")) stop("Response must be a survival object")
  
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  
  Z <- model.matrix(cureform, data)
  Z1 <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, ncol(Z))
  beta <- rep(0.5, nbeta)
  
  # --- Pre-tuning of Random Forest (10-fold CV) ---
  nw  <- factor(Status, levels = c(0,1), labels = c("cured","uncured"))
  Xrf <- as.data.frame(Z[, -1, drop = FALSE])
  
  if (is.null(mtry_grid)) {
    p <- ncol(Xrf)
    mtry_grid <- max(1L, floor(sqrt(p)))  # strict: only sqrt(p)
  }
  # Cap mtry (redundant with strict default, keeps user-supplied grids in check)
  p_all <- ncol(Xrf)
  mtry_cap <- max(1L, floor(p_all/3))
  mtry_grid <- sort(unique(as.integer(mtry_grid[mtry_grid <= mtry_cap])))
  if (length(mtry_grid) == 0L) mtry_grid <- max(1L, floor(sqrt(p_all)))
  # Stronger cap on mtry to reduce memorization
  p_all <- ncol(Xrf)
  mtry_cap <- max(1L, floor(p_all/3))
  mtry_grid <- sort(unique(mtry_grid[mtry_grid <= mtry_cap]))
  if (length(mtry_grid) == 0L) mtry_grid <- max(1L, floor(sqrt(p_all)))
  
  set.seed(1); K <- 10
  pos <- which(nw == "uncured"); neg <- which(nw == "cured")
  fpos <- split(sample(pos), rep(1:K, length.out = length(pos)))
  fneg <- split(sample(neg), rep(1:K, length.out = length(neg)))
  folds <- lapply(1:K, function(k) sort(c(fpos[[k]], fneg[[k]])))
  
  # fast AUC without extra packages
  auc_fast <- function(y, p){
    y <- as.integer(y == "uncured"); n1 <- sum(y==1); n0 <- sum(y==0)
    if (n1 == 0 || n0 == 0) return(NA_real_)
    r <- rank(p, ties.method = "average")
    (sum(r[y==1]) - n1*(n1+1)/2) / (n1*n0)
  }
  
  grid <- expand.grid(ntree = ntree_grid, mtry = mtry_grid)
  grid$auc <- NA_real_
  
  for (irow in seq_len(nrow(grid))){
    nt <- grid$ntree[irow]; mt <- grid$mtry[irow]
    y_all <- c(); p_all <- c()
    for (k in 1:K){
      vl <- folds[[k]]; tr <- setdiff(seq_len(nrow(Xrf)), vl)
      if (length(unique(nw[tr])) < 2 || length(unique(nw[vl])) < 2) next
      fit <- try(randomForest::randomForest(
        x = Xrf[tr, , drop = FALSE], y = nw[tr],
        ntree = nt, mtry = mt,
        nodesize = 40,
        maxnodes = 8,
        replace = FALSE,
        sampsize = pmax(1L, floor(0.5 * table(nw[tr])))
      ), silent = TRUE)
      if (inherits(fit, "try-error")) next
      pv <- try(predict(fit, newdata = Xrf[vl, , drop = FALSE], type = "prob")[, "uncured"], silent = TRUE)
      if (inherits(pv, "try-error")) next
      y_all <- c(y_all, nw[vl]); p_all <- c(p_all, pv)
    }
    grid$auc[irow] <- if (length(y_all) > 1) auc_fast(y_all, p_all) else NA_real_
  }
  
  best_idx <- if (all(is.na(grid$auc))) 1L else which.max(grid$auc)
  best_params <- list(ntree = grid$ntree[best_idx], mtry = grid$mtry[best_idx])
  
  # Initial RF with best params
  Xrf_init <- as.data.frame(Z[, -1, drop = FALSE])
  y_rf_init <- factor(Status, levels = c(0,1), labels = c("cured","uncured"))
  # stratified subsampling for the initializer, too
  ss0 <- pmax(1L, floor(0.5 * table(y_rf_init)))
  initial_mod <- randomForest::randomForest(
    x = Xrf_init, y = y_rf_init,
    ntree = best_params$ntree,
    mtry  = best_params$mtry,
    nodesize = 40,
    maxnodes = 8,
    replace = FALSE,
    sampsize = ss0
  )
  
  uncureprob <- predict(initial_mod, newdata = as.data.frame(Z[,  -1, drop = FALSE]), type = "prob")[, "uncured"]
  uncurepred <- predict(initial_mod, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")[, "uncured"]
  
  
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  
  
  
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data$hazard)
  t_grid  <- out.data$time
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1$hazard)
  t_grid1  <- out.data1$time
  
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  
  s0  <- S0_grid[idx_tr]   # length(Time)
  s01 <- S01_grid[idx_te]   # length(Time1)
  
  if(any(is.na(s0))) s0[is.na(s0)] <- min(s0, na.rm = TRUE)
  if(any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  
  
  emfit <- em.rf.Pois( Time = Time, Status = Status,
                       Time1 = Time1, Status1 = Status1,
                       X = X, X1 = X1,
                       Z = Z, Z1 = Z1,
                       uncureprob = uncureprob,
                       uncurepred = uncurepred,
                       beta = beta,
                       s0 = s0, s01 = s01,
                       emmax = emmax, eps = eps,
                       best_params = best_params)
  beta.est = emfit$latencyfit
  #b.est = emfit$b
  UN<-emfit$UN
  PRED<-emfit$PRED
  Sp = emfit$Sp
  Sp.pred = emfit$Sp.pred
  S1 = emfit$S1
  S1.pred = emfit$S1.pred
  s0 = emfit$s0
  s01 = emfit$s01
  S = emfit$S
  S.pred = emfit$S.pred
  conv = emfit$tau
  
  if (Var) {
    # --- Bootstrap for latency coefficients and uncure probabilities (RF EM) ---
    n <- length(Status)
    
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    # Stratified bootstrap indices on TRAIN
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (ib in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      
      # Rebuild TRAIN matrices from the same formulas
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      if (!inherits(Y_b, "Surv")) stop("Response must be a survival object")
      
      Time_b   <- Y_b[, 1]
      Status_b <- Y_b[, 2]
      
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Bootstrap baseline survival at bootstrap times (TRAIN only; no leakage)
      coxfit_b <- coxph(Surv(Time_b, Status_b) ~ 1)
      s0_b <- summary(survfit(coxfit_b), times = Time_b, extend = TRUE)$surv
      s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      
      # Initial RF on bootstrap TRAIN to initialize uncure probs
      y_rf_b <- factor(Status_b, levels = c(0, 1), labels = c("cured", "uncured"))
      Xrf_b  <- as.data.frame(Z_b[, -1, drop = FALSE])
      ss_b   <- pmax(1L, floor(0.5 * table(y_rf_b)))
      
      rf_init_b <- try(
        randomForest::randomForest(
          x = Xrf_b, y = y_rf_b,
          ntree = best_params$ntree,
          mtry  = best_params$mtry,
          nodesize = 40,
          maxnodes = 8,
          replace = FALSE,
          sampsize = ss_b
        ),
        silent = TRUE
      )
      
      if (inherits(rf_init_b, "try-error")) {
        uncureprob_b <- rep(mean(Status_b), length(Status_b))
        uncurepred_b <- rep(mean(Status_b), length(Status1))
      } else {
        pr_tr <- predict(rf_init_b, newdata = as.data.frame(Z_b[,  -1, drop = FALSE]), type = "prob")
        pr_te <- predict(rf_init_b, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "prob")
        uncureprob_b <- pr_tr[, "uncured"]
        uncurepred_b <- pr_te[, "uncured"]
      }
      
      uncureprob_b <- pmin(pmax(uncureprob_b, 1e-9), 1 - 1e-9)
      uncurepred_b <- pmin(pmax(uncurepred_b, 1e-9), 1 - 1e-9)
      
      # Fit RF-EM on bootstrap TRAIN; keep TEST fixed
      bootfit <- em.rf.Pois(
        Time_b, Status_b, Time1, Status1,
        X_b, X1, Z_b, Z1,
        uncureprob_b, uncurepred_b,
        beta = emfit$latencyfit,
        s0 = s0_b, s01 = NULL,
        emmax = emmax, eps = eps,
        best_params = best_params
      )
      
      latency_boot[ib, ] <- bootfit$latencyfit
      uncure_boot[ib, ]  <- as.numeric(bootfit$UN)
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    lower_uncure <- as.numeric(emfit$UN) - 1.96 * uncure_sd
    upper_uncure <- as.numeric(emfit$UN) + 1.96 * uncure_sd
    
    # clamp to [0, 1]
    lower_uncure <- pmax(0, lower_uncure)
    upper_uncure <- pmin(1, upper_uncure)
    
    # attach results to the returned object (minimal change outside bootstrap)
    emfit$latency_var  <- latency_var
    emfit$latency_sd   <- latency_sd
    emfit$lower_uncure <- lower_uncure
    emfit$upper_uncure <- upper_uncure
  }
  fit<-list()
  class(fit) <- c("smcure.rf.Pois")
  
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure}
  cat(" done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  #fit$b <- b.est
  fit$Sp = Sp
  fit$Sp.pred = Sp.pred
  fit$S1 = S1
  fit$S1.pred = S1.pred
  fit$s0 = s0
  fit$s01 = s01
  fit$S = S
  fit$S.pred = S.pred
  fit$tau = conv
  fit
  return(fit)
}









# XGBOOST
em.xgb.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                        uncureprob, uncurepred, beta, s0, s01,
                        emmax, eps, best_params, nrounds) {
  alpha <- 0.2  # local damping for EM (prevents overfit oscillations)
  n <- length(Status)
  m <- length(Status1)
  s  <- s0
  s1 <- s01
  K <- 5  # K-imputation heads
  
  n <- length(Status)
  
  
  K <- 5                  # K-imputation heads
  
  #
  convergence<- 1000;i <-1
  while (convergence > eps & i < emmax){  
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    survival<-drop(s^(exp((X[, -1, drop = FALSE]%*%(beta))))) # survival function of the progression times
    survival1<-drop(s1^(exp(X1[, -1, drop = FALSE]%*%(beta))))
    
    # Decision tree incidence: use current probability vectors (initialized in wrapper)
    UN   <- pmin(pmax(as.numeric(uncureprob), 1e-9), 1 - 1e-9)
    PRED <- pmin(pmax(as.numeric(uncurepred), 1e-9), 1 - 1e-9)
    
    
    
    
    w <- Status + (1-Status)*(1-((1-UN)^(survival))) 
    M <- Status - (survival * log(pmax(1 - UN, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - PRED, 1e-6)))
    
    
    # ---- K-imputation via XGBoost (TRAIN ONLY) ----
    V_matrix <- matrix(rbinom(n * K, size = 1, prob = rep(w, each = K)), nrow = n, byrow = TRUE)
    cure_preds <- matrix(NA_real_, nrow = n, ncol = K)
    pred_preds <- matrix(NA_real_, nrow = m + 0L, ncol = K)  # ensure integer length
    
    dtest <- xgboost::xgb.DMatrix(data = as.matrix(Z1[, -1, drop = FALSE]))
    for (k in 1:K) {
      dtrain_k <- xgboost::xgb.DMatrix(data = as.matrix(Z[, -1, drop = FALSE]), label = V_matrix[, k])
      xgb_mod <- xgboost::xgb.train(
        params = best_params,
        data = dtrain_k,
        nrounds = nrounds,
        verbose = 0
      )
      cure_preds[, k] <- as.numeric(predict(xgb_mod, dtrain_k))
      pred_preds[, k] <- as.numeric(predict(xgb_mod, dtest))
    }
    
    update_cureb <- pmin(pmax(rowMeans(cure_preds, na.rm = TRUE), 1e-6), 1 - 1e-6)
    update_pred  <- pmin(pmax(rowMeans(pred_preds, na.rm = TRUE), 1e-6), 1 - 1e-6)
    
    # Using a local dataframe to ensure 'offset' and 'subset' align correctly with matrices
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-8)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(logM)"))
    
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    if (!inherits(cox_fit, "try-error")) {
      update_beta <- as.numeric(cox_fit$coefficients)
    } else {
      update_beta <- beta
    }
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival 
    
    # ---- Convergence ----
    convergence <- sum(c(sum((update_beta - beta)^2),
                         (mean(update_cureb) - mean(uncureprob))^2,
                         (mean(update_s) - mean(s))^2), na.rm = TRUE)
    
    # ---- Update state with damping ----
    UN <- update_cureb
    PRED <- update_pred
    beta <- update_beta 
    s <- update_s
    s1 <- update_s1
    i <- i + 1
    
    
  }
  
  
  
  
  eta  <- as.vector(X[, -1, drop = FALSE]  %*% beta)
  eta1 <- as.vector(X1[, -1, drop = FALSE] %*% beta)
  
  survival  <- drop(s  ^ exp(eta))
  survival1 <- drop(s1 ^ exp(eta1))
  
  Sp = (1-UN)^(1-survival) # survival prob. of the population
  Sp.pred = (1-PRED)^(1-survival1) 
  S1 = (Sp-(1-UN))/UN # survival prob. of the susceptible group
  S1.pred = (Sp.pred-(1-PRED))/pmax(PRED, 1e-9)
  
  
  
  em.xgb.Pois <-list(latencyfit = beta, UN = UN,PRED = PRED,
                     Sp = Sp, Sp.pred = Sp.pred, S1 = S1, S1.pred = S1.pred, S.pred = survival1,
                     s0 = s, S = survival, tau = convergence, best_params = best_params, nrounds = nrounds)
}

smcure.xgb.Pois <- function(setting = NULL, formula, cureform, offset = NULL, data, testdata,
                            na.action = na.omit, Var = T, emmax = 1000, eps = 1e-3, nboot = 100) {
  # Build design matrices
  data <- na.action(data); testdata <- na.action(testdata)
  mf <- model.frame(formula, data); mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response"); Y1 <- model.extract(mp, "response")
  Time <- Y[, 1]; Status <- Y[, 2]; Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  Z <- model.matrix(cureform, data); Z1 <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf); X1 <- model.matrix(attr(mp, "terms"), mp)
  nbeta <- ncol(X) - 1
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, ncol(Z))
  beta <- rep(0.5, nbeta)
  
  # Initialize latency beta via plain CoxPH (no cure)
  
  X_df <- as.data.frame(X[, -1, drop = FALSE]); colnames(X_df) <- betanm
  cox_form <- as.formula(paste("Surv(Time, Status) ~", paste(betanm, collapse = " + ")))
  beta_init <- tryCatch({
    fit0 <- survival::coxph(cox_form, data = cbind.data.frame(Time=Time, Status=Status, X_df))
    b <- stats::coef(fit0); if (is.null(b)) rep(0, nbeta) else unname(b)
  }, error = function(e) rep(0, nbeta))
  
  # Crude incidence initializer via GLM on Status
  glm_data <- cbind.data.frame(Status = Status, as.data.frame(Z[, -1, drop = FALSE]))
  glm_fit <- tryCatch(glm(Status ~ ., data = glm_data, family = binomial()), error = function(e) NULL)
  p_init <- if (is.null(glm_fit)) rep(mean(Status), length(Status)) else as.numeric(predict(glm_fit, type = "response"))
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data$hazard)
  t_grid  <- out.data$time
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1$hazard)
  t_grid1  <- out.data1$time
  
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  
  s0  <- S0_grid[idx_tr]   # length(Time)
  s01 <- S01_grid[idx_te]   # length(Time1)
  
  if(any(is.na(s0))) s0[is.na(s0)] <- min(s0, na.rm = TRUE)
  if(any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  
  # One-step imputed labels for CV tuning (aligns with EM noise)
  eta0 <- drop(as.matrix(X[, -1, drop = FALSE]) %*% beta_init)
  surv0 <- drop(s0^(exp(eta0)))
  w0 <- Status + (1 - Status) * (1 - ((1 - p_init)^surv0))
  w0 <- pmin(pmax(w0, 0.02), 0.98)
  y_imp <- as.numeric(rbinom(length(w0), 1, w0))
  
  # 10-fold CV to tune (eta, nrounds) with early stopping (logloss)
  dtrain_cv <- xgboost::xgb.DMatrix(data = as.matrix(Z[, -1, drop = FALSE]), label = y_imp)
  eta_grid <- c(0.05, 0.04, 0.2, 0.03)
  nrounds_cap <- 500
  early_stop <- 15
  
  base_params <- list(
    objective = "binary:logistic",
    max_depth = 2,
    subsample = 0.6,
    colsample_bytree = 0.6,
    colsample_bylevel = 0.6,
    min_child_weight = 5,
    gamma = 2,
    lambda = 6,
    alpha = 4,
    eval_metric = "logloss"
  )
  
  best_eta <- NA_real_; best_iter <- NA_integer_; best_loss <- Inf
  for (eta in eta_grid) {
    params <- modifyList(base_params, list(eta = eta))
    cv <- xgboost::xgb.cv(
      params = params,
      data = dtrain_cv,
      nrounds = nrounds_cap,
      nfold = 10,
      stratified = TRUE,
      early_stopping_rounds = early_stop,
      verbose = 0
    )
    mean_logloss <- min(cv$evaluation_log$test_logloss_mean, na.rm = TRUE)
    iter <- cv$best_iteration
    if (is.finite(mean_logloss) && mean_logloss < best_loss) {
      best_loss <- mean_logloss; best_eta <- eta; best_iter <- ifelse(is.null(iter) || iter == 0, nrounds_cap, iter)
    }
  }
  if (!is.finite(best_eta)) { best_eta <- 0.1; best_iter <- 100 }
  best_params <- modifyList(base_params, list(eta = best_eta))
  nrounds <- best_iter
  
  # Train final initializer XGB on imputed labels
  dtrain_full <- xgboost::xgb.DMatrix(data = as.matrix(Z[, -1, drop = FALSE]), label = y_imp)
  dtest_full  <- xgboost::xgb.DMatrix(data = as.matrix(Z1[, -1, drop = FALSE]))
  xgb_init <- xgboost::xgb.train(params = best_params, data = dtrain_full, nrounds = nrounds, verbose = 0)
  uncureprob <- pmin(pmax(as.numeric(predict(xgb_init, dtrain_full)), 1e-6), 1 - 1e-6)
  uncurepred <- pmin(pmax(as.numeric(predict(xgb_init, dtest_full)),  1e-6), 1 - 1e-6)
  
  
  
  
  # Run EM
  emfit <- em.xgb.Pois(Time = Time, Status = Status,
                       Time1 = Time1, Status1 = Status1,
                       X = X, X1 = X1,
                       Z = Z, Z1 = Z1,
                       uncureprob = uncureprob,
                       uncurepred = uncurepred,
                       beta = beta,
                       s0 = s0, s01 = s01,
                       emmax = emmax, eps = eps,
                       best_params = best_params, nrounds = nrounds)
  beta.est = emfit$latencyfit
  #b.est = emfit$b
  UN<-emfit$UN
  PRED<-emfit$PRED
  Sp = emfit$Sp
  Sp.pred = emfit$Sp.pred
  S1 = emfit$S1
  S1.pred = emfit$S1.pred
  s0 = emfit$s0
  s01 = emfit$s01
  S = emfit$S
  S.pred = emfit$S.pred
  conv = emfit$tau
  
  if (Var) {
    # --- Bootstrap for latency coefficients and uncure probabilities (XGB EM) ---
    n <- length(Status)
    
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    # Stratified bootstrap indices on TRAIN
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (ib in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      
      # Rebuild TRAIN matrices from the same formulas
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      if (!inherits(Y_b, "Surv")) stop("Response must be a survival object")
      
      Time_b   <- Y_b[, 1]
      Status_b <- Y_b[, 2]
      
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Baseline survival for bootstrap TRAIN (fit on bootstrap TRAIN, evaluate at Time_b and fixed Time1)
      coxfit_b <- survival::coxph(survival::Surv(Time_b, Status_b) ~ 1)
      s0_b  <- summary(survival::survfit(coxfit_b), times = Time_b, extend = TRUE)$surv
      s01_b <- summary(survival::survfit(coxfit_b), times = Time1,  extend = TRUE)$surv
      if (any(is.na(s0_b)))  s0_b[is.na(s0_b)]   <- min(s0_b,  na.rm = TRUE)
      if (any(is.na(s01_b))) s01_b[is.na(s01_b)] <- min(s01_b, na.rm = TRUE)
      
      # Initialize beta from the main EM fit (stable starting point)
      beta_init_b <- emfit$latencyfit
      if (is.null(beta_init_b) || length(beta_init_b) != (ncol(X_b) - 1)) beta_init_b <- rep(0, ncol(X_b) - 1)
      
      # Crude incidence initializer via GLM on Status_b
      glm_data_b <- cbind.data.frame(Status = Status_b, as.data.frame(Z_b[, -1, drop = FALSE]))
      glm_fit_b <- tryCatch(glm(Status ~ ., data = glm_data_b, family = binomial()), error = function(e) NULL)
      p_init_b <- if (is.null(glm_fit_b)) rep(mean(Status_b), length(Status_b)) else as.numeric(predict(glm_fit_b, type = "response"))
      p_init_b <- pmin(pmax(p_init_b, 1e-6), 1 - 1e-6)
      
      # One-step imputed labels for bootstrap CV-like initializer (matches your main wrapper logic)
      eta0_b  <- drop(as.matrix(X_b[, -1, drop = FALSE]) %*% beta_init_b)
      surv0_b <- drop(s0_b^(exp(eta0_b)))
      w0_b <- Status_b + (1 - Status_b) * (1 - ((1 - p_init_b)^surv0_b))
      w0_b <- pmin(pmax(w0_b, 0.02), 0.98)
      y_imp_b <- as.numeric(rbinom(length(w0_b), 1, w0_b))
      
      dtrain_full_b <- xgboost::xgb.DMatrix(data = as.matrix(Z_b[, -1, drop = FALSE]), label = y_imp_b)
      dtest_full    <- xgboost::xgb.DMatrix(data = as.matrix(Z1[, -1, drop = FALSE]))
      
      xgb_init_b <- xgboost::xgb.train(params = best_params, data = dtrain_full_b, nrounds = nrounds, verbose = 0)
      uncureprob_b <- pmin(pmax(as.numeric(predict(xgb_init_b, dtrain_full_b)), 1e-6), 1 - 1e-6)
      uncurepred_b <- pmin(pmax(as.numeric(predict(xgb_init_b, dtest_full)),  1e-6), 1 - 1e-6)
      
      # Fit XGB-EM on bootstrap TRAIN; keep TEST fixed
      bootfit <- em.xgb.Pois(
        Time_b, Status_b, Time1, Status1,
        X_b, X1, Z_b, Z1,
        uncureprob_b, uncurepred_b,
        beta = beta_init_b,
        s0 = s0_b, s01 = s01_b,
        emmax = emmax, eps = eps,
        best_params = best_params,
        nrounds = nrounds
      )
      
      latency_boot[ib, ] <- bootfit$latencyfit
      uncure_boot[ib, ]  <- as.numeric(bootfit$UN)
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    lower_uncure <- as.numeric(emfit$UN) - 1.96 * uncure_sd
    upper_uncure <- as.numeric(emfit$UN) + 1.96 * uncure_sd
    
    # clamp to [0, 1]
    lower_uncure <- pmax(0, lower_uncure)
    upper_uncure <- pmin(1, upper_uncure)
  }
  fit<-list()
  class(fit) <- c("smcure.xgb.Pois")
  
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure}
  cat(" done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  #fit$b <- b.est
  fit$Sp = Sp
  fit$Sp.pred = Sp.pred
  fit$S1 = S1
  fit$S1.pred = S1.pred
  fit$s0 = s0
  fit$s01 = s01
  fit$S = S
  fit$S.pred = S.pred
  fit$tau = conv
  fit
  return(emfit)
}







# SPLINE
em.spline.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                           b, beta, s0, s01, emmax, eps) {
  n <- length(Status)
  m <- length(Status1)
  s <- as.numeric(s0)
  s1 <- as.numeric(s01)
  
  convergence <- 1000
  i <- 1
  
  while (convergence > eps && i <= emmax) {
    uncureprob <- as.vector(plogis(Z %*% b))
    uncurepred <- as.vector(plogis(Z1 %*% b))
    
    if(is.null(beta) || length(beta) != (ncol(X) - 1)) {
      beta <- rep(0, ncol(X) - 1)
    }
    
    # Ensure beta is a numeric vector for matrix multiplication
    curr_beta <- as.numeric(beta)
    
    survival  <- drop(s^(exp((X[, -1, drop = FALSE] %*% curr_beta))))
    survival1 <- drop(s1^(exp(X1[, -1, drop = FALSE] %*% curr_beta)))
    
    # E-step weights (M)
    M <- Status - (survival * log(pmax(1 - uncureprob, 1e-6)))
    M1 <- Status1 - (survival1 * log(pmax(1 - uncurepred, 1e-6)))
    
    # M-step: Incidence (optimizing b)
    Q1 <- function(par) {
      u1 <- as.vector(plogis(Z %*% par))
      -sum(M * log(pmax(-log(1 - u1), 1e-9))) - sum(log(pmax(1 - u1, 1e-9)))
    }
    update_b <- try(optim(par = b, fn = Q1, method = "Nelder-Mead")$par, silent = TRUE)
    if (inherits(update_b, "try-error")) update_b <- b
    
    # M-step: Latency (Cox) - USE DATA FRAME TO AVOID SUBSCRIPT ERRORS
    df_cox <- as.data.frame(X[, -1, drop = FALSE])
    colnames(df_cox) <- paste0("V", 1:ncol(df_cox))
    df_cox$Time <- Time
    df_cox$Status <- Status
    df_cox$logM <- log(pmax(M, 1e-8))
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(df_cox)[1:(ncol(X)-1)], collapse = "+"), "+ offset(logM)"))
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    update_beta <- if (!inherits(cox_fit, "try-error")) as.numeric(cox_fit$coefficients) else curr_beta
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    update_uncureprob <- as.vector(plogis(Z %*% update_b))
    
    convergence <- sum(c(update_beta - curr_beta,
                         mean(update_uncureprob) - mean(uncureprob))^2, na.rm = TRUE)
    
    b <- as.numeric(update_b)
    beta <- as.numeric(update_beta)
    s <- as.numeric(update_s)
    s1 <- as.numeric(update_s1)
    i <- i + 1
  }
  
  # Final estimates
  UN <- as.vector(plogis(Z %*% b))
  PRED <- as.vector(plogis(Z1 %*% b))
  
  final_surv  <- drop(s ^ exp(as.numeric(X[, -1, drop = FALSE] %*% beta)))
  final_surv1 <- drop(s1 ^ exp(as.numeric(X1[, -1, drop = FALSE] %*% beta)))
  
  Sp = (1 - UN)^(1 - final_surv)
  Sp.pred = (1 - PRED)^(1 - final_surv1)
  
  return(list(b = b,
              latencyfit = beta,
              UN = UN,
              PRED = PRED,
              Sp = Sp,
              Sp.pred = Sp.pred,
              S1 = (Sp - (1 - UN)) / pmax(UN, 1e-9),
              S1.pred = (Sp.pred - (1 - PRED)) / pmax(PRED, 1e-9),
              s0 = s,
              s01 = s1,
              S = final_surv,
              S.pred = final_surv1,
              tau = convergence))
}

smcure.spline.Pois <- function(setting = NULL, formula = NULL, cureform = NULL,
                               offset = NULL, data, testdata,
                               na.action = na.omit, Var = F,
                               emmax = 1000, eps = 1e-3, nboot = 100) {
  call <- match.call()
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  Z_raw <- model.matrix(cureform, data)
  Z1_raw <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  
  bnm <- colnames(Z_raw); nb <- ncol(Z_raw)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  # Spline construction
  Z_scaled_values <- scale(Z_raw[, -1, drop = FALSE])
  center_vals <- attr(Z_scaled_values, "scaled:center")
  scale_vals <- attr(Z_scaled_values, "scaled:scale")
  Z1_scaled_values <- scale(Z1_raw[, -1, drop = FALSE], center = center_vals, scale = scale_vals)
  
  df_fixed <- 1
  covariate_names <- colnames(Z_scaled_values)
  
  Z_spline_list <- lapply(covariate_names, function(var) splines::ns(Z_scaled_values[, var], df = df_fixed))
  Z_spline <- do.call(cbind, Z_spline_list)
  
  Z1_spline_list <- lapply(covariate_names, function(var) {
    basis <- splines::ns(Z_scaled_values[, var], df = df_fixed)
    predict(basis, Z1_scaled_values[, var])
  })
  Z1_spline <- do.call(cbind, Z1_spline_list)
  
  Z <- cbind(1, Z_spline)
  Z1 <- cbind(1, Z1_spline)
  
  # Baseline survival initialization
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  out.data <- basehaz(coxfit_train, centered = FALSE)
  s0_init <- stepfun(out.data$time, c(1, exp(-out.data$hazard)))(Time)
  
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  out.data1 <- basehaz(coxfit_test, centered = FALSE)
  s01_init <- stepfun(out.data1$time, c(1, exp(-out.data1$hazard)))(Time1)
  
  emfit <- em.spline.Pois(Time, Status, Time1, Status1, X, X1, Z, Z1,
                          b = rep(0, ncol(Z)), beta = rep(0, nbeta), 
                          s0 = s0_init, s01 = s01_init, emmax, eps)
  
  beta.est <- emfit$latencyfit
  b.est <- emfit$b
  UN <- emfit$UN
  PRED <- emfit$PRED
  
  if (Var) {
    n <- length(Status)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    uncure_boot <- matrix(0, nrow = nboot, ncol = n)
    
    for (ib in 1:nboot) {
      b_idx <- sample(1:n, n, replace = TRUE)
      bootdata <- data[b_idx, ]
      mf_b <- model.frame(formula, bootdata)
      Y_b <- model.extract(mf_b, "response")
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b_raw <- model.matrix(cureform, bootdata)
      
      # Re-scale for bootstrap
      Zb_scaled <- scale(Z_b_raw[, -1, drop = FALSE])
      Zb_spline_list <- lapply(colnames(Zb_scaled), function(v) splines::ns(Zb_scaled[, v], df = df_fixed))
      Zb_spline <- cbind(1, do.call(cbind, Zb_spline_list))
      
      s0_b <- s0_init[b_idx]
      
      bootfit <- try(em.spline.Pois(Y_b[,1], Y_b[,2], Time1, Status1, X_b, X1, Zb_spline, Z1,
                                    b.est, beta.est, s0_b, s01_init, emmax, eps), silent = TRUE)
      if (!inherits(bootfit, "try-error")) {
        latency_boot[ib,] <- bootfit$latencyfit
        uncure_boot[ib,] <- as.numeric(bootfit$UN)
      }
    }
    latency_sd <- apply(latency_boot, 2, sd)
  }
  
  fit <- list(latency = beta.est, UN = UN, PRED = PRED, b = b.est,
              Sp = emfit$Sp, Sp.pred = emfit$Sp.pred, S1 = emfit$S1, S1.pred = emfit$S1.pred,
              s0 = emfit$s0, s01 = emfit$s01, S = emfit$S, S.pred = emfit$S.pred, tau = emfit$tau)
  
  if (Var) {
    fit$latency_sd <- latency_sd
    fit$latency_pvalue <- (1 - pnorm(abs(fit$latency/latency_sd))) * 2
  }
  
  return(fit)
}



#NEURAL NETWORK
em.nn.Pois <- function(Time, Status, Time1, Status1, X, X1, Z, Z1,
                       uncureprob, uncurepred, beta, s0, s01,
                       emmax, eps, best_params, stepmax) {
  
  X <- as.matrix(X); X1 <- as.matrix(X1)
  Z <- as.matrix(Z); Z1 <- as.matrix(Z1)
  n <- length(Status); m <- length(Status1)
  
  s <- as.numeric(s0); s1 <- as.numeric(s01)
  
  convergence <- 1000; i <- 1
  
  while (convergence > eps && i <= emmax) {
    beta <- as.numeric(beta)
    
    # 1. Latency Predictors (Clamped to prevent Inf)
    eta_tr <- pmin(pmax(as.numeric(X[, -1, drop = FALSE] %*% beta), -20), 20)
    eta_te <- pmin(pmax(as.numeric(X1[, -1, drop = FALSE] %*% beta), -20), 20)
    
    survival  <- pmin(pmax(drop(s^exp(eta_tr)), 1e-10), 1)
    survival1 <- pmin(pmax(drop(s1^exp(eta_te)), 1e-10), 1)
    
    # 2. E-step (Clamped UN to prevent log(0))
    UN <- pmin(pmax(as.numeric(uncureprob), 1e-7), 1 - 1e-7)
    PRED <- pmin(pmax(as.numeric(uncurepred), 1e-7), 1 - 1e-7)
    
    w <- Status + (1 - Status) * (1 - ((1 - UN)^survival)) 
    w <- pmin(pmax(as.numeric(w), 0), 1)
    
    M  <- pmin(pmax(Status - (survival * log(1 - UN)), 1e-9), 10)
    M1 <- pmin(pmax(Status1 - (survival1 * log(1 - PRED)), 1e-9), 10)
    
    # 3. M-step (Incidence - Neural Network)
    K <- 5
    V_matrix <- matrix(rbinom(n * K, 1, rep(w, each = K)), nrow = n, byrow = TRUE)
    y_long <- as.vector(V_matrix)
    Z_long <- Z[rep(1:n, times = K), -1, drop = FALSE]
    
    train_df <- data.frame(y = y_long, as.data.frame(Z_long))
    names(train_df) <- make.names(names(train_df))
    
    nn_mod <- try(neuralnet::neuralnet(y ~ ., data = train_df, hidden = best_params,
                                       linear.output = FALSE, stepmax = stepmax, threshold = 0.5), silent = TRUE)
    
    update_cureb <- uncureprob; update_pred <- uncurepred
    
    if (!inherits(nn_mod, "try-error")) {
      Z_tr <- as.data.frame(Z[, -1, drop = FALSE]); names(Z_tr) <- make.names(names(Z_tr))
      Z_te <- as.data.frame(Z1[, -1, drop = FALSE]); names(Z_te) <- make.names(names(Z_te))
      update_cureb <- as.numeric(neuralnet::compute(nn_mod, covariate = Z_tr)$net.result)
      update_pred  <- as.numeric(neuralnet::compute(nn_mod, covariate = Z_te)$net.result)
    } else {
      # Fallback to GLM
      glm_fit <- glm(y ~ ., data = train_df, family = binomial())
      update_cureb <- as.numeric(predict(glm_fit, newdata = as.data.frame(Z[, -1, drop = FALSE]), type = "response"))
      update_pred <- as.numeric(predict(glm_fit, newdata = as.data.frame(Z1[, -1, drop = FALSE]), type = "response"))
    }
    update_cureb <- pmin(pmax(update_cureb, 1e-6), 1-1e-6)
    update_pred <- pmin(pmax(update_pred, 1e-6), 1-1e-6)
    
    
    # Using a local dataframe to ensure 'offset' and 'subset' align correctly with matrices
    df_cox <- data.frame(Time = Time, Status = Status, logM = log(pmax(M, 1e-8)))
    X_part <- as.data.frame(X[, -1, drop = FALSE])
    colnames(X_part) <- paste0("V", 1:ncol(X_part))
    df_cox <- cbind(df_cox, X_part)
    
    cox_formula <- as.formula(paste("Surv(Time, Status) ~", paste(colnames(X_part), collapse = "+"), "+ offset(logM)"))
    
    cox_fit <- try(coxph(cox_formula, data = df_cox, subset = M > 0, method = "breslow"), silent = TRUE)
    
    if (!inherits(cox_fit, "try-error")) {
      update_beta <- as.numeric(cox_fit$coefficients)
    } else {
      update_beta <- beta
    }
    
    update_s <- smsurv(Time, Status, X, update_beta, w = M, model = "ph")$survival
    update_s1 <- smsurv(Time1, Status1, X1, update_beta, w = M1, model = "ph")$survival
    
    convergence <- sum((update_beta - beta)^2, na.rm=TRUE) + (mean(update_cureb) - mean(uncureprob))^2
    
    beta <- update_beta; uncureprob <- update_cureb; uncurepred <- update_pred
    s <- pmin(pmax(update_s, 1e-12), 1); s1 <- pmin(pmax(update_s1, 1e-12), 1)
    i <- i + 1
  }
  
  
  # Numerical Safeguards for S1 calculation
  final_S <- s^exp(as.numeric(X[, -1, drop = FALSE] %*% beta))
  final_S1 <- s1^exp(as.numeric(X1[, -1, drop = FALSE] %*% beta))
  
  Sp <- (1 - uncureprob)^(1 - final_S)
  Sp_pred <- (1 - uncurepred)^(1 - final_S1)
  
  # Calculate S1 using the identity: Sp = (1-p) + p*S1 => S1 = (Sp - (1-p))/p
  # We use pmax(..., 0) to prevent negative results from precision errors
  S1_calc <- pmax(as.numeric((Sp - (1 - uncureprob)) / pmax(uncureprob, 1e-9)), 0)
  S1_pred_calc <- pmax(as.numeric((Sp_pred - (1 - uncurepred)) / pmax(uncurepred, 1e-9)), 0)
  
  return(list(latencyfit = beta, UN = uncureprob, PRED = uncurepred,
              Sp = Sp, Sp.pred = Sp_pred, 
              S1 = S1_calc, S1.pred = S1_pred_calc,
              s0 = s, s01 = s1, S = final_S, S.pred = final_S1, tau = convergence))
}


smcure.nn.Pois <- function(setting = NULL, formula = NULL, cureform = NULL,
                           offset = NULL, data, testdata,
                           na.action = na.omit, Var = T,
                           emmax = 1000, eps = 1e-3, nboot = 100) { # <-- CHANGE: Reduced default emmax
  
  start_t <- Sys.time()
  call <- match.call()
  
  data <- na.action(data)
  testdata <- na.action(testdata)
  
  mf <- model.frame(formula, data)
  mp <- model.frame(formula, testdata)
  Y <- model.extract(mf, "response")
  Y1 <- model.extract(mp, "response")
  Time <- Y[, 1]; Status <- Y[, 2]
  Time1 <- Y1[, 1]; Status1 <- Y1[, 2]
  Z <- model.matrix(cureform, data)
  Z1 <- model.matrix(cureform, testdata)
  X <- model.matrix(attr(mf, "terms"), mf)
  X1 <- model.matrix(attr(mp, "terms"), mp)
  nbeta <- ncol(X) - 1
  
  bnm <- colnames(Z); nb <- ncol(Z)
  betanm <- colnames(X)[-1]; nbeta <- ncol(X) - 1
  
  b <- rep(0.5, ncol(Z))
  beta <- rep(0.5, nbeta)
  
  Z_scaled_values <- scale(Z[, -1, drop = FALSE])
  center_vals <- attr(Z_scaled_values, "scaled:center")
  scale_vals <- attr(Z_scaled_values, "scaled:scale")
  Z1_scaled_values <- scale(Z1[, -1, drop = FALSE], center = center_vals, scale = scale_vals)
  
  set.seed(123)
  Z_scaled_df  <- as.data.frame(Z_scaled_values)
  Z1_scaled_df <- as.data.frame(Z1_scaled_values)
  ybin <- as.integer(Status == 1)
  tune_data <- cbind.data.frame(y = ybin, Z_scaled_df)
  k_folds <- 10
  
  pos <- which(ybin == 1); neg <- which(ybin == 0)
  fold_id_pos <- sample(rep(1:k_folds, length.out = length(pos)))
  fold_id_neg <- sample(rep(1:k_folds, length.out = length(neg)))
  folds <- lapply(1:k_folds, function(k) c(pos[fold_id_pos == k], neg[fold_id_neg == k]))
  
  
  hidden_grid <- list(c(2),c(4), c(8), c(16),c(4, 2), c(16, 8), c(32))
  #hidden_grid <- list(c(2), c(4), c(8), c(4, 2))
  stepmax_cv <- 5000
  
  cv_scores <- numeric(length(hidden_grid))
  for (h in seq_along(hidden_grid)) {
    ll <- numeric(k_folds)
    for (k in 1:k_folds) {
      idx_tr <- unlist(folds[-k]); idx_va <- folds[[k]]
      df_tr <- tune_data[idx_tr, , drop = FALSE]
      df_va <- tune_data[idx_va, , drop = FALSE]
      nn <- try(neuralnet::neuralnet(
        y ~ .,
        data = df_tr,
        hidden = hidden_grid[[h]],
        linear.output = FALSE,
        stepmax = stepmax_cv,
        threshold = 0.05,
        lifesign = "none"
      ), silent = TRUE)
      if (inherits(nn, "try-error") || is.null(nn$net.result)) { ll[k] <- NA_real_; next }
      cn <- colnames(nn$covariate)
      p_val <- as.numeric(neuralnet::compute(nn, df_va[, cn, drop = FALSE])$net.result)
      p_val <- pmin(pmax(p_val, 1e-6), 1 - 1e-6)
      ll[k] <- mean(df_va$y * log(p_val) + (1 - df_va$y) * log(1 - p_val))
    }
    cv_scores[h] <- mean(ll, na.rm = TRUE)
  }
  best_idx <- which.max(cv_scores)
  best_params <- hidden_grid[[best_idx]]
  
  final_nn <- try(neuralnet::neuralnet(
    y ~ .,
    data = tune_data,
    hidden = best_params,
    linear.output = FALSE,
    stepmax = 5000,
    threshold = 0.05,
    lifesign = "none"
  ), silent = TRUE)
  if (inherits(final_nn, "try-error") || is.null(final_nn$net.result)) {
    warning("Final NN training failed; using mean-prob initializer.")
    uncureprob <- rep(mean(ybin), length(ybin))
    uncurepred <- rep(mean(ybin), nrow(Z1_scaled_df))
  } else {
    cn <- colnames(final_nn$covariate)
    uncureprob <- as.numeric(neuralnet::compute(final_nn, Z_scaled_df[,  cn, drop = FALSE])$net.result)
    uncurepred <- as.numeric(neuralnet::compute(final_nn, Z1_scaled_df[, cn, drop = FALSE])$net.result)
    uncureprob <- pmin(pmax(uncureprob, 1e-6), 1 - 1e-6)
    uncurepred <- pmin(pmax(uncurepred, 1e-6), 1 - 1e-6)
  }
  
  
  coxfit_train <- coxph(Surv(Time, Status) ~ 1)
  coxfit_test <- coxph(Surv(Time1, Status1) ~ 1)
  
  out.data <- basehaz(coxfit_train, centered = FALSE)  # columns: hazard, time
  S0_grid <- exp(-out.data$hazard)
  t_grid  <- out.data$time
  
  out.data1 <- basehaz( coxfit_test, centered = FALSE)  # columns: hazard, time
  S01_grid <- exp(-out.data1$hazard)
  t_grid1  <- out.data1$time
  
  idx_tr <- pmax(1, findInterval(Time,  t_grid))
  idx_te <- pmax(1, findInterval(Time1, t_grid1))
  
  s0  <- S0_grid[idx_tr]   # length(Time)
  s01 <- S01_grid[idx_te]   # length(Time1)
  
  
  
  if(any(is.na(s0)))  s0[is.na(s0)]  <- min(s0,  na.rm = TRUE)
  if(any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  # >>> EDIT END
  
  
  if(any(is.na(s0))) s0[is.na(s0)] <- min(s0, na.rm = TRUE)
  if(any(is.na(s01))) s01[is.na(s01)] <- min(s01, na.rm = TRUE)
  
  # Add this inside smcure.nn.Pois before the emfit call:
  # cat("Z scaling check (Means):", colMeans(Z_scaled_values), "\n")
  #cat("Z scaling check (SDs):", apply(Z_scaled_values, 2, sd), "\n")
  
  # <-- CHANGE: Pass the stepmax_val variable to the function
  emfit <- em.nn.Pois(Time, Status, Time1, Status1, X, X1,
                      Z = cbind(1, Z_scaled_df), 
                      Z1 = cbind(1, Z1_scaled_df),
                      uncureprob = uncureprob, uncurepred = uncurepred,
                      beta = rep(0, ncol(X)-1), s0 = s0, s01 = s01,
                      emmax = emmax, eps = eps,
                      best_params = best_params, stepmax = 5000)
  
  
  beta.est = emfit$latencyfit
  #b.est = emfit$b
  UN<-emfit$UN
  PRED<-emfit$PRED
  Sp = emfit$Sp
  Sp.pred = emfit$Sp.pred
  S1 = emfit$S1
  S1.pred = emfit$S1.pred
  s0 = emfit$s0
  s01 = emfit$s01
  S = emfit$S
  S.pred = emfit$S.pred
  conv = emfit$tau
  
  if (Var) {
    # --- Bootstrap for latency coefficients and uncure probabilities (NN EM) ---
    n <- length(Status)
    
    uncure_boot  <- matrix(0, nrow = nboot, ncol = n)
    latency_boot <- matrix(0, nrow = nboot, ncol = nbeta)
    
    # Stratified bootstrap indices on TRAIN
    idx1 <- which(Status == 1)
    idx0 <- which(Status == 0)
    
    for (ib in 1:nboot) {
      id1 <- sample(idx1, length(idx1), replace = TRUE)
      id0 <- sample(idx0, length(idx0), replace = TRUE)
      boot_idx <- c(id1, id0)
      
      bootdata <- data[boot_idx, , drop = FALSE]
      
      # Rebuild bootstrap TRAIN objects
      mf_b <- model.frame(formula, bootdata)
      Y_b  <- model.extract(mf_b, "response")
      if (!inherits(Y_b, "Surv")) stop("Response must be a survival object")
      
      Time_b   <- Y_b[, 1]
      Status_b <- Y_b[, 2]
      
      X_b <- model.matrix(attr(mf, "terms"), mf_b)
      Z_b <- model.matrix(cureform, bootdata)
      
      # Scale Z on bootstrap TRAIN; apply to fixed TEST
      Zb_scaled <- scale(Z_b[, -1, drop = FALSE])
      ctr_b <- attr(Zb_scaled, "scaled:center")
      scl_b <- attr(Zb_scaled, "scaled:scale")
      Z1b_scaled <- scale(Z1[, -1, drop = FALSE], center = ctr_b, scale = scl_b)
      
      Z_b_scaled  <- cbind(1, Zb_scaled)
      Z1_b_scaled <- cbind(1, Z1b_scaled)
      
      # Baseline survival init for bootstrap TRAIN at Time_b
      coxfit_b <- survival::coxph(survival::Surv(Time_b, Status_b) ~ 1)
      s0_b <- summary(survival::survfit(coxfit_b), times = Time_b, extend = TRUE)$surv
      if (any(is.na(s0_b))) s0_b[is.na(s0_b)] <- min(s0_b, na.rm = TRUE)
      
      # Fast incidence initializer (GLM on bootstrap TRAIN)
      glm_df_b <- cbind.data.frame(y = as.integer(Status_b == 1), as.data.frame(Zb_scaled))
      glm_fit_b <- tryCatch(glm(y ~ ., data = glm_df_b, family = binomial()), error = function(e) NULL)
      
      if (is.null(glm_fit_b)) {
        uncureprob_b <- rep(mean(Status_b == 1), length(Status_b))
        uncurepred_b <- rep(mean(Status_b == 1), length(Status1))
      } else {
        uncureprob_b <- as.numeric(predict(glm_fit_b, type = "response"))
        uncurepred_b <- as.numeric(predict(glm_fit_b, newdata = as.data.frame(Z1b_scaled), type = "response"))
      }
      
      uncureprob_b <- pmin(pmax(uncureprob_b, 1e-6), 1 - 1e-6)
      uncurepred_b <- pmin(pmax(uncurepred_b, 1e-6), 1 - 1e-6)
      
      # Initialize beta from main EM fit if available
      beta_init_b <- emfit$latencyfit
      if (is.null(beta_init_b) || any(is.na(beta_init_b)) || length(beta_init_b) != (ncol(X_b) - 1)) {
        beta_init_b <- rep(0.5, ncol(X_b) - 1)
      }
      
      # Fit NN-EM on bootstrap TRAIN; keep TEST fixed
      bootfit <- em.nn.Pois(
        Time_b, Status_b, Time1, Status1,
        X_b, X1,
        Z = Z_b_scaled, Z1 = Z1_b_scaled,
        uncureprob = uncureprob_b,
        uncurepred = uncurepred_b,
        beta = beta_init_b,
        s0 = s0_b,
        s01 = NULL,
        emmax = emmax,
        eps = eps,
        best_params = best_params,
        stepmax = stepmax
      )
      
      latency_boot[ib, ] <- bootfit$latencyfit
      uncure_boot[ib, ]  <- as.numeric(bootfit$UN)
    }
    
    latency_var <- apply(latency_boot, 2, var)
    latency_sd  <- sqrt(latency_var)
    
    uncure_var <- apply(uncure_boot, 2, var)
    uncure_sd  <- sqrt(uncure_var)
    
    # CI around the main EM uncure probabilities
    
    lower_uncure <- as.numeric(emfit$UN) - 1.96 * uncure_sd
    upper_uncure <-as.numeric(emfit$UN) + 1.96 * uncure_sd
    
    # clamp to [0, 1]
    lower_uncure <- pmax(0, lower_uncure)
    upper_uncure <- pmin(1, upper_uncure)
  }
  fit<-list()
  class(fit) <- c("smcure.nn.Pois")
  
  fit$latency <- beta.est
  if(Var){
    fit$latency_var <- latency_var
    fit$latency_sd <- latency_sd
    fit$latency_zvalue <- fit$latency/latency_sd
    fit$latency_pvalue <- (1-pnorm(abs(fit$latency_zvalue)))*2
    fit$lower_uncure = lower_uncure
    fit$upper_uncure = upper_uncure}
  cat(" done.\n")
  fit$call <- call
  fit$bnm <- bnm
  fit$betanm <- betanm
  fit$UN<- UN
  fit$PRED<- PRED
  # fit$b <- b.est
  fit$Sp = Sp
  fit$Sp.pred = Sp.pred
  fit$S1 = S1
  fit$S1.pred = S1.pred
  fit$s0 = s0
  fit$s01 = s01
  fit$S = S
  fit$S.pred = S.pred
  fit$tau = conv
  return(fit)
  
}

























# =============================================================================
# SIMULATION SCRIPT
# =============================================================================




M <- 300  # Number of Monte Carlo replications
g <- 400   # Training set size
m <- 200   # Test set size

methods <- c("logit", "spline", "dt", "svm", "nn", "xgb","rf") 

settingop<-c(1,2,3)
all_settings_results <- list()

# --- NEW: holders for true generation-time proportions per setting ---
true_props <- vector("list", 3)
for (s in settingop) true_props[[s]] <- data.frame(
  run = integer(),
  Cured_Prop = numeric(),
  Censor_Overall = numeric(),
  Censor_Among_Susceptible = numeric(),
  Event_Overall = numeric()
)

get_simulation_params <- function(setting) {
  switch(as.character(setting),
         "1" = list(beta = c(1, 0.5), alpha = 2, delta = 0.2),
         "2" =  list(beta = c(1, 0.5), alpha = 2, delta = 0.2),
         # "3" = list(beta = c(1, 0.5), alpha = 2, delta = 0.20),
         "3" = list(beta = c(1.5, 0.5, 1.3, -0.6, -1.4), alpha = 0.2, delta = 0.2),
         stop("Unsupported setting")
  )
}



#

# --- NEW: Added robust helper function for AUC ---
extract_auc <- function(results, model, type) {
  sapply(results, function(x) {
    value <- x$auc[[model]][[type]]
    if (is.null(value)) return(NA)
    return(value)
  })
}
#--- NEW: Added robust helper function for all metrics (Bias and MSE) ---
extract_metric <- function(results, model, metric_type, train_test, metric_name) {
  sapply(results, function(x) {
    value <- x[[metric_type]][[model]][[train_test]][[metric_name]]
    if (is.null(value)) return(NA)
    return(value)
  })
}

for (current_setting in settingop) {
  
  
  #setting_start_time <- Sys.time()
  
  cat("\n====================================================\n")
  cat("STARTING SIMULATION FOR SETTING:", current_setting, "\n")
  cat("====================================================\n")
  results_per_setting <- list()
  
  for (r in 1:M) {
    cat("\nSimulation run:", r, "for setting:", current_setting, "\n")
    set.seed(250 + r)
    
    params <- get_simulation_params(current_setting)
    data_all <- data.Pois(n = g + m, alpha = params$alpha, beta = params$beta, delta = params$delta, setting = current_setting)
    
    # --- NEW: record truth from the generator (full sample, no leakage) ---
    cured_overall   <- mean(data_all$J == 0)
    censor_overall  <- mean(data_all$D == 0)
    susc_prop       <- mean(data_all$J == 1)
    censor_given_J1 <- if (susc_prop > 0) mean(data_all$D == 0 & data_all$J == 1) / susc_prop else NA_real_
    event_overall   <- mean(data_all$D == 1)
    true_props[[current_setting]] <- rbind(true_props[[current_setting]],
                                           data.frame(run = r,
                                                      Cured_Prop = cured_overall,
                                                      Censor_Overall = censor_overall,
                                                      Censor_Among_Susceptible = censor_given_J1,
                                                      Event_Overall = event_overall))
    split <- sample.split(data_all$J, SplitRatio = g / (g + m))
    trainingdata <- subset(data_all, split == TRUE)
    test <- subset(data_all, split == FALSE)
    
    
    
    # Define formulas based on setting
    #surv is for latency and cure is for incidence
    if (current_setting == c(1)) {
      surv_formula <- as.formula("Surv(Y, D) ~ z1 + z2")
      cure_formula <- as.formula("~ z1 + z2")
    } else if (current_setting == c(2)) {
      surv_formula <- as.formula("Surv(Y, D) ~ z1 + z2 ")
      # Use engineered features for simpler models
      cure_formula <- as.formula("~ z1 + z2")
      # } else if (current_setting == 3) {
      #  surv_formula <- as.formula("Surv(Y, D) ~ z1 + z2")
      # cure_formula <- as.formula("~ z1 + z2") # No simple features for trig functions
    } else if (current_setting == c(3)) {
      surv_formula <- as.formula("Surv(Y, D) ~ z2 + z4 + z8 + z6 + z10")
      # Use engineered features for simpler models
      cure_formula <- as.formula("~ z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8 + z9 + z10 ")
    }
    
    
    auc_results <- list()
    bias_results <- list()
    absolute_bias_results <- list()
    mse_results <- list()
    #runtime_results <- list()
    
    for (method_name in methods) {
      cat("Running method:", method_name, "\n")
      
      # Use basic formula for tree-based models as they can find interactions
      current_cure_formula <- cure_formula
      
      
      func <- get(paste0("smcure.", method_name, ".Pois"))
      
      #start_time <- Sys.time()
      out <- tryCatch({
        func(formula = surv_formula, cureform = current_cure_formula, data = trainingdata, testdata = test, Var = F)
      }, error = function(e) {
        warning(sprintf("Method %s failed in run %d for setting %d: %s", method_name, r, current_setting, e$message))
        NULL
      })
      
      if (!is.null(out)) {
        
        auc_results[[method_name]] <- list(
          trainingdata = as.numeric(roc(factor(trainingdata$J) ~ as.numeric(out$UN), auc = TRUE, quiet=TRUE)$auc),
          test = as.numeric(roc(factor(test$J) ~ as.numeric(out$PRED), auc = TRUE, quiet=TRUE)$auc)
        )
        
       
        # --- Test Set Metrics ---
        bias_test <- list(
          uncure = mean(out$UN - trainingdata$uncure),
          Sp     = mean(out$Sp - trainingdata$Sp, na.rm=T),
          S1     = mean(out$S1 - trainingdata$S1, na.rm=T),
          S      = mean(out$S - trainingdata$S, na.rm=T)     # <--- Corrected
        )
        
        abs_bias_test <- list(
          uncure = mean(abs(out$UN - trainingdata$uncure)),
          Sp     = mean(abs(out$Sp - trainingdata$Sp), na.rm=T),
          S1     = mean(abs(out$S1- trainingdata$S1), na.rm=T),
          S      = mean(abs(out$S - trainingdata$S), na.rm=T) # <--- Corrected
        )
        
        mse_test <- list(
          uncure = mean((out$UN - trainingdata$uncure)^2),
          Sp     = mean((out$Sp - trainingdata$Sp)^2, na.rm=T),
          S1     = mean((out$S1 - trainingdata$S1)^2, na.rm=T),
          S      = mean((out$S - trainingdata$S)^2, na.rm=T)  # <--- Corrected
        )
        
        # Store results in a nested list
        bias_results[[method_name]] <- list(testresult = bias_test )
        absolute_bias_results[[method_name]] <- list(testresult = abs_bias_test )
        mse_results[[method_name]] <- list(testresult = mse_test )
      }
    }
    
    results_per_setting[[r]] <- list(auc = auc_results, bias = bias_results, absoluteBias = absolute_bias_results, mse = mse_results)
  }
  
  all_settings_results[[current_setting]] <- results_per_setting
  
  
}


# --- Summarize and Print Results for Each Setting ---
for (current_setting in settingop) {
 
  
  cat("\n\n--- RESULTS FOR SETTING", current_setting, "---\n")
  
  results <- all_settings_results[[current_setting]]
  
  # The individual assignment loops are no longer needed as logic is moved into the table creation
  
  results_table <- data.frame(
    Metric = c("Bias (Test): Uncure", "Abs. Bias (Test): Uncure", "MSE (Test): Uncure",
               "Bias (Test): Sp(t)", "Abs. Bias (Test): Sp(t)", "MSE (Test): Sp(t)",
               "Bias (Test): S1(t)", "Abs. Bias (Test): S1(t)", "MSE (Test): S1(t)",
               "Bias (Test): S(t)", "Abs. Bias (Test): S(t)", "MSE (Test): S(t)",
               "AUC (Train)", "AUC (Test)")#, "Runtime (s)"
  )
  
  for (model in methods) {
    results_table[[toupper(model)]] <- c(
      mean(extract_metric(results, model, "bias", "testresult", "uncure"), na.rm = TRUE),
      mean(extract_metric(results, model, "absoluteBias", "testresult", "uncure"), na.rm = TRUE),
      mean(extract_metric(results, model, "mse", "testresult", "uncure"), na.rm = TRUE),
      
      mean(extract_metric(results, model, "bias", "testresult", "Sp"), na.rm = TRUE),
      mean(extract_metric(results, model, "absoluteBias", "testresult", "Sp"), na.rm = TRUE),
      mean(extract_metric(results, model, "mse", "testresult", "Sp"), na.rm = TRUE),
      
      mean(extract_metric(results, model, "bias", "testresult", "S1"), na.rm = TRUE),
      mean(extract_metric(results, model, "absoluteBias", "testresult", "S1"), na.rm = TRUE),
      mean(extract_metric(results, model, "mse", "testresult", "S1"), na.rm = TRUE),
      
      mean(extract_metric(results, model, "bias", "testresult", "S"), na.rm = TRUE),
      mean(extract_metric(results, model, "absoluteBias", "testresult", "S"), na.rm = TRUE),
      mean(extract_metric(results, model, "mse", "testresult", "S"), na.rm = TRUE),
      
      mean(extract_auc(results, model, "trainingdata"), na.rm = TRUE),
      mean(extract_auc(results, model, "test"), na.rm = TRUE)
      #sum(extract_runtime(results, model), na.rm = TRUE)
    )
  }
  
  # Apply rounding to 4 decimal places for all numeric columns
  for (col_name in toupper(methods)) {
    if (col_name %in% colnames(results_table)) {
      results_table[[col_name]] <- round(results_table[[col_name]], 4)
    }
  }
  
  
  print(results_table)
  
  
  # --- NEW: summarize true proportions for this setting (mean ± MC SE) ---
  tp <- true_props[[current_setting]]
  se <- function(x) sd(x, na.rm=TRUE)/sqrt(length(na.omit(x)))
  summary_props <- data.frame(
    Setting = current_setting,
    Cured_Prop_mean = mean(tp$Cured_Prop),   Cured_Prop_se = se(tp$Cured_Prop),
    Censor_Overall_mean = mean(tp$Censor_Overall), Censor_Overall_se = se(tp$Censor_Overall),
    Censor_Among_Susceptible_mean = mean(tp$Censor_Among_Susceptible, na.rm=TRUE),
    Censor_Among_Susceptible_se = se(tp$Censor_Among_Susceptible),
    Event_Overall_mean = mean(tp$Event_Overall), Event_Overall_se = se(tp$Event_Overall)
  )
  summary_props[,-1] <- lapply(summary_props[,-1], function(x) round(x, 4))
  cat("
True generation-time proportions (means ± MC SE) for setting", current_setting, ":
")
  print(summary_props)
  
  
  
}
time_taken <- proc.time() - ptm
time_taken




