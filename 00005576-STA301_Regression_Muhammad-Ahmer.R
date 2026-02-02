##################################
# LIBRARY INSTALLMENTS & IMPORTs #
##################################

install.packages(c(
  "dplyr", "purrr", "tibble", "ggplot2", "viridis", "Amelia", "readr",
  "car", "e1071", "nortest", "lmtest", "MASS", "pracma", "GGally"
))


library(dplyr)
library(purrr)
library(tibble)
library(ggplot2)
library(viridis)
library(Amelia)
library(readr)
library(car)
library(e1071)
library(nortest)
library(lmtest)
library(car)
library(MASS)
library(pracma)
library(GGally)
library(dplyr)
library(splines)



##############################
# DATA & DATA PRE-PROCESSING #
##############################

set.seed(87698) # ID for static sampling, to ensure consistent results

# Data Importing & Header Management
data <- read.csv("rideshare_kaggle.csv", header=FALSE, skip=1)
header <- read.csv("rideshare_kaggle.csv", header = FALSE, nrows = 1)
colnames(data) <- header
head(data)

# Removing Missing Values
cleaned_data <- data %>% filter(!is.na(price))

# Pre-Analysis Manual Feature Selection (Discussed in Report)
columns_to_remove <- c(
  "id",
  "timestamp",
  "datetime",
  "timezone",
  "product_id",
  "temperatureHighTime",
  "temperatureLowTime",
  "apparentTemperatureHighTime",
  "apparentTemperatureLowTime",
  "visibility.1",
  "uvIndexTime",
  "temperatureMinTime",
  "temperatureMaxTime",
  "apparentTemperatureMinTime",
  "windGustTime",
  "apparentTemperatureMaxTime"
)

# Sampling Method: every hour of every day of every mont available in the dataset, we will take X=32 records from
cleaned_data <- cleaned_data[, !(names(cleaned_data) %in% columns_to_remove)]
cleaned_data$combined <- paste(cleaned_data$month, cleaned_data$day, cleaned_data$hour, sep = "-")
print(cleaned_data$combined)

# "X" is selected to make it as close to the 10k requirement. Large data was found to give poorer results.
# Will be changed in the report 
X <- 32
equal_samples_df <- data.frame()
unique_combined_values <- unique(cleaned_data$combined)
for (value in unique_combined_values) {
  subset_data <- cleaned_data[cleaned_data$combined == value, ]
    if (nrow(subset_data) > X) {
    sampled_data <- subset_data[sample(1:nrow(subset_data), X), ]
  } else {
    sampled_data <- subset_data
  }
  equal_samples_df <- rbind(equal_samples_df, sampled_data)
}



sampled_data <- equal_samples_df
dim(sampled_data)

# Will not be used, but here for reference.
full_data <- cleaned_data
dim(full_data)

#####################################################
# FUNCTIONS FOR MODEL BUILDING & EVALUATION SECTION #
#####################################################

# Five Assumption Check
check_normality <- function(model, alpha = 0.05) {
  
  residuals <- resid(model)
  
  cat("---- NORMALITY CHECK ----\n")
  cat("\nHo: Residuals are normal\n")
  cat("Ha: Residuals are NOT normal\n")
  
  # Skewness
  skew_val <- skewness(residuals)
  cat("Skewness: ", skew_val, "\n")
  
  # Anderson-Darling Test
  ad_p <- ad.test(residuals)$p.value
  cat("Anderson-Darling Test: p-value = ", ad_p, "\n")
  cat(ifelse(ad_p > alpha, "Decision: Normality NOT violated\n\n", "Decision: Normality MAY BE violated\n\n"))
  
  # Kolmogorov-Smirnov Test
  ks_p <- ks.test(residuals, "pnorm", mean = mean(residuals), sd = sd(residuals))$p.value
  cat("Kolmogorov-Smirnov Test: p-value = ", ks_p, "\n")
  cat(ifelse(ks_p > alpha, "Decision: Normality NOT violated\n\n", "Decision: Normality MAY BE violated\n\n"))
  
  # Manual Check: Correlation on Normal Probability Plot
  n <- length(residuals)
  MSE <- sum(residuals^2) / model$df.residual
  sqrt_MSE <- sqrt(MSE)
  ranks <- rank(residuals, ties.method = "average")
  P <- (ranks - 0.375) / (n + 0.25)
  expected <- sqrt_MSE * qnorm(P)
  corr_val <- cor(residuals, expected)
  cat("Normal Probability Plot Correlation: ", corr_val, "\n")
  cat(ifelse(corr_val > 0.95, "Decision: Normality NOT violated\n", "Decision: Normality MAY BE violated\n"))
  cat("\n")
}
check_constant_variance <- function(model, alpha = 0.05) {
  library(lmtest)
  library(car)
  
  residuals <- resid(model)
  fitted_vals <- fitted(model)
  
  cat("---- CONSTANT VARIANCE CHECK ----\n")
  
  group <- ifelse(fitted_vals > median(fitted_vals), "High", "Low")
  
  cat("\nHo: The variances are equal across the groups.\n")
  cat("Ha: The variances are not equal across the groups.\n")
  ## Brown-Forsythe Test
  bf_model <- lm(abs(residuals) ~ group)
  bf_p <- summary(aov(bf_model))[[1]]$`Pr(>F)`[1]
  cat("Brown-Forsythe Test: p-value = ", bf_p, "\n")
  if (length(bf_p) == 1 && bf_p > alpha) {
    cat("Decision: Constant variance NOT violated (Brown-Forsythe)\n\n")
  } else {
    cat("Decision: Constant variance MAY BE violated (Brown-Forsythe)\n\n")
  }
  
  
  cat("Ho: The two groups have equal variances.\n")
  cat("Ha: The two groups have different variances.\n")
  ## Variance Test
  var_p <- var.test(residuals[group == "High"], residuals[group == "Low"])$p.value
  cat("Variance Test (Assuming Normal Residuals): p-value = ", var_p, "\n")
  if (var_p > alpha) {
    cat("Decision: Constant variance NOT violated (Variance Test)\n\n")
  } else {
    cat("Decision: Constant variance MAY BE violated (Variance Test)\n\n")
  }
  
  
  levene_test_result <- leveneTest(residuals ~ group)
  levene_p <- levene_test_result$`Pr(>F)`[1]
  cat("Levene's Test: p-value = ", levene_p, "\n")
  if (length(levene_p) == 1 && levene_p > alpha) {
    cat("Decision: Constant variance NOT violated (Levene's Test)\n\n")
  } else {
    cat("Decision: Constant variance MAY BE violated (Levene's Test)\n\n")
  }
}
check_equal_mean <- function(model, alpha = 0.05) {
  residuals <- resid(model)
  fitted_vals <- fitted(model)
  
  cat("---- EQUAL MEAN CHECK ----\n")
  
  group <- ifelse(fitted_vals > median(fitted_vals), "High", "Low")
  mean_res <- mean(residuals)
  ttest_p <- t.test(residuals[group == "High"], residuals[group == "Low"])$p.value
  
  
  cat("  H0: Mean of residuals = 0\n")
  cat("  Ha: Mean of residuals ≠ 0\n")
  
  # Mean of residuals
  cat("Mean of residuals: ", mean_res, "\n")
  if (abs(mean_res) < 1e-5) {
    cat("Decision: Equal mean NOT violated\n\n")
  } else {
    cat("Decision: Equal mean MAY BE violated\n\n")
  }
  
  # t-Test for equal means
  cat("t-Test for Equal Means: p-value = ", ttest_p, "\n")
  if (ttest_p > alpha) {
    cat("Decision: Equal mean NOT violated\n\n")
  } else {
    cat("Decision: Equal mean MAY BE violated\n\n")
  }
  
}
check_independence <- function(model, alpha = 0.05) {
  residuals <- resid(model)
  fitted_vals <- fitted(model)
  
  cat("---- INDEPENDENCE CHECK ----\n")
  
  cat("  Ho: No autocorrelation (independent residuals)\n")
  cat("  Ha: Autocorrelation present\n")
  dw_p <- durbinWatsonTest(model)$p
  cat("Durbin-Watson Test: p-value = ", dw_p, "\n")
  
  if (dw_p > alpha) {
    cat("Decision: Independence NOT violated\n\n")
  } else {
    cat("Decision: Independence MAY BE violated\n\n")
  }
  
}
check_linearity <- function(model) {
  residuals <- resid(model)
  fitted_vals <- fitted(model)
  
  cat("---- LINEARITY CHECK ----\n")
  
  cat("Ho: The model is linear.\n")
  cat("Ha: The model is NOT linear.\n")
  loess_fit <- loess(residuals ~ fitted_vals)
  loess_vals <- predict(loess_fit)
  curvature <- sd(loess_vals)
  
  cat("Curvature of loess fit: ", curvature, "\n")
  
  if (curvature < 0.05 * sd(residuals)) {
    cat("Decision: Linearity NOT violated (loess is mostly flat)\n\n")
  } else {
    cat("Decision: Linearity MAY BE violated (loess shows curvature)\n\n")
  }
  
  plot(fitted_vals, residuals, 
       xlab = "Fitted Values", ylab = "Residuals",
       main = "Linearity Check: Residuals vs Fitted")
  abline(h = 0, col = "red")
  lines(sort(fitted_vals), loess_vals[order(fitted_vals)], col = "blue", lwd = 2)
}

# Data & Result Processing
remove_outliers <- function(df, severity = 1.5) {
  for (col in names(df)) {
    if (is.numeric(df[[col]])) {
      Q1 <- quantile(df[[col]], 0.25, na.rm = TRUE)
      Q3 <- quantile(df[[col]], 0.75, na.rm = TRUE)
      IQR_val <- Q3 - Q1
      lower_bound <- Q1 - severity * IQR_val
      upper_bound <- Q3 + severity * IQR_val
      df <- df[df[[col]] >= lower_bound & df[[col]] <= upper_bound, ]
    }
  }
  return(df)
}
vif_manual <- function(model) {
  X <- model.matrix(model)[, -1]
  vif_vals <- sapply(1:ncol(X), function(i) {
    r2 <- suppressWarnings(summary(lm(X[, i] ~ X[, -i]))$r.squared)
    if (r2 == 1) NA else round(1 / (1 - r2), 2)
  })
  names(vif_vals) <- colnames(X)
  vif_vals
}
model_summary <- function(model) {
  s <- round(sigma(model), 6)
  rsq <- summary(model)$r.squared
  adj_rsq <- summary(model)$adj.r.squared
  pred_rsq <- calculate_R2_predicted(model, test_data, "none")
  
  cat("Model Summary\n")
  cat("S       R-sq   R-sq(adj)   R-sq(pred)\n")
  cat(sprintf("%.6f  %.2f%%   %.2f%%      %.2f%%\n",
              s, rsq * 100, adj_rsq * 100, pred_rsq * 100))
}


# Temporary R^2 Predicted Function, it works, but its a mess, better one used at the end
calculate_R2_predicted <- function(model, test_data, transformation = c("none", "sqrt_plus10", "log_squared", "boxcox"), lambda = NULL) {
  transformation <- match.arg(transformation)
  predicted_transformed <- predict(model, newdata = test_data)
  
  predicted <- switch(transformation,
                      "sqrt_plus10" = (predicted_transformed)^2 - 10,
                      "log_squared" = (predicted_transformed)^2,
                      "boxcox" = if (!is.null(lambda)) {
                        if (lambda == 0) exp(predicted_transformed) else (lambda * predicted_transformed + 1)^(1 / lambda)
                      } else {
                        stop("Lambda must be provided for Box-Cox back-transformation.")
                      },
                      "none" = predicted_transformed
  )
  
  actual <- test_data$price
  residuals <- actual - predicted
  tss <- sum((actual - mean(actual))^2)
  press <- sum(residuals^2)
  r_squared_pred <- 1 - (press / tss)
  
  return(round(r_squared_pred, 4))
}



set.seed(87698)

####################################################################################################
# SECTION 3.3.2: INITIAL LINEAR REGRESSION MODEL FITTING (NO FEATURE SELECTION, NO TRANSFORMATION) #
####################################################################################################

# Train-Test Split (70-30 Train-Test)
train_index <- sample(1:nrow(sampled_data), size = 0.7 * nrow(sampled_data))

# Split the data
train_data <- sampled_data[train_index, ]
test_data <- sampled_data[-train_index, ]

# Check the dimensions to confirm the split
cat("Training set dimensions: ", dim(train_data), "\n")
cat("Test set dimensions: ", dim(test_data), "\n")

# Renaming Training Data to "rideshare" for consistency with the remaining code
rideshare <- train_data 

# Combined was used for the "uniform" sampling, we do not need it anymore as it is an aggregate of three predictors
# Keeping it most likely would make multicollinearity, and would significantly increase the dimensionality
rideshare <- subset(rideshare, select = -combined)

# Section 3.3.2
model_basic <- lm(price ~ .,
                  data = rideshare)

anova(model_basic)
summary(model_basic)
model_summary(model_basic)
calculate_R2_predicted(model_basic, test_data, "none")
vif_manual(model_basic)


## LACK OF FIT TEST (SATURATED vs. FULL)

model_reduced <- lm(price ~ hour + day + month + source + destination + cab_type + 
                      distance + surge_multiplier + latitude + longitude, data = rideshare)

# Compare both models using ANOVA
lack_of_fit_test <- anova(model_reduced, model_basic)

# Output the result
print(lack_of_fit_test)






#####################
# MODEL ASSUMPTIONS #
#####################

# NOTE: this section cannot be done in a function, as it will overlap graphs, but I acknowledge that it is repetitive. 

# QQ-Plot
residuals <- resid(model_basic)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(model_basic)
plot_data <- data.frame(residuals = residuals(model_basic), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(model_basic)
check_constant_variance(model_basic)
check_equal_mean(model_basic)
check_independence(model_basic)
check_linearity(model_basic)



#####################################################################################
# SECION 3.3.3: INITIAL LINEAR REGRESSION MODEL FITTING (BOX-COX & OUTLIER REMOVAL) #
#####################################################################################

# Training data outlier removal, 1.5 is severity-level, which is the standard level
rideshare_outliers <- remove_outliers(rideshare, 1.5)
test_data_outliers <- remove_outliers(test_data, 1.5)

library(MASS)

bc <- boxcox(model_basic, lambda = seq(-2, 2, 0.1))
best_lambda <- bc$x[which.max(bc$y)]
cat("Best lambda:", best_lambda, "\n")

if (best_lambda == 0) {
  rideshare_outliers$price_bc <- log(rideshare_outliers$price)
} else {
  rideshare_outliers$price_bc <- (rideshare_outliers$price^best_lambda - 1) / best_lambda
}

# Section 3.3.3
model_bc <- lm(price_bc ~ . -price,
               data = rideshare_outliers)

summary(model_bc)
#model_summary(model_bc)
anova(model_bc)
#vif_manual(model_bc)
calculate_R2_predicted(model_bc, test_data_outliers, "boxcox", best_lambda)


# Because of Multicollinearity, we will perform Post-Analysis Manual Feature Selection
model_bc <- lm(price_bc ~ . 
               - price 
               - month 
               - destination 
               - cab_type 
               - temperature 
               - short_summary 
               - long_summary 
               - humidity 
               - temperatureLow 
               - dewPoint 
               - pressure 
               - uvIndex 
               - ozone 
               - sunriseTime 
               - moonPhase 
               - apparentTemperatureMax
               - apparentTemperatureMin
               - temperatureMin
               - sunsetTime
               - windBearing
               - apparentTemperatureLow
               - precipProbability
               - precipIntensity
               - apparentTemperatureHigh
               - temperatureMax,
               data = rideshare_outliers)

vif_manual(model_bc)
calculate_R2_predicted(model_bc, test_data_outliers, "boxcox", best_lambda)


#####################
# MODEL ASSUMPTIONS #
#####################


# QQ-Plot
residuals <- resid(model_bc)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(model_bc)
plot_data <- data.frame(residuals = residuals(model_bc), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(model_bc)
check_constant_variance(model_bc)
check_equal_mean(model_bc)
check_independence(model_bc)
check_linearity(model_bc)





###############################################################################
# SECTION 3.3.4: MODEL RE-FITTING (WITH LOG(Y+k), SQRT(Y+k), OUTLIER REMOVAL) #
###############################################################################

library(pracma)

rideshare_outliers <- remove_outliers(rideshare, 1.45)
test_data_outliers <- remove_outliers(test_data, 1.45)

model_transformed_sqrt <- lm(nthroot((price+10), 2) ~ .
                             - month 
                             - destination 
                             - cab_type 
                             - temperature 
                             - short_summary 
                             - long_summary 
                             - humidity 
                             - temperatureLow 
                             - dewPoint 
                             - pressure 
                             - uvIndex 
                             - ozone 
                             - sunriseTime 
                             - moonPhase 
                             - apparentTemperatureMax
                             - apparentTemperatureMin
                             - temperatureMin
                             - sunsetTime
                             - windBearing
                             - apparentTemperatureLow
                             - precipProbability
                             - precipIntensity
                             - apparentTemperatureHigh
                             - temperatureMax
                             - cloudCover,
               data = rideshare_outliers)


summary(model_transformed_sqrt)
anova(model_transformed_sqrt)
calculate_R2_predicted(model_transformed_sqrt, test_data_outliers, "sqrt_plus10")
vif_manual(model_transformed_sqrt)

#####################
# MODEL ASSUMPTIONS #
#####################


# QQ-Plot
residuals <- resid(model_transformed_sqrt)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(model_transformed_sqrt)
plot_data <- data.frame(residuals = residuals(model_transformed_sqrt), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(model_transformed_sqrt)
check_constant_variance(model_transformed_sqrt)
check_equal_mean(model_transformed_sqrt)
check_independence(model_transformed_sqrt)
check_linearity(model_transformed_sqrt)





###################################################################
# SECTION 3.3.5: MODEL RE-FITTING (WLS, PREDICTOR TRANSFORMATION) #
###################################################################

rideshare_outliers <- remove_outliers(rideshare, 1.5)
test_data_outliers <- remove_outliers(test_data, 1.5)

# Predictor Transformations (Remedy for Linearity)
rideshare_outliers$price_transformed <- log(rideshare_outliers$price + 10)
rideshare_outliers$distance_log <- log(rideshare_outliers$distance)
rideshare_outliers$temperatureHigh_log <- log(rideshare_outliers$temperatureHigh + 1)

# Initial Model, used to gather variance for weights
model_ols <- lm(price_transformed ~ .
                - temperatureHigh
                - distance
                - price
                - month 
                - destination 
                - cab_type 
                - temperature 
                - short_summary 
                - long_summary 
                - humidity 
                - temperatureLow 
                - dewPoint 
                - pressure 
                - uvIndex 
                - ozone 
                - sunriseTime 
                - moonPhase 
                - apparentTemperatureMax
                - apparentTemperatureMin
                - temperatureMin
                - sunsetTime
                - windBearing
                - apparentTemperatureLow
                - precipProbability
                - precipIntensity
                - apparentTemperatureHigh
                - temperatureMax
                - cloudCover,
                data = rideshare_outliers)

residuals_squared <- residuals(model_ols)^2
fitted_vals <- fitted(model_ols)
variance_model <- lm(log(residuals_squared) ~ log(fitted_vals))
log_variance <- predict(variance_model)
weights <- 1 / exp(log_variance)


model_WLS <- lm(price_transformed ~ .
                - temperatureHigh
                - distance
                - price
                - month 
                - destination 
                - cab_type 
                - temperature 
                - short_summary 
                - long_summary 
                - humidity 
                - temperatureLow 
                - dewPoint 
                - pressure 
                - uvIndex 
                - ozone 
                - sunriseTime 
                - moonPhase 
                - apparentTemperatureMax
                - apparentTemperatureMin
                - temperatureMin
                - sunsetTime
                - windBearing
                - apparentTemperatureLow
                - precipProbability
                - precipIntensity
                - apparentTemperatureHigh
                - temperatureMax
                - cloudCover,
                data = rideshare_outliers, weights = weights)


summary(model_WLS)
anova(model_WLS)
vif_manual(model_WLS)


#####################
# MODEL ASSUMPTIONS #
#####################


# QQ-Plot
residuals <- resid(model_WLS)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(model_WLS)
plot_data <- data.frame(residuals = residuals(model_WLS), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")


# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(model_WLS)
check_constant_variance(model_WLS)
check_equal_mean(model_WLS)
check_independence(model_WLS)
check_linearity(model_WLS)





#################################################################################
# MODEL RE-FITTING (POLYNOMIAL REGRESSION, SPLINE REGRESSION, INTERACTING TERMS #
#################################################################################

library(GGally)
library(dplyr)


selected_predictors <- c(
  "temperatureHigh", 
  "hour", "windGust", "distance", "longitude", "latitude"
)

predictor_data <- dplyr::select(as.data.frame(rideshare_outliers), all_of(selected_predictors))

ggpairs(predictor_data,
        upper = list(continuous = wrap("cor", size = 3)),
        lower = list(continuous = wrap("smooth", alpha = 0.3, size = 0.1)),
        diag = list(continuous = wrap("barDiag", bins = 20))) +
  theme_minimal(base_size = 12)


library(splines)

poly_model <- lm(
  sqrt(price + 10) ~ 
    name + source + icon + surge_multiplier +
    ns(temperatureHigh, df = 2) +
    ns(windGust, df = 2):ns(hour, df = 2) +  
    ns(temperatureHigh, df=2):ns(hour, df=2) +
    ns(latitude, df = 2):ns(longitude, df = 2),
  
  data = rideshare_outliers
)




summary(poly_model)
anova(poly_model)
calculate_R2_predicted(poly_model, test_data_outliers, "sqrt_plus10")
vif_manual(poly_model)

#####################
# MODEL ASSUMPTIONS #
#####################


# QQ-Plot
residuals <- resid(poly_model)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(poly_model)
plot_data <- data.frame(residuals = residuals(poly_model), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(poly_model)
check_constant_variance(poly_model)
check_equal_mean(poly_model)
check_independence(poly_model)
check_linearity(poly_model)





###########################
# MODEL RE-FITTING (WLS + POLYNOMIAL) #
###########################


#####################
# MODEL ASSUMPTIONS #
#####################


library(MASS)
library(splines)

base_model <- lm(
  price ~ 
    name + source + icon + surge_multiplier +
    ns(temperatureHigh, df = 2) +
    ns(windGust, df = 2):ns(hour, df = 2) +  
    ns(temperatureHigh, df=2):ns(hour, df=2) +
    ns(latitude, df = 2):ns(longitude, df = 2),
  data = rideshare_outliers
)

boxcox_result <- boxcox(base_model, lambda = seq(-2, 2, 0.1), plotit = TRUE)
best_lambda_2 <- boxcox_result$x[which.max(boxcox_result$y)]
cat("Best Lambda:", best_lambda_2, "\n")
rideshare_outliers$price_transformed <- if (abs(best_lambda_2) < 1e-4) {
  log(rideshare_outliers$price)
} else {
  (rideshare_outliers$price^best_lambda_2 - 1) / best_lambda_2
}

model_trans <- lm(
  price_transformed ~ 
    name + source + icon + surge_multiplier +
    ns(temperatureHigh, df = 2) +
    ns(windGust, df = 2):ns(hour, df = 2) +  
    ns(temperatureHigh, df=2):ns(hour, df=2) +
    ns(latitude, df = 2):ns(longitude, df = 2),
  data = rideshare_outliers
)

res_squared <- residuals(model_trans)^2
fitted_vals <- fitted(model_trans)
variance_model <- lm(log(res_squared) ~ log(fitted_vals))
weights <- 1 / exp(predict(variance_model))

model_WLS_boxcox <- lm(
  price_transformed ~ 
    name + source + icon + surge_multiplier +
    ns(temperatureHigh, df = 2) +
    ns(windGust, df = 2):ns(hour, df = 2) +  
    ns(temperatureHigh, df=2):ns(hour, df=2) +
    ns(latitude, df = 2):ns(longitude, df = 2),
  data = rideshare_outliers,
  weights = weights
)

summary(model_WLS_boxcox)
anova(model_WLS_boxcox)


# QQ-Plot
residuals <- resid(model_WLS_boxcox)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(model_WLS_boxcox)
plot_data <- data.frame(residuals = residuals(model_WLS_boxcox), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(model_WLS_boxcox)
check_constant_variance(model_WLS_boxcox)
check_equal_mean(model_WLS_boxcox)
check_independence(model_WLS_boxcox)
check_linearity(model_WLS_boxcox)


##########################################################################################
## SECTION 4: MODEL VALIDATION ##                                                       ##
##########################################################################################

evaluate_model_performance <- function(model, test_data, transformation = c("none", "sqrt_plus10", "log_squared", "log_plus10", "boxcox"), lambda = NULL) {
  transformation <- match.arg(transformation)
  predicted_transformed <- predict(model, newdata = test_data)
  
  # Apply back-transformation
  predicted <- switch(transformation,
                      "sqrt_plus10" = (predicted_transformed)^2 - 10,
                      "log_squared" = (predicted_transformed)^2,
                      "log_plus10" = exp(predicted_transformed) - 10,
                      "boxcox" = if (!is.null(lambda)) {
                        if (lambda == 0) exp(predicted_transformed) else (lambda * predicted_transformed + 1)^(1 / lambda)
                      } else {
                        stop("Lambda must be provided for Box-Cox back-transformation.")
                      },
                      "none" = predicted_transformed
  )
  
  actual <- test_data$price
  residuals <- actual - predicted
  
  # Model summary (for R^2 and adjusted R^2)
  model_summary <- summary(model)
  r_squared <- model_summary$r.squared
  adj_r_squared <- model_summary$adj.r.squared
  
  # Predicted R^2
  tss <- sum((actual - mean(actual))^2)
  sse <- sum(residuals^2)
  r_squared_pred <- 1 - sse / tss
  
  # Error metrics
  mse <- mean(residuals^2)
  mae <- mean(abs(residuals))
  mape <- mean(abs(residuals / actual)) * 100
  rmse <- sqrt(mse)
  
  # Plot actual vs predicted
  plot_df <- data.frame(actual = actual, predicted = predicted)
  plot(plot_df$actual, plot_df$predicted, 
       xlab = "Actual Price", ylab = "Predicted Price",
       main = "Actual vs Predicted", pch = 20, col = "blue")
  abline(0, 1, col = "red", lwd = 2)
  
  return(list(
    R_squared = round(r_squared, 4),
    Adjusted_R_squared = round(adj_r_squared, 4),
    R_squared_predicted = round(r_squared_pred, 4),
    SSE = round(sse, 4),
    MSE = round(mse, 4),
    MAE = round(mae, 4),
    MAPE = round(mape, 4),
    RMSE = round(rmse, 4)
  ))
}

evaluate_model_performance(model_basic, test_data)
evaluate_model_performance(model_bc, test_data_outliers, "boxcox", best_lambda)
test_data_outliers$distance_log <- log(test_data_outliers$distance)
test_data_outliers$temperatureHigh_log <- log(test_data_outliers$temperatureHigh + 1)
evaluate_model_performance(model_transformed_sqrt, test_data_outliers, "sqrt_plus10")
evaluate_model_performance(model_WLS, test_data_outliers, "log_plus10")
evaluate_model_performance(poly_model, test_data_outliers, "sqrt_plus10")
evaluate_model_performance(model_WLS_boxcox, test_data_outliers, "boxcox", best_lambda_2)

best_assumption_model_fs <- stepAIC(model_WLS_boxcox, direction = "both", trace = FALSE)
summary(best_assumption_model_fs)
vif(best_assumption_model_fs)

# QQ-Plot
residuals <- resid(best_assumption_model_fs)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(best_assumption_model_fs)
plot_data <- data.frame(residuals = residuals(best_assumption_model_fs), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(best_assumption_model_fs)
check_constant_variance(best_assumption_model_fs)
check_equal_mean(best_assumption_model_fs)
check_independence(best_assumption_model_fs)
check_linearity(best_assumption_model_fs)

evaluate_model_performance(best_assumption_model_fs, test_data_outliers, "boxcox", best_lambda_2)



##################################################
# FEATURE SELECTION AND DIMENSIONALITY REDUCTION #
##################################################

# IF YOU GET THIS ERROR: Error in eval(predvars, data, env) : object 'price_bc' not found
# This has a tendency of not running sometimes, please go back and run the best_lambda if-else block, Model #1
test_data_outliers$price_bc <- (test_data_outliers$price^best_lambda - 1) / best_lambda
best_r2_stepwise <- stepAIC(model_bc, direction = "both", trace = FALSE)
summary(best_r2_stepwise)
vif_manual(best_r2_stepwise)

# QQ-Plot
residuals <- resid(best_r2_stepwise)
residuals_df <- data.frame(residuals)
ggplot(residuals_df, aes(sample = residuals)) +
  stat_qq() +
  stat_qq_line(color = "red") +
  ggtitle("QQ Plot of Residuals")


# Residual vs. Fitted (for the remaining assumptions)
fitted_values <- fitted(best_r2_stepwise)
plot_data <- data.frame(residuals = residuals(best_r2_stepwise), fitted_values)
ggplot(plot_data, aes(x = fitted_values, y = residuals)) +
  geom_point() +
  geom_hline(yintercept = 0, color = "red", linetype = "dashed") +
  ggtitle("Residuals vs Fitted Values") +
  xlab("Fitted Values") +
  ylab("Residuals")

# Numeric-Based Assumption Tests (some covered in class, others are extension methods)
check_normality(best_r2_stepwise)
check_constant_variance(best_r2_stepwise)
check_equal_mean(best_r2_stepwise)
check_independence(best_r2_stepwise)
check_linearity(best_r2_stepwise)

evaluate_model_performance(best_r2_stepwise, test_data_outliers, "boxcox", best_lambda)








