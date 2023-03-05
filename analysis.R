#install.packages("tidyverse")
library(readr)
suppressPackageStartupMessages(library(dplyr))
results <- read_csv("results.csv",show_col_types = FALSE)

#Check for NAs
nas <- results %>% 
  summarise(across(everything(), ~ sum(is.na(.))))
missing <- sum(nas$operational) + sum(nas$axiomatic)
print(paste(missing, "missing values"))

assume_timeouts <- results %>%
  #Filter out where we don't have axiomatic models (XC/TSOXC)
  filter( architecture == "PTX" |
          architecture == "TSO" |
          architecture == "Compound") %>%
  mutate(operational = ifelse(operational == "𐄂?", "𐄂",operational))
  
discrepancies <- assume_timeouts %>%
  filter(axiomatic != operational)
print("following discrepancies found:")
print(discrepancies)