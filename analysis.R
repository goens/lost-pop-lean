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
  mutate(operational_timeout = ifelse(operational == "𐄂?", "𐄂",operational))

matches <- assume_timeouts %>%
  group_by(architecture) %>%
  summarize(matches = sum(axiomatic == operational_timeout))
print("matching litmus tests per architecture:")
print(matches)

discrepancies <- assume_timeouts %>%
  filter(axiomatic != operational_timeout)
print("following discrepancies found:")
print(select(discrepancies,architecture,test,operational,axiomatic))