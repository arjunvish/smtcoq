#!/bin/bash

# Input and output file paths
input_file="cvc5coqcop14"
output_file="14holes"

# Clear the output file if it already exists
> "$output_file"

# Initialize flags
found_warning=false

# Read the input file line by line
while IFS= read -r line; do
    # Check if the line starts with "WARNING"
    if [[ $line == WARNING* ]]; then
        found_warning=true
        echo "$line" >> "$output_file"
    elif [[ -z $line ]]; then
        # If an empty line is found, stop collecting lines
        found_warning=false
        echo "" >> "$output_file"
    elif $found_warning; then
        # If within a warning block, add the line to the output
        echo "$line" >> "$output_file"
    fi
done < "$input_file"
