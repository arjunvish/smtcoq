#!/bin/bash
#From cvc5coqcop, the output of cvc5coqc.sh, create a list of smt files that 
#have a particular output, for example, ones for which the checker returns `= false`
#(in this case we get the line previous to `= false`)

input_file="cvc5oldcoqcop"
output_file="checkerfalselist"

# Ensure the input file exists
if [ ! -f "$input_file" ]; then
    echo "Input file '$input_file' not found."
    exit 1
fi

# Ensure the output file is empty before starting
> "$output_file"

# Initialize a variable to keep track of the previous line
prev_line=""

# Read the input file line by line
while IFS= read -r current_line; do
    # Check if the current line matches "     = false"
    if [ "$current_line" == "     = false" ]; then
        # Write the previous line to the output file
        echo "$prev_line" >> "$output_file"
    fi
    # Update the previous line
    prev_line="$current_line"
done < "$input_file"

echo "Processing complete. Results are in '$output_file'."