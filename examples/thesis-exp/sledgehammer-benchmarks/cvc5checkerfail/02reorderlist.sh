#!/bin/bash
#Given a list of proof files, filter them by their size

# Ensure the input file exists
list="checkerfalselist"
oplist="checkerfalselist2"
if [ ! -f "$list" ]; then
    echo "Input file $list not found."
    exit 1
fi

# Create an empty temporary file to store filenames with line counts
tempfile=$(mktemp)

# Read each filename from the input file
while IFS= read -r filename; do
    if [ -f "$filename" ]; then
        # Count the number of lines in the file and append it to the temporary file
        linecount=$(wc -l < "$filename")
        echo "$linecount $filename" >> "$tempfile"
    else
        echo "File '$filename' not found, skipping."
    fi
done < "$list"

# Sort the temporary file by the number of lines (first column) and create the output file
sort -n "$tempfile" | awk '{print $2}' > "$oplist"

# Clean up the temporary file
rm "$tempfile"

echo "Sorted list has been written to $oplist."
