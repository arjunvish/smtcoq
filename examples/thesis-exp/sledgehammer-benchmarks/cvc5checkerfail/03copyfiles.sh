#!/bin/bash

#Once we have a list of all the proof files, sorted by their sizes, we can 
#create an individual folder for them (starting from 03), create a .md file explaining
#the issue, and copy the smt file, the proof file, and the .v file
list="checkerfalselist2"
CTR=3
while IFS= read -r line; do
    #Create directory "$CTRcvc5"
    if [ $CTR -lt 10 ]; then
        NEWCTR="0${CTR}"
    else
        NEWCTR="${CTR}"
    fi
    dir="${NEWCTR}cvc5"
    mkdir -p "$dir"

    #Create doc file
    file=./$dir/$dir.md
    touch "$file"

    echo "No exceptions are raised, but checker fails." >> "$file"
    echo >> "$file"
    
    # Extract the bare file name and path
    barefile=$(basename "$line")
    path=$(dirname "$line")
    
    pffname="${barefile}.cvc5oldpf"
    smtfname="${barefile}.smt_in"
    vfname="${barefile}cvc5.v"

    echo "Proof File: $pffname" >> "$file"
    echo "SMT File: $smtfname" >> "$file"
    echo "Path: $path" >> "$file"
    echo >> "$file"

    echo "Problem:" >> "$file"
    echo >> "$file"

    echo "Fix:" >> "$file"

    #Copy proof file
    pffull="${path}/${pffname}"
    pfnew="./${dir}/${pffname}"
    cp "$pffull" "$pfnew"

    #Copy SMT file
    smtfull="${path}/${smtfname}"
    smtnew="./${dir}/${smtfname}"
    cp "$smtfull" "$smtnew"

    #Copy Coq file
    vfull="${path}/${vfname}"
    vnew="./${dir}/${vfname}"
    cp "$vfull" "$vnew"

    #Increment CTR by 1
    CTR=$((CTR + 1))
done < "$list"