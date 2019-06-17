#!/usr/bin/env bash

# return the dependencies declared in some coq file as string
function get_deps () {
    grep "^Require" "$1.v" \
        | sed 's/Require \(Export *\|Import\| \)\?\(.*\)\..*$/\2/'
}

containsElement () {
    local e
    for e in "${@:2}"; do
       [[ "$e" == "$1" ]] && return 0;
    done
    return 1
}

# declare utilitie arrays
declare -A aa
declare -a remfiles
declare -a allfiles
declare -a folders

# Change here the master file and the dependency folders
# filenames should start with uppercase
remfiles=("all")
allfiles=("all")
folders=( $(find . -type d -printf '%P ') )
folders+=("")

# start filling the debug file
date > debug

echo "Generate makefile topdown..."
while true; do
    echo "==+== current: ${remfiles[0]} ==+=="
    if [[ ${#remfiles[@]} -eq 0 ]]; then
       echo "++++++ no more files" >> debug
       break
    else
       file=${remfiles[0]}
       remfiles=("${remfiles[@]:1}")
       echo "++=++ remaining: ${remfiles[*]} ++=++"
       echo "===============================" >> debug
       echo "++++++ file: ${file}" >> debug

       temp=$(get_deps "$file")
       deps=()
       for f in $temp; do
           # iterate through provided dep folders
           for d in "${folders[@]}"; do
                if [ -e "$d/$f.v" ]; then
                   deps+=("$d/$f")
               else
                   echo "${f} doesn't exist" >> debug
               fi
           done
       done

       echo "++=++ deps: ${deps[*]} ++=++"
       aa[$file]=${deps[*]}

       for i in "${deps[@]}"
       do
           echo "checking $i"
           containsElement "$i" "${allfiles[@]}"
           n=$?
           if [[ $n -eq 1 ]]
           then
               echo "++ new dependency: ${i}" >> debug
               remfiles=("${remfiles[@]}" "$i")
               allfiles=("${allfiles[@]}" "$i")
           else echo "++ not new dependency: ${i}" >> debug
           fi
       done
    fi
done

echo "# Makefile generated by create_makefile.sh" > Makefile
{ echo ""; echo "default : all.vo"; } >> Makefile

echo "" >> Makefile
echo "clean :" >> Makefile
echo "	-@find . -name \"*.aux\" -o -name \"*.vo\" -o -name \"*.glob\" -o -name \"*.v.d\" | xargs rm" >> Makefile

for i in "${!aa[@]}"; do
    echo "-------------------"
    echo "++ ${i}"

    echo "" >> Makefile
    echo -n "${i}.vo : ${i}.v " >> Makefile

    if [[ ${#aa[$i]} -eq 0 ]]; then
        echo "${i} doesn't have dependencies"
    else
        echo "${aa[$i]}"
        IFS=' ' read -a vals <<< "${aa[$i]}"
        for f in "${vals[@]}"
        do
            #echo "---- ${f}"
            echo -n "${f}.vo " >> Makefile
        done
    fi

    echo "" >> Makefile
    echo "	coqc -R coq-tools Tools -R velisarios Velisarios -R protocols Protocols -R simulator Simulator ${i}.v" >> Makefile
done