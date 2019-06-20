#!/bin/bash
target="bottom"
parameters=""

if [ "$1" == "bottom" ]; then
    target="bottom"
elif [ "$1" == "typecheck" ]; then
    target="verification"
    parameters="typecheck"
elif [ "$1" == "verify" ]; then
    target="verification"
elif [ "$1" == "tests" ]; then
    target="freertos"
else
    echo "Unknown target: " $1
    exit -1
fi

for file in `find source/* -maxdepth 0 -type d` ; do
    echo ">>> Testing subsystem: " $file
    cd $file
    TARGET=$target make $parameters
    if [ $? -gt 0 ] ; then
        echo ">>> Subsystem: " $file " FAILED"
        #exit -1
    else
        echo ">>> Subsystem: " $file " OK"
    fi
    cd -
done