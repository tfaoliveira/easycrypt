#!/bin/bash

for f in $(find . -type f | grep -v "/.git/" | grep -v "/_build/" |
	   grep -v ".exe" | grep -v ".icns"  | grep -v ".png")
do
	sed 's/[ \t]*$//' $f > $f.tmp
	if ! diff $f $f.tmp &> /dev/null; then
		rm $f.tmp
		exit 1
	else
		rm $f.tmp
	fi
done
