#!/bin/bash

for filename in *; do
  if ([ "$filename" == "run.sh" ] || [ "$filename" == "main.ml" ] || [ "$filename" == "extraction.v" ] || [ "$filename" == "_tags" ] || [ "$filename" == "remove.sh" ])
  then echo "$filename"
  else rm $filename
  fi
done
