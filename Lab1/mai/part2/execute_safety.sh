#!/bin/bash

spin -a NS2.pml
gcc -DSAFETY -o pan pan.c
./pan 
spin -t -p -l -g -r -s NS2.pml