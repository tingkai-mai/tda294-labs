#!/bin/bash

spin -a Philosophers.pml
gcc -o pan pan.c
./pan -a -f -N philHasEatenAtLeastOnce
# ./pan -a -N forksAreNotShared 
