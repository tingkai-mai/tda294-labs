#!/bin/bash

spin -a part2.pml
gcc -o pan pan.c
./pan -a -N forksAreNotShared 
