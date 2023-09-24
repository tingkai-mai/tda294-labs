#!/bin/bash

spin -a part1.pml
gcc -o pan pan.c
./pan -a -N forksAreNotShared 
