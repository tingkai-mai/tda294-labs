#!/bin/bash

spin -a Philosophers.pml
gcc -o pan pan.c
./pan -a -N forksAreNotShared 
