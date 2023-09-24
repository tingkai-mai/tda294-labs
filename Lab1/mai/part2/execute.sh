#!/bin/bash

spin -a NS2.pml
gcc -o pan pan.c
./pan -a -N forksAreNotShared 
