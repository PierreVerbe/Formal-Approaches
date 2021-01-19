# Formal approaches

## About this repository
This reposirtory contains an end-of-semester project in formal approach. <br>
The aim is to prove mathematically the correct functioning of a bubble sorting system. <br>

## Prerequisite
* Install GNU compiler collection <br>
* Install frama-c <br>

## Installation
* First clone this project
```bash
git clone https://github.com/PierreVerbe/Formal-Approaches
```

* Verify the installation of frama-c
```bash
frama-c -help
```

## Launching the analysis
* Launch frama-c 
```bash
frama-c -wp src/sort_1.c
```

* Launch frama-c graphical user interface
```bash
frama-c-gui -wp src/sort_1.c
```
