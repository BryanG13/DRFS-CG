# DRFS-CG: Demand-Responsive Feeder Service - Column Generation

C++ implementation of a demand-responsive feeder scheduling model using Mixed Integer Programming (MIP) with lazy constraints. The MIP is solved using CPLEX and modelled as a Column Generation model. 

## Overview

This repository contains a C++ solver that reads passenger and arrival data, builds a MIP model and writes assignment/solution files. The project is built with CMake and produces an executable in the `build/` directory.

## Build

Prerequisites: a C++ compiler and CMake (version >= 3.10).

From the repository root:

```bash
mkdir -p build
cd build
cmake ..
cmake --build . --config Debug
```

The resulting binary is typically placed under `build/DRFS_MIP` (see `build/`).

## Run

Place input files under the `data/input/` directory. Example input files included:

- `arrivals.txt`
- `mandatory.txt`
- `optional.txt`
- `passengers.txt`

Run the executable from the project root or `build/` directory. The program will write outputs to `data/output/` (e.g., `Asol.txt`, `Dsol.txt`, `visits.txt`, `walking.txt`, `xsol.txt`, `ysol.txt`).

Example:

```bash
./build/DRFS_MIP
```

## Data layout

Input files are plain text tabular files; check `data/input/` for formatting examples. Output files are written to `data/output/` and contain the computed assignments and solution details.

## License

This project is provided under the repository LICENSE file.

## Contact

Maintainer: Bryan Galarza
