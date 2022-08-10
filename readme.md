# Smart Contract Vulnerability

This repo contains our ([Liguo](https://github.com/chen-dudu) and myself) joint solution for Assignment 2 of SWEN90010 2022S1. The goal of the project is to detect and fix a vulnerability in a model of a small smart contract program—one that is inspired by the recursive reentrancy vulnerability of ["The DAO"](https://en.wikipedia.org/wiki/The_DAO_(organization)). The program is modelled in [Alloy 6](https://alloytools.org), which enables rigorous automatic predicate checks to be run to verify if the model has been specified "correctly". More details on the assignment specifications are available in [`specs.pdf`](./specs.pdf).

## How to Run
Download the [Alloy analyzer](https://alloytools.org/download.html) and open the [`dao.als`](./dao.als) file.
