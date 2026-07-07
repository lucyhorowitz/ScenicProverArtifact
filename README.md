# Overview
This artifact contains a prototype implementation of the ScenicProver framework, which supports all features described in the paper. A full version with documentation and additional quality-of-life features will be released before the paper is presented.

## Running the Artifact
This artifact contains a Dockerfile to easily run the case-study found in our paper. To begin, run the following command from the top level directory (while the Docker service is enabled). The command will build the docker image, and start a bash shell in a container from that image. After the shell is exited, it will then clean up by removing the container and image.

    docker build -t scenicprover . && docker run -it --rm scenicprover && docker rmi scenicprover

### Running the Case Study
To run a single instance of the case study, you can use the following command:

    scenic verify examples/contracts/dev_time.contract

This performs the case-study with a fixed testing time-budget (5 minutes by default) using our weak-merge heuristic. After the run terminates, an assurance case like the one found in our appendix will be printed out. The most important values can be found in the result summary at the end, which includes the “minimum X% correctness” corresponding to the guarantee over the entire system. 

As our case study operates on a time budget, it is unlikely that you will get the exact same results shown (as different systems will accomplish more/less testing in the same time budget). We do however encourage you to experiment with the case study, and provide two accessible parameters at the top of the case study `contract` file (`examples/contracts/dev_time.contract`) for this purpose: `NAIVE_APPROACH` and `TIME_LIMIT`. The first value is a boolean indicating whether or not the naive approach should be used, and the second is the testing time budget in seconds. By manipulating these values, one can produce substantially equivalent results to those found in our paper (see the comments near the parameters for details). Reviewers should feel free to experiment with other changes to the case study file, but we note that changes to the contracts themselves are likely to invalidate the existing Lean proofs, which could require substantial domain knowledge to repair. The proofs themselves can be found under `examples/contracts/LeanLTL/Examples/Scenic` (as indicated in the `.contract` file). Note also that the total time to run the case study will be longer than `TIME_LIMIT`, as the framework must also compile the program and check the proofs.

### Reproducing Appendix Results
Due to the inherent difficulty in being able to reproduce time-bounded experiments on various systems, we also offer a script that will instead reproduce Figure 7 in our Appendix. This figure uses a bound on the number of simulations actually making it to simulation instead of the more intuitive time budget (as is used in the figure in our main paper). This is roughly comparable to total time spent testing, but not exactly (simulations can have varying durations). To reproduce the data from this figure, you can use the following command:

    python3 run_experiments.py

This script will go through the various case study runs, printing intermediate results, and finish by printing a results summary which can be directly compared to Figure 7. The total runtime of the script was ~10 hours on an M4 Pro Macbook Pro.

### Understanding ScenicProver Proofs
The Lean proofs for our case study are located in `examples/contracts/LeanLTL/Examples/Scenic`. For example, the proof used by the expression `LeanRefinementProof("LeanLTL/Examples/Scenic/AccurateDistanceRefinement", LEANLTL_LOC, REPL_LOC)` in the `.contracts` file corresponds to the three proof files in `examples/contracts/LeanLTL/Examples/Scenic/AccurateDistanceRefinement`. When such an expression is run, ScenicProver generates the relevant directory and a `Lib.lean` file, along with an `AssumptionProof.lean` and `GuaranteesProof.lean` file *if they do not already exist*. These files together contain the definitions and proof obligations that ScenicProver needs discharged, with the actual proofs themselves (one each in `AssumptionProof.lean` and `GuaranteesProof.lean`) containing a `sorry`. This allows users to sketch their assurance case in ScenicProver and have it generate the proof obligations on the first pass, allowing the user to supply the proof without writing out all the needed boilerplate. Then, once the user has replaced the sorry with an actual proof, ScenicProver can be run again to actually check that the proof is correct.
