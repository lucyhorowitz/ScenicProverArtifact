import subprocess
import os

SIMULATION_COUNTS = [2**5, 2**6, 2**7, 2**8, 2**9, 2**10]

def run_case_study(naive, sim_count):
    os.environ["NAIVE_APPROACH"] = "1" if naive else "0"
    os.environ["SIM_COUNT"] = str(sim_count)
    print(f"Running Case Study with NAIVE={naive} and SIM_COUNT={sim_count}")
    result = subprocess.run(["scenic", "verify", "examples/contracts/dev_count.contract"], capture_output=True, encoding="utf-8")
    print(result.stdout)
    return float(result.stdout.splitlines()[-3][-6:-1])

if __name__ == '__main__':
    results = {}
    for sim_count in SIMULATION_COUNTS:
            for naive in [False, True]:
                results[(naive, sim_count)] = run_case_study(naive, sim_count)

    print("Heuristic Results (# Simulations, Correctness %):")
    for sim_count in SIMULATION_COUNTS:
        sim_count_str = str(sim_count).ljust(6, ' ')
        correctness = results[(False, sim_count)]
        print(f"  {sim_count_str}: {correctness:.2f}%")

    print("Naive Results (# Simulations, Correctness %):")
    for sim_count in SIMULATION_COUNTS:
        sim_count_str = str(sim_count).ljust(6, ' ')
        correctness = results[(True, sim_count)]
        print(f"  {sim_count_str}: {correctness:.2f}%")
