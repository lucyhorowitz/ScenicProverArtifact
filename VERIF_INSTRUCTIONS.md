# Running `scenic verify`

## One-time setup

1. Python environment: see `SETUP_AIRSIM.md`. Then:

   ```bash
   source ~/miniforge3/bin/activate airsim
   pip check          # "No broken requirements found."
   scenic --help      # CLI must load
   ```

2. Lean toolchain:

   ```bash
   sh install_lean.sh -y
   export PATH="$HOME/.elan/bin:$PATH"
   cd examples/contracts/LeanLTL && lake exe cache get && cd ../../..   # prebuilt mathlib (~6G)
   cd examples/contracts/repl && lake build && cd ../../..              # the REPL ScenicProver drives
   ```

   Check:

   ```bash
   lake --version                                  # Lake 5.x / Lean 4.x
   ls examples/contracts/repl/.lake/build/bin/repl
   du -sh examples/contracts/LeanLTL/.lake         # multiple GB
   ```

   Without the mathlib cache, verification builds all of mathlib from source
   and looks hung.

3. AirSim settings (Blocks reads this at startup only; re-copy → restart Blocks):

   ```bash
   mkdir -p ~/Documents/AirSim
   cp examples/airsim/settings/simple_drone_settings.json ~/Documents/AirSim/settings.json
   ```

## Running

```bash
# Terminal 1 — Blocks (RPC port 41451)
~/simulators/Blocks/LinuxBlocks1.8.1/LinuxNoEditor/Blocks.sh -windowed -ResX=640 -ResY=480 -NoVSync

# Terminal 2
source ~/miniforge3/bin/activate airsim
scenic verify examples/contracts/drone_distance.contract
```

AirSim velocity commands are quiet by default. To trace every command, run
`scenic verify -v 3 examples/contracts/drone_distance.contract`.

Budget more than `TIME_LIMIT` (default `5*60`): simulation testing runs for the
budget, plus compilation and proof checking.

To sanity-check the scenario without contracts:

```bash
scenic examples/contracts/followPatrol.scenic -S --count 1 --time 200
```

## Proof workflow

**Pass 1.** Run `scenic verify`. For each `LeanContractProof(...)` /
`LeanRefinementProof(...)` path it creates the directory and writes `Lib.lean`
(definitions + proof obligations) plus proof skeletons containing `sorry`:
`ComponentProof.lean` for `prove`, `AssumptionProof.lean` + `GuaranteesProof.lean`
for `refine`. Proof files are only written if missing; `Lib.lean` is rewritten
every run — never edit it.

**Pass 2.** Replace each `sorry` with a proof and re-run `scenic verify`.

Verification checks refinements top-down and stops at the first failure, so
pass 1 repeats as each proof is filled in. Outstanding proofs:

```bash
grep -rl sorry examples/contracts/LeanLTL/LeanLTL/Examples/Scenic/DroneDistance
```

Expected failure states:
- `AssertionError: Sorry used in Lean proof` — proof skeleton not filled in yet
- `Error in Lean proof: <file>` — generated Lean is broken; fix the generator

## Proof layout

Paths in each `.contract` map to directories under
`examples/contracts/LeanLTL/LeanLTL/Examples/Scenic/`:

```
AEB/            <- dev_time.contract, dev_count.contract
DroneDistance/  <- drone_distance.contract
HighwayMerge/   <- highway_merge.contract
```

Lean module paths mirror the layout. Moving a proof directory requires updating
both the `import` lines in its `.lean` files and the path string in the
`.contract`.

## Numeric semantics

Lean obligations are interpreted over ℚ (exact arithmetic). Trace values embed
exactly (every IEEE double is rational); floating-point rounding in component
bodies and the runtime monitor is assumed negligible relative to contract
margins.

## Gotchas

| Symptom | Cause | Fix |
|---|---|---|
| verification hangs early | no mathlib cache | `lake exe cache get` in `examples/contracts/LeanLTL` |
| `Connection refused` / RPC timeout | Blocks not running | start Blocks (port 41451) |
| only one drone spawns | stale `~/Documents/AirSim/settings.json` | re-copy, restart Blocks |
| `cannot import name 'PropositionalIoContract'` | PyPI pacti | `pip install -e ./pacti` |
