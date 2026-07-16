# AirSim + Scenic setup

Ubuntu 26.04, July 2026.

## Python environment

Python **3.11** via miniforge. (Ubuntu 26.04 ships 3.14 only; Scenic's pinned
deps have no cp314 wheels.)

```bash
curl -L -o /tmp/mf.sh https://github.com/conda-forge/miniforge/releases/latest/download/Miniforge3-Linux-x86_64.sh
bash /tmp/mf.sh -b -p ~/miniforge3
~/miniforge3/bin/conda create -y -n airsim python=3.11
source ~/miniforge3/bin/activate airsim
```

## Install (in this order)

```bash
# 1. Scenic (editable)
pip install -e .

# 2. pyeda — GCC 15 rejects its bundled espresso C code without these flags
CFLAGS="-Wno-error=incompatible-pointer-types -Wno-error=implicit-function-declaration -Wno-error=int-conversion" \
  pip install pyeda

# 3. airsim client — its setup.py imports the package at build time, so runtime
#    deps must already be installed and build isolation must be off
pip install msgpack-rpc-python              # tornado 4.5.3, msgpack-python 0.5.6
pip install --no-build-isolation airsim     # pulls numpy 2.x + opencv-contrib 5.x; re-pinned next

# 4. re-pin what airsim clobbered (Scenic needs numpy 1.x)
pip install 'numpy==1.26.4' 'opencv-contrib-python==4.11.0.86'

# 5. pacti — the vendored ./pacti checkout, not PyPI (PyPI 0.2.0 lacks
#    PropositionalIoContract; the scenic CLI entrypoint fails to load without it)
pip uninstall -y pacti
pip install -e ./pacti
```

Verify:

```bash
pip check                       # "No broken requirements found."
scenic --help                   # CLI must load (this is what exercises pacti)
python -c "import scenic, airsim; from scenic.simulators.airsim import AirSimSimulator; print('ok')"
```

## Gotchas

| Symptom | Cause | Fix |
|---|---|---|
| `Cannot compile Python.h` building numpy | Python 3.14, no wheels | use Python 3.11 |
| pyeda: `incompatible pointer type` error | GCC 15 strictness | `CFLAGS=-Wno-error=incompatible-pointer-types` |
| airsim build: `No module named numpy`/`msgpackrpc` | setup.py imports pkg at build | install deps first + `--no-build-isolation` |
| `scenic 3.0.0 requires numpy~=1.24` | airsim pulled numpy 2.x | re-pin `numpy==1.26.4`, `opencv-contrib-python==4.11.0.86` |
| `cannot import name 'PropositionalIoContract'` | PyPI pacti, not the fork | `pip install -e ./pacti` |

## Running a scenario

AirSim reads `~/Documents/AirSim/settings.json` at startup; editing it requires
restarting Blocks.

```bash
mkdir -p ~/Documents/AirSim
cp examples/airsim/settings/simple_drone_settings.json ~/Documents/AirSim/settings.json
```

Two terminals:

```bash
# Terminal 1 — the Unreal world (RPC port 41451)
chmod +x ~/simulators/Blocks/LinuxBlocks1.8.1/LinuxNoEditor/Blocks.sh   # first time only
~/simulators/Blocks/LinuxBlocks1.8.1/LinuxNoEditor/Blocks.sh -windowed -ResX=640 -ResY=480 -NoVSync

# Terminal 2 — Scenic
source ~/miniforge3/bin/activate airsim
scenic examples/airsim/multiDrone.scenic -S --count 1 --time 200
```

`-S` simulate, `--count N` number of simulations, `--time T` step cap.
Other example scenarios: `examples/airsim/`.
