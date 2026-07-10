FROM ubuntu:latest
WORKDIR /app

# Install dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl git build-essential libssl-dev zlib1g-dev libbz2-dev \
    libreadline-dev libsqlite3-dev wget llvm libncurses5-dev \
    libncursesw5-dev xz-utils tk-dev libffi-dev liblzma-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Pyenv and Python 3.11
ENV PYENV_ROOT="/root/.pyenv"
ENV PATH="$PYENV_ROOT/bin:$PYENV_ROOT/shims:$PATH"
RUN curl -fsSL https://pyenv.run | bash && \
    pyenv install 3.11 && \
    pyenv global 3.11

# Copy application source code into the image
COPY . /app/

RUN pip install .
# Temporary shapely workaround
RUN pip install shapely==2.0

# Temporary PYEDA Error workaround
RUN pip install git+https://github.com/NN---/pyeda.git

# Install Pacti
WORKDIR pacti
RUN pip install .
WORKDIR ..

# Install Lean
RUN sh install_lean.sh -y
ENV PATH="/root/.elan/bin:$PATH"
RUN lake

# Fetch prebuilt Lean/mathlib artifacts for LeanLTL so verification does not
# compile the full dependency graph at runtime.
WORKDIR examples/contracts/LeanLTL
RUN lake exe cache get
WORKDIR ../../..

# Build REPL
WORKDIR examples/contracts/repl
RUN lake build
WORKDIR ../../..

# AirSim 1.8.1 otherwise pulls NumPy 2.x through the latest OpenCV release,
# which is incompatible with Scenic and the binary Shapely wheel in this image.
RUN pip install msgpack-rpc-python promise wheel \
    numpy==1.26.4 opencv-contrib-python==4.10.0.84 && \
    pip install --no-build-isolation --no-deps airsim==1.8.1

CMD ["/bin/bash"]
