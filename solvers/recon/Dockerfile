FROM ubuntu:20.04 AS builder

RUN \
    apt-get update \
    && apt-get -y upgrade \
    && apt-get -y install build-essential clang

COPY ./src/ ./src/

WORKDIR ./src/

RUN make



FROM ubuntu:20.04

#------------------------------------------------
# (1) install fundamental commands
#------------------------------------------------
RUN \
    apt-get update \
    && apt-get -y upgrade \
    && apt-get -y install curl git man unzip vim wget sudo time \
    && apt-get -y clean \
    && rm -rf /var/lib/apt/lists/*

#   Hint: you may want to additionally install the followings.
#   apt install -y build-essential
#   apt install -y software-properties-common

#------------------------------------------------
# (2) clone the 2022solver directory to /
#------------------------------------------------
RUN git clone https://github.com/core-challenge/2022solver.git

COPY --from=builder ./src/recon_th ./2022solver/

COPY ./run.sh ./2022solver/

## TODO: remove this
#COPY ./benchmark/ ./2022solver/benchmark/
## or
## VOLUME ["/2022solver/benchmark"]


WORKDIR ./2022solver/

## TODO: remove this
#ENTRYPOINT ["/2022solver/run.sh"]
#CMD ["example/hc-toyno-01.col", "example/hc-toyno-01_01.dat"]
