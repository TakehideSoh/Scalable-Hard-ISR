# Abount Solver Track Submission

## About output (solution) files

- Output files shuld be the concatenation of [Output File Format](https://core-challenge.github.io/2022/#output-file-format) and a **verbose "GNU time" command log**.
  - **Do not use** the default "time" command which does not have verbose options.
  - (macOS) install "GNU time"  by `brew install gnu-time` for instance. It can be called by `gtime`.
  - (ubuntu) install "GNU time" by `apt install time` for instance. It can be called by `/usr/bin/time`.
- An example of acceptable submissions is as follows (executed on macOS).
  - `c` lines are comments if any (we encourage verbose comments so that others can assess solver's behaviour).
  - `a` lines are solution.
  - Following those solution lines, the results of `gtime -v` (or `/usr/bin/time -v`).

```bash
c $ gtime -v /Users/soh/app/scala-2.12.4/bin/scala -cp jar/scop.jar:jar/coresolver_2.12-1.3.5.jar fun.scop.app.isr.IsrSolver -isrsolver tj02 /Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01.col /Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01_01.dat 
c 0 GraphFile:/Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01.col
c 0 InstanceFile:/Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01_01.dat
c 0 #Node:7, #Edge:7, #Init:3, InitRatio:0.43, #Goal:3, GoalRatio:0.43
c 0 SatSolver: Sat4j(default)
c 0 IsrSolver: tj02
c step 1
c step 2
c step 3
a Yes
a 2 5 6
c 2 -> 0
a 0 5 6
c 5 -> 4
a 0 4 6
c 0 -> 3
a 3 4 6
	Command being timed: "/Users/soh/app/scala-2.12.4/bin/scala -cp jar/scop.jar:jar/coresolver_2.12-1.3.5.jar fun.scop.app.isr.IsrSolver -isrsolver tj02 /Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01.col /Users/soh/02_prog/2022benchmark/benchmark/handcrafted/hc-toyyes-01_01.dat"
	User time (seconds): 1.94
	System time (seconds): 0.19
	Percent of CPU this job got: 208%
	Elapsed (wall clock) time (h:mm:ss or m:ss): 0:01.02
	Average shared text size (kbytes): 0
	Average unshared data size (kbytes): 0
	Average stack size (kbytes): 0
	Average total size (kbytes): 0
	Maximum resident set size (kbytes): 109364
	Average resident set size (kbytes): 0
	Major (requiring I/O) page faults: 230
	Minor (reclaiming a frame) page faults: 34307
	Voluntary context switches: 295
	Involuntary context switches: 18599
	Swaps: 0
	File system inputs: 0
	File system outputs: 0
	Socket messages sent: 0
	Socket messages received: 0
	Signals delivered: 5
	Page size (bytes): 4096
	Exit status: 0
```

- You may wonder how to put "GNU time" results into a file. There are several options
  - `-o <file>` option puts the result into `<file>`
  - By using curly braces, you can redirect the results. 
    - For instance, `{ gtime -v SOLVER_CMD test.col test.dat > example.txt ; } 2>> example.txt` will put all outputs to `<example.txt>`.

## About solver (as a docker container)

- Please submit your solver executable on Ubuntu 20.04 as a docker container archive (tar.gz archive).


### Dockerfile and final product

- The basic template is as follows.

``` bash
FROM ubuntu:20.04

#------------------------------------------------
# (1) install fundamental commands
#------------------------------------------------
RUN \
    apt update && \
    apt -y upgrade && \
    apt install -y curl git man unzip vim wget sudo

#   Hint: you may want to additionally install the followings. 
#   apt install -y build-essential
#   apt install -y software-properties-common

#------------------------------------------------
# (2) clone the 2022solver directory to /
#------------------------------------------------
RUN git clone https://github.com/core-challenge/2022solver.git
```

- It will create an almost empty Ubuntu OS which has the `/2022solver/` directory.
- What you need to do is install your solver and rewrite `/2022solver/run.sh` so that `/2022solver/run.sh /2022solver/example/hc-toyno-01.col /2022solver/example/hc-toyno-01_01.dat` returns appropriate output.
- There are several ways to do that. The following is an instruction.

### Instruction

- At first, edit the above Dockerfile as you like (cloning 2022solver is mandatory).

- Then, build your docker image by the following command. Note that `mysolver` can be any "image name" and `v01` can be any "tag name".

```bash
docker build -t mysolver:v01 .
```

- It may take minutes. 
- If the command is successfully finished, `[+] Building xxx.xs (y/y) FINISHED` is displayed. 

`$ docker image ls` shows the image you just created. 

```bash
$ docker image ls
REPOSITORY   TAG       IMAGE ID       CREATED         SIZE
mysolver     v01       af8aaca552c0   3 minutes ago   277MB
```

- Next, let's launch your "container" from the image. 

```bash
$ docker run -it --name mysolver-container mysolver:v01 bash
root@13765b36541e:/# 
root@13765b36541e:/# ls 2022solver/
README.md  example  run.sh
```

- `root@13765b36541e:/# ` is the prompt in the running container. 
- Then, let's detach from your container by `ctrl-pq` (holding down `ctrl`, and type `p` and type `q`) which will keep your container alive (do not use `exit` or `ctrl-d` which will stop your container). 
- You get back to the prompt of your local machine. Then, `docker ps` will show your container running. 

```bash
$ docker ps -a
CONTAINER ID   IMAGE          COMMAND   CREATED          STATUS          PORTS     NAMES
13765b36541e   mysolver:v01   "bash"    13 minutes ago   Up 13 minutes             mysolver-container
```

- If you want to copy some file/directory on your local machine into the running container, please use `docker cp` as follows:

```bash
docker cp solver-track-instruction.md mysolver-container:/2022solver/
```

- In this example, a file `solver-track-instruction.md` is copied to `/2022solver/` of `mysolver-container`. 
- To re-enter a running container, use `docker exec` as follows. You can find the file `solver-track-instruction.md` copied from your local machine. 

```bash
$ docker exec -it mysolver-container bash
root@13765b36541e:/# ls 2022solver/
README.md  example  run.sh  solver-track-instruction.md
```

- By using the commands explained above, please install your solver and rewrite `run.sh` so that the command `/2022solver/run.sh /2022solver/example/hc-toyno-01.col /2022solver/example/hc-toyno-01_01.dat` returns appropriate output. 

- After completing your installation, the final task is `docker export`.
- If you are in the running container, please detach by `ctrl-pq`.
- Check your container exists `docker ps -a`. 

```bash
$ docker ps -a
CONTAINER ID   IMAGE          COMMAND   CREATED          STATUS          PORTS     NAMES
13765b36541e   mysolver:v01   "bash"    39 minutes ago   Up 39 minutes             mysolver-container
``` 

- Then, execure the following command, which will create your solver archive. 

```bash
$ docker export mysolver-container | gzip -c > mysolver-container.tar.gz
```

- Please add `mysolver-container.tar.gz` to your repository at your submission. 

### Docker command reference

- The official reference of Docker CLI is [here](https://docs.docker.com/engine/reference/run/).
- The followings are frequently used commands.
  - `docker build`
  - `docker image ls`
  - `docker ps -a`
  - `docker cp`
  - `docker exec`
  - `docker export`
