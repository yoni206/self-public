# Use an official image as a parent image
FROM ubuntu:latest

# Install Git and required build tools
RUN apt-get update && \
    apt-get install -y wget

RUN wget https://raw.githubusercontent.com/yoni206/self-public/refs/heads/main/zvika/pbvsolver
RUN chmod 755 pbvsolver

# # install dependencies
# RUN apt-get install gcc
# RUN apt-get install -y openjdk-11-jre-headless && \
#     apt-get clean;
# # RUN apt-get install -y git build-essential cmake python3 python3-pip
# RUN apt install python3-toml
# RUN apt install libgmp-dev -y
# 
# # Set the working directory inside the container
# WORKDIR /app
# 
# # Clone the repository
# RUN git clone -b pbv-master https://github.com/BergerZvika/smt-switch.git
# 
# # env variable
# # ENV PATH="$PATH:/app/bin:/app/smt-switch/deps/bison/bison-install/bin:/app/smt-switch/deps/flex/flex-install/bin:/app/smt-switch/deps/cvc5/build/bin"
# 
# 
# # Run the install.sh script
# WORKDIR /app/smt-switch/pbv
# RUN chmod +x install.sh && \
#    ./install.sh
# 
# # Set the working directory where the static binary exist
# WORKDIR /app/smt-switch/pbv/build
# 
# # Command to run the built program (change this as needed)
# # CMD ["echo", "Repository cloned, install.sh script run."]
# ENTRYPOINT [ "./pbvsolver" ]
# CMD ["../benchmarks/validation/test-bvconstant-unsat.smt2", "--debug", "--postwalk"]
