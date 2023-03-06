FROM ubuntu:focal-20230126
ENV TZ=Europe/London \
    DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y \
    openjdk-16-jdk \
    git \
    curl \
    sudo \
    vim

# Create a regular user
RUN useradd -rm -d /home/user -s /bin/bash -g root -G sudo -u 1001 user
USER user
WORKDIR /home/user

# Install Elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf > elan-install.sh
RUN chmod +x elan-install.sh
RUN ./elan-install.sh -y
RUN . /home/user/.elan/env
RUN /home/user/.elan/bin/elan self update

WORKDIR /home/user/models
COPY --chown=user . .
RUN /home/user/.elan/bin/lake update

USER root
RUN    /home/user/.elan/bin/lake build
CMD ["/usr/bin/bash"]

