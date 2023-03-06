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
RUN useradd --user-group --system --create-home --no-log-init user
USER user
WORKDIR /home/user

# Install Elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf > elan-install.sh
RUN chmod +x elan-install.sh
RUN ./elan-install.sh -y
RUN . /home/user/.elan/env
RUN /home/user/.elan/bin/elan self update

#WORKDIR /home/user/models
COPY --chown=user . models
WORKDIR /home/user/models


#Build Alloy
RUN cd org.alloytools.alloy && ./gradlew build

#USER root
#COPY . .

#Build Pop
RUN /home/user/.elan/bin/lake update
RUN    /home/user/.elan/bin/lake build

CMD ["/usr/bin/bash"]
