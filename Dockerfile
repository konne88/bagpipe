FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

RUN apt-get update; \
    apt-get install -y \
      binutils \
      default-jre \
      git \
      g++ \
      haskell-platform \
      make \
      python \
      python-pip \
      python-yaml \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git
RUN cd z3; python scripts/mk_make.py
RUN cd z3/build; make; make install
RUN rm -r z3

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.1.1/racket-6.1.1-x86_64-linux-ubuntu-precise.sh -O install.sh
RUN chmod +x install.sh
RUN ./install.sh --in-place --create-links /usr --dest /usr/racket
RUN rm install.sh

# install rosette
RUN git clone https://github.com/emina/rosette.git && \
    cd rosette; git checkout db80315cb37df8e32766f6436c9baad9544540a4 && \
                raco link rosette && \
                raco setup -l rosette && \
                ln -s /usr/bin/z3 bin/

# install some haskell packets that we think will be useful
RUN cabal update; \
    cabal install --force-reinstalls \
      array \
      base \
      bytestring \
      containers \
      filepath \
      MissingH \
      parsec \
      QuickCheck \
      regex-compat \
      split \
      syb \
      sexp \
      text-format-simple

RUN apt-get update; \
    apt-get install -y \
      binutils \
      camlp5 \
      curl \
      libpcre-ocaml-dev \
      libpcre3-dev \
      libreadline-dev \
      libz-dev \
      make \
      pkg-config \
      vim

# install coq
RUN curl -O https://coq.inria.fr/distrib/V8.5beta2/files/coq-8.5beta2.tar.gz
RUN tar -xvf coq-8.5beta2.tar.gz
RUN cd coq-8.5beta2; ./configure \
  -bindir /usr/local/bin \
  -libdir /usr/local/lib/coq \
  -configdir /etc/xdg/coq \
  -datadir /usr/local/share/coq \
  -mandir /usr/local/share/man \
  -docdir /usr/local/share/doc/coq \
  -emacs /usr/local/share/emacs/site-lisp \
  -coqdocdir /usr/local/share/texmf/tex/latex/misc
RUN cd coq-8.5beta2; make -j4; make install

# install sshd
RUN apt-get update; \
    apt-get install -y \
      openssh-server
RUN ssh-keygen -q -t rsa -N '' -f /root/.ssh/id_rsa
RUN cp /root/.ssh/id_rsa.pub /root/.ssh/authorized_keys
RUN echo 'Host *' >> /root/.ssh/config
RUN echo '    StrictHostKeyChecking no' >> /root/.ssh/config

# install bagpipe haskell parser
ADD src/bagpipe/hs /bagpipe/src/bagpipe/hs
RUN cd /bagpipe/src/bagpipe/hs/; cabal update; cabal install

# install bagpipe coq proof
ADD src/bagpipe/coq/Main /bagpipe/src/bagpipe/coq/Main
ADD src/bagpipe/coq/Makefile /bagpipe/src/bagpipe/coq/Makefile
RUN cd /bagpipe/src/bagpipe/coq/; make clean; make -j4

# install bagpipe coq extraction
ADD src/bagpipe/coq/Test /bagpipe/src/bagpipe/coq/Test
RUN cd /bagpipe/src/bagpipe/coq/; make -j4 test

# install bagpipe
ADD src/bagpipe/racket /bagpipe/src/bagpipe/racket
RUN cp /bagpipe/src/bagpipe/coq/build/bgpv.rkt /bagpipe/src/bagpipe/racket/main/
RUN find /bagpipe/src/bagpipe/racket -name compiled -type d -exec rm -r {} +
RUN raco make /bagpipe/src/bagpipe/racket/main/bagpipe.rkt
ENV BAGPIPE /bagpipe

# install scripts
ADD src/bagpipe/python /bagpipe/src/bagpipe/python
RUN cp /bagpipe/src/bagpipe/python/bagpipe /usr/bin/

ENTRYPOINT ["bagpipe"]
