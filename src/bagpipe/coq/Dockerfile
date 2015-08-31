FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

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
      pkg-config

RUN curl -L -O http://downloads.sourceforge.net/project/c-bgp/cbgp-2.3.2.tar.gz
RUN tar -xvf cbgp-2.3.2.tar.gz
RUN curl -L -O http://downloads.sourceforge.net/project/libgds/libgds-2.2.2.tar.gz
RUN tar -xvf libgds-2.2.2.tar.gz
RUN curl -O https://coq.inria.fr/distrib/V8.5beta2/files/coq-8.5beta2.tar.gz
RUN tar -xvf coq-8.5beta2.tar.gz

RUN cd libgds-2.2.2; ./configure; make -j4; make install
RUN ldconfig
RUN cd cbgp-2.3.2; ./configure; make -j4; make install
RUN ldconfig

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

RUN apt-get install -y haskell-platform

RUN cabal update; \
    cabal install parsec

RUN apt-get install -y vim

RUN cabal install either
RUN cabal install Quickcheck

ADD Main src/Main
ADD Makefile src/
RUN cd src; make

ADD Test src/Test
RUN cd src; make test

RUN cp src/Test/*.hs src/build/
RUN cd src/build; ghc TestCBGP

# ENTRYPOINT ["src/build/TestCBGP"]
