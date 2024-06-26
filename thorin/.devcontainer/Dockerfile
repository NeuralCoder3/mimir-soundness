FROM coqorg/coq:8.17

RUN opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
RUN opam install --yes coq.8.17.1 coq-autosubst coq-iris