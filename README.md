<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Mczify

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/math-comp/mczify/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/mczify/actions/workflows/docker-action.yml




This small library enables the use of the Micromega arithmetic solvers of Coq
for goals stated with the definitions of the Mathematical Components library
by extending the zify tactic.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Rocq/Coq versions: 8.18 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 2.3 or later
  - [MathComp](https://math-comp.github.io) algebra
- Rocq/Coq namespace: `mathcomp.zify`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Mczify
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-mathcomp-zify
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/mczify.git
cd mczify
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## File contents

- `zify_ssreflect.v`: Z-ification instances for the `coq-mathcomp-ssreflect`
  library
- `zify_algebra.v`: Z-ification instances for the `coq-mathcomp-algebra`
  library
- `zify.v`: re-exports all the Z-ification instances
- `ssrZ.v`: provides a minimal facility for reasoning about `Z` and relating
  `Z` and `int`
