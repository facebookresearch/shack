# shack: Semantic of Hack

The goal of this project is to formally define the semantic of the [Hack](https://hacklang.org/) language.
It will enable us to explore the semantic of existing and new features of this language,
and their interactions.

This project aims at giving a better understanding of what the semantic of
a Hack program is, and help us move towards a more sound type system.

## Requirements
Shack is formalized in the [Coq](https://coq.inria.fr/) proof assistant, using
the [Iris](https://iris-project.org/) framework. Both dependencies can be
installed via the Ocaml package manager [opam](https://opam.ocaml.org/).

Shack requires or works with:
* Coq 8.15.1
* Iris dev.2022-05-13.1.ebb89887

## Building shack
The whole project using Coq's Makefile setup to build. Everything can be built
by running the following command:

```
$ make
```

If the Makefile itself needs to be regenerated, one can run the following
command:
```
$ coq_makefile -f _CoqProject -o Makefile
```

See the [CONTRIBUTING](CONTRIBUTING.md) file for how to help out.


## License
shack is using the MIT license, as found in the LICENSE file.
