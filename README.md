Partage
==========

**Partage** is a library and a tool dedicated to parsing *tree adjoining
grammars* (TAGs).  It supports both adjunction and sister-adjunction.

It implements two kinds of parsers -- an Earley-style, bottom-up parser [1]
with special focus on structure (and, hence, computation) sharing [2], and an
A\* parser [3,4]. 

### Earley-style parser

The Earley-style parser implements two flavors of grammar compression:

  * Subtrees common to different elementary trees are shared.  The input TAG is
    transformed into an equivalent directed acyclic graph (DAG).
  * Flat production grammar rules representing the individual parts of the DAG
    are compressed into an FSA.  The default choice is a prefix-tree
    compression, although other forms of compression are also possible (e.g.,
    minimal FSA).

### A\* parser

The A\* parser works best on the results of dependency-aware supertagging in
which:

  * To each position in the input sentence a distribution of TAG elementary
    trees (supertags) which can be anchored at this position is assigned.  This
    comes from classic statistical supertagging.
  * To each position in the sentence the distribution of the possible heads is
    also assigned.  This can result from statistical dependency parsing.

The probability of a TAG derivation in this setting is defined as the product
of the probabilities of the participating supertags and the product of the
probabilities of the entailed dependency arcs.  The A\* parser then gurantees
to find a most probable derivation without searching the entire space of the
possible derivations.

Grammar compression is also used in the A\* parser, but to a very limited
extent.

    
[![Build Status](https://travis-ci.org/kawu/partage.svg)](https://travis-ci.org/kawu/partage)


Installation
------------

It is recommanded to install *partage* using the [Haskell Tool Stack][stack],
which you will need to downoload and install on your machine beforehand.
Then clone this repository into a local directory and use stack to install the
library by running:

    stack install


References
----------

[1] Miguel A. Alonso, David Cabrero, Eric de la Clergerie and Manuel
Vilares, *Tabular Algorithms for TAG Parsing*, in Proc. of EACL'99,
Ninth Conference of the European Chapter of the Association for
Computational Linguistics, pp. 150-157, Bergen, Norway, 1999.

[2] Jakub Waszczuk, Agata Savary, Yannick Parmentier, *Enhancing Practical TAG
Parsing Efficiency by Capturing Redundancy*, 21st International Conference on
Implementation and Application of Automata (CIAA 2016),
([PDF](https://hal.archives-ouvertes.fr/hal-01309598v2/document)).


[stack]: http://docs.haskellstack.org "Haskell Tool Stack"
[hackage]: http://hackage.haskell.org/package/partage "Partage Hackage repository"
