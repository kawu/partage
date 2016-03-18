Partage
==========

**Partage** is a Haskell library dedicated to parsing *tree adjoining grammars* (TAGs).

It implements an Earley-style, bottom-up parser similar to the one described in [1],
with special focus on structure (and, hence, computation) sharing.
Two particular flavours of structure sharing are currently implemented:

  * Subtrees common to different elementary trees are shared amongst them.
    The input TAG, which can be seen as a set of elementary (initial and auxiliary)
    grammar trees, is in fact transformed into an equivalent DAG.
  * Flat production grammar rules representing the individual parts of the DAG
    are then compressed in the form of a minimal FSA. Other forms of
    compression are also provided by the library (e.g. prefix tree).

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


[stack]: http://docs.haskellstack.org "Haskell Tool Stack"
[hackage]: http://hackage.haskell.org/package/partage "Partage Hackage repository"
