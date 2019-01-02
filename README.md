Partage
==========

**Partage** is a Haskell library and a tool dedicated to parsing *tree
adjoining grammars* (TAGs).  It supports both adjunction and sister-adjunction.

It implements two kinds of parsers -- an Earley-style, bottom-up parser [1]
with special focus on structure (and, hence, computation) sharing [2], and an
A\* parser [3,4].
    
[![Build Status](https://travis-ci.org/kawu/partage.svg)](https://travis-ci.org/kawu/partage)

#### Earley-style parser

The Earley-style parser implements two flavors of grammar compression:

  * Subtrees common to different elementary trees are shared.  The input TAG is
    in fact transformed into an equivalent directed acyclic graph (DAG).
  * Flat production grammar rules representing the individual parts of the DAG
    are compressed into an FSA.  The default choice is a prefix-tree
    compression, although other forms of compression are also possible (e.g.,
    minimal FSA).

#### A\* parser

The A\* parser works best on the results of dependency-aware supertagging in
which:

  * To each position in the input sentence a distribution of TAG elementary
    trees (supertags) which can be anchored at this position is assigned.  This
    comes from classic statistical supertagging.
  * To each position in the sentence the distribution of the possible heads is
    also assigned.  This can result from statistical dependency parsing.

The probability of a TAG derivation in this setting is defined as the product
of the probabilities of the participating supertags multiplied by the product
of the probabilities of the entailed dependency arcs.  The A\* parser then
gurantees to find a most probable derivation without searching the entire space
of the possible derivations.

Grammar compression is also used in the A\* parser, but to a very limited
extent.


Installation
------------

First you will need to download and install the [Haskell Tool Stack][stack].
Then run the following commands:

    git clone https://github.com/kawu/partage.git
    cd partage
    stack install

The last command builds the `partage` command-line tool and (on Linux) places
it in the `~/.local/bin/` directory by default. Installation on Windows, even
though not tested, should be also possible.

You can also run the following command in the local repository to make sure
that all the tests succeed:

    stack test


Data format
-----------

Partage works with tab-separated values (`.tsv`) files, with the individual
sentences separated by blank lines. Each non-blank line corresponds to a token
in the corresponding sentence and contains the following columns:

  * ID of the token
  * word form
  * head distribution
  * 1st supertag
  * 2nd supertag
  * ...

The head distribution entry has the form of `|` separated pairs, each pair consisting
of a head token ID and the corresponding probability (separated by a colon).
If this entry is empty, no head dependency constraints are assumed for the
corresponding position.

Each supertag entry consists of a supertag represented in the bracketed format
and the corresponding probability (also separated by a colon).  Here is an
example of how an input sentence represented in this format can look like.

```
1	John	2:1.0	(NP (N <>)):1.0
2	eats	0:1.0	(SENT (NP) (VP (V <>))):0.6	(SENT (NP) (VP (V <>) (NP))):0.4
3	an	4:0.5|1:0.5	(NP* (D <>)):1.0
4	apple	2:0.5|0:0.5	(NP (N <>)):1.0
```

In general, the token IDs have to correspond to the range `1..n` where `n` is
the sentence length.  ID `0` is reserved for the special dummy token
representing the root.  Another, larger example can be found in
`examples/french.tsv`.


Usage
-----

Use the following command to parse an input `test.tsv` file using A\*:

    partage astar -i test.tsv -s SENT

The `-s` option allows to specify the start symbol (i.e. the label of the root
of the resulting parse).  Assuming the example sentence presented above, this
command should result in:

```
1	John	2	(NP (N John))
2	eats	0	(SENT (NP) (VP (V eats) (NP)))
3	an	4	(NP* (D an))
4	apple	2	(NP (N apple))
```

In order to run the Earley-style parser on the same input file, run:

    partage earley -i test.tsv -s SENT

Note that the Earley-style parser ignores the dependency-related constraints
(third column of the input file).  The output is also different, it consists of
the set of parsed trees.  For the example sentence above:

```
(SENT (NP (N John)) (VP (V eats) (NP (D an) (N apple))))
```

Run `partage astar --help` and `partage earley --help` to learn more about the
possible parsing options.


References
----------

[1] Miguel A. Alonso, David Cabrero, Eric de la Clergerie and Manuel
Vilares, *Tabular Algorithms for TAG Parsing*, in Proc. of EACL'99,
Ninth Conference of the European Chapter of the Association for
Computational Linguistics, pp. 150-157, Bergen, Norway, 1999.

[2] Jakub Waszczuk, Agata Savary, Yannick Parmentier, *Enhancing Practical TAG
Parsing Efficiency by Capturing Redundancy*, 21st International Conference on
Implementation and Application of Automata (CIAA 2016), Seoul, South Korea,
2016, ([PDF](https://hal.archives-ouvertes.fr/hal-01309598v2/document)).

[3] Jakub Waszczuk, Agata Savary, and Yannick Parmentier, *Promoting multiword
expressions in A\* TAG parsing*, 26th International Conference on Computational
Linguistics (COLING 2016), Osaka, Japan, 2016,
([PDF](https://aclweb.org/anthology/C/C16/C16-1042.pdf)).

[4] Jakub Waszczuk, Agata Savary, and Yannick Parmentier, *Multiword
Expression-Aware A\* TAG Parsing Revisited*, 13th International Workshop on
Tree Adjoining Grammars and Related Formalisms, Umeå, Sweden, 2017.
([PDF](http://www.aclweb.org/anthology/W17-6209)).


[stack]: http://docs.haskellstack.org "Haskell Tool Stack"
[hackage]: http://hackage.haskell.org/package/partage "Partage Hackage repository"
