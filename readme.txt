deonticProver v.1.0 readme.txt
==============================

Copyright 2018 Bjoern Lellmann

This file is part of deonticProver.

deonticProver is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.
deonticProver is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTIBILITY of FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with deonticProver. If not, see <http://www.gnu.org/licenses/>.


Contents
--------
The following files should be included with the download:

- readme.txt (this file)
- deonticProverSource.pl
- header.sty
- output.tex
- gpl.txt

deonticProver is a prototype implementation of proof search in a weak
deontic logic under global assumptions. The global assumptions are
rendered consistent using the specificity principle, stating that more
specific obligations overrule less specific ones.

The prover is based on the article "Resolving conflicting obligations
in Mimamsa: A sequent-based approach" (published in the proceedings of
DEON 2018), see also
http://logic.at/staff/lellmann/static/publications/2018/DEON18final.pdf



Input syntax
------------

Formulae are built from the grammar

  Phi ::= atom | false | true | neg Phi | Phi and Phi | Phi or Phi |
            Phi -> Phi | obl(Phi, Phi) | rec(Phi, Phi)

where atom is any Prolog atom, e.g., p,q,r,... a1,a2,a3,...
The usual conventions about binding strength of the connectives apply,
i.e., 'neg' binds stronger than 'and' binds stronger than 'or' binds
stronger than '->'.


Usage
-----

You need a copy of SWI Prolog installed on your machine.
Load deonticProverSource.pl into SWIPL. To run the prover, enter

  ?- prv( Facts, DeonticAssumptions, Gamma => Delta ).

Here Facts is a list of atomic sequents of the form

  seq([ p1, p2, ... ], [ q1, q2, ... ])

with the p1, p2, q1, q2, ... atoms. Further, DeonticAssumptions is a
list of deontic assumptions, i.e., non-nested obligation or
recommendation formulae of the form obl(A,B) or rec(A,B) where A,B are
formulae without deontic operators. The input sequent Gamma => Delta
consists of two lists Gamma, Delta of formulae.


Example: Chariot makers and Agnihotra
-------------------------------------

Here, Facts is the list 

  [ seq([chmk],[sudra]), seq([sudra, mhk],[false]) ]

The assumptions in DeonticAssumptions are given by

  [ obl(agn,true), obl(neg agn, neg mhk), obl(agn, chmk) ]

Possible questions are whether a sudra should perform the Agnihotra:

  ?- prv( [ seq([chmk],[sudra]), seq([sudra, mhk],[false]) ], [ obl(agn,true), obl(neg adn, neg mhk), obl(agn, chmk) ], [] => [obl(agn,sudra)] ).

or whether a sudra who is also a teacher must not perform the Agnihotra:

  ?- prv( [ seq([chmk],[sudra]), seq([sudra, mhk],[false]) ], [ obl(agn,true), obl(neg adn, neg mhk), obl(agn, chmk) ], [] => [obl(neg agn,teacher and sudra)] ).

If the input is derivable, deonticProver produces a latex file
derivation.tex containing the derivation. To compile the output, run
Latex or PDFLatex on the file output.tex. Latex is available under

  https://www.latex-project.org
