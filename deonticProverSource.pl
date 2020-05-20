/*
Copyright 2018 Bjoern Lellmann

    This file is part of deonticProver.

    deonticProver is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    deonticProver is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with deonticProver.  If not, see <http://www.gnu.org/licenses/>.
*/

/* operator definitions etc */
  :- op(400,fy,neg),
     op(500,xfy,and),
     op(600,xfy,or),
     op(700,xfy,->),
     op(800,xfy,=>).

  :- use_module(library(lists)).

/* flag for kleeneing */
  :- set_prolog_flag(kleen,false).


/*   Linear nested sequents are lists of sequents;
     Sequents are pairs (Gamma => Delta) containing the antecedent Gamma
     and the succedent Delta, both as lists of formulae.
     The predicate prv takes as first argument a list of facts, i.e.,
     atomic proposional sequents, as second argument a list of deontic
     assumptions, i.e., non-nested obligation / recommendation
     formulae, and an input sequent Gamma => Delta, where Gamma and
     Delta are lists of formulae.
*/

/* local version (not for online!) */
/* run this in an interactive Prolog session creates the file
   derivation.tex containing the derivation (if the input is
   derivable)
*/

prv(Facts,Srauta,Gamma => Delta) :-
    assumptionsCheck(asmp(Facts,Srauta)),
    saturate(Facts,SaturatedFacts),
	open('derivation.tex',write,Stream1),
	write(Stream1,'\\begin{center}'),
	nl(Stream1),
	write(Stream1,'Facts: $'),
	ppwritefactlist(Stream1,Facts),
	write(Stream1,'\\,$'),
	nl(Stream1),nl(Stream1),
	write(Stream1,'Saturated Facts: $'),
	ppwritefactlist(Stream1,SaturatedFacts),
	write(Stream1,'\\,$'),
	nl(Stream1),nl(Stream1),
	write(Stream1,'Deontic assumptions: $'),
	ppwriteFList(Stream1,Srauta),
	write(Stream1,'\\,$'),
	nl(Stream1),
	write(Stream1,'\\end{center}'),
	nl(Stream1),
	close(Stream1),!,
	prove([], asmp(SaturatedFacts,Srauta), [seq(Gamma,Delta)],T),
        pptree(T),
	open('derivation.tex',append,Stream),
	ppwrite(Stream,T),
	close(Stream), !.

/* Online version */
prv_online(Fml, Facts, Srauta, Filename) :-
    prv_with_filename(Facts, Srauta, seq([],[Fml]), Filename).

prv_with_filename(FmlFacts,Srauta,seq(Gamma,Delta),Filename) :-
    maplist(facts2sequents,FmlFacts,Facts),
    assumptionsCheck(asmp(Facts,Srauta)),
    write('input ok'),
    saturate(Facts,SaturatedFacts),
    open(Filename,write,Stream1),
    write(Stream1,'\\documentclass{article}'),nl(Stream1),
    write(Stream1,'\\usepackage{header}'),nl(Stream1),
    write(Stream1,'\\begin{document}'),nl(Stream1),
    write(Stream1,'\\begin{center}'),
    nl(Stream1),
    write(Stream1,'Facts: $'),
    ppwriteFList(Stream1,FmlFacts),
    write(Stream1,'\\,$'),
    nl(Stream1),nl(Stream1),
    write(Stream1,'Saturated Facts: $'),
    ppwritefactlist(Stream1,SaturatedFacts),
    write(Stream1,'\\,$'),
    nl(Stream1),nl(Stream1),
    write(Stream1,'Deontic assumptions: $'),
    ppwriteFList(Stream1,Srauta),
    write(Stream1,'\\,$'),
    nl(Stream1),nl(Stream1),
    write(Stream1,'Formula: $'),
    ppwriteFList(Stream1,Delta),
    write(Stream1,'$'),
    nl(Stream1),
    write(Stream1,'\\end{center}'),
    nl(Stream1),
    close(Stream1),!,
    prove([], asmp(SaturatedFacts,Srauta), [seq(Gamma,Delta)],T), !,
    open(Filename,append,Stream),
    write(Stream,'\\begin{center}Result: Derivable!\\end{center}'),
    nl(Stream),
    ppwrite(Stream,T),
    write(Stream,'\\end{document}'),
    close(Stream), !.

/* Facts to Sequents /2: takes clause and converts it into sequent. */
facts2sequents(false,[]).
facts2sequents(true,[]).
facts2sequents(A,[A]) :-
    atom(A).
facts2sequents(A and B, List) :-
    facts2sequents(A,List1),
    facts2sequents(B,List2),
    append(List1,List2,List).
facts2sequents(A or B, List) :-
    facts2sequents(A,List1),
    facts2sequents(B,List2),
    append(List1,List2,List).
facts2sequents(A -> B, seq(List1,List2)) :-
    facts2sequents(A,List1),
    facts2sequents(B,List2).


/* Kleene'ing or not
 kleeneUnary is for unary connectives, kleeneBinary for binary ones
 Also implements loop checking by checking that the immediate subformulae
 are not there yet. By default, Kleene'ing is turned ON. Assert the
 predicate nokleeneing to turn it off. Assert the predicate kleeneing to
 turn it on.
*/
kleeneing :- set_prolog_flag(kleen,true).
nokleeneing :- set_prolog_flag(kleen,false).

kleeneUnary(Principal,List,Newlist,_,_) :-
	current_prolog_flag(kleen,false),
	select(Principal,List,Newlist).

kleeneUnary(_,List,Newlist,Subformula,Checklist) :-
	current_prolog_flag(kleen,true),!,
	\+ member(Subformula,Checklist),
	List = Newlist.

kleeneBinary(Principal,List,Newlist,_,_,_,_) :-
	current_prolog_flag(kleen,false),
	select(Principal,List,Newlist).

kleeneBinary(_,List,Newlist,Sub1,Checklist1,Sub2,Checklist2) :-
	current_prolog_flag(kleen,true),!,
	List = Newlist,
	\+ member(Sub1,Checklist1),
	\+ member(Sub2,Checklist2).

/* assumptionsCheck /1: Check that the assumptions are fine */
assumptionsCheck(asmp(Facts,Srauta)) :-
    factsCheck(Facts),
    srautaCheck(Srauta).

/* factsCheck /1: Check that the input is a list of atomic sequents
*/
factsCheck([]).
factsCheck([ seq(Gamma,Delta) | Tail ]) :-
    maplist(atom, Gamma),
    maplist(atom, Delta),
    factsCheck(Tail).


/* srautaCheck /1: Check that the input is a list of non-nested
   obligation formulae
*/
srautaCheck([]).
srautaCheck([Fml|Tail]) :-
    Fml =.. [Op,A,B], 
    member(Op,[obl,rec,for,per]),
    propositional(A),
    propositional(B),
    srautaCheck(Tail),!.

/* propositional /1: Check that the input is a propositional formula
*/
propositional(Literal) :-
    (member(Literal,[false,true])
     ;
     atom(Literal)),
     !.
propositional(Complex) :-
    Complex =.. [Op | Args],
    member(Op,[neg,and,or,->]),
    maplist(propositional,Args),!.


/* saturate /2: true if saturating Start under cuts yields Goal
   (disregarding sequents which can be derived from contained sequents
   using weakening, and initial sequents)
*/

saturate(Start,Goal) :-
    member(seq(Gamma,Delta),Start),
    list_to_set(Gamma,Sigma),
    list_to_set(Delta,Pi),
    \+ member(seq(Sigma,Pi),Start),!,
    saturate([seq(Sigma,Pi)|Start],Goal).
saturate(Start,Goal) :-
    member(seq(Sigma,Pi),Start),
    select(A,Pi,Pi1),
    member(seq(Omega,Theta),Start),
    select(A,Omega,Omega1),
    append(Sigma,Omega1,Gamma),
    append(Pi1,Theta,Delta),
    list_to_set(Gamma,GammaSet),
    list_to_set(Delta,DeltaSet),
    intersection(GammaSet,DeltaSet,[]),
    \+ subsumed(seq(GammaSet,DeltaSet),Start),!,
    saturate([seq(Gamma,Delta)|Start],Goal).
saturate(Goal,Goal).

subsumed(seq(GammaSet,DeltaSet),[seq(Sigma,Pi)|Tail]) :-
    subset(Sigma,GammaSet),
    subset(Pi,DeltaSet)
    ;
    subsumed(seq(GammaSet,DeltaSet),Tail).


/* The predicate prove takes as first argument a list of axioms as
   above, as second a list of assumptions, as third a linear nested
   sequent and as fourth a proof tree. The proof trees are used to
   print the derivation; constructors are the names of the applied
   rules. As first argument they take l (leaf), prop (propositional),
   mon (monotone), cl (classical) to differentiate the different kinds
   of nesting.
*/

/* initial sequents */
prove(_,_,[seq(Gamma,Delta)|Hist],botL(l,[seq(Gamma,Delta)|Hist])) :-
	member(false,Gamma),!.
prove(_,_,[seq(Gamma,Delta)|Hist],topR(l,[seq(Gamma,Delta)|Hist])) :-
	member(true,Delta),!.
prove(_,_,[seq(Gamma,Delta)|Hist],init(l,[seq(Gamma,Delta)|Hist])) :-
    member(F,Gamma), member(F,Delta),!.

/* rule for assumptions from Facts */
prove(_,asmp(Facts,_),[seq(Gamma,Delta)|Hist],fact(l,[seq(Gamma,Delta)|Hist])) :-
    member(seq(Sigma,Pi),Facts),
    subset(Sigma,Gamma),
    subset(Pi,Delta).

/* propositional rules */

/* Completeness for the unKleene'd rules uses that contractions can be
   pushed to below modal rules. The difference between the Kleene'd
   and unKleene'd versions is handled by kleeneUnary and kleeneBinary
   respectively.
*/

/* non-branching rules */
/* Negation */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],negL(p,[seq(Gamma,Delta)|Hist],[T])) :-
	member(neg A, Gamma),
	kleeneUnary(neg A, Gamma, Sigma, A, Delta),
        prove(Axioms,Assumptions,[seq(Sigma,[A|Delta])|Hist],T).
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],negR(p,[seq(Gamma,Delta)|Hist],[T])) :-
	member(neg A, Delta),
	kleeneUnary(neg A, Delta, Pi, A, Gamma),
        prove(Axioms,Assumptions,[seq([A|Gamma],Pi)|Hist],T).

/* Conjunction */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],conjL(p,[seq(Gamma,Delta)|Hist],[T])) :-
	member(A and B, Gamma),
	kleeneBinary(A and B, Gamma,Sigma,A,Gamma,B,Gamma),
        prove(Axioms,Assumptions,[seq([A,B|Sigma],Delta)|Hist],T).

/* Disjunction */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],disjR(p,[seq(Gamma,Delta)|Hist],[T])) :-
	member(A or B, Delta),
	kleeneBinary(A or B,Delta,Pi,A,Delta,B,Delta),
        prove(Axioms,Assumptions,[seq(Gamma,[A,B|Pi])|Hist],T).

/* Implication */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],implR(p,[seq(Gamma,Delta)|Hist],[T])) :-
	member(A -> B, Delta),
	kleeneBinary(A -> B,Delta,Pi,A,Gamma,B,Delta),
        prove(Axioms,Assumptions,[seq([A|Gamma],[B|Pi])|Hist],T).

/* Branching rules */
/* Conjunction */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],conjR(p,[seq(Gamma,Delta)|Hist],[T1,T2])) :-
	member(A and B, Delta),
	kleeneBinary(A and B,Delta,Pi,A,Pi,B,Pi),
        prove(Axioms,Assumptions,[seq(Gamma,[A|Pi])|Hist],T1),
        prove(Axioms,Assumptions,[seq(Gamma,[B|Pi])|Hist],T2).

/* Disjunction */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],disjL(p,[seq(Gamma,Delta)|Hist],[T1,T2])) :-
	member(A or B, Gamma),
	kleeneBinary(A or B,Gamma,Sigma,A,Gamma,B,Gamma),
        prove(Axioms,Assumptions,[seq([A|Sigma],Delta)|Hist],T1),
        prove(Axioms,Assumptions,[seq([B|Sigma],Delta)|Hist],T2).

/* Implication */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],implL(p,[seq(Gamma,Delta)|Hist],[T1,T2])) :-
	member(A -> B, Gamma),
	kleeneBinary(A -> B,Gamma,Sigma,A,Delta,B,Gamma),
        prove(Axioms,Assumptions,[seq([B|Sigma],Delta)|Hist],T1),
        prove(Axioms,Assumptions,[seq(Sigma,[A|Delta])|Hist],T2).

/* for the binary operator obl */

/* oblRight */

/* uses ternary operator tern to model the three premisses of the
   sequent rule proveOblUnfinished: takes a list of axioms, a
   tern(Seq1,Seq2,Seq3), a history and a derivation tree
*/

prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],oblR(p,[seq(Gamma,Delta)|Hist],[T])) :-
    member(obl(A,B), Delta),
    select(obl(A,B), Delta, Pi),
    proveOblUnfinished(Axioms, Assumptions,tern(seq([],[A]), seq([],[B]), seq([B],[])),[seq(Gamma,Pi)|Hist],T).

/* D-rule for Obl */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],oblD(p,[seq(Gamma,Delta)|Hist],[T])) :-
    member(obl(A,B), Gamma),
    select(obl(A,B), Gamma, Sigma),
    proveOblUnfinished(Axioms,Assumptions, tern(seq([A],[]), seq([],[B]), seq([B],[])),[seq(Sigma,Delta)|Hist],T).

/* P-rule for Obl */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],oblP(p,[seq(Gamma,Delta)|Hist],[T])) :-
    member(obl(A,B), Gamma),
    select(obl(A,B), Gamma, Sigma),
    provefinished(Axioms,Assumptions, [], [seq([A],[]),seq(Sigma,Delta)|Hist],T).

/* Clauses for the RECOMMENDATION operator */

/* recRight */

/* uses ternary operator ternRec to model the three premisses of the
   sequent rule proveRecUnfinished: takes a list of axioms, a
   ternRec(Seq1,Seq2,Seq3), a history and a derivation tree
*/

prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],recR(p,[seq(Gamma,Delta)|Hist],[T])) :-
    member(rec(A,B), Delta),
    select(rec(A,B), Delta, Pi),
    proveRecUnfinished(Axioms, Assumptions,ternRec(seq([],[A]), seq([],[B]), seq([B],[])),[seq(Gamma,Pi)|Hist],T).

/* P-rule for Rec */
prove(Axioms,Assumptions,[seq(Gamma,Delta)|Hist],recP(p,[seq(Gamma,Delta)|Hist],[T])) :-
    member(rec(A,B), Gamma),
    select(rec(A,B), Gamma, Sigma),
    provefinished(Axioms,Assumptions, [], [seq([A],[]),seq(Sigma,Delta)|Hist],T).

/* Obl Left */
proveOblUnfinished(Axioms,Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],oblL(obl,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],[T1,T2,T3])) :-
    member( obl(A,B), Sigma),
    select( obl(A,B), Sigma, Omega),
    provefinished(Axioms,Assumptions,[],[seq([A | Gamma1],Delta1),seq(Omega,Pi)|Hist],T1),
    provefinished(Axioms,Assumptions,[],[seq([B | Gamma2],Delta2),seq(Omega,Pi)|Hist],T2),
    provefinished(Axioms,Assumptions,[],[seq(Gamma3,[B | Delta3]),seq(Omega,Pi)|Hist],T3).

/* global assumptions rule */
/* implements the specificity principle */
proveOblUnfinished(Axioms,asmp(Facts,Srauta),tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],ass(obl(X,Y),obl,tern(seq(Gamma1,Delta1),seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist], TreeList)) :-
    member(obl(X,Y),Srauta),
    Prem1 = [seq([X|Gamma1],Delta1), seq(Sigma,Pi)|Hist],
    Prem2 = [seq(Gamma3,[Y|Delta3]), seq(Sigma,Pi)|Hist],
    PremList = [Prem1,Prem2],
    proveList(Axioms,asmp(Facts,Srauta),PremList,TreeList1),
    bagof(obl(V,W),member(obl(V,W),Srauta),OblList), 
    disproveOblAssumptions(Axioms,asmp(Facts,Srauta),tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y),OblList,TreeList2),
    noConflictingMostSpecific(Axioms,asmp(Facts,Srauta),tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y),OblList,TreeList3),
    append(TreeList1,[ndlist(TreeList2)|TreeList3],TreeList).

/* disproveOblAssumptions / 6 */
/* takes a list of axioms, a list of assumptions, a ternary sequent,
   a formula obl(X,Y) and a list Srauta of formulae of the form
   obl(V,W), checks that for each of the formulae from the list Srauta
   at least one of the three sequents relevant is not provable from the
   assumptions in Facts, and returns a list of derivation
   trees displaying which sequent is not derivable.
*/
/* NOTE: We assume that the facts are atomic sequents.
*/

disproveOblAssumptions(_,_, _, _, [], []).

disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y), [obl(Z,W)|TailOblList], [nonder(obl(Z,W),seq([W],[Y]))|TailTreeList]) :-
    \+ prove(Axioms,Assumptions,[seq([W],[Y])],_),
    disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)), obl(X,Y), TailOblList,TailTreeList).

disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y), [obl(Z,W)|TailOblList], [nonder(obl(Z,W),seq(Gamma3,[W|Delta3]))|TailTreeList]) :-
    \+ prove(Axioms,Assumptions,[seq(Gamma3,[W|Delta3])],_),
    disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y), TailOblList,TailTreeList).

disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y), [obl(Z,W)|TailOblList], [nonder(obl(Z,W),seq([Z|Delta1],Gamma1))|TailTreeList]) :-
    \+ prove(Axioms,Assumptions,[seq([Z|Delta1],Gamma1)],_),
    disproveOblAssumptions(Axioms, Assumptions,tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),obl(X,Y), TailOblList,TailTreeList).


/* noConflictingMostSpecific /  */
/* takes list of axioms, assumptions, ternary sequent, formula
   obl(X,Y), and list Srauta of obligations, checks that in Srauta
   there is no most specific obligation relative to the ternary sequent
   which conflicts with obl(X,Y).
*/
noConflictingMostSpecific(_,_,_,_,[],[]).

noConflictingMostSpecific(Axioms, Assumptions, tern(Seq1, Seq2, seq(Gamma3,Delta3)), obl(X,Y), [obl(C,D)|OblList], [nonder(obl(C,D),seq(Gamma3,[D|Delta3]))|TailTreeList]) :-
    \+ prove(Axioms, Assumptions, [seq(Gamma3,[D|Delta3])],_),
    noConflictingMostSpecific(Axioms,Assumptions, tern(Seq1, Seq2, seq(Gamma3,Delta3)), obl(X,Y), OblList, TailTreeList).

noConflictingMostSpecific(Axioms, Assumptions, tern(seq(Gamma,Delta), Seq2, Seq3), obl(X,Y), [obl(C,D)|OblList], [nonder(obl(C,D),seq([C|Delta],Gamma))|TailTreeList]) :-
    \+ prove(Axioms, Assumptions, [seq([C|Delta],Gamma)],_),
    noConflictingMostSpecific(Axioms,Assumptions, tern(seq(Gamma,Delta), Seq2, Seq3), obl(X,Y), OblList, TailTreeList).

noConflictingMostSpecific(Axioms, asmp(Facts,Srauta), Tern, Fml, [obl(C,D)|TailOblList], [Tree|TailTreeList]) :-
    noConflictingAux(Axioms,asmp(Facts,Srauta),Tern,obl(C,D),Srauta,Tree),
    noConflictingMostSpecific(Axioms,asmp(Facts,Srauta), Tern, Fml, TailOblList,TailTreeList).

/* noConflictingAux */
/* For checking that for a particular obligation formula obl(C,D) there
   exists a more specific obligation which entails the original antecedent.
*/
noConflictingAux(Axioms,Assumptions,tern(seq(Gamma1,Delta1),_,seq(Gamma3,Delta3)),obl(C,D),[obl(E,F)|_],der(obl(C,D),obl(E,F),[Tree1,Tree2,Tree3])) :-
    prove(Axioms,Assumptions,[seq(Gamma3,[F|Delta3])],Tree1),
    prove(Axioms,Assumptions,[seq([F],[D])],Tree2),
    prove(Axioms,Assumptions,[seq([E|Gamma1],Delta1)],Tree3).

noConflictingAux(Axioms,Assumptions,Tern,obl(C,D),[_|TailOblList],Tree) :-
    noConflictingAux(Axioms,Assumptions,Tern,obl(C,D),TailOblList,Tree).


/* proveList */
/* proves a list of sequents with histories and gives the list of
   derivation trees
*/
proveList(_,_,[],[]).
proveList(Axioms,Assumptions,[Seq|SeqList],[Tree|TreeList]) :-
    provefinished(Axioms,Assumptions,[],Seq,Tree), 
    proveList(Axioms,Assumptions,SeqList,TreeList).


/* for the binary operator rec */

/* Rec Left */
proveRecUnfinished(Axioms,Assumptions,ternRec(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],recL(rec,ternRec(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],[T1,T2,T3])) :-
    member( rec(A,B), Sigma),
    select( rec(A,B), Sigma, Omega),
    provefinished(Axioms,Assumptions,[],[seq([A | Gamma1],Delta1),seq(Omega,Pi)|Hist],T1),
    provefinished(Axioms,Assumptions,[],[seq([B | Gamma2],Delta2),seq(Omega,Pi)|Hist],T2),
    provefinished(Axioms,Assumptions,[],[seq(Gamma3,[B | Delta3]),seq(Omega,Pi)|Hist],T3).

/* global assumptions rule */
/* implements the specificity principle / monotonicity except for the case
   where the original recommendation from the deontic assumptions has an 
   antecedent which is impossible relative to the facts.
 */
proveRecUnfinished(Axioms,asmp(Facts,Srauta),ternRec(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist],ass(rec(X,Y),rec,ternRec(seq(Gamma1,Delta1),seq(Gamma2,Delta2), seq(Gamma3,Delta3)),[seq(Sigma,Pi)|Hist], TreeList)) :-
    member(rec(X,Y),Srauta),
    Prem1 = [seq([X|Gamma1],Delta1), seq(Sigma,Pi)|Hist],
    Prem2 = [seq(Gamma3,[Y|Delta3]), seq(Sigma,Pi)|Hist],
    PremList = [Prem1,Prem2],
    proveList(Axioms,asmp(Facts,Srauta),PremList,TreeList1),
    disproveRecAssumptions(Axioms,asmp(Facts,Srauta),tern(seq(Gamma1,Delta1), seq(Gamma2,Delta2), seq(Gamma3,Delta3)),rec(X,Y),Srauta,TreeList2),
    append(TreeList1,[ndlist(TreeList2)],TreeList).

/* disproveRecAssumptions / 6 */
/* takes a list of axioms, a list of assumptions, a ternary sequent,
   a formula rec(X,Y) and a list Srauta of formulae of the form
   rec(V,W), checks that for each of the formulae from the list Srauta
   at least one of the three sequents relevant is not provable from the
   assumptions in Facts, and returns a list of derivation
   trees displaying which sequent is not derivable.
*/

disproveRecAssumptions(Axioms,asmp(Facts,Srauta),tern(_, _, _), rec(X,Y), Srauta, [nonder(rec(X,Y),seq([X],[]))]) :-
    \+ prove(Axioms,asmp(Facts,Srauta),[seq([X],[])],_).

/* jump rule */
/* loop checking is implemented by adding an "invisible sequent"
 * invSeq(Gamma,Delta) containing the premiss Gamma => Delta of the
 * current sequent rule into the history. The current sequent rule is
 * closed only if its premiss is not an invisible sequent in the
 * history.
*/
provefinished(Axioms,Assumptions,_,[seq(Gamma,Delta)|Hist],T) :-
	\+ member(seqInv(Gamma,Delta),Hist),
	prove(Axioms,Assumptions,[seq(Gamma,Delta),seqInv(Gamma,Delta)|Hist],T).

/* Pretty printing on screen */
pptree(Term) :-
	pptreeAux(Term,0).

pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == init,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == botL,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == topR,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[p,Hist|[TreeList]]],
	Op \== seq,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3),write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[mon,Hist|[TreeList]]],
	nl, tab(Nest+2), write(Op), write('('),
	ppmonseqlist(Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[obl,Tern,Hist|[TreeList]]],
	Op = oblL,
	nl, tab(Nest+2), write(Op), write('('),
	ppoblseqlist(Tern,Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[rec,TernRec,Hist|[TreeList]]],
	Op = recL,
	nl, tab(Nest+2), write(Op), write('('),
	pprecseqlist(TernRec,Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[_,obl,Tern,Hist|[TreeList]]],
	Op = ass,
	nl, tab(Nest+2), write(Op), write('('),
	ppoblseqlist(Tern,Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[_,rec,TernRec,Hist|[TreeList]]],
	Op = ass,
	nl, tab(Nest+2), write(Op), write('('),
	pprecseqlist(TernRec,Hist),
	pptreeList(TreeList,Nest+2),
	nl, tab(Nest+3), write(')').
pptreeAux(nonder(Fml,Seq),Nest) :-
	nl, tab(Nest+2), write('for '), write(Fml), write(': '),
        write(nonderivable), write('('),
	ppSeq(Seq),
	nl, tab(Nest+3), write(')').
pptreeAux(ndlist(List),Nest) :-
    pptreeList(List,Nest).
pptreeAux(der(Fml1,Fml2,TreeList),Nest) :-
    nl, tab(Nest+2), write('for '), write(Fml1),
    write(': overruled by '),
    write(Fml2), write(': '),
    pptreeList(TreeList,Nest),
    nl, tab(Nest+3), write(')').
pptreeAux(Term,Nest) :-
	Term =.. [Op|[l,Hist]],
	Op == fact,
	nl, tab(Nest+2), write(Op), write('('),
	ppseqlist(Hist),
	nl,tab(Nest+3),write(')').

pptreeList([],_).
pptreeList([H|Tl],Nest) :-
	pptreeAux(H,Nest),
	pptreeList(Tl,Nest).

ppseqlist([]) :-
	write('').
ppseqlist([seqInv(_,_)|Hist]) :-
	ppseqlist(Hist).
ppseqlist([seq(Gamma,Delta)]) :-
	ppSeq(seq(Gamma,Delta)).
ppseqlist([seq(Gamma,Delta),Seq|Hist]) :-
	ppSeq(seq(Gamma,Delta)),
	write(' // '),
	ppseqlist([Seq|Hist]).

ppmonseqlist([]) :-
	write('').
ppmonseqlist([seqInv(_,_)|Hist]) :-
	ppmonseqlist(Hist).
ppmonseqlist([seq(Gamma,Delta),[]]) :-
	ppSeq(seq(Gamma,Delta)).
ppmonseqlist([seq(Gamma,Delta)|Hist]) :-
	ppSeq(seq(Gamma,Delta)),
	write(' /mon/ '),
	ppseqlist(Hist).

% ppoblseqlist: takes Tern,History
ppoblseqlist([]) :-
    write('').
ppoblseqlist(tern(First,Second,Third),Hist) :-
    ppSeq(First),
    write(';'),
    ppSeq(Second),
    write(';'),
    ppSeq(Third),
    write(' /obl/ '),
    ppseqlist(Hist).

% pprecseqlist: takes TernRec,History
pprecseqlist([]) :-
    write('').
pprecseqlist(ternRec(First,Second,Third),Hist) :-
    ppSeq(First),
    write(';'),
    ppSeq(Second),
    write(';'),
    ppSeq(Third),
    write(' /rec/ '),
    ppseqlist(Hist).

ppSeq(seq(Gamma,Delta)) :-
	write(Gamma),write('=>'),write(Delta).


/* writing LaTeX into the output file */
/* ppwrite /2 takes the stream and the proof tree */
ppwrite(Stream,Tree) :-
	nl(Stream),write(Stream,'\\['),nl(Stream),
	write(Stream,'\\begin{adjustbox}{max width=\\textwidth}'),nl(Stream),
	ppwriteAux(Stream,Tree,0),
	nl(Stream),write(Stream,'\\end{adjustbox}'),
	nl(Stream),write(Stream,'\\]'),nl(Stream),nl(Stream),!.

/* ppwriteAux /3 takes the stream, the proof tree, and the current nesting depth */
/* case distinction according to the last applied rule */
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == init, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\init]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == botL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\botL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == topR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\topR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[clfin,Dual,Hist|[List]]],
	Op == close, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\jump]{'),
	ppwriteNest(Stream,clfin,[Dual|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == negL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\negL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == negR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\negR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == conjL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\conjL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == conjR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\conjR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == disjL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\disjL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == disjR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\disjR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == implL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\implL]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == implR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\implR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == oblR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\oblR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == oblD, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\oblD]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == oblP, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\oblP]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[obl,Tern,Hist|[List]]],
	Op == oblL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\oblL]{'),
	ppwriteNest(Stream,obl,[Tern|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}'),!.
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[obl(X,Y),obl,Tern,Hist|[List]]],
	Op == ass, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\ass: '),
	ppwriteFml(Stream,obl(X,Y)),
        write(Stream,']{'),
	ppwriteNest(Stream,obl,[Tern|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == recR, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\recR]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op == recP, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\recP]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[rec,TernRec,Hist|[List]]],
	Op == recL, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\recL]{'),
	ppwriteNest(Stream,rec,[TernRec|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}'),!.
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[rec(X,Y),rec,TernRec,Hist|[List]]],
	Op == ass, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\ass: '),
	ppwriteFml(Stream,rec(X,Y)),
        write(Stream,']{'),
	ppwriteNest(Stream,rec,[TernRec|Hist]),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').
ppwriteAux(Stream,nonder(Fml,Seq),Nest) :-
        tab(Stream,Nest),
	write(Stream, '\\text{for }'),
	ppwriteFml(Stream,Fml),
	write(Stream,':& \\not\\entails '),
	ppwriteseqlist(Stream,[Seq]).
ppwriteAux(Stream,ndlist(List),Nest) :-
    tab(Stream, Nest+2),
    write(Stream,'\\begin{array}[b]{ll}'),
    ppwriteArrayList(Stream,List,Nest+2),
    nl(Stream), write(Stream, '\\end{array}').
ppwriteAux(Stream,der(Fml1,Fml2,TreeList),Nest) :-
    tab(Stream, Nest+2),
    write(Stream, '\\begin{array}[b]{l}\\text{for }'),
    ppwriteFml(Stream,Fml1),
    write(Stream,':\\\\ \\text{overruled by }'),
    ppwriteFml(Stream,Fml2),
    write(Stream,':\\end{array} &'),
    nl,
    ppwriteList(Stream,TreeList,Nest).
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[l,Seq]],
	Op == fact, tab(Stream,Nest+2),
	write(Stream,'\\infer[\\fact]{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').

/* catches all other cases */
ppwriteAux(Stream,Term,Nest) :-
	Term =.. [Op|[p,Seq|[List]]],
	Op \== seq, tab(Stream,Nest+2),
	write(Stream,'\\infer['),write(Stream,Op), write(Stream,']{'),
	ppwriteNest(Stream,p,Seq),write(Stream,'}{'), nl(Stream),
	ppwriteList(Stream,List,Nest+2),
	nl(Stream),tab(Stream,Nest+3),write(Stream,'}').

/* LaTex nested sequents */
ppwriteNest(Stream,p,Seq) :-
        reverse(Seq,Seq2),
	ppwriteseqlist(Stream,Seq2).
ppwriteNest(Stream,mon,[Seq|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\m]'),
	ppwriteseqlist(Stream,[Seq]).
ppwriteNest(Stream,cl,[dual(Seq1,Seq2)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\e] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,'\\right]').
ppwriteNest(Stream,clfin,[dual(Seq1,Seq2)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\e\\fin] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,'\\right]').
ppwriteNest(Stream,obl,[tern(Seq1,Seq2,Seq3)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\obl] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq3]),
	write(Stream,'\\right]').
ppwriteNest(Stream,rec,[ternRec(Seq1,Seq2,Seq3)|Hist]) :-
        reverse(Hist,Hist2),
	ppwriteseqlist(Stream,Hist2),
	write(Stream,'\\lns[\\rec] \\left['),
	ppwriteseqlist(Stream,[Seq1]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq2]),
	write(Stream,';'),
	ppwriteseqlist(Stream,[Seq3]),
	write(Stream,'\\right]').

/* LaTeX a list of premisses */
ppwriteList(_,[],_).
ppwriteList(Stream,[H|[]],Nest) :-
	ppwriteAux(Stream,H,Nest).
ppwriteList(Stream,[H|Tl],Nest) :-
	ppwriteAux(Stream,H,Nest),
	nl(Stream),tab(Stream,Nest+2),write(Stream,'&'), nl(Stream),
	ppwriteList(Stream,Tl,Nest).

/* LaTex a list of premisses in an array */
ppwriteArrayList(_,[],_).
ppwriteArrayList(Stream,[H|[]],Nest) :-
	ppwriteAux(Stream,H,Nest).
ppwriteArrayList(Stream,[H|Tl],Nest) :-
	ppwriteAux(Stream,H,Nest),
	nl(Stream),tab(Stream,Nest+2),write(Stream,'\\\\'), nl(Stream),
	ppwriteArrayList(Stream,Tl,Nest).

/* LaTeX a list of sequents */
ppwriteseqlist(Stream,[]) :- write(Stream,'').
ppwriteseqlist(Stream,[seqInv(_,_)|Hist]) :-
        ppwriteseqlist(Stream,Hist).
ppwriteseqlist(Stream,[seq(Gamma,Delta)|[]]) :-
	ppwriteFList(Stream,Gamma),write(Stream,' \\seq '),ppwriteFList(Stream,Delta).
ppwriteseqlist(Stream,[seq(Gamma,Delta),Seq|Hist]) :-
	ppwriteFList(Stream,Gamma),write(Stream,' \\seq '),ppwriteFList(Stream,Delta),
	write(Stream,' \\lns '),ppwriteseqlist(Stream,[Seq|Hist]).

/* LaTeX a list of facts */
ppwritefactlist(Stream,[]) :- write(Stream,'').
ppwritefactlist(Stream,[seq(Gamma,Delta)|[]]) :-
    write(Stream,'('),
    ppwriteFList(Stream,Gamma),
    write(Stream,' \\seq '),
    ppwriteFList(Stream,Delta),
    write(Stream,')').
ppwritefactlist(Stream,[seq(Gamma,Delta),Seq|Hist]) :-
    write(Stream,'('),
    ppwriteFList(Stream,Gamma),
    write(Stream,' \\seq '),
    ppwriteFList(Stream,Delta),
    write(Stream,')'),
    write(Stream,' \\; , \\; '),
    ppwritefactlist(Stream,[Seq|Hist]).


/* LaTeX a list of formulae */
ppwriteFList(_,[]).
ppwriteFList(Stream,[Fml]) :-
	ppwriteFml(Stream,Fml).
ppwriteFList(Stream,[H,G|Tail]) :-
	ppwriteFml(Stream,H),write(Stream,','),ppwriteFList(Stream,[G|Tail]).

/* LaTeX a formula */
ppwriteFml(Stream,false) :-
	write(Stream,' \\bot ').
ppwriteFml(Stream,true) :-
	write(Stream,' \\top ').
ppwriteFml(Stream,Term) :-
	atom(Term), write(Stream,'\\texttt{'),write(Stream,Term),write(Stream,'}').
ppwriteFml(Stream,neg(Fml)) :-
	write(Stream,' \\neg '),ppwriteFml(Stream,Fml).
ppwriteFml(Stream,and(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\land '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,or(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\lor '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,->(Fml1,Fml2)) :-
	write(Stream,'('),ppwriteFml(Stream,Fml1),
	write(Stream,' \\to '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,obl(Fml1,Fml2)) :-
	write(Stream,'\\obl('),ppwriteFml(Stream,Fml1),
	write(Stream,' / '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,rec(Fml1,Fml2)) :-
	write(Stream,'\\rec('),ppwriteFml(Stream,Fml1),
	write(Stream,' / '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,for(Fml1,Fml2)) :-
	write(Stream,'\\for('),ppwriteFml(Stream,Fml1),
	write(Stream,' / '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
ppwriteFml(Stream,per(Fml1,Fml2)) :-
	write(Stream,'\\per('),ppwriteFml(Stream,Fml1),
	write(Stream,' / '),
	ppwriteFml(Stream,Fml2),write(Stream,')').
