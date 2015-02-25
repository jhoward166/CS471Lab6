/*******************************************************************
        CS471 - Programming Languages
        Assignment Lab6 due: 10/10/2014
        Author: Howard, Joseph (jhoward4@binghamton.edu)
        Date: 10/09/2014
*********************************************************************/
/**
 * Rename file hw6.pl

 * Printing out the whole list:

      http://www.swi-prolog.org/FAQ/AllOutput.html

 ** You can find practice Prolog practice
     http://www.ic.unicamp.br/~meidanis/courses/mc336/2009s2/prolog/problemas/
   
*/

/* The only built-predicates you may use are:
     is, //, /, +, -, ^, *,=..,>, <,
     atom, is_list, functor, arg, integer, number, member, append
*/

/* 1: Below are 3 structures that representation expression trees.
      (Op is any Prolog operator.) This can be done in 3 clause.
      expTree does NOT have to be include as facts in the program.

     expTree(Op,Lt,Rt).
     expTree(lit,Value).
     expTree(Op,T).

    Write a Prolog program:
         eval(Tree,Value).
    which succeeds if Value is the result of computing the expressions
    represented by an expression tree.  For example:

   ?- eTree4(T),eval(T,V).
   T = expTree(float, expTree(sin, expTree(/, expTree(lit, pi), expTree(lit, 2))))
   V = 1.0

   ?- eTree1(T),eval(T,V).
   T = expTree(+, expTree(lit, 5), expTree(*, expTree(lit, 3), expTree(lit, 2)))
   V = 11.

   Below are trees you can use for testing.
*/

eTree1(expTree('+',
	      expTree(lit, 5),
	      expTree('*',
	           expTree(lit, 3),
	           expTree(lit, 2)
	       )
       )
 ).


eTree2(expTree('*',
	expTree('-',
	     expTree(lit, -3),
	     expTree(lit, 2)
	 ),

	expTree('+',
	      expTree(lit, 3),
	      expTree('-',
		     expTree(lit, 2)
		   )
	   )
	 )
 ).

eTree3(expTree('*',
	expTree('min',
	     expTree(lit, -3),
	     expTree(lit, 2)
	 ),

	expTree('+',
	     expTree(lit, 3),
	     expTree('-',
		    expTree(lit, 2)
		    )
	     )
	 )
 ).


eTree4(expTree(float,
	   expTree('sin',
	        expTree('/',
		       expTree(lit, pi),
		       expTree(lit, 2)
		     )
	    )
	   )
 ).

eval(expTree(lit,Value),Value).
eval(expTree(Op,T), Value):- eval(T,X), Y=..[Op,X], Value is Y.
eval(expTree(Op,Lt,Rt), Value):- eval(Lt,X), eval(Rt,Y), Z=..[Op,X,Y], Value is Z.


/** 2: Define a predicate concatALL(+NestedLists, -C), concatenate all the 
      elements in the NestedLists into a list C of only single terms.
   i.e.
   ?- concatALL([[1],[a,b,c],[],[100,91]],C).
   C = [1, a, b, c, 100, 91].
   ?- concatALL([[1],[a,[b,[c]],[]], [[[100],91],x] ],C). 
   C = [1, a, b, c, 100, 91, x].
   ?- concatALL([[],[foo(a),[[^,=,[+]],[c]],[]], [[[+(1,2)],91],*] ],C).
   C = [foo(a), ^, =, +, c, 1+2, 91, *] .

   This can be done in only 3 clauses.... think What NOT how.  You may include
   "!" to prevent generating incorrect alternative solutions.
*/
concatALL([],[]).
concatALL(A,B):- not(is_list(A)), B = [A].
concatALL([H|[]],B):- concatALL(H,B), !.
concatALL([H|T],B) :- concatALL(H,X), concatALL(T,Y), append(X,Y,B), !.


/* 3: Below is a database of US coins. */

coin(dollar, 100).
coin(half, 50).
coin(quarter, 25).
coin(dime,10).
coin(nickel,5).
coin(penny,1).



/* 3: Write a predicate change/2 that given the change amount, computes the ways
      in which we can give change.  Use USA's  coin denominations above.

      The predicate "change" is such that an positive integer S,
      change(S,T) "returns" a list of tuples, T, where the tuple contains the
      name of the denomination (Name,Count),
      the atom Name of the denomination and integer Count that gives
      the number of coins of each denomination in D that add up to S.
      For example::
        ?- change(127,L).
        L = [ (dollar, 1), (quarter, 1), (penny, 2)]
        Yes
        ?- change(44,L).
        L = [ (quarter, 1), (dime, 1), (nickel, 1), (penny, 4)] ;
        L = [ (quarter, 1), (dime, 1), (penny, 9)] ;
        L = [ (quarter, 1), (nickel, 3), (penny, 4)] ;
        L = [ (quarter, 1), (penny, 19)] ;
        L = [ (dime, 4), (penny, 4)] ;
        L = [ (nickel, 8), (penny, 4)] ;
        L = [ (penny, 44)] ;
        No

      The Coin Changing problem is an interesting problem usually studied in
      Algorthms.  http://condor.depaul.edu/~rjohnson/algorithm/coins.pdf is a
      nice discussion.
      Think about (no need to turn in)
         1) How could we generalize this problem to handle different
            denominations?
         2) What are the different techinques to find the change with the
            fewest number of coins ?
         3) What happens if the order of the "coin" facts change?

  */
change(0,[]).
change(C,L):- coin(A,B), C >= B, D is C mod B, E is C//B, change(D,M), append([(A, E)],M,L).


/*4 :(0pts) (Do not turn in.)
   Given the 4 logically equivalent predicates try to predict the outcome of 
   ?- subList1(X,[a]),fail.
   ?- subList2(X,[a]),fail.
   ?- subList3(X,[a]),fail.
   ?- subList4(X,[a]),fail.
   Try to understand why some produce "ERROR: Out of global stack"

*/ 
subList1(S,L):-append(_,S,P),append(P,_,L).
subList2(S,L):-append(P,_,L),append(_,S,P).
subList3(S,L):-append(S,_,T),append(_,T,L).
subList4(S,L):-append(_,T,L),append(S,_,T).

/* Using writes to see the backtracking */

subList1w(S,L):-write('1-1'),append(_,S,P),write(' 1-2'),write(P),append(P,_,L).
subList2w(S,L):-write('2-1'),append(P,_,L),write(' 2-2'),write(P),append(_,S,P).
subList3w(S,L):-write('3-1'),append(S,_,T),write(' 3-2'),write(T),append(_,T,L).
subList4w(S,L):-write('4-1'),append(_,T,L),write(' 4-2'),write(T),append(S,_,T).

