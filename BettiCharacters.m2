--------------------------------------------------------------------------------
-- Copyright 2021  Federico Galetto
--
-- This program is free software: you can redistribute it and/or modify it under
-- the terms of the GNU General Public License as published by the Free Software
-- Foundation, either version 3 of the License, or (at your option) any later
-- version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
-- FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
-- details.
--
-- You should have received a copy of the GNU General Public License along with
-- this program.  If not, see <http://www.gnu.org/licenses/>.
--------------------------------------------------------------------------------


newPackage(
     "BettiCharacters",
     Version => "1.0.1",
     Date => "June 30, 2021",
     AuxiliaryFiles => false,
     Authors => {{Name => "Federico Galetto",
     	       Email => "galetto.federico@gmail.com",
	       HomePage => "http://math.galetto.org"}},
     Headline => "finite group characters on free resolutions and graded modules",
     PackageImports => {"SimpleDoc"},
     DebuggingMode => false
     )


export {
    "action",
    "Action",
    "ActionOnComplex",
    "ActionOnGradedModule",
    "actors",
    "character",
    "characterTable",
    "Character",
    "CharacterTable",
    "decomposeCharacter",
    "inverseRingActors",
    "labels",
    "numActors",
    "ringActors",
    "Sub"
    }


----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

Action = new Type of HashTable
ActionOnComplex = new Type of Action
ActionOnGradedModule = new Type of Action
Character = new Type of HashTable
CharacterTable = new Type of HashTable

----------------------------------------------------------------------
-- New Methods-
---------------------------------------------------------------------

-- constructor for action on resolutions and modules
-- optional argument Sub=>true means ring actors are passed
-- as one-row matrices of substitutions, Sub=>false means
-- ring actors are passed as matrices
action = method(Options=>{Sub=>true})

-- constructor for action on resolutions
-- INPUT:
-- 1) a resolution
-- 2) a list of actors on the ring variables
-- 3) a list of actors on the i-th module of the resolution
-- 4) homological index i
action(ChainComplex,List,List,ZZ):=ActionOnComplex=>op->(C,l,l0,i) -> (
    --check C is a homogeneous min free res over a poly ring over a field
    R := ring C;
    if not isPolynomialRing R then (
	error "action: expected a complex over a polynomial ring";
	);
    if not isField coefficientRing R then (
	error "action: expected coefficients in a field";
	);
    if not all(length C,i -> isFreeModule C_(i+min(C))) then (
	error "action: expected a complex of free modules";
	);
    if not isHomogeneous C then (
	error "action: complex is not homogeneous";
	);
    --if user passes handcrafted complex give warning message
    if not C.?Resolution then (
	print "";
	print "Warning: complex is not a resolution computed by M2.";
	print "This could lead to errors or meaningless results.";
	);
    --check the matrix of the action on the variables has right size
    n := dim R;
    if not all(l,g->numColumns(g)==n) then (
	error "action: ring actor matrix has wrong number of columns";
	);
    if op.Sub then (
    	if not all(l,g->numRows(g)==1) then (
	    error "action: expected ring actor matrix to be a one-row substitution matrix";
	    );
    	--convert variable substitutions to matrices
	l=apply(l,g->(vars R)\\lift(g,R));
	) else (
	--if ring actors are matrices they must be square
    	if not all(l,g->numRows(g)==n) then (
	    error "action: ring actor matrix has wrong number of rows";
	    );
	--lift action matrices to R for uniformity with
	--input as substitutions
	l=apply(l,g->promote(g,R));
	);
    --check list of group elements has same length
    if #l != #l0 then (
	error "action: lists of actors must have equal length";
	);
    --check size of module actors matches rank of starting module
    r := rank C_i;
    if not all(l0,g->numColumns(g)==r and numRows(g)==r) then (
	error "action: module actor matrix has wrong number of rows or columns";
	);
    --store everything into a hash table
    new ActionOnComplex from {
	cache => new CacheTable from {
	    (symbol actors,i) => apply(l0,g->map(C_i,C_i,g))
	    },
	(symbol ring) => R,
	(symbol target) => C,
	(symbol numActors) => #l,
	(symbol ringActors) => l,
	(symbol inverseRingActors) => apply(l,inverse),
	(symbol actors) => apply(l0,g->map(C_i,C_i,g)),
	}
    )

-- shortcut constructor for resolutions of quotient rings
-- actors on generator are assumed to be trivial
action(ChainComplex,List) := ActionOnComplex => op -> (C,l) -> (
    R := ring C;
    l0 := toList(#l:(id_(R^1)));
    action(C,l,l0,min C,Sub=>op.Sub)
    )

-- returns number of actors
numActors = method()
numActors(Action) := ZZ => A -> A.numActors

-- returns action on ring variables
-- Sub=>true returns one-row substitution matrices
-- Sub=>false returns square matrices
ringActors = method(Options=>{Sub=>true})
ringActors(Action) := List => op -> A -> (
    if op.Sub then apply(A.ringActors,g->(vars ring A)*g)
    else A.ringActors
    )

-- returns the inverses of the actors on ring variables
-- same options as ringActors
inverseRingActors = method(Options=>{Sub=>true})
inverseRingActors(Action) := List => op -> A -> (
    if op.Sub then apply(A.inverseRingActors,g->(vars ring A)*g)
    else A.inverseRingActors
    )

-- returns various group actors
actors = method(TypicalValue=>List)

-- returns actors passed by user when constructing the action
actors(Action) := List => A -> A.actors

-- returns actors on resolution in a given homological degree
-- if homological degree is not the one passed by user,
-- the actors are computed and stored
actors(ActionOnComplex,ZZ) := List => (A,i) -> (
    -- homological degrees where action is already cached
    places := apply(keys A.cache, k -> k#1);
    C := target A;
    if zero(C_i) then return toList(numActors(A):map(C_i));
    if i > max places then (
    	-- function for actors of A in hom degree i
    	f := A -> apply(inverseRingActors A,actors(A,i-1),
	    -- given a map of free modules C.dd_i : F <-- F',
	    -- the inverse group action on the ring (as substitution)
	    -- and the group action on F, computes the group action on F'
	    (gInv,g0) -> sub(C.dd_i,gInv)\\(g0*C.dd_i)
	    );
    	-- make cache function from f and run it on A
    	((cacheValue (symbol actors,i)) f) A
    	) else (
    	-- function for actors of A in hom degree i
    	f = A -> apply(inverseRingActors A,actors(A,i+1), (gInv,g0) ->
	    -- given a map of free modules C.dd_i : F <-- F',
	    -- the inverse group action on the ring (as substitution)
	    -- and the group action on F', computes the group action on F
	    -- it is necessary to transpose because we need a left factorization
	    -- but M2's command // always produces a right factorization
	    transpose(transpose(C.dd_(i+1))\\transpose(sub(C.dd_(i+1),gInv)*g0))
	    );
    	-- make cache function from f and run it on A
    	((cacheValue (symbol actors,i)) f) A
	)
    )

-- method for returning characters of various action types
character = method()

-- construct a finite dimensional character
-- INPUT:
-- 1) polynomial ring (dictates coefficients and degrees)
-- 2) integer: character length (or number of actors)
-- 3) hash table for raw character: (homdeg,deg) => character
character(PolynomialRing,ZZ,HashTable) := Character => (R,cl,H) -> (
    -- check first argument is a polynomial ring over a field
    if not isPolynomialRing R or not isField coefficientRing R then (
	error "character: expected polynomial ring over a field";
	);
    dl := degreeLength R;
    -- check keys are in the right format
    k := keys H;
    if any(k, i -> class i =!= Sequence or #i != 2 or
	class i#0 =!= ZZ or class i#1 =!= List) then (
	error "character: expected keys of the form (ZZ,List)";
	);
    -- check degree vectors are allowed
    degs := apply(k,last);
    if any(degs, i -> #i != dl or any(i, j -> class j =!= ZZ)) then (
	error "character: expected integer degree vectors of length " | toString(dl);
	);
    -- check character vectors are allowed
    v := values H;
    if any(v, i -> #i != cl or any(i, j -> class j =!= R)) then (
	error "character: expceted characters in input ring and of length" | toString(cl);
	);
    new Character from {
	cache => new CacheTable,
	(symbol ring) => R,
	(symbol numActors) => cl,
	(symbol characters) => H,
	}
    )

-- return the character of one free module of a resolution
-- in a given homological degree
character(ActionOnComplex,ZZ) := Character => (A,i) -> (
    -- if complex is zero in hom degree i, return empty character
    if zero (target A)_i then (
	return new Character from {
	    cache => new CacheTable,
	    (symbol ring) => ring A,
	    (symbol numActors) => numActors A,
	    (symbol characters) => hashTable {},
	    };
	);
    -- function for character of A in hom degree i
    f := A -> (
	-- separate degrees of i-th free module
	degs := hashTable apply(unique degrees (target A)_i, d ->
	    (d,positions(degrees (target A)_i,i->i==d))
	    );
	-- create raw character from actors
	H := applyPairs(degs,
	    (d,indx) -> ((i,d),
		apply(actors(A,i), g -> trace g_indx^indx)
		)
	    );
	new Character from {
	    cache => new CacheTable,
	    (symbol ring) => ring A,
	    (symbol numActors) => numActors A,
	    (symbol characters) => H,
	    }
	);
    -- make cache function from f and run it on A
    ((cacheValue (symbol character,i)) f) A
    )

-- return characters of all free modules in a resolution
-- by repeatedly using previous function
character ActionOnComplex := HashTable => A -> (
    C := target A;
    directSum for i from min(C) to min(C)+length(C) list character(A,i)
    )

----------------------------------------------------------------------
-- Overloaded Methods
----------------------------------------------------------------------

-- get object acted upon
target(Action) := A -> A.target

-- printing for Action type
net Action := A -> (
    (net class target A)|" with "|(net numActors A)|" actors"
    )

-- get polynomial ring acted upon
ring Action := PolynomialRing => A -> A.ring

-- printing for Character type
net Character := c -> (
    if c.characters =!= hashTable {} then (
    	bottom := stack(" ",
    	    stack (horizontalJoin \ apply(sort pairs c.characters,(k,v) -> (net k, " => ", net v)))
    	    )
	) else bottom = null;
    stack("Character over "|(net c.ring), bottom)
    )

-- direct sum of characters
-- modeled after code in Macaulay2/Core/matrix.m2
Character ++ Character := Character => directSum
directSum Character := c -> Character.directSum (1 : c)
Character.directSum = args -> (
    -- check ring is the same for all summands
    R := (args#0).ring;
    if any(args, c -> c.ring =!= R)
    then error "directSum: expected characters all over the same ring";
    -- check character length is the same for all summands
    cl := (args#0).numActors;
    if any(args, c -> c.numActors != cl)
    then error "directSum: expected characters all of the same length";
    C := new Character from {
	cache => new CacheTable,
	(symbol ring) => R,
	(symbol numActors) => cl,
	-- add raw characters
	(symbol characters) => fold( (c1,c2) -> merge(c1,c2,plus),
	    apply(args, c -> c.characters) ),
	};
    C
    )


----------------------------------------------------------------------
-- New methods for ActionOnGradedModule
----------------------------------------------------------------------

-- constructor for action on various kinds of graded modules
-- INPUT:
-- 1) a graded module (polynomial ring or quotient, module, ideal)
-- 2) a list of actors on the ring variables
-- 3) a list of actors on the generators of the ambient free module
action(PolynomialRing,List,List) :=
action(QuotientRing,List,List) :=
action(Ideal,List,List) :=
action(Module,List,List):=ActionOnGradedModule=>op->(M,l,l0) -> (
    -- check M is graded over a poly ring over a field
    -- the way to get the ring depends on the class of M
    if instance(M,Ring) then (
	R := ambient M;
	) else (
	R = ring M;
	);
    if not isPolynomialRing R then (
	error "action: expected a module/ideal/quotient over a polynomial ring";
	);
    if not isField coefficientRing R then (
	error "action: expected coefficients in a field";
	);
    if not isHomogeneous M then (
	error "action: module/ideal/quotient is not graded";
	);
    --check matrix of action on variables has right size
    n := dim R;
    if not all(l,g->numColumns(g)==n) then (
	error "action: ring actor matrix has wrong number of columns";
	);
    if op.Sub then (
    	if not all(l,g->numRows(g)==1) then (
	    error "action: expected ring actor matrix to be a one-row substitution matrix";
	    );
    	--convert variable substitutions to matrices
	l=apply(l,g->(vars R)\\lift(g,R));
	) else (
	--if ring actors are matrices they must be square
    	if not all(l,g->numRows(g)==n) then (
	    error "action: ring actor matrix has wrong number of rows";
	    );
	--lift action matrices to R for uniformity with
	--input as substitutions
	l=apply(l,g->promote(g,R));
	);
    --check list of group elements has same length
    if #l != #l0 then (
	error "action: lists of actors must have equal length";
	);
    --check size of module actors matches rank of ambient module
    if instance(M,Module) then (
    	F := ambient M;
	) else ( F = R^1; );
    r := rank F;
    if not all(l0,g->numColumns(g)==r and numRows(g)==r) then (
	error "action: module actor matrix has wrong number of rows or columns";
	);
    --turn input object into a module M'
    if instance(M,QuotientRing) then (
	M' := coker presentation M;
	) else if instance(M,Module) then (
	M' = M;
	) else (
	M' = module M;
	);
    --store everything into a hash table
    new ActionOnGradedModule from {
	cache => new CacheTable,
	(symbol ring) => R,
	(symbol target) => M,
	(symbol numActors) => #l,
	(symbol ringActors) => l,
	(symbol inverseRingActors) => apply(l,inverse),
	(symbol actors) => apply(l0,g->map(F,F,g)),
	(symbol module) => M',
	(symbol relations) => image relations M',
	}
    )

-- shortcut constructor when actors on generator are trivial
action(PolynomialRing,List) :=
action(QuotientRing,List) :=
action(Ideal,List) :=
action(Module,List) := ActionOnGradedModule => op -> (M,l) -> (
    if instance(M,Module) then (
    	l0 := toList(#l:(id_(ambient M)));
	) else if instance(M,Ideal) then (
    	l0 = toList(#l:(id_(ambient module M)));	
	) else (
    	l0 = toList(#l:(id_(module ambient M)));	
	);
    action(M,l,l0,Sub=>op.Sub)
    )

-- returns actors on component of given multidegree
-- the actors are computed and stored
actors(ActionOnGradedModule,List) := List => (A,d) -> (
    M := A.module;
    -- get basis in degree d as map of free modules
    -- how to get this depends on the class of M
    b := ambient basis(d,M);
    if zero b then return toList(numActors(A):map(source b));
    -- function for actors of A in degree d
    f := A -> apply(ringActors A,actors A, (g,g0) -> (
    	    --g0*b acts on the basis of the ambient module
	    --sub(-,g) acts on the polynomial coefficients
	    --result must be reduced against module relations
	    --then factored by original basis to get action matrix
	    (sub(g0*b,g) % A.relations) // b
	    )
	);
    -- make cache function from f and run it on A
    ((cacheValue (symbol actors,d)) f) A
    )

-- returns actors on component of given degree
actors(ActionOnGradedModule,ZZ) := List => (A,d) -> actors(A,{d})

-- return character of component of given multidegree
character(ActionOnGradedModule,List) := Character => (A,d) -> (
    acts := actors(A,d);
    if all(acts,zero) then (
	return new Character from {
	    cache => new CacheTable,
	    (symbol ring) => ring A,
	    (symbol numActors) => numActors A,
	    (symbol characters) => hashTable {},
	    };
	);
    -- function for character of A in degree d
    f := A -> (
	new Character from {
	    cache => new CacheTable,
	    (symbol ring) => ring A,
	    (symbol numActors) => numActors A,
	    (symbol characters) => hashTable {(0,d) => apply(acts, trace)},
	    }
	);
    -- make cache function from f and run it on A
    ((cacheValue (symbol character,d)) f) A
    )

-- return character of component of given degree
character(ActionOnGradedModule,ZZ) := Character => (A,d) -> (
    character(A,{d})
    )

-- return character of components in a range of degrees
character(ActionOnGradedModule,ZZ,ZZ) := Character => (A,lo,hi) -> (
    if not all(gens ring A, v->(degree v)=={1}) then (
	error "character: expected a ZZ-graded polynomial ring";
    	);
    directSum for d from lo to hi list character(A,d)
    )


---------------------------------------------------------------------
-- New Methods for CharacterTable and decompositions ----------------
---------------------------------------------------------------------

-- method to construct character tables
characterTable = method();

-- main character table constructor
-- INPUT:
-- 1) list of conjugacy class sizes
-- 2) matrix of irreducible character values
-- 3) ring over which to construct the table
-- 4) list, permutation of conjugacy class inverses
characterTable(List,Matrix,PolynomialRing,List) :=
(conjSize,charTable,R,perm) -> (
    n := #conjSize;
    -- check all arguments have the right size
    if numRows charTable != n or numColumns charTable != n then (
	error "characterTable: expected matrix size to match number of conjugacy classes";
	);
    if #perm != n then (
	error "characterTable: expected permutation size to match number of conjugacy classes";
	);
    -- promote character matrix to R
    X := try promote(charTable,R) else (
	error "characterTable: could not promote character table to given ring";
	);
    -- check permutation has the right entries
    if set perm =!= set(1..n) then (
	error "characterTable: expected a permutation of {1,..," | toString(n) | "}";
	);
    -- check orthogonality relations
    ordG := sum conjSize;
    C := diagonalMatrix(R,conjSize);
    P := map(R^n)_(apply(perm, i -> i-1));
    m := C*transpose(X*P);
    -- if x is a character in a one-row matrix, then x*m is the one-row matrix
    -- containing the inner products of x with the irreducible characters
    if X*m != ordG*map(R^n) then (
	error "characterTable: orthogonality relations not satisfied";
	);
    -- create default labels
    l := for i to n-1 list "X"|toString(i);
    new CharacterTable from {
	(symbol size) => conjSize,
	(symbol table) => X,
	(symbol ring) => R,
	(symbol inverse) => perm,
	(symbol matrix) => m,
	(symbol labels) => l,
	}
    )

-- printing for character tables
net CharacterTable := T -> (
    -- top row of character table
    a := {{""} | T.size};
    -- body of character table
    b := apply(pack(1,T.labels),entries T.table,(i,j)->i|j);
    stack("Character table over "|(net T.ring)," ",
	netList(a|b,BaseRow=>1,Alignment=>Right,Boxes=>{{1},{1}},HorizontalSpace=>2)
	)
    )

-- character decomposition
decomposeCharacter = method();
decomposeCharacter(Character,CharacterTable) := (C,T) -> (
    -- check character and table are over same ring
    R := C.ring;
    if T.ring =!= R then (
	error "decomposeCharacter: expected character and table over the same ring";
	);
    -- check number of actors is the same
    if C.numActors != #T.size then (
	error "decomposeCharacter: expected character length does not match table";
	);
    ord := sum T.size;
    applyValues(C.characters, char -> (
	    prod := flatten entries (1/ord*promote(matrix{char},R)*T.matrix);
	    pos := positions(prod, v -> not zero v);
	    hashTable pack(2,mingle((T.labels)_pos,prod_pos))
	    )
	)
    )

----------------------------------------------------------------------
-- Documentation
----------------------------------------------------------------------

beginDocumentation()

doc ///

Node
    Key
    	BettiCharacters
    Headline
    	finite group characters on free resolutions and graded modules
    Description
    	Text
	    This package contains functions for computing characters
	    of free resolutions and graded modules equipped with
	    the action of a finite group.
	    
	    Let $R$ be a positively graded polynomial ring over a
	    field $\Bbbk$, and $M$ a finitely generated graded
	    $R$-module. Suppose $G$ is a finite group whose order
	    is not divisible by the characteristic of $\Bbbk$.
	    Assume $G$ acts $\Bbbk$-linearly on $R$ and $M$
	    by preserving degrees, and distributing over
	    $R$-multiplication.
	    If $F_\bullet$ is a minimal free resolution of $M$, and
	    $\mathfrak{m}$ denotes the maximal ideal generated by the variables
	    of $R$, then each $F_i / \mathfrak{m}F_i$ is a graded
	    $G$-representation. We call the
	    characters of the representations $F_i / \mathfrak{m}F_i$
	    the {\bf Betti characters} of $M$, since
	    evaluating them at the identity element of $G$ returns
	    the usual Betti numbers of $M$.
	    Moreover, the graded
	    components of $M$ are also $G$-representations.
	    
	    This package provides functions to
	    compute the Betti characters and the characters of
	    graded components of $M$
	    based on the algorithms in @arXiv("2106.14071","F. Galetto - Finite group characters on free resolutions")@.
	    The package is designed to
	    be independent of the group; the user may provide the
	    necessary information about the group action in the
	    form of matrices and/or substitutions into the variables
	    of the ring. See the menu below for using this package
	    to compute some examples from the literature.
    Subnodes
    	:Defining actions
      	action
      	:Computing actions and characters
	actors
        character
    	:Examples from the literature
      	"BettiCharacters Example 1"
      	"BettiCharacters Example 2"
      	"BettiCharacters Example 3"

	    
Node
   Key
       "BettiCharacters Example 1"
   Headline
       Specht ideals / subspace arrangements
   Description
    Text
    	In this example, we identify the Betti characters of the
	Specht ideal associated	with the partition (4,3).
	The action of the symmetric group on the resolution of
	this ideal is described in	
	@arXiv("2010.06522",
	    "K. Shibata, K. Yanagawa - Minimal free resolutions of the Specht ideals of shapes (n−2,2) and (d,d,1)")@.
	The same ideal is also the ideal of the 4-equals
	subspace arrangement in a 7-dimensional affine space.
	This point of view is explored in
	@HREF("https://doi.org/10.1007/s00220-014-2010-4",
	    "C. Berkesch, S. Griffeth, S. Sam - Jack polynomials as fractional quantum Hall states and the Betti numbers of the (k+1)-equals ideal")@.
	where the action of the symmetric group on the resolution
	is also described.
	
	We begin by constructing the ideal using the function
	@TO "SpechtModule::spechtPolynomials"@
	provided by the package @TO "SpechtModule::SpechtModule"@.
	We compute a minimal free resolution and its Betti table.
    Example
    	R=QQ[x_1..x_7]
	needsPackage "SpechtModule"
	I=ideal values spechtPolynomials(new Partition from {5,2},R)
	RI=res I
	betti RI
    Text
    	Next we set up the group action on the resolution.
	The group is the symmetric group on 7 elements.
	Its conjugacy classes are determined by cycle types,
	which are in bijection with partitions of 7.
	Once the action is set up, we compute the Betti characters.
    Example	
	G = for p in partitions(7) list (
    	    L := gens R;
    	    g := for u in p list (
    		l := take(L,u);
    		L = drop(L,u);
    		rotate(1,l)
    		);
    	    matrix { flatten g }
    	    )
	A=action(RI,G)
	elapsedTime c=character A
    Text
    	To make sense of these characters we decompose them
	against	the character table of the symmetric group,
	which can be computed using the function
	@TO "SpechtModule::characterTable"@
	provided by the package @TO "SpechtModule::SpechtModule"@.
	First we form a hash table with the irreducible characters.
	Then we define a function that computes the multiplicities
	of the irreducible characters in a given character.
	Finally, we apply this function to the Betti characters
	computed above.
    Example
    	irrReps = new HashTable from pack(2,
    	    mingle {
	    	partitions 7,
	    	apply(entries (characterTable 7)#values, r -> mutableMatrix{r})
	    	}
    	    )
    Text
    	As expected from the general theory, we find a single
	irreducible representation in each homological degree.	


Node
   Key
       "BettiCharacters Example 2"
   Headline
       Symbolic powers of star configurations
   Description
    Text
    	In this example, we identify the Betti characters of the
	third symbolic power of a monomial star configuration.
	The action of the symmetric group on the resolution of
	this ideal is described in Example 6.5 of
	@HREF("https://doi.org/10.1016/j.jalgebra.2020.04.037",
	    "J. Biermann, H. De Alba, F. Galetto, S. Murai, U. Nagel, A. O'Keefe, T. Römer, A. Seceleanu - Betti numbers of symmetric shifted ideals")@,
	and belongs to the larger class of symmetric shifted
	ideals.
	
	We start by constructing the ideal,
	and compute a minimal free resolution and its Betti table.
    Example
	R=QQ[x_1..x_6]
	I=intersect(apply(subsets(gens R,4),x->(ideal x)^3))
	RI=res I
	betti RI
    Text
    	Next we set up the group action on the resolution.
	The group is the symmetric group on 6 elements.
	Its conjugacy classes are determined by cycle types,
	which are in bijection with partitions of 6.
	Once the action is set up, we compute the Betti characters.
    Example	
	G = for p in partitions(6) list (
	    L := gens R;
	    g := for u in p list (
		l := take(L,u);
		L = drop(L,u);
		rotate(1,l)
		);
	    matrix { flatten g }
	    )
	A=action(RI,G)
	elapsedTime c=character A
    Text
    	To make sense of these characters we decompose them
	against	the character table of the symmetric group,
	which can be computed using the function
	@TO "SpechtModule::characterTable"@
	provided by the package @TO "SpechtModule::SpechtModule"@.
	First we form a hash table with the irreducible characters.
	Then we define a function that computes the multiplicities
	of the irreducible characters in a given character.
	Finally, we apply this function to the Betti characters
	computed above.
    Example
	needsPackage "SpechtModule"
	irrReps = new HashTable from pack(2,
	    mingle {
		partitions 6,
		apply(entries (characterTable 6)#values, r -> mutableMatrix{r})
		}
	    )
    Text
    	The description provided in
	@HREF("https://doi.org/10.1016/j.jalgebra.2020.04.037",
	    "J. Biermann, H. De Alba, F. Galetto, S. Murai, U. Nagel, A. O'Keefe, T. Römer, A. Seceleanu - Betti numbers of symmetric shifted ideals")@
	uses representations induced from products of smaller
	symmetric groups. In order, to compare with the results
	obtained here one may use the Littlewood-Richardson rule
	to decompose induced representations into a direct sum
	of irreducibles.


Node
   Key
       "BettiCharacters Example 3"
   Headline
       Klein configuration of points
   Description
    Text
    	In this example, we identify the Betti characters of the
	defining ideal of the Klein configuration of points in the
	projective plane and its square.
	The defining ideal of the Klein configuration is
	explicitly constructed in Proposition 7.3 of
	@HREF("https://doi.org/10.1093/imrn/rnx329",
	    "T. Bauer, S. Di Rocco, B. Harbourne, J. Huizenga, A. Seceleanu, T. Szemberg - Negative Curves on Symmetric Blowups of the Projective Plane, Resurgences, and Waldschmidt Constants")@.
	We start by constructing the ideal, its square, and both
	their resolutions and Betti tables. In order to later use
	characters, we work over the cyclotomic field obtained by
	adjoining a primitive 7th root of unity to $\mathbb{Q}$.
	(This example was precompiled by the package author.)
    Example
    	kk=toField(QQ[a]/ideal(sum apply(7,i->a^i)))
	R=kk[x,y,z]
	f4=x^3*y+y^3*z+z^3*x
	H=jacobian transpose jacobian f4
	f6=-1/54*det(H)
	I=minors(2,jacobian matrix{{f4,f6}})
	RI=res I
	betti RI
	I2=I^2;
	RI2=res I2
	betti RI2
    Text
	The unique simple group of order 168 acts as described
	in §2.2 of @HREF("https://doi.org/10.1093/imrn/rnx329",
	"BDHHSS")@. In particular, the group is generated by the
	elements @TT "g"@ of order 7, @TT "h"@ of order 3, and
	@TT "i"@ of order 2, and is minimally defined over the
	7th cyclotomic field. In addition, we consider the identity,
	the inverse of @TT "g"@,
	and another element @TT "j"@ of order 4 as representatives
	of the conjugacy classes of the group.
	The action of the group on the resolution of
	both ideals is described in the second proof of
	Proposition 8.1.
    Example
	g=matrix{{a^4,0,0},{0,a^2,0},{0,0,a}}
	h=matrix{{0,1,0},{0,0,1},{1,0,0}}
	i=(2*a^4+2*a^2+2*a+1)/7 * matrix{
    	    {a-a^6,a^2-a^5,a^4-a^3},
    	    {a^2-a^5,a^4-a^3,a-a^6},
    	    {a^4-a^3,a-a^6,a^2-a^5}
    	    }
	j=-1/(2*a^4+2*a^2+2*a+1) * matrix{
    	    {a^5-a^4,1-a^5,1-a^3},
    	    {1-a^5,a^6-a^2,1-a^6},
    	    {1-a^3,1-a^6,a^3-a}
    	    }
	G={id_(R^3),i,h,j,g,inverse g};
	A1=action(RI,G,Sub=>false)
	A2=action(RI2,G,Sub=>false)
	elapsedTime character A1
	elapsedTime character A2
    Text
	The character of the resolution of the ideal shows the
	free module in homological degree two is a direct sum
	of two trivial representations. It follows that its second
	exterior power is also trivial. As observed in the second
	proof of Proposition 8.1 in @HREF("https://doi.org/10.1093/imrn/rnx329",
	"BDHHSS")@, the free module in homological degree 3 in the
    	resolution of the square of the ideal is exactly this
	second exterior power and a trivial representation.
	
	In alternative, we can compute the symbolic square of the
	ideal modulo the ordinary square. The component of degree
	21 of this quotient matches the generators of the last
	module in the resolution of the ordinary square in degree
	24 (by local duality); in
	particular, it is a trivial representation. We can verify
	this directly.
    Example
	needsPackage "SymbolicPowers"
	Is2 = symbolicPower(I,2);
	M = Is2 / I2;
	B = action(M,G,Sub=>false)
	elapsedTime character(B,21)


Node
    Key
    	Action
    Headline
    	the class of all finite group actions
    Description
    	Text
	    This class is provided by the package
	    @TO BettiCharacters@.
    Subnodes
    	ActionOnComplex
	ActionOnGradedModule
	(net,Action)
	(ring,Action)
	ringActors
	(target,Action)
	    
Node
    Key
    	ActionOnComplex
    Headline
    	the class of all finite group actions on complexes
    Description
    	Text
	    This class is provided by the package
	    @TO BettiCharacters@.
	    
Node
    Key
    	ActionOnGradedModule
    Headline
    	the class of all finite group actions on graded modules
    Description
    	Text
	    This class is provided by the package
	    @TO BettiCharacters@.

	    
Node
    Key
    	Character
    Headline
    	the class of all characters of finite group representations
    Description
    	Text
	    This class is provided by the package
	    @TO BettiCharacters@.
    Subnodes
	(directSum,Character)
	(net,Character)
    	    
Node
    Key
    	action
    Headline
    	define finite group action
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to set up a finite group action on
	    a minimal free resolution or graded module.
	    See the specific use cases for more details.
    Subnodes
    	Action
	(action,ChainComplex,List,List,ZZ)
	(action,Module,List,List)
	Sub
	    
Node
    Key
    	(action,ChainComplex,List,List,ZZ)
    	(action,ChainComplex,List)
    Headline
    	define finite group action on a resolution
    Usage
    	A=action(C,G)
	A=action(C,G,G',i)
    Inputs
    	C:ChainComplex
	    a minimal free resolution over a polynomial ring @TT "R"@
	G:List
	    of group elements acting on the variables of @TT "R"@
	G':List
	    of group elements acting on a basis of @TT "C_i"@
	i:ZZ
	    a homological degree
    Outputs
    	A:ActionOnComplex
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to define the action of a finite group
	    on the minimal free resolution of a module over a
	    polynomial ring with coefficients in a field.
	    After setting up the action, use the function
	    @TO character@ to compute the Betti characters.
	    
	    The input @TT "G"@ is a @TO List@ of group elements
	    acting on the vector space spanned by the variables
	    of the ring @TT "R"@. By default, these elements are
	    passed as one-row substitution matrices as those
	    accepted by @TO substitute@. The optional input
	    @TO Sub@ may be used to pass these elements as square
	    matrices. For the function to work, @TT "G"@ can be an
	    arbitrary list of group elements however, in order to
	    obtain a complete representation theoretic description
	    of the characters, @TT "G"@ should be a list of
	    representatives of the conjugacy classes of the group.
	    
	    The example below sets up the action of a symmetric
	    group on the resolution of a monomial ideal.
	    The symmetric group acts by permuting the four
	    variables of the ring. The conjugacy classes of
	    permutations are determined by their cycle types,
	    which are in bijection with partitions. In this case,
	    we consider five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
    	Example
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    RI = res I
	    G = {matrix{{x_2,x_3,x_4,x_1}},
    		 matrix{{x_2,x_3,x_1,x_4}},
    		 matrix{{x_2,x_1,x_4,x_3}},
    		 matrix{{x_2,x_1,x_3,x_4}},
    		 matrix{{x_1,x_2,x_3,x_4}} }
	    A = action(RI,G)
	Text
	    The group elements acting on the ring can be recovered
	    using @TO ringActors@, while their inverses can be
	    recovered using @TO inverseRingActors@.
	    To recover just the number of group elements,
	    use @TO numActors@.
	Example
	    ringActors A
	    inverseRingActors A
	    numActors A
	Text
	    The simplified version of this function suffices when
	    dealing with resolutions of quotients of the ring
	    @TT "R"@ by an ideal as in the previous example.
	    In this case, the first module in the resolution is
	    @TT "R"@ and it is assumed that the group acts
	    trivially on the generator of this first module.
	    
	    When resolving modules or when more flexibility is 
	    needed, one may use the general version of the function.
	    In this case, it is necessary to specify a homological
	    degree @TT "i"@ and a list of group elements acting on
	    the module @TT "C_i"@. The group elements are passed
	    as a @TO List@ @TT "G'"@ of matrices written with
	    respect to the basis of @TT "C_i"@ used by Macaulay2.
	    Moreover, the group elements in @TT "G'"@ must match
	    (in number and order) the elements in @TT "G"@.
	    
	    To illustrate, we set up the action on the resolution
	    of the ideal in the previous example considered as a
	    module (as opposed to the resolution of the quotient
	    by the ideal). In this case, the elements of @TT "G'"@
	    are the permutation matrices obtained by acting with
	    elements of @TT "G"@ on the span of the minimal
	    generators of the ideal. For simplicity, we construct
	    these matrices by permuting columns of the identity.
    	Example
	    M = module I
	    RM = res M
	    G' = { (id_(R^6))_{2,4,5,0,1,3},
    		   (id_(R^6))_{2,0,1,4,5,3},
    		   (id_(R^6))_{0,4,3,2,1,5},
    		   (id_(R^6))_{0,2,1,4,3,5},
    		    id_(R^6) }
	    action(RM,G,G',0)
	Text
	    By changing the last argument, it is possible to
	    specify the action of the group on any module of the
	    resolution. For example, suppose we wish to construct
	    the action of the symmetric group on the resolution
	    of the canonical module of the quotient in the first
	    example. In this case, it will be more convenient to
	    declare a trivial action on the last module of the
	    resolution rather than figuring out the action on the
	    first module (i.e., the generators of the canonical
	    module). This can be achieved as follows.
    	Example
	    E = Ext^3(R^1/I,R^{-4})
	    RE = res E
	    G'' = toList(5:id_(R^1))
	    action(RE,G,G'',3)
    Caveat
    	This function determines if the complex @TT "C"@ is a free
	resolution computed by Macaulay2. If this is not the case,
	then the function produces a warning to inform the user that
	later computations (i.e., Betti characters) may fail or
	return meaningless results.


Node
    Key
    	(action,Module,List,List)
    	(action,Module,List)
    	(action,Ideal,List,List)
    	(action,Ideal,List)
    	(action,PolynomialRing,List,List)
    	(action,PolynomialRing,List)
    	(action,QuotientRing,List,List)
    	(action,QuotientRing,List)
    Headline
    	define finite group action on a graded module
    Usage
    	A=action(M,G)
	A=action(M,G,G')
    Inputs
    	M:Module
	    a graded module/ideal/quotient over a polynomial ring @TT "R"@
	G:List
	    of group elements acting on the variables of @TT "R"@
	G':List
	    of group elements acting on the ambient module of @TT "M"@
    Outputs
    	A:ActionOnGradedModule
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to define the action of a finite group
	    on a graded module over a polynomial ring
	    with coefficients in a field. This includes also an
	    ideal in the polynomial ring, a quotient of the
	    polynomial ring, and the polynomial ring itself.
	    After setting up the action, use the function
	    @TO character@ to compute the characters of graded
	    components.
	    
	    The input @TT "G"@ is a @TO List@ of group elements
	    acting on the vector space spanned by the variables
	    of the ring @TT "R"@. By default, these elements are
	    passed as one-row substitution matrices as those
	    accepted by @TO substitute@. The optional input
	    @TO Sub@ may be used to pass these elements as square
	    matrices. For the function to work, @TT "G"@ can be an
	    arbitrary list of group elements however, in order to
	    obtain a complete representation theoretic description
	    of the characters, @TT "G"@ should be a list of
	    representatives of the conjugacy classes of the group.
	    
	    The example below sets up the action of a symmetric
	    group on a polynomial ring, a monomial ideal,
	    and the corresponding quotient.
	    The symmetric group acts by permuting the four
	    variables of the ring. The conjugacy classes of
	    permutations are determined by their cycle types,
	    which are in bijection with partitions. In this case,
	    we consider five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
    	Example
	    R = QQ[x_1..x_4]
	    G = {matrix{{x_2,x_3,x_4,x_1}},
    		 matrix{{x_2,x_3,x_1,x_4}},
    		 matrix{{x_2,x_1,x_4,x_3}},
    		 matrix{{x_2,x_1,x_3,x_4}},
    		 matrix{{x_1,x_2,x_3,x_4}} }
	    action(R,G)
	    I = ideal apply(subsets(gens R,2),product)
    	    action(I,G)
	    Q = R/I
	    A = action(Q,G)
	Text
	    The group elements acting on the ring can be recovered
	    using @TO ringActors@.
	    To recover just the number of group elements,
	    use @TO numActors@.
	Example
	    ringActors A
	    numActors A
	Text
	    The simplified version of this function assumes that
	    the group acts trivially on the generator of the
	    polynomial ring.
	    
	    When working with a module @TT "M"@, one needs to
	    declare the action of the group on a basis of the free
	    ambient module of @TT "M"@.
	    Unless this action is trivial, it can be specified
	    using the third argument, a list @TT "G'"@ of matrices
	    written with respect to the basis of the free ambient
	    module of  @TT "M"@ used by Macaulay2.
	    Moreover, the group elements in @TT "G'"@ must match
	    (in number and order) the elements in @TT "G"@.
	    
	    To illustrate, we set up the action on the canonical
	    module of the quotient in the previous example.
	    We obtain the list of group elements @TT "G'"@ for the
	    canonical module by computing the action on its
	    resolution.
    	Example
	    E = Ext^3(R^1/I,R^{-4})
	    RE = res E
	    G'' = toList(5:id_(R^1))
	    B = action(RE,G,G'',3)
	    G' = actors(B,0)
	    action(E,G,G')


Node
    Key
    	actors
	(actors,Action)
    Headline
    	group elements of an action
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    When called (without additional arguments) on an object
	    of type @TO Action@,
	    this function returns the list of group elements
	    originally provided by the user to act on
	    a module or in a given homological
	    degree of a resolution. Note that these group elements
	    are assumed to trivial, unless otherwise indicated
	    when constructing the action.

	    The user may specify additional arguments to obtain
	    elements of the group acting in other degrees.
	    See the specific use cases for more details.
    	Example	    
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    M = module I
	    RM = res M
	    G = {matrix{{x_2,x_3,x_4,x_1}},
    		 matrix{{x_2,x_3,x_1,x_4}},
    		 matrix{{x_2,x_1,x_4,x_3}},
    		 matrix{{x_2,x_1,x_3,x_4}},
    		 matrix{{x_1,x_2,x_3,x_4}} }
	    G' = { (id_(R^6))_{2,4,5,0,1,3},
    		   (id_(R^6))_{2,0,1,4,5,3},
    		   (id_(R^6))_{0,4,3,2,1,5},
    		   (id_(R^6))_{0,2,1,4,3,5},
    		    id_(R^6) }
	    A = action(RM,G,G',0)
	    actors(A)
	    B = action(M,G)
	    actors(B)
    SeeAlso
    	action	    
    Subnodes
 	(actors,ActionOnComplex,ZZ)  
 	(actors,ActionOnGradedModule,List)
     	inverseRingActors
     	numActors
	    
Node
    Key
	(actors,ActionOnComplex,ZZ)
    Headline
    	group elements of action on resolution
    Usage
    	actors(A,i)
    Inputs
    	A:ActionOnComplex
	    a finite group action on a minimal free resolution
    	i:ZZ
	    a homological degree	    
    Outputs
    	:List
	    of group elements acting in homological degree @TT "i"@
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
    	    This function returns matrices describing elements of a
	    finite group acting on a minimal free resolution in a
	    given homological degree. If the homological degree is
	    the one where the user originally defined the action,
	    then the user provided elements are returned.
	    Otherwise, suitable elements are computed as indicated
	    in @arXiv("2106.14071","F. Galetto - Finite group characters on free resolutions")@.

	    To illustrate, we compute the action of a
	    symmetric group on the resolution of a monomial ideal.
	    The ideal is generated by
	    all squarefree monomials of degree two in four variables.
	    The symmetric group acts by permuting the four
	    variables of the ring. We only consider five
	    permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111 (since these are enough
		to determine the characters of the action).
    	Example	    
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    RI = res I
	    G = {matrix{{x_2,x_3,x_4,x_1}},
    		 matrix{{x_2,x_3,x_1,x_4}},
    		 matrix{{x_2,x_1,x_4,x_3}},
    		 matrix{{x_2,x_1,x_3,x_4}},
    		 matrix{{x_1,x_2,x_3,x_4}} }
	    A = action(RI,G)
	    actors(A,0)
	    actors(A,1)
	    actors(A,2)
	    actors(A,3)
    Caveat
    	When applied to a minimal free resolution $F_\bullet$,
    	this function returns matrices that induce the action of
	group elements on the representations $F_i/\mathfrak{m}F_i$, where
	$\mathfrak{m}$ is the maximal ideal generated by the variables of the
	polynomial ring.
	While these matrices often represent the action of the
	same group elements on the modules $F_i$ of the resolution,
	this is in general not a guarantee.
    SeeAlso
    	action	    


Node
    Key
	(actors,ActionOnGradedModule,List)
	(actors,ActionOnGradedModule,ZZ)
    Headline
    	group elements acting on components of a module
    Usage
    	actors(A,d)
    Inputs
    	A:ActionOnGradedModule
	    a finite group action on a graded module
	d:List
	    a (multi)degree
    Outputs
    	:List
	    of group elements acting in the given (multi)degree
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
    	    This function returns matrices describing elements of a
	    finite group acting on the graded component of
	    (multi)degree @TT "d"@ of a module.

	    To illustrate, we compute the action of a
	    symmetric group on the components of a monomial ideal.
	    The symmetric group acts by permuting the four
	    variables of the ring. We only consider five
	    permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111 (since these are enough
		to determine the characters of the action).
    	Example	    
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    G = {matrix{{x_2,x_3,x_4,x_1}},
          	 matrix{{x_2,x_3,x_1,x_4}},
          	 matrix{{x_2,x_1,x_4,x_3}},
          	 matrix{{x_2,x_1,x_3,x_4}},
          	 matrix{{x_1,x_2,x_3,x_4}} }
	    A = action(I,G)
	    actors(A,1)
	    actors(A,2)
	    actors(A,3)
    	Text
	    The degree argument can be an integer (in the case of
		single graded modules) or a list of integers (in
	    	the case of a multigraded module).
    SeeAlso
    	action	    


Node
    Key
    	character
    Headline
    	compute characters of finite group action
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this method to compute the Betti characters
	    of a finite group action on a minimal free resolution
	    or the characters of a finite group action on the
	    components of a graded module.
	    See the specific use cases for more details.
	    
	    All characters are bigraded by homological degree and
	    internal degree (inherited from the complex or module
		they are computed from). Modules are considered to
	    be concentrated in homological degree zero.
	    
	    Characters may also be constructed by hand using
	    @TO (character,PolynomialRing,ZZ,HashTable)@.
    Subnodes
    	Character
    	(character,ActionOnComplex)
    	(character,ActionOnComplex,ZZ)
     	(character,ActionOnGradedModule,List)
	(character,PolynomialRing,ZZ,HashTable)
	    
Node
    Key
    	(character,ActionOnComplex)
    Headline
    	compute all Betti characters of minimal free resolution
    Usage
    	character(A)
    Inputs
    	A:ActionOnComplex
	    a finite group action on a minimal free resolution
    Outputs
    	:HashTable
	    of the Betti characters of the resolution
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to compute all nonzero Betti
	    characters of a finite group action on a minimal free
	    resolution.
	    This function calls @TO (character,ActionOnComplex,ZZ)@
	    on all nonzero homological degrees and then assembles
	    the outputs in a hash table indexed by homological
	    degree.

	    To illustrate, we compute the Betti characters of a
	    symmetric group on the resolution of a monomial ideal.
	    The ideal is the symbolic square of the ideal generated by
	    all squarefree monomials of degree three in four variables.
	    The symmetric group acts by permuting the four
	    variables of the ring. The characters are determined
	    by five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
	Example
	    R = QQ[x_1..x_4]
	    J = intersect(apply(subsets(gens R,3),x->(ideal x)^2))
	    RJ = res J
	    G = { matrix{{x_2,x_3,x_4,x_1}},
    		  matrix{{x_2,x_3,x_1,x_4}},
    		  matrix{{x_2,x_1,x_4,x_3}},
    		  matrix{{x_2,x_1,x_3,x_4}},
    		  matrix{{x_1,x_2,x_3,x_4}} }
	    A = action(RJ,G)
	    character(A)
	Text
	    See @TO (character,ActionOnComplex,ZZ)@
	    for more details on this example.
    SeeAlso
    	action
	(character,ActionOnComplex,ZZ)


Node
    Key
    	(character,ActionOnComplex,ZZ)
    Headline
    	compute Betti characters of minimal free resolution
    Usage
    	character(A,i)
    Inputs
    	A:ActionOnComplex
	    a finite group action on a minimal free resolution
	i:ZZ
	    a homological degree
    Outputs
    	:Character
	    the @TT "i"@-th Betti character of the resolution
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to compute the Betti characters of a
	    finite group action on a minimal free resolution
	    in a given homological degree.
	    More explicitly, let $F_\bullet$ be a minimal free
	    resolution of a module $M$ over a polynomial ring $R$,
	    with a compatible action of a finite group $G$.
	    If $\mathfrak{m}$ denotes the maximal ideal generated by the
	    variables of $R$, then $F_i/\mathfrak{m}F_i$ is a graded
	    representation of $G$. We refer to its character as
	    the $i$-th {\bf Betti character} of $M$ (or a minimal free
	    resolution of $M$).
	    Betti characters are computed using Algorithm 1 in
	    @arXiv("2106.14071","F. Galetto - Finite group characters on free resolutions")@.

	    To illustrate, we compute the Betti characters of a
	    symmetric group on the resolution of a monomial ideal.
	    The ideal is the symbolic square of the ideal generated by
	    all squarefree monomials of degree three in four variables.
	    The symmetric group acts by permuting the four
	    variables of the ring. The characters are determined
	    by five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
	Example
	    R = QQ[x_1..x_4]
	    J = intersect(apply(subsets(gens R,3),x->(ideal x)^2))
	    RJ = res J
	    G = { matrix{{x_2,x_3,x_4,x_1}},
    		  matrix{{x_2,x_3,x_1,x_4}},
    		  matrix{{x_2,x_1,x_4,x_3}},
    		  matrix{{x_2,x_1,x_3,x_4}},
    		  matrix{{x_1,x_2,x_3,x_4}} }
	    A = action(RJ,G)
	    character(A,0)
	Text
	    By construction, the character in homological degree
	    0 is concentrated in degree 0 and trivial.
	Example
	    character(A,1)
	Text
	    The character in homological degree 1 has two
	    components. The component of degree 3 is the permutation
	    representation spanned by the squarefree monomials of
	    degree 3 (which can be identified with the natural
		representation of the symmetric group).
	    The component of degree 4 is the permutation representation
	    spanned by the squares of the squarefree monomials of degree
	    2.
	Example
	    character(A,2)
	Text
	    In homological degree 2, there is a component of degree
	    4 which is isomorphic to the irreducible standard
	    representation of the symmetric group.
	    In degree 5, we find the permutation representation of
	    the symmetric group on the set of ordered pairs of
	    distinct elements from 1 to 4.
	Example
	    character(A,3)
	Text
	    Finally, the character in homological degree 3 is
	    concentrated in degree 6 and corresponds to the direct
	    sum of the standard representation and the tensor
	    product of the standard representation and the sign
	    representation (i.e., the direct sum of the two
		irreducible representations of dimension 3).
    SeeAlso
    	action


Node
    Key
    	(character,ActionOnGradedModule,List)
    	(character,ActionOnGradedModule,ZZ)
    	(character,ActionOnGradedModule,ZZ,ZZ)
    Headline
    	compute characters of graded components of a module
    Usage
    	character(A,d)
    	character(A,lo,hi)
    Inputs
    	A:ActionOnGradedModule
	    a finite group action on a graded module
	d:List
	    a (multi)degree
    Outputs
    	:Character
	    the character of the components of a module in given degrees
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Use this function to compute the characters of the
	    finite group action on the graded components of a
	    module. The second argument is the (multi)degree of
	    the desired component. For $\mathbb{Z}$-graded rings,
	    one may compute characters in a range of degrees by
	    providing the lowest and highest degrees in the range.

	    To illustrate, we compute the Betti characters of a
	    symmetric group on the graded components of a polynomial
	    ring, a monomial ideal, and their quotient.
	    The characters are determined
	    by five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
	Example
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    G = {matrix{{x_2,x_3,x_4,x_1}},
          	 matrix{{x_2,x_3,x_1,x_4}},
          	 matrix{{x_2,x_1,x_4,x_3}},
          	 matrix{{x_2,x_1,x_3,x_4}},
          	 matrix{{x_1,x_2,x_3,x_4}} }
	    Q = R/I
	    A = action(R,G)
	    B = action(I,G)
	    C = action(Q,G)
	    character(A,0,5)
	    character(B,0,5)
	    character(C,0,5)
	    character(C,6)
    SeeAlso
    	action

	    
Node
    Key
    	(character,PolynomialRing,ZZ,HashTable)
    Headline
    	construct a character
    Usage
    	character(R,l,H)
    Inputs
    	R:PolynomialRing
	    over a field
    	l:ZZ
	    character length
    	H:HashTable
	    raw character data
    Outputs
    	:Character
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    The @TO character@ method is mainly designed to compute
	    characters of finite group actions defined via @TO action@.
	    The user who wishes to define characters by hand
	    may do so with this particular application of the method.
	    
	    The first argument is the polynomial ring the character
	    values will live in; this makes it possible to compare or
	    combine the hand-constructed character with other
	    characters over the same ring. The second argument is
	    the length of the character, i.e., the number of conjugacy
	    classes of the group whose representations the character
	    is coming from. The third argument is a hash table
	    containing the "raw" character data. The hash table
	    entries are in the format @TT "(i,d) => c"@, where @TT "i"@
	    is an integer representing homological degree, @TT "d"@
	    is a list representing the internal (multi)degree, and
	    @TT "c"@ is a list containing the values of the character
	    in the given degrees. Note that the values of the character
	    are elements in the ring given as the first argument.
	Example
	    R = QQ[x_1..x_3]
	    regRep = character(R,3, hashTable {
		    (0,{0}) => {1_R,1_R,1_R},
		    (0,{1}) => {-1_R,0_R,2_R},
		    (0,{2}) => {-1_R,0_R,2_R},
		    (0,{3}) => {1_R,-1_R,1_R},
		    })
	    I = ideal(x_1+x_2+x_3,x_1*x_2+x_1*x_3+x_2*x_3,x_1*x_2*x_3)
	    S3 = {matrix{{x_2,x_3,x_1}},
		  matrix{{x_2,x_1,x_3}},
		  matrix{{x_1,x_2,x_3}} }
	    Q = R/I
	    A = action(Q,S3)
	    character(A,0,3) === regRep
    Caveat
    	This constructor implements basic consistency checks but
	it is still be possible to construct objects that are not
	actually characters (not even virtual).
    SeeAlso
    	character

Node
    Key
    	(directSum,Character)
	(symbol ++,Character,Character)
    Headline
    	direct sum of characters
    Usage
    	character(c)
    	character(c1,c2,...)
    Inputs
    	c:Character
	    or sequence of characters
    Outputs
    	:Character
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns the direct sum of the input characters.
	    The operator @TT "++"@ may be used for the same purpose.
	Example
	    R = QQ[x_1..x_3]
	    I = ideal(x_1+x_2+x_3)
	    J = ideal(x_1-x_2,x_1-x_3)
	    S3 = {matrix{{x_2,x_3,x_1}},
		  matrix{{x_2,x_1,x_3}},
		  matrix{{x_1,x_2,x_3}} }
	    A = action(I,S3)
	    B = action(J,S3)
	    a = character(A,1)
	    b = character(B,1)
	    a ++ b
	    K = ideal(x_1,x_2,x_3)
	    C = action(K,S3)
	    c = character(C,1)
	    a ++ b === c

Node
    Key
    	inverseRingActors
    	(inverseRingActors,Action)
    Headline
    	get inverse of action on ring generators
    Usage
    	inverseRingActors(A)
    Inputs
    	A:Action
    Outputs
    	G:List
	    of group elements
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns a @TO List@ of group elements
	    acting on the vector space spanned by the variables
	    of the polynomial ring associated with the object
	    acted upon.
	    These are the inverses of the elements originally
	    defined by the user when constructing the action.
	    By default, these elements are
	    expressed as one-row substitution matrices as those
	    accepted by @TO substitute@. The optional input
	    @TO Sub@ may be used to return these elements as square
	    matrices.
    SeeAlso
    	action


Node
    Key
    	numActors
    	(numActors,Action)
    Headline
    	number of acting elements
    Usage
    	numActors(A)
    Inputs
    	A:Action
    Outputs
    	:ZZ
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns the number of group elements passed by the user
	    when defining the given action.
	    This number is not necessarily the order of the acting
	    group because in order to compute characters it is
	    enough to work with a representative of each conjugacy
	    class of the group.
    SeeAlso
    	action


Node
    Key
    	(net,Action)
    Headline
    	format for printing, as a net
    Description
    	Text
	    Format objects of type @TO Action@ for printing.
	    See @TO net@ for more information.

Node
    Key
    	(net,Character)
    Headline
    	format for printing, as a net
    Description
    	Text
	    Format objects of type @TO Character@ for printing.
	    See @TO net@ for more information.


Node
    Key
    	(ring,Action)
    Headline
    	get ring of object acted upon
    Usage
    	ring(A)
    Inputs
    	A:Action
    Outputs
    	:PolynomialRing
	    associated with the object acted upon
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns the polynomial ring associated with the object
	    being acted upon.
    SeeAlso
    	action


Node
    Key
    	ringActors
    	(ringActors,Action)
    Headline
    	get action on ring generators
    Usage
    	ringActors(A)
    Inputs
    	A:Action
    Outputs
    	G:List
	    of group elements
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns a @TO List@ of group elements
	    acting on the vector space spanned by the variables
	    of the polynomial ring associated with the object
	    acted upon.
	    These are the same elements originally defined by
	    the user when constructing the action.
	    By default, these elements are
	    expressed as one-row substitution matrices as those
	    accepted by @TO substitute@. The optional input
	    @TO Sub@ may be used to return these elements as square
	    matrices.
    SeeAlso
    	action


Node
    Key
    	(target,Action)
    Headline
    	get object acted upon
    Usage
    	target(A)
    Inputs
    	A:Action
    Description
    	Text
	    This function is provided by the package
	    @TO BettiCharacters@.
	    
	    Returns the object being acted upon.
	    Depending on the action, this object may be a
	    @TO ChainComplex@, a @TO PolynomialRing@, a
	    @TO QuotientRing@, an @TO Ideal@, or a @TO Module@.
    SeeAlso
    	action


Node
    Key
    	Sub
	[action, Sub]
	[ringActors, Sub]
	[inverseRingActors, Sub]
    Headline
    	act on ring via substitutions (rather than matrices)
    Description
    	Text
	    This optional input is provided by the package
	    @TO BettiCharacters@.
	    
	    By default, the group elements acting on a ring are
	    passed as one-row substitution matrices as those
	    accepted by @TO substitute@. Setting @TT "Sub=>false"@
	    allows the user to pass these elements as square
	    matrices.
	    
	    The example below sets up the action of a symmetric
	    group on the resolution of a monomial ideal.
	    The symmetric group acts by permuting the four
	    variables of the ring. The conjugacy classes of
	    permutations are determined by their cycle types,
	    which are in bijection with partitions. In this case,
	    we consider five permutations with cycle types,
	    in order: 4, 31, 22, 211, 1111.
	    For simplicity, we construct these matrices
	    by permuting columns of the identity.
    	Example
	    R = QQ[x_1..x_4]
	    I = ideal apply(subsets(gens R,2),product)
	    RI = res I
	    G = { (id_(R^4))_{1,2,3,0},
    		  (id_(R^4))_{1,2,0,3},
    		  (id_(R^4))_{1,0,3,2},
    		  (id_(R^4))_{1,0,2,3},
    		   id_(R^4) }
	    A = action(RI,G,Sub=>false)
    	Text
	    Similarly, setting @TT "Sub=>false"@
	    causes @TO ringActors@ and @TO inverseRingActors@
	    to return the group elements acting on the ring as
	    square matrices. With the default setting
	    @TT "Sub=>true"@, the same elements are returned as
	    one-row substitution matrices.
    	Example
	    ringActors(A,Sub=>false)
	    inverseRingActors(A,Sub=>false)
	    ringActors(A)
	    inverseRingActors(A)
///
	    
----------------------------------------------------------------------
-- Tests
----------------------------------------------------------------------

-- Test 0 (monomial ideal, symmetric group)
TEST ///
clearAll
R = QQ[x,y,z]
I = ideal(x*y,x*z,y*z)
RI = res I
S3 = {matrix{{y,z,x}},matrix{{y,x,z}},matrix{{x,y,z}}}
A = action(RI,S3)
a = character(R,3,hashTable {
    ((0,{0}), {1_R,1_R,1_R}),
    ((1,{2}), {0_R,1_R,3_R}),
    ((2,{3}), {-1_R,0_R,2_R})
    })
assert((character A) === a)
B = action(R,S3)
b = character(R,3,hashTable {
    ((0,{0}), {1_R,1_R,1_R}),
    ((0,{1}), {0_R,1_R,3_R}),
    ((0,{2}), {0_R,2_R,6_R}),
    ((0,{3}), {1_R,2_R,10_R})
    })
assert(character(B,0,3) === b)
C = action(I,S3)
c = character(R,3,hashTable {
    ((0,{2}), {0_R,1_R,3_R}),
    ((0,{3}), {1_R,1_R,7_R})
    })
assert(character(C,0,3) === c)
D = action(R/I,S3)
d = character(R,3,hashTable {
    ((0,{0}), {1_R,1_R,1_R}),
    ((0,{1}), {0_R,1_R,3_R}),
    ((0,{2}), {0_R,1_R,3_R}),
    ((0,{3}), {0_R,1_R,3_R})
    })
assert(character(D,0,3) === d)
assert(b === c++d)
///

-- Test 1 (non-monomial ideal, symmetric group)
TEST ///
clearAll
R = QQ[x_1..x_5]
I = ideal(
    	(x_1-x_4)*(x_2-x_5),
    	(x_1-x_3)*(x_2-x_5),
    	(x_1-x_3)*(x_2-x_4),
    	(x_1-x_2)*(x_3-x_5),
    	(x_1-x_2)*(x_3-x_4)	
    )
RI = res I
S5 = for p in partitions(5) list (
    L := gens R;
    g := for u in p list (
	l := take(L,u);
	L = drop(L,u);
	rotate(1,l)
	);
    matrix { flatten g }
    )
A = action(RI,S5)
a = character(R,7,hashTable {
    ((0,{0}), {1_R,1_R,1_R,1_R,1_R,1_R,1_R}),
    ((1,{2}), {0_R,-1_R,1_R,-1_R,1_R,1_R,5_R}),
    ((2,{3}), {0_R,1_R,-1_R,-1_R,1_R,-1_R,5_R}),
    ((3,{5}), {1_R,-1_R,-1_R,1_R,1_R,-1_R,1_R})
    })
assert((character A) === a)
B = action(R,S5)
b = character(R,7,hashTable {
    ((0,{0}), {1_R,1_R,1_R,1_R,1_R,1_R,1_R}),
    ((0,{1}), {0_R,1_R,0_R,2_R,1_R,3_R,5_R}),
    ((0,{2}), {0_R,1_R,1_R,3_R,3_R,7_R,15_R}),
    ((0,{3}), {0_R,1_R,1_R,5_R,3_R,13_R,35_R})
    })
assert(character(B,0,3) === b)
C = action(I,S5)
c = character(R,7,hashTable {
    ((0,{2}), {0_R,-1_R,1_R,-1_R,1_R,1_R,5_R}),
    ((0,{3}), {0_R,-2_R,1_R,-1_R,0_R,4_R,20_R})
    })
assert(character(C,0,3) === c)
D = action(R/I,S5)
d = character(R,7,hashTable {
    ((0,{0}), {1_R,1_R,1_R,1_R,1_R,1_R,1_R}),
    ((0,{1}), {0_R,1_R,0_R,2_R,1_R,3_R,5_R}),
    ((0,{2}), {0_R,2_R,0_R,4_R,2_R,6_R,10_R}),
    ((0,{3}), {0_R,3_R,0_R,6_R,3_R,9_R,15_R})
    })
assert(character(D,0,3) === d)
assert(b === c++d)
///

-- Test 3 (non symmetric group, tests actors)
TEST ///
clearAll
kk = toField(QQ[w]/ideal(sum apply(5,i->w^i)))
R = kk[x,y]
D5 = {
    matrix{{x,y}},
    matrix{{w*x,w^4*y}},
    matrix{{w^2*x,w^3*y}},
    matrix{{y,x}}
    }
A = action(R,D5)
a = {
    map(R^{4:-3},R^{4:-3},{{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}),
    map(R^{4:-3},R^{4:-3},{{w^3,0,0,0},{0,w,0,0},{0,0,w^4,0},{0,0,0,w^2}}),
    map(R^{4:-3},R^{4:-3},{{w,0,0,0},{0,w^2,0,0},{0,0,w^3,0},{0,0,0,w^4}}),
    map(R^{4:-3},R^{4:-3},{{0,0,0,1},{0,0,1,0},{0,1,0,0},{1,0,0,0}})
    }
assert(actors(A,3) === a)
ca = character(R,4, hashTable {((0,{3}), apply(a,trace))})
assert(character(A,3) === ca)
d1=map(R^1,R^{4:-3},{{x^3,x^2*y,x*y^2,y^3}})
d2=map(R^{4:-3},R^{3:-4},{{-y,0,0},{x,-y,0},{0,x,-y},{0,0,x}})
Rm=chainComplex(d1,d2)
B = action(Rm,D5)
assert(actors(B,1) === a)
cb1 = character(R,4, hashTable {((1,{3}), apply(a,trace))})
assert(character(B,1) === cb1)
b = {
    map(R^{3:-4},R^{3:-4},{{1,0,0},{0,1,0},{0,0,1}}),
    map(R^{3:-4},R^{3:-4},{{w^2,0,0},{0,1,0},{0,0,w^3}}),
    map(R^{3:-4},R^{3:-4},{{w^4,0,0},{0,1,0},{0,0,w}}),
    map(R^{3:-4},R^{3:-4},{{0,0,-1},{0,-1,0},{-1,0,0}})
    }
assert(actors(B,2) === b)
cb2 = character(R,4, hashTable {((2,{4}), apply(b,trace))})
assert(character(B,2) === cb2)
///

end

--below is code for Example 3
    Example
	g=matrix{{a^4,0,0},{0,a^2,0},{0,0,a}}
	h=matrix{{0,1,0},{0,0,1},{1,0,0}}
	i=(2*a^4+2*a^2+2*a+1)/7 * matrix{
    	    {a-a^6,a^2-a^5,a^4-a^3},
    	    {a^2-a^5,a^4-a^3,a-a^6},
    	    {a^4-a^3,a-a^6,a^2-a^5}
    	    }
	j=-1/(2*a^4+2*a^2+2*a+1) * matrix{
    	    {a^5-a^4,1-a^5,1-a^3},
    	    {1-a^5,a^6-a^2,1-a^6},
    	    {1-a^3,1-a^6,a^3-a}
    	    }
	G={id_(R^3),i,h,j,g,inverse g};
	A1=action(RI,G,Sub=>false)
	A2=action(RI2,G,Sub=>false)
	elapsedTime character A1
	elapsedTime character A2
    Example
	needsPackage "SymbolicPowers"
	Is2 = symbolicPower(I,2);
	M = Is2 / I2;
	B = action(M,G,Sub=>false)
	character(B,21)

--multiplicities for example 1
	multiplicities = c -> select(
    	    applyValues(irrReps,
		v -> innerProduct(7,v,mutableMatrix{new List from c})),
    	    v -> v!=0
    	    )
	multiplicities c#0#{0}
	multiplicities c#1#{2}
	multiplicities c#2#{3}
	multiplicities c#3#{4}
	multiplicities c#4#{5}
	multiplicities c#5#{7}

--multliplicities for example 2
	multiplicities = c -> select(
	    applyValues(irrReps,
		v -> innerProduct(6,v,mutableMatrix{new List from c})),
	    v -> v!=0
	    )
	applyValues(c#0, v -> multiplicities v)
	applyValues(c#1, v -> multiplicities v)
	applyValues(c#2, v -> multiplicities v)
	applyValues(c#3, v -> multiplicities v)
	applyValues(c#4, v -> multiplicities v)
