$( q0.mm  20-May-2017 $)
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                      Metamath source file for Q0
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  This is an implementation in Metamath of Church's Type Theory - Formulation
  based on Equality, by Peter B. Andrews (1963 and 2002). 

  This implementation is based on the following sources:
  * Andrews, Peter B. (2002). An Introduction to Mathematical Logic and Type 
    Theory: To Truth Through Proof, Second Edition, Springer.
    Chapter 5: Type Theory. References are given in parenthesis, like in (5201)
  * https://plato.stanford.edu/entries/type-theory-church/#ForBasEqu
  * https://en.wikipedia.org/wiki/Q0_(mathematical_logic)
  
  Thierry Arnoux    [15-May-2017] First version
  $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                              Syntax
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                              Types
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $c type $. $( Declare a constant symbol used to declare types $)
  $c ( $.  $( subscript left parenthesis $)
  $c ) $.  $( subscript right parenthesis $)

  $( Introduce variable names to represent types $)
  $v alpha $. $( subscript greek letter alpha $)
  $v beta $.  $( subscript greek letter beta $)
  $v gamma $.  $( subscript greek letter gamma $)
  $v delta $.  $( subscript greek letter delta $)
  ta $f type alpha $. $( Let variable ` alpha ` denote a type $)
  tb $f type beta $. $( Let variable ` beta ` denote a type $)
  tg $f type gamma $. $( Let variable ` gamma ` denote a type $)
  td $f type delta $. $( Let variable ` delta ` denote a type $)

  $( Formula, see https://plato.stanford.edu/entries/type-theory-church/#For $)

  $( Type symbols are defined inductively as follows: $)

	$( ` i ` is a type symbol (denoting the type of individuals). 
	    There may also be additional primitive type symbols which are used in 
	    formalizing disciplines where it is natural to have several sorts of 
	    individuals. 
	    [Editors Note: In what follows, the entry distinguishes between the 
	    symbols  ` _i ` , ` I. ` , and  ` i^` . The first is the symbol used for 
	    the type  of individuals; the second is the symbol used for a logical 
	    constant  (see below); the third is the symbol used as a variable-binding 
	    operator  that represents the definite description "the". The reader 
	    should check to  see that the browser is displaying these symbols 
	    correctly.] $)
  $( ` _i ` is a type symbol, denoting the type of individuals. $)
  $c _i $. $( subscript greek letter iota $)
  ti $a type _i $. $( Let constant ` _i ` be a type $)

	$( ` _o ` is a type symbol, denoting the type of truth values. $)
  $c _o $. $( subscript greek letter omicron $)
  to $a type _o $. $( Let constant ` _o ` be a type $)

	$( If ` alpha ` and ` beta ` are types, so is ` ( alpha beta ) ` ,
	    the type of functions from elements of type ` beta ` to elements of type
	    ` alpha ` . $)
  tab $a type ( alpha beta ) $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                               Formulas
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $( Declare primitive constant symbols $)
  $c wff $. $( Symbol used to introduce wff $)
  $c : $. $( Semicolon, used in type statements $)
  $c [ $.  $( Left bracket $)
  $c ] $.  $( Right bracket $)

  $( Introduce variable names to represent formulas $)
  $v A $.
  $v B $.
  $v W $.
  fa $f wff A $.
  fb $f wff B $.
  fw $f wff W $.

  $c statement $. $( Statement symbol $)
  $c . $. $( Used to terminate a wff statement $)
  $c |- $. $( Turnstile - used to introduce provable statements - 
              read:  "the following symbol sequence is provable" or 'a proof 
              exists for") $)

	$( A formula is a finite sequence of primitive symbols. 
	   Certain formulas are called well-formed formulas (wffs).
     In this metamath library:
     - the symbol ` formula ` is used to declare Q0's wff.
     - the symbol ` statement ` is used for both type statements (declaring that 
       a variable is of a given type) and formula statements (the wff itself)
       which follows.  
     - the symbol ` |- ` is used for provable statements, both provable type 
       statements and provable wff. 
       
	   We write ` |- A : alpha ` as an abbreviation for wff ` A ` is of type 
	   ` alpha `, and define this concept inductively as follows: $)

	$( The following structure is to be read ` A ` is of type ` alpha ` 
	   It is used in hypothesis steps when we want to restrict statements
	   to formulas of certain types. In Church's notation, the subscript is added
	   whenever the formula is used. However in this implementation, we'll first
	   state the types requirements, then use the formula symbols without 
	   subscripts. $)
  wta $a statement A : alpha $.
	
	$( Statement of the type theory are wff of type ` _o ` . However we don't
	   (can't?) add an hypothesis step that requires ` W : _o ` . Instead,
	   all our axioms will effectively be of type ` _o ` $)
  ww $a statement W . $.

  $( $j syntax 'wff'; 
        syntax 'statement'; 
        syntax '|-' as 'statement'; 
        primitive 'wa' 'wap' 'wab'; 
        primitive 'fw' 'fap' 'fab'; 
        primitive 'fop' 'fal' 'fex' ; 
  $)
  $( $j syntax 'type'; 
        primitive 'tab'; 
  $)

	$( The constuct ` [ A B ] ` is called "application" and represents the value
	   of a function ` A ` applied to ` B ` . $)
  fap $a wff [ A B ] $.

  ${
    wap.1 $e |- A : ( alpha beta ) $.
    wap.2 $e |- B : beta $.
    $( If ` A ` is a variable of type ` ( alpha beta ) ` and ` B ` is a wff of 
       type ` beta `then ` [ A B ] ` is a wff of type ` alpha ` . $)
    wap $a |- [ A B ] : alpha $.
  $}


  $c variable $. $( Variable symbol $)
  $c L^ $.  $( Lambda symbol $)

  $( Introduce variable names to represent variables $)
  $v x $.
  $v y $.
  $v g $.
  vx $f variable x $.
  vy $f variable y $.
  vg $f variable g $.
  
  $( A variable alone is a wff $)
  fx $a wff x $.
  
  $( A variable can be assigned any type (note that this can possibly be 
     dangerous as we cannot prevent it to be invoked several times in the same
     proof, with different types. $)
  xa $a |- x : alpha $.
  
  $( The construct ` [ L^ x A ] ` is called "abstraction" and represents the 
     function mapping ` x ` to ` A ` , whereas ` x ` can be free in ` A ` . $)
  fab $a wff [ L^ x A ] $.

  ${
    wab.1 $e |- A : alpha $.
    wab.2 $e |- x : beta $.
		$( If ` x ` is a variable of type ` beta ` and ` A ` is a wff of type 
		   ` alpha `then ` [ L^ x A ] ` is a wff of type ` ( alpha beta ) ` . 
		   I.e. ` [ L^ x A ] ` is constructing a function from elements of type 
		   ` beta ` , the type of ` x ` , to elements of type ` alpha ` , the
		   type of ` A ` . $)
    wab $a |- [ L^ x A ] : ( alpha beta ) $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       Logical Primitive Constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( In this formulation Q0 of Church's type theory there are primitive 
     constants Q detnoting equality, and ` ~ ` (negation), ` \/ ` 
     (disjunction), and ` P ` (used in defining the universal quantifier),
     are defined in terms of ` Q ` . $)

  $c Q. $. $( Logical primitive constant Q for the equality operator $)
  $c I. $. $( Logical primitive constant i for the individual operator $)
  fq $a wff Q. $.
  fi $a wff I. $.

  $( Define the type of ` Q ` $)
  wq $a |- Q. : ( ( _o alpha ) alpha ) $.

  $( Define the type of ` I ` $)
  wi $a |- I. : ( _i ( _o _i ) ) $.

  ${
    wqeq.1 $e |- A : alpha $.
    wqeq.2 $e |- B : alpha $.
    $( The wff ` [ [ Q. A ] B ] ` is a truth value. We will later define it
       as ` [ A = B ] ` - see ~ df-eq . $)
    wqeq $p |- [ [ Q. A ] B ] : _o $=
      ( to fq fap tab wq wap ) FAGBHCFAIAGBAJDKEK $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                           Q0's inference rule 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce additional symbols to represent formulas $)
  $v C $.
  $v D $.
  fc $f wff C $.
  fd $f wff D $.

  $( Q0 has a single inference rule called 'R' .
  
     Inference in Q0 replaces a subexpression at any depth within a WFF with an 
     equal expression. Metamath's only built-in inference rule substitutes all 
     occurrences of variables in a theorem, provided the hypothesis have been 
     proven with the same substitutions.
     
     In metamath, we will therefore require several axioms to express the
     substitution rule, in an inductive way, for all basic formula building 
     blocks (function application and lambda abstraction). 
     
     Similarly, we may require severa applications of the axioms in metamath 
     where a single inference rule appears in the Q0 textbook proofs.
     
     The hypothesis ~ r-f.1 , ` [ [ Q. A ] B ] ` could have been written 
     ` [ A = B ] ` , but this abbreviation has not been introduced yet. 
     See ~ df-eq. and ~ df-op $)
	${
	  r-f.1 $e |- [ [ Q. A ] B ] . $.
    ${
      r-t.2 $e |- B : alpha $.
      $( Inference in a type declaration $)
      r-t $a |- A : alpha $.
    $}
    ${
	    r-f.2 $e |- A . $.
      $( The Q0 inference rule, related to modus ponens and equality : if 
         ` [ A = B ] ` we can infer ` B ` from ` A ` . $)
	    r-f $a |- B . $.
	  $}

    $( We can apply the inference rule of Q0 only on the first (function) term 
       of a function application. $)
    r-ap1 $a |- [ [ Q. [ A C ] ] [ B C ] ] . $.

    $( We can apply the inference rule of Q0 only on the second term of a 
       function application. $)
    r-ap2 $a |- [ [ Q. [ C A ] ] [ C B ] ] . $.

    $( We can apply the inference rule of Q0 on the term of an abstraction $) 
    r-ab $a |- [ [ Q. [ L^ x A ] ] [ L^ x B ] ] . $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                              Abbreviations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( I order to be able to define axioms using abbreviations, we have to define
     them first, though one can convince himself it would have been possible to 
     state the axioms solely based on the Q. and I. operators and the primitive
     constructs application and abstraction. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                    Operation Syntax / Infix Notation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $( Several abbreviations follow a scheme ` [ A R B ] ` where ` R ` is the new
     operator taking two variables, and ` [ A R B ] ` the result of this 
     operation. This definition will allow to define them all in one shot,
     and avoid multiplying the substitution rules. At the same time, it can 
     be reused for common constructs like ` [ A + B ] ` . $)

  $( Introduce an additional symbol to represent an operation formula $)
    $v R $.
    fr $f wff R $.
  
  $( Extract from [2]:
  
     As noted by Schonfinkel (1924), functions of more than one argument can be 
     represented in terms of functions of one argument when the values of these 
     functions can themselves be functions. For example, if f is a function of 
     two arguments, for each element x of the left domain of f there is a 
     function g (depending on x) such that gy = fxy for each element y of the 
     right domain of f. We may now write g = fx, and regard f as a function of 
     a single argument, whose value for any argument x in its domain is a 
     function fx, whose value for any argument y in its domain is fxy.

     For a more explicit example, consider the function + which carries any 
     pair of natural numbers to their sum. We may denote this function by 
     ` + : ( ( sigma sigma ) sigma ) ` ,  where ` sigma ` is the type of 
     natural numbers. Given any number x, ` [ + x ] ` is the function which, 
     when applied to any number y, gives the value ` [ [ + x ] y ] ` , which is 
     ordinarily abbreviated as ` [ x + y ] ` . Thus ` [ +  x ] ` is the 
     function of one argument which adds x to any number. 
     When we think of ` + ` as a function of one argument, we see that it maps 
     any number ` x ` to the function ` [ + x ] ` . $)
  
  fop $a wff [ A R B ] $.
  $( Define the syntax for operations on two variables. This first 
     definition cannot make use of the ` [ A = B ] ` construct itself, since 
     we chose to consider that that construct actually follows the same model 
     itself. $)
  df-op $a |- [ [ Q. [ A R B ] ] [ [ R A ] B ] ] . $.

  ${
    wop.1 $e |- A : alpha $.
    wop.2 $e |- B : beta $.
    wop.3 $e |- R : ( ( gamma beta ) alpha ) $.
    $( Type of the operation construct. $)
    wop $p |- [ A R B ] : gamma $=
      ( fop fap df-op tab wap r-t ) CDEFJFDKZEKDEFLCBPECBMAFDIGNHNO $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                Equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c = $. $( Constant for equality $)
  feq $a wff = $.

  $( Define equality as the logical ` Q. ` primitive operator. With this 
     definition, formulas like ` [ = [ A ] B ] ` or ` [ A Q. B ] ` would make
     sense, however we will always use ` [ [ Q A ] B ] ` and ` [ A = B ] `
     instead : All those formulas are equivalent. $)
  df-eq $a |- [ [ Q. = ] Q. ] . $.

  ${
    eqq.1 $e |- [ A = B ] . $.
    $( Substitution of an equality into its form using the ` Q. ` operator 
       by its abbreviation. This theorem, if applied on the axioms and on the 
       abbreviations definitions, will lead to their exploded form. $)
    eqq $p |- [ [ Q. A ] B ] . $=
      ( feq fap fq df-eq r-ap1 fop df-op r-f ) DAEZBEZFAEZBELNBDFAGHHABDIMABDJC
      KK $.
      $( [13-May-2017] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       Abbreviation Definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Define additional constants which will be derived from ` Q ` and ` I ` $)
  $c == $. $( Logical constant equivalence ( U+2261 ' Identical to ' ) $)
  $c T. $. $( Truth $)
  $c F. $. $( Falsehood $)
  $c ~ $. $( Logical negation $)
  $c \/ $. $( Logical disjunction $)
  $c /\ $. $( Logical conjunction $)
  $c -> $. $( Logical inference ( U+2283 ' Superset of ' ) $)
  fbi $a wff == $.
  ft $a wff T. $.
  ff $a wff F. $.
  fn $a wff ~ $.
  fan  $a wff /\ $.
  fo   $a wff \/ $.
  fin  $a wff -> $.

  ${
    df-bi.1 $e |- B : _o $.
    $( Define logical equivalence as equality of truth values. 
       Term ` B ` must be a truth value, and term ` A ` can be inferred to be.
       $)
    df-bi $a |- [ [ A == B ] = [ A = B ] ] . $.
  $}  

  $( Define truth. $)
  df-t $a |- [ T. = [ Q. = Q. ] ] . $.

  $( Define falsehood. $)
  df-f $a |- [ F. = [ [ L^ x T. ] = [ L^ x x ] ] ] . $.

  $( Define negation. $)
  df-neg $a |- [ ~ = [ Q. F. ] ] . $.

  $( Define conjunction. $)
  df-an $a |- [ /\ = [ L^ x [ L^ y 
    [ [ L^ g [ [ g T. ] T. ] ] = [ L^ g [ [ g x ] y ] ] ] ] ] ] . $.

  $( Define inference. $)
  df-in $a |- [ -> = [ L^ x [ L^ y [ x = [ x /\ y ] ] ] ] ] . $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       Universal Quantifiers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c A. $. $( Universal quantifier $)
  $c E. $. $( Existential quantifier $)

  $( Formula building rules for the abbreviations $)
  fal  $a wff [ A. x A ] $.
  fex  $a wff [ E. x A ] $.

  ${
    df-al.1 $e |- A : _o $.
    $( Define universal quantifier $)
    df-al $a |- [ [ A. x A ] = [ [ L^ x T. ] = [ L^ x A ] ] ] . $. 
  $}
  ${
    df-ex.1 $e |- A : _o $.
    $( Define existential quantifier $)
    df-ex $a |- [ [ E. x A ] = [ ~ [ A. x [ ~ A ] ] ] ] . $. 
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Abbreviations Types
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    weq.1 $e |- A : alpha $.
    weq.2 $e |- B : alpha $.
    $( ` [ A = B ] ` is a truth value. $)
    weq $p |- [ A = B ] : _o $=
      ( to feq fop fap df-op fq df-eq r-ap1 wqeq r-t ) FBCGHGBIZCIZBCGJFQKBIZCI
      PRCGKBLMMABCDENOO $.
  $}
  
  ${
    wbi.1 $e |- B : _o $.
    wbi.2 $e |- A : _o $.
    $( ` [ A == B ] ` is a truth value. $)
    wbi $p |- [ A == B ] : _o $=
      ( to fbi fop feq df-bi eqq weq r-t ) EABFGZABHGZMNABCIJEABDCKL $.
  $}

  $( ` T. ` is a truth value. $)
  wt $p |- T. : _o $=
    ( to ft fq feq fop df-t eqq tab wq weq r-t ) ABCCDEZBLFGAAHAHCCAIZMJK $.

  $( ` F. ` is a truth value. $)
  wf $p |- F. : _o $=
    ( vx to ff ft fab fx feq fop df-f eqq tab wt xa wab weq r-t ) BCDAEZAFZAEZG
    HZCTAIJBBKQSBBDALBAMZNBBRAUAUANOP $.

  $( The negation's type is a function from truth value to truth value $)
  wn $p |- ~ : ( _o _o ) $=
    ( to tab fn fq ff fap df-neg eqq wq wf wap r-t ) AABZCDEFZCNGHMADEAIJKL $.

  $( Type of the conjunction operator $)
  wan $p |- /\ : ( ( _o _o ) _o ) $=
    ( vg vx vy to tab fan fx ft fap fab feq fop df-an eqq xa wt wap wab weq r-t
    ) DDEZDEZFAGZHIZHIZAJZUCBGZIZCGZIZAJZKLZCJZBJZFUNBCAMNUADUMBDDULCDUBEUFUKDU
    BUEADDUDHUADUCHUBAOZPQPQUORDUBUJADDUHUIUADUCUGUODBOZQDCOZQUORSUQRUPRT $.

  $( Type of tthe logical inference operator $)
  win $p |- -> : ( ( _o _o ) _o ) $=
    ( vx vy to tab fin fx fan fop feq fab df-in eqq xa wan wop weq wab r-t ) CC
    DZCDEAFZTBFZGHZIHZBJZAJZEUEABKLSCUDACCUCBCTUBCAMZCCCTUAGUFCBMZNOPUGQUFQR $.

  ${
    wneg.1 $e |- A : _o $.
    $( The negation of a truth value is a truth value. $)
    wneg $p |- [ ~ A ] : _o $=
      ( to fn wn wap ) CCDAEBF $.
  $}

  ${
    wim.1 $e |- A : _o $.
    wim.2 $e |- B : _o $.
    $( An inference is a truth value. $)
    wim $p |- [ A -> B ] : _o $=
      ( to fin win wop ) EEEABFCDGH $.
  $}

  ${
    wal.1 $e |- A : _o $.
    $( An universal quantifier is a truth value. $)
    wal $p |- [ A. x A ] : _o $=
      ( ta to fal ft fab feq fop df-al eqq tab wt xa wab weq r-t ) EABFZGBHZABH
      ZIJZSUBABCKLEDMTUAEDGBNDBOZPEDABCUCPQR $.
    $( An existential quantifier is a truth value. $)
    wex $p |- [ E. x A ] : _o $=
      ( to fex fn fap fal df-ex eqq wneg wal r-t ) DABEZFFAGZBHZGZNQABCIJPOBACK
      LKM $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                                Axioms
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Introduce variable names to represent function formulas $)
  $v F $.
  $v G $.
  fff $f wff F $.
  ffg $f wff G $.

	${
	  ax-1.1 $e |- G : ( _o _o ) $.
    ax-1.2 $e |- x : _o $.
    $( Axiom 1 expresses the idea that ` T. ` and ` F. ` are the only boolean 
       values. $)
	  ax-1 $a |- [ [ [ G T. ] /\ [ G F. ] ] = [ A. x [ G x ] ] ] . $.
	$}

  ${
    ax-2.1 $e |- A : alpha $.
    ax-2.2 $e |- B : alpha $.
    ax-2.3 $e |- C : ( _o alpha ) $.
    $( Axiom 2 expresses the idea that applying the same function on two equal
       values yields to the same value. $)
    ax-2 $a |- [ [ A = B ] -> [ [ C A ] = [ C B ] ] ] . $.
  $}

  ${
    ax-3.1 $e |- F : ( alpha beta ) $.
    ax-3.2 $e |- G : ( alpha beta ) $.
    ax-3.3 $e |- x : beta $.
    $( Axiom 3 $)
    ax-3 $a |- [ [ F = G ] = [ A. x [ [ F x ] = [ G x ] ] ] ] . $.
  $}

  ${
    $d x B $.
    ax-4c.1 $e |- A : alpha $.
    ax-4c.2 $e |- x : alpha $.
    $( Axiom 4 for formula where x is free in ` B ` note that we make use of
       Metamath's $) 
    ax-4c $a |- [ [ [ L^ x B ] A ] = B ] . $.
  $}

  ${
    ax-4i.1 $e |- A : alpha $.
    ax-4i.2 $e |- x : alpha $.
    ax-4i $a |- [ [ [ L^ x x ] A ] = A ] . $.
  $}

  ${
    ax-4ap.1 $e |- A : alpha $.
    ax-4ap.2 $e |- B : ( beta gamma ) $.
    ax-4ap.3 $e |- C : gamma $.
    ax-4ap.4 $e |- x : alpha $.
    ax-4ap $a |- 
      [ [ [ L^ x [ B C ] ] A ] = [ [ [ L^ x B ] A ] [ [ L^ x C ] A ] ] ] . $.
  $}

  ${
    $d x y $. $d y A $.
    ax-4ab.1 $e |- A : alpha $.
    ax-4ab.2 $e |- x : alpha $.
    $( Axiom 4 for Lambda Abstractions. Note the the distinct variable 
       requirements $)
    ax-4ab $a |- [ [ [ L^ x [ L^ y B ] ] A ] =  [ L^ y [ [ L^ x B ] A ] ] ] . $.
  $}

  ${
    ax-4ab2.1 $e |- A : alpha $.
    ax-4ab2.2 $e |- B : beta $.
    ax-4ab2.3 $e |- x : alpha $.
    ax-4ab2 $a |- [ [ [ L^ x [ L^ x B ] ] A ] = [ [ L^ x B ] A ] ] . $.
  $}

  ax-5 $a |- [ [ I. [ Q. A ] ] = A ] . $.

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                       Elementary Logic in Q0
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Elimination of Q.
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( We prove theorem ~ qeq which is useful to eliminate ` Q. ` forms of 
     equality and replace them by the abbreviation ` [ A = B ] ` . $)

  ${
    qid.1 $e |- A : alpha $.
    $( Identical formula are equal - ` Q. ` form , similar to ~ eqid X5200 $)
    qid $p |- [ [ Q. A ] A ] . $=
      ( vx fq fx fab fap xa ax-4i eqq r-ap2 r-ap1 r-f ) EDFDGBHZHZBHEBHZBHPQBOB
      EOBABDCADIJKZLMRN $.
  $}

  ${
    qr.1 $e |- A : alpha $.
    ${
      qr.2 $e |- [ [ Q. A ] B ] . $.
      $( Swap terms in the ` Q. ` form of an equality $)
      qr $p |- [ [ Q. B ] A ] . $=
        ( fq fap r-ap2 r-ap1 qid r-f ) FBGZBGFCGZBGLMBBCFEHIABDJK $.

      $( Infer equality from its ` Q. ` form $)
      qeq $p |- [ A = B ] . $=
        ( feq fap fop to qr r-t weq df-op fq tab df-eq wq r-ap1 r-f ) FBGZCGZBC
        FHZIUBUAABCDACBABCDEJDKLBCFMJNBGZCGUAUCTCNFBIAOAOZFNUDFNPAQKPJRRESS $.
    $}
  $}
  
  $( We can now redefine operation, using an equality form rather than a ` Q. ` 
     form. $)
  ${
    dfop.1 $e |- A : alpha $.
    dfop.2 $e |- B : beta $.
    dfop.3 $e |- R : ( ( gamma beta ) alpha ) $.
    $( Define an operation using equality. $)
    dfop $p |- [ [ A R B ] = [ [ R A ] B ] ] . $=
      ( fop fap wop df-op qeq ) CDEFJFDKEKABCDEFGHILDEFMN $.
  $}

  ${
    eqid.a $e |- A : alpha $.
    $( Identical formula are equal. (5200) $)
    eqid $p |- [ A = A ] . $=
      ( qid qeq ) ABBCABCDE $.
  $}

  ${
    eqr.1 $e |- A : alpha $.
    eqr.2 $e |- [ A = B ] . $.
    $( Infer equality with swapped terms (5201.2) $)
    eqr $p |- [ B = A ] . $=
      ( eqq qr r-t qeq ) ACBACBABCDBCEFGZDHJI $.
  $}

  ${
    eqtr.1 $e |- A : alpha $.
    eqtr.2 $e |- [ A = B ] . $.
    eqtr.3 $e |- [ B = C ] . $.
    $( Transitivity of the identity. (5201.3) $)
    eqtr $p |- [ A = C ] . $=
      ( fq fap eqq r-ap2 r-f qeq ) ABDEHBIZCINDICDNCDGJKBCFJLM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Substitution Rules for Equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( We prove here the inference rule R, based on equality ~ apeq1.1 rather 
     than its Q. form ~ r-f.1 . These new substitution can now be used in place 
     of ~ r-ap1 and co., and the Q. primitive does not need to appear in the 
     formulas. $)

  ${
    teq.1 $e |- B : alpha $.
    teq.2 $e |- [ A = B ] . $.
    $( Infer type from equality, similar to ~ r-t $)
    teq $p |- A : alpha $=
      ( eqq r-t ) ABCBCEFDG $.
  $}

  ${
    teqr.1 $e |- A : alpha $.
    teqr.2 $e |- [ A = B ] . $.
    $( Infer type from equality, revere form. $)
    teqr $p |- B : alpha $=
      ( eqr teq ) ACBDABCDEFG $.
  $}

  ${
    mpeq.1 $e |- A . $.
    mpeq.2 $e |- [ A = B ] . $.
    $( Modus Ponens based on equality. $)
    mpeq $p |- B . $=
      ( eqq r-f ) ABABDECF $.
  $}

  ${
    apeq12.1 $e |- A : ( alpha beta ) $.
    apeq12.2 $e |- C : beta $.
    apeq12.3 $e |- [ A = B ] . $.
    apeq12.4 $e |- [ C = D ] . $.
    $( Equality building rule for function application. (5201.4) $)
    apeq12 $p |- [ [ A C ] = [ B D ] ] . $=
      ( fap wap fq eqq r-ap1 r-ap2 r-f qeq ) ACEKZDFKZABCEGHLMSKZCFKZKUATKUBT
      UACDFCDINOPEFCEFJNPQR $.
  $}

  ${
    apeq1.1 $e |- A : ( alpha beta ) $.
    apeq1.2 $e |- C : beta $.
    apeq1.3 $e |- [ A = B ] . $.
    $( Equality building rule for function application. (5201.5) $)
    apeq1 $p |- [ [ A C ] = [ B C ] ] . $=
      ( eqid apeq12 ) ABCDEEFGHBEGIJ $.
  $}

  ${
    apeq2.1 $e |- A : alpha $.
    apeq2.2 $e |- C : ( beta alpha ) $.
    apeq2.3 $e |- [ A = B ] . $.
    $( Equality building rule for function application. (5201.6) $)
    apeq2 $p |- [ [ C A ] = [ C B ] ] . $=
      ( tab eqid apeq12 ) BAEECDGFBAIEGJHK $.
  $}

  ${
    abeq.1 $e |- A : alpha $.
    abeq.2 $e |- [ A = B ] . $.
    $( Equality building rule for function abstraction. $)
    abeq $p |- [ [ L^ x A ] = [ L^ x B ] ] . $=
      ( tb tab fab xa wab eqq r-ab qeq ) AGHBDICDIAGBDEGDJKBCDBCFLMN $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                More Substitution Rules for Equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( We can now also prove equality builders for the operation and quantifier 
     forms $)

  ${
    opeq12.1 $e |- A : alpha $.
    opeq12.2 $e |- C : beta $.
    opeq12.3 $e |- R : ( ( gamma beta ) alpha ) $.
    obeq12.4 $e |- [ A = B ] . $.
    opeq12.5 $e |- [ C = D ] . $.
    $( Equality building rule for operation $)
    opeq12 $p |- [ [ A R C ] = [ B R D ] ] . $=
      ( fop fap wop dfop wap eqq qr tab apeq2 apeq12 r-t eqr eqtr ) CDFHNHDOZFO
      ZEGHNZABCDFHIJKPABCDFHIJKQCUHHEOZGOZUICBUGFCBUAZAHDKIRZJRCBUGUJFGUMJAULDE
      HIKLUBMUCCUIUKABCEGHAEDADEIDELSTIUDZBGFBFGJFGMSTJUDZKPABCEGHUNUOKQUEUFUF
      $.
  $}

  ${
    opeq1.1 $e |- A : alpha $.
    opeq1.2 $e |- C : beta $.
    opeq1.3 $e |- R : ( ( gamma beta ) alpha ) $.
    obeq1.4 $e |- [ A = B ] . $.
    $( Equality building rule for operation. 
       (This proof could be shortened using ~ opeq12 ) $)
    opeq1 $p |- [ [ A R C ] = [ B R C ] ] . $=
      ( eqid opeq12 ) ABCDEFFGHIJKBFILM $.
  $}

  ${
    opeq2.1 $e |- A : alpha $.
    opeq2.2 $e |- C : beta $.
    opeq2.3 $e |- R : ( ( gamma alpha ) beta ) $.
    obeq2.4 $e |- [ A = B ] . $.
    $( Equality building rule for operation $)
    opeq2 $p |- [ [ C R A ] = [ C R B ] ] . $=
      ( eqid opeq12 ) BACFFDEGIHJBFILKM $.
  $}

  ${
    eqeq12.1 $e |- A : alpha $.
    eqeq12.2 $e |- C : alpha $.
    eqeq12.3 $e |- [ A = B ] . $.
    eqeq12.4 $e |- [ C = D ] . $.
    $( Prove an equality of two equalities. $)
    eqeq12 $p |- [ [ A = C ] = [ B = D ] ] . $=
      ( to feq tab fq df-eq wq r-t opeq12 ) AAJBCDEKFGJALALKMNAOPHIQ $.
  $}

  ${
    eqeq1.1 $e |- A : alpha $.
    eqeq1.2 $e |- C : alpha $.
    eqeq1.3 $e |- [ A = B ] . $.
    $( Infer an equality from an equality of the first terms. $)
    eqeq1 $p |- [ [ A = C ] = [ B = C ] ] . $=
      ( eqid eqeq12 ) ABCDDEFGADFHI $.
  $}

  ${
    eqeq2.1 $e |- A : alpha $.
    eqeq2.2 $e |- C : alpha $.
    eqeq2.3 $e |- [ A = B ] . $.
    $( Infer an equality from an equality of the second terms. $)
    eqeq2 $p |- [ [ C = A ] = [ C = B ] ] . $=
      ( eqid eqeq12 ) ADDBCFEADFHGI $.
  $}

  ${    
    aleq.1 $e |- A : _o $.
    aleq.2 $e |- [ A = B ] . $.
    $( Equality building rule for universal quantifier $)
    aleq $p |- [ [ A. x A ] = [ A. x B ] ] . $=
      ( ta to fal ft fab feq fop wal df-al eqq r-t tab wab eqr eqtr qr xa wt fq
      df-eq wq abeq opeq2 ) GACHICJZACJZKLZBCHZACDMACDNGULUKBCGBAGABDABEOUADPZM
      ZGULUIBCJZKLUKUNBCUMNGFQZUPGUOUJUIKGFBCUMFCUBZRGFICUCUQRGUPQUPQKUDUEUPUFP
      GBACUMGABDESUGUHTST $.

    $( Equality building rule for universal quantifier $)
    exeq $p |- [ [ E. x A ] = [ E. x B ] ] . $=
      ( to fex fn fap fal wex df-ex wneg wal wn apeq2 aleq eqtr eqr teq ) FACGZ
      HHBIZCJZIZBCGZACDKZFUAHHAIZCJZIUDUFACDLFFUHUCHUGCADMZNOUGUBCUIFFABHDOEPQP
      RFUEUDBCFBADFABDESTZKBCUJLSR $.
  $}

  ${
		dfeq.1 $e |- A : alpha $.
		dfeq.2 $e |- B : alpha $.
	  $( A definition of equality. $)
	  dfeq $p |- [ [ A = B ] == [ [ Q. A ] B ] ] . $=
	    ( feq fop fq fap fbi to weq tab df-eq wq r-t dfop wap qeq apeq1 eqtr wqeq 
	    wop wbi df-bi eqr mpeq ) BCFGZHBIZCIZFGZUHUJJGZKUHFBIZCIUJABCDELAAKBCFDEK
	    AMZAMZFHNAOPZQKAUMUICUNAFBUPDREUNAFHBUPDUOFHUPNSTTUAKULUKUHUJABCDEUBZAAKB
	    CFDEUPUCUDUHUJUQUEUFUG $.
  $}

  ${
    obab.1 $e |- A : alpha $.
    obab.2 $e |- B : beta $.
    obab.3 $e |- C : gamma $.
    obab.4 $e |- R : ( ( delta gamma ) beta ) $.
    obab.5 $e |- x : alpha $.
    $( A theorem similar to the ax-4 series, for operation $)
    obab $p |- [ [ [ L^ x [ B R C ] ] A ] = 
      [ [ [ L^ x B ] A ] [ [ L^ x R ] A ] [ [ L^ x C ] A ] ] ] . $=
      ? $.
  $}

  ${
    eqab.1 $e |- A : alpha $.
    eqab.2 $e |- B : beta $.
    eqab.3 $e |- C : beta $.
    eqab.4 $e |- x : alpha $.
    $( A theorem similar to the ax-4 series, for equality $)
    eqab $p |- [ [ [ L^ x [ B = C ] ] A ] = 
      [ [ [ L^ x B ] A ] = [ [ L^ x C ] A ] ] ] . $=
      ? $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             Equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    bieq.1 $e |- B : _o $.
    bieq.2 $e |- [ A == B ] . $.
    $( Infer equality from equivalence $)
    bieq $p |- [ A = B ] . $=
      ( fbi fop feq df-bi mpeq ) ABEFABGFDABCHI $.
  $}

  ${
    mpbi.1 $e |- B : _o $.
    mpbi.2 $e |- A . $.
    mpbi.3 $e |- [ A == B ] . $.
    $( An inference from a biconditional, related to modus ponens. (5201.1) $)
    mpbi $p |- B . $=
      ( bieq mpeq ) ABDABCEFG $.
  $}

  ${    
    albi.1 $e |- A : _o $.
    albi.2 $e |- [ A == B ] . $.
    $( Equivalence building rule for universal quantifier, derived from 
       ~ aleq $)
    albi $p |- [ [ A. x A ] == [ A. x B ] ] . $=
      ? $.

    $( Equivalence building rule for universal quantifier, derived from
       ~ exeq $)
    exbi $p |- [ [ E. x A ] == [ E. x B ] ] . $=
      ? $.
  $}

  $( Theorems (5202) ~ (5204) are not proven here, substitution rules will
     be used instead. $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Elementary Logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
   $d F x $.
   dffun.1 $e |- F : ( alpha beta ) $. 
   $( A definition of a function (5205). Note that ` x ` shall not be free in
      ` F ` . $)
   dffun $p |- [ F = [ L^ x [ F x ] ] ] . $=
     ( vy feq fop fx fap fab tab to fal weq xa ax-3 wap wab eqtr eqid ax-4c eqr
     ax-4ap ax-4i apeq12 eqeq2 aleq mpeq ) DDGHZDDCIZJZCKZGHZABLZDEUAMUJDFIZJZU
     QGHZFNZUNUODDEEOABFDDEEBFPZQMUNUSUODUMEABULCABDUKEBCPZRVASZOZMUNUQUMUPJZGH
     ZFNUSVCABFDUMEVBUTQVEURFAUQVDABDUPEUTRZABUMUPVBUTRZOAVDUQUQVGVFAVDDCKZUPJZ
     UKCKZUPJZJUQVGBABUPDCUKUTEVAVAUDABVIDVKUPUOBVHUPUOBDCEVASUTRBBVJUPBBUKCVAV
     ASUTRBUPDCUTVAUBBUPCUTVAUEUFTUGUHTUCTUI $.
  $}

  ${
   dft.1 $e |- A : alpha $.
	 $( A definition of truth. (5210) $)
	 dft $p |- [ T. = [ A = A ] ] . $=
	   ( vx vy to ft fab fap feq fop wt xa wab wap fx tab mpeq weq eqtr ax-4c eqr
     fal eqid ax-3 df-al ax-4i eqeq12 abeq eqeq2 apeq1 eqab ) FGGDHZBIZBBJKZLFU
     NGFAUMBFAGDLADMZNZCOZABGDCUPUAUBFUNDPZUSJKZDHZBIZUOURFAUMVABUQCUMEPZEHZUSI
     ZVEJKZDHZJKZUMVAJKVFDUCZVHVDVDJKVIAAQVDAAVCEAEMZVJNZUDAADVDVDVKVKUPUERVFDA
     VEVEAAVDUSVKUPOZVLSZUFRFAQVGVAUMFAVFDVMUPNUQFVFUTDVMAVEUSVEUSVLVLAUSEUPVJU
     GZVNUHUIUJRUKFVBUSDHZBIZVPJKUOFAVABFAUTDAUSUSUPUPSUPNCOAABUSDUSCUPUPUPULAV
     PBVPBAAVOBAAUSDUPUPNCOZVQABDCUPUGZVRUHTTT $.
  $}

  $( Truth and Truth. (5211) $)
  tant $p |- [ [ T. /\ T. ] = T. ] . $=
    ? $.

  $( Truth holds. (5212) $)
  truth $p |- T. . $=
    ? $.

  imval $p |- [ [ A -> B ] == [ A == [ A /\ B ] ] ] . $=
    ? $.

  imval2 $p |- [ [ A -> B ] = [ [ ~ A ] \/ B ] ] . $=
    ? $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    exmpbi.1 $e |- A : _o $.
    exmpbi.2 $e |- [ A == B ] . $.
    exmpbi.3 $e |- [ E. x A ] . $.
    $( Inference rule for existential unifier $)
    exmpbi $p |- [ E. x B ] . $=
      ? $. 
  $}

	eqcom $p |- [ [ A = B ] -> [ B = A ] ] . $=
	  ? $.

  ${
    wiki.1 $e |- [ E. x A ] . $.
    wiki.2 $e |- [ A -> B ] . $.
    $( Example in wikipedia $)
    wiki $p |- [ E. x [ A /\ B ] ] . $=
      ? $.    
	$}
