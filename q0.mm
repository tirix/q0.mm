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
                        Variable Type Declarations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( In Church's notation, a subscript is added whenever a formula is used
     to specify its type. However in this implementation, we'll first
     state the types requirements, then use the formula symbols without 
     subscripts. For compound formula, this will be done as hypothesis, but
     for variables, this will be done in the context of the formula, as
     part of a variable type declaration, prepended to the statement. $)

  $( Declare primitive constant symbols $)
  $c | $. $( Empty variable declaration $)
  $c : $. $( Semicolon, used in type statements $)
  $c wff $. $( Symbol used to introduce wff's $)
  $c variable $. $( Symbol used to introduce variables $)
  $c vardecl $. $( Symbol used to introduce variable type declarations $)

  $( Introduce variable names to represent wff $)
  $v A B W $.
  fa $f wff A $.
  fb $f wff B $.
  fw $f wff W $.

  $( Introduce variable names to represent Q0 variables $)
  $v x y z g $.
  vx $f variable x $.
  vy $f variable y $.
  vz $f variable z $.
  vg $f variable g $.

  $( Define variable type declarations : variable type declarations consist in
     a list of "variable : type" assignments. $)
  $v V/  W/ $.
  fvv $f vardecl V/ $.
  fvw $f vardecl W/ $.

  $( Empty variable type declaration $)
  de $a vardecl | $.

  $( Recursive variable type declaration, prepending a "variable : type"
     assignment to an already existing variable type declaration. $)
  dx $a vardecl x : alpha V/ $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                               Formulas
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $( Declare primitive constant symbols $)
  $c [ $.  $( Left bracket $)
  $c ] $.  $( Right bracket $)


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
	   to formulas of certain types. $)
  sta $a statement V/ A : alpha $.
	
	$( Statement of the type theory are wff of type ` _o ` . However we don't
	   add an hypothesis step that requires ` W : _o ` , as this would 
	   unnecessarily complexify the statements.
	   Instead, all our axioms will effectively be of type ` _o ` $)
  sw $a statement V/ W . $.

  $( Both statement definitions also include a list variable type declarations
     ` V/ ` which is used to specific the types of the variables used in these 
     statements. Any hypothesis for wff types are specified in separated 
     hypothesis statements. However, this cannot be done for variables as 
     variable's scopes are the statements in which they are used, and they 
     cannot be extracted, which is the reason why variable type declarations
     have been introduced. $)

  ${
    $d x A $.
    dat.1 $e |- V/ A : alpha $.
    $( If ` x ` does not appear in a type statement, then a variable type 
       declaration for ` x ` can be added. $)
    dat $a |- x : beta V/ A : alpha $.
  $}

  ${
    $d x W $.
    daf.1 $e |- V/ W . $.
    $( If ` x ` does not appear in a wff statement, then a variable type 
       declaration for ` x ` can be added. $)
    daf $a |- x : alpha V/ W . $.
  $}

  ${
    $d x A $.
    ddt.1 $e |- x : alpha V/ A : beta $.
    $( Drop an unused variable type hypothesis from a type statement. $)
    ddt $a |- V/ A : beta $.
  $}

  ${
    $d x W $.
    ddf.1 $e |- x : alpha V/ W . $.
    $( Drop an unused variable type hypothesis from a wff statement. $)
    ddf $a |- V/ W . $.
  $}
  
  ${
    ds2t.1 $e |- x : alpha y : beta V/ A : gamma $.
    $( Swap the two first type declarations in a type statement $)
    ds2t $a |- y : beta x : alpha V/ A : gamma $.
  $}
  
  ${
    ds2f.1 $e |- x : alpha y : beta V/ W . $.
    $( Swap the two first type declarations in a wff statement $)
    ds2f $a |- y : beta x : alpha V/ W . $.
  $}

  ${
    ds3t.1 $e |- x : alpha y : beta z : gamma V/ A : delta $.
    $( Swap the two next type declarations in a type statement $)
    ds3t $a |- x : alpha z : gamma y : beta V/ A : delta $.
  $}
  
  ${
    ds3f.1 $e |- x : alpha y : beta z : gamma V/ W . $.
    $( Swap the two next type declarations in a wff statement $)
    ds3f $a |- x : alpha z : gamma y : beta V/ W . $.
  $}

  ${
    drt.1 $e |- x : alpha V/ A : beta $.
    $( Repeat a variable type declaration in a type statement $)
    drt $a |- x : alpha x : alpha V/ A : beta $.
  $}

  ${
    drf.1 $e |- x : alpha V/ W . $.
    $( Repeat a variable type declaration in a wff statement $)
    drf $a |- x : alpha x : alpha V/ W . $.
  $}

  $( The following comment contains hints to some automatic syntax verifiers. 
     It does not seem to be used by MMJ2. $)  
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

  $( A variable alone is a wff $)
  fx $a wff x $.
  
  ${
    $d x V/ $.
    $( Infer a variable type from the same variable type hypothesis. $)
    wxid $a |- x : alpha V/ x : alpha $.
  $}

	$( The constuct ` [ A B ] ` is called "application" and represents the value
	   of a function ` A ` applied to ` B ` . $)
  fap $a wff [ A B ] $.

  ${
    wap.1 $e |- V/ A : ( alpha beta ) $.
    wap.2 $e |- V/ B : beta $.
    $( If ` A ` is a variable of type ` ( alpha beta ) ` and ` B ` is a wff of 
       type ` beta `then ` [ A B ] ` is a wff of type ` alpha ` . $)
    wap $a |- V/ [ A B ] : alpha $.
  $}

  $c L^ $.  $( Lambda symbol $)
  
  $( The construct ` [ L^ x A ] ` is called "abstraction" and represents the 
     function mapping ` x ` to ` A ` , whereas ` x ` can be free in ` A ` . $)
  fab $a wff [ L^ x A ] $.

  ${
    wab.1 $e |- x : beta V/ A : alpha $.
		$( If ` x ` is a variable of type ` beta ` and ` A ` is a wff of type 
		   ` alpha `then ` [ L^ x A ] ` is a wff of type ` ( alpha beta ) ` . 
		   I.e. ` [ L^ x A ] ` is constructing a function from elements of type 
		   ` beta ` , the type of ` x ` , to elements of type ` alpha ` , the
		   type of ` A ` . $)
    wab $a |- V/ [ L^ x A ] : ( alpha beta ) $.
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
  wq $a |- V/ Q. : ( ( _o alpha ) alpha ) $.

  $( Define the type of ` I ` $)
  wi $a |- V/ I. : ( _i ( _o _i ) ) $.

  ${
    wqeq.1 $e |- V/ A : alpha $.
    wqeq.2 $e |- V/ B : alpha $.
    $( The wff ` [ [ Q. A ] B ] ` is a truth value. We will later define it
       as ` [ A = B ] ` - see ~ df-eq . $)
    wqeq $p |- V/ [ [ Q. A ] B ] : _o $=
      ( to fq fap tab wq wap ) GAHBICDGAJAHBDADKELFL $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                        Q0's inference rule ` R `
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
	  r-f.1 $e |- V/ [ [ Q. A ] B ] . $.
    ${
      r-t.2 $e |- V/ B : alpha $.
      $( Inference in a type declaration $)
      r-t $a |- V/ A : alpha $.
    $}
    ${
	    r-f.2 $e |- V/ A . $.
      $( The Q0 inference rule, related to modus ponens and equality : if 
         ` [ A = B ] ` we can infer ` B ` from ` A ` . $)
	    r-f $a |- V/ B . $.
	  $}

    $( We can apply the inference rule of Q0 only on the first (function) term 
       of a function application. $)
    r-ap1 $a |- V/ [ [ Q. [ A C ] ] [ B C ] ] . $.

    $( We can apply the inference rule of Q0 only on the second term of a 
       function application. $)
    r-ap2 $a |- V/ [ [ Q. [ C A ] ] [ C B ] ] . $.
  $}
  ${
    r-ab.1 $e |- x : alpha V/ [ [ Q. A ] B ] . $.
    $( We can apply the inference rule of Q0 on the term of an abstraction $) 
    r-ab $a |- V/ [ [ Q. [ L^ x A ] ] [ L^ x B ] ] . $.
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
    $v R S $.
    fr $f wff R $.
    fs $f wff S $.
  
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
  df-op $a |- V/ [ [ Q. [ A R B ] ] [ [ R A ] B ] ] . $.

  ${
    wop.1 $e |- V/ A : alpha $.
    wop.2 $e |- V/ B : beta $.
    wop.3 $e |- V/ R : ( ( gamma beta ) alpha ) $.
    $( Type of the operation construct. $)
    wop $p |- V/ [ A R B ] : gamma $=
      ( fop fap df-op tab wap r-t ) CDEGKGDLZELFDEFGMCBQEFCBNAGDFJHOIOP $.
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
  df-eq $a |- V/ [ [ Q. = ] Q. ] . $.

  ${
    eqq.1 $e |- V/ [ A = B ] . $.
    $( Substitution of an equality into its form using the ` Q. ` operator 
       by its abbreviation. This theorem, if applied on the axioms and on the 
       abbreviations definitions, will lead to their exploded form. $)
    eqq $p |- V/ [ [ Q. A ] B ] . $=
      ( feq fap fq df-eq r-ap1 fop df-op r-f ) EAFZBFZGAFZBFCMOCBEGCACHIIABEJNC
      ABCEKDLL $.
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
  for  $a wff \/ $.
  fin  $a wff -> $.

  ${
    df-bi.1 $e |- V/ B : _o $.
    $( Define logical equivalence as equality of truth values. 
       Term ` B ` must be a truth value, and term ` A ` can be inferred to be.
       $)
    df-bi $a |- V/ [ [ A == B ] = [ A = B ] ] . $.
  $}  

  $( Define truth. $)
  df-t $a |- V/ [ T. = [ Q. = Q. ] ] . $.

  $( Define falsehood. $)
  df-f $a |- V/ [ F. = [ [ L^ x T. ] = [ L^ x x ] ] ] . $.

  $( Define negation. $)
  df-neg $a |- V/ [ ~ = [ Q. F. ] ] . $.

  $( Define conjunction. $)
  df-an $a |- V/ [ /\ = [ L^ x [ L^ y 
    [ [ L^ g [ [ g T. ] T. ] ] = [ L^ g [ [ g x ] y ] ] ] ] ] ] . $.

  $( Define disunction. $)
  df-or $a |- V/ [ \/ = [ L^ x [ L^ y 
    [ ~ [ [ ~ x ] /\ [ ~ y ] ] ] ] ] ] . $.

  $( Define inference. $)
  df-in $a |- V/ [ -> = [ L^ x [ L^ y [ x = [ x /\ y ] ] ] ] ] . $.

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
    df-al.1 $e |- x : alpha V/ A : _o $.
    $( Define universal quantifier $)
    df-al $a |- V/ [ [ A. x A ] = [ [ L^ x T. ] = [ L^ x A ] ] ] . $. 

    $( Define existential quantifier $)
    df-ex $a |- V/ [ [ E. x A ] = [ ~ [ A. x [ ~ A ] ] ] ] . $. 
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Abbreviations Types
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    weq.1 $e |- V/ A : alpha $.
    weq.2 $e |- V/ B : alpha $.
    $( ` [ A = B ] ` is a truth value. $)
    weq $p |- V/ [ A = B ] : _o $=
      ( to feq tab fq df-eq wq r-t wop ) AAGBCDHEFGAIAIHJDDKADLMN $.
  $}
  
  ${
    wbi.1 $e |- V/ B : _o $.
    wbi.2 $e |- V/ A : _o $.
    $( ` [ A == B ] ` is a truth value. $)
    wbi $p |- V/ [ A == B ] : _o $=
      ( to fbi fop feq df-bi eqq weq r-t ) FABGHZABIHZCNOCABCDJKFABCEDLM $.
  $}

  $( ` T. ` is a truth value. $)
  wt $p |- V/ T. : _o $=
    ( to ft fq feq fop df-t eqq tab wq weq r-t ) BCDDEFZACMAAGHBBIBIDDABAJZNKL
    $.

  ${
    $d x V/ $.
	  $( ` F. ` is a truth value. $)
	  wf $p |- V/ F. : _o $=
	    ( vx to ff ft fab fx feq fop df-f eqq tab wt dat wab wxid weq r-t ) CDEBF
	    ZBGZBFZHIZADUBABAJKCCLSUAACCEBACCEBAAMNOCCTBACBAPOQR $.
  $}

  $( The negation's type is a function from truth value to truth value $)
  wn $p |- V/ ~ : ( _o _o ) $=
    ( to tab fn fq ff fap df-neg eqq wq wf wap r-t ) BBCZDEFGZADOAAHINBEFABAJAK
    LM $.

  ${
    $d x y g V/ $.
	  $( Type of the conjunction operator $)
	  wan $p |- V/ /\ : ( ( _o _o ) _o ) $=
	    ( vg vx vy to tab fan fx ft fap fab feq fop df-an eqq dx wxid wap wab dat
     wt ds3t ds2t weq r-t ) EEFZEFZGBHZIJZIJZBKZUHCHZJZDHZJZBKZLMZDKZCKZAGUSACD
     BANOUFEURCAEEUQDECAPZEUGFZUKUPEDUTPZVAEUKDUTVAEUKCAEUGUJBAEEUIIUGBAPZUFEUH
     IVCUGBAQZVCUAZRVERSTTEUGUOBVBEUGEUODBUTEEUGEUODCBAEEUMUNEDECVCPZPUFEUMDVFU
     FEUHULVFUGEUHCVCVDTECVCQRTEDVFQRUBUCSUDSSUE $.
  $}

  ${
    $d x y V/ $.
	  $( Type of tthe logical inference operator $)
	  win $p |- V/ -> : ( ( _o _o ) _o ) $=
	    ( vx vy to tab fin fx fan fop feq fab df-in eqq dx wxid dat wan wop weq 
	    wab r-t ) DDEZDEFBGZUCCGZHIZJIZCKZBKZAFUHABCALMUBDUGBADDUFCDBANZDUCUEDCUI
	    NZDDUCCUIDBAOPZDDDUCUDUJHUKDCUIOUJQRSTTUA $.
  $}

  ${
    wneg.1 $e |- V/ A : _o $.
    $( The negation of a truth value is a truth value. $)
    wneg $p |- V/ [ ~ A ] : _o $=
      ( to fn wn wap ) DDEABBFCG $.
  $}

  ${
    wim.1 $e |- V/ A : _o $.
    wim.2 $e |- V/ B : _o $.
    $( An inference is a truth value. $)
    wim $p |- V/ [ A -> B ] : _o $=
      ( to fin win wop ) FFFABCGDECHI $.
  $}

  ${
    wal.1 $e |- x : alpha V/ A : _o $.
    $( An universal quantifier is a truth value. $)
    wal $p |- V/ [ A. x A ] : _o $=
      ( to fal ft fab feq fop df-al eqq tab dx wt wab weq r-t ) FBCGZHCIZBCIZJK
      ZDTUCDABCDELMFANUAUBDFAHCDACDOPQFABCDEQRS $.
    $( An existential quantifier is a truth value. $)
    wex $p |- V/ [ E. x A ] : _o $=
      ( to fex fn fap fal df-ex eqq dx wneg wal r-t ) FBCGZHHBIZCJZIZDQTDABCDEK
      LSDARCDBACDMENONP $.
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
	  ax-1.1 $e |- x : _o V/ G : ( _o _o ) $.
    $( Axiom 1 expresses the idea that ` T. ` and ` F. ` are the only boolean 
       values. (1.) $)
	  ax-1 $a |- V/ [ [ [ G T. ] /\ [ G F. ] ] = [ A. x [ G x ] ] ] . $.
	$}

  ${
    ax-2.1 $e |- V/ A : alpha $.
    ax-2.2 $e |- V/ B : alpha $.
    ax-2.3 $e |- V/ C : ( _o alpha ) $.
    $( Axiom 2 expresses the idea that applying the same function on two equal
       values yields to the same value. (2.) $)
    ax-2 $a |- V/ [ [ A = B ] -> [ [ C A ] = [ C B ] ] ] . $.
  $}

  ${
    ax-3.1 $e |- x : beta V/ F : ( alpha beta ) $.
    ax-3.2 $e |- x : beta V/ G : ( alpha beta ) $.
    $( Axiom 3 (3.) $)
    ax-3 $a |- V/ [ [ F = G ] = [ A. x [ [ F x ] = [ G x ] ] ] ] . $.
  $}

  $( Axiom 4 is here broken down into 5 axioms like in Andrews [2002]. $)
  ${
    $d x B $.
    $( Axiom 4.1 for formula where x is not free in ` B ` note that we make use 
       of Metamath's distinct variable statement. We dropped the hypothesis
       that ` B ` is of a type ` beta ` if ` x ` is of type ` alpha ` , since
       this can anyway always be obtained by ~ dat . (4_1.) $) 
    ax-4c $a |- V/ [ [ [ L^ x B ] A ] = B ] . $.
  $}

  $( Axiom 4.2 $)
  ax-4i $a |- V/ [ [ [ L^ x x ] A ] = A ] . $.

  ${
    ax-4ap.1 $e |- V/ A : alpha $.
    ax-4ap.2 $e |- x : alpha V/ B : ( beta gamma ) $.
    ax-4ap.3 $e |- x : alpha V/ C : gamma $.
    $( Axiom 4.3 $)
    ax-4ap $a |- V/ 
      [ [ [ L^ x [ B C ] ] A ] = [ [ [ L^ x B ] A ] [ [ L^ x C ] A ] ] ] . $.
  $}

  ${
    $d x y $. $d y A $.
    ax-4ab.1 $e |- V/ A : alpha $.
    ax-4ab.2 $e |- x : alpha y : gamma V/ B : delta $.
    $( Axiom 4.4 for Lambda Abstractions. Note the the distinct variable 
       requirements $)
    ax-4ab $a |- V/ [ [ [ L^ x [ L^ y B ] ] A ] =  [ L^ y [ [ L^ x B ] A ] ] ] 
      . $.
  $}

  ${
    ax-4ab2.1 $e |- V/ A : alpha $.
    ax-4ab2.2 $e |- x : alpha V/ B : delta $.
    $( Axiom 4.5 for Lambda Abstractions. $)
    ax-4ab2 $a |- V/ [ [ [ L^ x [ L^ x B ] ] A ] = [ L^ x B ] ] . $.
  $}

  $( Axiom 5. Axiom of Descriptions $)
  ax-5 $a |- V/ [ [ I. [ Q. A ] ] = A ] . $.

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

  $( Identical formula are equal - ` Q. ` form , similar to ~ eqid X5200 $)
  qid $p |- V/ [ [ Q. A ] A ] . $=
    ( vx fq fx fab fap ax-4i eqq r-ap2 r-ap1 r-f ) DCECFAGZGZAGDAGZAGBNOBAMABDM
    ABACBHIZJKPL $.

  ${
    qr.1 $e |- V/ [ [ Q. A ] B ] . $.
    $( Swap terms in the ` Q. ` form of an equality $)
    qr $p |- V/ [ [ Q. B ] A ] . $=
      ( fq fap r-ap2 r-ap1 qid r-f ) EAFZAFEBFZAFCKLCAABCEDGHACIJ $.

    $( Infer equality from its ` Q. ` form $)
    qeq $p |- V/ [ A = B ] . $=
      ( feq fap fop df-op qr fq df-eq r-ap1 r-f ) EAFZBFZABEGZCPOCABCEHIJAFZBFZ
      OCORCNQCBEJCACKLLIDMM $.
  $}
  
  $( We can now redefine operation, using an equality form rather than a ` Q. ` 
     form. $)
  $( Define an operation using equality. $)
  dfop $p |- V/ [ [ A R B ] = [ [ R A ] B ] ] . $=
    ( fop fap df-op qeq ) ABDEDAFBFCABCDGH $.

  $( Identical formula are equal. (5200) $)
  eqid $p |- V/ [ A = A ] . $=
    ( qid qeq ) AABABCD $.

  ${
    eqr.1 $e |- V/ [ A = B ] . $.
    $( Infer equality with swapped terms (5201.2) $)
    eqr $p |- V/ [ B = A ] . $=
      ( eqq qr qeq ) BACABCABCDEFG $.
  $}

  ${
    eqtr.1 $e |- V/ [ A = B ] . $.
    eqtr.2 $e |- V/ [ B = C ] . $.
    $( Transitivity of the identity. (5201.3) $)
    eqtr $p |- V/ [ A = C ] . $=
      ( fq fap eqq r-ap2 r-f qeq ) ADCGAHZBHMDHCBDCMBDCFIJABCEIKL $.
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
    teq.1 $e |- V/ B : alpha $.
    teq.2 $e |- V/ [ A = B ] . $.
    $( Infer type from equality, similar to ~ r-t $)
    teq $p |- V/ A : alpha $=
      ( eqq r-t ) ABCDBCDFGEH $.
  $}

  ${
    teqr.1 $e |- V/ A : alpha $.
    teqr.2 $e |- V/ [ A = B ] . $.
    $( Infer type from equality, revere form. $)
    teqr $p |- V/ B : alpha $=
      ( eqr teq ) ACBDEBCDFGH $.
  $}

  ${
    mpeq.1 $e |- V/ A . $.
    mpeq.2 $e |- V/ [ A = B ] . $.
    $( Modus Ponens based on equality. $)
    mpeq $p |- V/ B . $=
      ( eqq r-f ) ABCABCEFDG $.
  $}

  ${
    apeq12.1 $e |- V/ [ A = B ] . $.
    apeq12.2 $e |- V/ [ C = D ] . $.
    $( Equality building rule for function application. (5201.4) $)
    apeq12 $p |- V/ [ [ A C ] = [ B D ] ] . $=
      ( fap fq eqq r-ap1 r-ap2 r-f qeq ) ADHZBEHZCIOHZAEHZHQPHCRPCQABCEABCFJKLD
      ECADECGJLMN $.
  $}

  ${
    apeq1.1 $e |- V/ [ A = B ] . $.
    $( Equality building rule for function application. (5201.5) $)
    apeq1 $p |- V/ [ [ A C ] = [ B C ] ] . $=
      ( eqid apeq12 ) ABCDDEDCFG $.
  $}

  ${
    apeq2.1 $e |- V/ [ A = B ] . $.
    $( Equality building rule for function application. (5201.6) $)
    apeq2 $p |- V/ [ [ C A ] = [ C B ] ] . $=
      ( eqid apeq12 ) DDCABDCFEG $.
  $}

  ${
    abeq.1 $e |- x : alpha V/ [ A = B ] . $.
    $( Equality building rule for function abstraction. $)
    abeq $p |- V/ [ [ L^ x A ] = [ L^ x B ] ] . $=
      ( fab dx eqq r-ab qeq ) BDGCDGEABCDEBCADEHFIJK $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                More Substitution Rules for Equality
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Theorems (5202) ~ (5204) are not proven here, substitution rules will
     be used instead. $)

  $( We can now also prove equality builders for the operation and quantifier 
     forms $)

  ${
    opeq123.1 $e |- V/ [ A = B ] . $.
    opeq123.2 $e |- V/ [ R = S ] . $.
    opeq123.3 $e |- V/ [ C = D ] . $.
    $( Equality building rule for operation $)
    opeq123 $p |- V/ [ [ A R C ] = [ B S D ] ] . $=
      ( fop fap dfop apeq12 eqr eqtr ) ADFKFALZDLZCBEGKZADCFMSRCSGBLZELZCRBECGM
      RUACQTCDEFGCABIHNJNOPOP $.
  $}

  ${
    opeq13.1 $e |- V/ [ A = B ] . $.
    opeq13.2 $e |- V/ [ C = D ] . $.
    $( Equality building rule for operation $)
    opeq13 $p |- V/ [ [ A R C ] = [ B R D ] ] . $=
      ( eqid opeq123 ) ABCDEFFGFCIHJ $.
  $}

  ${
    obeq1.1 $e |- V/ [ A = B ] . $.
    $( Equality building rule for operation. 
       (This proof could be shortened using ~ opeq12 ) $)
    opeq1 $p |- V/ [ [ A R C ] = [ B R C ] ] . $=
      ( eqid opeq13 ) ABCDDEFDCGH $.
  $}

  ${
    obeq3.1 $e |- V/ [ A = B ] . $.
    $( Equality building rule for operation $)
    opeq3 $p |- V/ [ [ C R A ] = [ C R B ] ] . $=
      ( eqid opeq13 ) DDCABEDCGFH $.
  $}

  ${
    eqeq12.1 $e |- V/ [ A = B ] . $.
    eqeq12.2 $e |- V/ [ C = D ] . $.
    $( Prove an equality of two equalities. $)
    eqeq12 $p |- V/ [ [ A = C ] = [ B = D ] ] . $=
      ( feq opeq13 ) ABCDEHFGI $.
  $}

  ${
    eqeq1.1 $e |- V/ [ A = B ] . $.
    $( Infer an equality from an equality of the first terms. $)
    eqeq1 $p |- V/ [ [ A = C ] = [ B = C ] ] . $=
      ( eqid eqeq12 ) ABCDDEDCFG $.
  $}

  ${
    eqeq2.1 $e |- V/ [ A = B ] . $.
    $( Infer an equality from an equality of the second terms. $)
    eqeq2 $p |- V/ [ [ C = A ] = [ C = B ] ] . $=
      ( eqid eqeq12 ) DDCABDCFEG $.
  $}

  ${    
    aleq.1 $e |- x : alpha V/ A : _o $.
    aleq.2 $e |- x : alpha V/ [ A = B ] . $.
    $( Equality building rule for universal quantifier $)
    aleq $p |- V/ [ [ A. x A ] = [ A. x B ] ] . $=
      ( fal ft fab feq fop df-al to dx eqq qr r-t eqr eqtr abeq opeq3 ) BDHIDJZ
      BDJZKLZECDHZABDEFMUFUEEUFUCCDJZKLEUEACDENCBADEOZBCUHBCUHGPQFRMUGUDEUCKACB
      DEBCUHGSUAUBTST $.

    $( Equality building rule for universal quantifier $)
    exeq $p |- V/ [ [ E. x A ] = [ E. x B ] ] . $=
      ( fex fn fap fal df-ex to dx wn wap apeq2 aleq teqr eqtr eqr ) BDHIIBJZDK
      ZJZECDHZABDEFLUDIICJZDKZJZEUEUCUGEIAUBUFDEMMIBADENZUIOFPBCUIIGQRQUEUHEACD
      EMBCUIFGSLUATT $.
  $}

  ${
    dfeq.1 $e |- V/ A : alpha $.
    dfeq.2 $e |- V/ B : alpha $.
    $( A definition of equality. $)
    dfeq $p |- V/ [ [ A = B ] == [ [ Q. A ] B ] ] . $=
      ( feq fop fq fap fbi dfop df-eq qeq apeq1 eqtr to tab wq wap df-bi mpeq
      eqr ) BCGHZIBJZCJZGHZUDUFKHZDUDGBJZCJDUFBCDGLUIUEDCGIDBGIDDMNOOPUHUGDUDUF
      DQAUECDQARAIBDADSETFTUAUCUB $.
  $}

  ${
    opab.1 $e |- V/ A : alpha $.
    opab.2 $e |- x : alpha V/ B : beta $.
    opab.3 $e |- x : alpha V/ C : gamma $.
    opab.4 $e |- x : alpha V/ R : ( ( delta gamma ) beta ) $.
    $( A theorem similar to the ax-4 series, for operation $)
    opab $p |- V/ [ [ [ L^ x [ B R C ] ] A ] = 
      [ [ [ L^ x B ] A ] [ [ L^ x R ] A ] [ [ L^ x C ] A ] ] ] . $=
      ( fop fab fap dfop apeq1 eqtr dx abeq tab wap ax-4ap eqr ) FIJOZGPZEQZJGP
      EQZFGPEQZQZIGPEQZQZHUKUMUJOZUIJFQZGPEQZUMQZHUNUIUPIQZGPZEQHURUHUTHEAUGUSG
      HFIAGHUAZJRUBSADCEUPGHIKDCUCZBJFVANLUDMUETUQULHUMAVBBEJGHFKNLUESTUOUNHUKU
      MHUJRUFT $.

    ${
      $d x R $.
      $( If ` x ` is not free in ` R ` , then the result is simpler $)
      opab13 $p |- V/ [ [ [ L^ x [ B R C ] ] A ] = 
        [ [ [ L^ x B ] A ] R [ [ L^ x C ] A ] ] ] . $=
        ( fop fab fap opab eqid ax-4c opeq123 eqtr ) FIJOGPEQFGPEQZIGPEQZJGPEQZ
        OHUCUDJOABCDEFGHIJKLMNRUCUCHUDUDUEJUCHSEJGHTUDHSUAUB $.
	  $}
  $}

  ${
    eqab.1 $e |- V/ A : alpha $.
    eqab.2 $e |- x : alpha V/ B : beta $.
    eqab.3 $e |- x : alpha V/ C : beta $.
     $( A theorem similar to the ax-4 series, for equality $)
    eqab $p |- V/ [ [ [ L^ x [ B = C ] ] A ] = 
      [ [ [ L^ x B ] A ] = [ [ L^ x C ] A ] ] ] . $=
      ( to feq tab fq df-eq wq r-t dat opab13 ) ABBKCDEFGLHIJKBMBMZALEFTLNFFOBF
      PQRS $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             Equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    bieq.1 $e |- V/ B : _o $.
    bieq.2 $e |- V/ [ A == B ] . $.
    $( Infer equality from equivalence $)
    bieq $p |- V/ [ A = B ] . $=
      ( fbi fop feq df-bi mpeq ) ABFGABHGCEABCDIJ $.
  $}

  ${
    mpbi.1 $e |- V/ B : _o $.
    mpbi.2 $e |- V/ A . $.
    mpbi.3 $e |- V/ [ A == B ] . $.
    $( An inference from a biconditional, related to modus ponens. (5201.1) $)
    mpbi $p |- V/ B . $=
      ( bieq mpeq ) ABCEABCDFGH $.
  $}

  ${
    eqbi.1 $e |- V/ B : _o $.
    eqbi.3 $e |- V/ [ A = B ] . $.
    $( Infer equivalence from equality $)
    eqbi $p |- V/ [ A == B ] . $=
      ( feq fop fbi df-bi eqr mpeq ) ABFGZABHGZCEMLCABCDIJK $.
  $}

  ${
    $d x A $. $d x B $.
    albi.1 $e |- V/ B : _o $.
    albi.2 $e |- V/ [ A == B ] . $.
    $( Equivalence building rule for universal quantifier, derived from 
       ~ aleq $)
    albi $p |- V/ [ [ A. x A ] == [ A. x B ] ] . $=
      ( ta fal to dat wal bieq teq feq fop daf aleq eqbi ) ACHBCHDGBCDIGBCDEJKG
      ABCDIGACDIABDEABDEFLZMJGABNOCDSPQR $.

    $( Equivalence building rule for universal quantifier, derived from
       ~ exeq $)
    exbi $p |- V/ [ [ E. x A ] == [ E. x B ] ] . $=
      ( ta fex to dat wex bieq teq feq fop daf exeq eqbi ) ACHBCHDGBCDIGBCDEJKG
      ABCDIGACDIABDEABDEFLZMJGABNOCDSPQR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Values for Abreviations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y V/ $. $d y A $.
    imv.1 $e |- V/ A : _o $.
    imv.2 $e |- V/ B : _o $.
    $( Value of a logical implication $)
    imv $p |- V/ [ [ A -> B ] = [ A = [ A /\ B ] ] ] . $=
      ( vy vx fin fop fx fan feq fab fap apeq1 to dx wxid dat eqtr dfop wan wop
      df-in weq ax-4ab eqab ax-4i opab13 ax-4c opeq13 eqeq12 abeq tab ddt ) ABH
      IZAAFJZKIZLIZFMZBNZCAABKIZLIZUPHANZBNCVAABCHUAVDUTCBVDGJZVEUQKIZLIZFMGMZA
      NZCUTHVHCAGFCUDOVIVGGMANZFMCUTPPPAVGGFCDPVEVFPGPFCQZQZPGVKRZPPPVEUQVLKVMP
      PUQGVKPFCRZSZVLUBZUCZUEUFPVJUSFCVJVEGMANZVFGMANZLIVKUSPPAVEGVKVFPPAFCDSZV
      MVQUGVRAVKVSURAGVKUHZVSVRUQGMANZKIVKURPPPPAVEGVKUQKVTVMVOVPUIVRAVKWBUQKWA
      AUQGVKUJUKTULTUMTTOTVAAFMBNZURFMBNZLICVCPPBAFCUREVTPPPAUQVKKVTVNPPPUNPUNK
      GVKVPUOUCUGWCACWDVBBAFCUJZWDWCUQFMBNZKICVBPPPPBAFCUQKEVTVNVKUBUIWCACWFBKW
      EBFCUHUKTULTT $.
  $}

  ${
    $d x y V/ $. $d y A $.
    orv.1 $e |- V/ A : _o $.
    orv.2 $e |- V/ B : _o $.
    $( Value of a logical implication $)
    orv $p |- V/ [ [ A \/ B ] = [ ~ [ [ ~ A ] /\ [ ~ B ] ] ] ] . $=
      ( vy vx for fop fap fn fan fab to wap eqtr ax-4ap ax-4c apeq12 ddt fx dat
      dfop df-or apeq1 dx wn wxid wan wop ax-4ab opab13 ax-4i opeq13 abeq tab )
      ABHIHAJZBJZCKKAJZKBJZLIZJZABCHUCURKFMBJZUSKFUAZJZLIZFMBJZJZCVBURKVFJZFMZB
      JCVHUQVJCBUQKKGUAZJZVELIZJZGMAJZFMZCVJUQVNFMGMZAJCVPHVQCAGFCUDUENNNAVNGFC
      DNNKVMNGNFCUFZUFZVSUGZNNNVLVEVSLNNKVKVSVTNGVRUHZOZNNKVDVSVTNNVDGVRNFCUHZU
      BZOZVSUIZUJZOUKPNVOVIFCVOKGMAJZVMGMAJZJVRVINNNAKGVRVMNNAFCDUBZVTWGQWHKVRW
      IVFAKGVRRZWIVLGMAJZVEGMAJZLIVRVFNNNNAVLGVRVELWJWBWEWFULWLUSVRWMVELWLWHVKG
      MAJZJVRUSNNNAKGVRVKWJVTWAQWHKVRWNAWKAGVRUMSPWMWHVDGMAJZJVRVENNNAKGVRVDWJV
      TWDQWHKVRWOVDWKAVDGVRRSPUNPSPUOPUENNNBKFCVFENNNUPZKGVRVTTZNNNUSVEVRLNNKAV
      RWQWJOZNNVEGVRWETNWPNUPLGVRWFTZUJQPVCKCVGVABKFCRZVGUSFMBJZVEFMBJZLICVANNN
      NBUSFCVELEWRNNKVDVRWQWCOWSULXAUSCXBUTLXAVCAFMBJZJCUSNNNBKFCAEWQWJQVCKCXCA
      WTBAFCRSPXBVCVDFMBJZJCUTNNNBKFCVDEWQWCQVCKCXDBWTBFCUMSPUNPSPP $.
  $}

  ${
    negv.1 $e |- V/ A : _o $.
    $( Value of negation $)
     negv $p |- V/ [ [ ~ A ] = [ F. = A ] ] . $=
       ( fn fap fq ff feq fop df-neg apeq1 to wf wqeq dfeq bieq eqr eqtr ) DAEF
       GEZAEZBGAHIZDSBABJKUATBUATBLGABBMZCNLGABUBCOPQR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Elementary Logic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y F $. $d x y V/ $. $d x beta $.
    dffun.1 $e |- V/ F : ( alpha beta ) $. 
    $( A definition of a function (5205). Note that ` x ` shall not be free in
      ` F ` . $)
    dffun $p |- V/ [ F = [ L^ x [ F x ] ] ] . $=
      ( vy feq fop fx fap fab eqid fal dat ax-3 dx wxid wap eqtr tab wab ax-4ap
      weq ax-4c ax-4i apeq12 opeq3 aleq eqr mpeq ) EEHIZEECJZKZCLZHIZDEDMULEGJZ
      KZURHIZGNZDUPABGDEEABUAZBEGDFOZVBPUPUTDUPURUOUQKZHIZGNDUTABGDEUOVBVABUOGD
      ABUNCDABEUMBCDQVABECDFOBCDRSUBOZPBVDUSGDAURVCBGDQZABEUQVFVBBGDRZSABUOUQVF
      VEVGSUDVCURVFURHVCECLUQKZUMCLUQKZKVFURBABUQECVFUMVGVABECVFVBOBCVFRUCVHEVF
      VIUQUQECVFUEUQCVFUFUGTUHUITUJTUK $.
  $}

  $( (5207) We have not introduced an operator for substitution.
     We'll actually write ` [ [ L^ x B ] A ] ` wherever "the result of 
     the substitution of ` x ` by ` A ` in ` B ` " is meant. $)

  ${
    5209.1 $e |- x : alpha V/ [ B = C ] . $.
    $( (5209) $)
    5209 $p |- V/ [ [ [ L^ x B ] A ] = [ [ L^ x C ] A ] ] . $=
      ( fab abeq apeq1 ) CDHFDHEBACFDEGIJ $.
  $}

  ${
    $d x y V/ $.
    dft.1 $e |- V/ A : alpha $.
    $( A definition of truth. (5210) $)
    dft $p |- V/ [ T. = [ A = A ] ] . $=
      ( vx vy ft fab fap feq fop ax-4c eqr fx fal wxid mpeq ax-4i eqeq12 eqtr
      eqid tab wab dat ax-3 dx wap weq df-al abeq eqeq2 apeq1 eqab ) GGEHZBIZCB
      BJKZUOGCBGECLMUOENZUQJKZEHZBIZCUPUNUSCBUNFNZFHZUQIZVCJKZEHZJKZUNUSJKCVDEO
      ZVFCVBVBJKVGCVBCUAAAECVBVBAAUBAVBECAAVAFCAFCPUCUDZVHUEQAVDECAVCVCAECUFZAA
      VBUQVIVHAECPZUGZVKUHUIQVEUSCUNAVDURECVCUQVIVCUQUQFVIRZVLSUJUKQULUTUQEHBIZ
      VMJKCUPAABUQECUQDVJVJUMVMBCVMBBECRZVNSTTT $.
  $}

  ${
    $d x V/ $.
    $( A definition of falsehood. (Lemma for (5214)) $)
    dff $p |- V/ [ F. = [ A. x x ] ] . $=
      ( ff ft fab fx feq fop fal df-f to wxid df-al eqr eqtr ) CDAEAFZAEGHZBPAI
      ZABJRQBKPABKABLMNO $.
  $}

  ${
    $d x y V/ $.
    $( Truth and Truth equals Truth. (5211) $)
    tteqt $p |- V/ [ [ T. /\ T. ] = T. ] . $=
	    ( vx vy ft fan fop fal fab fap ff fx feq to dx wt wab ax-1 ax-4c eqr eqtr
      opeq13 wxid wap aleq eqeq12 mpeq tab dat dft df-al ) DDEFZDBGZADDCHZDIZUM
      JIZEFZUMBKZIZBGZLFUKULLFABAUMMMDCMBANZMCUTNOPZQUPUKAUSULUNDAUODEDDCARJDCA
      RUAMURDBAMMUMUQUTVAMBAUBUCUQDCUTRUDUEUFDULADDBHZVBLFZAULMMUGVBAMMDBAMMDBA
      AOUHZPUIULVCAMDBAVDUJSTST $.
  $}

  $( Truth holds. (Lemma for 5212) $)
  truth $p |- V/ T. . $=
    ( fq feq fop ft eqid to tab wq dft eqr mpeq ) BBCDZEABAFEMAGGHGHBAGAIJKL $.

  $( Truth and Truth. (5212) $)
  tant $p |- V/ [ T. /\ T. ] . $=
    ( ft fan fop truth tteqt eqr mpeq ) BBBCDZAAEIBAAFGH $.

  ${
    eqan.1 $e |- V/ A : alpha $.
    eqan.2 $e |- V/ C : beta $.
    eqan.3 $e |- V/ [ A = B ] . $.
    eqan.4 $e |- V/ [ C = D ] . $.
    $( Infer conjunction of equalities (5213) $)
    eqan $p |- V/ [ [ A = B ] /\ [ C = D ] ] . $=
      ( ft fan fop feq tant dft opeq3 eqtr opeq13 mpeq ) LLMNCDONZFGONZMNEEPLUB
      ELUCMLCCONEUBACEHQCDECOJRSLFFONEUCBFEIQFGEFOKRSTUA $.
  $}

  ${
    $d x y V/ $.
    $( Conjunction of Truth and Falsehood. (5214) $)
    tfeqf $p |- V/ [ [ T. /\ F. ] = F. ] . $=
      ( vy vx ft ff fan fop fx fal fab fap feq to dx wxid wab ax-1 ax-4i opeq13
      wap aleq eqeq12 mpeq dff eqr eqtr ) DEFGZBHZBIZAECHZCJZDKZUKEKZFGZUKUHKZB
      IZLGUGUILGABAUKMMUJCMBANZMCUQOPZQUNUGAUPUIULDAUMEFDCARECARSMUOUHBAMMUKUHU
      QURMBAOTUHCUQRUAUBUCEUIABAUDUEUF $.
  $}

  ${
    uin.1 $e |- V/ A : alpha $.
    uin.2 $e |- x : alpha V/ B : _o $.
    uin.3 $e |- V/ [ A. x B ] . $. 
    $( Universal Instanciation (5215) - Here we write ` [ [ L^ x B ] A ] ` 
       instead of "the result of the substitution of ` x ` by ` A ` in ` B ` " 
       See (5207).
       $)
    uin $p |- V/ [ [ L^ x B ] A ] . $=
      ( ft fab fap truth ax-4c eqr fal feq fop df-al mpeq apeq1 eqtr ) ICDJZBKZ
      EELIIDJZBKZEUCUEIEBIDEMNUDUBEBCDOUDUBPQEHACDEGRSTUAS $.
  $}

  ${
    $d x y V/ $.
    tana.1 $e |- V/ A : _o $.
    $( Conjunction with Truth. (5216) $)
    tana $p |- V/ [ [ T. /\ A ] = A ] . $=
      ( vy vx ft fan fop fab fap feq to ff eqab opeq13 opab13 ax-4c eqtr eqeq12
      ax-4i fx dx wt dat wxid tab wan ddt wop weq fal tteqt teq tfeqf eqan ax-1
      wf wab wap aleq mpeq uin ) FDUAZGHZDIAJZVCDIAJZKHZFAGHZAKHBVDVCKHZDIAJVGB
      LAVIDBCLVDVCLDBUBZLLLFVCVJGLLFDBBUCZUDZLDBUEZLLLUFZLUFGEVJLEVJUBZUGZUHZUI
      ZVMUJFFGHZFKHZFMGHZMKHZGHZVIDUKZBLLVSFBWAMLVSFBVKBULZUMLWAMBBUQZBUNZUMWEW
      GUOFEUAZGHZWHKHZEIZFJZWKMJZGHZWKVCJZDUKZKHWCWDKHBDBWKVNLWKDBLLWJEBLWIWHLE
      BUBZLLLFWHWQGWQUCZLEBUEZWQUGZUIZWSUJURUDZUPWNWCBWPWDWNWIEIZFJZWHEIZFJZKHZ
      XCMJZXEMJZKHZGHBWCWLXGBWMXJGLLFWIEBWHVKXAWSNLLMWIEBWHWFXAWSNOXGVTBXJWBGXD
      VSBXFFXDFEIZFJZXFGHBVSLLLLFFEBWHGVKWRWSWTPXLFBXFFGFFEBQFEBTZORXMSXHWABXIM
      XHXKMJZXIGHBWALLLLMFEBWHGWFWRWSWTPXNFBXIMGMFEBQMEBTZORXOSORLWOVIDBLLWKVCV
      JXBVMUSWOXCVCJZXEVCJZKHVJVILLVCWIEVJWHVMLLLFWHVOGVOUCZLEVJUEZVPUIXSNXPVDV
      JXQVCXPXKVCJZXQGHVJVDLLLLVCFEVJWHGVMXRXSVPPXTFVJXQVCGVCFEVJQVCEVJTZORYASR
      UTSVAVAVBLLAVDDBVCCVRVMNVAVEVHBVFAVEFDIAJZVFGHBVHLLLLAFDBVCGCVLVMVQPYBFBV
      FAGAFDBQADBTZORYCSVA $.
  $}

  ${ 
    $d x y V/ $.
    $( Equality of Truth and falsehood. (5217) $)
    teqf $p |- V/ [ [ T. = F. ] = F. ] . $=
      ( vy vx ft ff feq fop fal fan fab fap to dx wt wxid wab eqab ax-4c eqeq12
      eqtr fx tab weq dat ax-1 ax-4i wf opeq13 wap aleq mpeq dft eqr opeq1 tana
      eqeq1 df-f ax-3 teqr ) DEFGZDBUAZFGZBHZAEDUTIGZVCFGZUTVCFGADDFGZUTIGZVCFG
      ZVEADCUAZFGZCJZDKZVKEKZIGZVKVAKZBHZFGVHABAVKLLUBLVKBALLVJCALDVILCAMZVQNZL
      CAOZUCPUDZUEVNVGAVPVCVLVFAVMUTIVLDCJZDKZVICJZDKZFGAVFLLDDCAVIANZVRVSQWBDA
      WDDDDCARDCAUFSTVMWAEKZWCEKZFGAUTLLEDCAVIAUGZVRVSQWFDAWGEEDCARECAUFSTUHLVO
      VBBALLVKVALBAMZVTLBAOZUIZVOWAVAKZWCVAKZFGZWIVBLLVADCWIVIWJLCWIMNZLCWIOZQZ
      WLDWIWMVAVADCWIRVACWIUFSZTUJSUKVGVDAVCVFDAUTIDVFALDAWEULUMUNUPUKVDUTAVCUT
      ALDEAWEWHUCUOUPUKEVCAEWAWCFGZAVCCAUQWSWNBHAVCLLBAWAWCLLDCWIWOPLLVICWIWPPU
      RLWNVBBALVOWNWIWKWQUSWRUJTTUMT $.
  $}

  ${ 
    $d x y V/ $.
    teqa.1 $e |- V/ A : _o $.
    $( Equality with Truth. (5218) $)
    teqa $p |- V/ [ [ T. = A ] = A ] . $=
      ( vy vx ft feq fop fab fap to dx wxid weq eqab ax-4c ax-4i eqeq12 eqtr ff
      fx wt wab wap teqr fan fal wf dft eqr teqf eqan ax-1 dat opeq13 aleq mpeq
      uin ) FDUAZGHZUSGHZDIAJZFAGHZAGHZBKAVADBCKFEUAZGHZVEGHZEIZUSJZVAKDBLZKKVH
      USVJKKVGEVJKVFVEKEVJLZKFVEVKVKUBZKEVJMZNZVMNUCZKDBMZUDZVIVFEIZUSJZVEEIZUS
      JZGHVJVAKKUSVFEVJVEVPVNVMOVSUTVJWAUSVSFEIZUSJZWAGHVJUTKKUSFEVJVEVPVLVMOWC
      FVJWAUSUSFEVJPUSEVJQZRSWDRSZUEFFGHZFGHZFTGHZTGHZUFHZVADUGZBKKWFFBWHTKFFBB
      UBZWLNKFTBWLBUHZNFWFBKFBWLUIUJBUKULVHFJZVHTJZUFHZVIDUGZGHWJWKGHBDBVHVOUMW
      PWJBWQWKWNWGBWOWIUFWNVRFJZVTFJZGHBWGKKFVFEBVEWLKFVEKEBLKKFEBWLUNZKEBMZNZX
      AOWRWFBWSFWRWBFJZWSGHBWFKKFFEBVEWLWTXAOXCFBWSFFFEBPFEBQZRSXDRSWOVRTJZVTTJ
      ZGHBWIKKTVFEBVEWMXBXAOXEWHBXFTXEWBTJZXFGHBWHKKTFEBVEWMWTXAOXGFBXFTTFEBPTE
      BQZRSXHRSUOKVIVADBVQWEUPRUQUQURVBUTDIAJZUSDIAJZGHBVDKKAUTDBUSCKFUSVJKKFDB
      WLUNZVPNVPOXIVCBXJAXIFDIAJZXJGHBVCKKAFDBUSCXKVPOXLFBXJAAFDBPADBQZRSXMRSUQ
      $.
  $}

  ${
    eqt1.1 $e |- V/ A : _o $.
    eqt1.2 $e |- V/ A . $.
    $( Rule T, first direction (5219) $)
    eqt1 $p |- V/ [ T. = A ] . $=
      ( ft feq fop teqa eqr mpeq ) AEAFGZBDKABABCHIJ $.
  $}

  ${
    eqt2.1 $e |- V/ A : _o $.
    eqt2.2 $e |- V/ [ T. = A ] . $.
    $( Rule T, second direction (5219) $)
      eqt2 $p |- V/ A . $=
      ( ft truth mpeq ) EABBFDG $.
  $}

  ${
    $d x A $.
    ugen.1 $e |- V/ A : _o $.
    ugen.2 $e |- V/ A . $.
    $( Universal generalization (5220) The distinct variable restriction 
       prevents ` x ` from occurring in ` A ` . $)
    ugen $p |- V/ [ A. x A ] . $=
      ( ta ft fab feq fop fal dx to dat daf eqt1 abeq df-al eqr mpeq ) GBHABHIJ
      ZABKZCFGABCAFBCLMFABCDNZFABCEOPQUBUACFABCUCRST $.
  $}

  ${
    $d x V/ $. $d x F $.
    rcasap.1 $e |- V/ F : ( _o _o ) $.
    rcasap.2 $e |- V/ [ F T. ] . $.
    rcasap.3 $e |- V/ [ F F. ] . $.
    rcasap.4 $e |- V/ B : _o $.
    $( Rule of cases (5222), special version for function application. $)
    rcasap $p |- V/  [ F B ] . $=
      ( vx fab fap fx to dx wap ft ff fan fop eqt1 mpeq tab dat wxid tant wt wf
      fal opeq13 ax-1 uin ax-4ap ax-4c ax-4i apeq12 ) CHIAJZHKZHIAJZJZCAJBCUPJZ
      HIAJURBLAUSHBGLLCUPLHBMLLUALCHBDUBZLHBUCZNCOJZCPJZQRZUSHUGBOOQRVDBBUDOVBB
      OVCQVBBLLCOBDBUENESVCBLLCPBDBUFNFSUHTHBCUTUITUJLLLACHBUPGUTVAUKTUOCBUQAAC
      HBULAHBUMUNT $.
  $}

  $( This additional form for the axiom 4, where the lambda form is applied 
     to the same variable it is created with, is not in the original textbook, 
     but seems to be required in Metamath to prove ~ rcases . $)
  ax-4v $a |- V/ [ [ [ L^ x A ] x ] = A ] . $.

  ${
    $d x B $.
    daabap.1 $e |- V/ B : alpha $.
    daabap.2 $e |- V/ [ [ L^ x A ] B ] . $.
	  $( This additional axiom, which adds a type declaration to the application
	     of an abstration, where that variable ` x ` is actually free, seems to 
	     be required in Metamath to prove ~ rcases . $)
	  daabap $a |- x : alpha V/ [ [ L^ x A ] B ] . $.
  $}

  ${
    $d x V/ $.
    rcases.1 $e |- x : _o V/ A : _o $.
    rcases.2 $e |- V/ [ [ L^ x A ] T. ] . $.
    rcases.3 $e |- V/ [ [ L^ x A ] F. ] . $.
    $( Rule of cases (5222) $)
    rcases $p |- x : _o V/ A . $=
      ( fab fx fap to dx drt wab ft wt daabap ff wf wxid rcasap ax-4v mpeq ) AB
      GZBHZIAJBCKZUDUEUCJJABUEJJABCDLMJANBCCOEPJAQBCCRFPJBCSTABUEUAUB $.
  $}

  ${
    tima.1 $e |- V/ A : _o $.
    $( Implication of the truth (5223) $)
    tima $p |- V/ [ [ T. -> A ] = A ] . $=
      ( ft fin fop fan feq wt imv to wan wop teqa eqtr tana ) DAEFZDAGFZBAQDRHF
      BRDABBIZCJRBKKKDABGSCBLMNOABCPO $.
  $}

  ${
    mp.1 $e |- V/ A : _o $.
    mp.2 $e |- V/ B : _o $.
    mp.3 $e |- V/ [ A -> B ] . $.
    mp.4 $e |- V/ A . $.
    $( Modus Ponens. (5224) $)
    mp $p |- V/ B . $=
      ( ft fin fop eqt1 eqr opeq1 mpeq tima ) HBIJZBCABIJPCFAHCBIHACACDGKLMNBCE
      ON $.
  $}

 
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Examples
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    wiki.1 $e |- x : _o V/ A : _o $.
    wiki.2 $e |- x : _o V/ B : _o $.
    wiki.3 $e |- V/ [ E. x A ] . $.
    wiki.4 $e |- x : _o V/ [ A -> B ] . $.
    $( Example in wikipedia $)
    wiki $p |- V/ [ E. x [ A /\ B ] ] . $=
      ( fex fan fop to fin feq dx imv mpeq exeq ) ACIABJKZCIDGLASCDEABMKASNKLCD
      OZHABTEFPQRQ $.
	$}
