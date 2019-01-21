(* The propositional logic structure, which will build a tree of propositions*)
(* The 'Lits' or literals are the axioms*)
datatype prop = 
		  Lit of string
		| Not of prop
		| And of prop * prop
		| Or of prop * prop
		| Imp of prop * prop
		| Iff of prop * prop;
		
(* order of precedence is Lit, Not, And, Or, Imp, Iff, so same as prop is written here*)

(* Returns an identity for the prop, does the constructor contain 1 or 2 sub propositions. *)
(* More specific identities for extracting And and Or, used in prettyprinting. *)
datatype propType = Unit | Pair | AND | OR;

fun idProp (Lit s) = Unit | idProp (Not p) = Unit | idProp (And p) = Pair
  | idProp (Or p) = Pair | idProp (Imp p) = Pair | idProp (Iff p) = Pair;	
  
fun idPropAnd (Lit s) = Unit | idPropAnd (Not p) = Unit | idPropAnd (And p) = AND
  | idPropAnd (Or p) = Pair | idPropAnd (Imp p) = Pair | idPropAnd (Iff p) = Pair;
  
fun idPropOr (Lit s) = Unit | idPropOr (Not p) = Unit | idPropOr (And p) = Pair
  | idPropOr (Or p) = OR | idPropOr (Imp p) = Pair | idPropOr (Iff p) = Pair;

(*Functions for creating a list of literals and bools, and for looking up in it*)
(* Simple list, O(n) for each search, not the most efficient *)
exception Missing;

fun update (pairs, lit, b) = (lit,b)::pairs;

fun lookup (i, [])           = raise Missing
  | lookup (i, (literal:string,b:bool)::pairs) =
      if i=literal then  b  else  lookup(i, pairs);
      
(* This function tests to see if a given proposition holds under an interpretation*)
fun test (Lit s, pairs) = lookup(s, pairs)
  | test (Not p, pairs) = not (test(Not p, pairs))
  | test (And (p1, p2), pairs) = (test (p1, pairs)) andalso (test (p2, pairs))
  | test (Or (p1,p2), pairs) = (test (p1, pairs)) orelse (test (p2, pairs))
  | test (Imp (p1, p2), pairs) = (not (test (p1, pairs))) orelse (test (p2, pairs))
  | test (Iff (p1, p2), pairs) = (test (Imp (p1,p2), pairs)) 
  								andalso (test (Imp (p2, p1), pairs));

(* For testing, an example proposition and interpretation *)  
(* Running these four lines should output val it = true: bool, val it = false: bool*)								
val p = And(Imp(Lit "P", Lit "Q"),Imp(Lit "Q", Lit "P"));
val inter1 = [("P", true), ("Q", true)];
val inter2 = [("P", true), ("Q", false)];
test(p,inter1); test(p, inter2);

(* This function converts the proposition to Negation Normal Form *)
(* This is where only ∧, ∨ and ¬ are used, no -> or <-> *)
fun convNNF (Lit s) = Lit s
  | convNNF (Not p) = Not (convNNF p)
  | convNNF (And (p1, p2)) = And ((convNNF p1), (convNNF p2))
  | convNNF (Or (p1, p2)) = Or ((convNNF p1),(convNNF p2))
  | convNNF (Imp (p1, p2)) = Or (Not (convNNF p1), (convNNF p2))
  | convNNF (Iff (p1, p2)) = convNNF(And (Imp (p1, p2), Imp(p2, p1)));
  
(* Pretty Printing: This function prints in a human readable format: *)
fun prettyprint (Lit s) = s
  | prettyprint (Not p) = 
  		(case p of 
  			  (Lit s) => "!" ^ s
  			| (Not p2) => "!" ^ (prettyprint p2)
  			| _ => "!(" ^ (prettyprint p) ^ ")" )
  | prettyprint (And (p1,p2)) = 
  		(case (idPropAnd p1, idPropAnd p2) of
  			  (Unit, Unit) => (prettyprint p1) ^ " & " ^ (prettyprint p2)
  			| (AND, Unit) => (prettyprint p1) ^ " & " ^ (prettyprint p2)
  			| (Unit, AND) => (prettyprint p1) ^ " & " ^ (prettyprint p2)
  			| (Unit, Pair) => (prettyprint p1) ^ " & (" ^ (prettyprint p2) ^ ")"
  			| (Pair, Unit) => "(" ^ (prettyprint p1) ^ ") & " ^ (prettyprint p2)
  			| _ => "(" ^ (prettyprint p1) ^ ") & (" ^ (prettyprint p2) ^ ")" )
  | prettyprint (Or (p1, p2)) =
  		(case (idPropOr p1, idPropOr p2) of
  			  (Unit, Unit) => (prettyprint p1) ^ " | " ^ (prettyprint p2)
  			| (OR, Unit) => (prettyprint p1) ^ " | " ^ (prettyprint p2)
  			| (Unit, OR) => (prettyprint p1) ^ " | " ^ (prettyprint p2)
  			| (Unit, Pair) => (prettyprint p1) ^ " | (" ^ (prettyprint p2) ^ ")"
  			| (Pair, Unit) => "(" ^ (prettyprint p1) ^ ") | " ^ (prettyprint p2)
  			| _ => "(" ^ (prettyprint p1) ^ ") | (" ^ (prettyprint p2) ^ ")" )
  | prettyprint (Imp (p1, p2)) = 
  		(case (p1,p2) of
  			  (Iff p3, Iff p4) => "(" ^ (prettyprint (Iff p3)) ^ ") -> (" ^ (prettyprint (Iff p4)) ^ ")"
  			| (Iff p3, _) => "(" ^ (prettyprint (Iff p3)) ^ ") -> " ^ (prettyprint p2)
  			| (_, Iff p4) => (prettyprint p1) ^ " -> (" ^ (prettyprint (Iff p4)) ^ ")"
  			| _ => (prettyprint p1) ^ " -> " ^ (prettyprint p2) )
  | prettyprint (Iff (p1, p2)) = 
  		(case (p1,p2) of
  			  (Imp p3, Imp p4) => "(" ^ (prettyprint (Imp p3)) ^ ") <-> (" ^ (prettyprint (Imp p4)) ^ ")"
  			| (Imp p3, _) => "(" ^ (prettyprint (Imp p3)) ^ ") <-> " ^ (prettyprint p2)
  			| (_, Imp p4) => (prettyprint p1) ^ " <-> (" ^ (prettyprint (Imp p4)) ^ ")"
  			| _ => (prettyprint p1) ^ " <-> " ^ (prettyprint p2) );

fun printout p = TextIO.print("\nproposition: " ^ prettyprint(p) ^ "\n\n");

(* Testing: printout (convNNF p); should give : proposition: (!P | Q) & (!Q | P) *)

(* This section takes a string and converts it into a prop structure *)
exception empty;
exception malformedInput;

(* Used in reading literals, if it gets the head of an empty list, returning a non alpha
 exits the function *)
fun headLit [] = #"?"
  | headLit (x::xs) = x;

fun head [] = raise empty
  | head (x::xs) = x;
  
fun tail [] = raise empty
  | tail (x::xs) = xs;

(* Given a list of chars, it extracts the literal as a string, and returns the remaining list*)
(* Takes a bool to tell it the start of the list is a char, if false it returns an empty string*)
(* Test it with: readLiteral (true, (explode "abcd123"));, should give abcd and the list of 1,2,3 chars*)
fun readLiteral (b,[]) = ("", [])
  | readLiteral (false, c) = ("", c) 
  | readLiteral (true,(s::chars)) = 
  	let val x = readLiteral ((Char.isAlpha (headLit chars)), chars) in
  		((Char.toString s) ^ (#1 x), (#2 x))
  	end;

(* Checks that the input is valid syntax before creating tree*)
fun check([],0,operations,operands) = if operands = operations + 1 then true else false
  | check([],brackets,operations,operands) = false
  | check((s::chars),brackets,operations,operands) = 
  		if brackets < 0 then false else
  		(* Reads in the literal and increments operands, passing in the string after the literal *)
  		if (Char.isAlpha s) then check(#2 (readLiteral(true, (s::chars))), brackets, operations, operands + 1)
  		else if s = #" " then check(chars, brackets, operations, operands)
  		else
  			let val h = (headLit chars) in
  			(case s of
  				  #"(" => if (Char.isAlpha h) orelse h = #"!" orelse h =  #"(" then
  				  check(chars, brackets+1, operations, operands) else false
  				| #")" => if h = #"&" orelse h = #"|" orelse h = #"<" orelse h = #"-" then
  							check(chars, brackets-1, operations, operands) else false
  				| #"&" => check(chars, brackets, operations+1, operands)
  				| #"|" => check(chars, brackets, operations+1, operands)
  				| #"!" =>  if h = #"(" orelse h = #"!" orelse (Char.isAlpha h) then
  							check(chars, brackets, operations, operands) else false
  				| #"<" => if h = #"-" then 
  							check(chars, brackets, operations, operands) else false
  				| #"-" => if h = #">" then 
							check((tail chars), brackets, operations+1, operands) else false
			    | _ => false)
			end;
	
fun chk s = check((explode s), 0, 0, 0);
(* Testing the checking function*)
(*		    
chk "!(Q&P)<->(A|B)"; should return true
chk "((A|B)&C"; should return false
*)
			
(*Tokens will be used to tokenise the string after it is checked*)
(* Sub is for bracketed sub propositions from the input*)
datatype tokens = tLit of string | tnot | tand | tor | tImp | tIff | subOpen | subClose;

(*Since its after checking, it knows the structure is valid, so can only get these tokens
  Or a literal *)
fun tokenizer tokens [] = rev tokens
  | tokenizer tokens (s::chars) = 
  		(case s of
  			  #"(" => tokenizer (subOpen::tokens) chars
  			| #")" => tokenizer (subClose::tokens) chars
  			| #"!" => tokenizer (tnot::tokens) chars
  			| #"&" => tokenizer (tand::tokens) chars
  			| #"|" => tokenizer (tor::tokens) chars
  			| #"-" => tokenizer (tImp::tokens) (tail chars)
  			| #"<" => tokenizer (tIff::tokens) (tail (tail chars))
  			| #" " => tokenizer tokens chars
  			| _ => let val lit = (readLiteral (true, (s::chars))) in
  					  tokenizer ((tLit (#1 lit))::tokens) (#2 lit) end );

(* Where the user has used parentheses, get the parenthesised contents and the remaining string*)
(* Note this will include inner parentheses, they have to balance *)
exception probablyAccidentlyIncludedFirstBracket;
fun getSubProp (tokens, 0, innerList) = (innerList, tokens)
  | getSubProp ((t::tokens), brackets, innerList) =
  			if t = subOpen then getSubProp(tokens, brackets+1, (t::innerList))
  			else if t = subClose then getSubProp(tokens, brackets-1, (t::innerList))
  			else getSubProp(tokens, brackets, (t::innerList))
  | getSubProp ([], brackets, innerList) = raise probablyAccidentlyIncludedFirstBracket;

(* Gets the inner expression, in correct order without the enclosing brackets *)
(* Assumes you pass from the string discovered after the first bracket *)
(* Note here we are working on the tokens now, not the char literals*)
fun getInner tokens =
			let val t = getSubProp(tokens, 1, []) in
				(rev (tail (#1 t)), #2 t)
			end;  
			
(* testing get inner (which extracts token lists from within parenthesis, and removes the parems)*)
(* tokenizer [] (explode "(ab&c)|d");
getInner (tail it);  should return a tokens list of 
([tLit "ab", tand, tLit "c"], [tor, tLit "d"])*)

(* Constructing the prop tree from the tokens list, in order of precedence:
  Not, And, Or, Imp, Iff,
  all brackets will be built into props first*)
  
datatype builder = Prop of prop | Token of tokens;

(* Copies the tokens into a builder list - a bit wasteful but otherwise I would have to
  change the tokenizer stage to wrap everything in a 'Token' constructor*)
fun genBuilderList [] builderList = builderList
  | genBuilderList (t::tokenList) builderList = genBuilderList tokenList ((Token t) :: builderList);
  
fun genBuilders tokenList = rev (genBuilderList tokenList []);

exception errorInBuild; (*A serious error, if this exception occurs a very significant bug is present,
 probably meaning that the checker has allowed syntax that should not be acceptable in the language*)

(*Replaces not tokens with not props*)
fun replaceNot [] builderOut = builderOut
  | replaceNot ((b:builder)::builderIn) builderOut = 
  		if b = (Token tnot) then
  			(case (head builderIn) of
				  (Prop p) => replaceNot (tail builderIn) (Prop (Not p) :: builderOut)
				| (Token (tLit s)) => replaceNot (tail builderIn) (Prop (Not (Lit s)) :: builderOut)
				| _ => raise errorInBuild
			)
		else replaceNot builderIn (b::builderOut);

fun repNot build = rev (replaceNot build []);

(*Rep op can take any pair operator given a function to construct the relevant prop 
 data type and a tokens data type that it is searching for and replace it with the relevant prop structure *)
fun replaceOp [] builderOut (p:(prop * prop -> prop)) top = builderOut
  | replaceOp (b1::[]) builderOut p top = b1::builderOut
  | replaceOp (b1::b2::[]) builderOut (p:(prop * prop -> prop)) top = (b2::b1::builderOut) 
  | replaceOp ((b1:builder)::bop::builderIn) builderOut (p:(prop * prop -> prop)) top = 
  		if bop = (Token top) then
  			(case (b1, (head builderIn)) of
  				  (Prop p1, Prop p2) => 
  				  	replaceOp (tail builderIn) (Prop (p (p1, p2)) :: builderOut) p top
  				| (Prop p1, Token (tLit s)) => 
  					replaceOp (tail builderIn) (Prop (p (p1, (Lit s))) :: builderOut) p top
  				| (Token (tLit s), Prop p2) =>
  					replaceOp (tail builderIn) (Prop (p ((Lit s), p2)) :: builderOut) p top
  				| (Token (tLit s1), Token (tLit s2)) =>  
  					replaceOp (tail builderIn) (Prop (p ((Lit s1), (Lit s2))) :: builderOut) p top
  				| _ => raise errorInBuild
  					
  			) 
  		else replaceOp (bop::builderIn) (b1::builderOut) p top;
  		
fun insAnd(p1, p2) = And (p1,p2);
fun insOr(p1, p2) = Or (p1,p2);
fun insImp(p1, p2) = Imp (p1,p2);
fun insIff(p1, p2) = Iff (p1,p2);
			    
fun repOp build f tokenOperator = rev (replaceOp build [] f tokenOperator);

			    
(* Testing on not
	val b = tokenizer [] (explode "!a&b|!c"); // gets some tokens
	val build = genBuilders b; // converts to builder list
	repNot build; // hopefully removes nots
	
	testing on or:
	val b = tokenizer [] (explode "!a&b|!c");
	val build = genBuilders b;
	repNot build;
	repOp it insOr tor;
	
	
	val b = tokenizer [] (explode "!a&b|c<->!d");
*)

(*Now need to build function that applies them to all*)

fun replaceAll [] = []
  | replaceAll tokensList = 
  		let val builderList = genBuilders tokensList in
  			let val notsList = repNot builderList in
  				let val andsList = repOp notsList insAnd tand in
  					let val orsList = repOp andsList insOr tor in
  						let val impsList = repOp orsList insImp tImp in
  							repOp impsList insIff tIff
  		end end end end end;


(*For testing, rakes an input string, with no brakets in*)

(*Outputs a fully parsed proposition *)
fun outputProposition ((Prop p)::[]) = printout p;

(* Applies a non simplified NNF set of transformations as defined above *)
fun convertToNNF ((Prop p)::[]) = convNNF p;

(* Checks if the subsection contains a bracketed subsection: *)
(* If it does, it fetches it and returns the remaining tokens to be parsed*)
fun containsSub [] = (false, ([], []))
  | containsSub (t::tokens) = if t = subOpen then (true, getInner tokens) else containsSub tokens;
  
fun getBuiltProp ((Prop p)::[]) = p;
  
(*Performs iterative parses of replaceAll in bracketed subsections, 
by funding subsections, converting them and adding them to the builderList*)
fun convertSubsections [] builderList = builderList
  | convertSubsections tokens builderList = 
  		let val contains = containsSub tokens in
  			if #1 contains = false then replaceAll tokens
  			else convertSubsections (#2 (#2 contains)) (Prop (getBuiltProp (convertSubsections (#1 (#2 contains)) [])) :: builderList)
  		end ;
  		
fun convertTokens ts = convertSubsections ((subOpen::ts)@[subClose]) [];

(* For now its using the non brackets version, cause that was not working*)
(* will build later*) 		
fun inputString str = if (chk str) then (replaceAll (tokenizer [] (explode str)))
				  else raise malformedInput;
				  
				  
(*to input a string, do inputString <your string proposition>*)
(*to print it out use outputProposition (using the aboves result)*)
(*to convert to NNF form use convertToNNF on the first result*)
(*to putput that use printout*)
(*to apply a implementation, see the implementation function at the top, using getBuiltProp
to get the prop out the final builder list, and pass it into the implementation funtion*)







