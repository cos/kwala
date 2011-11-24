module KWALA-SYNTAX
/*@ \section{Syntax}
...*/
 syntax Variable ::= #Int		

 syntax TypeNameBase ::= #Id				
			| #Id "/" TypeNameBase				[:prec(33):]
 syntax TypeName ::= "L" TypeNameBase						[:prec(33):]
			| "A" TypeNameBase
	//put A instead of [
 syntax TypeReference ::= "<" #Id "," TypeName ">"				[:prec(40):]
 syntax FieldReference ::= "<" #Id "," TypeName "," #Id "," TypeReference ">"	[:prec(50):]

 syntax Params ::= List{Variable,","}
	//put , instead of space
 syntax NewInstructionBase ::= Variable "=" "new" TypeReference "@" #Int 	[:prec(70):]
 syntax NewInstruction ::= NewInstructionBase 					[:prec(70):]
			| NewInstructionBase "(" Params ")" 			[:prec(70):]
 syntax GetInstruction ::= Variable "=" "getfield" FieldReference Variable 	[:prec(70):]
			| Variable "=" "getstatic" FieldReference		[:prec(70):]
 syntax PutInstruction ::= "putfield" Variable "=" Variable FieldReference	[:prec(70):]
			| "putstatic" Variable FieldReference			[:prec(70):]
 syntax PhiInstruction ::= Variable "=" "phi" "(" Params ")" 			[:prec(70):]
	//put param list in ()

 syntax Instruction ::= NewInstruction
			| GetInstruction
			| PutInstruction
			| PhiInstruction

 syntax Statement ::= Instruction ";"	[:prec(100):]
end module


module KWALA
  imports KWALA-SYNTAX
/*@ \section{Semantics}
... */

/*@ \subsection{Configuration}
...*/
configuration <T color="gray">
		<k color="red"> $PGM:K </k>
		</T>

// configuration <T color="gray">
//		<class multiplicity="*" color="white"> 	
//		  <className color="cyan"> Object </className>
//		  <method multiplicity="*" color="yellow">
//			<methodName color="red"> main </methodName>
//			<edges color="orange"> .Map </edge>
//			<basicBlock multiplicity="*" color="brown">
//				<blockName color="gray"> null </blockName>
//				<block color="white"> .List </block>
//			</basicBlock>
//		  </method>
//		 </class>
//		 <heapAbstraction color="yellow">.Map</heapAbstraction>
//		 <task color="violet"> 
//			<k color="white"> $PGM:K </k>
//		 </task>
//		</T>




/*@ \subsection{Results}
...*/

//  syntax KResult ::= #Int | #Bool

/*@ \subsection{Arithmetic Expressions}
...*/

/*@ \subsubsection{Variable Lookup}
...*/

//  rule <k> X:#Id => I ...</k> <state>... X |-> I ...</state>

/*@ \subsubsection{Arithmetic operators}
...*/

//  rule I1:#Int + I2:#Int => I1 +Int I2
//  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 

/*@ \subsection{Boolean Expressions}
...*/

//  rule I1 <= I2 => I1 <=Int I2
//  rule not(T:#Bool) => notBool T  
//  rule true and B:BExp => B  
//  rule false and _ => false

/*@ \subsection{Statements}
...*/

/*@ \subsubsection{Skip}
...*/

//  rule skip => .

/*@ \subsubsection{Assignment}
...*/

//  rule <k> X:=I:#Int => . ...</k> <state>... X |-> (_ => I) ...</state>

/*@ \subsubsection{Sequential Composition}
...*/

//  rule S1:Stmt ; S2:Stmt => S1 ~> S2

/*@ \subsubsection{Conditional}
...*/

//  rule if true then S:Stmt else _ => S
//  rule if false then _ else S => S

/*@ \subsubsection{While Loop}
...*/

//  rule <k> while B do S => if B then (S ; while B do S) else skip ...</k> [:structural:]

/*@ \subsection{Programs}
...*/

//  rule <k> var ; S => S ...</k>
//  rule <k> var (X,Xl:Ids => Xl); _ ...</k> <state>... . => X |-> 0 ...</state> 
end module
