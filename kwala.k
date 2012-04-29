module KWALA-SYNTAX
/*@ \section{Syntax}
...*/
 syntax #Id ::= object
		| null
	//convert class names to start with lower case or '

 syntax Variable ::= #Int		
 syntax VariableName ::= "v" #Int						[:prec(20):]

 syntax MethodName ::= "<" "init" ">" | #Id | "main"

// [Ljava/lang/String;

 syntax FormalParams ::= List{TypeName,","}
// note: change to "[" "]" if you want to look at the formal parameters
// syntax Selector ::= MethodName "(" FormalParams ")" "V"			[:prec(40):]
 syntax Selector ::= MethodName "[" FormalParams "]" 				[:prec(40):]
 syntax TypeName ::= #Id				
			| #Id "/" TypeName					[:prec(33):]
// syntax TypeName ::= "L" TypeNameBase						[:prec(33):]
//			| "A" TypeNameBase
	//put A instead of [
 syntax TypeReference ::= "<" #Id "," TypeName ">"				[:prec(41):]
 syntax FieldReference ::= "<" #Id "," TypeName "," #Id "," TypeReference ">"	[:prec(50):]
//note: originally <...> but it seems to the parser this clashes with the cell(?) syntax
 syntax MethodReference ::= "<|" #Id "," TypeName "," Selector "|>"		[:prec(51):]
			| "none"

 syntax Params ::= List{Variable,","}
	//put , instead of space
 syntax NewInstructionBase ::= Variable "=" "new" TypeReference "@" #Int 		[:prec(70):]
 syntax NewInstruction ::= NewInstructionBase 						[:prec(71):]
			| NewInstructionBase "(" Params ")" 				[:prec(72):]
 syntax GetInstruction ::= Variable "=" "getfield" FieldReference Variable 		[:prec(73):]
// meaning: Var1 = gf F Var2 <=> Var1 = Var2 . F
			| Variable "=" "getstatic" FieldReference			[:prec(74):]
 syntax PutInstruction ::= "putfield" Variable "=" Variable FieldReference		[:prec(75):]
// meaning: pf Var1 = Var2 F <=> Var1 . F = Var2
			| "putstatic" Variable FieldReference					[:prec(76):]
 syntax PhiInstruction ::= Variable "=" "phi" "(" Params ")" 					[:prec(77):]
 syntax PhiPhiInstruction ::= Variable "=" "phiphi" "(" Params ")" 				[:prec(78):]
	//put param list in ()
// syntax InvokeSpecialWord ::= "invokespecial"  
//				| "invokestatic"
 syntax InvokeSpecialInstruction ::= "invokespecial" MethodReference Params "@" #Int "exception" ":" Variable	[:prec(79):]

 syntax Instruction ::= NewInstruction
			| GetInstruction
			| PutInstruction
			| PhiInstruction
			| PhiPhiInstruction
			| "return"
			| InvokeSpecialInstruction
			| "noinstruction"


 syntax BBEdge ::= #Id "->" #Id ";"						[:prec(80):]
 
 syntax BlockBody ::= List{Instruction,";"}					[:prec(81):]
// syntax BlockBody ::= Instruction
//			| BlockBody ";" BlockBody 				[:prec(80):]
 syntax Block ::= #Id ":" "{" BlockBody	"}"					[:prec(90):]
// 		| #Id ":" "{" "}"						[:prec(90):]

 syntax TaskUnit ::= BBEdge
		| Block

 syntax Task ::= TaskUnit
		| Task  Task							[:prec(96) gather(E e):]
// syntax Task ::= List{TaskUnit,";"}						[:prec(100):] 

 syntax Program ::= MethodDefinition 
			| "start"
			| "analysis"
			| "done"			
			| Program "+++" Program					[:prec(98) gather(E e):]
 syntax MethodDefinition ::= MethodReference "{" Task "}"			[:prec(97):]
 // syntax ClassBody ::= MethodDefinition
 				// | ClassBody ClassBody	[:prec(98) gather(E e):]

// syntax ClassDefinition ::= TypeReference "{{" ClassBody "}}" [:prec(99):]
// syntax TopTask ::= ClassDefinition
			// | TopTask TopTask								[:prec(100) gather(E e):]

end module


module KWALA
  imports KWALA-SYNTAX
/*@ \section{Semantics}
... */

/*@ \subsection{Configuration}
...*/
 configuration <T color="gray">
		  <method multiplicity="*" color="yellow">
			  <methodName color="red"> none </methodName>
			  <edges color="orange"> .List </edges>
			  <basicBlocks color="yellow">
		  	   <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<k color="white"> noinstruction </k>				
			   </basicBlock>
			  </basicBlocks>
		  </method>
		 @latex("\\kBR")
		<cenvs multiplicity="*"> .Set </cenvs>
		<invocations color="blue">
		 <invocation multiplicity="*"  color="brown">
			<variables color="red" > .Map </variables>
			<body color="white"> 
		 	   <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<k color="white"> noinstruction </k>				
			   </basicBlock>
			</body>
		 </invocation>
		</invocations>
		<nextPointer> 0 </nextPointer>
		<nextObject> 0 </nextObject>
		 @latex("\\kBR")
		<constraints>
		 <pointsTo color="green"> .Map </pointsTo>
		 <copy color="orange"> .Map </copy>
		 <fieldRead color="yellow"> .Map </fieldRead>
		 <fieldWrite color="white"> .Map </fieldWrite>
		</constraints>
		<objects>
			<object multiplicity="*">
		 		<name color="green"> 0 </name>
		 		<fields color="yellow"> .Map </fields>
			</object>
		</objects>
		 <task color="violet"> 
			<ik color="white"> $PGM:K </ik>
			<mname color="white"> "none" </mname>
		 </task>
		</T>


/*@ \subsection{Processing Basic Blocks}
...*/
 rule  T1:TaskUnit T2:Task => T1 ~> T2 
 rule  I1:Instruction ; BBl2:BlockBody => I1 ~> BBl2 
// rule MR1:MethodReference { T2 } => MR1 ~> T2 
 rule Pg1:Program +++ Pg2:Program => Pg1 ~> Pg2

 syntax ListItem ::= "[" #Id "," #Id "]"
 rule <ik> BB1:#Id -> BB2:#Id ; => . ...</ik>
	<mname> MR1 </mname> 
	<method> 
	      <methodName> MR1 </methodName>
	      <edges> . => [BB1,BB2] ...</edges>
	...</method>
 
 rule <ik> BB:#Id : { Bl:BlockBody }  => . ...</ik>
	<mname> MR1 </mname>
	<method>
		<methodName> MR1 </methodName> 
		(. =>  <basicBlock> <blockName> BB </blockName> <k> Bl </k></basicBlock>) 
	...</method>

 rule <ik> BB:#Id : { }  => . ...</ik>
	<mname> MR1 </mname>
	<method> 
		<methodName> MR1 </methodName>
		<basicBlocks> 
			(. =>  <basicBlock> <blockName> BB </blockName> <k> noinstruction </k> </basicBlock>) 
		...</basicBlocks> 		
	...</method>

 rule  <ik> ( MR1:MethodReference { T2 } => T2 ) ...</ik>
	<mname> _ => MR1 </mname> 
	 (. => <method> 
		<methodName> MR1 </methodName> 
		<edges> .List </edges> 
		<basicBlocks> .Bag </basicBlocks>  
	</method>) 
	
rule  <ik> start => . ...</ik>

 rule <ik> . => analysis </ik>
//	<mname> _ => "<" Ap1 "," TN1 "," "main" "(" FP1 ")" "V" ">" </mname>
	<mname> _ => none </mname>
	<method>
		<methodName> <| Ap1:#Id , TN1:TypeName , main [ FP1:FormalParams ] |> </methodName>
//		<methodName> <| Ap1:#Id , TN1:TypeName , Sl1:Selector |> </methodName>
		<basicBlocks> BBls:Bag</basicBlocks>
	...</method> 
	( . => <invocation> <variables> .Map </variables> <body> BBls </body> </invocation>)

/*@ \subsection{Gathering Constraints}
...*/

syntax K ::= "wrappedList" "(" Bag ")"
// syntax MapVals ::= List{#Int,";;;"}

//@ Phi functions

 rule <invocation>... 
	<k>  V1:#Int =phi( P:Params )  =>  V1 = phiphi(P) ...</k>
	<variables> . => v V1 |-> NP  ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>

 rule <invocation>... 
	<k>  V1 =phiphi( V2:#Int, P )  =>  V1 = phiphi(P) ...</k>
	<variables>... v V1 |-> P1:#Int _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<copy>... P2 |-> wrappedList ( <cenvs> ( . => SetItem ( P1 ) ) RestSet:Set </cenvs> ) ...</copy>
	when notBool(P1 in RestSet)

 rule <invocation>... 
	<k>  V1 =phiphi( V2, P )  =>  V1 = phiphi(P) ...</k>
	<variables>... v V1 |-> P1:#Int _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<copy> ( . =>  P2 |-> wrappedList ( <cenvs> SetItem( P1 ) </cenvs> ) ) Rest </copy>
	when notBool(P2 in keys(Rest:Map)) 
	

 rule <invocation>... 
	<k>  V1 =phi( ) =>  . ...</k>
	...</invocation>

//@ Get field
 
 syntax FieldToPointer ::= "(" FieldReference "|>" #Int ")"
 // 
  rule <invocation>... 
  	<k>   V1 = getfield F:FieldReference V2 =>  . ...</k>
  	<variables> ( . => v V1 |-> NP ) _:Map v V2 |-> P2 ...</variables>
  	...</invocation>
  	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
  	<fieldRead> ( . => P2 |-> wrappedList ( <cenvs> SetItem( ( F |> NP ) ) </cenvs> ) ) Rest </fieldRead>
  	when notBool(P2 in keys(Rest)) 
  
  rule <invocation>... 
  	<k>   V1 = getfield F V2 =>  . ...</k>
  	<variables> ( . => v V1 |-> NP ) _:Map v V2 |-> P2 ...</variables>
  	...</invocation>
  	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
  	<fieldRead>... P2 |-> wrappedList( <cenvs> ( . => SetItem( ( F |> NP ) ) ) RestSet </cenvs> ) ...</fieldRead>

//@ Put field 

 rule <invocation>... 
 	<k>  (putfield V1 = V2:#Int F:FieldReference =>  .) ...</k>
 	<variables> ... v V1 |-> P1:#Int  _:Map v V2 |-> P2:#Int ...</variables>
 	...</invocation>
 	<fieldWrite> ( . => P1 |-> wrappedList ( <cenvs> SetItem( ( F |> P2 ) ) </cenvs> ) ) Rest:Map </fieldWrite>
 	<pointsTo>... P1 |->  wrappedList ( <cenvs>... SetItem ( O:#Int) ...</cenvs> ) ...</pointsTo>
 	<object> <name> O </name> <fields> ( . =>  F |-> NP ) ...</fields> </object>
 	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
 	when notBool(P1 in keys(Rest)) 

 rule <invocation>... 
   	<k>   putfield V1 = V2 F =>  . ...</k>
     <variables> ... v V1 |-> P1  _:Map v V2 |-> P2 ...</variables>
     ...</invocation>
     <fieldWrite>... P1 |-> wrappedList ( <cenvs> ( . => SetItem(  ( F |> P2 ) ) ) RestSet </cenvs> ) ...</fieldWrite>
     <pointsTo>... P1 |->  wrappedList ( <cenvs>... SetItem ( O ) ...</cenvs> ) ...</pointsTo>
     <object> <name> O </name> <fields> ( . =>  F |-> NP ) ...</fields> </object>
     <nextPointer> NP => NP +Int 1 </nextPointer>

//@ New instruction

 rule <invocation>... 	
	<k>   V1:#Int = new TR:TypeReference @ _:#Int =>  . ...</k>
	<variables>  ( . => v V1 |-> NP ) ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<nextObject> NO:#Int => NO +Int 1 </nextObject>
	<pointsTo> . => NP |-> wrappedList ( <cenvs> SetItem ( NO ) </cenvs> ) ...</pointsTo>
	<objects>(. => <object> <name> NO </name> <fields> .Map </fields> </object>) ...</objects>

/*@ \subsection{Resolving Constraints}*/

//@ First type of graph: if copy encountered, propagate points-to
rule <copy>... B |->  wrappedList( <cenvs>... SetItem ( A ) ...</cenvs> ) ...</copy>
	<pointsTo>... 
		B |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
		_:Map  
		A |-> wrappedList( <cenvs> ( . => SetItem ( O ) ) OldSet:Set </cenvs> )
	...</pointsTo>
	when notBool(O in OldSet)

rule <copy>... B |->  wrappedList( <cenvs>... SetItem ( A ) ...</cenvs> ) ...</copy>
	<pointsTo> B |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
		RestOfTheWorld:Map  
		( . => A |-> wrappedList( <cenvs> SetItem ( O ) </cenvs> ) )
	</pointsTo>
	when notBool(A in keys(RestOfTheWorld))

//@ Second type of graph: if field-read and points-to encountered, propagate copy
rule <copy>... P1 |->   wrappedList( <cenvs> ( . => SetItem ( A:#Int ) ) OldSet:Set </cenvs> ) ...</copy>
	<pointsTo>... 
		B:#Int |->   wrappedList( <cenvs>... SetItem ( O:#Int ) ...</cenvs> ) 
	...</pointsTo>
	<fieldRead>... 
		B |->  wrappedList( <cenvs>... SetItem(  ( F |> A ) )...</cenvs> ) 
	...</fieldRead>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(A in OldSet)

rule <copy> ( . => P1 |->   wrappedList( <cenvs> SetItem ( A ) </cenvs> ) ) OldMap:Map </copy>
	<pointsTo>... 
		B |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldRead>... 
		B |->  wrappedList( <cenvs>...SetItem(  ( F |> A ) )...</cenvs> ) 
	...</fieldRead>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(P1 in keys(OldMap))

//@ Third type of graph: if field-write and points-to encountered, propagate copy
rule <copy>... B |->   wrappedList( <cenvs> ( . => SetItem ( P1 ) ) OldSet </cenvs> ) ...</copy>
	<pointsTo>... 
		A |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldWrite>... 
		A |->  wrappedList( <cenvs>... SetItem(  ( F |> B ) ) ...</cenvs> ) 
	...</fieldWrite>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(P1 in OldSet)

rule <copy> ( . => B |->   wrappedList( <cenvs> SetItem ( P1 ) </cenvs> ) ) OldMap </copy>
	<pointsTo>... 
		A |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldWrite>... 
		A |->  wrappedList( <cenvs>... SetItem(  ( F |> B ) ) ...</cenvs> ) 
	...</fieldWrite>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(B in keys(OldMap))

end module
