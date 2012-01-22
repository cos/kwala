module KWALA-SYNTAX
/*@ \section{Syntax}
...*/
 syntax #Id ::= object
		| null
	//convert class names to start with lower case or '

 syntax Variable ::= #Int		
 syntax VariableName ::= "v" #Int						[:prec(20):]

 syntax Selector ::= "<" "init" ">" "(" ")" "V"					[:prec(40):]
 syntax TypeName ::= #Id				
			| #Id "/" TypeName					[:prec(33):]
// syntax TypeName ::= "L" TypeNameBase						[:prec(33):]
//			| "A" TypeNameBase
	//put A instead of [
 syntax TypeReference ::= "<" #Id "," TypeName ">"				[:prec(40):]
 syntax FieldReference ::= "<" #Id "," TypeName "," #Id "," TypeReference ">"	[:prec(50):]
 syntax MethodReference ::= "<" #Id "," TypeName "," Selector ">"		[:prec(50):]

 syntax Params ::= List{Variable,","}
	//put , instead of space
 syntax NewInstructionBase ::= Variable "=" "new" TypeReference "@" #Int 	[:prec(70):]
 syntax NewInstruction ::= NewInstructionBase 					[:prec(70):]
			| NewInstructionBase "(" Params ")" 			[:prec(70):]
 syntax GetInstruction ::= Variable "=" "getfield" FieldReference Variable 	[:prec(70):]
// meaning: Var1 = gf F Var2 <=> Var1 = Var2 . F
			| Variable "=" "getstatic" FieldReference		[:prec(70):]
 syntax PutInstruction ::= "putfield" Variable "=" Variable FieldReference	[:prec(70):]
// meaning: pf Var1 = Var2 F <=> Var1 . F = Var2
			| "putstatic" Variable FieldReference			[:prec(70):]
 syntax PhiInstruction ::= Variable "=" "phi" "(" Params ")" 			[:prec(70):]
 syntax PhiPhiInstruction ::= Variable "=" "phiphi" "(" Params ")" 		[:prec(70):]
	//put param list in ()
// syntax InvokeSpecialWord ::= "invokespecial"  
//				| "invokestatic"
 syntax InvokeSpecialInstruction ::= "invokespecial" MethodReference Params "@" #Int "exception" ":" Variable	[:prec(70):]

 syntax Instruction ::= NewInstruction
			| GetInstruction
			| PutInstruction
			| PhiInstruction
			| PhiPhiInstruction
			| "return"
			| InvokeSpecialInstruction
			| "noinstruction"
			| "main"


 syntax BBEdge ::= #Id "->" #Id ";"						[:prec(70):]
 
// syntax BlockBody ::= List{Instruction,";"}					[:prec(80):]
 syntax BlockBody ::= Instruction
			| BlockBody ";" BlockBody 				[:prec(80):]
 syntax Block ::= #Id ":" "{" BlockBody	"}"					[:prec(90):]
 		| #Id ":" "{" "}"						[:prec(90):]

 syntax TaskUnit ::= BBEdge
		| Block
		| "start"
		| "analysis"
		| "done"

 syntax Task ::= TaskUnit
		| Task  Task							[:prec(100):]
// syntax Task ::= List{TaskUnit,";"}						[:prec(100):] 

end module


module KWALA
  imports KWALA-SYNTAX
/*@ \section{Semantics}
... */

/*@ \subsection{Configuration}
...*/
//configuration <T color="gray">
//		<k color="red"> $PGM:K </k>
//		</T>

 configuration <T color="gray">
		<class multiplicity="*" color="white"> 	
		  <className color="cyan"> object </className>
		  <method multiplicity="*" color="yellow">
			  <methodName color="red"> null </methodName>
			  <edges color="orange"> .List </edges>
			  <basicBlocks color="yellow">
		  	   <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<block color="white"> noinstruction </block>				
			   </basicBlock>
			  </basicBlocks>
		  </method>
		 </class>
		<cenvs multiplicity="*"> .Set </cenvs>
		<objects color="LightBlue"> 
		 <object multiplicity="*">
			<name> 0 </name>
			<fields color="red"> .Map </fields>
		 </object>
		</objects>
		<invocations color="blue">
		 <invocation multiplicity="*"  color="brown">
			<variables color="red" > .Map </variables>
			<k color="white"> 
		 	   <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<block color="white"> noinstruction </block>				
			   </basicBlock>
			</k>
		 </invocation>
		</invocations>
		<nextPointer> 0 </nextPointer>
		<nextObject> 0 </nextObject>
		<constraints>
		 <pointsTo color="green"> .Map </pointsTo>
		 <copy color="orange"> .Map </copy>
		 <fieldRead color="yellow"> .Map </fieldRead>
		 <fieldWrite color="white"> .Map </fieldWrite>
		</constraints>
		<object multiplicity="*">
		 <name color="green"> 0 </name>
		 <fields color="yellow"> .Map </fields>
		</object>
		 <task color="violet"> 
			<ik color="white"> $PGM:K </ik>
		 </task>
		</T>


/*@ \subsection{Processing Basic Blocks}
...*/
 rule T1:TaskUnit T2:Task => T1 ~> T2
 rule I1:Instruction ; BBl2:BlockBody => I1 ~> BBl2

 syntax ListItem ::= "[" #Id "," #Id "]"
 rule <ik> BB1:#Id -> BB2:#Id ; => . ...</ik>
      <edges> . => [BB1,BB2] ...</edges>
 
 rule <ik> BB:#Id : { Bl:BlockBody }  => . ...</ik>
	<method> (. =>  <basicBlock> <blockName> BB </blockName> <block> Bl </block></basicBlock>) ...</method>
 rule <ik> BB:#Id : { }  => . ...</ik>
	<method> (. =>  <basicBlock> <blockName> BB </blockName> <block> noinstruction </block></basicBlock>) ...</method>

 rule <ik> start => . ...</ik>
	( . => <class> <className> "blah" </className> <method> <methodName> "blahah" </methodName> <edges> .List </edges> 
	 <basicBlocks> .Bag </basicBlocks>
	 </method> </class>)

 rule <ik> . => analysis </ik>
	<basicBlocks> BBls:Bag </basicBlocks>
	( . => <invocation> <variables> .Map </variables> <k> BBls </k> </invocation>)

/*@ \subsection{Gathering Constraints}
...*/

//@ Phi functions

 rule <invocation>... 
	<block>  V1 =phi( P:Params )  =>  V1 = phiphi(P) ...</block>
	<variables> . => v V1 |-> NP  ...</variables>
	...</invocation>
	<nextPointer> NP => NP +Int 1 </nextPointer>

 rule <invocation>... 
	<block>  V1 =phiphi( V2, P )  =>  V1 = phiphi(P) ...</block>
	<variables>... v V1 |-> P1:#Int _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<copy>... P2 |-> wrappedList ( <cenvs> ( . => SetItem ( P1 ) ) RestSet:Set </cenvs> ) ...</copy>
	when notBool(P1 in RestSet)

 rule <invocation>... 
	<block>  V1 =phiphi( V2, P )  =>  V1 = phiphi(P) ...</block>
	<variables>... v V1 |-> P1:#Int _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<copy> ( . =>  P2 |-> wrappedList ( <cenvs> SetItem( P1 ) </cenvs> ) ) Rest </copy>
	when notBool(P2 in keys(Rest)) 
	

 rule <invocation>... 
	<block>  V1 =phi( ) =>  . ...</block>
	...</invocation>

//@ Get field
 
 syntax SetItem ::= "(" FieldReference "|>" #Int ")"

 rule <invocation>... 
	<block>   V1 = getfield F:FieldReference V2 =>  . ...</block>
	<variables> ( . => v V1 |-> NP ) _:Map v V2 |-> P2 ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<fieldRead> ( . => P2 |-> wrappedList ( <cenvs> ( F |> NP ) </cenvs> ) ) Rest </fieldRead>
	when notBool(P2 in keys(Rest)) 

 rule <invocation>... 
	<block>   V1 = getfield F V2 =>  . ...</block>
	<variables> ( . => v V1 |-> NP ) _:Map v V2 |-> P2 ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<fieldRead>... P2 |-> wrappedList( <cenvs> ( . => ( F |> NP ) ) RestSet </cenvs> ) ...</fieldRead>

//@ Put field 

 rule <invocation>... 
	<block>   putfield V1 = V2:#Int F =>  . ...</block>
	<variables> ... v V1 |-> P1:#Int  _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<fieldWrite> ( . => P1 |-> wrappedList ( <cenvs> ( F |> P2 ) </cenvs> ) ) Rest:Map </fieldWrite>
	<pointsTo>... P1 |->  wrappedList ( <cenvs>... SetItem ( O ) ...</cenvs> ) ...</pointsTo>
	<object> <name> O </name> <fields> ( . =>  F |-> NP ) ...</fields> </object>
	<nextPointer> NP => NP +Int 1 </nextPointer>
	when notBool(P1 in keys(Rest)) 

 rule <invocation>... 
	<block>   putfield V1 = V2 F =>  . ...</block>
	<variables> ... v V1 |-> P1  _:Map v V2 |-> P2 ...</variables>
	...</invocation>
	<fieldWrite>... P1 |-> wrappedList ( <cenvs> ( . => ( F |> P2 ) ) RestSet </cenvs> ) ...</fieldWrite>
	<pointsTo>... P1 |->  wrappedList ( <cenvs>... SetItem ( O ) ...</cenvs> ) ...</pointsTo>
	<object> <name> O </name> <fields> ( . =>  F |-> NP ) ...</fields> </object>
	<nextPointer> NP => NP +Int 1 </nextPointer>

//@ New instruction
 syntax K ::= "wrappedList" "(" Bag ")"
// syntax MapVals ::= List{#Int,";;;"}

 rule <invocation>... 	
	<block>   V1:#Int = new TR:TypeReference @ _:#Int =>  . ...</block>
	<variables>  ( . => v V1 |-> NP ) ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<nextObject> NO:#Int => NO +Int 1 </nextObject>
	<pointsTo> . => NP |-> wrappedList ( <cenvs> SetItem ( NO ) </cenvs> ) ...</pointsTo>
	(. => <object> <name> NO </name> <fields> .Map </fields> </object>)

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
		B |->  wrappedList( <cenvs>... ( F |> A ) ...</cenvs> ) 
	...</fieldRead>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(A in OldSet)

rule <copy> ( . => P1 |->   wrappedList( <cenvs> SetItem ( A ) </cenvs> ) ) OldMap:Map </copy>
	<pointsTo>... 
		B |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldRead>... 
		B |->  wrappedList( <cenvs>... ( F |> A ) ...</cenvs> ) 
	...</fieldRead>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(P1 in keys(OldMap))

//@ Third type of graph: if field-write and points-to encountered, propagate copy
rule <copy>... B |->   wrappedList( <cenvs> ( . => SetItem ( P1 ) ) OldSet </cenvs> ) ...</copy>
	<pointsTo>... 
		A |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldWrite>... 
		A |->  wrappedList( <cenvs>... ( F |> B ) ...</cenvs> ) 
	...</fieldWrite>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(P1 in OldSet)

rule <copy> ( . => B |->   wrappedList( <cenvs> SetItem ( P1 ) </cenvs> ) ) OldMap </copy>
	<pointsTo>... 
		A |->   wrappedList( <cenvs>... SetItem ( O ) ...</cenvs> ) 
	...</pointsTo>
	<fieldWrite>... 
		A |->  wrappedList( <cenvs>... ( F |> B ) ...</cenvs> ) 
	...</fieldWrite>
	<object> <name> O </name> <fields>... F |-> P1 ...</fields> </object>
	when notBool(B in keys(OldMap))

end module
