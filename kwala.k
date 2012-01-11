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
 syntax TypeReference ::= "<" #Id "," TypeName ">"				[:prec(41):]
 syntax FieldReference ::= "<" #Id "," TypeName "," #Id "," TypeReference ">"	[:prec(50):]
 syntax MethodReference ::= "<" #Id "," TypeName "," Selector ">"		[:prec(51):]

 syntax Params ::= List{Variable,","}
	//put , instead of space
 syntax NewInstructionBase ::= Variable "=" "new" TypeReference "@" #Int 	[:prec(70):]
 syntax NewInstruction ::= NewInstructionBase 					[:prec(71):]
			| NewInstructionBase "(" Params ")" 			[:prec(72):]
 syntax GetInstruction ::= Variable "=" "getfield" FieldReference Variable 	[:prec(73):]
// meaning: Var1 = gf F Var2 <=> Var1 = Var2 . F
			| Variable "=" "getstatic" FieldReference		[:prec(74):]
 syntax PutInstruction ::= "putfield" Variable "=" Variable FieldReference	[:prec(75):]
// meaning: pf Var1 = Var2 F <=> Var1 . F = Var2
			| "putstatic" Variable FieldReference			[:prec(76):]
 syntax PhiInstruction ::= Variable "=" "phi" "(" Params ")" 			[:prec(77):]
 syntax PhiPhiInstruction ::= Variable "=" "phiphi" "(" Params ")" 		[:prec(78):]
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


 syntax BBEdge ::= #Id "->" #Id ";"						[:prec(79):]
 
 syntax BlockBody ::= List{Instruction,";"}					[:prec(80):]


 syntax Block ::= #Id ":" "{" BlockBody	"}"					[:prec(90):]


 syntax TaskUnit ::= BBEdge
		| Block
		| "start"
		| "analysis"

 syntax Task ::= TaskUnit
		| Task Task							[:prec(100) gather(E e):]


end module


module KWALA
  imports KWALA-SYNTAX
/*@ \section{Semantics}
... */

/*@ \subsection{Configuration}
...*/




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

		<invocations color="blue">
		 <invocation multiplicity="*"  color="brown">
			<variables color="red" > .Map </variables>
			<k color="white"> 
			  <basicBlocks color="yellow">
		 	   <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<block color="white"> noinstruction </block>				
			   </basicBlock>
			  </basicBlocks>
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
// rule I1:Instruction ; I2:Instruction ; BBl2:BlockBody => I1 ~> I2 ~> BBl2
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
	( . => <invocation> <variables> .Map </variables> <k> <basicBlocks> BBls </basicBlocks> </k> </invocation>)

/*@ \subsection{Gathering Constraints}
...*/

 syntax RelElement ::=  "(" FieldReference "|>" #Int ")"
	| "(|" #Int "|)"
 syntax RelList ::= List{RelElement,","}
 syntax K ::= RelList

//@ Phi functions

 rule <invocation>... 
	<block>  V1:#Int =phi( P:Params )  =>  V1 = phiphi(P) ...</block>
	<variables> . => v V1 |-> NP  ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<copy> . => NP |-> .RelList ... </copy>

 rule <invocation>... 
	<block>  V1 =phiphi( V2:#Int, P )  =>  V1 = phiphi(P) ...</block>
	<variables>... v V1 |-> P1:#Int _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<copy>... P1 |-> ( RL1:RelList => (| P2 |),RL1 ) ...</copy>


 rule <invocation>... 
	<block>  V1 =phi( ) =>  . ...</block>
	...</invocation>


//@ Get field

 rule <invocation>... 
	<block>   V1:#Int = getfield F:FieldReference V2:#Int =>  . ...</block>
	<variables> ( . => v V1 |-> NP:#Int ) _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<fieldWrite> ( . => P2 |-> ( F |> NP ),.RelList ) ... </fieldWrite>

//@ Put field 

 rule <invocation>... 
	<block>   putfield V1:#Int = V2:#Int F:FieldReference =>  . ...</block>
	<variables> ... v V1 |-> P1:#Int  _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<fieldRead> ( . => P1 |-> ( F |> P2 ),.RelList ) Rest:Map </fieldRead>
	when notBool(P1 in keys(Rest))

 rule <invocation>... 
	<block>   putfield V1:#Int = V2:#Int F:FieldReference =>  . ...</block>
	<variables> ... v V1 |-> P1:#Int  _:Map v V2 |-> P2:#Int ...</variables>
	...</invocation>
	<fieldRead>... P1 |-> ( RL1 => ( F |> P2 ),RL1 ) ...</fieldRead>


//@ New instruction

 rule <invocation>... 
	<block>   V1 = new TR:TypeReference @ _:#Int =>  . ...</block>
	<variables>  ( . => v V1 |-> NP ) ...</variables>
	...</invocation>
	<nextPointer> NP:#Int => NP +Int 1 </nextPointer>
	<nextObject> NO:#Int => NO +Int 1 </nextObject>
	<pointsTo> ( . => NP |-> ( (| NO |),.RelList ) ) ...</pointsTo>
	(. => <object> <name> NO </name> <fields> .Map </fields> </object>)

end module





