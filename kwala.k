module KWALA-SYNTAX
/*@ \section{Syntax}
...*/
 syntax #Id ::= object
		| main
		| null
	//convert class names to start with lower case or '

 syntax Variable ::= #Int		

 syntax TypeNameBase ::= #Id				
			| #Id "/" TypeNameBase					[:prec(33):]
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
i syntax GetInstruction ::= Variable "=" "getfield" FieldReference Variable 	[:prec(70):]
			| Variable "=" "getstatic" FieldReference		[:prec(70):]
 syntax PutInstruction ::= "putfield" Variable "=" Variable FieldReference	[:prec(70):]
			| "putstatic" Variable FieldReference			[:prec(70):]
 syntax PhiInstruction ::= Variable "=" "phi" "(" Params ")" 			[:prec(70):]
	//put param list in ()

 syntax Instruction ::= NewInstruction
			| GetInstruction
			| PutInstruction
			| PhiInstruction

 syntax BBEdge ::= #Id "->" #Id ";"						[:prec(70):]
 
 syntax BlockBody ::= List{Instruction,";"}					[:prec(80):]
 syntax Block ::= #Id ":" "{" BlockBody	"}"					[:prec(90):]

 syntax TaskUnit ::= BBEdge
		| Block

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
			  <methodName color="red"> main </methodName>
			  <edges color="orange"> .List </edges>
		 	  <basicBlock multiplicity="*" color="brown">
				<blockName color="gray"> null </blockName>
				<block color="white"> .List </block>				
			  </basicBlock>
		  </method>
		 </class>
		 <heapAbstraction color="yellow"> .Map </heapAbstraction>
		 <task color="violet"> 
			<k color="white"> $PGM:K </k>
		 </task>
		</T>


/*@ \subsection{Processing Basic Blocks}
...*/
 rule T1:TaskUnit T2:Task => T1 ~> T2

 syntax ListItem ::= "[" #Id "," #Id "]"
 rule <k> BB1:#Id -> BB2:#Id ; => . ...</k>
      <edges> . => [BB1,BB2] ...</edges>
 
 rule <k> BB:#Id : { Bl:BlockBody }  => . ...</k>
	<method> (. =>  <basicBlock> <blockName> BB </blockName> <block> Bl </block></basicBlock>) ...</method>

/*@ \subsection{Results}
...*/

//  syntax KResult ::= #Int | #Bool

end module
