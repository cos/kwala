import java.io.IOException;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.CancelException;

import sabazios.wala.WalaAnalysis;

public class WALAExporter {
	public static void main(String[] args) {
		WalaAnalysis a = new WalaAnalysis();
		a.addBinaryDependency("particles");
		try {
			a.setup("Lparticles/Particle", "foo()V");
			
			CallGraph cg = a.getCallGraph();
			CGNode entry = cg.getEntrypointNodes().iterator().next();
			System.out.println("\n\n");
			IR ir = entry.getIR();
			for(SSAInstruction i: ir.getInstructions())
				System.out.println(i + ";");
			
			SSACFG cfg = ir.getControlFlowGraph();
			System.out.println(cfg);
		} catch (ClassHierarchyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (CancelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
