import java.io.IOException;
import java.util.Iterator;

import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSACFG.BasicBlock;
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
			SSACFG cfg = ir.getControlFlowGraph();
			for(ISSABasicBlock bb: cfg) {
				System.out.println("BB"+bb.getNumber()+": {");
				for(SSAInstruction i: bb)
					System.out.println(i + ";");
				System.out.println("}");
			}
			System.out.println(entry.getMethod().getClass());
			for(ISSABasicBlock bb: cfg) 
			{
				Iterator<ISSABasicBlock> succNodes = cfg.getSuccNodes(bb);
				while (succNodes.hasNext()) {
					ISSABasicBlock sbb = (ISSABasicBlock) succNodes
							.next();					
					System.out.println("BB"+bb.getNumber()+"->"+"BB"+sbb.getNumber());
				}
			}
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
