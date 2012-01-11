import java.io.IOException;
import java.util.Collection;
import java.util.Iterator;

import sabazios.wala.ScopeBuilder;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IClassLoader;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ssa.DefaultIRFactory;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.IRFactory;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.types.ClassLoaderReference;

public class WALAExporter {
	private static IRFactory<IMethod> irFactory;

	public static void main(String[] args) {
		ScopeBuilder sb = new ScopeBuilder();
		sb.addBinaryDependency("particles");
		try {
			AnalysisScope scope = sb.getScope();
			ClassHierarchy cha = ClassHierarchy.make(scope);

			IClassLoader appLoader = cha
					.getLoader(ClassLoaderReference.Application);
			Iterator<IClass> iterateAllClasses = appLoader.iterateAllClasses();

			while (iterateAllClasses.hasNext()) {
				IClass iClass = (IClass) iterateAllClasses.next();
				System.out.println(iClass);
				Collection<IMethod> declaredMethods = iClass
						.getDeclaredMethods();
				for (IMethod m : declaredMethods) {
					System.out.println(m);
					irFactory = new DefaultIRFactory();
					outputMethod(m);
				}
			}
		} catch (ClassHierarchyException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalArgumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private static void outputMethod(IMethod m) {
		IR ir = irFactory.makeIR(m, null,
				SSAOptions.defaultOptions());
		SSACFG cfg = ir.getControlFlowGraph();
		for (ISSABasicBlock bb : cfg) {
			System.out.println("BB" + bb.getNumber() + ": {");
			for (SSAInstruction i : bb)
				System.out.println(i + ";");
			System.out.println("}");
		}
		for (ISSABasicBlock bb : cfg) {
			Iterator<ISSABasicBlock> succNodes = cfg
					.getSuccNodes(bb);
			while (succNodes.hasNext()) {
				ISSABasicBlock sbb = (ISSABasicBlock) succNodes
						.next();
				System.out.println("BB" + bb.getNumber() + "->"
						+ "BB" + sbb.getNumber() + ";");
			}
		}
	}
}
