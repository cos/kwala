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
import com.ibm.wala.types.Descriptor;
import com.ibm.wala.types.Selector;
import com.ibm.wala.types.TypeName;

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

			StringBuffer output = new StringBuffer();

			while (iterateAllClasses.hasNext()) {
				IClass iClass = (IClass) iterateAllClasses.next();
				Collection<IMethod> declaredMethods = iClass
						.getDeclaredMethods();
				for (IMethod m : declaredMethods) {
					Selector selector = m.getSelector();
					Descriptor descriptor = selector.getDescriptor();
					String descriptorOutput = "";
					if (descriptor.getNumberOfParameters() > 0) {
						for (TypeName typeName : descriptor.getParameters()) {
							descriptorOutput += typeName.toString() + ",";
						}
						descriptorOutput = descriptorOutput
								.substring(0,descriptorOutput.length() - 1);
					}
					descriptorOutput = "(" + descriptorOutput + ")" + descriptor.getReturnType();
					String selectorOutput = selector.getName().toString()
							+ descriptorOutput;
					String mOutput = "< "
							+ m.getDeclaringClass().getClassLoader().getName()
							+ ", " + m.getDeclaringClass().getName() + ", "
							+ selectorOutput + " >";
					output.append(mOutput + " { \n");
					irFactory = new DefaultIRFactory();

					outputMethod(output, m);
					output.append("} andherecomesanothermethod \n");
				}
			}

			output.delete(
					output.length() - "andherecomesanothermethod".length() - 2,
					output.length() - 1);
			String theOutput = output.toString();
			theOutput = theOutput.replace('[', 'A');
			theOutput = theOutput.replace("String", "SString");
			System.out.println(theOutput);
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

	private static void outputMethod(StringBuffer output, IMethod m) {
		IR ir = irFactory.makeIR(m, null, SSAOptions.defaultOptions());
		SSACFG cfg = ir.getControlFlowGraph();
		for (ISSABasicBlock bb : cfg) {
			output.append("\tBB" + bb.getNumber() + ": { \n");
			for (SSAInstruction i : bb)
				output.append("\t" + i + ";\n");
			if (output.charAt(output.length() - 2) == ';')
				output.deleteCharAt(output.length() - 2);
			output.append("\t}\n");
		}
		for (ISSABasicBlock bb : cfg) {
			Iterator<ISSABasicBlock> succNodes = cfg.getSuccNodes(bb);
			while (succNodes.hasNext()) {
				ISSABasicBlock sbb = (ISSABasicBlock) succNodes.next();
				output.append("\tBB" + bb.getNumber() + "->" + "BB"
						+ sbb.getNumber() + ";\n");
			}
		}
	}
}
