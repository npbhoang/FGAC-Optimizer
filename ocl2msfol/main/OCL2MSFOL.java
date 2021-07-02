package main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import dmparser.models.DataModel;
import ocl2msfol.visitor.DefC;
import ocl2msfol.visitor.LogicValue;
import ocl2msfol.visitor.O2F_FalseVisitor;
import ocl2msfol.visitor.O2F_InvalidVisitor;
import ocl2msfol.visitor.O2F_NullVisitor;
import ocl2msfol.visitor.O2F_TrueVisitor;
import ocl2msfol.visitor.OCL2MSFOLVisitor;
import oclparser.expressions.Expression;
import oclparser.expressions.OclExp;
import oclparser.expressions.Variable;
import oclparser.simple.OCLParser;
import oclparser.types.Type;

public class OCL2MSFOL {

	private static DataModel dm;
	private static OclExp exp;
	private static LogicValue lvalue;
	private static Set<Variable> adhocContextualSet = new HashSet<>();
	private static Map<Expression, DefC> defC = new HashMap<Expression, DefC>();

	public static void setExpression(String string) {
		OCLParser OCLParser = new OCLParser();
		adhocContextualSet.forEach(OCLParser::putAdhocContextualSet);
		Expression exp_ = OCLParser.parse(string, dm);
		if (exp_ instanceof OclExp)
			exp = (OclExp) exp_;
	}

	public static void putAdhocContextualSet(String vName, String vType) {
		Variable v = new Variable(vName, new Type(vType));
		adhocContextualSet.remove(v);
		adhocContextualSet.add(v);
	}

	public static void setDataModel(DataModel dm_) {
		dm = dm_;
	}

	public static List<String> map2msfol(boolean negation) {
		OCL2MSFOLVisitor visitor;

		List<String> formulas = new ArrayList<>();
		for (Variable v : adhocContextualSet) {
			formulas.add(String.format("(declare-const %s %s)", v.getName(), "Classifier"));
			formulas.add(String.format("(assert (%s %s))", v.getType(), v.getName()));
		}

		defC = new HashMap<Expression, DefC>();

		if (lvalue == LogicValue.INVALID) {
			visitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.FALSE) {
			visitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.NULL) {
			visitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
		} else {
			visitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
		}
		exp.accept(visitor);

		for (DefC d : defC.values()) {
			formulas.add(String.format("(declare-fun %s)", d.getNameDefinition()));
			formulas.add(String.format("(assert %s)", d.getAssertion()));
		}

//		formulas.add(visitor.getFOLFormulae());
		//TODO: Temporary change
		if (negation) {
			formulas.add(String.format("(assert (not %s))", visitor.getFOLFormulae()));
		} else {
			formulas.add(String.format("(assert %s)", visitor.getFOLFormulae()));
		}
		
		return formulas;
	}

	public static LogicValue getLvalue() {
		return lvalue;
	}

	public static void setLvalue(LogicValue lvalue) {
		OCL2MSFOL.lvalue = lvalue;
	}

	public static void setExpression(OclExp exp_) {
		exp = exp_;
	}
}
