package ocl2msfol.visitor;


import java.util.List;
import java.util.Map;
import java.util.Set;

import org.vgu.dm2schema.dm.DataModel;

import oclparser.expressions.AssociationClassCallExp;
import oclparser.expressions.BooleanLiteralExp;
import oclparser.expressions.Expression;
import oclparser.expressions.IntegerLiteralExp;
import oclparser.expressions.IteratorExp;
import oclparser.expressions.IteratorKind;
import oclparser.expressions.LiteralExp;
import oclparser.expressions.OclExp;
import oclparser.expressions.OperationCallExp;
import oclparser.expressions.PropertyCallExp;
import oclparser.expressions.StringLiteralExp;
import oclparser.expressions.Variable;
import oclparser.expressions.VariableExp;
import oclparser.utils.VariableUtils;

public class O2F_DefCVisitor extends OCL2MSFOLVisitor {

	public O2F_DefCVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
		this.setDataModel(dm);
		this.setAdhocContextualSet(adhocContextualSet);
		this.defC = defC;
	}

	@Override
	public void visit(Expression exp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(IteratorExp iteratorExp) {
		switch (IteratorKind.valueOf(iteratorExp.getKind())) {
		case collect:
			break;
		case select:
			// First line
			String newDefCName = "TEMP" + String.valueOf(defC.size());
			List<Variable> fVars = VariableUtils.FVars(iteratorExp);
			if (fVars.isEmpty()) {
			String arguments = "Classifier";
			DefC defCElement = new DefC();
			defCElement.setNameDefinition(String.format("%s (%s) Bool", newDefCName, arguments));
			defCElement.setNameApplied(String.format("(%s %s)", newDefCName, "%s"));
			defC.put(iteratorExp, defCElement);
			String var = iteratorExp.getIterator().getName();
			String type = "Classifier";
			String template = Template.Def_c.select_1;
			String firstArgument = app(defCElement.getNameApplied(), fVars, var);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			
			Expression sourceExp = (OclExp) iteratorExp.getSource();
			List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			String secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			Expression bodyExp = iteratorExp.getBody();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(trueVisitor);
			String thirdArgument = trueVisitor.getFOLFormulae();

			defCElement.setAssertion(String.format(template, var, type, firstArgument, secondArgument, thirdArgument));
			} else {
//				String template = Template.Def_c.select_0;
			}
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(OperationCallExp operationCallExp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(LiteralExp literalExp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(StringLiteralExp stringLiteralExp) {
		// StringLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		// BooleanLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		// IntegerLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		// PropertyCallExp does not have a Def_c definition
	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		// TODO: Implement Def_c definition for association-end expressions of case many-to-many
	}

	@Override
	public void visit(VariableExp variableExp) {
		// VariableExp does not have a Def_c definition
	}

}
