package ocl2msfol.visitor;
/**************************************************************************
Copyright 2020 ngpbh
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/


import java.util.List;
import java.util.Map;
import java.util.Set;

import dmparser.models.DataModel;
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
import oclparser.expressions.TypeExp;
import oclparser.expressions.Variable;
import oclparser.expressions.VariableExp;
import oclparser.utils.VariableUtils;

public class O2F_FalseVisitor extends OCL2MSFOLVisitor {

    public O2F_FalseVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
        case any:
            break;
        case asBag:
            break;
        case asOrderedSet:
            break;
        case asSequence:
            break;
        case asSet:
            break;
        case at:
            break;
        case collect:
            break;
        case count:
            break;
        case excludes:
            break;
        case excludesAll:
            break;
        case excluding:
            break;
        case exists:
            String template = Template.False.exists;

            String var = iteratorExp.getIterator().getName();
            String type = "Classifier";

            OclExp sourceExp = (OclExp) iteratorExp.getSource();
            List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            sourceExp.accept(evalVisitor);
            String firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            Expression bodyExp = iteratorExp.getBody();
            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            bodyExp.accept(falseVisitor);
            String secondArgument = falseVisitor.getFOLFormulae();

            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            sourceExp.accept(invalVisitor);
            String thirdArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument, thirdArgument));
            break;
        case first:
            break;
        case flatten:
            break;
        case forAll:
            template = Template.False.forAll;

            var = iteratorExp.getIterator().getName();
            type = iteratorExp.getSource().getType().getReferredType();

            sourceExp = (OclExp) iteratorExp.getSource();
            fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            sourceExp.accept(evalVisitor);
            firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            bodyExp = iteratorExp.getBody();
            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            bodyExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            sourceExp.accept(invalVisitor);
            thirdArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument, thirdArgument));
            break;
        case includes:
        	template = Template.False.includes;
			// TODO: Investigate what is the meaning of this?
			// This can be duplicated. Temporary put it as i.
			type = "Classifier";

			sourceExp = (OclExp) iteratorExp.getSource();

			Variable temp = new Variable("temp", sourceExp.getType().getElementType());

			fVarsSrc = VariableUtils.FVars(sourceExp);
//			fVarsSrc = VariableUtils.getComplement(adhocContextualSet.stream().collect(Collectors.toList()), fVarsSrc);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);

			if (iteratorExp.getSource() instanceof AssociationClassCallExp) {
				firstArgument = special_app(evalVisitor.getFOLFormulae(), fVarsSrc, temp);
			} else {
				firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, temp.getName());
			}

			bodyExp = iteratorExp.getBody();
			fVarsSrc = VariableUtils.FVars(bodyExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(evalVisitor);
			String secondArgumentTemplate = "(not (= %s %s))";
			String secondsecondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, null);
			secondArgument = String.format(secondArgumentTemplate, temp.getName(), secondsecondArgument);

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			thirdArgument = invalVisitor.getFOLFormulae();

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(invalVisitor);
			String forthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, temp.getName(), type, firstArgument, secondArgument,
					thirdArgument, forthArgument));
            break;
        case includesAll:
            break;
        case including:
            break;
        case indexOf:
            break;
        case isEmpty:
            template = Template.False.isEmpty;

            Expression exp = iteratorExp.getSource();
            var = "x";
            type = iteratorExp.getSource().getType().getElementType().getReferredType();

            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            List<Variable> fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, "Classifier",
                firstArgument, secondArgument));
            break;
        case isUnique:
            break;
        case last:
            break;
        case notEmpty:
            template = Template.False.notEmpty;

            exp = iteratorExp.getSource();
            var = "x";
            type = iteratorExp.getSource().getType().getElementType().getReferredType();

            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, "Classifier",
                firstArgument, secondArgument));
            break;
        case one:
            break;
        case reject:
            break;
        case select:
            break;
        case size:
            break;
        case sortedBy:
            break;
        case sum:
            break;
        case union:
            break;
        default:
            break;
        }
    }

    private String special_app(String folFormulae, List<Variable> fVarsSrc, Variable var) {
    	if (fVarsSrc.size() != 1) {
			System.out.println("There is an exception here O2F_True (243) !");
			return null;
		} else {
			Variable one = fVarsSrc.get(0);
			return folFormulae.replace(one.getType().getReferredType(), one.getName())
					.replace(var.getType().getReferredType(), var.getName());
		}
	}

	@Override
    public void visit(OperationCallExp operationCallExp) {
        switch (operationCallExp.getReferredOperation().getName()) {
        case "allInstances":
            break;
        case "oclIsUndefined":
            String template = Template.False.oclIsUndefined;
            Expression exp = operationCallExp.getSource();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template,
                nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
            break;
        case "oclIsInvalid":
            template = Template.False.oclIsInvalid;
            exp = operationCallExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case "oclIsKindOf":
            template = Template.False.oclIsKindOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            Expression argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) operationCallExp.getArguments()
                    .get(0)).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            }
            break;
        case "oclIsTypeOf":
            template = Template.False.oclIsTypeOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) operationCallExp.getArguments()
                    .get(0)).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            }
            break;
        case "oclAsType":
            break;
        case "=":
            template = Template.False.equality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            String firstArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            String secondArgument = evalVisitor.getFOLFormulae();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            String thirdArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            String forthArgument = nullVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            String fifthArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            String sixthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "<>":
            template = Template.False.inequality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            secondArgument = nullVisitor.getFOLFormulae();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            exp.accept(evalVisitor);
            thirdArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            forthArgument = evalVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            fifthArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            sixthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "<=":
        case ">=":
        case ">":
        case "<":
        case "and":
            template = Template.False.and;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            exp.accept(falseVisitor);
            firstArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "or":
            template = Template.False.or;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            exp.accept(falseVisitor);
            firstArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "not":
            template = Template.False.not;
            exp = operationCallExp.getArguments().get(0);
            trueVisitor = new O2F_TrueVisitor(dm,adhocContextualSet,defC);
            exp.accept(trueVisitor);
            this.setFOLFormulae(String.format(template, trueVisitor.getFOLFormulae()));
            break;
        case "implies":
            template = Template.False.implies;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            trueVisitor = new O2F_TrueVisitor(dm,adhocContextualSet,defC);
            exp.accept(trueVisitor);
            firstArgument = trueVisitor.getFOLFormulae();
            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "size":
            break;
        case "isUnique":
            break;
        case "flatten":
            break;
        default:
            break;
        }
    }

    @Override
    public void visit(LiteralExp literalExp) {
    	// We don't implement concrete detail for abstract objects.
    }

    @Override
    public void visit(StringLiteralExp stringLiteralExp) {
        // TODO Implement StringLiteralExp for O2Ffalse
    }

    @Override
    public void visit(BooleanLiteralExp booleanLiteralExp) {
    	if (booleanLiteralExp.getValue()) {
    		this.setFOLFormulae("false");
    	} else {
    		this.setFOLFormulae("true");
    	}
    }

    @Override
    public void visit(IntegerLiteralExp integerLiteralExp) {
    	// TODO Implement IntegerLiteralExp for O2Ffalse
    }

    @Override
    public void visit(PropertyCallExp propertyCallExp) {
    	// TODO Implement PropertyCallExp for O2Ffalse
    }

    @Override
    public void visit(AssociationClassCallExp associationClassCallExp) {
    	// TODO Implement AssociationClassCallExp for O2Ffalse
    }

    @Override
    public void visit(VariableExp variableExp) {
    	// TODO Implement VariableExp for O2Ffalse
    }
}
