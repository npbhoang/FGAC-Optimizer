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


import java.util.Map;
import java.util.Set;

import org.vgu.dm2schema.dm.DataModel;

import com.vgu.se.jocl.expressions.AssociationClassCallExp;
import com.vgu.se.jocl.expressions.BooleanLiteralExp;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.IntegerLiteralExp;
import com.vgu.se.jocl.expressions.IteratorExp;
import com.vgu.se.jocl.expressions.IteratorKind;
import com.vgu.se.jocl.expressions.LiteralExp;
import com.vgu.se.jocl.expressions.M2OAssociationClassCallExp;
import com.vgu.se.jocl.expressions.O2OAssociationClassCallExp;
import com.vgu.se.jocl.expressions.OperationCallExp;
import com.vgu.se.jocl.expressions.PropertyCallExp;
import com.vgu.se.jocl.expressions.StringLiteralExp;
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.expressions.VariableExp;

public class O2F_InvalidVisitor extends OCL2MSFOLVisitor {

    public O2F_InvalidVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
            break;
        case first:
            break;
        case flatten:
            break;
        case forAll:
            break;
        case includes:
            break;
        case includesAll:
            break;
        case including:
            break;
        case indexOf:
            break;
        case isEmpty:
            String template = Template.Invalid.isEmpty;
            Expression exp = iteratorExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case isUnique:
            break;
        case last:
            break;
        case notEmpty:
            template = Template.Invalid.notEmpty;
            exp = iteratorExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case one:
            break;
        case reject:
            break;
        case select:
        	template = Template.Invalid.select;
            exp = iteratorExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
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

    @Override
    public void visit(OperationCallExp operationCallExp) {
        switch (operationCallExp.getReferredOperation().getName()) {
        case "allInstances":
            String template = Template.Invalid.allInstances;
            this.setFOLFormulae(template);
            break;
        case "oclIsUndefined":
            template = Template.Invalid.oclIsUndefined;
            this.setFOLFormulae(template);
            break;
        case "oclIsInvalid":
            template = Template.Invalid.oclIsInvalid;
            this.setFOLFormulae(template);
            break;
        case "oclIsKindOf":
            template = Template.Invalid.oclIsKindOf;
            this.setFOLFormulae(template);
            break;
        case "oclIsTypeOf":
            template = Template.Invalid.oclIsTypeOf;
            this.setFOLFormulae(template);
            break;
        case "oclAsType":
            break;
        case "=":
            template = Template.Invalid.equality;

            Expression exp = operationCallExp.getSource();
            Expression argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            String firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            String secondArgument = nullVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            String thirdArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            String forthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument));
            break;
        case "<>":
            template = Template.Invalid.inequality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            secondArgument = nullVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            thirdArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            forthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument));
            break;
        case "<=":
        case ">=":
        case ">":
        case "<":
            break;
        case "and":
            template = Template.Invalid.and;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            firstArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();
            trueVisitor = new O2F_TrueVisitor(dm,adhocContextualSet,defC);
            exp.accept(trueVisitor);
            String fifthArgument = trueVisitor.getFOLFormulae();
            argExp.accept(trueVisitor);
            thirdArgument = trueVisitor.getFOLFormulae();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            String sixthArgument = nullVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            forthArgument = nullVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "or":
            template = Template.Invalid.or;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            firstArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();
            falseVisitor = new O2F_FalseVisitor(dm,adhocContextualSet,defC);
            exp.accept(falseVisitor);
            fifthArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            thirdArgument = falseVisitor.getFOLFormulae();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            sixthArgument = nullVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            forthArgument = nullVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "not":
            template = Template.Invalid.not;
            exp = operationCallExp.getArguments().get(0);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case "implies":
            template = Template.Invalid.implies;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            firstArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "size":
            break;
        case "isEmpty":
            template = Template.Invalid.isEmpty;
            exp = operationCallExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case "notEmpty":
            template = Template.Invalid.notEmpty;
            exp = operationCallExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
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
    	this.setFOLFormulae("false");
    }

    @Override
    public void visit(BooleanLiteralExp booleanLiteralExp) {
    	this.setFOLFormulae("false");
    }

    @Override
    public void visit(IntegerLiteralExp integerLiteralExp) {
        String template = Template.Invalid.intLiteral;
        this.setFOLFormulae(template);
    }

    @Override
    public void visit(PropertyCallExp propertyCallExp) {
        String template = Template.Invalid.attribute;

        Expression exp = propertyCallExp.getNavigationSource();

        nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
        exp.accept(nullVisitor);

        invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
        exp.accept(invalVisitor);

        this.setFOLFormulae(String.format(template,
            nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
    }

    @Override
    public void visit(AssociationClassCallExp associationClassCallExp) {
        if (associationClassCallExp instanceof O2OAssociationClassCallExp) {
            String template = Template.Invalid.association_0_1_arity;
            Expression exp = associationClassCallExp.getNavigationSource();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template, nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
        } else if (associationClassCallExp instanceof M2OAssociationClassCallExp 
            && ((M2OAssociationClassCallExp) associationClassCallExp).isOneEndAssociationCall()) {
            String template = Template.Invalid.association_0_1_arity;
            Expression exp = associationClassCallExp.getNavigationSource();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template, nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
        } else {
        	String template = Template.Invalid.association_n_arity;
            Expression exp = associationClassCallExp.getNavigationSource();
            nullVisitor = new O2F_NullVisitor(dm,adhocContextualSet,defC);
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(dm,adhocContextualSet,defC);
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template, nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
        }
    }

    @Override
    public void visit(VariableExp variableExp) {
        String template = Template.Invalid.variable;
        String var = variableExp.getVariable().getName();
        String type = variableExp.getType().getReferredType();
        this.setFOLFormulae(String.format(template, var, invalidOf(type)));
    }
}
