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

import dmparser.models.Attribute;
import dmparser.models.DataModel;
import dmparser.models.Entity;
import oclparser.expressions.AssociationClassCallExp;
import oclparser.expressions.BooleanLiteralExp;
import oclparser.expressions.Expression;
import oclparser.expressions.IntegerLiteralExp;
import oclparser.expressions.IteratorExp;
import oclparser.expressions.IteratorKind;
import oclparser.expressions.LiteralExp;
import oclparser.expressions.M2OAssociationClassCallExp;
import oclparser.expressions.O2OAssociationClassCallExp;
import oclparser.expressions.OperationCallExp;
import oclparser.expressions.PropertyCallExp;
import oclparser.expressions.StringLiteralExp;
import oclparser.expressions.Variable;
import oclparser.expressions.VariableExp;

public class O2F_EvalVisitor extends OCL2MSFOLVisitor {

    public O2F_EvalVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
	    	defCVisitor = new O2F_DefCVisitor(dm,adhocContextualSet,defC);
	    	iteratorExp.accept(defCVisitor);
	    	String defCNameApplied = defC.get(iteratorExp).getNameApplied();
	    	this.setFOLFormulae(String.format(defCNameApplied, "%s"));
	    	break;
		default:
			break;
		}
    }

    @Override
    public void visit(OperationCallExp operationCallExp) {
        switch (operationCallExp.getReferredOperation().getName()) {
        case "allInstances":
            String template = Template.Eval.allInstances;
            String clazz = operationCallExp.getSource().getType()
                .getReferredType();
            this.setFOLFormulae(String.format(template, clazz, "%s"));
            break;
        case "oclIsUndefined":
            break;
        case "oclIsKindOf":
            break;
        case "oclIsTypeOf":
            break;
        case "oclAsType":
            break;
        case "=":
        case "<>":
        case "<=":
        case ">=":
        case ">":
        case "<":
        case "and":
        case "or":
            break;
        case "not":
            break;
        case "implies":
            break;
        case "size":
            break;
        case "isEmpty":
            break;
        case "notEmpty":
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
    	// TODO Implement StringLiteralExp in O2F_eval definition

    }

    @Override
    public void visit(BooleanLiteralExp booleanLiteralExp) {
        // TODO Implement BooleanLiteralExp in O2F_eval definition

    }

    @Override
    public void visit(IntegerLiteralExp integerLiteralExp) {
        String template = Template.Eval.intLiteral;
        this.setFOLFormulae(String.format(template,
            Integer.toString(integerLiteralExp.getValue())));
    }

    @Override
    public void visit(PropertyCallExp propertyCallExp) {
        String property = propertyCallExp.getReferredProperty();
        String clazz = null;
        for (Entity e : dm.getEntities().values()) {
            for (Attribute att : e.getAttributes()) {
                if (att.getName().equals(property)) {
                    clazz = e.getName();
                }
            }
        }
        evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
        Expression exp = propertyCallExp.getNavigationSource();
        exp.accept(evalVisitor);
        String template = Template.Eval.attribute;
        this.setFOLFormulae(String.format(template, property,
            evalVisitor.getFOLFormulae(), clazz));
    }

    @Override
    public void visit(AssociationClassCallExp associationClassCallExp) {
        if (associationClassCallExp instanceof O2OAssociationClassCallExp) {
            String association = associationClassCallExp.getAssociation();
            String clazz = associationClassCallExp
                .getReferredAssociationEndType().getReferredType();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            String template = Template.Eval.association_0_1_arity;
            this.setFOLFormulae(String.format(template, association,
                evalVisitor.getFOLFormulae(), clazz));
        } else if (associationClassCallExp instanceof M2OAssociationClassCallExp
            && ((M2OAssociationClassCallExp) associationClassCallExp)
                .isOneEndAssociationCall()) {
            String association = associationClassCallExp.getAssociation();
            String clazz = associationClassCallExp
                .getReferredAssociationEndType().getReferredType();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            String template = Template.Eval.association_0_1_arity;
            this.setFOLFormulae(String.format(template, association,
                evalVisitor.getFOLFormulae(), clazz));
        } else {
        	String association = associationClassCallExp.getAssociation();
        	String template = Template.Eval.association_n_arity;
        	evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            this.setFOLFormulae(String.format(template, association,
                    "%s"));
        }
    }

    @Override
    public void visit(VariableExp variableExp) {
        String template = Template.Eval.variable;
        this.setFOLFormulae(
            String.format(template, variableExp.getVariable().getName()));
    }
}
