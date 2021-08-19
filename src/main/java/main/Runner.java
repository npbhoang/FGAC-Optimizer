package main;

import java.util.List;

import dmparser.models.Association;
import dmparser.models.Attribute;
import dmparser.models.DataModel;
import dmparser.models.Entity;
import dmparser.models.Pair;
import ocl2msfol.visitor.LogicValue;
import oclparser.expressions.OclExp;
import oclparser.expressions.Variable;
import oclparser.simple.OCLParser;
import oclparser.types.Type;
import smparser.models.SecurityModel;
import smparser.utils.RuleUtils;
import utils.PrintingUtils;

public class Runner {

	public void run(Configuration c) {
		// Init DataModel object.
		DataModel dataModel = c.getDataModelFile();
		// Init array that stores all FOL formulas.
		List<String> formulas = PrintingUtils.init();
		// Generate the data model theories.
		formulas.addAll(DM2MSFOL.map2msfol(dataModel));
		// Init OCLParser, set the data model
		OCLParser oclParser = new OCLParser();
		OCL2MSFOL.setDataModel(dataModel);
		// Generate data invariant formulas
		for (String inv : c.getOclInvariants()) {
			OclExp exp = (OclExp) oclParser.parse(inv, dataModel);
			OCL2MSFOL.setExpression(exp);
			formulas.addAll(OCL2MSFOL.map2msfol(false));
		}
		// Init Security Model object
		SecurityModel securityModel = c.getSecurityModelFile();
		// Set security context variables into OCL parsing environment.
		// Otherwise, it cannot parse.
		// Also, add basic properties about these variables into the theory, i.e. what
		// class it belongs.
		for (Pair<String, String> pair : c.getSecurityVariables()) {
			oclParser.putAdhocContextualSet(new Variable(pair.getLeft(), new Type(pair.getRight())));
			formulas.add(String.format("(declare-const %s %s)", pair.getLeft(), "Classifier"));
			formulas.add(String.format("(assert (%s %s))", pair.getRight(), pair.getLeft()));
		}
		// This is for adding new axiom for association
		if (!c.getIsAttribute()) {
			Association association = c.getAssociation();
			String leftVariable = c.getSecurityVariables().get(1).getLeft();
			String rightVariable = c.getSecurityVariables().get(2).getLeft();
			formulas.add(String.format("(assert (%s %s %s))", association.getName(), leftVariable, rightVariable));
		}
		// Generate properties formulas
		for (String prop : c.getOclProperties()) {
			OclExp exp = (OclExp) oclParser.parse(prop, dataModel);
			OCL2MSFOL.setExpression(exp);
			OCL2MSFOL.setLvalue(LogicValue.TRUE);
			formulas.addAll(OCL2MSFOL.map2msfol(false));
		}
		// sAuth is the final authorization constraint that need to be checked.
		String sAuth = null;

		if (c.getIsAttribute()) {
			// If the caller want to read an attribute
			// We get the entity and attribute from the data model,
			// then retrieve the authorization constraint of this attribute from security
			// model
			Entity entity = c.getEntity();
			Attribute attribute = c.getAttribute();
			sAuth = RuleUtils.getPolicyForAttribute(securityModel, entity, attribute, c.getsRole());
		} else {
			// If the caller want to read an association
			// We get the association from the data model,
			// then retrieve the authorization constraint from security model
			Association association = c.getAssociation();
			sAuth = RuleUtils.getPolicyForAssociation(securityModel, association, c.getsRole());
		}
		// Parse it into OclExp object
		OclExp oclAuth = (OclExp) oclParser.parse(sAuth, dataModel);
		// Depends on the mode, decide to negate it or not.
		boolean negation = false;
		if (c.getCheckAuthorized()) {
//					oclAuth = new OperationCallExp(null, new Operation("not"), Arrays.asList(oclAuth));
			negation = true;
		}
		// Generate its FOL formula
		OCL2MSFOL.setExpression(oclAuth);
		OCL2MSFOL.setLvalue(LogicValue.TRUE);
		formulas.addAll(OCL2MSFOL.map2msfol(negation));
		// Adding (check-sat) and (get-models)
		formulas.add("(check-sat)");
//		formulas.add("(get-model)");
		// Printout all formulas.
		formulas.forEach(s -> System.out.println(s));

	}

}
