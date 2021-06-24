package main;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;

import org.json.simple.parser.ParseException;

import dmparser.models.Association;
import dmparser.models.Attribute;
import dmparser.models.DataModel;
import dmparser.models.Entity;
import dmparser.models.Pair;
import dmparser.utils.DmUtils;
import oclparser.expressions.OclExp;
import oclparser.expressions.Operation;
import oclparser.expressions.OperationCallExp;
import oclparser.expressions.Variable;
import oclparser.simple.OCLParser;
import oclparser.types.Type;
import smparser.models.SecurityModel;
import smparser.utils.RuleUtils;
import utils.PrintingUtils;

public class Runner {

	public static class Context {
		
		// Data Model
		final static String dataModelFilePath = "src\\main\\resources\\university.json";
		
		// List of data invariants
		final static List<String> invariants = Arrays.asList(
				"Lecturer.allInstances()->forAll(l|Student.allInstances()->forAll(s|l.students->includes(s)))"
				);
		
		// Security Model
		final static String securityModelFilePath = "src\\main\\resources\\secVGU#3.json";
		
		// Security variables: self, caller, association-ends
		// For now, please add "k" as a prefix of these variables.
		final static List<Pair<String, String>> securityVariables = Arrays
				.asList(new Pair<String, String>("kcaller", "Lecturer"), 
						new Pair<String, String>("kstudents", "Student"),
						new Pair<String, String>("klecturers", "Lecturer"));

		// Properties of the security variables
		final static List<String> properties = Arrays.asList();
		
		// role of caller
		final static String role = "Lecturer";

		// if caller reads an attribute of a class
		final static boolean isAttribute = false;
		final static String entityToRead = null;
		final static String attributeToRead = null;
		
		// if caller reads an association
		// note: please change the boolean isAttribute = false.
		final static String associationToRead = "Enrollment";
		
		// checkAuthroized negate the authorization constraints
		final static boolean checkAuthroized = false;
			
	}

	public static void main(String[] args) throws FileNotFoundException, IOException, ParseException, Exception {
		
		// Init DataModel object.
		DataModel dataModel = DMParser.fromFilePath(Context.dataModelFilePath);
		// Init array that stores all FOL formulas.
		List<String> formulas = PrintingUtils.init();
		// Generate the data model theories.		
		formulas.addAll(DM2MSFOL.map2msfol(dataModel));
		// Init OCLParser, set the data model
		OCLParser oclParser = new OCLParser();
		OCL2MSFOL.setDataModel(dataModel);
		// Generate data invariant formulas
		for (String inv : Context.invariants) {
			OclExp exp = (OclExp) oclParser.parse(inv, dataModel);
			OCL2MSFOL.setExpression(exp);
			formulas.addAll(OCL2MSFOL.map2msfol());
		}
		// Init Security Model object
		SecurityModel securityModel = SMParser.fromFilePath(Context.securityModelFilePath);
		// Set security context variables into OCL parsing environment.
		// Otherwise, it cannot parse.
		// Also, add basic properties about these variables into the theory, i.e. what class it belongs.
		for (Pair<String, String> pair : Context.securityVariables) {
			oclParser.putAdhocContextualSet(new Variable(pair.getLeft(), new Type(pair.getRight())));
			formulas.add(String.format("(declare-const %s %s)", pair.getLeft(), "Classifier"));
			formulas.add(String.format("(assert (%s %s))", pair.getRight(), pair.getLeft()));
		}
		// Generate properties formulas
		for (String prop : Context.properties) {
			OclExp exp = (OclExp) oclParser.parse(prop, dataModel);
			OCL2MSFOL.setExpression(exp);
			formulas.addAll(OCL2MSFOL.map2msfol());
		}
		// sAuth is the final authorization constraint that need to be checked.
		String sAuth = null;
		
		if (Context.isAttribute) {
			// If the caller want to read an attribute
			// We get the entity and attribute from the data model,
			// then retrieve the authorization constraint of this attribute from security model
			Entity entity = DmUtils.getEntity(dataModel, Context.entityToRead);
			Attribute attribute = DmUtils.getAttribute(entity, Context.attributeToRead);
			sAuth = RuleUtils.getPolicyForAttribute(securityModel, entity, attribute, Context.role);
		} else {
			// If the caller want to read an association
			// We get the association from the data model,
			// then retrieve the authorization constraint from security model
			Association association = DmUtils.getAssociation(dataModel, Context.associationToRead);
			sAuth = RuleUtils.getPolicyForAssociation(securityModel, association, Context.role);
		}
		// Parse it into OclExp object
		OclExp oclAuth = (OclExp) oclParser.parse(sAuth, dataModel);
		// Depends on the mode, decide to negate it or not.
		if (Context.checkAuthroized) {
			oclAuth = new OperationCallExp(null, new Operation("not"), Arrays.asList(oclAuth));
		}
		// Generate its FOL formula
		OCL2MSFOL.setExpression(oclAuth);
		formulas.addAll(OCL2MSFOL.map2msfol());
		// Adding (check-sat) and (get-models)
		formulas.add("(check-sat)");
		formulas.add("(get-model)");
		// Printout all formulas.
		formulas.forEach(s -> System.out.println(s));

	}
}
