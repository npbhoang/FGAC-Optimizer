package utils;

import java.util.ArrayList;
import java.util.List;

public class PrintingUtils {
	public static List<String> init() {
		List<String> formulas = new ArrayList<String>();
		formulas.add("(set-logic UFSLIA)");
		formulas.add("(set-option :produce-models true)");
		formulas.add("(declare-sort Classifier 0)");
		formulas.add("(declare-const nullClassifier Classifier)");
        formulas.add("(declare-const invalidClassifier Classifier)");
        formulas.add("(declare-const nullInt Int)");
        formulas.add("(declare-const invalidInt Int)");
        formulas.add("(declare-const nullString String)");
        formulas.add("(declare-const invalidString String)");
        formulas.add("(assert (distinct nullClassifier invalidClassifier))");
        formulas.add("(assert (distinct nullInt invalidInt))");
        formulas.add("(assert (distinct nullString invalidString))");
		return formulas;
	}
}
