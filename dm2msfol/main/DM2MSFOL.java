/**************************************************************************
Copyright 2020 Vietnamese-German-University

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

package main;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import dmparser.models.Association;
import dmparser.models.Attribute;
import dmparser.models.DataModel;
import dmparser.models.Entity;

public class DM2MSFOL {

	private static class Template {
		public static String ENTITY = "(declare-fun %s (Classifier) Bool)";
		public static String ENTITY_1 = "(assert (not (%s nullClassifier)))";
		public static String ENTITY_1_BIS = "(assert (not (%s invalidClassifier)))";
		public static String ATTRIBUTE = "(declare-fun %s_%s (Classifier) %s)";
		public static String ATTRIBUTE_1 = "(assert (= (%s_%s nullClassifier) invalid%s))";
		public static String ATTRIBUTE_1_BIS = "(assert (= (%s_%s invalidClassifier) invalid%s))";
		public static String ATTRIBUTE_2 = "(assert (forall ((x Classifier))\r\n" + "    (=> (%s x)\r\n"
				+ "        (distinct (%s_%s x) invalid%s))))";
		public static String ASSOCIATION = "(declare-fun %s (Classifier Classifier) Bool)";
		public static String ASSOCIATION_1 = "(assert (forall ((x Classifier))\r\n" + "    (forall ((y Classifier)) \r\n"
				+ "        (=> (%s x y) \r\n" + "            (and %s %s)))))";
		public static String ENTITY_2 = "(assert (forall ((x Classifier)) \r\n" + "    (=> (%s x) (not %s))))";
		public static String ASSOCIATION_2 = "(declare-fun %s_%s (Classifier) Classifier))";
		public static String ASSOCIATION_3 = "(assert (= (%s_%s nullClassifier) invalidClassifier))";
		public static String ASSOCIATION_3_BIS = "(assert (= (%s_%s invalidClassifier) invalidClassifier))";
		public static String ASSOCIATION_4 = "(assert (forall ((x Classifier))\r\n" + "    (=> (%4$s x)\r\n"
				+ "        (or (= (%1$s_%2$s x) nullClassifier)\r\n" + "            (%3$s (%1$s_%2$s x))))))";
		public static String ASSOCIATION_5 = "(assert (forall ((x Classifier))\r\n" + "    (forall ((y Classifier))\r\n"
				+ "        (=> (and (%1$s x)\r\n" + "                 (%2$s y)\r\n"
				+ "                 (= (%2$s_%3$s y) x))\r\n" + "            (%1$s_%4$s x y)))))";
		public static String ASSOCIATION_6 = "(assert (forall ((x Classifier))\r\n" + "    (forall ((y Classifier))\r\n"
				+ "        (=> (%1$s_%2$s x y)\r\n" + "            (= (%3$s_%4$s y) x)))))";
	}

	public static DataModel dm;

	public static void setDataModel(DataModel dm_) {
		dm = dm_;
	}

	public static List<String> map2msfol(DataModel dm_) throws IOException {
		setDataModel(dm_);
		List<String> formulas = new ArrayList<String>();
		formulas.addAll(generateEntitiesTheory());
		formulas.addAll(generateAttributesTheory());
		formulas.addAll(generateAssociationEndsTheory());
		formulas.addAll(generateAuxiliaryTheory());
		return formulas;
	}

	private static List<String> generateAuxiliaryTheory() throws IOException {
		List<String> formulas = new ArrayList<String>();
		for (Entity e : dm.getEntities().values()) {
			List<Entity> exclusion = new ArrayList<Entity>();
			for (Entity e_ : dm.getEntities().values()) {
				if (e_ != e) {
					exclusion.add(e_);
				}
			}
			if (exclusion.isEmpty()) {
				break;
			} else if (exclusion.size() == 1) {
				String s = String.format("(%s x)", exclusion.get(0).getName());
				formulas.add(String.format(Template.ENTITY_2, e.getName(), s));
			} else {
				String s = "";
				for (Entity e_ : exclusion) {
					s = s.concat(String.format(" (%s x)", e_.getName()));
				}
				String s_ = String.format("(or%s)", s);
				formulas.add(String.format(Template.ENTITY_2, e.getName(), s_));
			}
		}
		return formulas;
	}

	private static List<String> generateAssociationEndsTheory() throws IOException {
		List<String> formulas = new ArrayList<String>();
		for (Association as : dm.getAssociations()) {
			if (as.isManyToMany()) {
				formulas.add(String.format(Template.ASSOCIATION, as.getName()));
				String lhs = String.format("(%s x)", as.getLeftEntityName());
				String rhs = String.format("(%s y)", as.getRightEntityName());
				formulas.add(String.format(Template.ASSOCIATION_1, as.getName(), lhs, rhs));
			} else if (as.isManyToOne()) {
				formulas.add(String.format(Template.ASSOCIATION_2, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_3, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_3_BIS, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_4, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName(), as.getOneEnd().getTargetClass(), as.getOneEnd().getCurrentClass()));
				String associationName = String.format("%s_%s", as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName());
				formulas.add(String.format(Template.ASSOCIATION, associationName));
				formulas.add(String.format(Template.ASSOCIATION_1, associationName, String.format("(%s x)", as.getManyEnd().getCurrentClass()),
						String.format("(%s y)", as.getManyEnd().getTargetClass())));
				formulas.add(String.format(Template.ASSOCIATION_5, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp(), as.getManyEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_6, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName(), as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp()));
			} else {
				// Implement one-to-one transformation from DM2MSFOL
			}
		}
		return formulas;
	}

	private static List<String> generateAttributesTheory() throws IOException {
		List<String> formulas = new ArrayList<String>();
		for (Entity e : dm.getEntities().values()) {
			formulas.addAll(generateAttributesEntityTheory(e));
		}
		return formulas;
	}

	private static List<String> generateAttributesEntityTheory(Entity e) throws IOException {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ENTITY_1_BIS, e.getName()));
		for (Attribute at : e.getAttributes()) {
			formulas.addAll(generateAttributeEntityTheory(e, at));
		}
		return formulas;
	}

	private static List<String> generateAttributeEntityTheory(Entity e, Attribute at)
			throws IOException {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ATTRIBUTE, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_1, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_1_BIS, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_2, e.getName(), at.getName(),
				e.getName(), at.getType().compareTo("String") == 0 ? "String" : "Int"));
		return formulas;
	}

	private static List<String> generateEntitiesTheory() throws IOException {
		List<String> formulas = new ArrayList<String>();
		for (Entity entity : dm.getEntities().values()) {
			formulas.addAll(generateEntityTheory(entity));
		}
		return formulas;
	}

	private static List<String> generateEntityTheory(Entity e) throws IOException {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ENTITY, e.getName()));
		formulas.add(String.format(Template.ENTITY_1, e.getName()));
		return formulas;
	}
}
