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

package smparser.utils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

import dmparser.models.Association;
import dmparser.models.Attribute;
import dmparser.models.Entity;
import smparser.models.Action;
import smparser.models.AssociationUnitRule;
import smparser.models.AttributeUnitRule;
import smparser.models.Auth;
import smparser.models.RoleModel;
import smparser.models.RuleModel;
import smparser.models.SecResourceAssociationModel;
import smparser.models.SecResourceAttributeModel;
import smparser.models.SecUnitRule;
import smparser.models.SecurityModel;

public class RuleUtils {

    public static List<SecUnitRule> getAllUnitRules(SecurityModel securityModel) {
        List<SecUnitRule> unitRules = new ArrayList<SecUnitRule>();
        unitRules.addAll(getUnitRulesFromEntity(securityModel));
        unitRules.addAll(getUnitRulesFromAssociaiton(securityModel));
        return unitRules;
    }
    
    public static HashMap<String, List<SecUnitRule>> filterAndIndexRules(
            String action, Association association, List<SecUnitRule> rules) {
            HashMap<String, List<SecUnitRule>> indexRules = new HashMap<String, List<SecUnitRule>>();
            if (rules != null) {
                for (SecUnitRule rule : rules) {
                    if (rule instanceof AssociationUnitRule) {
                        AssociationUnitRule attRule = (AssociationUnitRule) rule;
                        if (attRule.getAssociation().equals(association.getName())
                            && attRule.getAction().equals(action)) {
                            if (indexRules.containsKey(rule.getRole())) {
                                indexRules.get(rule.getRole()).add(rule);
                            } else {
                                indexRules.put(rule.getRole(),
                                    new ArrayList<SecUnitRule>());
                                indexRules.get(rule.getRole()).add(rule);
                            }
                        }
                    }
                }
            }
            return indexRules;
        }
    
    public static HashMap<String, List<SecUnitRule>> filterAndIndexRules(
            String action, Entity entity, Attribute attribute,
            List<SecUnitRule> rules) {
            HashMap<String, List<SecUnitRule>> indexRules = new HashMap<String, List<SecUnitRule>>();
            if (rules != null) {
                for (SecUnitRule rule : rules) {
                    if (rule instanceof AttributeUnitRule) {
                        AttributeUnitRule attRule = (AttributeUnitRule) rule;
                        if (attRule.getEntity().equals(entity.getName())
                            && attRule.getAttribute().equals(attribute.getName())
                            && attRule.getAction().equals(action)) {
                            if (indexRules.containsKey(rule.getRole())) {
                                indexRules.get(rule.getRole()).add(rule);
                            } else {
                                indexRules.put(rule.getRole(),
                                    new ArrayList<SecUnitRule>());
                                indexRules.get(rule.getRole()).add(rule);
                            }
                        }
                    }
                }
            }
            return indexRules;
        }

    private static Collection<? extends SecUnitRule> getUnitRulesFromAssociaiton(
        SecurityModel securityModel) {
        List<SecUnitRule> rules = new ArrayList<SecUnitRule>();
        rules.addAll(
            getUnitRulesFromAssociaiton(Action.CREATE, securityModel));
        rules.addAll(
            getUnitRulesFromAssociaiton(Action.READ, securityModel));
        rules.addAll(
            getUnitRulesFromAssociaiton(Action.UPDATE, securityModel));
        rules.addAll(
            getUnitRulesFromAssociaiton(Action.DELETE, securityModel));
        return rules;
    }

    private static Collection<? extends SecUnitRule> getUnitRulesFromAssociaiton(
        Action action, SecurityModel securityModel) {
        List<SecUnitRule> rules = new ArrayList<SecUnitRule>();
        List<RuleModel> secReadRuleModels = securityModel.getRules().stream()
            .filter(
                r -> r.getActions() != null && r.getActions().contains(action))
            .collect(Collectors.toList());
        for (RuleModel ruleModel : secReadRuleModels) {
            List<RoleModel> roles = ruleModel.getRoles();
            List<SecResourceAssociationModel> resources = ruleModel
                .getResources().stream()
                .filter(res -> res instanceof SecResourceAssociationModel)
                .map(SecResourceAssociationModel.class::cast)
                .collect(Collectors.toList());
            List<Auth> auths = ruleModel.getAuth().stream()
                .map(au -> new Auth(au)).collect(Collectors.toList());
            for (RoleModel role : roles) {
                for (SecResourceAssociationModel resource : resources) {
                    rules
                        .add(new AssociationUnitRule(Action.READ.name(),
                            role.getRole(), auths, resource.getAssociation()));
                }
            }
        }
        return rules;
    }

    private static Collection<? extends SecUnitRule> getUnitRulesFromEntity(
        SecurityModel securityModel) {
        List<SecUnitRule> rules = new ArrayList<SecUnitRule>();
        rules.addAll(
            getUnitRulesFromEntity(Action.CREATE, securityModel));
        rules
            .addAll(getUnitRulesFromEntity(Action.READ, securityModel));
        rules.addAll(
            getUnitRulesFromEntity(Action.UPDATE, securityModel));
        rules.addAll(
            getUnitRulesFromEntity(Action.DELETE, securityModel));
        return rules;
    }

    private static Collection<? extends SecUnitRule> getUnitRulesFromEntity(
        Action action, SecurityModel securityModel) {
        List<SecUnitRule> rules = new ArrayList<SecUnitRule>();
        List<RuleModel> secReadRuleModels = securityModel.getRules().stream()
            .filter(
                r -> r.getActions() != null && r.getActions().contains(action))
            .collect(Collectors.toList());
        for (RuleModel ruleModel : secReadRuleModels) {
            List<RoleModel> roles = ruleModel.getRoles();
            List<SecResourceAttributeModel> resources = ruleModel.getResources()
                .stream()
                .filter(res -> res instanceof SecResourceAttributeModel)
                .map(SecResourceAttributeModel.class::cast)
                .collect(Collectors.toList());
            List<Auth> auths = ruleModel.getAuth().stream()
                .map(au -> new Auth(au)).collect(Collectors.toList());
            for (RoleModel role : roles) {
                for (SecResourceAttributeModel resource : resources) {
                    rules.add(new AttributeUnitRule(Action.READ.name(),
                        role.getRole(), auths, resource.getEntity(),
                        resource.getAttribute()));
                }
            }
        }
        return rules;
    }

	public static String getPolicyForAttribute(SecurityModel securityModel, Entity entity, Attribute attribute,
			String role) {
		List<SecUnitRule> rules = RuleUtils.getAllUnitRules(securityModel);
		HashMap<String, List<SecUnitRule>> indexRules = RuleUtils.filterAndIndexRules(
				"READ", entity, attribute, rules);
		List<SecUnitRule> ruleRoleBased = indexRules.get(role);
		List<String> authChecks = ruleRoleBased.stream().map(SecUnitRule::getAuths)
		        .flatMap(auths -> auths.stream().map(Auth::getOcl))
		        .collect(Collectors.toList());
		String authOcl = rewriteExpression(authChecks);
		return authOcl;
	}

	private static String rewriteExpression(List<String> authChecks) {
		String authOcl = null;
		if(authChecks!= null && !authChecks.isEmpty()) {
			if (authChecks.size() == 1) {
				authOcl = authChecks.get(0);
			} else {
				authOcl = authChecks.get(0);
				for(int i = 1; i < authChecks.size(); i++) {
					authOcl = authOcl.concat(" or ").concat(authChecks.get(i));
				}
			}
		}
		return authOcl;
	}

	public static String getPolicyForAssociation(SecurityModel securityModel, Association association, String role) {
		List<SecUnitRule> rules = RuleUtils.getAllUnitRules(securityModel);
		HashMap<String, List<SecUnitRule>> indexRules = RuleUtils.filterAndIndexRules(
				"READ", association, rules);
		List<SecUnitRule> ruleRoleBased = indexRules.get(role);
		List<String> authChecks = ruleRoleBased.stream().map(SecUnitRule::getAuths)
		        .flatMap(auths -> auths.stream().map(Auth::getOcl))
		        .collect(Collectors.toList());
		String authOcl = rewriteExpression(authChecks);
		return authOcl;
	}

}
