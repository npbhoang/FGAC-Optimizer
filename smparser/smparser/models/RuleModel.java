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

package smparser.models;

import java.util.ArrayList;
import java.util.List;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;

public class RuleModel {
    private List<RoleModel> roles;
    private List<Action> actions;
    private List<ResrouceModel> resources;
    private List<AuthModel> auth;

    public RuleModel(JSONObject authEntityJSON) {
        roles = convertRoles((JSONArray) authEntityJSON.get("roles"));
        actions = convertActions((JSONArray) authEntityJSON.get("actions"));
        resources = convertResources(
            (JSONArray) authEntityJSON.get("resources"));
        auth = convertAuth((JSONArray) authEntityJSON.get("auth"));
    }

    private List<AuthModel> convertAuth(JSONArray authsJSON) {
        List<AuthModel> auths = new ArrayList<AuthModel>();
        for (Object authJSON : authsJSON) {
            auths.add(new AuthModel(authJSON));
        }
        return auths;
    }

    private List<ResrouceModel> convertResources(JSONArray resourcesJSON) {
        List<ResrouceModel> resources = new ArrayList<ResrouceModel>();
        for (Object resourceJSON : resourcesJSON) {
            resources.add(SecResourceFactory.create(resourceJSON));
        }
        return resources;
    }

    private List<Action> convertActions(JSONArray actionsJSON) {
        List<Action> actions = new ArrayList<Action>();
        for (Object actionJSON : actionsJSON) {
            actions.add(Action.getAction((String) actionJSON));
        }
        return actions;
    }

    private List<RoleModel> convertRoles(JSONArray rolesJSON) {
        List<RoleModel> roles = new ArrayList<RoleModel>();
        for (Object roleJSON : rolesJSON) {
            roles.add(new RoleModel((String) roleJSON));
        }
        return roles;
    }

    public List<RoleModel> getRoles() {
        return roles;
    }

    public void setRoles(List<RoleModel> roles) {
        this.roles = roles;
    }

    public List<Action> getActions() {
        return actions;
    }

    public void setActions(List<Action> actions) {
        this.actions = actions;
    }

    public List<ResrouceModel> getResources() {
        return resources;
    }

    public void setResources(List<ResrouceModel> resources) {
        this.resources = resources;
    }

    public List<AuthModel> getAuth() {
        return auth;
    }

    public void setAuth(List<AuthModel> auth) {
        this.auth = auth;
    }

    public RuleModel(List<RoleModel> roles, List<Action> actions,
        List<ResrouceModel> resources, List<AuthModel> auth) {
        super();
        this.roles = roles;
        this.actions = actions;
        this.resources = resources;
        this.auth = auth;
    }

    public RuleModel() {
    }
}


