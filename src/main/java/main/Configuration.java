package main;

import java.util.List;

import org.vgu.dm2schema.dm.Association;
import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.Entity;
import org.vgu.dm2schema.dm.Pair;

import smparser.models.SecurityModel;

public class Configuration {
	private DataModel dataModelFile; 
	private SecurityModel securityModelFile;
	private List<String> oclInvariants;
	private List<Pair<String, String>> securityVariables;
	private List<String> oclProperties;
	private Entity entity;
	private Attribute attribute;
	private Association association;
	private String sRole;
	private Boolean isAttribute, checkAuthorized;

	public DataModel getDataModelFile() {
		return dataModelFile;
	}

	public void setDataModelFile(DataModel dataModelFile) {
		this.dataModelFile = dataModelFile;
	}

	public SecurityModel getSecurityModelFile() {
		return securityModelFile;
	}

	public void setSecurityModelFile(SecurityModel securityModelFile) {
		this.securityModelFile = securityModelFile;
	}

	public List<String> getOclInvariants() {
		return oclInvariants;
	}

	public void setOclInvariants(List<String> oclInvariants) {
		this.oclInvariants = oclInvariants;
	}

	public List<Pair<String, String>> getSecurityVariables() {
		return securityVariables;
	}

	public void setSecurityVariables(List<Pair<String, String>> securityVariables) {
		this.securityVariables = securityVariables;
	}

	public List<String> getOclProperties() {
		return oclProperties;
	}

	public void setOclProperties(List<String> oclProperties) {
		this.oclProperties = oclProperties;
	}

	public String getsRole() {
		return sRole;
	}

	public void setsRole(String sRole) {
		this.sRole = sRole;
	}

	public Boolean getIsAttribute() {
		return isAttribute;
	}

	public void setIsAttribute(Boolean isAttribute) {
		this.isAttribute = isAttribute;
	}

	public Boolean getCheckAuthorized() {
		return checkAuthorized;
	}

	public void setCheckAuthorized(Boolean checkAuthorized) {
		this.checkAuthorized = checkAuthorized;
	}

	public Entity getEntity() {
		return entity;
	}

	public void setEntity(Entity entity) {
		this.entity = entity;
	}

	public Attribute getAttribute() {
		return attribute;
	}

	public void setAttribute(Attribute attribute) {
		this.attribute = attribute;
	}

	public Association getAssociation() {
		return association;
	}

	public void setAssociation(Association association) {
		this.association = association;
	}

}