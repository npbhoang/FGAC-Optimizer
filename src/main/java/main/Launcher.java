package main;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Map;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.vgu.dm2schema.dm.Association;
import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.DmUtils;
import org.vgu.dm2schema.dm.Entity;
import org.vgu.dm2schema.dm.Pair;

import smparser.models.SecurityModel;

public class Launcher {

	private static final String ENV_DM_PATH = "PATHTODATAMODEL";
	private static final String ENV_SM_PATH = "PATHTOSECURITYMODEL";
	private static final String ENV_INVS = "INVARIANTS";
	private static final String ENV_PROPS = "PROPERTIES";
	private static final String ENV_ROLE = "ROLE";
	private static final String ENV_ENTITY = "ENTITY";
	private static final String ENV_ATTRIBUTE = "ATTRIBUTE";
	private static final String ENV_ASSOCIATION = "ASSOCIATION";
	private static final String ENV_AUTHORIZED = "CHECKAUTHORIZED";

	private static Configuration createConfiguration() {
		Configuration c = new Configuration();
		final Map<String, String> env = System.getenv();

		final String sDataModelPath = env.get(ENV_DM_PATH);
		if (sDataModelPath != null) {
			final File fileDataModel = new File(sDataModelPath);
			if (fileDataModel.canRead()) {
				DataModel dataModel;
				try {
					dataModel = new DataModel(new JSONParser().parse(new FileReader(fileDataModel)));
				} catch (Exception e) {
					throw new IllegalArgumentException("Cannot read Datamodel JSON file " + sDataModelPath);
				}
				c.setDataModelFile(dataModel);
				if (DmUtils.getUserEntity(dataModel) == null) {
					throw new IllegalArgumentException("Datamodel has no userclass, please specify one!");
				}
			} else {
				throw new IllegalArgumentException("Cannot read Datamodel JSON file " + sDataModelPath);
			}
		}

		final String sSecurityModelPath = env.get(ENV_SM_PATH);
		if (sSecurityModelPath != null) {
			final File fileSecurityModel = new File(sSecurityModelPath);
			if (fileSecurityModel.canRead()) {
				SecurityModel securityModel;
				try {
					securityModel = new SecurityModel(
							(JSONArray) new JSONParser().parse(new FileReader(fileSecurityModel)));
				} catch (IOException | ParseException e) {
					throw new IllegalArgumentException("Cannot read Securitymodel JSON file " + sSecurityModelPath);
				}
				c.setSecurityModelFile(securityModel);
			} else {
				throw new IllegalArgumentException("Cannot read Securitymodel JSON file " + sSecurityModelPath);
			}
		}

		final String sInvariants = env.get(ENV_INVS);
		if (sInvariants != null) {
			c.setOclInvariants(Arrays.asList(sInvariants.split("##")));
		} else {
			c.setOclInvariants(new ArrayList<String>());
		}

		final String sProperties = env.get(ENV_PROPS);
		if (sProperties != null) {
			c.setOclProperties(Arrays.asList(sProperties.split("##")));
		} else {
			c.setOclProperties(new ArrayList<String>());
		}

		final String sRole = env.get(ENV_ROLE);
		if (sRole != null) {
			c.setsRole(sRole);
		}

		final String sEntity = env.get(ENV_ENTITY);
		if (sEntity != null && c.getDataModelFile() != null) {
			Entity entity = DmUtils.getEntity(c.getDataModelFile(), sEntity);
			if (entity != null) {
				c.setEntity(entity);
			} else {
				throw new IllegalArgumentException("Cannot find Entity with name " + sEntity);
			}
		}

		final String sAttribute = env.get(ENV_ATTRIBUTE);
		if (sAttribute != null && c.getEntity() != null) {
			Attribute attribute = DmUtils.getAttribute(c.getEntity(), sAttribute);
			if (attribute != null) {
				c.setAttribute(attribute);
			} else {
				throw new IllegalArgumentException("Cannot find Attribute with name " + sAttribute);
			}
		}

		final String sAssociation = env.get(ENV_ASSOCIATION);
		if (sAssociation != null && c.getDataModelFile() != null) {
			Association association = DmUtils.getAssociation(c.getDataModelFile(), sAssociation);
			if (association != null) {
				c.setAssociation(association);
			} else {
				throw new IllegalArgumentException("Cannot find Association with name " + sAssociation);
			}
		}

		final String sCheckAuthorized = env.get(ENV_AUTHORIZED);
		if (sCheckAuthorized != null) {
			c.setCheckAuthorized(Boolean.valueOf(sCheckAuthorized));
		}

		setAuxiliariesConfigs(c);

		return c;
	}

	private static void setAuxiliariesConfigs(Configuration c) {
		Attribute attribute = c.getAttribute();
		Association association = c.getAssociation();
		Entity userEntity = DmUtils.getUserEntity(c.getDataModelFile());
		if (attribute != null && association != null) {
			throw new IllegalArgumentException(String.format("Cannot check two properties at once: (i) %s and (ii) %s", attribute.getName(), association.getName()));
		} else if (attribute != null) {
			c.setIsAttribute(true);
			Entity entity = c.getEntity();
			c.setSecurityVariables(Arrays.asList(
					new Pair<String, String>("kcaller", userEntity.getName()),
					new Pair<String, String>("kself", entity.getName())
					));
		} else if (association != null) {
			c.setIsAttribute(false);
			String leftEndVariable = String.format("k%s", association.getLeftEnd());
			String rightEndVariable = String.format("k%s", association.getRightEnd());
			c.setSecurityVariables(Arrays.asList(
					new Pair<String, String>("kcaller", userEntity.getName()),
					new Pair<String, String>(leftEndVariable, association.getLeftEntityName()),
					new Pair<String, String>(rightEndVariable, association.getRightEntityName())
					));
		} else {
			throw new IllegalArgumentException(String.format("Missing propery to be checked!"));
		}
		
	}

	public static void main(String[] args) {

		Configuration c = createConfiguration();
		new Runner().run(c);

	}
}
