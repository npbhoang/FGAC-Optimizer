package main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import smparser.models.SecurityModel;

public class SMParser {
	public static SecurityModel fromFilePath(String securityModelFilePath) throws FileNotFoundException, IOException, ParseException, Exception {
		File securityModelFile = new File(securityModelFilePath);
		return new SecurityModel(
				(JSONArray) new JSONParser().parse(new FileReader(securityModelFile)));
	}
}
