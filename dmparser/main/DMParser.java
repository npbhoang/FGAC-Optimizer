package main;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import dmparser.models.DataModel;

public class DMParser {
	public static DataModel fromFilePath(String dataModelFilePath) throws FileNotFoundException, IOException, ParseException, Exception {
		File dataModelFile = new File(dataModelFilePath);
		return new DataModel(new JSONParser().parse(new FileReader(dataModelFile.getAbsolutePath())));
	}
}
