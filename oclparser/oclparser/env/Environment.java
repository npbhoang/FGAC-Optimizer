/**************************************************************************
Copyright 2019 Vietnamese-German-University

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


package oclparser.env;

import java.io.IOException;
import java.io.Reader;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;

import oclparser.expressions.NullLiteralExp;
import oclparser.expressions.OclExp;

public class Environment {
    private JSONArray plainUMLContext;
    private String oclExpStr;
    private OclExp oclExp;

    public JSONArray getPlainUMLContext() {
        return plainUMLContext;
    }
    public void setPlainUMLContext(String plainUMLContext) throws ParseException {
        this.plainUMLContext = (JSONArray) new JSONParser().parse(plainUMLContext);
    }
    public void setPlainUMLContext(Reader reader) throws IOException, ParseException {
        this.plainUMLContext = (JSONArray) new JSONParser().parse(reader);
    }
    public String getOclExpStr() {
        return oclExpStr;
    }
    public void setOclExpStr(String oclExpStr) {
        this.oclExpStr = oclExpStr;
    }
    public OclExp getOclExp() {
        return oclExp;
    }
    public void setOclExp(OclExp oclExp) {
        this.oclExp = oclExp;
    }
    public OclExp parse() {
        //TODO: Add parsing function.
        return new NullLiteralExp();
    }
}
