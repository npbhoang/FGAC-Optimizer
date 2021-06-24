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

public enum Action {
    READ, CREATE, UPDATE, DELETE;

    public static Action getAction(String action) {
        if (action == null)
            return null;
        if ("READ".compareToIgnoreCase(action) == 0)
            return READ;
        if ("CREATE".compareToIgnoreCase(action) == 0)
            return CREATE;
        if ("UPDATE".compareToIgnoreCase(action) == 0)
            return UPDATE;
        if ("DELETE".compareToIgnoreCase(action) == 0)
            return DELETE;
        else
            return null;
    }
}
