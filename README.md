# q0.mm
A Metamath library for the Q0 logic

About Metamath, see http://us.metamath.org/
About Q0, see for example https://en.wikipedia.org/wiki/Q0_(mathematical_logic)

## Usage

* in the "metamath program": simply load the mm file (e.g. `metamath q0.mm`). 
* in MMJ2: you will have to define specific parameters in runParms.txt, as follows:
```
  LogicStmtType,statement
  DefineWorkVarType,wff,&W,200
  DefineWorkVarType,vardecl,&D,200
  DefineWorkVarType,variable,&V,200
  DefineWorkVarType,type,&T,200
  DefineWorkVarType,statement,&S,200
  DeclareWorkVars
```
* In eMetamath: custom work variable prefixes and logical statement types can be defined in the Project Properties panel.
