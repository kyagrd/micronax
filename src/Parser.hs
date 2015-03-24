module Parser where

import Language.LBNF

bnfc [lbnf|
token BCbegin ( '{' '-' ) ;
token BCend   ( '-' '}' ) ;
comment "--" ;
comment "{-" "-}" ;

EAdd.   Exp     ::=     Exp     "+"     Exp1    ;
ESub.   Exp     ::=     Exp     "-"     Exp1    ;
EMul.   Exp1    ::=     Exp1    "*"     Exp2    ;
EDiv.   Exp1    ::=     Exp1    "/"     Exp2    ;
EInt.   Exp2    ::=     Integer         ;
coercions       Exp     2       ;
          |]
