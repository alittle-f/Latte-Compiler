%option noyywrap
%{
    #define YY_NO_UNPUT
    #define YY_NO_INPUT

    #include "parser.h"
    #include <ostream>
    #include <fstream>
    using namespace std;

    extern FILE *yyin; 
    extern FILE *yyout;
    extern bool dump_tokens;

    void DEBUG_FOR_LAB4(string tok, string val){
        fprintf(yyout, "%-12s%-12s\n", tok.c_str(), val.c_str());
    }
%}

    // 数据类型
INT "int"
FLOAT "float"

    // 变量和常量，包括十进制浮点数
DEC ([1-9][0-9]*|0)|((([0-9]*[.][0-9]*([eE][+-]?[0-9]+)?)|([0-9]+[eE][+-]?[0-9]+)))
HEX (0[Xx](([1-9a-fA-F][0-9a-fA-F]*)|0))|(0[xX](([0-9A-Fa-f]*[.][0-9A-Fa-f]*([pP][+-]?[0-9]+)?)|([0-9A-Fa-f]+[pP][+-]?[0-9]+)))
OCT (0(([1-7][0-7]*)|0)(\.[0-7]+)?)
ID [[:alpha:]_][[:alpha:][:digit:]_]*
EOL (\r\n|\n|\r)
WHITE [\t ]

FORMATCHAR [\r\n\t ]+

    // 语句
CONST "const"
VOID "void"
IF "if"
ELSE "else"
WHILE "while"
BREAK "break"
CONTINUE "continue"
RETURN "return"

    // 表达式、关系、逻辑运算
EQ "=="
GEQ ">="
LEQ "<="
NEQ "!="
ASSIGN "="
PLUSASSIGN "+="
SUBASSIGN "-="
MULASSIGN "*="
DIVASSIGN "/="
GRA ">"
LES "<"
PLUS "+"
SUB "-"
MUL "*"
DIV "/"
MOD "%"
AND "&&"
OR "||"
NOT "!"

LPAREN "("
RPAREN ")"
LBRACE "{"
RBRACE "}"
LSQUARE "["
RSQUARE "]"
COMMA ","
SEMICOLON ";"

    // 注释
LINECOMMENT \/\/[^\n]*
BLOCKCOMMENTBEGIN "/*"
BLOCKCOMMENTELEMENT .
BLOCKCOMMENTEND "*/"
%x BLOCKCOMMENT

%%

"int" {
    /*
    * Questions: 
    *   Q1: Why we need to return INT in further labs?
    *   Q2: What is "INT" actually?
    */
    if(dump_tokens)
        DEBUG_FOR_LAB4("INT", "int");
    return INT;
}
"float" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("FLOAT", "float");
    return FLOAT;
}
"void" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("VOID", "void");
    return VOID;
}

"if" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("IF", "if");
    return IF;
};
"else" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ELSE", "else");
    return ELSE;
};
"return" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("RETURN", "return");
    return RETURN;
}
"const" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("CONST", "const");
    return CONST;
}
"while" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("WHILE", "while");
    return WHILE;
};
"break" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("BREAK", "break");
    return BREAK;
};
"continue" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("CONTINUE", "continue");
    return CONTINUE;
};

"==" {
    if(dump_tokens)
         DEBUG_FOR_LAB4("EQ", "==");
    return EQ;
}
">=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("GEQ", ">=");
    return GEQ;
}
"<=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("LEQ", "<=");
    return LEQ;
}
"!=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("NEQ", "!=");
    return NEQ;
}
"+=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("PLUSASSIGN", "+=");
    return PLUSASSIGN;
}
"-=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("SUBASSIGN", "-=");
    return SUBASSIGN;
}
"*=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("MULASSIGN", "*=");
    return MULASSIGN;
}
"/=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("DIVASSIGN", "/=");
    return DIVASSIGN;
}

"=" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ASSIGN", "=");
    return ASSIGN;
}
"<" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("LESS", "<");
    return LES;
}
">" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("GRA", ">");
    return GRA;
}
"+" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ADD", "+");
    return ADD;
}
"-" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("SUB", "-");
    return SUB;
}
"*" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("MUL", "*");
    return MUL;
    
}
"/" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("DIV", "/");
    return DIV;
    
}
"%" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("MOD", "%");
    return MOD;
}
"&&" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("AND", "&&");
    return AND;
    
}
"||" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("OR", "||");
    return OR;
    
}
"!" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("NOT", "!");
    return NOT;
    
}
"," {
    if(dump_tokens)
        DEBUG_FOR_LAB4("COMMA", ",");
    return COMMA;
}
";" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("SEMICOLON", ";");
    return SEMICOLON;
}
"(" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("LPAREN", "(");
    return LPAREN;
}
")" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("RPAREN", ")");
    return RPAREN;
}
"{" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("LBRACE", "{");
    return LBRACE;
}
"}" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("RBRACE", "}");
    return RBRACE;
}
"[" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("LSQUARE", "[");
    return LSQUARE;
}
"]" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("RSQUARE", "]");
    return RSQUARE;
    
}

{DEC} {
    if(dump_tokens)
        DEBUG_FOR_LAB4("DEC", yytext);
    bool isFloat = false;
    for(long unsigned int i = 0; i < strlen(yytext); i++) {
        if(yytext[i] == '.' || yytext[i] == 'e' || yytext[i] == 'E') {
            isFloat = true;
            break;
        }
    }
    if(isFloat) {
        yylval.itype = atof(yytext);
        return FLOATNUM;
    }
    else {
        yylval.itype = atoi(yytext);
        return INTEGER;
    }
}

{HEX} {
    if(dump_tokens)
        DEBUG_FOR_LAB4("HEX", yytext);
    bool isFloat = false;
    for(long unsigned int i = 0; i < strlen(yytext); i++) {
        if(yytext[i] == '.' || yytext[i] == 'p' || yytext[i] == 'P') {
            isFloat = true;
            break;
        }
    }
    if(isFloat) {
        float temp;
        sscanf(yytext, "%f", &temp);
        return FLOATNUM;
    }
    else {
        char *endptr = NULL;
        yylval.itype = strtol(yytext, &endptr, 16);
        return INTEGER;
    }
}

{OCT} {
    if(dump_tokens)
        DEBUG_FOR_LAB4("OCT", yytext);
        bool isFloat = false;
    for(long unsigned int i = 0; i < strlen(yytext); i++) {
        if(yytext[i] == '.') {
            isFloat = true;
            break;
        }
    }
    if(isFloat) {
        float temp;
        sscanf(yytext, "%f", &temp);
        return FLOATNUM;
    }
    else {
        char *endptr = NULL;
        yylval.itype = strtol(yytext, &endptr, 8);
        return INTEGER;
    }
}

"putint" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(TypeSystem::intType);
    Type* funcType = new FunctionType(TypeSystem::voidType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}

"getint" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    Type* funcType = new FunctionType(TypeSystem::intType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"putch" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(TypeSystem::intType);
    Type* funcType = new FunctionType(TypeSystem::voidType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"getch" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    Type* funcType = new FunctionType(TypeSystem::intType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"putarray" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(TypeSystem::intType);
    vecType.push_back(new ArrayType(TypeSystem::intType, -1));
    Type* funcType = new FunctionType(TypeSystem::voidType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"getarray" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(new ArrayType(TypeSystem::intType, -1));
    Type* funcType = new FunctionType(TypeSystem::intType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"putfloat" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(TypeSystem::floatType);
    Type* funcType = new FunctionType(TypeSystem::voidType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}

"getfloat" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    Type* funcType = new FunctionType(TypeSystem::floatType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"putfarray" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(TypeSystem::intType);
    vecType.push_back(new ArrayType(TypeSystem::floatType, -1));
    Type* funcType = new FunctionType(TypeSystem::voidType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}
"getfarray" {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    std::vector<Type*> vecType;
    std::vector<SymbolEntry*> vecSe;
    vecType.push_back(new ArrayType(TypeSystem::floatType, -1));
    Type* funcType = new FunctionType(TypeSystem::intType, vecType,vecSe);
    SymbolTable* st = identifiers;
    while(st->getPrev())
        st = st->getPrev();
    SymbolEntry* se = new IdentifierSymbolEntry(funcType, yytext, st->getLevel(), -1, true);
    st->install(yytext, se);
    return ID;
}

{ID} {
    if(dump_tokens)
        DEBUG_FOR_LAB4("ID", yytext);
    char *lexeme;
    lexeme = new char[strlen(yytext) + 1];
    strcpy(lexeme, yytext);
    yylval.strtype = lexeme;
    return ID;
}

{EOL} yylineno++;
{WHITE}

{LINECOMMENT} {yylineno++; BEGIN INITIAL;}
{BLOCKCOMMENTBEGIN} {BEGIN BLOCKCOMMENT;}
<BLOCKCOMMENT>{BLOCKCOMMENTELEMENT} {if(!strcmp(yytext, "\n")) yylineno++;}
<BLOCKCOMMENT>{BLOCKCOMMENTEND} {BEGIN INITIAL;}

%%