#ifndef __AST_H__
#define __AST_H__

#include <fstream>
#include "Operand.h"

class SymbolEntry;
class Unit;
class Function;
class BasicBlock;
class Instruction;
class IRBuilder;

class Node
{
private:
    static int counter;
    int seq;
    Node* next;
protected:
    std::vector<Instruction*> true_list;
    std::vector<Instruction*> false_list;
    static IRBuilder *builder;
    void backPatch(std::vector<Instruction*> &list, BasicBlock*bb);
    std::vector<Instruction*> merge(std::vector<Instruction*> &list1, std::vector<Instruction*> &list2);

public:
    Node();
    int getSeq() const {return seq;};
    static void setIRBuilder(IRBuilder*ib) {builder = ib;};
    virtual void output(int level) = 0;
    virtual void typeCheck() = 0;
    virtual void genCode() = 0;
    void setNext(Node* node);
    Node* getNext() {return next;}
    std::vector<Instruction*>& trueList() {return true_list;}
    std::vector<Instruction*>& falseList() {return false_list;}
    void pushBackTrue(Instruction *ins) {true_list.push_back(ins);}
    void pushBackFalse(Instruction *ins) {false_list.push_back(ins);}
};

class ExprNode : public Node
{
protected:
    SymbolEntry *symbolEntry;
    Type *type;
    Operand *dst;   // The result of the subtree is stored into dst.
public:
    ExprNode(SymbolEntry *symbolEntry) : symbolEntry(symbolEntry){};
    Operand* getOperand() {return dst;};
    SymbolEntry* getSymPtr() {return symbolEntry;};
    virtual double getValue() {return -1;};
    virtual Type* getType() {return type;};
    void output(int level);
    void typeCheck();
    void genCode();
    void intToBool();
};

class BinaryExpr : public ExprNode
{
private:
    int op;
    ExprNode *expr1, *expr2;
public:
    enum {ADD, SUB, MUL, DIV, MOD, AND, OR, EQ, GEQ, LEQ, NEQ, GRA, LES};
    BinaryExpr(SymbolEntry *se, int op, ExprNode*expr1, ExprNode*expr2) ;
    double getValue();
    void output(int level);
    void typeCheck();
    void genCode();
};

class UnaryExpr : public ExprNode
{
private:
    int op;
    ExprNode *expr;
public:
    enum {NOT, SUB};
    UnaryExpr(SymbolEntry *se, int op, ExprNode*expr);
    void output(int level);
    double getValue();
    int getOp() const {return op;};
    void setType(Type* type) {this->type = type;}
    void typeCheck();
    void genCode();
};

class Constant : public ExprNode
{
public:
    Constant(SymbolEntry *se);
    double getValue();
    void output(int level);
    void typeCheck();
    void genCode();
};

class Id : public ExprNode
{
private:
    ExprNode* arrIdx;
    bool left = false;
public:
    Id(SymbolEntry *se, ExprNode* arrIdx = nullptr);
    double getValue();
    ExprNode* getArrIdx() { return arrIdx; };
    bool isLeft() const { return left; };
    void setLeft() { left = true; } 
    void output(int level);
    void typeCheck();
    void genCode();
};

class ConstId : public ExprNode
{
public:
    ConstId(SymbolEntry *se) : ExprNode(se){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class FuncParam : public ExprNode
{
public:
    FuncParam(SymbolEntry *se) : ExprNode(se){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class CallFunc : public ExprNode {
private:
    ExprNode* param;
public:
    CallFunc(SymbolEntry* se, ExprNode* param = nullptr);
    void output(int level);
    void typeCheck();
    void genCode();
};

class StmtNode : public Node
{};

class CompoundStmt : public StmtNode
{
private:
    StmtNode *stmt;
public:
    CompoundStmt(StmtNode *stmt) : stmt(stmt) {};
    void output(int level);
    void typeCheck();
    void genCode();
};

class SeqNode : public StmtNode
{
private:
    StmtNode *stmt1, *stmt2;
public:
    SeqNode(StmtNode *stmt1, StmtNode *stmt2) : stmt1(stmt1), stmt2(stmt2){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class DeclStmt : public StmtNode
{
private:
    Id *id;
    ExprNode* expr;
public:
    DeclStmt(Id* id, ExprNode* expr = nullptr) : id(id) {
        if (expr) {
            this->expr = expr;
        }
    };
    Id* getId() {return id;};
    void output(int level);
    void typeCheck();
    void genCode();
};

class IfStmt : public StmtNode
{
private:
    ExprNode *cond;
    StmtNode *thenStmt;
public:
    IfStmt(ExprNode *cond, StmtNode *thenStmt) : cond(cond), thenStmt(thenStmt){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class IfElseStmt : public StmtNode
{
private:
    ExprNode *cond;
    StmtNode *thenStmt;
    StmtNode *elseStmt;
public:
    IfElseStmt(ExprNode *cond, StmtNode *thenStmt, StmtNode *elseStmt) : cond(cond), thenStmt(thenStmt), elseStmt(elseStmt) {};
    void output(int level);
    void typeCheck();
    void genCode();
};

class WhileStmt : public StmtNode {
private:
    ExprNode *cond;
    StmtNode *stmt;
    BasicBlock *cond_bb;
    BasicBlock *end_bb;
public:
    WhileStmt(ExprNode* cond, StmtNode* stmt=nullptr) : cond(cond), stmt(stmt) {};
    void output(int level);
    void setStmt(StmtNode* stmt){this->stmt = stmt;};
    void typeCheck();
    void genCode();
    BasicBlock* get_cond_bb(){return this->cond_bb;};
    BasicBlock* get_end_bb(){return this->end_bb;};
};

class BreakStmt : public StmtNode {
    private:
    StmtNode * whileStmt;
   public:
    BreakStmt(StmtNode* whileStmt){this->whileStmt=whileStmt;};
    void output(int level);
    void typeCheck();
    void genCode();
};

class ContinueStmt : public StmtNode {
private:
    StmtNode *whileStmt;
public:
    ContinueStmt(StmtNode* whileStmt){this->whileStmt=whileStmt;};
    void output(int level);
    void typeCheck();
    void genCode();
};

class ReturnStmt : public StmtNode
{
private:
    ExprNode *retValue;
public:
    ReturnStmt(ExprNode*retValue=nullptr) : retValue(retValue) {};
    void output(int level);
    void typeCheck();
    void genCode();
};

class AssignStmt : public StmtNode
{
private:
    ExprNode *lval;
    ExprNode *expr;
public:
    AssignStmt(ExprNode *lval, ExprNode *expr) : lval(lval), expr(expr) {};
    void output(int level);
    void typeCheck();
    void genCode();
};

class ExprStmt : public StmtNode {
private:
    ExprNode* expr;
public:
    ExprStmt(ExprNode* expr) : expr(expr){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class BlankStmt : public StmtNode {
   public:
    BlankStmt(){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class FunctionDef : public StmtNode
{
private:
    SymbolEntry *se;
    DeclStmt *decl;
    StmtNode *stmt;
public:
    FunctionDef(SymbolEntry *se, DeclStmt *decl, StmtNode *stmt) : se(se), decl(decl), stmt(stmt){};
    void output(int level);
    void typeCheck();
    void genCode();
};

class Ast
{
private:
    Node* root;
public:
    Ast() {root = nullptr;}
    void setRoot(Node*n) {root = n;}
    void output();
    void typeCheck();
    void genCode(Unit *unit);
};

#endif
