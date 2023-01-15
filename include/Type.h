#ifndef __TYPE_H__
#define __TYPE_H__
#include <vector>
#include <string>
#include "SymbolTable.h"
#include "Ast.h"

class Type
{
private:
    int kind;
protected:
    enum {INT, VOID, FUNC, PTR, BOOL, ARRAY, FLOAT};
    int size;
public:
    Type(int kind, int size = 0) : kind(kind), size(size){};
    virtual ~Type() {};
    virtual std::string toStr() = 0;
    bool isInt() const {return kind == INT;};
    bool isVoid() const {return kind == VOID;};
    bool isFunc() const {return kind == FUNC;};
    bool isBool() const {return kind == BOOL;};
    bool isArray() const {return kind == ARRAY;};
    bool isPtr() const {return kind == PTR;};
    bool isFloat() const {return kind == FLOAT;}
    int getSize() const {return size;};
    int getKind() const {return kind;};
};

class IntType : public Type
{
private:
    bool constant;
public:
    IntType(int size, bool constant = false) : Type(Type::INT, size), constant(constant){};
    std::string toStr();
    bool isConst() const {return constant;};
};

class VoidType : public Type
{
public:
    VoidType() : Type(Type::VOID){};
    std::string toStr();
};

class FunctionType : public Type
{
private:
    Type *returnType;
    std::vector<Type*> paramsType;
    std::vector<SymbolEntry*> paramsSe;
public:
    FunctionType(Type* returnType, std::vector<Type*> paramsType, std::vector<SymbolEntry*> paramsSe) : 
    Type(Type::FUNC), returnType(returnType), paramsType(paramsType), paramsSe(paramsSe){};
    Type* getRetType() {return returnType;};
    std::vector<Type*> getParamsType() {return paramsType;};
    std::vector<SymbolEntry*> getParamsSe() {return paramsSe;};
    std::string toStr();
};

class ArrayType : public Type {
private:
    Type* elementType;
    Type* arrayType = nullptr;
    int length;
    bool constant;
public:
    ArrayType(Type* elementType, int length, bool constant = false)
        : Type(Type::ARRAY),
          elementType(elementType),
          length(length),
          constant(constant) {
        size = elementType->getSize() * length;
    };
    std::string toStr();
    int getLength() const { return length; };
    Type* getElementType() const { return elementType; };
    void setArrayType(Type* arrayType) { this->arrayType = arrayType; };
    bool isConst() const { return constant; };
    Type* getArrayType() const { return arrayType; };
};

class PointerType : public Type
{
private:
    Type *valueType;
public:
    PointerType(Type* valueType) : Type(Type::PTR) {this->valueType = valueType;};
    std::string toStr();
    Type* getValueType() const {return valueType;};
};

class FloatType : public Type {
private:
    bool constant;
public:
    FloatType(int size, bool constant = false) : Type(Type::FLOAT, size), constant(constant){};
    std::string toStr();
    bool isConst() const {return constant;};
};

class TypeSystem
{
private:
    static IntType commonInt;
    static VoidType commonVoid;
    static IntType commonBool;
    static IntType commonConstInt;
    static FloatType commonFloat;
    static FloatType commonConstFloat;
public:
    static Type *intType;
    static Type *voidType;
    static Type *boolType;
    static Type *constIntType;
    static Type *floatType;
    static Type *constFloatType;
};

#endif