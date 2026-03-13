/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 *
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp"
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

// Helper function to calculate GCD
static int gcd(int a, int b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

// Helper function to add rational numbers / integers
static Value addValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(v1.get())->n + dynamic_cast<Integer*>(v2.get())->n);
    } else if (v1->v_type == V_RATIONAL || v2->v_type == V_RATIONAL) {
        int num1, den1, num2, den2;
        if (v1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(v1.get())->n;
            den1 = 1;
        } else {
            Rational* r1 = dynamic_cast<Rational*>(v1.get());
            num1 = r1->numerator;
            den1 = r1->denominator;
        }
        if (v2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(v2.get())->n;
            den2 = 1;
        } else {
            Rational* r2 = dynamic_cast<Rational*>(v2.get());
            num2 = r2->numerator;
            den2 = r2->denominator;
        }
        int num = num1 * den2 + num2 * den1;
        int den = den1 * den2;
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in addition");
}

static Value subtractValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(v1.get())->n - dynamic_cast<Integer*>(v2.get())->n);
    } else if (v1->v_type == V_RATIONAL || v2->v_type == V_RATIONAL) {
        int num1, den1, num2, den2;
        if (v1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(v1.get())->n;
            den1 = 1;
        } else {
            Rational* r1 = dynamic_cast<Rational*>(v1.get());
            num1 = r1->numerator;
            den1 = r1->denominator;
        }
        if (v2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(v2.get())->n;
            den2 = 1;
        } else {
            Rational* r2 = dynamic_cast<Rational*>(v2.get());
            num2 = r2->numerator;
            den2 = r2->denominator;
        }
        int num = num1 * den2 - num2 * den1;
        int den = den1 * den2;
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in subtraction");
}

static Value multiplyValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        return IntegerV(dynamic_cast<Integer*>(v1.get())->n * dynamic_cast<Integer*>(v2.get())->n);
    } else if (v1->v_type == V_RATIONAL || v2->v_type == V_RATIONAL) {
        int num1, den1, num2, den2;
        if (v1->v_type == V_INT) {
            num1 = dynamic_cast<Integer*>(v1.get())->n;
            den1 = 1;
        } else {
            Rational* r1 = dynamic_cast<Rational*>(v1.get());
            num1 = r1->numerator;
            den1 = r1->denominator;
        }
        if (v2->v_type == V_INT) {
            num2 = dynamic_cast<Integer*>(v2.get())->n;
            den2 = 1;
        } else {
            Rational* r2 = dynamic_cast<Rational*>(v2.get());
            num2 = r2->numerator;
            den2 = r2->denominator;
        }
        int num = num1 * num2;
        int den = den1 * den2;
        return RationalV(num, den);
    }
    throw RuntimeError("Wrong typename in multiplication");
}

static Value divideValues(const Value &v1, const Value &v2) {
    int num1, den1, num2, den2;
    if (v1->v_type == V_INT) {
        num1 = dynamic_cast<Integer*>(v1.get())->n;
        den1 = 1;
    } else if (v1->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        num1 = r1->numerator;
        den1 = r1->denominator;
    } else {
        throw RuntimeError("Wrong typename in division");
    }

    if (v2->v_type == V_INT) {
        num2 = dynamic_cast<Integer*>(v2.get())->n;
        den2 = 1;
    } else if (v2->v_type == V_RATIONAL) {
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        num2 = r2->numerator;
        den2 = r2->denominator;
    } else {
        throw RuntimeError("Wrong typename in division");
    }

    if (num2 == 0) {
        throw RuntimeError("Division by zero");
    }

    int num = num1 * den2;
    int den = den1 * num2;
    return RationalV(num, den);
}

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive
    std::vector<Value> values;
    for (const auto &r : rands) {
        values.push_back(r->eval(e));
    }
    return evalRator(values);
}

Value Var::eval(Assoc &e) { // evaluation of variable
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                {E_VOID,     {new MakeVoid(), {}}},
                {E_EXIT,     {new Exit(), {}}},
                {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                {E_LISTQ,    {new IsList(new Var("parm")), {"parm"}}},
                {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                {E_PLUS,     {new PlusVar({}),  {}}},
                {E_MINUS,    {new MinusVar({}), {}}},
                {E_MUL,      {new MultVar({}),  {}}},
                {E_DIV,      {new DivVar({}),   {}}},
                {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_EQQ,      {new IsEq(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_CONS,     {new Cons(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_CAR,      {new Car(new Var("parm")), {"parm"}}},
                {E_CDR,      {new Cdr(new Var("parm")), {"parm"}}},
                {E_LIST,     {new ListFunc({}), {}}},
                {E_SETCAR,   {new SetCar(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_SETCDR,   {new SetCdr(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                {E_NOT,      {new Not(new Var("parm")), {"parm"}}},
                {E_AND,      {new AndVar({}), {}}},
                {E_OR,       {new OrVar({}), {}}},
                {E_LT,       {new LessVar({}), {}}},
                {E_LE,       {new LessEqVar({}), {}}},
                {E_GE,       {new GreaterEqVar({}), {}}},
                {E_GT,       {new GreaterVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            if (it != primitive_map.end()) {
                return ProcedureV(it->second.second, it->second.first, e);
            }
        }
        throw RuntimeError("Undefined variable: " + x);
    }
    // Check if value is nullptr (defined but unusable in letrec)
    if (matched_value.get() != nullptr && matched_value.get()->v_type == V_VOID &&
        dynamic_cast<Void*>(matched_value.get()) == nullptr) {
        throw RuntimeError("Variable used before initialization");
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    return addValues(rand1, rand2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    return subtractValues(rand1, rand2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    return multiplyValues(rand1, rand2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    return divideValues(rand1, rand2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args
    if (args.empty()) {
        return IntegerV(0);
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = addValues(result, args[i]);
    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args
    if (args.empty()) {
        throw RuntimeError("- requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Unary minus
        if (args[0]->v_type == V_INT) {
            return IntegerV(-dynamic_cast<Integer*>(args[0].get())->n);
        } else if (args[0]->v_type == V_RATIONAL) {
            Rational* r = dynamic_cast<Rational*>(args[0].get());
            return RationalV(-r->numerator, r->denominator);
        }
        throw RuntimeError("Wrong typename");
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = subtractValues(result, args[i]);
    }
    return result;
}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args
    if (args.empty()) {
        return IntegerV(1);
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = multiplyValues(result, args[i]);
    }
    return result;
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    if (args.empty()) {
        throw RuntimeError("/ requires at least 1 argument");
    }
    if (args.size() == 1) {
        // Reciprocal
        return divideValues(IntegerV(1), args[0]);
    }
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = divideValues(result, args[i]);
    }
    return result;
}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;

        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }

        long long result = 1;
        long long b = base;
        int exp = exponent;

        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }

        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        long long left = (long long)r1->numerator;
        long long right = (long long)n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        long long left = (long long)n1 * r2->denominator;
        long long right = (long long)r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        long long left = (long long)r1->numerator * r2->denominator;
        long long right = (long long)r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    return BooleanV(compareNumericValues(rand1, rand2) <= 0);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    if (args.size() < 2) {
        throw RuntimeError("< requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    if (args.size() < 2) {
        throw RuntimeError("<= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    if (args.size() < 2) {
        throw RuntimeError("= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    if (args.size() < 2) {
        throw RuntimeError(">= requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    if (args.size() < 2) {
        throw RuntimeError("> requires at least 2 arguments");
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return PairV(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = PairV(args[i], result);
    }
    return result;
}

Value IsList::evalRator(const Value &rand) { // list?
    if (rand->v_type == V_NULL) {
        return BooleanV(true);
    }
    if (rand->v_type != V_PAIR) {
        return BooleanV(false);
    }
    // Check if it's a proper list
    Value curr = rand;
    while (curr->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(curr.get());
        curr = p->cdr;
    }
    return BooleanV(curr->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("car requires a pair");
    }
    return dynamic_cast<Pair*>(rand.get())->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("cdr requires a pair");
    }
    return dynamic_cast<Pair*>(rand.get())->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-car! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;
    return VoidV();
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("set-cdr! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;
    return VoidV();
}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // Check if type is Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // Check if type is Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // Check if type is Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // Check if type is Null or Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

// Helper function to convert Syntax to Value
Value syntaxToValue(Syntax s);

Value syntaxToValue(Syntax s) {
    Number *num = dynamic_cast<Number*>(s.get());
    if (num) {
        return IntegerV(num->n);
    }

    RationalSyntax *rat = dynamic_cast<RationalSyntax*>(s.get());
    if (rat) {
        return RationalV(rat->numerator, rat->denominator);
    }

    TrueSyntax *t = dynamic_cast<TrueSyntax*>(s.get());
    if (t) {
        return BooleanV(true);
    }

    FalseSyntax *f = dynamic_cast<FalseSyntax*>(s.get());
    if (f) {
        return BooleanV(false);
    }

    SymbolSyntax *sym = dynamic_cast<SymbolSyntax*>(s.get());
    if (sym) {
        return SymbolV(sym->s);
    }

    StringSyntax *str = dynamic_cast<StringSyntax*>(s.get());
    if (str) {
        return StringV(str->s);
    }

    List *lst = dynamic_cast<List*>(s.get());
    if (lst) {
        if (lst->stxs.empty()) {
            return NullV();
        }
        Value result = NullV();
        for (int i = lst->stxs.size() - 1; i >= 0; i--) {
            result = PairV(syntaxToValue(lst->stxs[i]), result);
        }
        return result;
    }

    throw RuntimeError("Unknown syntax type in quote");
}

Value Begin::eval(Assoc &e) {
    if (es.empty()) {
        return VoidV();
    }
    Value result = VoidV();
    for (size_t i = 0; i < es.size(); i++) {
        result = es[i]->eval(e);
    }
    return result;
}

Value Quote::eval(Assoc& e) {
    return syntaxToValue(s);
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(true);
    }
    Value result = BooleanV(true);
    for (size_t i = 0; i < rands.size(); i++) {
        result = rands[i]->eval(e);
        // In Scheme, anything other than #f is true
        if (result->v_type == V_BOOL && !dynamic_cast<Boolean*>(result.get())->b) {
            return BooleanV(false);
        }
    }
    return result;
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    if (rands.empty()) {
        return BooleanV(false);
    }
    for (size_t i = 0; i < rands.size(); i++) {
        Value result = rands[i]->eval(e);
        // In Scheme, anything other than #f is true
        if (result->v_type != V_BOOL || dynamic_cast<Boolean*>(result.get())->b) {
            return result;
        }
    }
    // All values were #f
    Value last_result = rands[rands.size() - 1]->eval(e);
    return last_result;
}

Value Not::evalRator(const Value &rand) { // not
    if (rand->v_type == V_BOOL && !dynamic_cast<Boolean*>(rand.get())->b) {
        return BooleanV(true);
    }
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    Value cond_val = cond->eval(e);
    // In Scheme, anything other than #f is true
    if (cond_val->v_type == V_BOOL && !dynamic_cast<Boolean*>(cond_val.get())->b) {
        return alter->eval(e);
    }
    return conseq->eval(e);
}

Value Cond::eval(Assoc &env) {
    for (size_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].empty()) {
            throw RuntimeError("cond clause cannot be empty");
        }

        // Check if this is an else clause
        Var *else_var = dynamic_cast<Var*>(clauses[i][0].get());
        if (else_var && else_var->x == "else") {
            // This is the else clause
            if (clauses[i].size() == 1) {
                return BooleanV(true);
            }
            Value result = VoidV();
            for (size_t j = 1; j < clauses[i].size(); j++) {
                result = clauses[i][j]->eval(env);
            }
            return result;
        }

        // Evaluate the condition
        Value cond_val = clauses[i][0]->eval(env);

        // Check if condition is true
        if (cond_val->v_type != V_BOOL || dynamic_cast<Boolean*>(cond_val.get())->b) {
            // Condition is true
            if (clauses[i].size() == 1) {
                return cond_val;
            }
            Value result = VoidV();
            for (size_t j = 1; j < clauses[i].size(); j++) {
                result = clauses[i][j]->eval(env);
            }
            return result;
        }
    }
    // No clause matched
    return VoidV();
}

Value Lambda::eval(Assoc &env) {
    return ProcedureV(x, e, env);
}

Value Apply::eval(Assoc &e) {
    Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }

    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());

    // Evaluate arguments
    std::vector<Value> args;
    for (size_t i = 0; i < rand.size(); i++) {
        args.push_back(rand[i]->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()) {
        throw RuntimeError("Wrong number of arguments");
    }

    // Create new environment with parameters bound to arguments
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < args.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // Check if it's a recursive function definition
    Lambda *lambda_expr = dynamic_cast<Lambda*>(e.get());
    if (lambda_expr) {
        // For recursive functions, first bind the variable to a placeholder
        Assoc new_env = extend(var, Value(nullptr), env);
        Value proc_val = e->eval(new_env);
        modify(var, proc_val, new_env);
        // Update the global environment
        modify(var, proc_val, env);
        if (find(var, env).get() == nullptr) {
            env = extend(var, proc_val, env);
        }
    } else {
        Value val = e->eval(env);
        if (find(var, env).get() != nullptr) {
            modify(var, val, env);
        } else {
            env = extend(var, val, env);
        }
    }
    return VoidV();
}

Value Let::eval(Assoc &env) {
    // Evaluate all bindings in the current environment
    std::vector<Value> values;
    for (const auto &b : bind) {
        values.push_back(b.second->eval(env));
    }

    // Create new environment with bindings
    Assoc new_env = env;
    for (size_t i = 0; i < bind.size(); i++) {
        new_env = extend(bind[i].first, values[i], new_env);
    }

    // Evaluate body in new environment
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // Create environment with all variables bound to nullptr (unusable)
    Assoc new_env = env;
    for (const auto &b : bind) {
        new_env = extend(b.first, Value(nullptr), new_env);
    }

    // Evaluate all bindings in the new environment
    for (const auto &b : bind) {
        Value val = b.second->eval(new_env);
        modify(b.first, val, new_env);
    }

    // Evaluate body
    return body->eval(new_env);
}

Value Set::eval(Assoc &env) {
    Value val = e->eval(env);
    Value existing = find(var, env);
    if (existing.get() == nullptr) {
        throw RuntimeError("set! variable not defined: " + var);
    }
    modify(var, val, env);
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }

    return VoidV();
}
