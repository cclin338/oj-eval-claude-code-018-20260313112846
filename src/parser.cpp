/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 *
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    // Check if the first element is a symbol
    // If not, use Apply function to package to a closure;
   //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // Not a symbol, treat as function application
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), parameters));
    }

    string op = id->s;

    // Check if it's a variable in the environment
    if (find(op, env).get() != nullptr) {
        // It's a defined variable, treat as function application
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), parameters));
    }

    // Check if it's a primitive
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }

        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1]));
            } else {
                return Expr(new PlusVar(parameters));
            }
        } else if (op_type == E_MINUS) {
            if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                return Expr(new MinusVar(parameters));
            }
        } else if (op_type == E_MUL) {
            if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                return Expr(new MultVar(parameters));
            }
        }  else if (op_type == E_DIV) {
            if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                return Expr(new DivVar(parameters));
            }
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_EXPT) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for expt");
            }
            return Expr(new Expt(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                return Expr(new LessVar(parameters));
            }
        } else if (op_type == E_LE) {
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                return Expr(new LessEqVar(parameters));
            }
        } else if (op_type == E_EQ) {
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }
        } else if (op_type == E_GE) {
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterEqVar(parameters));
            }
        } else if (op_type == E_GT) {
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterVar(parameters));
            }
        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-car!");
            }
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-cdr!");
            }
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_EQQ) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for eq?");
            }
            return Expr(new IsEq(parameters[0], parameters[1]));
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for boolean?");
            }
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for number?");
            }
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for null?");
            }
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for pair?");
            }
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for procedure?");
            }
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for symbol?");
            }
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for list?");
            }
            return Expr(new IsList(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for string?");
            }
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_VOID) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for void");
            }
            return Expr(new MakeVoid());
        } else if (op_type == E_EXIT) {
            if (parameters.size() != 0) {
                throw RuntimeError("Wrong number of arguments for exit");
            }
            return Expr(new Exit());
        } else if (op_type == E_DISPLAY) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for display");
            }
            return Expr(new Display(parameters[0]));
        }
        throw RuntimeError("Unhandled primitive: " + op);
    }

    // Check if it's a reserved word
    if (reserved_words.count(op) != 0) {
        switch (reserved_words[op]) {
            case E_BEGIN: {
                vector<Expr> body;
                for (size_t i = 1; i < stxs.size(); i++) {
                    body.push_back(stxs[i]->parse(env));
                }
                return Expr(new Begin(body));
            }
            case E_QUOTE: {
                if (stxs.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                return Expr(new Quote(stxs[1]));
            }
            case E_IF: {
                if (stxs.size() != 4) {
                    throw RuntimeError("Wrong number of arguments for if");
                }
                return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env), stxs[3]->parse(env)));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List *clause_list = dynamic_cast<List*>(stxs[i].get());
                    if (!clause_list) {
                        throw RuntimeError("cond clause must be a list");
                    }
                    vector<Expr> clause;
                    for (size_t j = 0; j < clause_list->stxs.size(); j++) {
                        clause.push_back(clause_list->stxs[j]->parse(env));
                    }
                    clauses.push_back(clause);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                if (stxs.size() < 3) {
                    throw RuntimeError("lambda requires at least 2 arguments");
                }
                // Parse parameter list
                List *param_list = dynamic_cast<List*>(stxs[1].get());
                if (!param_list) {
                    throw RuntimeError("lambda parameter list must be a list");
                }
                vector<string> params;
                for (size_t i = 0; i < param_list->stxs.size(); i++) {
                    SymbolSyntax *param = dynamic_cast<SymbolSyntax*>(param_list->stxs[i].get());
                    if (!param) {
                        throw RuntimeError("lambda parameter must be a symbol");
                    }
                    params.push_back(param->s);
                }
                // Parse body
                vector<Expr> body;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body.push_back(stxs[i]->parse(env));
                }
                return Expr(new Lambda(params, Expr(new Begin(body))));
            }
            case E_DEFINE: {
                if (stxs.size() < 3) {
                    throw RuntimeError("define requires at least 2 arguments");
                }
                // Check if it's a function definition shorthand or variable definition
                SymbolSyntax *var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                List *func_def = dynamic_cast<List*>(stxs[1].get());

                if (var_sym) {
                    // Variable definition: (define var expr ...)
                    if (primitives.count(var_sym->s) || reserved_words.count(var_sym->s)) {
                        throw RuntimeError("Cannot redefine keyword: " + var_sym->s);
                    }
                    vector<Expr> body;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        body.push_back(stxs[i]->parse(env));
                    }
                    return Expr(new Define(var_sym->s, Expr(new Begin(body))));
                } else if (func_def && !func_def->stxs.empty()) {
                    // Function definition shorthand: (define (name params...) body ...)
                    SymbolSyntax *func_name = dynamic_cast<SymbolSyntax*>(func_def->stxs[0].get());
                    if (!func_name) {
                        throw RuntimeError("Function name must be a symbol");
                    }
                    if (primitives.count(func_name->s) || reserved_words.count(func_name->s)) {
                        throw RuntimeError("Cannot redefine keyword: " + func_name->s);
                    }
                    vector<string> params;
                    for (size_t i = 1; i < func_def->stxs.size(); i++) {
                        SymbolSyntax *param = dynamic_cast<SymbolSyntax*>(func_def->stxs[i].get());
                        if (!param) {
                            throw RuntimeError("Function parameter must be a symbol");
                        }
                        params.push_back(param->s);
                    }
                    vector<Expr> body;
                    for (size_t i = 2; i < stxs.size(); i++) {
                        body.push_back(stxs[i]->parse(env));
                    }
                    return Expr(new Define(func_name->s, Expr(new Lambda(params, Expr(new Begin(body))))));
                } else {
                    throw RuntimeError("Invalid define syntax");
                }
            }
            case E_LET: {
                if (stxs.size() < 3) {
                    throw RuntimeError("let requires at least 2 arguments");
                }
                List *bindings = dynamic_cast<List*>(stxs[1].get());
                if (!bindings) {
                    throw RuntimeError("let bindings must be a list");
                }
                vector<pair<string, Expr>> bind;
                for (size_t i = 0; i < bindings->stxs.size(); i++) {
                    List *binding = dynamic_cast<List*>(bindings->stxs[i].get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("let binding must be a list of 2 elements");
                    }
                    SymbolSyntax *var = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var) {
                        throw RuntimeError("let variable must be a symbol");
                    }
                    bind.push_back(mp(var->s, binding->stxs[1]->parse(env)));
                }
                vector<Expr> body;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body.push_back(stxs[i]->parse(env));
                }
                return Expr(new Let(bind, Expr(new Begin(body))));
            }
            case E_LETREC: {
                if (stxs.size() < 3) {
                    throw RuntimeError("letrec requires at least 2 arguments");
                }
                List *bindings = dynamic_cast<List*>(stxs[1].get());
                if (!bindings) {
                    throw RuntimeError("letrec bindings must be a list");
                }
                // Create a placeholder environment with all variables bound to nullptr
                Assoc letrec_env = env;
                vector<string> var_names;
                for (size_t i = 0; i < bindings->stxs.size(); i++) {
                    List *binding = dynamic_cast<List*>(bindings->stxs[i].get());
                    if (!binding || binding->stxs.size() != 2) {
                        throw RuntimeError("letrec binding must be a list of 2 elements");
                    }
                    SymbolSyntax *var = dynamic_cast<SymbolSyntax*>(binding->stxs[0].get());
                    if (!var) {
                        throw RuntimeError("letrec variable must be a symbol");
                    }
                    var_names.push_back(var->s);
                    letrec_env = extend(var->s, Value(nullptr), letrec_env);
                }
                // Now parse all bindings in the letrec environment
                vector<pair<string, Expr>> bind;
                for (size_t i = 0; i < bindings->stxs.size(); i++) {
                    List *binding = dynamic_cast<List*>(bindings->stxs[i].get());
                    Expr expr = binding->stxs[1]->parse(letrec_env);
                    bind.push_back(mp(var_names[i], expr));
                }
                vector<Expr> body;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body.push_back(stxs[i]->parse(letrec_env));
                }
                return Expr(new Letrec(bind, Expr(new Begin(body))));
            }
            case E_SET: {
                if (stxs.size() != 3) {
                    throw RuntimeError("set! requires exactly 2 arguments");
                }
                SymbolSyntax *var = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var) {
                    throw RuntimeError("set! variable must be a symbol");
                }
                return Expr(new Set(var->s,  stxs[2]->parse(env)));
            }
            default:
                throw RuntimeError("Unknown reserved word: " + op);
        }
    }

    // Default: use Apply to be an expression (function application)
    vector<Expr> parameters;
    for (size_t i = 1; i < stxs.size(); i++) {
        parameters.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(stxs[0]->parse(env), parameters));
}
