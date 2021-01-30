// -------------------------------------------------------------
// 1. Syntax
// -------------------------------------------------------------
type VarName = string
// Syntax:
//
// τ := Int | Bool | τ1->τ2
// e ::= x | λx : τe | e1 · e2 | true | false | if e then e1 else e2
// v ::= true | false | λx : τ.e
// E ::= [·] | Ee | vE | if E then e1 else e2
type Type1Type2 = Type -> Type

datatype Type = Int | Bool | Type1Type2

datatype Exp =
    | Var(x: VarName)
    //| λx : τe 是什么定义
    | Mul(e1 :Exp, e2:Exp)
    | Cond(e: Exp, e1: Exp, e2: Exp)

datatype Value =
    | TrueB()
    | FalseB()
    //| λx : τ.e 是什么定义

datatype Eva = //这个我完全没看懂。。
    | 
    |
    | 
    | CondC(E:Eva, e1 : Exp, e2 : Exp)

predicate isVar(e: Exp)
{
    match e {
        case Var(x) => true
        //case 
        case Mul(e1,e2) => false
        case Cond(e1, e2, e3) => false
    }
}
function FV(e: Exp): set<VarName> {
    match(e) {
        case Var(x) => {x}
       // case 
        case Mul(e1, e2) => FV(e1) * FV(e2)
        case Cond(e, e1, e2) => FV(e) + FV(e1) + FV(e2)
    }
}
// An environment is a partial mapping from variables to types
type Env = map<VarName, Type>
predicate hasTypeExp(gamma: Env, e: Exp, t: Type)


// -------------------------------------------------------------
// 2. Small-step semantics
// -------------------------------------------------------------


// -------------------------------------------------------------
// 3. Typing rules system
// -------------------------------------------------------------