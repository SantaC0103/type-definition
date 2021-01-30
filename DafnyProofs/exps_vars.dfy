/**
 * --------------------------------------
 * Static Analysis and Constraint Solving
 * Lesson 3: Type-based analysis
 * --------------------------------------
 *
 *          Manuel Montenegro
 *
 * This module defines an expression language, its small-step semantics,
 * a type system and its proof of correctness.
 * 
 */


// -------------------------------------------------------------
// 1. Syntax
// -------------------------------------------------------------
type VarName = string

// Syntax of expressions and values:
//
// e := v | x | e1 + e2 | e1 <= e2 | e1 ? e2 : e3
// v := n | true | false

datatype Exp =
      Val(v: Value)
    | Var(x: VarName)
    | Add(e1: Exp, e2: Exp)
    | Leq(e1: Exp, e2: Exp)
    | Cond(e1: Exp, e2: Exp, e3: Exp)

datatype Value =
    | Const(n: int)
    | TrueB()
    | FalseB()
  
    

// Syntax of types:
//
// τ := Int | Bool

datatype Type = Int | Bool

// The following predicate determines if a given expression
// is a value.
predicate isValue(e: Exp)
{
    match e {
        case Val(x) => true
        case Var(n) => false
        case Add(e1, e2) => false
        case Leq(e1, e2) => false
        case Cond(e1, e2, e3) => false
    }
}

// The following functiong returns the free variables
// in a expression

function FV(e: Exp): set<VarName> {
    match(e) {
        case Val(v) => {}
        case Var(x) => {x}
        case Add(e1, e2) => FV(e1) + FV(e2)
        case Leq(e1, e2) => FV(e1) + FV(e2)
        case Cond(e1, e2, e3) => FV(e1) + FV(e2) + FV(e3)
    }
}



// -------------------------------------------------------------
// 2. Small-step semantics
// -------------------------------------------------------------

// A state σ is an assignment of values to variables
type State = VarName -> Value


// Definition of state update: σ[x ↦ v]
function changeState(st: State, x: VarName, v: Value) : State {
    y => if y == x then v else st(y)
}

//
// We have judgements of the form σ ⊢ e --> e', meaning that under
// the state σ, the expression e is reduced in one evaluation step
// into another expression e'.
//
// 
//    ------------------- [Var]
//      σ ⊢ x --> σ(x)
//
//          σ ⊢ e1 --> e1'
//    ---------------------------- [Add1]
//      σ ⊢ e1 + e2 --> e1' + e2
//
//          σ ⊢ e2 --> e2'
//    ---------------------------- [Add2]
//      σ ⊢ n1 + e2 --> n1 + e2'
//
//    ---------------------------- [Add3]
//      σ ⊢ n1 + n2 --> n1 +Z n2
//
//          σ ⊢ e1 --> e1'
//    ---------------------------- [Leq1]
//      σ ⊢ e1 <= e2 --> e1' <= e2
//
//          σ ⊢ e2 --> e2'
//    ---------------------------- [Leq2]
//      σ ⊢ n1 <= e2 --> n1 <= e2'
//
//             n1 <=Z n2
//    ---------------------------- [Leq3]
//       σ ⊢ n1 <= n2 --> true
//
//             ¬(n1 <=Z n2)
//    ---------------------------- [Leq4]
//       σ ⊢ n1 <= n2 --> false
//
//               σ ⊢ e1 --> e1'
//    -------------------------------------- [Cond1]
//      σ ⊢ e1 ? e2 : e3 --> e1' ? e2 : e3
//
//
//    ------------------------------ [Cond2]
//      σ ⊢ true ? e2 : e3 --> e2
//
//
//    ------------------------------ [Cond3]
//      σ ⊢ false ? e2 : e3 --> e3

predicate smallStep(s: State, e: Exp, e': Exp)
{
    match e {
        case Val(v) => false
        case Var(x) => e' == Val(s(x))
        case Add(e1, e2) =>
                exists e1' :: smallStep(s, e1, e1') && e' == Add(e1', e2)
           ||
                exists n1, e2' :: e1 == Val(Const(n1)) && smallStep(s, e2, e2') && e' == Add(Val(Const(n1)), e2')
            ||
                exists n1, n2 :: e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && e' == Val(Const(n1 + n2))
        case Leq(e1, e2) =>
                exists e1' :: smallStep(s, e1, e1') && e' == Leq(e1', e2)
            ||
                exists n1, e2' :: e1 == Val(Const(n1)) && smallStep(s, e2, e2') && e' == Leq(Val(Const(n1)), e2')
            ||
                exists n1, n2 :: e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && n1 <= n2 && e' == Val(TrueB())
            ||
                exists n1, n2 :: e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && !(n1 <= n2) && e' == Val(FalseB())

        case Cond(e1, e2, e3) =>
                exists e1' :: smallStep(s, e1, e1') && e' == Cond(e1', e2, e3)
            ||
                (e1 == Val(TrueB()) && e' == e2)
            ||
                (e1 == Val(FalseB()) && e' == e3)
    }
}

// -------------------------------------------------------------
// 3. Type system
// -------------------------------------------------------------

// An environment is a partial mapping from variables to types
type Env = map<VarName, Type>

// We have judgements of the form Γ ⊢ e :: τ
//
//  ------------------------ [CONST]
//       Γ ⊢ n :: Int
//
//  ------------------------ [TRUE]
//      Γ ⊢ true :: Bool
//
//  ------------------------ [FALSE]
//      Γ ⊢ false :: Bool
//
//
//  ------------------------ [VAR]
//      Γ ⊢ x :: Γ(x)
//
//   Γ ⊢ e1 :: Int  Γ ⊢ e2 :: Int
//  ------------------------------ [ADD]
//      Γ ⊢ e1 + e2 :: Int
//
//   Γ ⊢ e1 :: Int  Γ ⊢ e2 :: Int
//  ------------------------------ [LEQ]
//      Γ ⊢ e1 <= e2 :: Bool
//
//   Γ ⊢ e1 :: Bool  Γ ⊢ e2 :: τ    Γ ⊢ e3 :: τ
//  ---------------------------------------------- [COND]
//                Γ ⊢ e1 ? e2 : e3 :: τ


// The predicate hasType(Γ, e, τ)  denotes a judgement Γ ⊢ e :: τ
predicate hasType(gamma: Env, e: Exp, t: Type)
{
    match e {
        case Val(Const(n)) => t == Int
        case Val(TrueB()) => t == Bool
        case Val(FalseB()) => t == Bool

        case Var(x) => x in gamma && t == gamma[x]
        
        case Add(e1, e2) => hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Int

        case Leq(e1, e2) => hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Bool

        case Cond(e1, e2, e3) => hasType(gamma, e1, Bool) && hasType(gamma, e2, t) && hasType(gamma, e3, t)
    }    
}

// Some properties on typing rules

// If Γ ⊢ e :: τ and x1 is a variable not occurring in e, then:
// Γ[x1 ↦ τ1] ⊢ e :: τ for any τ1
lemma {:induction false} extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma, e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma[x1 := t1], e, t)
{
    match e {
        case Val(v) => {
            assert hasType(gamma, e, t) ==> hasType(gamma[x1 := t1], e, t);
        }
        case Var(x) => {
            // Since x != x1, we know that Γ[x1 ↦ τ1](x) = Γ(x)
            assert x in FV(e);
            assert x != x1;
            assert gamma[x1 := t1][x] == gamma[x];
            assert hasType(gamma[x1 := t1], e, t);
        }
        
        case Add(e1, e2) =>  {
            calc {
                    hasType(gamma, e, t);
                ==> // by [ADD] typing rule 
                    hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Int;
                ==> { extendGamma(gamma, e1, Int, x1, t1); }  // by I.H. on e1
                    hasType(gamma[x1 := t1], e1, Int) && hasType(gamma, e2, Int) && t == Int;
                ==> { extendGamma(gamma, e2, Int, x1, t1); }   // by I.H. on e2
                    hasType(gamma[x1 := t1], e1, Int) && hasType(gamma[x1 := t1], e2, Int) && t == Int;
                ==> // by [ADD] typing rule
                    hasType(gamma[x1 := t1], e, Int) && t == Int;
                ==> 
                    hasType(gamma[x1 := t1], e, t);
            }

        }

        case Leq(e1, e2) =>  {
            calc {
                    hasType(gamma, e, t);
                ==>
                    hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Bool;
                ==> { extendGamma(gamma, e1, Int, x1, t1); }
                    hasType(gamma[x1 := t1], e1, Int) && hasType(gamma, e2, Int) && t == Bool;
                ==> { extendGamma(gamma, e2, Int, x1, t1); }
                    hasType(gamma[x1 := t1], e1, Int) && hasType(gamma[x1 := t1], e2, Int) && t == Bool;
                ==> 
                    hasType(gamma[x1 := t1], e, Bool) && t == Bool;
                ==> 
                    hasType(gamma[x1 := t1], e, t);
            }            
        }

        case Cond(e1, e2, e3) =>  {
            calc {
                    hasType(gamma, e, t);
                ==>
                    hasType(gamma, e1, Bool) && hasType(gamma, e2, t) && hasType(gamma, e3, t);
                ==> { extendGamma(gamma, e1, Bool, x1, t1); }
                    hasType(gamma[x1 := t1], e1, Bool) && hasType(gamma, e2, t) && hasType(gamma, e3, t);
                ==> { extendGamma(gamma, e2, t, x1, t1); }
                    hasType(gamma[x1 := t1], e1, Bool) && hasType(gamma[x1 := t1], e2, t) && hasType(gamma, e3, t);
                ==> { extendGamma(gamma, e3, t, x1, t1); }
                    hasType(gamma[x1 := t1], e1, Bool) && hasType(gamma[x1 := t1], e2, t) && hasType(gamma[x1 := t1], e3, t);
                ==> 
                    hasType(gamma[x1 := t1], e, t);
            }                           
        }
    }
}    

// If Γ[x1 ↦ τ1] ⊢ e :: τ and x1 is a variable not occurring in e, then:
// Γ ⊢ e :: τ
lemma removeGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasType(gamma[x1 := t1], e, t)
    requires x1 !in FV(e)
    ensures hasType(gamma, e, t)
{
    // It is very similar to the previous one.
    // In fact, Dafny can prove it by itself.
}


// Inversion lemma:
// If Γ ⊢ v :: τ, where v is a value, then v must be either True or False
lemma inversionBool(gamma: Env, v: Value)
    requires hasType(gamma, Val(v), Bool)
    ensures v == TrueB || v == FalseB
{
    // By inspection of the typing rules
}    

// -------------------------------------------------------------
// 4. Progress theorem
// -------------------------------------------------------------
//  For any σ, e: 
//  If there exist Γ, τ such that  Γ ⊢ e :: τ, then either e is
//  a value or there exists some e' such that σ ⊢ e --> e'
//

lemma progress(s: State, e: Exp)
    requires exists gamma, t :: hasType(gamma, e, t)
    ensures isValue(e) || (exists e' :: smallStep(s, e, e'))
{
    // Let Γ and τ be an environment and a type
    // under which the expression is well-typed
    var gamma, t :| hasType(gamma, e, t);

    // We prove it by structural induction on e
    // We distinguish cases depending on the expression
    match e {
        case Val(x) => {
            // A value is a value :-).
            // The theorem holds trivially.
            assert isValue(e);
        }

        case Var(x) => {
            // A variable is always reduced to its value.
            assert smallStep(s, e, Val(s(x)));
            assert exists e' :: smallStep(s, e, e');
        }

        case Add(e1, e2) => {
            // The only typing rule appliable is [ADD]
            // Therefore 
            //      Γ ⊢ e1 :: Int    Γ ⊢ e2 :: Int
            //      ------------------------------- [ADD]
            //              Γ ⊢ e :: Int
            assert hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Int;

            // Apply IH on e1. Either e1 is a value or it progresses. We distinguish
            // cases.
            progress(s, e1);
            assert isValue(e1) || (exists e1', sigma :: smallStep(sigma, e1, e1'));

            if (isValue(e1)) {
                // If it is a value, it must be a constant, by inspection
                // of the typing rules.
                assert exists n1 :: e1 == Val(Const(n1));
                var n1 :| e1 == Val(Const(n1));
                // Apply IH on e2. Either e2 is a value or it progresses. Again, we
                // distinguish cases:
                progress(s, e2);
                assert isValue(e2) || (exists e2' :: smallStep(s, e2, e2'));


                if (isValue(e2)) {
                    // If both e1 and e2 are values, they must be constants.
                    assert exists n2 :: e2 == Val(Const(n2));
                    var n2 :| e2 == Val(Const(n2));
                    // We can apply [Add3] and perform a computation step.
                    assert smallStep(s, e, Val(Const(n1 + n2)));
                    assert exists e' :: smallStep(s, e, e');
                } else {
                    // If e2 progresses to some e2', then we can apply [Add2]
                    var e2' :| smallStep(s, e2, e2');
                    // so as to get σ ⊢ e1 + e2 --> e1 + e2'
                    assert smallStep(s, Add(Val(Const(n1)), e2), Add(Val(Const(n1)), e2'));
                    assert smallStep(s, Add(e1, e2), Add(e1, e2'));
                    assert smallStep(s, e, Add(e1, e2'));
                    assert exists e' :: smallStep(s, e, e');
                }
            } else {
                // If e1 progresses to some e1', we can apply [Add1]
                var e1' :| smallStep(s, e1, e1');
                // so as to get σ ⊢ e1 + e2 --> e1' + e2
                assert smallStep(s, Add(e1, e2), Add(e1', e2));
                assert smallStep(s, e, Add(e1', e2));
                assert exists e' :: smallStep(s, e, e');
            }
        }

        case Leq(e1, e2) => {
            // The only typing rule appliable is [LEQ]
            // Therefore 
            //      Γ ⊢ e1 :: Int    Γ ⊢ e2 :: Int
            //      ------------------------------- [ADD]
            //              Γ ⊢ e :: Bool
            assert hasType(gamma, e1, Int) && hasType(gamma, e2, Int) && t == Bool;

            // Similar procedure, but now the result type is a boolean

            progress(s, e1);
            assert isValue(e1) || (exists e1' :: smallStep(s, e1, e1'));
            if (isValue(e1)) {
                assert exists n1 :: e1 == Val(Const(n1));
                var n1 :| e1 == Val(Const(n1));
                progress(s, e2);
                assert isValue(e2) || (exists e2' :: smallStep(s, e2, e2'));
                if (isValue(e2)) {
                    assert exists n2 :: e2 == Val(Const(n2));
                    var n2 :| e2 == Val(Const(n2));
                    if (n1 <= n2) {
                        assert smallStep(s, e, Val(TrueB));
                    } else {
                        assert smallStep(s, e, Val(FalseB));

                    }
                } else {
                    var e2' :| smallStep(s, e2, e2');
                    assert smallStep(s, Leq(Val(Const(n1)), e2), Leq(Val(Const(n1)), e2'));
                    assert smallStep(s, Leq(e1, e2), Leq(e1, e2'));
                    assert smallStep(s, e, Leq(e1, e2'));
                    assert exists e' :: smallStep(s, e, e');
                }
            } else {
                var e1' :| smallStep(s, e1, e1');
                assert smallStep(s, Leq(e1, e2), Leq(e1', e2));
                assert smallStep(s, e, Leq(e1', e2));
                assert exists e' :: smallStep(s, e, e');
            }
        }

        case Cond(e1, e2, e3) => {
            // The only typing rule appliable is [COND]
            // Therefore 
            //      Γ ⊢ e1 :: Bool    Γ ⊢ e2 :: τ     Γ ⊢ e3 :: τ
            //      ----------------------------------------------- [COND]
            //              Γ ⊢ e1 ? e2 : e3 :: τ

            assert hasType(gamma, e1, Bool) && hasType(gamma, e2, t) && hasType(gamma, e3, t);

            // Apply IH on e1. Either it is a value or progresses.
            progress(s, e1);
            assert isValue(e1) || (exists e1' :: smallStep(s, e1, e1'));

            if (isValue(e1)) {
                // If it is a value, it must be true or false,
                // we apply the corresponding rule in each case.
                assert e1 == Val(TrueB) || e1 == Val(FalseB);
                if (e1 == Val(TrueB)) {
                    assert smallStep(s, e, e2);
                    assert exists e' :: smallStep(s, e, e');
                } else {
                    assert smallStep(s, e, e3);
                    assert exists e' :: smallStep(s, e, e');
                }
            } else {
                // If e1 progresses into e1', we can
                // do a step e1 ? e2 : e3 --> e1' ? e2 : e3
                var e1' :| smallStep(s, e1, e1');
                assert smallStep(s, Cond(e1, e2, e3), Cond(e1', e2, e3));
                assert exists e' :: smallStep(s, e, e');
            }
        }
    }    
}


// -------------------------------------------------------------
// 5. Preservation theorem.
// -------------------------------------------------------------

// Consistency:
// 
// We say that σ is consistent with Γ if for every
// x ∈ dom Γ it holds that Γ ⊢ σ(x) :: Γ(x)

predicate consistent(s: State, gamma: Env)
{
    forall x | x in gamma :: hasType(gamma, Val(s(x)), gamma[x])
}

// Lemma: if σ is consistent with Γ and Γ ⊢ v :: τ, then σ[x ↦ v] is consistent with Γ[x ↦ τ]
lemma consistentExtend(st: State, gamma: Env, x: VarName, v: Value, t: Type)
    requires consistent(st, gamma)
    requires hasType(gamma, Val(v), t)
    ensures consistent(changeState(st, x, v), gamma[x := t])
{
    forall z | z in gamma
        ensures hasType(gamma[x := t], Val(changeState(st, x, v)(z)), gamma[x := t][z])
    {
        // Assume some z ∈ dom Γ. We distinguish cases according to whether z == x or z != x
        if (z == x) {
            calc {
                    hasType(gamma, Val(v), t);
                ==> { assert changeState(st, x, v)(z) == v && gamma[x := t][z] == t; }
                    hasType(gamma, Val(changeState(st, x, v)(z)), gamma[x := t][z]);
                ==> { extendGamma(gamma, Val(changeState(st, x, v)(z)), gamma[x := t][z], x, t); }
                    hasType(gamma[x := t], Val(changeState(st, x, v)(z)), gamma[x := t][z]);
            }
        } else {
            calc {
                    consistent(st, gamma)
                ==>
                    hasType(gamma, Val(st(z)), gamma[z]);
                ==> { assert changeState(st, x, v)(z) == st(z) && gamma[x := t][z] == gamma[z]; }
                    hasType(gamma, Val(changeState(st, x, v)(z)), gamma[x := t][z]);
                ==> { extendGamma(gamma, Val(changeState(st, x, v)(z)), gamma[x := t][z], x, t); }
                    hasType(gamma[x := t], Val(changeState(st, x, v)(z)), gamma[x := t][z]);
            }
        }
    }
}

// Lemma: if σ is consistent with Γ[x := τ], then σ is consistent with Γ
lemma consistentRemove(st: State, gamma: Env, x: VarName, v: Value, t: Type)
    requires consistent(st, gamma[x := t])
    requires x !in gamma
    ensures consistent(changeState(st, x, v), gamma)
{
    // Similarly as above
}

// Preservation theorem:
//
// If Γ ⊢ e :: τ and σ ⊢ e --> e' for some σ consistent with Γ,
// then Γ ⊢ e' :: τ

lemma preservation(gamma: Env, s: State, e: Exp, e': Exp, t: Type)
    requires hasType(gamma, e, t) && smallStep(s, e, e') && consistent(s, gamma)
    ensures hasType(gamma, e', t)
{
    // By structural induction on e
    // We distinguish cases:
    match (e) {
        case Val(v) => {
            // If it is a value, then we cannot have
            // σ ⊢ e --> e' for any e'
            assert false;
        }

        case Var(x) => {
            // If it is a variable, then Γ ⊢ x :: Γ (x)
            // and σ ⊢ x --> σ(x)
            assert e' == Val(s(x));
            assert gamma[x] == t;
            assert hasType(gamma, Val(s(x)), gamma[x]);

            // By consistency, we have Γ ⊢ σ(x) :: Γ(x)
            assert hasType(gamma, e', t);
        }

        case Add(e1, e2) => {
            assert t == Int;
            // If we have done a step from e1 + e2, we have applied [Add1], [Add2] or [Add3]
            if e1' :| smallStep(s, e1, e1') && e' == Add(e1', e2) {
                // Case [Add1] : There is some e1' such that e1 --> e1'.

                // Applying IH we get that Γ ⊢ e1' :: Int
                preservation(gamma, s, e1, e1', Int);
                assert hasType(gamma, e1', Int);
                // Therefore: Γ ⊢ e1' + e2 :: Int
                assert hasType(gamma, e2, Int);
                assert hasType(gamma, e', Int);
            } else if n1, e2' :| e1 == Val(Const(n1)) && smallStep(s, e2, e2') && e' == Add(Val(Const(n1)), e2') {
                // Case [Add2]: Similarly, but applying IH on e2'
                preservation(gamma, s, e2, e2', Int);
                assert hasType(gamma, Val(Const(n1)), Int);
                assert hasType(gamma, e2', Int);
                assert hasType(gamma, e', Int);
            } else {
                // Case [Add3]: Trivial, since the result is an integer
                assert exists n1, n2 :: e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && e' == Val(Const(n1 + n2));
                assert hasType(gamma, e', Int);
            }
        }

        case Leq(e1, e2) => {
            // The initial expression has boolean type, and e1 and e2 have integer type.
            assert t == Bool;
            assert hasType(gamma, e1, Int);
            assert hasType(gamma, e2, Int);

            
            // Depending on the small-step rule applied:
            if e1' :| smallStep(s, e1, e1') && e' == Leq(e1', e2) {
                // Case [Leq1]: Apply IH on e1.
                preservation(gamma, s, e1, e1', Int);
                assert hasType(gamma, e1', Int);
                assert hasType(gamma, e2, Int);
                assert hasType(gamma, e', Bool);
            } else if n1, e2' :| e1 == Val(Const(n1)) && smallStep(s, e2, e2') && e' == Leq(Val(Const(n1)), e2') {
                // Case [Leq2]: Apply IH on e2.
                preservation(gamma, s, e2, e2', Int);
                assert hasType(gamma, Val(Const(n1)), Int);
                assert hasType(gamma, e2', Int);
                assert hasType(gamma, e', Bool);                
            } else if n1, n2 :| e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && n1 <= n2 && e' == Val(TrueB()) {
                // Case [Leq3]: Trivial
                assert hasType(gamma, e', Bool);
            } else {
                // Case [Leq4]: Trivial
                assert exists n1, n2 :: e1 == Val(Const(n1)) && e2 == Val(Const(n2)) && !(n1 <= n2) && e' == Val(FalseB());
                assert hasType(gamma, e', Bool);
            }

        }

        case Cond(e1, e2, e3) => {
            // The condition has type boolean, and e2 and e3 has the same type as the whole conditional.
            assert hasType(gamma, e1, Bool) && hasType(gamma, e2, t) && hasType(gamma, e3, t);
            // Depending on the rule applied:
            if e1' :| smallStep(s, e1, e1') && e' == Cond(e1', e2, e3) {
                // [Cond1]. Apply IH on e1
                preservation(gamma, s, e1, e1', Bool);
                assert hasType(gamma, e1', Bool);
                assert hasType(gamma, e2, t);
                assert hasType(gamma, e3, t);
                assert hasType(gamma, e', t);
            } else if e1 == Val(TrueB()) && e' == e2 {
                // [Cond2]. Trivial
                assert hasType(gamma, e', t);
            } else {
                // [Cond2]. Trivial
                assert e1 == Val(FalseB()) && e' == e3;
                assert hasType(gamma, e', t);
            }
        }
    }

}