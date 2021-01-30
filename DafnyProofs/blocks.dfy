/**
 * --------------------------------------
 * Static Analysis and Constraint Solving
 * Lesson 3: Type-based analysis
 * --------------------------------------
 *
 *          Manuel Montenegro
 *
 * This module defines an imperative language with block-scoped variables, its small-step semantics,
 * a type system and its proof of correctness.
 * 
 */

type VarName = string

// Syntax of expressions and values:
//
// e := v | x | e1 + e2 | e1 <= e2 | e1 ? e2 : e3
// v := n | true | false
//

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

// Syntax of statements
//
// S := skip | x:=e | S1;S2 | if e then S1 else S2 | while e do S | begin var x::τ := e; S end

datatype Stm =
      Skip
    | Assign(x: VarName, e: Exp)
    | Seq(s1: Stm, s2: Stm)
    | If(e: Exp, s1: Stm, s2: Stm)
    | While(e: Exp, s: Stm)
    | Block(x: VarName, t: Type, e: Exp, s: Stm)

// Syntax of types
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

// Free variables in an expression
function FVExp(e: Exp): set<VarName> {
    match(e) {
        case Val(v) => {}
        case Var(x) => {x}
        case Add(e1, e2) => FVExp(e1) + FVExp(e2)
        case Leq(e1, e2) => FVExp(e1) + FVExp(e2)
        case Cond(e1, e2, e3) => FVExp(e1) + FVExp(e2) + FVExp(e3)
    }
}

// Free variables in a statement
function FVStm(s: Stm): set<VarName> {
    match s {
        case Skip() => {}
        case Assign(x, e) => FVExp(e) + {x}
        case Seq(s1, s2) => FVStm(s1) + FVStm(s2)
        case If(e, s1, s2) => FVExp(e) + FVStm(s1) + FVStm(s2)
        case While(e, s1) => FVExp(e) + FVStm(s1)
        case Block(x, t, e, s) => FVExp(e) + FVStm(s) - { x }
    }
}


// A state σ is an assignment of values to variables
type State = VarName -> Value

// Definition of state update: σ[x ↦ v]
function changeState(st: State, x: VarName, v: Value) : State {
    y => if y == x then v else st(y)
}

// -------------------------------------------------------------
// 1. Preliminary definitions and results
// -------------------------------------------------------------


// Small step semantics relation. See exps_vars.dfy for details.
// Its definition is irrelevant in this module
//
// It defines a relation σ ⊢ e --> e'
predicate smallStepExp(s: State, e: Exp, e': Exp)

// An environment is a partial mapping from variables to types
type Env = map<VarName, Type>

// Typing relation on expressions. See exps_vars.dfy for details
// Its definition is irrelevant in this module.
// We have judgements of the form Γ ⊢ e :: τ
predicate hasTypeExp(gamma: Env, e: Exp, t: Type)

// Some properties on typing rules proved in exps_vars.dfy

// If Γ ⊢ e :: τ and x1 is a variable not occurring in e, then:
// Γ[x1 ↦ τ1] ⊢ e :: τ for any τ1
lemma extendGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasTypeExp(gamma, e, t)
    requires x1 !in FVExp(e)
    ensures hasTypeExp(gamma[x1 := t1], e, t)


// If Γ[x1 ↦ τ1] ⊢ e :: τ and x1 is a variable not occurring in e, then:
// Γ ⊢ e :: τ
lemma removeGamma(gamma: Env, e: Exp, t: Type, x1: VarName, t1: Type)
    requires hasTypeExp(gamma[x1 := t1], e, t)
    requires x1 !in FVExp(e)
    ensures hasTypeExp(gamma, e, t)



// Consistency relation:
// 
// We say that σ is consistent with Γ if for every
// x ∈ dom Γ it holds that Γ ⊢ σ(x) :: Γ(x)
predicate consistent(st: State, gamma: Env)
{
    forall x | x in gamma :: hasTypeExp(gamma, Val(st(x)), gamma[x])
}

// Lemma: if σ is consistent with Γ and Γ ⊢ v :: τ, then σ[x ↦ v] is consistent with Γ[x ↦ τ]
// (see exps_vars.dfy for its proof)
lemma consistentExtend(st: State, gamma: Env, x: VarName, v: Value, t: Type)
    requires consistent(st, gamma)
    requires hasTypeExp(gamma, Val(v), t)
    ensures consistent(changeState(st, x, v), gamma[x := t])

// Lemma: if σ is consistent with Γ[x := τ], then σ is consistent with Γ
// (see exps_vars.dfy for its proof)
lemma consistentRemove(st: State, gamma: Env, x: VarName, v: Value, t: Type)
    requires consistent(st, gamma[x := t])
    requires x !in gamma
    ensures consistent(changeState(st, x, v), gamma)

// -------------------------------------------------------------
// 2. Small-step semantic rules for statements
// -------------------------------------------------------------

// A configuration γ is either a pair (S, σ) or a single state σ.
datatype Conf = Pair(s: Stm, st: State) | End(st: State)

// Small-step semantic relation: (S, σ) --> γ
//
// An execution step from S under the state σ leads to the configuration γ.
//
// 
//    -------------------- [Skip]
//      (skip, σ) --> σ
//
//              σ ⊢ e --> e'
//    ------------------------------- [Assign1]
//      (x := e, σ) --> (x := e', σ)
//
//
//    ------------------------------- [Assign2]
//      (x := v, σ) --> σ[x ↦ v]
//
//          (S1, σ) --> (S1', σ')
//    ------------------------------- [Seq1]
//      (S1; S2, σ) --> (S1'; S2, σ')
//
//              (S1, σ) --> σ'
//    ------------------------------- [Seq2]
//        (S1; S2, σ) --> (S2, σ')
//
//                           σ ⊢ e --> e'
//    ---------------------------------------------------------- [If1]
//     (if e then S1 else S2, σ) --> (if e' then S1 else S2, σ)
//
//                           
//    ------------------------------------------- [If1]
//     (if true then S1 else S2, σ) --> (S1, σ)
//
//                           
//    ------------------------------------------- [If2]
//     (if true then S1 else S2, σ) --> (S2, σ)
//
//                           
//    ------------------------------------------------------------------ [While]
//     (while e do S, σ) --> (if e then (S; while b do S) else skip, σ)
//
//                          σ ⊢ e --> e'
//    ---------------------------------------------------------------- [Block1]
//     (begin x::τ := e; S end, σ) --> (begin x::τ := e'; S end, σ)
//
//                        (S, σ[x ↦ v]) --> (S', σ')
//    ------------------------------------------------------------------------------ [Block2]
//     (begin x::τ := v; S end, σ) --> (begin x::τ := σ'(x); S' end, σ'[x ↦ σ(x)])
//
//                (S, σ[x ↦ v]) --> σ'
//    ---------------------------------------------- [Block3]
//     (begin x::τ := v; S end, σ) --> σ'[x ↦ σ(x)]



predicate smallStep(s: Stm, st: State, conf: Conf)
{
    match s {
        case Skip() => conf == End(st)
        case Assign(x, e) => 
                exists e' :: smallStepExp(st, e, e') && conf == Pair(Assign(x, e'), st)
            ||
                exists v :: e == Val(v) && conf == End(changeState(st, x, v))
        case Seq(s1, s2) =>
                exists st' :: smallStep(s1, st, End(st')) && conf == Pair(s2, st')
            || 
                exists s1', st' :: smallStep(s1, st, Pair(s1', st')) && conf == Pair(Seq(s1', s2), st')
        case If(e, s1, s2) =>
                exists e' :: smallStepExp(st, e, e') && conf == Pair(If(e', s1, s2), st)
            || 
                (e == Val(TrueB) && conf == Pair(s1, st))
            || 
                (e == Val(FalseB) && conf == Pair(s2, st))
        case While(e, s1) =>
                conf == Pair(If(e, Seq(s1, While(e, s1)), Skip), st)
        
        case Block(x, t, e, s) =>
                exists e' :: smallStepExp(st, e, e') && conf == Pair(Block(x, t, e', s), st)
            ||
                exists v, s', st' :: e == Val(v) && smallStep(s, changeState(st, x, v), Pair(s', st'))
                                                 && conf == Pair(Block(x, t, Val(st'(x)), s'), changeState(st', x, st(x)))
            ||
                exists v, st' :: e == Val(v) && smallStep(s, changeState(st, x, v), End(st'))
                                                 && conf == End(changeState(st', x, st(x)))
    }
}


// -------------------------------------------------------------
// 3. Typing rules for statements
// -------------------------------------------------------------


// Typing rules for statements. We have judgements of the form Γ ⊢ S, meaning
// that the program S is well typed under the environment Γ.
//
// 
//    -------------------- [SKIP]
//         Γ ⊢ skip
//
//       Γ ⊢ e :: Γ (x)
//    -------------------- [ASSIGN]
//         Γ ⊢ x := e
//
//       Γ ⊢ S1   Γ ⊢ S2
//    -------------------- [SEQ]
//         Γ ⊢ S1;S2
//
//      Γ ⊢ e :: Bool  Γ ⊢ S1   Γ ⊢ S2
//    ----------------------------------- [IF]
//          Γ ⊢ if e then S1 else S2
//
//      Γ ⊢ e :: Bool  Γ ⊢ S
//    ------------------------ [WHILE]
//        Γ ⊢ while e do S
//
//      Γ ⊢ e :: τ    Γ[x :: τ] ⊢ S
//    ---------------------------------- [BLOCK]
//        Γ ⊢ begin x::τ := e; S end

predicate wellTyped(gamma: Env, s: Stm)
    decreases s
{
    match s {
        case Skip() => true
        case Assign(x, e) => x in gamma && hasTypeExp(gamma, e, gamma[x])
        case Seq(s1, s2) => wellTyped(gamma, s1) && wellTyped(gamma, s2)
        case If(e, s1, s2) => hasTypeExp(gamma, e, Bool) && wellTyped(gamma, s1) && wellTyped(gamma, s2)
        case While(e, s1) => hasTypeExp(gamma, e, Bool) && wellTyped(gamma, s1)
        case Block(x, t, e, s1) => hasTypeExp(gamma, e, t) && wellTyped(gamma[x := t], s1)
    }   
}

// -------------------------------------------------------------
// 4. Progress theorem
// -------------------------------------------------------------

// We assume that progress hold on expressions
//
// See exps_vars for the full proof.
lemma progressExp(s: State, e: Exp)
    requires exists gamma, t :: hasTypeExp(gamma, e, t)
    ensures isValue(e) || (exists e' :: smallStepExp(s, e, e'))


// Inversion lemma, if a value is of type bool, it must be
// either true or false
//
// See exps_vars.dfy for more details.
lemma inversionBool(gamma: Env, v: Value)
    requires hasTypeExp(gamma, Val(v), Bool)
    ensures v == TrueB || v == FalseB


// Progress theorem:
//
// If Γ ⊢ S for some Γ, then there exists some configuration γ such that
// (S, σ) --> γ
lemma progress(st: State, s: Stm)
    requires exists gamma :: wellTyped(gamma, s)
    ensures exists c :: smallStep(s, st, c)
{
    // Let Γ be the environment until which S is typed.
    var gamma :| wellTyped(gamma, s);

    match s {
        // If S = skip, a step is always possible
        case Skip() => {
            assert smallStep(s, st, End(st));
        } 

        // If S = (x := e)
        case Assign(x, e) =>  {
            // Since S is well typed, we know that Γ ⊢ e :: Γ(x)
            assert x in gamma && hasTypeExp(gamma, e, gamma[x]);
            
            // If the expression is a value, we can apply [Assign1]
            if v :| e == Val(v) {
                assert smallStep(s, st, End(changeState(st, x, v)));
            } else {
                // If the expression is not a value, we can perform a
                // step on that expression, since it is well-typed.
                // We apply progress theorem for expressions:
                progressExp(st, e);
                assert exists e' :: smallStepExp(st, e, e');
                var e' :| smallStepExp(st, e, e');
                // Now we apply [Assign2]
                assert smallStep(s, st, Pair(Assign(x, e'), st));
            }
        }

        // If S = (S1; S2)
        case Seq(s1, s2) => {
            // We know that S1 is well typed, so we apply IH
            // in order to get (S1, σ) --> γ1 for some γ1
            assert wellTyped(gamma, s1);
            progress(st, s1);
            assert exists c1 :: smallStep(s1, st, c1);
            var c1 :| smallStep(s1, st, c1);


            match c1 {
                // If γ1 is an intermediate configuration, we apply [Seq1]
                case Pair(s1', st1) => {
                    assert smallStep(s, st, Pair(Seq(s1', s2), st1));
                }
                // If γ1 is a final configuration, we apply [Seq2]
                case End(st1) => {
                    assert smallStep(s, st, Pair(s2, st1));
                }
            }
        }

        // If S = (if e then S1 else S2)
        case If(e, s1, s2) => { 
            // If e is a value v
            if v :| e == Val(v) {
                // This value must have type Bool, according to [IF]
                assert hasTypeExp(gamma, e, Bool);
                // Apply inversion lemma: v must be either true or false
                inversionBool(gamma, v);
                assert v == TrueB() || v == FalseB();

                // Depending on the boolean value, we apply [If2] or [If3]
                if v == TrueB {
                    assert smallStep(s, st, Pair(s1, st));
                } else {
                    assert smallStep(s, st, Pair(s2, st));
                }
            } else {
                // If e is not a value, it still must be well-typed
                assert hasTypeExp(gamma, e, Bool);
                // This means it can perform a step by progress theorem on expressions
                progressExp(st, e);
                assert exists e' :: smallStepExp(st, e, e');
                var e' :| smallStepExp(st, e, e');
                // So we apply [If1]
                assert smallStep(s, st, Pair(If(e', s1, s2), st));
            }
        }

        // If S = (while e do S1)
        // We can always apply a step.
        case While(e, s1) => {
            assert smallStep(s, st, Pair(If(e, Seq(s1, While(e, s1)), Skip), st));
        }

        // If S = (begin x::τ := e; S1 end)
        case Block(x, t, e, s1) => {
            // Assume that e is well-typed, by rule [BLOCK]
            assert hasTypeExp(gamma, e, t);

            // If e is a value
            if (isValue(e)) {
                var v :| e == Val(v);
                // We assume that Γ[x := τ] ⊢ S1
                assert wellTyped(gamma[x := t], s1);
                // We can therefore apply IH to show that (S1, σ[x ↦ v]) --> γ1 for some γ1
                progress(changeState(st, x, v), s1);
                var c :| smallStep(s1, changeState(st, x, v), c);
                match c {
                    // If γ1 is terminal:
                    case End(st') =>  {
                        // We apply [Seq3]
                        assert smallStep(s1, changeState(st, x, v), End(st'));
                        assert exists v, st'' :: 
                                e == Val(v) &&
                                smallStep(s1, changeState(st, x, v), End(st''));
                        assert smallStep(s, st, End(changeState(st', x, st(x))));
                    }
                    // If γ1 is not terminal
                    case Pair(s1', st') => {                        
                        // We apply [Seq2]
                        assert smallStep(s1, changeState(st, x, v), Pair(s1', st'));
                        assert exists v, s1', st'' ::
                                e == Val(v) &&
                                smallStep(s1, changeState(st, x, v), Pair(s1', st''));

                        assert smallStep(Block(x, t, Val(v), s1), st, 
                                        Pair(Block(x, t, Val(st'(x)), s1'), changeState(st', x, st(x))));
                    }
                }
            } else {
                // If e is not a value, we apply progress theorem on expressions
                progressExp(st, e);
                // so there is some e' such that σ ⊢ e --> e'
                assert exists e' :: smallStepExp(st, e, e');
                var e' :| smallStepExp(st, e, e');
                // Therefore we can apply [Seq1]
                assert smallStep(Block(x, t, e, s1), st, 
                                        Pair(Block(x, t, e', s1), st));
            }
        }
    }
}


// -------------------------------------------------------------
// 5. Preservation theorem
// -------------------------------------------------------------

// We assume that preservation holds on expressions:

// If Γ ⊢ e :: τ and σ ⊢ e --> e' for some σ consistent with Γ,
// then Γ ⊢ e' :: τ

lemma preservationExp(gamma: Env, s: State, e: Exp, e': Exp, t: Type)
    requires hasTypeExp(gamma, e, t) && smallStepExp(s, e, e') && consistent(s, gamma)
    ensures hasTypeExp(gamma, e', t)


// Preservation of consistency for terminal steps:
//
// If Γ ⊢ S, σ is consistent with Γ, and (S, σ) --> σ'
// then σ' is consistent with Γ
lemma preservationEnd(gamma: Env, s: Stm, st: State, st': State)
    requires wellTyped(gamma, s)
    requires consistent(st, gamma)
    requires smallStep(s, st, End(st'))
    ensures consistent(st', gamma)
    decreases s
{
    // By induction on the structure of S
    match s {
        // Case S = skip. Trivial, since σ = σ'
        case Skip() => { assert st == st'; } 

        // Case S = (x := e)
        case Assign(x, e) =>  {
            // If it is a terminal step, then e must be a value v.
            assert exists v :: e == Val(v);
            var v :| e == Val(v);
            // In this case σ' = σ[x ↦ v]
            assert st' == changeState(st, x, v);
            // Assume that Γ ⊢ v :: Γ(x), because of [ASSIGN]
            assert hasTypeExp(gamma, Val(v), gamma[x]);
            assert st'(x) == v;

            // We prove consistency: ∀y. y ∈ dom Γ ==> Γ ⊢ σ'(y) :: Γ(y)
            forall y: VarName | y in gamma
                ensures hasTypeExp(gamma, Val(st'(y)), gamma[y])
            {
                if (y == x) {
                    assert st'(y) == v;
                    assert hasTypeExp(gamma, Val(st'(y)), gamma[y]);
                } else {
                    assert st'(y) == st(y);
                    assert hasTypeExp(gamma, Val(st'(y)), gamma[y]);
                }
            }
        }

        // Case S = (S1; S2)
        // Not a terminal step
        case Seq(s1, s2) => {
            assert false;
        }

        // Case S = (if e then S1 else S2)
        // Not a terminal step
        case If(e, s1, s2) => {
            assert false;
        }

        // Case S = (while e do S)
        // Not a terminal step
        case While(e, s1) => { 
            assert false;
        }

        // Case S = (begin var x::τ := e; S1 end)
        case Block(x, t, e, s1) => {
            
            assert smallStep(Block(x, t, e, s1), st, End(st'));
            // In block-scoped statements we can apply [Block1], [Block1] or [Block1]
            assert exists e' :: smallStepExp(st, e, e') && End(st') == Pair(Block(x, t, e', s1), st)
            ||
                exists v, s1', st'' :: e == Val(v) && smallStep(s1, changeState(st, x, v), Pair(s1', st''))
                                                 && End(st') == Pair(Block(x, t, Val(st''(x)), s1'), changeState(st'', x, st(x)))
            ||
                exists v, st'' :: e == Val(v) && smallStep(s1, changeState(st, x, v), End(st''))
                                                 && End(st') == End(changeState(st'', x, st(x)));

            // We cannot have applied [Block1], since we would reach a nonterminal state.
            if e' :| smallStepExp(st, e, e') && End(st') == Pair(Block(x, t, e', s1), st) {
                assert End(st') == Pair(Block(x, t, e', s1), st);
                assert false;
            } else if v, s1', st'' :| e == Val(v) && smallStep(s1, changeState(st, x, v), Pair(s1', st''))
                                                 && End(st') == Pair(Block(x, t, Val(st''(x)), s1'), changeState(st'', x, st(x))) {
            // We cannot have applied [Block2], since we would reach a nonterminal state.
                assert End(st') == Pair(Block(x, t, Val(st''(x)), s1'), changeState(st'', x, st(x)));
                assert false;
            } else {
            // Therefore, we must have applied [Block3], which means that
            // S = (begin var x::τ := v; S1 end), (S1, σ[x ↦ v]) --> σ'' and σ' == σ''[x ↦ σ(x)]

                var v, st'' :| e == Val(v) && smallStep(s1, changeState(st, x, v), End(st''))
                                                 && st' == changeState(st'', x, st(x));
                
                // We know that S1 is well-typed, and σ consistent with respect to Γ
                assert wellTyped(gamma[x := t], s1);
                assert consistent(st, gamma);
                // We also know that Γ ⊢ v :: τ
                assert hasTypeExp(gamma, Val(v), t);
                // Therefore, by consistency extension lemma,
                consistentExtend(st, gamma, x, v, t);
                // it holds that σ[x ↦ v] is consistent with Γ[x :: τ]
                assert consistent(changeState(st, x, v), gamma[x := t]);
                // We can therefore apply IH to get that σ'' is consistent with Γ[x :: τ]
                preservationEnd(gamma[x := t], s1, changeState(st, x, v), st'');
                assert consistent(st'', gamma[x := t]);
                if (x in gamma) {
                    // If x belongs to the domain of Γ
                    assert consistent(st, gamma);
                    // Then Γ ⊢ σ(x) :: Γ(x) by consistency of σ w.r.t. Γ
                    assert hasTypeExp(gamma, Val(st(x)), gamma[x]);
                    // Since x does not appear free in σ(x) we can apply extension theorem
                    // to get Γ[x :: τ] ⊢ σ(x) :: Γ(x)
                    extendGamma(gamma, Val(st(x)), gamma[x], x, t);
                    assert hasTypeExp(gamma[x := t], Val(st(x)), gamma[x]);
                    // Therefore, σ' = σ''[x ↦ σ(x)] is consistent with Γ[x :: τ][x :: Γ(x)] = Γ
                    consistentExtend(st'', gamma[x := t], x, st(x), gamma[x]);
                    assert consistent(changeState(st'', x, st(x)), gamma[x := t][x := gamma[x]]);
                    assert gamma[x := t][x := gamma[x]] == gamma[x := gamma[x]] == gamma;
                    assert consistent(st', gamma);
                } else {
                    // If x does not belong to the domain of Γ
                    assert x !in gamma;
                    assert consistent(st'', gamma[x := t]);
                    // We can remove it from the environment, so σ' = σ''[x ↦ σ(x)] is consistent w.r.t. Γ
                    consistentRemove(st'', gamma, x, st(x), t);
                    assert consistent(changeState(st'', x, st(x)), gamma);
                    assert consistent(st', gamma);
                }
            }
        }
    }    
}    

// Preservation of well-typedness and consistency for intermediate steps:
//
// If Γ ⊢ S, σ is consistent with Γ, and (S, σ) --> (S', σ')
// then Γ ⊢ S' and σ' is consistent with Γ

lemma preservationPair(gamma: Env, s: Stm, st: State, s': Stm, st': State)
    requires wellTyped(gamma, s)
    requires consistent(st, gamma)
    requires smallStep(s, st, Pair(s', st'))
    ensures wellTyped(gamma, s')
    ensures consistent(st', gamma)
    decreases s
{ 
    // By induction on the structure of S
    match s {
        // Skip is terminal
        case Skip() => { assert false; } 

        // An assignment is not terminal if e can be reduced
        case Assign(x, e) =>  { 
            // By [ASSIGN] rule, Γ ⊢ e :: Γ(x)
            assert hasTypeExp(gamma, e, gamma[x]);

            if e' :| smallStepExp(st, e, e') && s' == Assign(x, e') && st' == st {
                // If σ ⊢ e --> e', then Γ ⊢ e' :: Γ(x) by type preservation on expressions
                preservationExp(gamma, st, e, e', gamma[x]);
                assert hasTypeExp(gamma, e', gamma[x]);
                // Therefore we can apply [ASSIGN] again
                assert wellTyped(gamma, Assign(x, e'));
                // Since σ = σ', consistency is preserved
                assert consistent(st', gamma);
            } else {
                // If e is a value, we reach a final configuration
                assert false;                
            }
        }

        // Case S = (S1; S2)
        case Seq(s1, s2) => {
            // If an execution step of S1 leads to a final state σ'
            if smallStep(s1, st, End(st')) && s' == s2 {
                // Since S2 is well-typed, so is S'
                assert wellTyped(gamma, s2);
                assert wellTyped(gamma, s');

                // Apply preservation of consistency on (S1, σ) --> σ'
                preservationEnd(gamma, s1, st, st');
                // Therefore, σ' is consistent with Γ
                assert forall x | x in gamma :: hasTypeExp(gamma, Val(st'(x)), gamma[x]);
                assert consistent(st', gamma);
            } else {
            // If an execution step on S1 leads to an intermediate configuration (S1',σ')
                var s1' :| smallStep(s1, st, Pair(s1', st')) && s' == Seq(s1', s2);
                // We apply IH on e1
                preservationPair(gamma, s1, st, s1', st');

                // Since Γ ⊢ S1' and Γ ⊢ S2, we apply [SEQ]
                assert wellTyped(gamma, s1');
                assert wellTyped(gamma, s2);
                assert wellTyped(gamma, Seq(s1', s2));
                assert wellTyped(gamma, s');

                // Again, consistency holds by IH.
                assert forall x | x in gamma :: hasTypeExp(gamma, Val(st'(x)), gamma[x]);
                assert consistent(st', gamma);
            }
        }

        // Case S = (if e then S1 else S2)
        case If(e, s1, s2) => {
            // If we have appled [If1], we have σ ⊢ e --> e'
            if e' :| smallStepExp(st, e, e') && s' == If(e', s1, s2) && st' == st {
                // We get σ' = σ so consistency is preserved
                assert consistent(st', gamma);

                // We apply preservation on the guard
                assert hasTypeExp(gamma, e, Bool);
                preservationExp(gamma, st, e, e', Bool);
                // So Γ ⊢ e' :: Bool
                assert hasTypeExp(gamma, e', Bool);
                // Therefore we apply [IF] and S' is well-typed
                assert wellTyped(gamma, s1);
                assert wellTyped(gamma, s2);
                assert wellTyped(gamma, s');
            } else if e == Val(TrueB) && s' == s1 && st' == st {
                // If we have applied [If2], the result is well-typed, since
                // so is S1, and consistency is preserved since the state
                // does not change
                assert wellTyped(gamma, s1);
                assert wellTyped(gamma, s');

                assert consistent(st', gamma);
            } else { 
                // If we have applied [If3], the result is well-typed, since
                // so is S2, and consistency is preserved since the state
                // does not change
                assert e == Val(FalseB) && s' == s2 && st' == st;
                assert wellTyped(gamma, s2);
                assert wellTyped(gamma, s');

                assert consistent(st', gamma);
            }

        }

        // Case S = (while e do S1)
        case While(e, s1) => { 
            // In this case (S, σ) --> (if e then (S1; while b do S1) else skip, σ')
            // with σ' = σ, so consistency is preserved
            assert s' == If(e, Seq(s1, While(e, s1)), Skip);
            assert st' == st;

            // We apply [SEQ] to get Γ ⊢ S; while b do S1
            assert wellTyped(gamma, While(e, s1));
            assert wellTyped(gamma, s1);
            assert wellTyped(gamma, Seq(s1, While(e, s1)));
            // We apply [IF] to get Γ ⊢ S'
            assert hasTypeExp(gamma, e, Bool);
            assert wellTyped(gamma, If(e, Seq(s1, While(e, s1)), Skip));
        }

        // Case S = (begin var x::τ := e; S end)
        case Block(x, t, e, s1) => {
            assert smallStep(Block(x, t, e, s1), st, Pair(s', st'));
                
            if e' :| smallStepExp(st, e, e') && s' == Block(x, t, e', s1) && st' == st {
                // If we have applied a step on e --> e'
                // We know that the type of e is preserved, so e' is well-typed.
                // Therefore we can apply [BLOCK] rule, and consistency is preserved
                // since σ' = σ
                assert hasTypeExp(gamma, e, t) && smallStepExp(st, e, e') && consistent(st, gamma);
                preservationExp(gamma, st, e, e', t);
                assert hasTypeExp(gamma, e', t);
                assert wellTyped(gamma[x := t], s1);
                assert wellTyped(gamma, Block(x, t, e', s1));
                assert consistent(st', gamma);
            } else if v, s1', st'' :| e == Val(v) && smallStep(s1, changeState(st, x, v), Pair(s1', st''))
                                                 && s' == Block(x, t, Val(st''(x)), s1') && st' == changeState(st'', x, st(x)) {
                
                // If e is a value, we have applied a step on (S1, σ[x ↦ v]) obtaining (S1', σ'')
                // We know by [BLOCK] that Γ[x::τ] ⊢ S1
                // and that Γ ⊢ v :: τ
                assert wellTyped(gamma[x := t], s1);
                assert consistent(st, gamma);
                assert hasTypeExp(gamma, Val(v), t);
                // By applying consistency extension: σ[x ↦ v] is consistent w.r.t. Γ[x::τ]
                consistentExtend(st, gamma, x, v, t);
                assert consistent(changeState(st, x, v), gamma[x := t]);
                assert smallStep(s1, changeState(st, x, v), Pair(s1', st''));

                // Apply IH to show that Γ[x :: τ] ⊢ S1' and that σ'' is consistent with Γ[x :: τ]
                preservationPair(gamma[x := t], s1, changeState(st, x, v), s1', st'');

                assert wellTyped(gamma[x := t], s1');
                assert consistent(st'', gamma[x := t]);
                // consistency on σ'' implies that Γ[x :: τ] ⊢ σ''(x) :: τ
                assert hasTypeExp(gamma[x := t], Val(st''(x)), t);
                // By environment removal lemma, we get Γ ⊢ σ''(x) :: τ
                removeGamma(gamma, Val(st''(x)), t, x, t);
                assert hasTypeExp(gamma, Val(st''(x)), t);
                
                if (x in gamma) {
                    // If x belongs to dom Γ
                    assert consistent(st'', gamma[x := t]);
                    // By consistency of σ, Γ ⊢ σ(x) :: Γ(x)
                    assert hasTypeExp(gamma, Val(st(x)), gamma[x]);
                    // Therefore: Γ[x :: τ] ⊢ σ(x) :: Γ(x) by extension lemma
                    extendGamma(gamma, Val(st(x)), gamma[x], x, t);
                    assert hasTypeExp(gamma[x := t], Val(st(x)), gamma[x]);

                    // Since σ'' is consistent with Γ[x :: τ], and Γ[x :: τ] ⊢ σ(x) :: Γ(x)
                    // it holds that σ''[x ↦ σ(x)] is consistent with Γ[x :: τ][x :: Γ(x)] = Γ
                    // which proves consistency preservation
                    consistentExtend(st'', gamma[x := t], x, st(x), gamma[x]);
                    assert consistent(changeState(st'', x, st(x)), gamma[x := t][x := gamma[x]]);
                    assert gamma[x := t][x := gamma[x]] == gamma[x := gamma[x]] == gamma;
                    assert consistent(st', gamma);
                } else {
                    // In this case, we know that σ'' is consistent with Γ[x :: τ]
                    // from which it holds that σ'' is consistent with Γ
                    assert consistent(st'', gamma[x := t]);
                    consistentRemove(st'', gamma, x, st(x), t);
                    assert consistent(changeState(st'', x, st(x)), gamma);
                    assert consistent(st', gamma);
                }
                

                assert consistent(changeState(st'', x, st(x)), gamma);
                assert consistent(st', gamma);
                // Since S1, is well typed, we can apply [BLOCK]
                assert wellTyped(gamma, s');
            } else {
                // If we have applied [Seq3], this leads to a terminal configuration,
                // which contradicts the assumption of the theorem
                assert exists v, st'' :: e == Val(v) && smallStep(s1, changeState(st, x, v), End(st'')) && Pair(s', st') == End(changeState(st'', x, st(x)));
                assert false;
            }
        }
    }    
}    

    