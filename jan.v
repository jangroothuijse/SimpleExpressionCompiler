Require Import Arith.
Require Import Ascii.
Require Import String.
Require Import List.


(* 3.1 
 * Give an Inductive definition of a datatype Exp of (the abstract syntax
 * for) ⟨exp⟩s. 
 *)

Inductive BinOp := | add : BinOp | sub : BinOp | mul : BinOp.

Inductive Exp : Set := 
| lit : nat -> Exp
| exp : BinOp -> Exp -> Exp -> Exp.


(* 3.2
 * Define a function
 * eval: Exp -> nat
 * giving a semantics for ⟨exp⟩s.
 *)

Fixpoint eval (e: Exp) : nat :=
match e with
| lit n => n
| exp op e1 e2 => match op with
  | add => eval e1 + eval e2
  | sub => eval e1 - eval e2
  | mul => eval e1 * eval e2
  end
end.

Eval compute in eval (lit 3).
Eval compute in eval (exp mul (lit 2) (lit 3)).

(* Not relevant for the proof *)
Inductive Tok := | num : nat -> Tok
| binop : BinOp -> Tok | popen : Tok | pclose : Tok.

(* returns reversed list of tokens *)
Fixpoint lex_ (s: string) (l: list Tok) (y : bool) : option (list Tok) :=
match s with 
| EmptyString => Some l
| String h t => let c := (nat_of_ascii h) in match c with
  | 32 => lex_ t l false | 43 => lex_ t (binop add :: l) false
  | 45 => lex_ t (binop sub :: l) false 
  | 42 => lex_ t (binop mul :: l) false
  | 40 => lex_ t (popen :: l) false | 41 => lex_ t (pclose :: l) false
  (* to avoid mutual recursion and double testing, lex numbers here *)
  | _ => if (andb (leb c 57) (leb 48 c)) then let d := c - 48 in match l with 
    | nil => lex_ t (num d :: nil) true
    | cons x xs => match x with   
      | num n => match y with 
        | false => lex_ t (num d :: x :: xs) true
        (* in this case, we where already parsing a number *)
        | true => lex_ t (num (n * 10 + d) :: xs) true
        end
      | _ => lex_ t (num d :: x :: xs) true
      end
    end else None
  end  
end.

Fixpoint lex (s: string) : option (list Tok) := 
  option_map (@rev Tok) (lex_ s nil false).

Eval compute in lex "12 * (13 + 1400)".

Fixpoint parse_ (i : nat) (s: list Tok) : prod (list Tok) (option Exp) :=
match i with | 0 => (nil, None) | S j =>
match s with
| nil => (nil, None)
| h :: t => let (t2, oe1) := match h with
  | popen => let (t3, oe2) := parse_ j t in match oe2 with
    | None => (nil, None) 
    | Some e2 => match t3 with 
      | nil => (nil, None)
      | h2 :: t4 => match h2 with 
        | pclose => (t4, oe2) 
        | _=> (nil, None) 
      end 
    end 
  end
  | num n => (t, Some (lit n))
  | _ => (nil, None)
  end in 
  match oe1 with | None => (nil, None) | Some e1 =>
  match t2 with
  | nil => (t2, Some e1)
  | h2 :: t3 => match h2 with
    | pclose => (t2, Some e1)
    | binop o => let (t4, oe2) := parse_ j t3 in match oe2 with
       | None => (nil, None)
       | Some e2 => (t4, Some (exp o e1 e2))
       end
    | _ => (nil, None)
    end
  end
  end
end
end.

Definition parse (s: list Tok) : option Exp := 
let (t, e) := parse_ (length s) s in match t with 
| nil => e 
| _ => None end. (* checks that all tokens are consumed *)

Fixpoint option_flatten (A : Type) (a : option (option A)) : option A := 
match a with | None => None | Some x => x end.

(* compiler front-end *)
Fixpoint lex_and_parse (s : string) : (option Exp) := 
  option_flatten Exp (option_map (parse) (lex s)). 

Eval compute in lex_and_parse "14 + 5".
Eval compute in lex_and_parse "14 ++ 5".
Eval compute in lex_and_parse "(13 + 14) + 5".
Eval compute in lex_and_parse "13 + (14 + 5)".
Eval compute in lex_and_parse "(((13)) + (14 + 5) * (15 + 6))".
Eval compute in lex_and_parse "(((13)) + (14 + 5) * (15 + 6)))".
Eval compute in lex_and_parse "((((13)) + (14 + 5) * (15 + 6))".
(* / Not relevant for the proof *)

(* 3.3 
 * Give an Inductive definition of a datatype RPN of Reverse Polish Notation
 * for ⟨exp⟩s. 
 *)

Inductive RPNSymbol := 
| rpnlit : nat -> RPNSymbol
| rpnop : BinOp -> RPNSymbol.

Definition RPN := list RPNSymbol.


(* 3.4
 * Write a compiler
 *  rpn : Exp -> RPN
 *)

Fixpoint rpn (e: Exp) : RPN := match e with
| lit n => (rpnlit n) :: nil
| exp op e1 e2 => app (rpn e1) (app (rpn e2) (rpnop op :: nil))
end.


(* 3.5
 *  Write an evaluator rpn_eval for RPN, returning an option nat. 
 *)

Fixpoint rpn_eval_ (s: list nat) (code: RPN) : option nat := match code with
| nil => match s with | nil => None | r :: _ => Some r end
| h :: tl => match h with
  | rpnlit n => rpn_eval_ (cons n s) tl
  | rpnop op => match s with
    | nil => None 
    | n1 :: s1 => match s1 with
      | nil => None
      | n2 :: s2 => match op with
        | add => rpn_eval_ (n2 + n1 :: s2) tl
        | sub => rpn_eval_ (n2 - n1 :: s2) tl
        | mul => rpn_eval_ (n2 * n1 :: s2) tl
        end
      end
    end
  end
end.

Definition rpn_eval (code: RPN) := rpn_eval_ nil code.

Eval compute in option_map (rpn_eval) (option_map (rpn) (lex_and_parse "1+5*6")).
Eval compute in option_map (rpn_eval) (option_map (rpn) (lex_and_parse "15*5+5")).

(* I don't know why I did not have these, please comment them out if you have them *)

Lemma app_nil: forall (a:Type) (x : list a), x ++ nil = x.
induction x.
simpl.
reflexivity.
simpl.
rewrite IHx.
reflexivity.
Qed.

Theorem app_assoc: forall (a:Type) (x y z : list a) , x ++ (y ++ z) = (x ++ y) ++ z.
intro a.
induction x.
simpl.
reflexivity.
simpl.
intros y z.
rewrite IHx with (y := y) (z := z).
reflexivity.
Qed.

Theorem step : forall e : Exp, forall s : list nat, forall t : RPN, 
    rpn_eval_ s (app (rpn e) t) = rpn_eval_ (eval e :: s) t.
intro e.
induction e.
intros s t.
simpl.
reflexivity.
simpl.
induction b.
intros s t.
assert (s1 := (rpn e1 ++ rpn e2 ++ rpnop add :: nil) ++ t 
             = rpn e1 ++ (rpn e2 ++ ((rpnop add :: nil) ++ t))).
replace ((rpn e1 ++ rpn e2 ++ rpnop add :: nil) ++ t) 
   with (rpn e1 ++ (rpn e2 ++ ((rpnop add :: nil) ++ t))).

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop add :: nil) ++ t) 
             = rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop add :: nil) ++ t)).
apply IHe1 with (t := rpn e2 ++ (rpnop add :: nil) ++ t).

assert (step2: rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop add :: nil) ++ t)
             = rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop add :: nil) ++ t)).
apply IHe2 with (t := (rpnop add :: nil) ++ t).

assert (step3: 
      rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop add :: nil) ++ t)
    = rpn_eval_ (eval e1 + eval e2 :: s) t).
simpl.
reflexivity.
rewrite step1.
rewrite step2.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc with (x:= rpn e1).
rewrite app_assoc with (z:= t).
reflexivity.

(* Same for - *)
intros s t.
assert (s1 := (rpn e1 ++ rpn e2 ++ rpnop sub :: nil) ++ t 
             = rpn e1 ++ (rpn e2 ++ ((rpnop sub :: nil) ++ t))).
replace ((rpn e1 ++ rpn e2 ++ rpnop sub :: nil) ++ t) 
   with (rpn e1 ++ (rpn e2 ++ ((rpnop sub :: nil) ++ t))).

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop sub :: nil) ++ t) 
             = rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop sub :: nil) ++ t)).
apply IHe1 with (t := rpn e2 ++ (rpnop sub :: nil) ++ t).

assert (step2: rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop sub :: nil) ++ t)
             = rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop sub :: nil) ++ t)).
apply IHe2 with (t := (rpnop sub :: nil) ++ t).

assert (step3: 
      rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop sub :: nil) ++ t)
    = rpn_eval_ (eval e1 - eval e2 :: s) t).
simpl.
reflexivity.
rewrite step1.
rewrite step2.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc with (x:= rpn e1).
rewrite app_assoc with (z:= t).
reflexivity.

(* and again for multiplication *)
intros s t.
assert (s1 := (rpn e1 ++ rpn e2 ++ rpnop mul :: nil) ++ t 
             = rpn e1 ++ (rpn e2 ++ ((rpnop mul :: nil) ++ t))).
replace ((rpn e1 ++ rpn e2 ++ rpnop mul :: nil) ++ t) 
   with (rpn e1 ++ (rpn e2 ++ ((rpnop mul :: nil) ++ t))).

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop mul :: nil) ++ t)
             = rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop mul :: nil) ++ t)).
apply IHe1 with (t := rpn e2 ++ (rpnop mul :: nil) ++ t).

assert (step2: rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop mul :: nil) ++ t)
             = rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop mul :: nil) ++ t)).
apply IHe2 with (t := (rpnop mul :: nil) ++ t).

assert (step3: 
      rpn_eval_ (eval e2 :: eval e1 :: s) ((rpnop mul :: nil) ++ t)
    = rpn_eval_ (eval e1 * eval e2 :: s) t).
simpl.
reflexivity.
rewrite step1.
rewrite step2.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc with (x:= rpn e1).
rewrite app_assoc with (z:= t).
reflexivity.
Qed.

(* 3.6
 * Prove that 
 *   forall e:Exp, Some (eval e) = rpn_eval (rpn e)
 *  This solution relies on the 'step' theorem proved earlier 
 *)

Theorem interpret_equals_compile : forall e:Exp, Some (eval e) = rpn_eval (rpn e).
unfold rpn_eval.
induction e.
simpl.
reflexivity.
induction b.
simpl.
rewrite step.
rewrite step.
simpl.
reflexivity.
simpl.
rewrite step.
rewrite step.
simpl.
reflexivity.
simpl.
rewrite step.
rewrite step.
simpl.
reflexivity.
Qed.


(* 3.7 
 * Generalize the above to Expressions containing variables, and evaluation
 * with respect to an environment of bindings of variables to nats.
 *)

Inductive Exp2 := 
| lit2 : nat -> Exp2 
| var : nat -> Exp2
| letvar : nat -> Exp2 -> Exp2 -> Exp2
| exp2 : BinOp -> Exp2 -> Exp2 -> Exp2 .

Fixpoint lookup (n: nat) (l: list nat) : nat :=
match l with
| nil => 0
| h :: tl => match n with
  | 0 => h
  | S n0 => lookup n0 tl
  end
end.

Fixpoint setvar (n m: nat) (l: list nat) : (list nat) := 
match l with
| nil => 
  match n with 
  | 0 => m :: nil
  | S n0 => 0 :: setvar n0 m nil
  end
| h :: tl => match n with
  | 0 => m :: tl
  | S n0 => h :: setvar n0 m tl
  end
end.

Fixpoint eval2 (e: Exp2) (env: list nat) : nat := match e with
| lit2 n => n
| var n => lookup n env
| letvar n e1 e2 => eval2 e2 (setvar n (eval2 e1 env) env)
| exp2 op e1 e2 => 
  match op with
  | add => (eval2 e1 env) + (eval2 e2 env)
  | sub => (eval2 e1 env) - (eval2 e2 env)
  | mul => (eval2 e1 env) * (eval2 e2 env)
  end  
end.

Inductive RPNSymbol2 := 
| rpnlit2 : nat -> RPNSymbol2
| rpnvar : nat -> RPNSymbol2
| popframe : RPNSymbol2
| pushframe : RPNSymbol2
| rpnop2 : BinOp -> RPNSymbol2.

Definition RPN2 := list RPNSymbol2.

Fixpoint rpn2 (e: Exp2) : RPN2 := match e with
| lit2 n => (rpnlit2 n) :: nil
| var n => (rpnvar n) :: nil
| letvar n e1 e2 => 
    (rpn2 e1) ++ ((rpnlit2 n) :: pushframe :: rpn2 e2) ++ (popframe :: nil)
| exp2 op e1 e2 => app (rpn2 e1) (app (rpn2 e2) (rpnop2 op :: nil))
end.

(* Adds to rpn_eval_ the concept of stackframes for the environment *)
Fixpoint rpn2_eval_ (s : list nat) (f : list (list nat)) (code: RPN2) : option nat := 
match f with 
| nil => None 
| f1 :: fx =>
  match code with
  | nil => 
    match s with 
    | nil => None 
    | r :: _ => Some r 
    end
  | h :: tl => 
    match h with
    | rpnlit2 n => rpn2_eval_ (n :: s) f tl
    | rpnvar n => rpn2_eval_ (lookup n f1 :: s) f tl
    | popframe => rpn2_eval_ s fx tl
    | pushframe => 
      match s with
      | nil => None
      | n1 :: s1 => 
        match s1 with 
        | nil => None
        | n2 :: s2 => rpn2_eval_ s2 ((setvar n1 n2 f1) :: f) tl
        end
      end
    | rpnop2 op => 
      match s with
      | nil => None 
      | n1 :: s1 => 
        match s1 with
        | nil => None
        | n2 :: s2 => 
          match op with
          | add => rpn2_eval_ (n2 + n1 :: s2) f tl
          | sub => rpn2_eval_ (n2 - n1 :: s2) f tl
          | mul => rpn2_eval_ (n2 * n1 :: s2) f tl
          end
        end
      end
    end
  end 
end.

Definition rpn2_eval (code : RPN2) (env : list nat) : option nat :=
rpn2_eval_ nil (env :: nil) code.

Definition testExp : Exp2 := 
letvar 0 
(* = *)
(exp2 add (lit2 3) (lit2 6))
(* in *) 
(exp2 add
  (exp2 mul (var 0) 
  (letvar 0
    (* = *)
    (lit2 2)
    (* in *)
    (var 0)
  ))
  (var 0)
).

Eval compute in eval2 testExp (0 :: nil).
Eval compute in rpn2_eval_ nil ((0 :: nil) :: nil) (rpn2 testExp).
Eval compute in rpn2_eval (rpn2 testExp) (0 :: nil).

Theorem step2 : 
  forall e : Exp2, forall s m : list nat,
    forall t : RPN2, forall fx : list (list nat),
      rpn2_eval_ s (m :: fx) (app (rpn2 e) t) = rpn2_eval_ ((eval2 e m) :: s) (m :: fx) t.
intros e.
induction e.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
(* Case letvar, so the push and pop steps *)
intros s m t fx.
assert (s1 : 
  (rpn2 e1 ++ rpnlit2 n :: (pushframe :: (rpn2 e2 ++ (popframe :: nil)))) ++ t 
  =
  rpn2 e1 ++ ((rpnlit2 n :: (pushframe :: (rpn2 e2 ++ (popframe :: nil)))) ++ t)    
  ).
rewrite app_assoc.
reflexivity.
rewrite s1.
rewrite IHe1 with (t := (rpnlit2 n :: pushframe :: rpn2 e2 ++ popframe :: nil) ++ t) (fx := fx).
simpl.
assert (s2 : (rpn2 e2 ++ popframe :: nil) ++ t = 
              rpn2 e2 ++ ((popframe :: nil) ++ t)).
rewrite app_assoc.
reflexivity.
rewrite s2.
apply IHe2 with (t := (popframe :: nil) ++ t).
(* Case exp2 *)
simpl.
induction b.

(* addition *)
intros s m t fx.
replace ((rpn2 e1 ++ rpn2 e2 ++ rpnop2 add :: nil) ++ t)
       with (rpn2 e1 ++ (rpn2 e2 ++ ((rpnop2 add :: nil) ++ t))).
assert (step1: 
    rpn2_eval_ s (m :: fx) (rpn2 e1 ++ rpn2 e2 ++ (rpnop2 add :: nil) ++ t) 
  = rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 add :: nil) ++ t)).
apply IHe1 with (t := rpn2 e2 ++ (rpnop2 add :: nil) ++ t).
rewrite step1.

assert (step2: 
    rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 add :: nil) ++ t)
  = rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 add :: nil) ++ t)).
apply IHe2 with (t := (rpnop2 add :: nil) ++ t) (m := m) (fx := fx).
rewrite step2.

assert (step3: 
    rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 add :: nil) ++ t)
  = rpn2_eval_ (eval2 e1 m + eval2 e2 m :: s) (m :: fx) t).
simpl.
reflexivity.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc.
reflexivity.

(* subtraction *)
intros s m t fx.
replace ((rpn2 e1 ++ rpn2 e2 ++ rpnop2 sub :: nil) ++ t)
       with (rpn2 e1 ++ (rpn2 e2 ++ ((rpnop2 sub :: nil) ++ t))).
assert (step1: 
    rpn2_eval_ s (m :: fx) (rpn2 e1 ++ rpn2 e2 ++ (rpnop2 sub :: nil) ++ t) 
  = rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 sub :: nil) ++ t)).
apply IHe1 with (t := rpn2 e2 ++ (rpnop2 sub :: nil) ++ t).
rewrite step1.

assert (step2: 
    rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 sub :: nil) ++ t)
  = rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 sub :: nil) ++ t)).
apply IHe2 with (t := (rpnop2 sub :: nil) ++ t) (m := m) (fx := fx).
rewrite step2.

assert (step3: 
    rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 sub :: nil) ++ t)
  = rpn2_eval_ (eval2 e1 m - eval2 e2 m :: s) (m :: fx) t).
simpl.
reflexivity.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc.
reflexivity.

(* multiplication *)
intros s m t fx.
replace ((rpn2 e1 ++ rpn2 e2 ++ rpnop2 mul :: nil) ++ t)
       with (rpn2 e1 ++ (rpn2 e2 ++ ((rpnop2 mul :: nil) ++ t))).
assert (step1: 
    rpn2_eval_ s (m :: fx) (rpn2 e1 ++ rpn2 e2 ++ (rpnop2 mul :: nil) ++ t) 
  = rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 mul :: nil) ++ t)).
apply IHe1 with (t := rpn2 e2 ++ (rpnop2 mul :: nil) ++ t).
rewrite step1.

assert (step2: 
    rpn2_eval_ (eval2 e1 m :: s) (m :: fx) (rpn2 e2 ++ (rpnop2 mul :: nil) ++ t)
  = rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 mul :: nil) ++ t)).
apply IHe2 with (t := (rpnop2 mul :: nil) ++ t) (m := m) (fx := fx).
rewrite step2.

assert (step3: 
    rpn2_eval_ (eval2 e2 m :: eval2 e1 m :: s) (m :: fx) ((rpnop2 mul :: nil) ++ t)
  = rpn2_eval_ (eval2 e1 m * eval2 e2 m :: s) (m :: fx) t).
simpl.
reflexivity.
rewrite step3.
reflexivity.
rewrite app_assoc.
rewrite app_assoc.
rewrite app_assoc.
reflexivity.
Qed.

Theorem interpret_equals_compile2 : forall e:Exp2, forall m: list nat, Some (eval2 e m) = rpn2_eval (rpn2 e) m.
unfold rpn2_eval.
induction e.
simpl.
reflexivity.
simpl.
reflexivity.
intro m.
replace (rpn2 (letvar n e1 e2)) with (rpn2 (letvar n e1 e2) ++ nil).
rewrite step2 with (e := (letvar n e1 e2)) (m := m) (s := nil) (t := nil) (fx := nil).
simpl.
reflexivity.
apply app_nil.
intro m.
replace (rpn2 (exp2 b e1 e2)) with (rpn2 (exp2 b e1 e2) ++ nil).
induction b.
rewrite step2 with (m := m) (s := nil) (t := nil) (fx := nil).
simpl.
reflexivity.
rewrite step2 with (m := m) (s := nil) (t := nil) (fx := nil).
simpl.
reflexivity.
rewrite step2 with (m := m) (s := nil) (t := nil) (fx := nil).
simpl.
reflexivity.
apply app_nil.
Qed.




(* Some usefull functions for the simple expression compiler *)

Definition compile (s : string) : option RPN := option_map (rpn) (lex_and_parse s).

Eval compute in compile "4 + 5".
Eval compute in compile "7 + 8 + 6".
Eval compute in compile "(5 + 7) + (6 * 3)".
Eval compute in compile "(((1)) + (1 + 5) * (1 + 6))".


Definition compile_and_run (s : string) : option nat := option_flatten (nat) 
  (option_map (rpn_eval) (compile s)).

Eval compute in compile_and_run "4 + 5".

Definition interpret (s: string) : option nat := option_map (eval) (lex_and_parse s).
Eval compute in interpret "4 + 5".