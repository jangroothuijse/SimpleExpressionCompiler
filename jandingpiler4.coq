Require Import Arith.
Require Import Ascii.
Require Import String.

(* Give an Inductive definition of a datatype Exp of (the abstract syntax
for) ⟨exp⟩s. *)

Inductive BinOp := | add : BinOp | sub : BinOp | mul : BinOp.

Inductive Exp : Set := 
| lit : nat -> Exp
| exp : BinOp -> Exp -> Exp -> Exp.

(* 
  Define a function
  eval: Exp -> nat
  giving a semantics for ⟨exp⟩s.
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

Inductive Tok := | num : nat -> Tok
| binop : BinOp -> Tok | popen : Tok | pclose : Tok.

Require Import List.
Print list.
Print option.
Print andb.

(* returns reversed list of tokens *)
Fixpoint lex_ (s: string) (l: list Tok) (y : bool) : option (list Tok) :=
match s with 
| EmptyString => Some l
| String h t => let c := (nat_of_ascii h) in match c with
  | 32 => lex_ t l false | 43 => lex_ t (cons (binop add) l) false
  | 45 => lex_ t (cons (binop sub) l) false 
  | 42 => lex_ t (cons (binop mul) l) false
  | 40 => lex_ t (cons popen l) false | 41 => lex_ t (cons pclose l) false
  (* to avoid mutual recursion and double testing, lex numbers here *)
  | _ => if (andb (leb c 57) (leb 48 c)) then let d := c - 48 in match l with 
    | nil => lex_ t (cons (num d) nil) true
    | cons x xs => match x with   
      | num n => match y with 
        | false => lex_ t (cons (num d) (cons x xs)) true
        (* in this case, we where already parsing a number *)
        | true => lex_ t (cons (num (n * 10 + d)) xs) true
        end
      | _ => lex_ t (cons (num d) (cons x xs)) true
      end
    end else None
  end  
end.

Search list.
Search option.

Print rev.
Print id.

Fixpoint lex (s: string) : option (list Tok) := 
  option_map (@rev Tok) (lex_ s nil false).

Eval compute in lex "12 * (13 + 1400)".

Fixpoint parse_ (i : nat) (s: list Tok) : prod (list Tok) (option Exp) :=
match i with | 0 => (nil, None) | S j =>
match s with
| nil => (nil, None)
| cons h t => let (t2, oe1) := match h with
  | popen => let (t3, oe2) := parse_ j t in match oe2 with
    | None => (nil, None) 
    | Some e2 => match t3 with 
      | nil => (nil, None)
      | cons h2 t4 => match h2 with 
        | pclose => (t4, oe2) 
        | _=>(nil, None) 
      end 
    end 
  end
  | num n => (t, Some (lit n))
  | _ => (nil, None)
  end in 
  match oe1 with | None => (nil, None) | Some e1 =>
  match t2 with
  | nil => (t2, Some e1)
  | cons h2 t3 => match h2 with
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

Definition parse (s: list Tok) : option Exp := let (t, e) := parse_ (length s) s in 
match t with | nil => e | _ => None end. (* checks that all tokens are consumed *)

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

(* Give an Inductive definition of a datatype RPN of Reverse Polish Notation
for ⟨exp⟩s. *)

Inductive RPNSymbol := 
| rpnlit : nat -> RPNSymbol
| rpnop : BinOp -> RPNSymbol.

Definition RPN := list RPNSymbol.

(* Write a compiler
   rpn : Exp -> RPN *)

Fixpoint rpn (e: Exp) : RPN := match e with
| lit n => cons (rpnlit n) nil
| exp op e1 e2 => app (rpn e1) (app (rpn e2) (cons (rpnop op) nil))
end.

(* Write an evaluator rpn_eval for RPN, returning an option nat. *)

Fixpoint rpn_eval_ (s: list nat) (code: RPN) : option nat := match code with
| nil => match s with | nil => None | cons r _ => Some r end
| cons h tl => match h with
  | rpnlit n => rpn_eval_ (cons n s) tl
  | rpnop op => match s with
    | nil => None 
    | cons n1 s1 => match s1 with
      | nil => None
      | cons n2 s2 => match op with
        | add => rpn_eval_ (cons (n2 + n1) s2) tl
        | sub => rpn_eval_ (cons (n2 - n1) s2) tl
        | mul => rpn_eval_ (cons (n2 * n1) s2) tl
        end
      end
    end
  end
end.

Print rpn_eval_.

Definition rpn_eval (code: RPN) := rpn_eval_ nil code.

Eval compute in option_map (rpn_eval) (option_map (rpn) (lex_and_parse "1+5*6")).
Eval compute in option_map (rpn_eval) (option_map (rpn) (lex_and_parse "15*5+5")).

(* I doont know why i did not have these, please comment them out if you have them *)

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

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop add :: nil) ++ t) = 
   rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop add :: nil) ++ t)).
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

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop sub :: nil) ++ t) = 
   rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop sub :: nil) ++ t)).
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

assert (step1: rpn_eval_ s (rpn e1 ++ rpn e2 ++ (rpnop mul :: nil) ++ t) = 
   rpn_eval_ (eval e1 :: s) (rpn e2 ++ (rpnop mul :: nil) ++ t)).
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

(* Prove that forall e:Exp, Some (eval e) = rpn_eval (rpn e)
   This solution relies on the 'step' theorem proved earlier *)

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




(* Generalize the above to Expressions containing variables, and evaluation
with respect to an environment of bindings of variables to nats. *)

Inductive Exp2 := 
| lit2 : nat -> Exp2 
| var : nat -> Exp2
| exp2 : BinOp -> Exp2 -> Exp2 -> Exp2 .

Fixpoint lookup (n: nat) (l: list nat) : option nat :=
match l with
| nil => None
| h :: tl => match n with
  | 0 => Some h
  | S n0 => lookup n0 tl
  end
end.

Fixpoint eval2 (e: Exp2) (env: list nat) : option nat := match e with
| lit2 n => Some n
| var n => lookup n env
| exp2 op e1 e2 => match eval2 e1 env with
  | None => None
  | Some v1 => match eval2 e2 env with
    | None => None
    | Some v2 => match op with
      | add => Some (v1 + v2)
      | sub => Some (v1 - v2)
      | mul => Some (v1 * v2)
      end
    end
  end
end.

(* Discuss how you might avoid explicit consideration of None terms in the
definition of rpn_eval, and explain how you need to modify your formal-
ization in Coq. *)

(* In order to avoid explicit None's everywhere, one would have to verify that al looked
 up variables actually exists; or default to 0 *)
(* The formalization would have to be changed to include the 'var' case whenever we
 do induction on Exp (now Exp2). The workings of var would be almost identical to a 
 normal literal. *)


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

