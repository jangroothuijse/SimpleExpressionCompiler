Inductive even : nat -> Prop :=
| even0 : even 0
| evenSS : forall n:nat, even n -> even (S (S n)).

Print le.

Require Import Arith.
Require Import Ascii.
Require Import String.

Print string.

Eval compute in length "Hello world!!!".

Print ascii.

Print leb.

Fixpoint ones (s: string) : nat :=
match s with
| EmptyString => 0
| String h t => if (beq_nat 49 (nat_of_ascii h)) then 1 + ones t else ones t
end.

Eval compute in ones "0000110000ol".

Print nat.

Inductive BinOp := | add : BinOp | sub : BinOp | mul : BinOp.

Inductive Exp : Set := 
| lit : nat -> Exp
| exp : BinOp -> Exp -> Exp -> Exp.

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

Inductive RPNSymbol := 
| rpnlit : nat -> RPNSymbol
| rpnop : BinOp -> RPNSymbol.

Definition RPN := list RPNSymbol.

Search list.
Fixpoint rpn (e: Exp) : RPN := match e with
| lit n => cons (rpnlit n) nil
| exp op e1 e2 => app (rpn e1) (app (rpn e2) (cons (rpnop op) nil))
end.

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
(* Theorem interpret_equals_compile_h1 : forall e f g : Exp, forall o : binop,  *)  
Search list.

(* I doont know why i did not have these, please comment them out if you have them *)

Lemma app_nil: forall (a:Type) (x : list a), x ++ nil = x.
induction x.
simpl.
reflexivity.
simpl.
rewrite IHx.
reflexivity.
Qed.

Search list.

Print app_nil.

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

Inductive Exp2 

Definition compile (s : string) : option string := option_map (toRPN) (lex_and_parse s).

Eval compute in compile "4 + 5".
Eval compute in compile "7 + 8 + 6".
Eval compute in compile "(5 + 7) + (6 * 3)".
Eval compute in compile "(((1)) + (1 + 5) * (1 + 6))".

Fixpoint run_ (s: list nat) (t : list Tok) : option nat := 
match t with
| nil => match s with | nil => None | cons r _ => Some r end
| cons h tl => match h with 
  | num n => run_ (cons n s) tl
  | binop op => match s with | nil => None | cons n1 t2 => match t2 with
    | nil => None | cons n2 t3 => match op with
       | add => (run_ (cons (n1 + n2) t3) tl) 
       | sub => (run_ (cons (n1 - n2) t3) tl)
       | mul => (run_ (cons (n1 * n2) t3) tl)
    end end
  end
  | _ => None
  end
end.

Definition run (t : list Tok) : option nat := run_ nil t.

Definition compile_and_run (s : string) : option nat := option_flatten (nat) 
  (option_map (run) (option_flatten (list Tok) (option_map (lex) (compile s)))).

Definition interpret (s: string) : option nat := option_map (eval) (lex_and_parse s).
 (* now interpret = compile_and_run... *)

Theorem compile_equals_run : forall s : string, compile_and_run s = interpret s.
Proof.
intro t.
unfold compile_and_run.
unfold interpret.
unfold compile.
induction (lex_and_parse t).
induction a.
simpl.
induction n.
simpl.
unfold run.
simpl.
reflexivity.
unfold string_of_nat.
unfold string_of_nat_.
by cases.

