
(* material : Lecture Notes on the Lambda Calculus by Peter Selinger *)


Fail Definition Ident := fun x => x.
(* Cannot infer the type of x. *)
(* You can't do Ident Ident .So coq can't implements untyped lambda *)

Definition Ident := fun x:Set => x.

Fail Compute Ident Ident.
(* Type error *)


(* But!!! We cant define a new Type *)

(* First, variable *)
(* Inductive var : Type := *)
(*   | Var : nat -> var. *)

(* Inductive term : Type := *)
(* | var : term *)                  (* how to express this: var is term *)
(* | App : term -> term -> term *)
(* | Lambda : var -> term -> term. *)

Inductive var : Type :=
  | X : nat -> var.

Check X 0.

Inductive term : Type :=
  | Var : var -> term
  | Lambda  : var -> term -> term
  | App : term -> term -> term.

Check Var (X 0).
Check Lambda (X 0) (Var (X 0)). (* \x.x *)
Check App (Lambda (X 0) (Var (X 0))) (Var (X 0)). (* \x.x x *)

(** compute free vaiable *)
(* compute list minus list *)

Definition var_eq (x y : var) : bool :=
  match x with
  | X nx => match y with
            |X ny =>  Nat.eqb nx ny
            end
  end.

Require Export List.
Check filter.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(* I don't know how to import these notation ... *)

Fixpoint remove_one(l : list var) (x : var) :=
  filter (fun xi => negb (var_eq xi x)) l.

Example remove_one_test : remove_one [X 1; X 2; X 0] (X 0) = [X 1; X 2].
Proof. simpl. reflexivity. Qed.

Fixpoint minus (l1 l2 : list var) : list var :=
  match l2 with
  | [] => l1
  | h :: tail =>  minus (remove_one l1 h) tail
  end.

Example minus_test : minus [X 1; X 2; X 3] [X 1; X 3] = [X 2].
Proof. reflexivity. Qed.

Fixpoint FV (t : term) : list var :=
  match t with
  | Var xi => xi :: nil
  | Lambda x  t' => remove_one (FV t') x
  | App m n => FV m ++ FV n
  end.

Example FV_test1 : FV (Lambda (X 0) (Var (X 0))) = []. (* \x.x *)
Proof. reflexivity. Qed.

(* \x.x x *)
Example FV_test2 : FV (App (Lambda (X 0) (Var (X 0))) (Var (X 0))) = [X 0].
Proof. reflexivity. Qed.

(* rename y by x(whether free or not) in m , or m{y/x} *)

Fixpoint renaming (m : term) (y x : var) : term :=
  match m with
  | Var xi => if var_eq xi x then Var y
              else Var xi
  | Lambda xi m' =>  if var_eq xi x
                     then Lambda y (renaming m' y x)
                     else Lambda xi (renaming m' y x)
  | App m1 m2 =>  App (renaming m1 y x) (renaming m2 y x)
  end. 


(*   \x1.x0 x0   {x3/x0} *)
Example renaming_test1 :
  renaming (App (Lambda (X 1) (Var (X 0))) (Var (X 0))) (X 3) (X 0)  =
           (App (Lambda (X 1) (Var (X 3))) (Var (X 3))).
Proof. reflexivity. Qed.

(* get all var in a term *)
Fixpoint all_var (t : term) : list var :=
  match t with
  | Var x => [x]
  | Lambda x t' => x :: all_var t'
  | App t1 t2 => (all_var t1) ++ (all_var t2)
  end.
Example all_var_test1 :
  all_var (App (Lambda (X 1) (Var (X 0))) (Var (X 4))) = [X 1; X 0; X 4].
Proof. simpl. reflexivity. Qed.

Fixpoint var_in_list (x : var) (l : list var) : bool :=
  match l with
  | [] => false
  | h :: l' => if var_eq  x h then true else var_in_list x l'
  end.
Example var_in_list_test1:
  var_in_list (X 3) [X 1; X 0; X 4] = false.
Proof. reflexivity. Qed.
Example var_in_list_test2:
  var_in_list (X 4) [X 1; X 0; X 4] = true.
Proof. reflexivity. Qed.



(* \alpha-equivalence *)
Axiom alpha_eq : forall (t:term) (x y:var),
    not (In y (all_var t)) -> Lambda x t = Lambda y (renaming t y x).

(* proof  \x1.x1 = \x0.x0 *)
Example alpha_eq_test1:
  Lambda (X 1) (Var (X 1)) = Lambda (X 0) (Var (X 0)).
Proof.
  replace (Lambda (X 0) (Var (X 0)))
  with (Lambda (X 0) (renaming (Var (X 1)) (X 0) (X 1))).
  apply alpha_eq.
  simpl.
  intros [h1 | h2].
  - inversion h1. - exact h2.
  - simpl. reflexivity.
Qed.

(* rules for alpha-equivalence:
 refl:       M = M.
 symm:       M = N -> N = M.
 trans:      M = N -> N = P -> M = P
 cong:       M = M' -> N = N' -> App M N = App M' N'
 xi :        M = M' -> Lambda x M = Lambda x M'     
 alpha       y \notin M ->  Lambda x M = Lambda y (M{y/x})
*)
Theorem refl : forall (M : term), M = M.
Proof. intros. reflexivity. Qed.

Theorem symm: forall (M N : term), M = N -> N = M.
Proof. intros. symmetry. apply H. Qed.

Theorem trans: forall (M N P : term), M = N -> N = P -> M = P.
Proof. intros. rewrite H. apply H0. Qed.

Theorem cong: forall (M N M' N' : term), M = M' ->  N = N' -> App M N = App M' N'.
Proof. intros. rewrite H. rewrite H0. reflexivity. Qed.

Theorem xi: forall(M M' : term) (x : var), M = M' -> Lambda x M = Lambda x M'.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem alpha: forall (M : term) (x y: var),
    ~(In y (all_var M)) -> Lambda x M = Lambda y (renaming M y x).
Proof. apply alpha_eq. Qed.


(** Substitution *)

(* find var in a term having the biggest nat in it *)
Definition max_var (M : term) : var :=
  X (fold_right Nat.max 0 (map (fun v:var => match v with | X n => n end)
                               (all_var M))).
Theorem max_var_test1:  max_var (App (Lambda (X 1) (Var (X 5))) (Var (X 0))) = (X 5).
Proof. reflexivity. Qed.

Definition next_var (M : term) : var :=
  X (S (fold_right Nat.max 0 (map (fun v:var => match v with | X n => n end)
                               (all_var M)))).
Theorem next_var_test1:  next_var (App (Lambda (X 1) (Var (X 5))) (Var (X 0))) = (X 6).
Proof. reflexivity. Qed.


(* M[N/x],  capture-avoiding, substitute free occurrences of x in M by N *)
Fail Fixpoint subs (M N : term) (x : var) :=
  match M with
  | Var xi => if var_eq xi x then N else M
  | App M1 M2 => App (subs M1 N x) (subs M2 N x)
  | Lambda y M' =>  if var_eq y x
                    then M
                    else if negb (var_in_list y (FV N)) 
                         then Lambda y (subs M' N x)
                         else let y' := next_var (App M N) in
                              Lambda y' (subs (renaming M' y' y) N x)
  end.
(* wooooooooooooooc                                       *)
(* Error: Cannot guess decreasing argument of fix.        *)
(* you can't write unterminate program in coq ??????!!!!! *)
(* but renaming won't make M' bigger                      *)


























