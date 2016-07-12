Require Import Coq.Unicode.Utf8 Arith FunctionalExtensionality String Coq.Program.Equality.

Set Implicit Arguments.

Inductive exp : Set :=
| Var : string -> exp
| Const : bool -> exp
| Abs : string -> exp -> exp
| App : exp -> exp -> exp
| If : exp -> exp -> exp -> exp.

Inductive ty  : Set :=
| Bool : ty
| Fun : ty -> ty -> ty.

Inductive value : exp -> Prop :=
| VBool : forall b, value (Const b)
| VAbs : forall x e, value (Abs x e).

Definition tyenv := list (string * ty).

Definition venv := list (string * exp).

Definition extend {T : Set} (G : list (string * T)) (x:string) (t : T) : list (string * T) :=
  cons (x,t) G.

Fixpoint mextend  {T : Set} (e : list (string * T)) (G : list (string * T)) {struct G} : list (string * T) :=
  match G with
    | nil => e
    | cons (x,v) G' => extend (mextend e G') x v
  end.

Fixpoint lookup {T : Set}
                (E : list (string * T))
                (x:string) : option T :=
  match E with
    |cons (y,t) rest => if string_dec y x then Some t else lookup rest x
    |nil => None
  end.

Fixpoint drop {T : Set}
         (x:string)
         (E : list (string * T)) : list (string * T) :=
  match E with
    | nil => nil
    | cons (y,t) rest => if string_dec x y then drop x rest else cons (y,t) (drop x rest)
  end.

Reserved Notation "Γ '|--' e" (at level 10).

Inductive has_type : tyenv -> exp -> ty -> Prop :=
| TConst : forall Γ b, has_type Γ (Const b) Bool
| TVar : forall Γ x t, lookup Γ x = Some t -> has_type Γ (Var x) t
| TAbs : forall Γ x e t t', has_type (extend (drop x Γ) x t) e t' ->
                       has_type Γ (Abs x e) (Fun t t')
| TApp : forall Γ e e' t1 t2, has_type Γ e (Fun t1 t2) ->
                         has_type Γ e' t1 ->
                         has_type Γ (App e e') t2
| TIf : forall Γ e1 e2 e3 t, has_type Γ e1 Bool ->
                        has_type Γ e2 t ->
                        has_type Γ e3 t ->
                        has_type Γ (If e1 e2 e3) t
where "Γ '|--' e" := (has_type Γ e).

Hint Constructors has_type ty exp value.


Inductive context : Set :=
| CHole : context
| CApp1 : context -> exp -> context
| CApp2 : exp -> context -> context
| CIf : context -> exp -> exp -> context.

Inductive plug : context -> exp -> exp -> Prop :=
| PHole : forall e, plug CHole e e
| PApp1 : forall e e' C e2, plug C e e' ->
                       plug (CApp1 C e2) e (App e' e2)
| PApp2 : forall e e' C v, plug C e e' ->
                       value v ->
                       plug (CApp2 v C) e (App v e')
| PIf : forall e e' C e2 e3, plug C e e' ->
                        plug (CIf C e2 e3) e (If e' e2 e3).

Fixpoint sub (x:string) (e:exp) (e':exp) : exp :=
  match e with
    | Var y => if string_dec y x then e' else e
    | Const b => e
    | Abs y body => if string_dec y x
                   then e
                   else Abs y (sub x body e')
    | App e1 e2 => App (sub x e1 e') (sub x e2 e')
    | If ec e1 e2 => If (sub x ec e')
                       (sub x e1 e')
                       (sub x e2 e')
    end.

Notation "'[' x ':=' s ']' t" := (sub x t s) (at level 20).


Inductive step_prim : exp -> exp -> Prop :=
| SBeta : forall x e v, value v -> step_prim (App (Abs x e) v)
                                       ([x:=v]e)
| SIfTrue : forall e1 e2, step_prim (If (Const true) e1 e2) e1
| SIfFalse : forall e1 e2, step_prim (If (Const false) e1 e2) e2.

Inductive step : exp -> exp -> Prop :=
| Step : forall C e1 e2 e1' e2', plug C e1 e1' ->
                            plug C e2 e2' ->
                            step_prim e1 e2 ->
                            step e1' e2'.

Inductive multi A (R : A -> A -> Prop) : A -> A -> Prop :=
| MultiRefl : forall x,
  multi R x x
| MultiStep : forall x1 x2 x3,
  R x1 x2
  -> multi R x2 x3
  -> multi R x1 x3.

Hint Constructors multi.

Lemma multi_trans {A} : forall (R : A -> A -> Prop) a b c,
                      multi R a b ->
                      multi R b c ->
                      multi R a c.
Proof.
  intros.
  induction H; eauto.
Qed.


Lemma plug_same : forall C x e1 e2,
                    plug C x e1 ->
                    plug C x e2 ->
                    e1 = e2.
Proof.
  intro C.
  induction C; intros.

  inversion H. inversion H0. subst. assumption.

  inversion H. inversion H0.
  assert (e' = e'0).
  eapply IHC. eapply H5. eassumption.
  rewrite H11; reflexivity.

  inversion H. inversion H0.
  assert (e' = e'0).
  eapply IHC. eauto. eassumption.
  subst; reflexivity.

  inversion H. inversion H0.
  assert (e' = e'0).
  eapply IHC. eauto. eassumption.
  subst; reflexivity.
Qed.

Lemma plug_exists : forall C e e' e1,
                      plug C e e' ->
                      multi step e e1 ->
                      exists e1', plug C e1 e1'.
Proof.
  intro C.
  induction C; intros.
  (* hole *)
  exists e1. eapply PHole.
  (* app1 *)
  inversion H; subst.
  eapply IHC in H5; eauto. inversion H5.
  exists (App x e). eapply PApp1; eauto.
  (* app2 *)
  inversion H; subst.
  eapply IHC in H3; eauto. inversion H3.
  exists (App e x). eapply PApp2; eauto.
  (* if *)
  inversion H; subst.
  eapply IHC in H6; eauto. inversion H6.
  exists (If x e e0). eapply PIf; eauto.
Qed.

Lemma plug_compose : forall C C' e e' e'',
                       plug C e e' ->
                       plug C' e' e'' ->
                       (exists C'', forall e1 e2 e3,
                                 plug C e1 e2 ->
                                 plug C' e2 e3 ->
                                 plug C'' e1 e3).
Proof.
  induction 2.
  (* hole *)
  exists C. intros. inversion H1; subst. eauto.
  (* app1 *)
  apply IHplug in H. inversion H.
  exists (CApp1 x e2). intros.
  destruct e4; inversion H3; subst.
  eapply PApp1. eapply H1; eauto.
  (* app2 *)
  apply IHplug in H. inversion H.
  exists (CApp2 v x). intros.
  destruct e3; inversion H4; subst.
  eapply PApp2. eapply H2; eauto. eauto.
  (* if *)
  apply IHplug in H. inversion H.
  exists (CIf x e2 e3). intros.
  destruct e5; inversion H3; subst.
  eapply PIf. eapply H1; eauto.
Qed.

Lemma step_context : forall C e1 e2,
                        step e1 e2 ->
                        forall e1' e2',
                        plug C e1 e1' ->
                        plug C e2 e2' ->
                        step e1' e2'.
Proof.
  intros.
  inversion H; subst.
  destruct (plug_compose H2 H0).
  eapply Step.
  eapply (H5 _ _ _ H2 H0).
  eapply (H5 _ _ _ H3 H1).
  eauto.
Qed.

Lemma multi_context : forall C e1 e2,
                        multi step e1 e2 ->
                        forall e1' e2',
                        plug C e1 e1' ->
                        plug C e2 e2' ->
                        multi step e1' e2'.
Proof.
  intros C e1 e2 H.
  induction H; intros.

  assert (e1' = e2'). eapply plug_same; eauto.
  subst. econstructor.

  assert (exists ex2, plug C x2 ex2). eapply plug_exists. eapply H1. eapply MultiStep. eapply H. econstructor.

  inversion H3.

  assert (H5: step e1' x).
  Focus 2. eapply MultiStep. eapply H5. eapply IHmulti.
  assumption. assumption.

  inversion H. subst.

  destruct (plug_compose H5 H1).
  eapply Step.
  eapply (H8 _ _ _ H5 H1).
  eapply (H8 _ _ _ H6 H4).
  eauto.
Qed.

Inductive free_in : string -> exp -> Prop :=
| free_var : forall x, free_in x (Var x)
| free_abs : forall x y e, free_in x e ->
                      x <> y ->
                      free_in x (Abs y e)
| free_app1 : forall x e1 e2, free_in x e1 ->
                         free_in x (App e1 e2)
| free_app2 : forall x e1 e2, free_in x e2 ->
                         free_in x (App e1 e2)
| free_if1 : forall x e1 e2 e3, free_in x e1 ->
                           free_in x (If e1 e2 e3)
| free_if2 : forall x e1 e2 e3, free_in x e2 ->
                           free_in x (If e1 e2 e3)
| free_if3 : forall x e1 e2 e3, free_in x e3 ->
                           free_in x (If e1 e2 e3).

Hint Constructors free_in.

Definition closed t := forall x, ~ free_in x t.

Fixpoint closed_env (e:venv) :=
  match e with
    | nil => True
    | cons (_,e1) en => closed e1 /\ closed_env en
  end.

Definition halts  (e:exp) : Prop :=  exists e', multi step e e' /\  value e'.

Fixpoint SN (T : ty) (t : exp) : Prop :=
  (nil |-- t T) /\ halts t /\
  (match T with
     | Bool => True
     | Fun T1 T2 => forall s, SN T1 s -> SN T2 (App t s)
   end).

Reserved Notation "Γ '|=' Σ" (at level 40).

Inductive fulfills : tyenv -> venv -> Prop :=
| FNil : fulfills nil nil
| FCons : forall x t e Γ Σ,
            SN t e ->
            fulfills Γ Σ ->
            fulfills (cons (x,t) Γ) (cons (x,e) Σ)
where "Γ '|=' Σ" := (fulfills Γ Σ).


Fixpoint close (Σ : venv) (e : exp) : exp :=
  match Σ with
    |nil => e
    |cons (x,v) Σ' => close Σ' ([x:=v]e)
  end.

Lemma close_const : forall Σ b, close Σ (Const b) = (Const b).
Proof.
  intros.
  induction Σ; eauto.
  unfold close. fold close. intuition.
Qed.

Lemma halts_value : forall v, value v -> halts v.
Proof.
  intros.
  unfold halts. exists v. split. eapply MultiRefl. assumption.
Qed.

Lemma sn_halts : forall t e, SN t e -> halts e.
Proof.
  intros.
  unfold SN in H.
  destruct t; inversion H; inversion H1; eauto.
Qed.

Lemma TConst_compat : forall Γ Σ b, Γ |= Σ ->
                               SN Bool (close Σ (Const b)).
Proof.
  intros. unfold SN; fold SN; repeat split; try rewrite close_const; eauto.
  eapply halts_value. eauto.
Qed.


Lemma lookup_fulfill_v : forall (Γ:tyenv) (Σ:venv),
                           Γ |= Σ ->
                           forall x (t:ty),
                             lookup Γ x = Some t ->
                             exists v, lookup Σ x = Some v.
Proof.
  intros Γ Σ H.
  induction H; intros.
  inversion H.
  simpl in *. destruct (string_dec x x0); eauto.
Qed.

Lemma string_dec_refl : forall T s (t:T) (f:T), (if string_dec s s then t else f) = t.
Proof.
  intros.
  destruct (string_dec s s). eauto. exfalso. eauto.
Qed.

Lemma string_dec_ne : forall T s s' (t:T) (f:T), s <> s' -> (if string_dec s s' then t else f) = f.
Proof.
  intros.
  destruct (string_dec s s'). subst. contradiction H. eauto. reflexivity.
Qed.



Lemma sub_closed : forall x e, ~ free_in x e -> forall e', [x:=e']e = e.
Proof.
  intros.
  induction e; simpl; eauto.

  (* var *)
  destruct (string_dec s x); eauto. subst. exfalso.
  eapply H. eapply free_var.
  (* abs *)
  destruct (string_dec s x); eauto.
  rewrite IHe; eauto.
  (* app *)
  rewrite IHe1; eauto.
  rewrite IHe2; eauto.
  (* if *)
  intuition.
  rewrite H0. rewrite H1. rewrite H2. eauto.
Qed.


Lemma close_closed : forall Σ e, closed e -> close Σ e = e.
Proof.
  intro Σ.
  induction Σ; eauto.
  simpl. destruct a.
  intros.
  assert (H1 : [s:=e]e0 = e0).
  Focus 2. rewrite H1. eapply IHΣ. assumption.

  unfold closed in H.
  assert (H1 : ~ free_in s e0). eapply H.

  eapply sub_closed; eauto.
Qed.

Lemma close_var : forall Σ x e, closed_env Σ ->
                           lookup Σ x = Some e ->
                           close Σ (Var x) = e.
Proof.
  intros.
  induction Σ.
  (* nil *)
  inversion H0.
  (* cons *)
  unfold close. fold close. unfold sub. fold sub.
  destruct a.
  destruct (string_dec x s).
  (* x = s *)
  simpl in H0. rewrite e1 in H0.
  rewrite string_dec_refl in H0. inversion H0.
  subst. unfold closed_env in H. fold closed_env in H.
  eapply close_closed; intuition.
  (* x <> s *)
  eapply IHΣ. simpl in H. intuition.
  simpl in H0. destruct (string_dec s x) in H0; intuition.
Qed.

Lemma lookup_fulfill_sn : forall Γ Σ,
                            Γ |= Σ ->
                            forall t x v,
                              lookup Γ x = Some t ->
                              lookup Σ x = Some v ->
                              SN t v.
Proof.
  intros Γ Σ H.
  induction H; intros.
  inversion H.

  unfold lookup in *. destruct (string_dec x x0).
  inversion H1; inversion H2; subst. eauto.
  eauto.
Qed.

Lemma lookup_drop : forall (Γ : list (string * ty)) x y,
                      x <> y ->
                      lookup (drop x Γ) y = lookup Γ y.
Proof.
  intros.
  induction Γ; eauto.
  simpl.
  destruct a.
  destruct (string_dec x s); subst; eauto.
  destruct (string_dec s y); subst; eauto.
  contradiction H. reflexivity.
  destruct (string_dec s y); subst; eauto.
  simpl. rewrite string_dec_refl. reflexivity.
  simpl. rewrite string_dec_ne; eauto.
Qed.

Lemma free_in_context : forall x e t Γ,
                          free_in x e ->
                          Γ |-- e t ->
                              exists t', lookup Γ x = Some t'.
Proof.
  intros.
  induction H0; inversion H; subst; eauto.
  destruct IHhas_type; eauto.
  exists x1. simpl in H1. rewrite string_dec_ne in H1.
  rewrite lookup_drop in H1; eauto.
  eauto.
Qed.

Lemma typable_empty_closed : forall e t, nil |-- e t -> closed e.
Proof.
  intros.
  unfold closed. unfold not.
  intros.
  destruct (free_in_context H0 H). inversion H1.
Qed.

Lemma sn_typable_empty : forall e t, SN t e -> nil |-- e t.
Proof.
  intros.
  destruct t; unfold SN in H; destruct H; eauto.
Qed.

Lemma sn_closed : forall t e, SN t e -> closed e.
Proof.
  intros.
  eapply typable_empty_closed.
  eapply sn_typable_empty.
  eassumption.
Qed.


Lemma fulfill_closed : forall Γ Σ, Γ |= Σ -> closed_env Σ.
Proof.
  intros.
  induction H.
  econstructor.
  simpl.
  split.
  eapply sn_closed.
  eassumption. eassumption.
Qed.



Lemma TVar_compat : forall Γ Σ x t, Γ |= Σ ->
                               lookup Γ x = Some t ->
                                   SN t (close Σ (Var x)).
Proof.
  intros.
  destruct (lookup_fulfill_v H x H0).
  rewrite close_var with (e := x0); eauto.
  eapply lookup_fulfill_sn; eauto.
  eapply fulfill_closed; eauto.
Qed.

Lemma close_abs : forall Σ x e, close Σ (Abs x e) =
                           Abs x (close (drop x Σ) e).
Proof.
  induction Σ; intros.
  reflexivity.
  destruct a.
  simpl. destruct (string_dec x s); simpl; eauto.
Qed.


Lemma context_invariance : forall Γ Γ' e t,
     Γ |-- e t  ->
     (forall x, free_in x e -> lookup Γ x = lookup Γ' x)  ->
     Γ' |-- e t.
Proof.
  intros.
  generalize dependent Γ'.
  induction H; eauto.
  econstructor. rewrite H0 in H. eassumption. eauto.

  econstructor. eapply IHhas_type. intros.
  destruct (string_dec x x0); subst.
  simpl. rewrite string_dec_refl. rewrite string_dec_refl. eauto.
  simpl. rewrite string_dec_ne; eauto. rewrite string_dec_ne; eauto. rewrite lookup_drop. rewrite lookup_drop.
  eapply H0. econstructor; eauto. eauto. eauto.

  econstructor; eauto.

  econstructor; eauto.
Qed.


Lemma substitution_preserves_typing : forall Γ x t v e t',
     (extend Γ x t') |-- e t  ->
     nil |-- v t'   ->
     Γ |-- ([x:=v]e) t.
Proof.
  intros.
  generalize dependent Γ.
  generalize dependent t.
  induction e;
    intros; simpl; inversion H; subst; eauto.
  (* val *)
  destruct (string_dec s x); subst.
  (* = *)
  inversion H. simpl in H3.
  rewrite string_dec_refl in H3. inversion H3. subst.
  eapply context_invariance. eauto.
  intros. destruct (free_in_context H1 H0). inversion H2.
  (* <> *)
  eapply TVar. inversion H. simpl in H3.
  rewrite string_dec_ne in H3; eauto.
  (* abs *)
  destruct (string_dec s x); subst.
  (* = *)
  eapply context_invariance.
  eapply H. intros. inversion H1.
  simpl. rewrite string_dec_ne; eauto.
  (* <> *)
  eapply TAbs.
  eapply IHe.
  eapply context_invariance.
  eapply H5.
  intros. simpl. destruct (string_dec s x0); subst.
  rewrite string_dec_ne; eauto.
  rewrite string_dec_ne; eauto.
Qed.

Lemma sn_types : forall t e, SN t e -> nil |-- e t.
Proof.
  intros.
  destruct t; unfold SN in H; inversion H; eauto.
Qed.


Lemma close_preserves : forall Γ Σ, Γ |= Σ ->
                        forall G e t,
                          (mextend G Γ) |-- e t ->
                          G |-- (close Σ e) t.
Proof.
  induction 1; intros.
  simpl in *; eauto.

  simpl in H1. simpl.
  apply IHfulfills.
  eapply substitution_preserves_typing; eauto.
  eapply sn_types; eauto.
Qed.

Lemma fulfills_drop : forall Γ Σ,
    Γ |= Σ ->
    forall x, (drop x Γ) |= (drop x Σ).
Proof.
  intros c e V. induction V.
    intros. simpl. constructor.
    intros. unfold drop. destruct (string_dec x0 x); auto.
    constructor; eauto.
Qed.

Lemma extend_drop : forall {T:Set}
                      (Γ : list (string * T))
                      (Γ' : list (string * T)) x x',
  lookup (mextend Γ' (drop x' Γ)) x
  = if string_dec x x'
    then lookup Γ' x
    else lookup (mextend Γ' Γ) x.
Proof.
  intros.
  destruct (string_dec x x'); subst.

  induction Γ; eauto.
  destruct a. simpl. rewrite <- IHΓ.
  destruct (string_dec x' s); subst; eauto.
  simpl. rewrite string_dec_ne; eauto.

  induction Γ; eauto.
  simpl. destruct a.
  destruct (string_dec x' s); subst; eauto.
  rewrite IHΓ. simpl. rewrite string_dec_ne; eauto.
  simpl. destruct (string_dec s x); subst; eauto.
Qed.

Lemma preservation : forall Γ e1 e2 t, multi step e1 e2 ->
                                  Γ |-- e1 t ->
                                      Γ |-- e2 t.
Admitted.


Lemma values_dont_step : forall v e, value v -> ~step v e.
Proof.
  unfold not. intros.
  inversion H0;
  inversion H; subst; inversion H1; subst;
  inversion H3.
Qed.


Ltac invert H := inversion H; clear H; subst.
Ltac invert1 H := invert H; [].

Lemma step_prim_deterministic : forall e1 e2 e2',
                                  step_prim e1 e2 ->
                                  step_prim e1 e2' ->
                                  e2 = e2'.
Proof.
  intros.
  invert H; invert H0; eauto.
Qed.

Ltac smash :=
  repeat try match goal with
               |[H : App _ _ = App _ _ |- _] => invert H
               |[H : If _ _ _ = If _ _ _ |- _] => invert H
               |[H : plug _ _ _ |- _] => invert1 H
               |[H : plug _ _ ?v, H1 : value ?v |- _] => invert H
               |[H : step_prim _ _ |- _] => invert H
               |[H : value (App _ _) |- _] => invert H
               |[H : value (If _ _ _) |- _] => invert H
               |[H : If _ _ _ = App _ _ |- _] => invert H
               |[H : App _ _ = If _ _ _ |- _] => invert H
             end.

Lemma plug_step_uniq : forall C e e1 e2,
                         plug C e1 e ->
                         step_prim e1 e2 ->
                         forall C' e1' e2',
                           plug C' e1' e ->
                           step_prim e1' e2' ->
                           C = C' /\ e1' = e1.
Proof.
  intros C e e1 e2 H H0.
  induction H; intros.
  (* hole *)
  inversion H0; inversion H; eauto; subst; eauto.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.
  smash.

  (* app1 *)
  inversion H1.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H8; subst; eauto.
  smash.

  (* app2 *)
  inversion H2.
  smash.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H10; subst; eauto.

  (* if *)
  inversion H1.
  smash.
  assert (C = C0 /\ e1' = e).
  eapply IHplug; eauto. inversion H9; subst; eauto.
Qed.


Lemma step_deterministic : forall e1 e2 e2',
                             step e1 e2 ->
                             step e1 e2' ->
                             e2 = e2'.
Proof.
  induction 1; intros.
  invert H2.
  destruct (plug_step_uniq H H1 H3 H5); subst.
  assert (e2 = e3).
  apply (step_prim_deterministic H1 H5).
  subst.
  destruct (plug_same H4 H0); eauto.
Qed.


Lemma step_preserves_halting : forall e e',
                                 step e e' ->
                                 (halts e <-> halts e').
Proof.
  intros. unfold halts.
  split; intros; inversion H0; clear H0;
  subst; inversion H1; clear H1.
  (* -> *)
  inversion H0; subst. exfalso.
  eapply values_dont_step in H2. eauto.
  assert (x2 = e'). eapply step_deterministic; eauto.
  subst. exists x; eauto.
  (* <- *)
  exists x. split; eauto.
Qed.

Ltac use_sn :=
  match goal with
    | [H : SN _ _ |- _ ] => unfold SN in H; fold SN in H
  end;
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
         end;
  unfold SN; fold SN; intuition.


Ltac use_preservation :=
  match goal with
    | [ H : nil |-- ?e ?t, S : step ?e ?u |- nil |-- ?u ?t ] =>
      eapply preservation; repeat eassumption
  end.

Ltac use_preserve_halting :=
  match goal with
    | [ H : step ?T ?U, H1 : halts ?T |- halts ?U ] =>
      eapply (step_preserves_halting T U); repeat eassumption
    | [ H : multi step ?T ?U, H1 : halts ?T |- halts ?U ] =>
      eapply MultiStep; eauto; eapply (step_preserves_halting T U); repeat eassumption
  end.


Lemma step_preserves_sn : forall t e e',
                            step e e' ->
                            SN t e ->
                            SN t e'.
Proof.
  induction t; intros e e' H H0;

  use_sn; try use_preservation; try use_preserve_halting.

  eapply MultiStep. eapply H; eauto. eauto.
  eapply step_preserves_halting with (e := e); eauto.

  eapply MultiStep. eapply H; eauto. eauto.
  eapply step_preserves_halting with (e := e); eauto.

  eapply IHt2; eauto.

  eapply step_context. eapply H.
  eapply PApp1. eapply PHole.
  eapply PApp1. eapply PHole.
Qed.

Lemma multistep_preserves_sn : forall t e e',
                                 multi step e e' ->
                                 SN t e ->
                                 SN t e'.
Proof.
  intros.
  induction H; eauto.
  eapply IHmulti.
  eapply step_preserves_sn; eauto.
Qed.


Lemma anti_reduct : forall e' e t, multi step e e' ->
                              SN t e' ->
                              nil |-- e t ->
                              SN t e.
Proof.
  intros.
  generalize dependent e.
  generalize dependent e'.
  induction t.
  (* Bool *)
  unfold SN.
  split; eauto. split; eauto.
  (* halting *)
  inversion H0. inversion H3. clear H3 H5.
  unfold halts in *.
  inversion H4. exists x. split. eapply multi_trans. eapply H.
  inversion H3. assumption. inversion H3. assumption.

  (* Fun *)
  unfold SN.
  split; eauto. split.
  (* halting *)
  inversion H0. inversion H3. clear H0 H3.
  unfold halts in *.
  inversion H4. exists x. split. eapply multi_trans. eapply H.
  inversion H0. assumption. inversion H0. assumption.
  (* special *)
  fold SN in *. intros.
  eapply IHt2. inversion H0. inversion H4. clear H0 H4.
  eapply H6. eapply H2. eapply multi_context with (C := CApp1 CHole s). eauto. eapply PApp1. eapply PHole. eapply PApp1. eapply PHole.
  (* typing *)
  eapply TApp; eauto. eapply sn_types in H2; assumption.
Qed.

Lemma anti_reduct' : forall e' e t,
                       nil |-- e t ->
                       multi step e e' ->
                              SN t e' ->
                              SN t e.
Proof.
  intros. eapply anti_reduct; eauto.
Qed.

Lemma swap_sub : forall x1 x2 v1 v2 e,
                   x1 <> x2 ->
                   closed v1 ->
                   closed v2 ->
                   [x1:=v1]([x2:=v2]e) = [x2:=v2]([x1:=v1]e).
Proof.
  intros.
  induction e.
  simpl.
  destruct (string_dec s x1); subst.
  destruct (string_dec x1 x2); subst.
  exfalso; eauto.
  simpl. rewrite string_dec_refl.
  rewrite sub_closed; eauto.
  destruct (string_dec s x2); subst.
  simpl. rewrite string_dec_refl.
  rewrite sub_closed; eauto.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_ne; eauto.
  eauto.
  simpl.
  destruct (string_dec s x1); subst; eauto.
  destruct (string_dec x1 x2); subst; eauto.
  simpl. rewrite string_dec_refl. rewrite string_dec_refl.
  eauto.
  simpl. rewrite string_dec_refl.
  rewrite string_dec_ne; eauto.
  destruct (string_dec s x2); subst; eauto.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_refl. reflexivity.
  simpl. rewrite string_dec_ne; eauto.
  rewrite string_dec_ne; eauto.
  rewrite IHe. reflexivity.
  simpl. rewrite IHe1. rewrite IHe2. eauto.
  simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. eauto.
Qed.


Lemma multi_subst : forall x v1 v2 e,
                      closed v1 -> closed v2 ->
                      [x:=v1]([x:=v2]e) = [x:=v2]e.
Proof.
  intros.
  induction e.
  simpl.
  destruct (string_dec s x); eauto.
  rewrite sub_closed; eauto.
  simpl. rewrite string_dec_ne; eauto.
  eauto.
  simpl. destruct (string_dec s x); eauto.
  simpl. destruct (string_dec s x); eauto.
  exfalso. eapply n; eapply e0.
  simpl. destruct (string_dec s x); eauto.
  rewrite IHe; eauto.
  simpl. rewrite IHe1. rewrite IHe2. eauto.
  simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. eauto.
Qed.

Lemma sub_close: forall Σ x v e,
                      closed v ->
                      closed_env Σ ->
                      close Σ ([x:=v]e) = [x:=v](close (drop x Σ) e).
Proof.
  intro Σ.
  induction Σ; intros; eauto.

  destruct a; subst.
  simpl.

  destruct (string_dec s x); subst; eauto.
  rewrite string_dec_refl.
  rewrite multi_subst. eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto. eauto.

  rewrite string_dec_ne. simpl.
  rewrite swap_sub; eauto.
  eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto. eauto.
Qed.


Lemma multistep_App2 : forall v e e',
                         value v ->
                         multi step e e' ->
                         multi step (App v e) (App v e').
Proof.
  intros.
  eapply multi_context with (e1 := e) (e2 := e'); eauto.
  eapply PApp2. eapply PHole. eauto.
  eapply PApp2. eapply PHole. eauto.
Qed.






Lemma sub_close_extend :
  forall x v e Σ,
    closed v ->
    closed_env Σ ->
    [x:=v](close (drop x Σ) e) =
    close (extend (drop x Σ) x v) e.
Proof.
  intros.
  generalize dependent e.
  simpl.
  induction Σ; intros; eauto.
  destruct a.
  simpl. destruct (string_dec x s); eauto.
  eapply IHΣ; eauto.
  inversion H0; eauto.
  simpl.
  rewrite IHΣ.
  rewrite swap_sub; eauto.
  inversion H0; eauto.
  inversion H0; eauto.
Qed.

Lemma drop_sub : forall Σ x v e,
                   closed v ->
                   closed_env Σ ->
                   close (drop x Σ) ([x:=v]e) =
                   close Σ ([x:=v]e).
Proof.
  intro Σ.
  induction Σ; intros; eauto.
  destruct a; eauto.
  simpl.
  destruct (string_dec x s); eauto.
  subst. rewrite multi_subst. eapply IHΣ; eauto.
  inversion H0; eauto. inversion H0; eauto.
  eauto.
  simpl.
  rewrite swap_sub; eauto.
  eapply IHΣ. inversion H0; eauto. inversion H0; eauto.
  inversion H0; eauto.
Qed.

Lemma extend_drop' : forall Σ (x:string) (v:exp) e,
                       closed_env Σ ->
                       closed v ->
                       close (extend (drop x Σ) x v) e = close (cons (x,v) Σ) e.
Proof.
  intros.
  induction Σ; eauto; try (inversion H).
  destruct a.
  simpl.
  destruct (string_dec x s). subst.
  rewrite multi_subst.
  rewrite (sub_close Σ).
  rewrite sub_close_extend. rewrite IHΣ; eauto. simpl.
  rewrite drop_sub; eauto.
  inversion H; eauto.
  inversion H; eauto. eauto.
  inversion H; eauto.
  eauto.
  inversion H; eauto.
  inversion H; eauto.
  eauto.
  simpl.
  rewrite swap_sub; eauto.
  rewrite drop_sub. reflexivity.
  eauto. eauto.
  inversion H; eauto.
  inversion H; eauto.
Qed.

Lemma lookup_mextend : forall (Γ : list (string * ty)) x x0 t,
                        x <> x0 ->
                        lookup ((x, t) :: Γ) x0 =
                        lookup (mextend (cons (x, t) nil) Γ) x0.
Proof.
  intros.
  simpl. rewrite string_dec_ne; eauto.
  induction Γ; simpl.
  rewrite string_dec_ne; eauto.
  destruct a. simpl.
  rewrite IHΓ. reflexivity.
Qed.



Lemma TAbs_compat : forall Γ Σ x e t t',
                      Γ |= Σ ->
                      (extend Γ x t) |-- e t' ->
                      (forall v, SN t v -> SN t' (close (extend (drop x Σ) x v) e)) ->
                      SN (Fun t t') (close Σ (Abs x e)).
Proof.
  intros.
  assert (WT: nil |-- (Abs x (close (drop x Σ) e)) (Fun t t')).
    { eapply TAbs. eapply close_preserves.
      { eapply fulfills_drop; eauto. }
      eapply context_invariance.
      { apply H0. }
      intros.
      unfold extend. rewrite extend_drop. destruct (string_dec x0 x).
      + subst. simpl. rewrite string_dec_refl. rewrite string_dec_refl. reflexivity.
      + assert (drop x (nil : list (string * ty)) = nil); eauto. rewrite H3. eapply lookup_mextend; eauto.
    }
    simpl. split. rewrite close_abs.
    auto.
    split.
    apply halts_value. rewrite close_abs. apply VAbs.

    intros.
     destruct (sn_halts t s H2) as [v [P Q]].
     pose proof (multistep_preserves_sn t P H2).
     eapply anti_reduct' with (close (cons (x,v) Σ) e).
     eapply TApp. rewrite close_abs.
     apply sn_types; auto.

     simpl.
     split. eauto. split. eapply halts_value. eauto.
     intros.
     assert (halts s0). eapply sn_halts. eapply H4.
     inversion H5.
     eapply anti_reduct' with (e' := close (extend (drop x Σ) x x0) e).
     eapply TApp. eapply WT. eapply sn_types; eauto.
     eapply multi_trans with (b := (App (Abs x (close (drop x Σ) e)) x0)).
     inversion H6. clear H6.
     eapply multi_context with (e1 := s0) (e2 := x0); eauto.
     eapply PApp2. eapply PHole. eauto. eapply PApp2. eapply PHole. eauto.
     eapply MultiStep. eapply Step. eapply PHole. eapply PHole. eapply SBeta. inversion H6; eauto.
     rewrite sub_close_extend. eapply MultiRefl.
     eapply sn_closed. eapply multistep_preserves_sn.
     inversion H6.
     eapply H7. eauto.

     eapply fulfill_closed; eauto.

     eapply H1. eapply multistep_preserves_sn.
     inversion H6.
     eapply H7. eauto.

     eapply sn_types. eapply H2.

     eapply multi_trans.  eapply multistep_App2; eauto.

     rewrite close_abs. eapply VAbs.

     eapply MultiStep.
     eapply Step. eapply PHole. eapply PHole.
     rewrite close_abs.
     eapply SBeta. eauto. simpl.
     rewrite sub_close. eapply MultiRefl.
     eapply sn_closed; eauto.
     eapply fulfill_closed; eauto.

     rewrite <- extend_drop'.
     eapply H1. assumption.
     eapply fulfill_closed; eauto.
     eapply sn_closed; eauto.
Qed.

Lemma close_app : forall Σ e1 e2,
                    close Σ (App e1 e2) =
                    App (close Σ e1) (close Σ e2).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma TApp_compat : forall Γ Σ e1 e2 t t',
                      Γ |= Σ ->
                      SN (Fun t t') (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t' (close Σ (App e1 e2)).
Proof.
  intros.
  rewrite close_app.
  destruct H0. destruct H2. eapply H3; eauto.
Qed.

Lemma close_if : forall Σ e1 e2 e3,
                    close Σ (If e1 e2 e3) =
                    If (close Σ e1) (close Σ e2) (close Σ e3).
Proof.
  intro Σ.
  induction Σ; simpl; intuition.
Qed.

Lemma TIf_compat : forall Γ Σ e1 e2 e3 t,
                      Γ |= Σ ->
                      SN Bool (close Σ e1) ->
                      SN t (close Σ e2) ->
                      SN t (close Σ e3) ->
                      SN t (close Σ (If e1 e2 e3)).
Proof.
  intros.
  rewrite close_if.
  (* need to get a boolean, so we know how to step *)
  inversion H0. inversion H4. inversion H5. inversion H7. eapply preservation with (e2 := x) (Γ := nil) (t := Bool) in H8. inversion H8. inversion H7.
  destruct b; subst.
  (* true *)
  eapply anti_reduct with (e' := close Σ e2); eauto.
  eapply multi_trans with (b := (If (Const true) (close Σ e2) (close Σ e3))).
  eapply multi_context.
  eauto.
  eapply PIf. eapply PHole. eapply PIf. eapply PHole.
  eapply MultiStep. eapply Step with (C := CHole). eapply PHole. eapply PHole. eapply SIfTrue. eapply MultiRefl.
  (* typing *)
  eapply TIf; eauto. eapply sn_types in H1; eauto.
  eapply sn_types in H2; eauto.
  (* false *)
  eapply anti_reduct with (e' := close Σ e3); eauto.
  eapply multi_trans with (b := (If (Const false) (close Σ e2) (close Σ e3))).
  eapply multi_context.
  eauto.
  eapply PIf. eapply PHole. eapply PIf. eapply PHole.
  eapply MultiStep. eapply Step with (C := CHole). eapply PHole. eapply PHole. eapply SIfFalse. eapply MultiRefl.
  (* typing *)
  eapply TIf; eauto. eapply sn_types in H1; eauto.
  eapply sn_types in H2; eauto.

  subst. inversion H9. subst. inversion H9. subst. inversion H9. eapply sn_types; eauto.

Qed.

Lemma extend_drop'' : forall Γ x t t' e,
                        (extend (drop x Γ) x t) |-- e t' ->
                        (extend Γ x t) |-- e t'.
Proof.
  intros.
  eapply context_invariance; eauto.
  intros.
  inversion H0; subst;
  inversion H; subst; simpl;
  destruct (string_dec x x0); eauto; subst;
  simpl;
  try (repeat (rewrite string_dec_refl; eauto));
  try (repeat (rewrite string_dec_ne; eauto));
  rewrite lookup_drop; eauto.
Qed.

Lemma drop_fulfills : forall Γ Σ x,
                        Γ |= Σ ->
                        drop x Γ |= drop x Σ.
Proof.
  intros.
  induction H. econstructor.
  simpl.
  destruct (string_dec x x0); eauto.
  econstructor. eauto. eassumption.
Qed.

Theorem fundamental : forall e t Γ Σ,
                        Γ |-- e t ->
                            Γ |= Σ ->
                            SN t (close Σ e).
Proof.
  intros.
  generalize dependent Σ.
  induction H; intros.

  eapply TConst_compat; eauto.

  eapply TVar_compat; eauto.

  eapply TAbs_compat; eauto.
  eapply extend_drop'' in H. eauto.
  intros. eapply IHhas_type. eapply FCons; eauto.
  eapply drop_fulfills; eauto.

  eapply TApp_compat; eauto.

  eapply TIf_compat; eauto.
Qed.
