(* Require Import Coq.Unicode.Utf8. *)
Require Import Fampoly.Loader.
Require Import Fampoly.LibTactics.
From Coq Require Import Nat.
Require Import PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Notation ident := nat.

Module STLC_Families.

Ltac destruct_ALL :=
  repeat 
    match goal with
    | [h : _ \/ _ |- _ ] => destruct h; subst; eauto
    | [h : _ /\ _ |- _ ] => destruct h; subst; eauto
    | [h : exists _ , _ |- _ ] => destruct h; subst; eauto
    | [h : Some _ = Some _ |- _] => inversion h; subst; eauto
    | [h : {_} + {_} |- _] => destruct h; subst; eauto
    end.

Ltac forwardALL :=
    repeat (
        match goal with
        | h0 : _ -> _ |- _ =>
            forwards*: h0; generalize dependent h0
        end
    ); intros.

Definition partial_map k := ident -> option k.
Definition empty {A : Type} : partial_map A :=
  fun _ => None.
Definition update {A : Type} (m : partial_map A)
  (x : ident) (v : A) : partial_map A := 
  fun x' => if eqb x x' then Some v else m x'. 

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Theorem update_shadow:
  forall {A} {x} {T1} {T0} {G : partial_map A},
  (x |-> T1; x |-> T0; G) = (x |-> T1; G).
  unfold update.
  intros. eapply functional_extensionality. intros.
  destruct (PeanoNat.Nat.eq_dec x x0); subst; 
  try repeat rewrite PeanoNat.Nat.eqb_refl; subst; eauto.
  rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite n in *; eauto.
Qed.


Theorem update_permute:
forall {A} {x x0} {T1} {T0} {G : partial_map A},
  x <> x0 ->
  (x |-> T1; x0 |-> T0; G) = (x0 |-> T0; x |-> T1; G).
  unfold update.
  intros. eapply functional_extensionality. intros.
  destruct (PeanoNat.Nat.eq_dec x x1); subst; 
  try repeat rewrite PeanoNat.Nat.eqb_refl; subst; eauto. 
  assert (x0 <> x1) as H0. intro. symmetry in H0. try contradiction.
  rewrite <- PeanoNat.Nat.eqb_neq in H0. rewrite H0 in *; subst; eauto.
  rewrite <- PeanoNat.Nat.eqb_neq in n. rewrite n in *; subst ;eauto.
Qed.

Lemma empty_not_update:
  forall {T} {G : partial_map T} {k} {v},
    empty <> update G k v.
  intros T G k v h. 
  assert (empty k = (update G k v) k) as H0; try rewrite h; eauto.
  unfold update in H0; eauto.
  rewrite PeanoNat.Nat.eqb_refl in H0.
  try discriminate. 
Qed.

Family STLC.
FInductive ty: Set :=
  | ty_unit : ty
  | ty_arrow : ty -> ty -> ty.


FInductive tm : Set :=
  | tm_var : ident -> tm    
  | tm_abs : ident -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_unit: tm.


FScheme tm_prec PRecT about tm.

FInductive value : self__STLC.tm -> Prop :=
  | vabs   : forall x body , (value (self__STLC.tm_abs x body)) (* omit self__STLCTm later*)
  | vtunit : value (self__STLC.tm_unit).


(* This is the only inversion lemma that we will prove manually
*)

FInduction _value_not_tm_var 
  about self__STLC.value
  motive (fun z (h : self__STLC.value z) => forall i,  (self__STLC.tm_var i) = z -> False).
FProof.
+ intros. prec_discriminate self__STLC.tm_prec H. 
+ intros. prec_discriminate self__STLC.tm_prec H. 
Qed. FEnd _value_not_tm_var .

Field value_not_tm_var : forall i, ~ self__STLC.value (self__STLC.tm_var i) :=
  fun i v => self__STLC._value_not_tm_var (self__STLC.tm_var i) v i eq_refl.


(* Other Simple Inversion Lemma is introduced in this way
    A better way of understanding is, we hold this is an invariant/constraint of the definition
      across all inheritance, i.e. value_not_tm_var never holds under any extension
*)

Closing Fact value_not_tm_app : 
  forall x y, ~ self__STLC.value (self__STLC.tm_app x y) by { intros x y H; inversion H; eauto }.

FRecursion subst 
  about tm 
  motive ((fun (_ : tm) => (ident -> tm -> tm))) by _rec.


Case tm_var  
  := (fun s x t => if (eqb x s) then t else (self__STLC.tm_var s)).

Case tm_abs 
  := (fun s body rec_body => 
     fun x t => 
    if (eqb x s) 
    then (self__STLC.tm_abs s body)
    else (self__STLC.tm_abs s (rec_body x t))).

Case tm_app 
  := (fun t rec_t t0 rec_t0 => 
    fun x t' =>
    self__STLC.tm_app (rec_t x t') (rec_t0 x t')).

Case tm_unit 
  := (fun x t => self__STLC.tm_unit).

FEnd subst.





Field context : Type := partial_map self__STLC.ty.
(* self__STLC --> self$$STLC *)
FInductive step : self__STLC.tm -> self__STLC.tm -> Prop :=
  | st_app0 : forall a a' b,
    (step a a') -> (step (self__STLC.tm_app a b) (self__STLC.tm_app a' b)) 
    (* omit self__STLCTm later*)
  | st_app1 : forall a b b',
    (self__STLC.value a)   -> (step b b') -> (step (self__STLC.tm_app a b) (self__STLC.tm_app a b'))
  | st_app2 : forall b x body,
    (self__STLC.value b) -> (step (self__STLC.tm_app (self__STLC.tm_abs x body) b) (self__STLC.subst body x b)).

Closing Fact not_step_tm_var:
  forall i x',
    ~ step (tm_var i) x' 
  by {intros i x' h; inversion h}.

Closing Fact not_step_tm_abs:
  forall x b x',
    ~ step (tm_abs x b) x' 
  by {intros x b x' h; inversion h}.

Closing Fact not_step_tm_unit:
  forall x',
    ~ step tm_unit x' 
  by { intros x' h; inversion h }.

Closing Fact step_tm_app_inv:
  forall x y t,
    step (tm_app x y) t ->
    ((exists x', step x x'
      /\ t = (tm_app x' y)))
    \/  (value x 
      /\ (exists y', step y y'
      /\ (t = (tm_app x y'))))
    \/  ((exists v body,  x = tm_abs v body 
      /\ value y 
      /\ t =  (subst body v y)))
  by {intros x y t h; inversion h; subst; eauto;
      try (left; repeat eexists; subst; eauto;fail);
      try (right; left; repeat eexists; subst; eauto;fail);
      try (right; right; repeat eexists; subst; eauto;fail)}.

MetaData _steps. 
(* We want a non-extensible steps 
    such that inversion on it is possible *)
Inductive steps : self__STLC.tm -> self__STLC.tm -> Prop:=
  | sts_refl : forall x, steps x x
  | sts_trans : forall x y z, self__STLC.step x y -> steps y z -> steps x z.
FEnd _steps.


Field irreducible : tm -> Prop := fun x => forall x', step x x' -> False.


FInductive has_type : self__STLC.context -> self__STLC.tm -> self__STLC.ty -> Prop :=
  | ht_var : forall G x T1,
      G x = Some T1 ->
      has_type G (self__STLC.tm_var x) T1
  | ht_app : forall G x y T1 T2,
      has_type G x (self__STLC.ty_arrow T1 T2) ->
      has_type G y T1 ->
      has_type G (self__STLC.tm_app x y) T2
  | ht_abs : forall G x body T1 T2,
      has_type (x |-> T1; G) body T2 ->
      has_type G (self__STLC.tm_abs x body) (self__STLC.ty_arrow T1 T2)
  | ht_unit : forall G,
      has_type G self__STLC.tm_unit self__STLC.ty_unit .


Closing Fact not_ht_abs_unit :
  forall g x b,
    ~ has_type g (tm_abs x b) ty_unit
  by { intros g x b h; inversion h}.

Closing Fact ht_abs_inv:
  forall G x body T1 T2,
  has_type G (tm_abs x body) (ty_arrow T1 T2) ->
  has_type (x |-> T1 ; G) body T2
  by {intros G x body T1 T2 h; inversion h; subst; eauto}.



MetaData clean_up_impossibilities.
  Ltac clean_up_impossibilities :=
    match goal with
      | h0: (self__STLC.value (self__STLC.tm_app _ _)) |- _  => destruct (self__STLC.value_not_tm_app _ _ h0)
      | h0: (self__STLC.value (self__STLC.tm_var _ )) |- _  => destruct (self__STLC.value_not_tm_var _ h0)
      | h0: empty _ = Some _ |- _ => inversion h0
      | h0: self__STLC.has_type _ (self__STLC.tm_abs _ _) self__STLC.ty_unit |- _ => destruct (self__STLC.not_ht_abs_unit _ _ _ h0)
      | h0: (self__STLC.step (self__STLC.tm_abs _ _) _) |- _ => destruct (self__STLC.not_step_tm_abs _ _ _ h0)
      | h0: (self__STLC.step (self__STLC.tm_var _) _) |- _ => destruct (self__STLC.not_step_tm_var _ _ h0)
      | h0: (self__STLC.step self__STLC.tm_unit _) |- _ => destruct (self__STLC.not_step_tm_unit _ h0)
      | h0: empty = update _ _ _ |- _ =>
            destruct (empty_not_update h0); eauto
      | h0: update _ _ _ = empty |- _ =>
            symmetry in h0; destruct (empty_not_update h0); eauto
    end.
FEnd clean_up_impossibilities.

Closing Fact value_arrow_type_abs:
  forall t T1 T2,
  value t ->
  has_type empty t (ty_arrow T1 T2) ->
  exists x b, t = tm_abs x b
  by { intros t T1 T2 h1 h2; inversion h1; subst; eauto; inversion h2; subst; eauto }.

Closing Fact value_arrow_type_unit:
  forall t,
  value t ->
  has_type empty t ty_unit ->
  t = tm_unit
  by { intros t h1 h2; inversion h1; subst; eauto; inversion h2; subst; eauto }.

Ltac try_unfold_first := 
  match goal with 
  | [ |- ?h ?t] => try unfold h; try unfold t 
  end.

FInduction progress 
  about has_type
  motive 
  (fun G t T (h : has_type G t T) =>
        G = empty -> (value t) \/ (exists t', step t t')).
FProof.
+  cbn in *; subst; intros G x T h H. subst. inversion h.
+  cbv delta. cbn in *. intros; subst.
right.
forwardALL. clear H0. clear H2.
destruct H1; subst; eauto.
destruct (self__STLC.value_arrow_type_abs _ _ _ H0 __i) as [x' [b HH]]; subst; eauto; destruct_ALL.
eexists. eapply self__STLC.st_app2; eauto.
eexists. eapply self__STLC.st_app1; eauto.
destruct H0 as [t' hh].
eexists. eapply self__STLC.st_app0; eauto.
+ intros; cbn in *. left. eapply  self__STLC.vabs.
+ intros; cbn in *. left. eapply self__STLC.vtunit.
Qed. FEnd progress.

FInduction  subst_lemma
  about has_type
  motive 
  (fun G1 body T2 (h : has_type G1 body T2) =>
  forall G x k T1,
  G1 = (update G x T1) ->
  (forall G', has_type G' k T1) ->
  has_type G (subst body x k) T2).
  FProof.
+ intros; cbn in *. frec_eval self__STLC.subst. 
unfold self__STLC.subst_handler.tm_var. 
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
try rewrite PeanoNat.Nat.eqb_refl in *; eauto. unfold update in e.
rewrite PeanoNat.Nat.eqb_refl in *; eauto. inversion e; subst; eauto.
rewrite <- PeanoNat.Nat.eqb_neq in n; subst; eauto. 
unfold update in e. rewrite n in *; cbn in *; eauto. eapply self__STLC.ht_var; eauto.
+ intros; cbn in *. 
frec_eval self__STLC.subst.
subst; eauto. unfold self__STLC.subst_handler.tm_app. 
eapply self__STLC.ht_app;eauto.

+  intros; cbn in *;subst; eauto.
frec_eval self__STLC.subst. unfold self__STLC.subst_handler.tm_abs.
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;
try rewrite PeanoNat.Nat.eqb_refl; cbn in *; subst; eauto.
++ eapply self__STLC.ht_abs; eauto. rewrite update_shadow in __i; eauto.
++ assert ((x0 =? x) = false) as H0. eapply PeanoNat.Nat.eqb_neq; eauto.
  rewrite H0 in *. eapply self__STLC.ht_abs; eauto.
  eapply H; subst; eauto. eapply update_permute; eauto.

+ intros; cbn in *;subst; eauto. 
frec_eval self__STLC.subst. unfold self__STLC.subst_handler.tm_unit. eapply self__STLC.ht_unit.
Qed. FEnd subst_lemma  .

FInductive fv : ident -> self__STLC.tm -> Prop :=
  | fv_var : forall x,
        fv x (self__STLC.tm_var x) 
  | fv_app1 : forall x a b,
        fv x a -> fv x (self__STLC.tm_app a b)
  | fv_app2 : forall x a b,
        fv x b -> fv x (self__STLC.tm_app a b)
  | fv_abs :  forall x v body,
        fv x body -> x <> v -> fv x (self__STLC.tm_abs v body).
       
  Closing Fact fv_inv_tm_var:
    forall x x',
      fv x (tm_var x') ->
      x = x' 
    by { intros x x' h; inversion h; subst; eauto }.
  
  Closing Fact fv_inv_tm_app:
    forall x a b,
      fv x (tm_app a b) ->
      fv x a \/ fv x b
    by { intros x a b h; inversion h; subst; eauto }.
  
  Closing Fact fv_inv_tm_unit:
    forall x,
    ~ fv x tm_unit
    by {intros x h; inversion h; subst; eauto}.
  
  Closing Fact fv_inv_tm_abs:
    forall x v body,
      fv x (tm_abs v body) ->
      fv x body /\ x <> v
    by {intros x v body h; repeat split; inversion h; subst; eauto}.

FInduction free_var_in_ctx
  about self__STLC.has_type
  motive (
    fun G t T (h : self__STLC.has_type G t T) =>
    forall x,
    fv x t ->
    exists U, G x = Some U
  ).
StartFProofAll. repeat split; repeat (intro; intros); cbn in * .
+ forwards*: self__STLC.fv_inv_tm_var. subst; eauto.
+ forwards*: self__STLC.fv_inv_tm_app. destruct_ALL; eauto.
+ forwards*: self__STLC.fv_inv_tm_abs; destruct_ALL; subst; eauto.
forwards*: H; eauto; destruct_ALL; subst; eauto. unfold update in H3.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto.
+ destruct (self__STLC.fv_inv_tm_unit _ H).
Qed. FEnd free_var_in_ctx.

FInduction 
  free_var_matters
  about self__STLC.has_type
  motive 
  (fun G1 t T (h : self__STLC.has_type G1 t T ) =>
  forall G2,
  (forall x,
  self__STLC.fv x t -> G1 x = G2 x) ->
  self__STLC.has_type G2 t T).
StartFProofAll. repeat split; repeat (intro; intros); cbn in *; eauto using self__STLC.ht_unit.
+ eapply self__STLC.ht_var; eauto. erewrite <- H; eauto. eapply self__STLC.fv_var.
+ eapply self__STLC.ht_app; eauto; eauto using self__STLC.fv_app1,self__STLC.fv_app2.
+ eapply self__STLC.ht_abs; eauto. eapply H; eauto.
intros; subst; eauto. unfold update. 
destruct (PeanoNat.Nat.eq_dec x x0); subst; try rewrite PeanoNat.Nat.eqb_refl; subst; eauto. 
assert ((x =? x0) = false) as hh. eapply PeanoNat.Nat.eqb_neq; eauto.  rewrite hh in *.
eapply H0; eauto using self__STLC.fv_abs.
Qed. FEnd free_var_matters.


  Field weakening_lemma:
      forall k T,
      self__STLC.has_type empty k T ->
      (forall G, self__STLC.has_type G k T).
  FProof.
  intros k T h. intros. 
  eapply self__STLC.free_var_matters; try (exact h). intros x H.
  destruct  (self__STLC.free_var_in_ctx _ _ _ h _ H); try self__STLC.clean_up_impossibilities.
  Qed. FEnd weakening_lemma.
  
FInduction preservation
  about has_type
  motive 
  (fun G t T (h : has_type G t T) =>
  G = empty ->
  forall t',
  step t t' ->
  has_type empty t' T).
StartFProofAll. repeat split; repeat (intro; intros); cbn in *; 
try (subst; cbn in *; self__STLC.clean_up_impossibilities).
(* Case tm_app *) subst; cbn in *. 
destruct (self__STLC.step_tm_app_inv _ _ _ H2); destruct_ALL; eauto; 
try eapply self__STLC.ht_app; subst; eauto; try self__STLC.clean_up_impossibilities.
eapply self__STLC.subst_lemma; eauto. eapply self__STLC.ht_abs_inv; eauto.
intros. eapply self__STLC.weakening_lemma; eauto.
Qed. FEnd preservation.


Field preservation2 :
  forall t t',
    self__STLC.steps t t' ->
    forall T,
    has_type empty t T ->
    has_type empty t' T.
FProof.
intros t t' h. induction h; intros; subst; eauto using self__STLC.preservation.
eapply IHh; eauto. eapply self__STLC.preservation; eauto.
Qed. FEnd preservation2.
  

Field type_safety:
  forall t t' T,
    has_type empty t T ->
    self__STLC.steps t t' ->
    value t' \/ (exists t'', step t' t'').
FProof.
intros. eapply self__STLC.progress; eauto using self__STLC.preservation2.
Qed. FEnd type_safety.

FEnd STLC.

Family STLC_fix extends STLC.


(* Inherit Until Field tm. *)
FInductive tm : Set :=
  | tm_fix : ident -> tm  -> tm.



(* Inherit Until Field subst_handler. *)

FRecursion subst.

Case tm_fix
  := (fun s body rec_body => 
    fun x t => 
    if (eqb x s) 
    then (self__STLC_fix.tm_fix s body)
    else (self__STLC_fix.tm_fix s (rec_body x t))).

FEnd subst.




(* Inherit Field context. *)

FInductive step : self__STLC_fix.tm -> self__STLC_fix.tm -> Prop :=
  | st_fix : forall i body, 
    step (self__STLC_fix.tm_fix i body) (self__STLC_fix.subst body i (self__STLC_fix.tm_fix i body)).


FInductive has_type : (partial_map self__STLC_fix.ty) -> self__STLC_fix.tm -> self__STLC_fix.ty -> Prop :=
  | ht_fix : forall G x body T,
  has_type (x |-> T; G) body T ->
  has_type G (self__STLC_fix.tm_fix x body) T.



(* Closing Fact value_fix_type_inv:
  forall t i T,
  self__STLC_fix.value t ->
  self__STLC_fix.has_type empty t (self__STLC_fix.ty_fix i T) ->
  (exists t', t = self__STLC_fix.tm_fold t' /\ self__STLC_fix.value t')
by {
  intros t i T h h1;
  inversion h; subst; eauto; inversion h1; subst; eauto}.*)

FInduction progress. 
StartFProofAll. 
repeat split; (repeat intro;intros); subst; eauto.

try (right; eauto using self__STLC_fix.st_fix;fail).
Qed. FEnd progress. 



FInduction subst_lemma.
StartFProofAll. repeat split; (repeat intro;intros); subst; frec_eval self__STLC_fix.subst; eauto using self__STLC_fix.ht_fix.  
unfold self__STLC_fix.subst_handler.tm_fix.
destruct (PeanoNat.Nat.eq_dec x0 x); subst; eauto;try rewrite PeanoNat.Nat.eqb_refl; cbn in *; subst; eauto.
+ eapply self__STLC_fix.ht_fix; eauto. erewrite <- update_shadow; eauto.
+   assert ((x0 =? x) = false) as H0. eapply PeanoNat.Nat.eqb_neq; eauto.
  rewrite H0 in *. eapply self__STLC_fix.ht_fix; eauto.
  eapply H; subst; eauto. eapply update_permute; eauto. 

Qed. FEnd subst_lemma.  

FInductive fv  : ident -> self__STLC_fix.tm -> Prop :=
| fv_fix :  forall x v body,
fv x body -> x <> v -> fv x (self__STLC_fix.tm_fix v body).


Closing Fact fv_inv_tm_fix:
forall x v body,
fv x (tm_fix v body) ->
fv x body /\ x <> v
by {intros x v body h; repeat split; inversion h; subst; eauto}.




FInduction free_var_in_ctx.
StartFProofAll. repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
eauto using self__STLC_fix.fv_inv_tm_fix. 
destruct (self__STLC_fix.fv_inv_tm_fix _ _ _ H0); eauto.
forwards: (H x0); destruct_ALL; eauto. unfold update in H3.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto.

Qed. FEnd free_var_in_ctx.



FInduction free_var_matters.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
eapply  self__STLC_fix.ht_fix; eauto. unfold update in *. eapply H; eauto. intros.
destruct (Nat.eq_dec x x0);subst; simpl; eauto; try discriminate; try contradiction. 
rewrite Nat.eqb_refl; eauto.
assert ((x =? x0) = false) as HH. eapply PeanoNat.Nat.eqb_neq; eauto.
rewrite HH in *; eauto. eapply H0; eauto using  self__STLC_fix.fv_fix.

Qed. FEnd free_var_matters.




Closing Fact step_tm_fix_inv:
  forall i body y,
  step (tm_fix i body) y ->
    (y = subst body i (tm_fix i body))
by { intros i body y h; inversion h; subst; eauto }. 


(* Closing Fact step_tm_unfold_inv:
  forall x y,
  self__STLC_fix.step (self__STLC_fix.tm_unfold x) y ->
    (exists x', y = self__STLC_fix.tm_unfold x' /\ self__STLC_fix.step x x') \/ 
    (exists v, x = self__STLC_fix.tm_fold v /\ self__STLC_fix.value v /\ y = v)
by { intros x y h; inversion h; subst; eauto }. *)

Closing Fact ht_fix_inv:
forall G i body T,
has_type G (tm_fix i body) T ->
has_type (i |-> T ; G) body T
by {intros G i body T h; inversion h; subst; eauto}.

FInduction preservation.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
forwards*: self__STLC_fix.step_tm_fix_inv; destruct_ALL; subst.
eapply self__STLC_fix.subst_lemma; intros; eauto.
eapply self__STLC_fix.weakening_lemma; intros; eauto.

eauto using self__STLC_fix.ht_fix.

Qed. FEnd preservation.

FEnd STLC_fix.

Family STLC_isorec extends STLC.

FInductive ty : Set :=
  | ty_var : ident -> ty
  | ty_isorec : ident -> ty -> ty.


Family substT_internal.
Field motive : self__STLC_isorec.ty -> Set := 
  fun (_ : self__STLC_isorec.ty) => ident -> self__STLC_isorec.ty -> self__STLC_isorec.ty.

Field ty_unit :
  ident -> self__STLC_isorec.ty -> self__STLC_isorec.ty :=
  fun x t => self__STLC_isorec.ty_unit.

Field ty_arrow : 
  forall (a : self__STLC_isorec.ty) 
  (rec_a : forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty)
  (b : self__STLC_isorec.ty) 
  (rec_b : forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty),
  forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty :=
  fun a rec_a b rec_b => 
    fun x t => self__STLC_isorec.ty_arrow (rec_a x t) (rec_b x t).


Field ty_var :
  forall (s : ident),
  forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty :=
  fun s => fun x t => 
  if (eqb x s) then t else (self__STLC_isorec.ty_var s).

Field ty_isorec :
  forall (i : ident) (body : self__STLC_isorec.ty) 
  (rec_body : forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty),
  forall (x : ident) (t : self__STLC_isorec.ty), self__STLC_isorec.ty  :=
  fun i body rec_body x t=>
    if (eqb x i) then t else (self__STLC_isorec.ty_isorec i (rec_body x t)).
FEnd substT_internal.

FRecursor substT 
  about self__STLC_isorec.ty 
  motive self__STLC_isorec.substT_internal.motive 
  using self__STLC_isorec.substT_internal 
  by _rec. 

FInductive tm : Set :=
  (* sum *)
  | tm_fold : tm -> tm 
  | tm_unfold : tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_isorec.tm -> Prop :=
  | vfold : forall v, value v -> value (self__STLC_isorec.tm_fold v).

FInduction _value_not_tm_var.
FProof.
+ intros. prec_discriminate self__STLC_isorec.tm_prec H0.
Qed. FEnd _value_not_tm_var.



FRecursion subst.


Case tm_fold := 
  (fun a rec_a =>
      fun x t => 
      self__STLC_isorec.tm_fold (rec_a x t)).

Case tm_unfold := 
  (fun a rec_a =>
      fun x t => 
      self__STLC_isorec.tm_unfold (rec_a x t)).


FEnd subst.



(* Inherit Field subst.

Closing Fact subst_tm_fold :
forall a,
self__STLC_isorec.subst (self__STLC_isorec.tm_fold a) = self__STLC_isorec.subst_internal.tm_fold a (self__STLC_isorec.subst a)
by { intros; eauto }.

Closing Fact subst_tm_unfold :
forall a,
self__STLC_isorec.subst (self__STLC_isorec.tm_unfold a) = self__STLC_isorec.subst_internal.tm_unfold a (self__STLC_isorec.subst a)
by { intros; eauto }. *)



Inherit Field context.

FInductive step : self__STLC_isorec.tm -> self__STLC_isorec.tm -> Prop :=
  | st_fold : forall a a', 
    step a a' ->
    step (self__STLC_isorec.tm_fold a) (self__STLC_isorec.tm_fold a')
  | st_unfold0 : forall a a', 
    step a a' ->
    step (self__STLC_isorec.tm_unfold a) (self__STLC_isorec.tm_unfold a')
  | st_unfold1 : forall v, 
  self__STLC_isorec.value v ->
    step (self__STLC_isorec.tm_unfold (self__STLC_isorec.tm_fold v)) v.

Inherit Until Field has_type.

FInductive has_type : (partial_map self__STLC_isorec.ty) -> self__STLC_isorec.tm -> self__STLC_isorec.ty -> Prop :=
  | ht_fold : forall G t i T, 
      has_type G t (self__STLC_isorec.substT T i (self__STLC_isorec.ty_isorec i T)) ->
      has_type G (self__STLC_isorec.tm_fold t) (self__STLC_isorec.ty_isorec i T) 
  | ht_unfold : forall G t i T, 
    has_type G t (self__STLC_isorec.ty_isorec i T) ->
    has_type G (self__STLC_isorec.tm_unfold t) (self__STLC_isorec.substT T i (self__STLC_isorec.ty_isorec i T)).

Inherit Until Field progress.

Closing Fact value_isorec_type_inv:
  forall t i T,
  value t ->
  has_type empty t (ty_isorec i T) ->
  (exists t', t = tm_fold t' /\ value t')
by {
  intros t i T h h1;
  inversion h; subst; eauto; inversion h1; subst; eauto}.

FInduction progress. 
StartFProofAll. 
repeat split; __unfold_ftheorem_motive; (repeat intro;intros);
subst; eauto;
try
(forwardALL; destruct_ALL;
try (left; eauto using self__STLC_isorec.vfold; fail);
try (right; eauto using self__STLC_isorec.st_fold, self__STLC_isorec.st_unfold0,self__STLC_isorec.st_unfold1 ;fail)).
(* tm_case *)
forwards*: self__STLC_isorec.value_isorec_type_inv; eauto; destruct_ALL; subst; right; eauto using self__STLC_isorec.st_fold, self__STLC_isorec.st_unfold0,self__STLC_isorec.st_unfold1.
Qed. FEnd progress.


FInduction subst_lemma.
StartFProofAll. repeat split; (repeat intro;intros); subst; frec_eval self__STLC_isorec.subst; eauto using self__STLC_isorec.ht_fold,self__STLC_isorec.ht_unfold. 
Qed. FEnd subst_lemma.  

FInductive fv  : ident -> self__STLC_isorec.tm -> Prop :=
  | fv_fold : forall x a,
      fv x a ->
      fv x (self__STLC_isorec.tm_fold a)
  | fv_unfold : forall x a,
      fv x a ->
      fv x (self__STLC_isorec.tm_unfold a).

Closing Fact fv_inv_tm_fold:
  forall x t, fv x (tm_fold t) -> fv x t
by {intros x t h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_unfold:
  forall x t, fv x (tm_unfold t) -> fv x t
by {intros x t h; inversion h; subst; eauto}.



FInduction free_var_in_ctx.
StartFProofAll. repeat split;
(repeat intro;intros); cbn in *; eauto; subst; eauto;
eauto using self__STLC_isorec.fv_inv_tm_fold, self__STLC_isorec.fv_inv_tm_unfold. 
Qed. FEnd free_var_in_ctx.


FInduction free_var_matters.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto using 
self__STLC_isorec.ht_fold,self__STLC_isorec.ht_unfold, self__STLC_isorec.fv_unfold, self__STLC_isorec.fv_fold. 
Qed. FEnd free_var_matters.




(* Inherit Until Field preservation. *)


Closing Fact step_tm_fold_inv:
  forall x y,
  step (tm_fold x) y ->
    (exists x', y = tm_fold x' /\ step x x')
by { intros x y h; inversion h; subst; eauto }.


Closing Fact step_tm_unfold_inv:
  forall x y,
  step (tm_unfold x) y ->
    (exists x', y = tm_unfold x' /\ step x x') \/ 
    (exists v, x = tm_fold v /\ value v /\ y = v)
by { intros x y h; inversion h; subst; eauto }.

Closing Fact ht_fold_inv:
forall G i t T,
has_type G (tm_fold t) (ty_isorec i T) ->
has_type G t (substT T i (ty_isorec i T))
by {intros G i t T h; inversion h; subst; eauto}.

FInduction preservation.
StartFProofAll.
repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto.
forwards*: self__STLC_isorec.step_tm_fold_inv; destruct_ALL; subst; eauto using self__STLC_isorec.ht_fold.


forwards*: self__STLC_isorec.step_tm_unfold_inv; destruct_ALL; subst; eauto using self__STLC_isorec.ht_unfold, self__STLC_isorec.ht_fold_inv.

Qed. FEnd preservation.

FEnd STLC_isorec.
