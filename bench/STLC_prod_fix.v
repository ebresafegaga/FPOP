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

Family STLC_prod extends STLC.
FInductive ty : Set :=
  | ty_prod : ty -> ty -> ty.



FInductive tm : Set :=
  | tm_prod : tm -> tm -> tm  
  | tm_pi1 : tm -> tm  
  | tm_pi2 : tm -> tm.

(* Inherit Until Field value. *)

FInductive value : self__STLC_prod.tm -> Prop :=
  | vprod : forall a b, value a -> value b -> value (self__STLC_prod.tm_prod a b ).

FInduction _value_not_tm_var.
FProof.
+ intros. prec_discriminate self__STLC_prod.tm_prec H1.
Qed. FEnd _value_not_tm_var.

(* Inherit Field value_not_tm_app. *)

Closing Fact vprod_inv:
  (forall a b,
  value (tm_prod a b) -> value a /\ value b)
  by {intros a b h; 
  repeat split; 
  inversion h; subst; eauto}.

FRecursion subst.
Case tm_pi1 
  := (fun a rec_a x t => tm_pi1 (rec_a x t)).

Case tm_pi2 
  := (fun a rec_a x t => tm_pi2 (rec_a x t)).

Case tm_prod 
  := (fun a rec_a b rec_b x t => 
      tm_prod (rec_a x t) (rec_b x t)).

FEnd subst.

(* Inherit Field subst. *)

(* Closing Fact subst_tm_pi1 : forall a, 
self__STLC_prod.subst (self__STLC_prod.tm_pi1 a) = 
self__STLC_prod.subst_handler.tm_pi1 a (self__STLC_prod.subst a) 
by { intros; eauto }.

Closing Fact subst_tm_pi2 : forall a, 
self__STLC_prod.subst (self__STLC_prod.tm_pi2 a) = 
self__STLC_prod.subst_handler.tm_pi2 a (self__STLC_prod.subst a) 
by { intros; eauto }.

Closing Fact subst_tm_prod :
  forall a b,
  self__STLC_prod.subst (self__STLC_prod.tm_prod a b) = 
  self__STLC_prod.subst_handler.tm_prod a (self__STLC_prod.subst a) b (self__STLC_prod.subst b) 
by { intros; eauto }. *)



(* Inherit Field context. *)

FInductive step : self__STLC_prod.tm -> self__STLC_prod.tm -> Prop :=
  | st_prod0 : forall a a' b,
    (step a a') -> (step (self__STLC_prod.tm_prod a b) (self__STLC_prod.tm_prod a' b)) 
  | st_prod1 : forall a b b',
    self__STLC_prod.value a ->
    (step b b') -> (step (self__STLC_prod.tm_prod a b) (self__STLC_prod.tm_prod a b')) 
  | st_pi10 : forall a a',
    step a a' ->
    (step (self__STLC_prod.tm_pi1 a) (self__STLC_prod.tm_pi1 a')) 
  | st_pi11 : forall a b,
    self__STLC_prod.value a ->
    self__STLC_prod.value b ->
    (step (self__STLC_prod.tm_pi1 (self__STLC_prod.tm_prod a b)) a) 
  | st_pi20 : forall a a',
    step a a' ->
    (step (self__STLC_prod.tm_pi2 a) (self__STLC_prod.tm_pi2 a')) 
  | st_pi21 : forall a b,
    self__STLC_prod.value a ->
    self__STLC_prod.value b ->
    (step (self__STLC_prod.tm_pi2 (self__STLC_prod.tm_prod a b)) b).




Closing Fact st_prod_inv:
    forall a b c,
    step (tm_prod a b) c -> 
      (exists a', step a a' /\ c = tm_prod a' b)
      \/ (exists b', value a /\ step b b' /\ c = tm_prod a b') by 
  {intros a b c h0;
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.
  
Closing Fact st_pi1_inv:
    forall a b,
    self__STLC_prod.step (tm_pi1 a) b -> 
      (exists a', step a a' /\ b = tm_pi1 a')
      \/ (exists x y, value x /\ value y /\ a = tm_prod x y /\ x = b)
by {intros a b h0; 
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.

  
Closing Fact st_pi2_inv:
    forall a b,
    step (tm_pi2 a) b -> 
      (exists a', step a a' /\ b = tm_pi2 a')
      \/ (exists x y, value x /\ value y /\ a = tm_prod x y /\ y = b)
by {intros a b h0; 
    inversion h0; subst; eauto;
    try (left; repeat eexists; repeat split; eauto; fail);
    try (right; repeat eexists; repeat split; eauto; fail); auto}.


(* Inherit Field irreducible. *)


FInductive has_type : self__STLC_prod.context -> self__STLC_prod.tm -> self__STLC_prod.ty -> Prop :=
  | ht_pi1 : forall G t A B,
      has_type G t (self__STLC_prod.ty_prod A B) ->
      has_type G (self__STLC_prod.tm_pi1 t) A
  | ht_pi2 : forall G t A B,
      has_type G t (self__STLC_prod.ty_prod A B) ->
      has_type G (self__STLC_prod.tm_pi2 t) B
  | ht_prod : forall G a b A B,
      has_type G a A ->
      has_type G b B ->
      has_type G (self__STLC_prod.tm_prod a b) (self__STLC_prod.ty_prod A B).

(* Inherit Field value_arrow_type_unit. *)

(* Canonical form *)
Closing Fact value_prod_type_inv:
  forall t A B,
  value t ->
  has_type empty t (ty_prod A B) ->
  exists a b, t = tm_prod a b /\ value a /\ value b /\ has_type empty a A /\ has_type empty b B
by { intros t A B h0 h1; inversion h1; subst; eauto;
     inversion h0; subst; eauto; repeat eexists; repeat split; eauto }.

FInduction progress. 
FProof. 
+ intros G t A B h0 h1 h2; cbn in *; eauto; subst; eauto. 
  destruct (h1 eq_refl); right;
  [forwards*: self__STLC_prod.value_prod_type_inv; 
    destruct_ALL;
    subst; 
    eauto
    |  destruct_ALL
  ]; eauto using self__STLC_prod.st_pi10, self__STLC_prod.st_pi11.
+  intros G t A B h0 h1 h2;intros; cbn in *; subst;eauto. 
destruct (h1 eq_refl); right;
[forwards*: self__STLC_prod.value_prod_type_inv; 
  destruct_ALL;
  subst; 
  eauto
  |  destruct_ALL
]; eauto using self__STLC_prod.st_pi20, self__STLC_prod.st_pi21.

+  intros G a b A B h0 h1 h2 h3 _h4; cbn in *; subst; eauto.
destruct (h1 eq_refl); 
destruct (h3 eq_refl);
  eauto using self__STLC_prod.vprod;
destruct_ALL; 
try (right; repeat eexists; eauto using self__STLC_prod.st_prod0, self__STLC_prod.st_prod1 ; fail).

Qed. FEnd progress.


FInduction subst_lemma.
StartFProofAll. repeat split; 
(repeat intro; intros); cbn in *; eauto; subst; eauto; frec_eval self__STLC_prod.subst;
eauto using self__STLC_prod.ht_pi1, self__STLC_prod.ht_pi2, self__STLC_prod.ht_prod.
Qed. FEnd subst_lemma.

FInductive fv : ident -> self__STLC_prod.tm -> Prop :=
| fv_prod0 : forall x a b,
    fv x a -> fv x (self__STLC_prod.tm_prod a b)
| fv_prod1 : forall x a b,
    fv x b -> fv x (self__STLC_prod.tm_prod a b)
| fv_pi1 : forall x a,
    fv x a -> fv x (self__STLC_prod.tm_pi1 a)
| fv_pi2 : forall x a,
    fv x a -> fv x (self__STLC_prod.tm_pi2 a).


Closing Fact fv_inv_tm_prod:
forall x a b,
fv x (tm_prod a b) ->
fv x a \/ fv x b
by {intros x a b h; inversion h; subst; eauto}.

Closing Fact fv_inv_tm_pi1:
forall x a,
fv x (tm_pi1 a) ->
fv x a
by {intros x a h; inversion h; subst; eauto}.


Closing Fact fv_inv_tm_pi2:
forall x a,
fv x (tm_pi2 a) ->
fv x a
by {intros x a h; inversion h; subst; eauto}.



(* Inherit Field fv_inv_tm_abs. *)

FInduction free_var_in_ctx.
StartFProofAll. repeat split; (repeat intro;intros); cbn in *; eauto; subst; eauto. 
+ forwards* : self__STLC_prod.fv_inv_tm_pi1; destruct_ALL; eauto.
+ forwards* : self__STLC_prod.fv_inv_tm_pi2; destruct_ALL; eauto.
+ forwards* : self__STLC_prod.fv_inv_tm_prod; destruct_ALL; eauto.
Qed. FEnd free_var_in_ctx.


FInduction free_var_matters.
StartFProofAll. repeat split;
(repeat intro;intros); cbn in *; eauto; subst; 
eauto using self__STLC_prod.ht_pi1, self__STLC_prod.fv_pi1, self__STLC_prod.ht_pi2, self__STLC_prod.fv_pi2.
(* Case tm_prod *) eapply self__STLC_prod.ht_prod; eauto using self__STLC_prod.fv_prod0, self__STLC_prod.fv_prod1.
Qed. FEnd free_var_matters.


(* Inherit Field weakening_lemma. *)

Closing Fact inject_tm_prod:
  forall a b c d,
  tm_prod a b = tm_prod c d ->
  a = c /\ b = d
by {intros a b c d h; inversion h; subst; eauto}.

FInduction preservation.
FProof.
+ intros G t A B H H0 H1 t' H2; intros; cbn in *; eauto; subst; eauto. 
forwards*: self__STLC_prod.st_pi1_inv; destruct_ALL; 
eauto using (H0 eq_refl),  self__STLC_prod.ht_pi1.
forwards*: (self__STLC_prod.vprod _ _ H1 H3) .
forwards*: (self__STLC_prod.value_prod_type_inv _ _ _ H4 H); destruct_ALL; eauto.
forwards*: self__STLC_prod.inject_tm_prod; destruct_ALL; subst; eauto.

+ intros G t A B H H0 H1 t' H2; intros; cbn in *; eauto; subst; eauto. 
forwards*: self__STLC_prod.st_pi2_inv; destruct_ALL; 
eauto using (H0 eq_refl),  self__STLC_prod.ht_pi2.
forwards*: (self__STLC_prod.vprod _ _ H1 H3) .
forwards*: (self__STLC_prod.value_prod_type_inv _ _ _ H4 H); destruct_ALL; eauto.
forwards*: self__STLC_prod.inject_tm_prod; destruct_ALL; subst; eauto.
+  intros G a b A B h0 h1 h2 h3 h4 t' h5; cbn in *; eauto; subst; eauto.
forwards*: self__STLC_prod.st_prod_inv; destruct_ALL; eauto.
forwards*: (h1 eq_refl); eauto using self__STLC_prod.ht_prod.
forwards*: (h3 eq_refl); eauto using self__STLC_prod.ht_prod.
Qed. FEnd preservation.

Time FEnd STLC_prod.
