Require Import Relations.
Require Import Wellfounded.
Require Import CoqlibC.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import AxiomsC.
(** newly added **)
Require Export Smallstep.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Definition PStep (L: semantics) (P: L.(state) -> Prop) :=
  (fun s1 t s2 => step L (globalenv L) s1 t s2 /\ P s1)
.

Definition PStar (L: semantics) (P: L.(state) -> Prop) :=
  (star (fun (_: L.(genvtype)) => PStep L P)) L.(globalenv)
.

Definition PStarN (L: semantics) (P: L.(state) -> Prop) :=
  (starN (fun (_: L.(genvtype)) => PStep L P)) L.(globalenv)
.

Definition PPlus (L: semantics) (P: L.(state) -> Prop) :=
  (plus (fun (_: L.(genvtype)) => PStep L P)) L.(globalenv)
.

Lemma PStep_iff
      L P Q
      (IFF: all1 (P <1> Q))
  :
    PStep L P = PStep L Q
.
Proof.
  repeat (eapply functional_extensionality; i).
  eapply prop_ext.
  split; i.
  - inv H. econs; eauto. eapply IFF; eauto.
  - inv H. econs; eauto. eapply IFF; eauto.
Qed.

Lemma star_inv
      G ST
      (step: G -> ST -> trace -> ST -> Prop) (ge: G) st0 tr st1
      (STAR: star step ge st0 tr st1)
  :
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step ge st0 tr st1>>
.
Proof.
  inv STAR; eauto.
  right. econs; eauto.
Qed.

Lemma plus_or_star_inv
      G ST
      (step: G -> ST -> trace -> ST -> Prop) (ge: G) st0 tr st1
      (STAR: plus step ge st0 tr st1 \/ star step ge st0 tr st1)
  :
    <<EQ: st0 = st1 /\ tr = []>> \/ <<PLUS: plus step ge st0 tr st1>>
.
Proof.
  des; eauto. eapply star_inv; eauto.
Qed.
