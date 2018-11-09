Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import AdequacyLocal.
Require Import Csem AsmC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import Linking.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import AsmregsC.
Require Import MatchSimModSem.

Set Implicit Arguments.


Lemma match_program_refl
      F V
      `{Linker F} `{Linker V}
      (prog: AST.program F V)
  :
    match_program (fun _ => eq) eq prog prog
.
Proof.
  econs; eauto.
  destruct prog; ss.
  ginduction prog_defs; ii; ss.
  { econs; eauto. }
  destruct a; ss.
  econs; eauto.
  - econs; eauto. ss. destruct g; ss.
    + econs; eauto. eapply linkorder_refl.
    + econs; eauto. destruct v; ss.
  - rpapply IHprog_defs; eauto.
    apply Axioms.functional_extensionality. i.
    destruct x; ss.
    apply Axioms.functional_extensionality. i.
    destruct x; ss.
    apply prop_ext. split; ii.
    + inv H1. ss. clarify. inv H3; econs; ss; eauto; econs; ss; eauto.
      apply linkorder_refl.
    + inv H1. ss. clarify. inv H3; econs; ss; eauto; econs; ss; eauto.
      apply linkorder_refl.
Unshelve.
  all: ss.
Qed.

Local Existing Instance Val.mi_normal.
Local Opaque Z.mul Z.add Z.sub Z.div.

Parameter C_module: Csyntax.program -> Mod.t.

Lemma genv_eq
      F V
      (ge1 ge2: Genv.t F V)
      (PUB: ge1.(Genv.genv_public) = ge2.(Genv.genv_public))
      (NEXT: ge1.(Genv.genv_next) = ge2.(Genv.genv_next))
      (SYMB: ge1.(Genv.genv_symb) = ge2.(Genv.genv_symb))
      (DEFS: ge1.(Genv.genv_defs) = ge2.(Genv.genv_defs))
  :
    ge1 = ge2
.
Proof.
  destruct ge1, ge2; ss. clarify.
  f_equal.
  - apply proof_irr.
  - apply proof_irr.
  - apply proof_irr.
Qed.



(* Local Existing Instance SimMemId.SimMemId | 0. *)
(* Local Existing Instance SimMemId.SimSymbId | 0. *)
(* Local Existing Instance SoundTop.Top | 0. *)

Lemma asm_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  { i; ss. clarify. }
  intro GENV; des.
  inv SIMSKENVLINK.
 
  econs; ss; eauto.
  { eapply SoundTop.sound_state_local_preservation; eauto. }
  ii; ss.

  inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  fold fundef in *.
  split; ii; cycle 1.
  { (* init progress *) des. exists st_init_src. inv SAFESRC. econs; ss; eauto. }
  rename tgt into m0.
  rename st_init_tgt into st0.
  rename skenv_link_tgt into skenv_link.
  (* init bsim *)
  esplits; eauto.
  (* lxsim *)
  instantiate (1:= (SimMemId.mk m0 m0)). instantiate (1:= Ord.lift_idx unit_ord_wf tt).
  clear - GENV.
  generalize dependent st0.
  pcofix CIH. ii. pfold.
  destruct (classic ((modsem skenv_link asm).(ModSem.is_call) st0)).
  { (* call *)
    ss. rr in H. des.
    econs 3; eauto.
    { econs; eauto. }
    ii. des. clear_tac.
    exists args_src. exists (SimMemId.mk args_src.(Args.m) args_src.(Args.m)). ss.
    esplits; eauto.
    { econs; ss; eauto. }
    ii. ss. des.
    esplits; eauto.
    inv SIMRETV. ss. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. clarify.
  }
  destruct (classic ((modsem skenv_link asm).(ModSem.is_return) st0)).
  { (* final *)
    ss. rr in H0. des.
    dup H0. set (R:= retv). inv H0.
    econs 4; eauto.
    { instantiate (1:= SimMemId.mk m2 m2). ss. }
    { econs; eauto. }
    { ss. }
  }
  econs 1; eauto.
  ii; des. clear_tac.
  esplits; eauto.
  econs; eauto; cycle 1.
  { admit "ez - receptive". }
  ii. ss. inv STEPSRC.
  esplits; eauto. left. apply plus_one. econs; eauto.
  { admit "ez - determinate". }
  econs; eauto.
Unshelve.
  all: ss.
Qed.

Lemma asm_id_trial2
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  { i; ss. clarify. }
  intro GENV; des.
  inv SIMSKENVLINK.
 
  eapply match_states_sim with (index := unit)
                               (sound_state := SoundTop.sound_state)
                               (match_states := fun sm_arg idx st_src0 st_tgt0 sm =>
                                                  st_src0 = st_tgt0 /\ SimMem.wf sm)
                               (match_states_at := top4); ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eapply SoundTop.sound_state_local_preservation; eauto.
  - (* init bsim *)
    ii. des. exists st_init_tgt. inv SAFESRC. econs; ss; eauto.
    esplits; ss; eauto.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  - (* init progress *)
    ii. des.
    inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
    exists st_init_src. inv SAFESRC. econs; ss; eauto.
  - (* call wf *)
    ii; des; ss.
  - (* call fsim *)
    ii; des; ss.
    destruct sm0; ss. clarify.
    eexists _, (SimMemId.mk _ _); ss. esplits; eauto.
    econs; ss; eauto.
  - (* after fsim *)
    ii; des; ss.
    destruct sm_ret; ss. clarify. clear_tac.
    destruct retv_src, retv_tgt; ss. inv SIMRET. ss. clarify.
    esplits; eauto.
  - (* final fsim *)
    ii; des; ss. clarify.
    destruct retv_src; ss.
    exists (SimMemId.mk m m).
    esplits; ss; eauto.
  - (* step fsim *)
    ii; ss. des. clarify. clear_tac.
    esplits; eauto.
    { admit "ez - receptive". }
    ii; des. esplits; eauto. left. apply plus_one. econs; eauto.
    { admit "ez - determinate". }
Unshelve.
  all: ss.
Qed.

Lemma asm_ext_top
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Inductive sound_state (skenv: SkEnv.t) (su: Sound.t) (m_init: mem): AsmC.state -> Prop :=
| sound_state_intro
    init_rs rs0 m0
    (MLE: Unreach.mle su m_init m0)
    (RS: forall pr, UnreachC.val' su m0.(Mem.nextblock) (rs0#pr))
    (MEM: UnreachC.mem' su m0)
    (INIT: forall pr, UnreachC.val' su m0.(Mem.nextblock) (init_rs#pr))
    (WF: forall blk (PRIV: su.(UnreachC.unreach) blk) (PUB: Plt blk su.(Unreach.ge_nb)), False)
    (* (SKE: UnreachC.skenv su m0 skenv) *)
    (SKE: su.(Unreach.ge_nb) = skenv.(Genv.genv_next))
  :
    sound_state skenv su m_init (mkstate init_rs (State rs0 m0))
.

Lemma val_nextblock
      su0 blk0 blk1 v
      (SU: UnreachC.val' su0 blk0 v)
      (LE: Ple blk0 blk1)
  :
    <<SU: UnreachC.val' su0 blk1 v>>
.
Proof.
  ii. clarify. exploit SU; eauto. i; des. esplits; eauto. xomega.
Qed.

(* Inductive Mem_future (P: val -> Prop) (m0 m1: Mem.mem): Prop := *)
(* | Mem_future_alloc *)
(*     lo hi blk *)
(*     (ALLOC: m0.(Mem.alloc) lo hi = (m1, blk)) *)
(*   : *)
(*     Mem_future P m0 m1 *)
(* | Mem_future_store *)
(*     ( *)
(* . *)

Lemma to_mreg_preg_of
      pr mr
      (MR: Asm.to_mreg pr = Some mr)
  :
    <<PR: preg_of mr = pr>>
.
Proof. destruct mr, pr; ss; des_ifs. Qed.

Lemma asm_unreach_local_preservation
      asm skenv_link
  :
    <<PRSV: Preservation.local_preservation (modsem skenv_link asm) (sound_state skenv_link)>>
.
Proof.
  s.
  econs; ii; ss; eauto.
  - (* init *)
    inv INIT.
    r in SUARG. des.
    rename m into m2.
    assert(SURS: forall pr, UnreachC.val' su_init (Mem.nextblock m2) (rs pr)).
    {
      ii. unfold PregEq.t in *. spc PTRFREE.

      inv STORE.
      exploit Mem.alloc_result; eauto. i; clarify.
      exploit Mem.nextblock_alloc; eauto. intro SUCC.

      hexploit PTRFREE; eauto.
      { rewrite PTR. ss. }
      clear PTRFREE.
      i; des; clarify; cycle 1.
      { rewrite PTR in *. rewrite <- NB in *. erewrite Mem.nextblock_alloc; eauto.
        clear - VAL RSPC. rr in VAL. symmetry in RSPC. repeat spc VAL. des. split; ss. eauto with xomega.
      }
      { rewrite PTR in *. clarify.
        clear - MEM NB SUCC.
        inv MEM. unfold Mem.valid_block in *.
        split; ss.
        - ii. exploit BOUND; eauto. i. xomega.
        - rewrite <- NB. rewrite SUCC. xomega.
      }
      rewrite Forall_forall in *.
      (* TODO: pull out as a lemma *)
      assert(IN: In (rs pr) (Args.vs args)).
      { clear - ARG VALS0 MR.
        r in VALS0.
        generalize (loc_arguments_one (fn_sig fd)); intro ONES.
        abstr (loc_arguments (fn_sig fd)) locs. abstr (Args.vs args) vs.
        ginduction vs; ii; ss; inv VALS0; ss.
        rewrite in_app_iff in ARG.
        des; eauto.
        exploit ONES; eauto. i; des. destruct a1; ss. des; ss.
        inv H2. inv H1. left. f_equal. clear - MR. eapply to_mreg_preg_of; eauto.
      }
      Fail spc VALS. (* TODO: fix spc *)
      specialize (VALS _ IN). rewrite PTR in *.
      clear - VALS NB SUCC.
      exploit VALS; eauto. i; des. esplits; eauto.
      rewrite <- NB.
      rewrite SUCC.
      xomega.
    }
    econs; eauto; ss.
    + (* mle *)

      inv STORE.
      exploit Mem.alloc_result; eauto. i; clarify.
      exploit Mem.nextblock_alloc; eauto. intro SUCC.

      econs; eauto.
      * ii.
        eapply Mem.perm_alloc_4; eauto.
        eapply UNCH; eauto.
        { unfold Mem.valid_block in *. des_ifs. xomega. }
        { unfold Mem.valid_block in *. rewrite SUCC. xomega. }
      * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1.
        { eapply Mem.unchanged_on_implies; eauto.
          ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. }
        { eapply Mem.alloc_unchanged_on; eauto. }
      * eapply Mem_unchanged_on_trans_strong; eauto; cycle 1.
        { eapply Mem.unchanged_on_implies; eauto.
          ii. ss. des. des_ifs. unfold Mem.valid_block in *. xomega. }
        { eapply Mem.alloc_unchanged_on; eauto. }
    + (* mem *)

      inv STORE.
      exploit Mem.alloc_result; eauto. i; clarify.
      exploit Mem.nextblock_alloc; eauto. intro SUCC.

      inv MEM.
      econs; ss; eauto; cycle 1.
      { ii. exploit BOUND; eauto. i. unfold Mem.valid_block in *. rewrite <- NB. rewrite SUCC. xomega. }
      { rewrite <- NB. rewrite SUCC. xomega. }
      i.
      admit "this should hold".
    + (* ske *)
      inv SKENV. rewrite PUB in *. ss.
  - (* step *)
      admit "ez".
  - (* call *)
    inv AT. ss.
    exploit (Sound.greatest_ex su0 (Args.mk (Vptr blk0 Ptrofs.zero true) vs m1)); ss; eauto.
    { exists su0. esplits; eauto.
      { refl. }
      inv SUST. econs; ss; eauto.
      + ii. exploit (RS PC); eauto. i; des. clarify. esplits; eauto. admit "ez".
      + esplits; eauto.
        * rewrite Forall_forall. i.
          admit "extcall-arguments".
        * admit "this should hold".
    }
    esplits; eauto.
    + inv SUST.
      etrans; eauto.
      exploit RS; eauto. intro SU; des.
      eapply Unreach.free_mle; eauto.
    + admit "somehow... this should have been proven in somewhere else".
    + ii. inv AFTER. ss.
      destruct retv; ss. rename m into m2.
      econs; eauto.
      { inv SUST. etrans; eauto.
        admit "free-mle-unfree dual".
      }
      { admit "this should hold". }
      { inv SUST. admit "nontrivial... free-mle-unfree". }
      { inv SUST.
        ii. exploit INIT; eauto. i; des. esplits; eauto. admit "ez".
      }
      { inv SUST. ss. }
      { inv SUST. ss. }
  - (* return *)
    inv SUST. inv FINAL. ss. clarify.
    exists su0. esplits; eauto.
    { refl. }
    { econs; ss.
      - erewrite Mem.nextblock_free; eauto.
      - admit "this should hold".
    }
    etrans; eauto.
    eapply UnreachC.free_mle; eauto.
    exploit INIT; eauto. i; des. ss.
Unshelve.
  all: ss.
Qed.

Let asm_ext_unreach_lxsim: forall
    asm skenv_link
    m_src0 m_tgt0
    (GENV: Genv.match_genvs (match_globdef (fun _ : AST.program fundef unit => eq) eq asm)
                            (SkEnv.revive (SkEnv.project skenv_link (defs asm)) asm)
                            (SkEnv.revive (SkEnv.project skenv_link (defs asm)) asm))
    m_src1 m_tgt1
    st_init_src st_init_tgt
  ,
  <<LXSIM: lxsim (modsem skenv_link asm) (modsem skenv_link asm)
                 (fun st => exists su m_init, sound_state skenv_link su m_init st)
                 (SimMemExt.mk m_src0 m_tgt0) (lift_idx unit_ord_wf tt) st_init_src st_init_tgt
                 (SimMemExt.mk m_src1 m_tgt1)>>
.
Proof.
  i. revert_until m_tgt1.
  pcofix CIH. ii. pfold.
Abort.

Lemma asm_ext_unreach
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  assert(PROGSKEL: match_program (fun _ => eq) eq (Sk.of_program fn_sig asm) (Sk.of_program fn_sig asm)).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  assert(PROG: match_program (fun _ => eq) eq asm asm).
  { econs; eauto. ss. eapply match_program_refl; eauto. }
  esplits; eauto.
  econs; ss; eauto.
  ii. inv SSLE. clear_tac.


  eapply match_states_sim; ss.
  - (* WF *)
    eapply unit_ord_wf.
  - (* lprsv *)
    eapply asm_unreach_local_preservation; eauto.
  - (* init bsim *)
    admit "".
  - (* init progress *)
    admit "".
  - (* call bsim *)
    admit "".
  - 
  econs; ss; eauto.
  { eapply asm_unreach_local_preservation; eauto. }
  ii; ss.

  exploit (SimSymbId.sim_skenv_revive PROG); try apply SIMSKENV; eauto.
  { i; ss. clarify. }
  intro GENV; des.
  inv SIMSKENVLINK. inv SIMSKENV. ss.

  inv SIMARGS. destruct args_src, args_tgt; ss. clarify. destruct sm_arg; ss. clarify.
  rename fptr into fptr_src. rename fptr0 into fptr_tgt.
  rename vs into vs_src. rename vs0 into vs_tgt.
  fold fundef in *.
  inv FPTR; ss.
  split; ii; cycle 1.
  { (* tgt progress *)
    des. inv SAFESRC. esplits. econs; ss; eauto.
    - rp; eauto. symmetry. eapply Mem.mext_next; eauto.
    - admit "this should hold - store_arguments_progress".
  }
  (* bsim *)
  rename src into m_src0. rename tgt into m_tgt0.
  bar.
  inv INITTGT. rename m into m_tgt1.
  assert(exists m_src1, <<STORESRC: AsmC.store_arguments m_src0 rs vs_src (fn_sig fd) m_src1>>).
  { admit "this should hold - store_arguments_progress". }
  des.
  esplits; eauto.
  ss.
  instantiate (1:= (SimMemExt.mk m_src1 m_tgt1)). instantiate (1:= Ord.lift_idx unit_ord_wf tt).
  clear - GENV.
  rename _st_init_src into st_init_src. abstr {| init_rs := rs; st := State rs m_tgt1 |} st_init_tgt.
  generalize dependent st_init_src.
  generalize dependent st_init_tgt.
  pcofix CIH. ii. pfold.
  destruct (classic ((modsem skenv_link asm).(ModSem.is_call) st0)).
  { ss. rr in H. des.
    econs 3; eauto.
    { econs; eauto. }
    ii. des. clear_tac.
    exists args_src. exists (SimMemId.mk args_src.(Args.m) args_src.(Args.m)). ss.
    esplits; eauto.
    { econs; ss; eauto. }
    ii. ss. des.
    esplits; eauto.
    inv SIMRETV. ss. destruct retv_src, retv_tgt; ss. clarify. destruct sm_ret; ss. clarify.
  }
  destruct (classic ((modsem skenv_link asm).(ModSem.is_return) st0)).
  { ss. rr in H0. des.
    dup H0. set (R:= retv). inv H0.
    econs 4; eauto.
    { instantiate (1:= SimMemId.mk m2 m2). ss. }
    { econs; eauto. }
    { ss. }
  }
  econs 1; eauto.
  ii; des. clear_tac.
  esplits; eauto.
  econs; eauto; cycle 1.
  { admit "ez". }
  ii. ss. inv STEPSRC.
  esplits; eauto. left. apply plus_one. econs; eauto.
  { admit "ez". }
  econs; eauto.
Unshelve.
  all: ss.
Qed.
Qed.

Lemma asm_inj_id
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma asm_inj_drop
      (asm: Asm.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = asm.(AsmC.module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = asm.(AsmC.module)>>)
.
Proof.
  admit "this should hold".
Qed.






Lemma ccc_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_ext_top
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_ext_unreach
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemExt.SimMemExt SimMemExt.SimSymbExtends UnreachC.Unreach mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_inj_id
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimMemInjC.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.

Lemma ccc_inj_drop
      (ccc: Csyntax.program)
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemInjC.SimMemInj SimSymbDrop.SimSymbDrop SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(C_module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(C_module)>>)
.
Proof.
  admit "this should hold".
Qed.



Lemma lift
      `{SM: SimMem.class} `{@SimSymb.class SM} `{Sound.class}
      X (to_mod: X -> Mod.t)
      (MOD: forall x, exists mp,
            ModPair.sim mp /\ mp.(ModPair.src) = x.(to_mod) /\ mp.(ModPair.tgt) = x.(to_mod))
  :
    <<PROG: forall xs, exists pp,
        ProgPair.sim pp /\ ProgPair.src pp = map to_mod xs /\ ProgPair.tgt pp = map to_mod xs
                                                                                    >>
.
Proof.
  ii.
  induction xs; ii; ss.
  { esplits; eauto. }
  des.
  specialize (MOD a). des.
  exists (mp :: pp). esplits; ss; eauto with congruence.
Qed.

