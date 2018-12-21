Require Import FSets.
Require Import CoqlibC Errors Ordered Maps IntegersC Floats.
Require Import AST Linking.
Require Import ValuesC Memory GlobalenvsC Events Smallstep.
Require Import Ctypes CopC ClightC SimplLocals.
Require Import sflib.
Require SimMemInj.
(** newly added **)
Require Export SimplLocalsproof.
Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem AsmregsC MatchSimModSem.
Require SimMemInjC.
Require SoundTop.
Require Import CtypingC.
Require Import ModSemProps.

Set Implicit Arguments.
Local Existing Instance Val.mi_normal.



Lemma val_casted_list_spec
      vs tys
  :
    Forall2 val_casted vs (typelist_to_listtype tys) <-> val_casted_list vs tys
.
Proof.
  split; i.
  - ginduction vs; destruct tys; ii; ss; inv H; clarify; econs; eauto.
  - ginduction vs; destruct tys; ii; ss; inv H; clarify; econs; eauto.
Qed.

Lemma typecheck_inject
      j vs0 vs1 tys
      (TYS: typecheck vs0 tys)
      (INJ: Val.inject_list j vs0 vs1)
  :
    <<TYS: typecheck vs1 tys>>
.
Proof.
  inv TYS. econs; eauto.
  rewrite <- forall2_eq in *.
  eapply forall2_val_casted_inject; eauto.
Qed.

Lemma typify_inject
      v_src ty tv_src v_tgt j
      (TYP: typify_c v_src ty tv_src)
      (INJ: Val.inject j v_src v_tgt)
  :
    <<INJ: Val.inject j tv_src (typify v_tgt (typ_of_type ty))>>
.
Proof.
  inv TYP.
  - exploit wt_retval_has_type; eauto. i; des. unfold typify. des_ifs.
    inv INJ; ss.
  - ss.
Qed.

Lemma proj_sig_res_type
      targs0 tres0 cconv0
  :
    proj_sig_res (signature_of_type targs0 tres0 cconv0) = typ_of_type tres0
.
Proof.
  destruct tres0; ss.
Qed.

Lemma typecheck_typecheck
      vs fd
      (CTYS: typecheck vs (type_of_params (fn_params fd)))
  :
    <<TYS: ValuesC.typecheck vs (signature_of_function fd) vs>>
.
Proof.
  inv CTYS.
  econs; eauto.
  - exploit Forall2_length; eauto. i. ss. etrans; eauto. rewrite typelist_to_listtype_length; ss.
  - ss. eapply has_type_list_typify; eauto.
    rpapply val_casted_has_type_list; eauto.
    rewrite typlist_of_typelist_eq; ss.
  - unfold Conventions1.size_arguments. des_ifs. etrans; eauto.
    rewrite typlist_of_typelist_eq. unfold signature_of_function. ss. refl.
Qed.

Lemma transf_function_type
      f_src f_tgt
      (TRANSL: transf_function f_src = OK f_tgt)
  :
    (* <<TY: f_src.(type_of_function) = f_tgt.(type_of_function)>> *)
    (<<PRMS: (fn_params f_src) = (fn_params f_tgt)>>) /\
    (<<RET: (fn_return f_src) = (fn_return f_tgt)>>) /\
    (<<CCONV: (fn_callconv f_src) = (fn_callconv f_tgt)>>)
.
Proof.
  unfold transf_function, bind in *. des_ifs.
Qed.




Section SIMMODSEM.

Variable skenv_link_src skenv_link_tgt: SkEnv.t.
Variable sm_link: SimMem.t.
Variable prog: Clight.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge: Clight.genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link_src (defs prog)) prog)
                                  prog.(prog_comp_env).
Let tge: Clight.genv := Build_genv (SkEnv.revive (SkEnv.project skenv_link_tgt (defs tprog)) tprog)
                                   tprog.(prog_comp_env).
Definition msp: ModSemPair.t :=
  ModSemPair.mk (ClightC.modsem1 skenv_link_src prog) (ClightC.modsem2 skenv_link_tgt tprog) tt sm_link
.

Inductive match_states
          (sm_init: SimMem.t)
          (idx: nat) (st_src0: Clight.state) (st_tgt0: Clight.state) (sm0: SimMem.t): Prop :=
| match_states_intro
    (MATCHST: SimplLocalsproof.match_states ge st_src0 st_tgt0 sm0)
    (MCOMPATSRC: st_src0.(ClightC.get_mem) = sm0.(SimMem.src))
    (MCOMPATTGT: st_tgt0.(ClightC.get_mem) = sm0.(SimMem.tgt))
.

Theorem make_match_genvs :
  SimSymbId.sim_skenv (SkEnv.project skenv_link_src (defs prog)) (SkEnv.project skenv_link_tgt (defs tprog)) ->
  Genv.match_genvs (match_globdef (fun (ctx: AST.program fundef type) f tf => transf_fundef f = OK tf) eq prog) ge tge /\ prog_comp_env prog = prog_comp_env tprog.
Proof.
  subst_locals. ss.
  rr in TRANSL. destruct TRANSL. r in H.
  esplits.
  - eapply SimSymbId.sim_skenv_revive; eauto.
    { ii. u. unfold transf_fundef, bind in MATCH. des_ifs; ss; clarify. }
  - hexploit (prog_comp_env_eq prog); eauto. i.
    hexploit (prog_comp_env_eq tprog); eauto. i.
    ss. congruence.
Qed.

Theorem sim_modsem
  :
    ModSemPair.sim msp
.
Proof.
  (* rr in TRANSL. destruct TRANSL as [TRANSL0 TRANSL1]. *)
  eapply match_states_sim with (match_states := match_states)
                               (match_states_at := fun _ _ => eq)
                               (sound_state := SoundTop.sound_state);
    eauto; ii; ss.
  - instantiate (1:= Nat.lt). apply lt_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - (* init bsim *)
    (* destruct sm_arg; ss. clarify. *)
    destruct args_src, args_tgt; ss.
    inv SIMARGS; ss. clarify.
    inv INITTGT.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    eexists. exists sm_arg.
    esplits; eauto.
    { refl. }
    + econs; eauto; ss; cycle 1.
      { inv SAFESRC. ss. }
      * inv TYP.
        inv SAFESRC. folder. ss.
        exploit (Genv.find_funct_transf_partial_genv SIMGE); eauto. intro FINDFTGT; des. ss.
        assert(MGE: match_globalenvs ge (SimMemInj.inj sm_arg) (Genv.genv_next skenv_link_src)).
        {
          inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss. 
          econs; eauto.
          + ii. ss. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
          + ii. ss. uge. des_ifs. eapply Plt_Ple_trans.
            { genext. }
            ss. refl.
        }
        hexploit sim_external_inject_eq_fsim; try apply FINDF0; et. i; clarify.
        exploit typecheck_inject; eauto. intro TYPTGT0; des.
        exploit typecheck_typecheck; eauto. intro TYPTGT1; des.
        rpapply match_call_state; ss; eauto.
        { i. inv SIMSKENV. inv SIMSKE. ss. inv INJECT. ss. 
          econs; eauto.
          - etrans; try apply MWF. ss.
          - etrans; try apply MWF. ss.
        }
        { econs; et. }
        { apply MWF. }
        { inv TYP. eapply val_casted_list_spec; eauto. }
        f_equal.
        (* { unfold bind in *. des_ifs. exploit transf_function_type; eauto. i; des. *)
        (*   unfold type_of_function. f_equal; try congruence. } *)
        { unfold transf_function in *. unfold bind in *. des_ifs. }
        { inv TYPTGT1. rewrite <- TYP0 at 2. f_equal. ss.
          unfold transf_function in *. unfold bind in *. des_ifs.
        }
  - (* init progress *)
    des. inv SAFESRC.
    inv SIMARGS; ss.
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    exploit (Genv.find_funct_match_genv SIMGE); eauto. i; des. ss. clarify. folder.
    hexploit (@sim_external_inject_eq_fsim); try apply FINDF; eauto. clear FPTR. intro FPTR.
    (* unfold transf_function, bind in *. des_ifs. *)
    unfold bind in *. des_ifs.
    esplits; eauto. econs; eauto.
    + folder. ss. rewrite <- FPTR. eauto.
    + eapply typecheck_typecheck; et. exploit transf_function_type; eauto. i; des.
      eapply typecheck_inject; et. congruence.
  - (* call wf *)
    inv MATCH; ss. inv MATCHST; ss.
  - (* call fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv MATCH; ss. destruct sm0; ss. clarify.
    inv CALLSRC. inv MATCHST; ss.
    folder.
    inv MCOMPAT; ss. clear_tac.
    exploit (sim_external_funct_inject SIMGE); eauto. { ii; clarify; ss. des; ss. } intro EXTTGT.
    esplits; eauto.
    + econs; eauto.
      * des. clarify. esplits; eauto.
        (* exploit (sim_internal_funct_inject SIMGE); try apply SIG; et. *)

        (* Arguments sim_internal_funct_inject [_]. *)
        (* destruct SIMSKENVLINK. inv H.  rr in SIMSKENV1. clarify. *)
        (* exploit (sim_internal_funct_inject); try apply VAL; try apply SIG; et. *)
        (* { erewrite match_globdef_eq. eapply Global_match_genvs_refl. } *)
        (* { inv SIMSKENV. ss. } *)

        (***************** TODO: Add as a lemma in GlobalenvsC. *******************)
        inv SIMSKENV.
        assert(fptr_arg = tv).
        { eapply sim_external_inject_eq_fsim; try apply SIG; et. Undo 1.
          inv VAL; ss. des_ifs_safe. apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *.
          inv SIMSKE. ss. inv INJECT; ss.
          exploit (DOMAIN b1); eauto.
          { eapply Genv.genv_defs_range; et. }
          i; clarify.
        }
        clarify.
        eapply SimSymb.simskenv_func_fsim; eauto; ss.
        (* { destruct tv; ss. des_ifs. econs; eauto; cycle 1. *)
        (*   { psimpl. instantiate (1:= 0). ss. } *)
        (*   inv H. inv INJECT. eapply DOMAIN; eauto. *)
        (*   { apply Genv.find_funct_ptr_iff in SIG. unfold Genv.find_def in *. eapply Genv.genv_defs_range; et. } *)
        (* } *)
    + ss.
    + reflexivity.
  - (* after fsim *)
    hexploit (SimMemInjC.skenv_inject_revive prog); et. { apply SIMSKENV. } intro SIMSKENV0; des.
    exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.
    inv AFTERSRC.
    inv SIMRET. ss. exists (SimMemInj.unlift' sm_arg sm_ret). destruct sm_ret; ss. clarify.
    inv MATCH; ss. inv MATCHST; ss.
    inv HISTORY. ss. clear_tac.
    esplits; eauto.
    + econs; eauto.
    + econs; ss; eauto. destruct retv_src, retv_tgt; ss. clarify.
      inv MLE0; ss.
      inv MCOMPAT. clear_tac.
      rpapply match_return_state; ss; eauto; ss.
      (* { clear - MWF. inv MWF. ii. apply TGTEXT in H. rr in H. des. ss. } *)
      { ss. ii.
        eapply match_cont_incr_bounds; eauto; swap 2 4.
        { instantiate (1:= tge). ss. esplits; eauto. }
        { eauto with mem. }
        { eauto with mem. }
        eapply match_cont_extcall; eauto.
        { instantiate (1:= tge). ss. esplits; eauto. }
        { eapply Mem.unchanged_on_implies; try eassumption. ii. rr. esplits; eauto. }
        { eapply SimMemInj.inject_separated_frozen; et. }
        { refl. }
        { refl. }
      }
      { eapply MWFAFTR. }
      { eapply typify_inject; et. }
    + refl.
  - (* final fsim *)
    inv MATCH. inv FINALSRC; inv MATCHST; ss.
    inv MCONT_EXT. inv MCOMPAT; ss.
    eexists sm0. esplits; ss; eauto. refl.
  - exploit make_match_genvs; eauto. { apply SIMSKENV. } intro SIMGE. des.

    esplits; eauto.
    { apply modsem1_receptive. }
    inv MATCH.
    ii. hexploit (@step_simulation prog ge tge); eauto.
    i; des.
    esplits; eauto.
    + left. eapply spread_dplus; eauto. eapply modsem2_determinate; eauto.
    + econs; ss.
      * inv H0; ss; inv MCOMPAT; ss.
      * inv H0; ss; inv MCOMPAT; ss.
Unshelve.
  all: ss; try (by econs).
Qed.

End SIMMODSEM.


Section SIMMOD.

Variable prog: Clight.program.
Variable tprog: Clight.program.
Hypothesis TRANSL: match_prog prog tprog.

Definition mp: ModPair.t :=
  ModPair.mk (ClightC.module1 prog) (ClightC.module2 tprog) tt
.

Theorem sim_mod
  :
    ModPair.sim mp
.
Proof.
  econs; ss.
  - r. admit "easy - see DeadcodeproofC".
  - ii. eapply sim_modsem; eauto.
Unshelve.
  all: ss.
Qed.

End SIMMOD.
