Require Import Events.
Require Import Values.
Require Import AST.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import LinkingC.
Require Import SimSymb.
Require Import MapsC.


Set Implicit Arguments.

Require Import SimSymb.
Require Import SimMem.
Require Import SimMemInj.
Require Import ModSem.



Section MEMINJ.
  
Context `{CTX: Val.meminj_ctx}.

(* Definition t': Type := ident -> bool. *)
Definition t': Type := ident -> Prop.

Inductive sim_sk (ss: t') (sk_src sk_tgt: Sk.t): Prop :=
| sim_sk_intro
    (KEPT: forall
        id
        (KEPT: ~ ss id)
      ,
       sk_tgt.(prog_defmap) ! id = sk_src.(prog_defmap) ! id)
    (DROP: forall
        id
        (DROP: ss id)
      ,
        sk_tgt.(prog_defmap) ! id = None)
    (* (SIMSK: forall *)
    (*     id *)
    (*   , *)
    (*    sk_tgt.(prog_defmap) ! id = if ss id then None else sk_src.(prog_defmap) ! id) *)
    (CLOSED: ss <1= sk_src.(privs))
    (PUB: sk_src.(prog_public) = sk_tgt.(prog_public))
    (MAIN: sk_src.(prog_main) = sk_tgt.(prog_main))
.

Inductive sim_skenv (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
| sim_skenv_intro
    (SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          /\ <<KEPT: ~ ss id>>
    )
    (SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\
           <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>)
    (SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>
           /\ <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>
             (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    )
    (SIMDEF: forall
        blk_src blk_tgt delta def_src isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, <<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: def_src = def_tgt>>)
    (SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, <<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: def_src = def_tgt>>)
    (PUBS: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss)
.

Definition sim_skenv_splittable (sm0: SimMem.t) (ss: t') (skenv_src skenv_tgt: SkEnv.t): Prop :=
    (<<SIMSYMB1: forall
        id blk_src blk_tgt delta
        (SIMVAL: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta true))
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        <<DELTA: delta = Ptrofs.zero>> /\ <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>>
                                          /\ <<KEPT: ~ ss id>>
    >>)
    /\
    (<<SIMSYMB2: forall
        id
        (KEPT: ~ ss id)
        blk_src
        (BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src)
      ,
        exists blk_tgt,
          <<BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt>> /\
           <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>>>)
    /\
    (<<SIMSYMB3: forall
        id blk_tgt
        (BLKTGT: skenv_tgt.(Genv.find_symbol) id = Some blk_tgt)
      ,
        exists blk_src,
          <<BLKSRC: skenv_src.(Genv.find_symbol) id = Some blk_src>>
           /\ <<SIM: SimMem.sim_val sm0 (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt Ptrofs.zero true)>>
             (* /\ <<KEPT: ss.(kept) id>> <---------- This can be obtained via SIMSYMB1. *)
    >>)
    /\
    (<<SIMDEF: forall
        blk_src blk_tgt delta def_src isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src)
      ,
        exists def_tgt, <<DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   (<<SIM: def_src = def_tgt>>)>>)
    /\
    (<<SIMDEFINV: forall
        blk_src blk_tgt delta def_tgt isreal
        (SIMFPTR: sm0.(SimMem.sim_val) (Vptr blk_src Ptrofs.zero true) (Vptr blk_tgt delta isreal))
        (DEFTGT: skenv_tgt.(Genv.find_def) blk_tgt = Some def_tgt)
      ,
        exists def_src, <<DEFSRC: skenv_src.(Genv.find_def) blk_src = Some def_src>> /\
                                  <<DELTA: delta = Ptrofs.zero>> /\
                                           <<REAL: isreal = true>> /\
                                                   <<SIM: def_src = def_tgt>>>>)
    /\
    (<<PUBS: (fun id => In id skenv_src.(Genv.genv_public)) <1= ~1 ss>>)
.

Theorem sim_skenv_splittable_spec
  :
    (sim_skenv_splittable <4= sim_skenv) /\ (sim_skenv <4= sim_skenv_splittable)
.
Proof.
  split; ii; inv PR; ss; des; econs; eauto.
Qed.

Inductive le (ss0: t') (sk_src sk_tgt: Sk.t) (ss1: t'): Prop :=
| le_intro
    (LE: ss0 <1= ss1)
    (OUTSIDE: forall
        id
        (IN: (ss1 -1 ss0) id)
      ,
        <<OUTSIDESRC: ~ sk_src.(defs) id>> /\ <<OUTSIDETGT: ~ sk_tgt.(defs) id>>)
.

Global Program Definition link_ss (ss0 ss1: t'): option t' :=
  (* Some (fun id => orb (ss0 id) (ss1 id)) *)
  Some (ss0 \1/ ss1)
.

Global Program Instance Linker_t: Linker t' := {|
  link := link_ss;
  linkorder (ss0 ss1: t') := ss0 <1= ss1;
|}.


Lemma linkorder_defs
      F V
      `{Linker F} `{Linker V}
      (p0 p1: AST.program F V)
      (LINKORD: linkorder p0 p1)
  :
    <<DEFS: p0.(defs) <1= p1.(defs)>>
.
Proof.
  inv LINKORD.
  ii. u in *. des.
  simpl_bool. des_sumbool. apply prog_defmap_spec in PR. des.
  exploit H3; try eassumption. i; des.
  apply prog_defmap_spec. esplits; eauto.
Qed.

Lemma Genv_invert_symbol_none_spec
      F V
      (ge: Genv.t F V)
      b
  :
    <<INV: Genv.invert_symbol ge b = None>> <-> <<FIND: forall id, Genv.find_symbol ge id <> Some b>>
.
Proof.
  unfold Genv.find_symbol, Genv.invert_symbol in *.
  abstr (Genv.genv_symb ge) tree.
  split; i; des; red.
  - generalize dependent H.
    eapply PTree_Properties.fold_rec; ii; ss; clarify.
    + eapply H0; eauto. erewrite H; eauto.
    + erewrite PTree.gempty in H0. ss.
    + des_ifs.
      rewrite PTree.gsspec in *. des_ifs.
      eapply H1; eauto.
  -
    eapply PTree_Properties.fold_rec; ii; ss; clarify.
    des_ifs.
    contradict H. ii. eapply H; eauto.
Qed.


Global Program Instance SimSymbDrop: SimSymb.class SimMemInj := {
  t := t';
  le := le;
  sim_sk := sim_sk;
  sim_skenv := sim_skenv;
}
.
(* Next Obligation. *)
(*   inv SIMSK. *)
(*   econs; eauto. *)
(*   ii. *)
(*   destruct (classic (ss id)). *)
(*   - erewrite DROP in *; eauto. ss. *)
(*   - erewrite <- KEPT; ss. *)
(*     esplits; eauto. *)
(*     reflexivity. *)
(* Qed. *)
Next Obligation.
  econs; eauto. ii. des; ss.
Qed.
Next Obligation.
  inv LE0. inv LE1.
  econs; eauto.
  ii; des.
  specialize (OUTSIDE id).
  specialize (OUTSIDE0 id).
  destruct (classic (ss1 id)).
  - exploit OUTSIDE; eauto.
  - exploit OUTSIDE0; eauto. i; des.
    hexploit (linkorder_defs LINKORD0); eauto. i; des.
    hexploit (linkorder_defs LINKORD1); eauto. i; des.
    esplits; eauto.
Qed.
Next Obligation.
  admit "See 'link_match_program' in Unusedglobproof.v.
Note that we have one more goal (exists ss) but it is OK, as the 'link_match_program' proof already proves it.".
Qed.
Next Obligation.
  admit "See 'init_meminj_preserves_globals' in Unusedglobproof.v".
Qed.
Next Obligation.
  admit "The proof must exist in Unusedglobproof.v. See match_stacks_preserves_globals, match_stacks_incr".
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto.
Qed.
Next Obligation.
  exploit SkEnv.project_spec_preserves_wf; try apply LESRC; eauto. intro WFSMALLSRC.
  exploit SkEnv.project_spec_preserves_wf; try apply LETGT; eauto. intro WFSMALLTGT.
(* THIS IS TOP *)
  inv SIMSKENV. ss.
  apply sim_skenv_splittable_spec.
  dsplits; eauto; ii; ss.
  - (* SIMSYMB1 *)
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    exploit SIMSYMB1; eauto. { rewrite <- KEEP. ss. } i; des.

    inv LETGT.
    destruct (classic (defs sk_tgt id)); cycle 1.
    { erewrite SYMBDROP0; ss.
      exfalso.
      clear - LE KEPT H H0 SIMSK.
      apply H0. clear H0.
      inv SIMSK.
      u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss. esplits; eauto.
      - exfalso. apply KEPT. inv LE. eauto.
    }
    erewrite SYMBKEEP0; ss.
    esplits; eauto.
    {
      clear - LE H0 KEPT.
      inv LE.
      ii. apply KEPT.
      apply NNPP. ii.
      exploit OUTSIDE; eauto. { split; eauto. }
    }


  - (* SIMSYMB2 *)
    inv LESRC.
    destruct (classic (defs sk_src id)); cycle 1.
    { exfalso. exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro KEEP; des.

    rewrite KEEP in *.
    exploit (SIMSYMB2 id); eauto.
    { inv LE. ii. eapply KEPT. specialize (OUTSIDE id).
      exploit OUTSIDE; eauto. i; des. ss.
    }
    i; des.
    esplits; eauto.

    inv LETGT.
    erewrite SYMBKEEP0; ss.
    destruct (classic (defs sk_tgt id)); ss.
    { exfalso.
      clear - LE KEPT H H0 SIMSK.
      apply H0. clear H0.
      inv SIMSK.
      u in *.
      simpl_bool. des_sumbool. rewrite prog_defmap_spec in *.
      destruct (classic (ss id)); cycle 1.
      - erewrite KEPT0; ss.
      - exfalso. apply KEPT. ss.
    }

  - (* SIMSYMB3 *)
    inv LETGT.
    destruct (classic (defs sk_tgt id)); cycle 1. 
    { exploit SYMBDROP; eauto. i; des. clarify. }

    erewrite SYMBKEEP in *; ss.
    exploit SIMSYMB3; eauto. i; des.
    esplits; eauto.

    inv LESRC.
    erewrite SYMBKEEP0; ss.

    { clear - H SIMSK.
      inv SIMSK.
      u in *. simpl_bool. des_sumbool. rewrite prog_defmap_spec in *. des.
      destruct (classic (ss id)); ss.
      { erewrite DROP in *; ss. }
      exploit KEPT; eauto. i; des. rewrite <- H1. esplits; eauto.
    }

  - (* SIMDEF *)

    inv LESRC.
    inv WFSMALLSRC. exploit DEFSYMB; eauto. intro SYMBSMALL; des. rename SYMB into SYMBSMALL.
    destruct (classic (defs sk_src id)); cycle 1.
    { exploit SYMBDROP; eauto. i; des. clarify. }
    exploit SYMBKEEP; eauto. intro SYMBBIG; des. rewrite SYMBSMALL in *. symmetry in SYMBBIG.
    inv WFSRC.
    exploit SYMBDEF; eauto. i; des.
    exploit SIMDEF; eauto. i; des. clarify.

    exploit SPLITHINT; eauto. i; des.
    move DEFSRC at bottom. move H0 at bottom.

    exploit DEFKEPT; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    i; des.
    clarify.

    (* assert(def_src = def_tgt). *)
    (* { exploit DEFKEEP; eauto. eapply Genv.find_invert_symbol; eauto. i. *)
    (*   rewrite DEFSRC in *. rewrite H0 in *. des. clarify. } clarify. *)
    esplits; eauto.

    inv LETGT.
    exploit SIMSYMB1; eauto. i; des.

    destruct (Genv.find_def skenv_tgt blk_tgt) eqn:T.
    { exploit DEFKEPT0; eauto.
      { eapply Genv.find_invert_symbol; eauto. }
      i; des.
      clarify.
    }
    exploit DEFKEEP0; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    { inv SIMSK. exploit KEPT1; eauto. i.
      Lemma defs_prog_defmap
            F V (prog: AST.program F V)
            (NORP: list_norepet (prog_defs_names prog))
        :
          forall id, (exists gd, (prog_defmap prog) ! id = Some gd) <-> defs prog id
      .
      Proof.
        ii. unfold defs, prog_defs_names. split; i; des; des_sumbool.
        - exploit in_prog_defmap; eauto. i; des. rewrite in_map_iff. esplits; eauto; ss.
        - rewrite in_map_iff in *. des. destruct x; ss. clarify.
          exploit prog_defmap_norepet; eauto.
      Qed.
      ttttttttttttttttttttt
    }
    inv WFSMALLTGT.
    exploit SYMBDEF1; eauto. i; des. clarify.

    erewrite DEFKEEP0; eauto.
    { eapply Genv.find_invert_symbol; eauto. }
    { apply NNPP. ii.
      exploit DEFDROP0; eauto.
      { eapply Genv.find_invert_symbol; eauto. }
      i; des. clarify.
      inv WFSMALLTGT.
      exploit SYMBDEF1; eauto. i; des. clarify.
    }

  - (* SIMDEFINV *)
    inv LETGT.

    assert(Genv.find_def skenv_link_tgt blk_tgt = Some def_tgt).
    {
      destruct (Genv.invert_symbol skenv_link_tgt blk_tgt) eqn:T.
      - erewrite <- DEFKEEP; eauto.
        apply Genv.invert_find_symbol in T.
        apply NNPP; ii. exploit SYMBDROP; eauto. i; des.
        exploit DEFDROP; eauto.
        { apply Genv.find_invert_symbol. eauto. } i; des. clarify.
      - exploit DEFORPHAN; eauto. i; des. clarify.
    }
    exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto.

    inv WFSMALLTGT. exploit DEFSYMB; eauto. intro SYMBSMALLTGT; des.
    exploit SPLITHINT1; eauto. i; des.
    Fail clears blk_src.
    assert(blk_src = blk_src0).
    (* { *)
    (*   assert(KEPT: ~ ss id). *)
    (*   { exploit SPLITHINT; eauto. i; des. ss. } *)
    (*   exploit SPLITHINT0; try apply BLKSRC; eauto. i; des. clarify. clear_tac. *)
    (*   exploit SPLITHINT0; eauto. i; des. clarify. clear_tac. *)
    (* } *)
    { assert(MEMWF: SimMem.wf sm).
      { admit "". }
      inv MEMWF. inv PUBLIC0.
      apply NNPP. ii.
      move SIMFPTR at bottom. move SIM at bottom.
      inv SIMFPTR. inv SIM. rewrite Ptrofs.add_zero_l in *.
      About mi_no_overlap.
      assert(delta = 0).
      { admit "This is not true! [ADMIT UID: c82ce12b5f6f1e33e194129e030a5e93ad8767227d8b854207cf0797c994d484]".
        (* clear - H6. *)
        (* unfold Ptrofs.zero in *. *)
        (* hexploit (Ptrofs.intrange (Ptrofs.repr delta)); eauto. i. *)
        (* Local Transparent Ptrofs.repr. ss. Local Opaque Ptrofs.repr. *)
        (* Print Ptrofs.int. *)
        (* unfold Ptrofs.repr in *. ss. *)
        (* injection H6. ii. *)
        (* erewrite Ptrofs.Z_mod_modulus_eq in H0. *)
        (* rewrite Z.mod_small in *; ss. *)
        (* xomega. *)
        (* assert(Ptrofs.Z_mod_modulus_range' delta). *)
        (* dependent destruction H6. *)
        (* inv H6. clarify. *)
      }
      admit "Add disjointness in sim_skenv or relax meminj_no_overlap with Ptrofs.modulus or somehow...".
    }
    clarify.

    inv LESRC.
    inv WFSRC. exploit DEFSYMB; eauto. i; des.
    assert(id = id0). { eapply Genv.genv_vars_inj. apply SYMBSMALLTGT. eauto. } clarify.
    assert(defs sk_src id0).
    { apply NNPP. ii. erewrite SYMBDROP0 in *; eauto. ss. }
    exploit SYMBKEEP0; eauto. i; des. rewrite BLKSRC in *. symmetry in H2.
    erewrite DEFKEEP0; eauto.
    { apply Genv.find_invert_symbol; eauto. }
  - (* PUBS *)
    inv LESRC.
    rewrite PUBLIC in *.
    exploit PUBS; eauto.
    inv LE. eauto.
Qed.
Next Obligation.
  inv SIMSKENV.
  econs; eauto; ii; ss.
  - inv SIMFPTR; ss.
    des_ifs_safe; ss. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEF; eauto. i; des.
    inv SIM.
    rewrite DEFTGT.
    esplits; eauto.
    des_ifs.
  - inv SIMFPTR; ss; cycle 1.
    des_ifs_safe. unfold Genv.find_funct_ptr in *. des_ifs_safe.
    exploit SIMDEFINV; eauto. i; des.
    inv SIM.
    rewrite DEFSRC.
    esplits; eauto.
    des_ifs.
    exfalso.
    apply n.
    rewrite Ptrofs.add_zero_l in *. rewrite DELTA in *. rewrite Ptrofs.add_zero in *. clarify.
Qed.
Next Obligation.
  inv SIMSKENV.
  unfold System.skenv in *.
  esplits; eauto.
  econs; ii; ss; eauto; try rewrite Genv_map_defs_symb in *; apply_all_once Genv_map_defs_def; eauto.
  - des. exploit SIMDEF; eauto. i; des. clarify.
    esplits; eauto.
    eapply Genv_map_defs_def_inv in DEFTGT. rewrite DEFTGT. ss.
  - des. exploit SIMDEFINV; eauto. i; des. clarify.
    esplits; eauto.
    eapply Genv_map_defs_def_inv in DEFSRC. rewrite DEFSRC. ss.
  - eapply PUBS; eauto.
Qed.
Next Obligation.
  destruct sm0, args_src, args_tgt; ss. inv MWF; ss. inv ARGS; ss. clarify.
  inv SIMSKENV; ss.
  exploit external_call_mem_inject_gen; eauto.
  { instantiate (1:= skenv_sys_tgt).
    rr. esplits; ii; ss.
    - admit "We 'Unusedglob.v' don't remove unused ids from publics, 'good_prog' property will be broken.
As we don't want to change 'Unusedglob.v', we might remove the notion of 'good_prog'".
    - exploit SIMSYMB1; eauto. i; des. rewrite Ptrofs.add_zero_l in *.
      esplits; eauto.
      admit "Same as c82ce12b5f6f1e33e194129e030a5e93ad8767227d8b854207cf0797c994d484".
    - exploit SIMSYMB2; eauto.
      { ii. eapply PUBS; eauto. unfold Genv.public_symbol in H. des_ifs. des_sumbool. ss. }
      i; des.
      esplits; eauto.
      inv SIM; ss. rewrite Ptrofs.add_zero_l in *.
      admit "Same as c82ce12b5f6f1e33e194129e030a5e93ad8767227d8b854207cf0797c994d484".
    - unfold Genv.block_is_volatile, Genv.find_var_info.
      destruct (Genv.find_def skenv_sys_src b1) eqn:T0.
      { exploit SIMDEF; try eassumption.
        { econs; eauto. }
        i; des.
        des_ifs.
      }
      destruct (Genv.find_def skenv_sys_tgt b2) eqn:T1.
      { exploit SIMDEFINV; try eassumption.
        { econs; eauto. }
        i; des.
        des_ifs.
      }
      ss.
  }
  i; des.




  (* TODO: almost exactly copied from SimMemInj. we may remove duplicate code some way *)
  do 2 eexists.
  dsplits; eauto.
  - instantiate (1:= Retv.mk _ _); ss. eauto.
  - instantiate (1:= mk _ _ _ _ _ _ _). econs; ss; eauto.
  - econs; ss; eauto.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply Mem.unchanged_on_implies; eauto. u. i; des; ss.
    + eapply inject_separated_frozen; eauto.
    + ii. eapply external_call_max_perm; eauto.
  - apply inject_separated_frozen in H5.
    econs; ss.
    + eapply after_private_src; ss; eauto.
    + eapply after_private_tgt; ss; eauto.
    + inv H2. xomega.
    + inv H3. xomega.
Qed.

End MEMINJ.

