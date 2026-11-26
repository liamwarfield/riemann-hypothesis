module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRowLiftFamilyOverColumnChoices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IntertwinersExistScalarUpdateInvariant
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

open GlobalTheory.Mem.R3.Res

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem baseWeight_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {F : Face D A} (h : R.BaseW F) (k l) :
    (R.upd6 k l).BaseW F :=
  ⟨h.lev, ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE, h.models.HW,
      h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX, h.models.νV,
      h.models.νW, h.models.BV, h.models.order⟩, RealDat.weak_chain_of_scalar_update h.chain k l, RealDat.weak_theta_props_of_scalar_update h.thP k l⟩


set_option maxHeartbeats 2000000 in
theorem intertwinersExist_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} (e : R.ExAt) (k l) : (R.upd6 k l).ExAt :=
  ⟨e.ItY, e.ItX, e.ioY, e.ioX, e.Th, e.ioP, e.thF, e.thG⟩


set_option maxHeartbeats 2000000 in
theorem nz_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (k l) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (∃ j, NzAt (R.updS k l) F F0 j w ∨ NzAt (R.updS k l) F F0 j (Formalism.DivisionValues.conjPl w)) ↔
      ∃ j, NzAt R F F0 j w ∨ NzAt R F F0 j (Formalism.DivisionValues.conjPl w) :=
  (complexSide_nonzeroIndexPlaces_iff_self (R.updS k l) F { R.num F 0 0 with F0 := F0 } w).symm.trans
    (complexSide_nonzeroIndexPlaces_iff R F k l R.err0 F.Dc F.Sp F.Zsc { R.num F 0 0 with F0 := F0 } w)


open Classical in
def kapOf (S : RealDat3 D A3 Ks) : ℝ :=
  if h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 then h.choose else S.kap

theorem kapOf_eq (S : RealDat3 D A3 Ks) (κ : ℝ)
    (hκ : Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ)
    (hn : ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0) : kapOf S = κ := by
  have h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 := ⟨κ, hκ, hn⟩
  obtain ⟨t, p, hp, hl⟩ := hn
  unfold kapOf
  rw [dite_eq_left h]
  exact Lift.IsKap.unique h.choose_spec.1 hκ t p hp hl


set_option maxHeartbeats 2000000 in
theorem isScal_kapOf (S : RealDat3 D A3 Ks) (F : Face3 D A3) (h0 : S.eigenvalue_at_base_of_scalar) (h1 : S.scal_off F) (h2 : S.zero_part_eigenvalue_convention F)
    (h3 : S.scal_abs F) (h4 : S.scal_tup) : (S.updS (kapOf S) S.lam3).IsScal F := by
  refine ⟨h0, fun κ h h' => kapOf_eq S κ h h', fun i p v l hv hp he => ?_, fun i t p hp => ?_, fun i p v hv hp => ?_, h4⟩
  · exact h1 i p v l hv ((RealDat3.partAt_updS _ _ _ _ _).1 hp) ((RealDat3.sim_updS _ _ _ _ _ _).1 he)
  · rw [RealDat3.zs_updS]
    exact h2 i t p hp
  · rw [RealDat3.zs_updS]
    exact h3 i p v hv fun hl => hp ((RealDat3.partAt_updS _ _ _ _ _).2 hl)

variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}


set_option maxHeartbeats 4000000 in
theorem pins_updS (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) (k l) (hs : ((dat3 f μ R mu tw).updS k l).IsScal (bare3 _ P0 ψ0 P1 ψ1)) :
    Pins ((dat3 f μ R mu tw).updS k l) (bare3 _ P0 ψ0 P1 ψ1) cG := by
  have i := isInert mu tw h.char.inert
  have u := isTup hf h.char.tup n
  have kv := keep mu tw h.keep
  exact ⟨⟨baseWeight_scalar_update_invariant (baseW (A := A3.A) mu tw hf h.char.base e) k _, ⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩,
      fun t => h.char.fullY (f t), fun t => h.char.fullX (f t), fun i t => h.char.fullP i (f t), hs,
      ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, h.char.phase, h.char.allPl⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩, h.phs, h.trSem⟩


set_option maxHeartbeats 4000000 in
theorem pins_kapOf (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) :
    Pins ((dat3 f μ R mu tw).updS (kapOf (dat3 f μ R mu tw)) (dat3 f μ R mu tw).lam3) (bare3 _ P0 ψ0 P1 ψ1) cG :=
  pins_updS hf h e n _ _ (isScal_kapOf _ _ (fun i t => h.char.scal.lam0 i (f t)) h.char.scal.off
    (fun i t => h.char.scal.abs0 i (f t)) h.char.scal.abs fun i t => h.char.scal.tup i (f t))

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl}



set_option maxHeartbeats 4000000 in
theorem exAt_res (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resR h).toRealDat.ExAt :=
  Res.exAt (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') e



set_option maxHeartbeats 4000000 in
theorem pins_resK (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) :
    Pins ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact pins_kapOf (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc)


variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')





end Record

end GlobalTheory.Mem.R3.ResEx

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' Wt'' : Set X.B.places.Pl} (z : Dat X I hX T Wt)





end GlobalTheory.Mem.R3.ResTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt : Set X.B.places.Pl}


set_option maxHeartbeats 4000000 in
def geoR (z : Dat X I hX T Wt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) :
    GlobalTheory.RealGeo.GeoHalf z.core ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3).toRealDat fun _ => 1 :=
  ⟨(z.resGeo h).κ, (z.resGeo h).v₀,
    GlobalTheory.RealGeo.Upd.updFWT z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).fw,
    (z.resGeo h).bar,
    fun i => GlobalTheory.RealGeo.Upd.updO z.core (z.resR h).toRealDat (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 ((z.resGeo h).O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE (kapOf (z.resR h)) (z.resR h).lam (z.resR h).err0 (z.resGeo h).O i ((z.resGeo h).pins i),
    (z.resGeo h).rhoGeo, (z.resGeo h).equivAll, (z.resGeo h).cTie, (z.resGeo h).phase⟩


set_option maxHeartbeats 4000000 in
def res (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := (z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3
  cG := z.cG
  geo := geoR z Wt' h
  pins := pins_resK z h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set X.B.places.Pl} (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')


set_option maxHeartbeats 4000000 in
theorem res_exAt : (res z e Wt' h hc).R.toRealDat.ExAt := intertwinersExist_scalar_update_invariant (exAt_res z h e) _ _


set_option maxHeartbeats 4000000 in
theorem res_inGeo (hi : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (res z e Wt' h hc).geo := by
  have h' := (z.inGeo_resGeo_iff h).2 hi
  exact ⟨h'.jEvExists, h'.jEvBar, h'.evInj, h'.jUnif, h'.geoAct, h'.latFull, h'.dimMatch⟩


set_option maxHeartbeats 4000000 in
theorem restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces (F0) : (res z e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  exact (nz_updS (z.resR h) _ _ _ F0 _).trans (exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _))


set_option maxHeartbeats 4000000 in
theorem res_std (hs : z.Std) : (res z e Wt' h hc).Std := by
  obtain ⟨⟨c, h1, h2, h5⟩, hV⟩ := hs
  refine ⟨⟨c, h1, fun hc' t φ g x hm => h2 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h5⟩, fun i => ?_⟩
  obtain ⟨cv, h3, h4, h6⟩ := hV i
  exact ⟨cv, h3, fun hc' t φ g x hm => h4 hc' (inclU I (usedOf_mono I T h) t) φ g x hm, h6⟩

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.ResStd

open GlobalTheory.Mem.R3.ResEx

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

theorem of_diag {n : ℕ} {P : Fin n → Fin n → Prop} (H : ∀ i, P i i) (i i' : Fin n) (h : (i : ℕ) = i') : P i i' :=
  (Fin.ext h : i = i') ▸ H i


set_option maxHeartbeats 4000000 in
theorem res_ext (z : Dat (w.st Z) w.I hX T Wt) (e : z.R.toRealDat.ExAt) {Wt' : Set B.places.Pl} (h : Wt' ⊆ Wt)
    (hc : ConjStable (w.st Z) Wt') : Ext z (res z e Wt' h hc) := by
  exact {
    H := HEq.rfl
    l := HEq.rfl
    c := HEq.rfl
    Dw := HEq.rfl
    Xo := HEq.rfl
    U := HEq.rfl
    V := HEq.rfl
    dict := HEq.rfl
    mu := HEq.rfl
    Kf := HEq.rfl
    cE := HEq.rfl
    chiW := HEq.rfl
    x₀ := HEq.rfl
    iota := HEq.rfl
    ψ := HEq.rfl
    θ := HEq.rfl
    βW := HEq.rfl
    βY := HEq.rfl
    nW := HEq.rfl
    βV := HEq.rfl
    ΛV := HEq.rfl
    ΛW := HEq.rfl
    Pg := HEq.rfl
    eG := HEq.rfl
    Sb := HEq.rfl
    BV i i' hi := by
      obtain rfl : i = i' := Fin.ext hi
      exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    MW i i' hi := by
      obtain rfl : i = i' := Fin.ext hi
      refine ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun φ φ' hφ => ?_⟩
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
      subst h2
      exact HEq.rfl
    forms i i' hi φ φ' hφ k k' hk := by
      obtain rfl : i = i' := Fin.ext hi
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := (cast_eq_iff_heq).2 hφ
      subst h2
      have hN : (type_of% k') = (type_of% k) := rfl
      have hnn : (res z e Wt' h hc).R.nW i = z.R.nW i := rfl
      have h3 : cast hN k' = k := (cast_eq_iff_heq).2 ((Fin.heq_ext_iff hnn).2 hk.symm)
      subst h3
      rfl
    W1 v v' hv := by
      have e' : v = v' := (w.D Z).plEq.injective (HeightOneSpectrum.ext (Ideal.ext fun x => hv x x rfl))
      subst e'
      rw [restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces]
    cV i i' hi := by
      obtain rfl : i = i' := Fin.ext hi
      exact ⟨HEq.rfl, HEq.rfl⟩
    pb := HEq.rfl
    ΛY := (HEq.refl z.R.ΛY)
    κ := by
      refine of_diag fun i => ⟨?_, ?_, ?_⟩
      · exact (HEq.refl (z.geo.κ i).aP)
      · exact (HEq.refl (z.geo.κ i).aM)
      · exact (Eq.refl (z.geo.κ i).n)
    ref := by
      refine of_diag fun i => ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (HEq.refl (z.R.vP i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.HV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.thF i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.thG i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.νV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.fdV i (mu0F (tuOf w.I (usedOf w.I T Wt)))))
      · exact (HEq.refl (z.R.νW i))
      · exact (HEq.refl (z.R.fdW i))
    jL := by
      refine of_diag fun i => ?_
      intro ok ok' φ φ' hφ
      have hT : (type_of% φ') = (type_of% φ) := rfl
      have h2 : cast hT φ' = φ := Subtype.ext (funext fun d => Subtype.ext
        (MvPolynomial.map_injective _ (RingHom.injective _) (eq_of_heq (hφ d d HEq.rfl))))
      subst h2
      exact (by with_unfolding_all exact (HEq.refl (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok (cast hT φ') :)))) :))
  }

end GlobalTheory.Mem.R3.ResStd

namespace GlobalTheory.Mem.R3.Rw

theorem stepW_keep_of_ev {Q : Ctx → Prop} (h : Ev Q) (p : WP) : StepW p fun K _ _ _ _ => Q K :=
  Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)


set_option maxHeartbeats 4000000 in
theorem exists_pre2_of_fine_of_resChar_mem : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite →
    GlobalTheory.Published.CuspRapidDecay → WeightCaseCondition → StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok)
      (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G → GrpTrue Z.N f → GrpAt (w.st Z) w.I →
      DV.KapDef (w.D Z) → Fine z → (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) →
      (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) →
      ∃ P : Pre2 K w, P.Z₀ = Z ∧ P.Wt = z.W1 (F0K K.s (w.D Z)) ∧ Ext z P.z := by
  intro hWe hDS hHC hCR hHW
  have hInp := GlobalTheory.LinksInputs.inputs_of_hypotheses hWe hDS hHC hCR
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hAll := hId.and (hHW.and (stepW_keep_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start))
  refine hAll.trans (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨-, -, hCoh⟩, hHW', hHost⟩ := H
  intro Z hX z hG2 hGT hGA hKap hFine hsub hSp
  obtain ⟨hEx, hGeo, hCore, hStd⟩ := hFine
  have hle : z.W1 (F0K K.s (w.D Z)) ⊆ {v | B.places.resChar v ∈ T.pl} := hsub
  have hc : ConjStable (w.st Z) (z.W1 (F0K K.s (w.D Z))) := fun v hv => z.nonzero_index_places_conj_stable _ v hv
  let z' := ResStd.res z hEx _ hle hc
  have hW : z'.W1 (F0K K.s (w.D Z)) = z.W1 (F0K K.s (w.D Z)) := ResStd.restrictAdelicDataTwistedPlaces_nonzeroIndexPlaces z hEx hle hc _
  have hEx' : z'.R.toRealDat.ExAt := ResStd.res_exAt z hEx hle hc
  have hGeo' : GlobalTheory.RealGeo.InGeo z'.geo := ResStd.res_inGeo z hEx hle hc hGeo
  have hCore' : CoreP z' := hCore
  have hStd' : z'.Std := ResStd.res_std z hEx hle hc hStd
  have hH : Holds z'.R z'.F := hHW' Z hX _ z' hGT hGA hKap hEx' hGeo' hCore' hG2 hW.symm hsub
  have hcs : ∀ v, B.places.conj v ∈ z'.W1 (F0K K.s (w.D Z)) ↔ v ∈ z'.W1 (F0K K.s (w.D Z)) := fun v =>
    ⟨fun h => by simpa only [B.places.conj_conj] using z'.nonzero_index_places_conj_stable _ _ h, fun h => z'.nonzero_index_places_conj_stable _ v h⟩
  obtain ⟨-, hFmax, -, -, hSt, -⟩ := hHost (w.st Z) hO
  obtain ⟨q⟩ := GlobalTheory.T.nonempty_rowLiftFamily_over_columnChoices B f T w Z hX _ z' (hInp _) hFmax (hSt 0).1 (fun i => (hSt _).2.2 (by omega) i.2) hH hcs
  exact ⟨{
    Z₀ := Z
    hX := hX
    Wt := _
    z := z'
    q := q
    g := hG2
    coh := hCoh
    grp := hGT
    grpAt := hGA
    kap := hKap
    intersectionNumber_baseChange := hH
    exAt := hEx'
    inGeo := hGeo'
    core := hCore'
    exact := hW.symm
    sub := hsub
    supp := hSp
    std := hStd' }, rfl, rfl, ResStd.res_ext z hEx hle hc⟩

end GlobalTheory.Mem.R3.Rw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constructionStartingChoices_of_fine_adelicData : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → WeightCaseCondition → StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}), GIs2 K w Z.G → GrpTrue Z.N f → GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → Fine z → (∀ v ∈ z.W1 (F0K K.s (w.D Z)), B.places.resChar v ∈ T.pl) → (∀ v, v ∉ z.W1 (F0K K.s (w.D Z)) → T.psi v = 1) → ∃ P : Pre2 K w, P.Z₀ = Z ∧ P.Wt = z.W1 (F0K K.s (w.D Z)) ∧ Ext z P.z := by
  first | exact @GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem | exact GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem | (intros; apply GlobalTheory.Mem.R3.Rw.exists_pre2_of_fine_of_resChar_mem <;> assumption)
end
