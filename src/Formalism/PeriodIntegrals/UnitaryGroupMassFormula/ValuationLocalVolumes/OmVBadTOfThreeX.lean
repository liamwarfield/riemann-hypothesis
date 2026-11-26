module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountPOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LocalOmegaVolumeUnique
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimIndep
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology Filter
  PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem prim_indep {a : ℕ} (X : TupV (E := E) v n a) (hX : IsPrim v Λ X) :
    X ∈ IndepV (E := E) (n := n) v a := by
  show LinearIndependent (Fv F v ⊗[F] E) X
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  obtain ⟨h0, hπ, -⟩ := unif_spec v ϖ hϖ
  have hm : ∀ m : ℕ, sc (E := E) v (ϖ ^ m)⁻¹ * c i ∈ OEv (E := E) v := by
    intro m
    refine hX.2 (fun j => sc (E := E) v (ϖ ^ m)⁻¹ * c j) ?_ i
    have e : (∑ j, (sc (E := E) v (ϖ ^ m)⁻¹ * c j) • X j) = sc (E := E) v (ϖ ^ m)⁻¹ • ∑ j, c j • X j := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_smul]
    rw [e, hc, smul_zero]
    exact (latLoc (E := E) v Λ).zero_mem
  by_contra hne
  have hN : {x : Fv F v ⊗[F] E | x ≠ c i} ∈ 𝓝 (0 : Fv F v ⊗[F] E) := isOpen_ne.mem_nhds (Ne.symm hne)
  obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (OEv (E := E) v) (isCompact_oEv v) (fun k => ϖ ^ k) hπ _ hN
  apply hk _ (hm k)
  show ϖ ^ k • (sc (E := E) v (ϖ ^ k)⁻¹ * c i) = c i
  rw [smul_eq_sc, ← mul_assoc, sc_mul, mul_inv_cancel₀ (pow_ne_zero _ h0), sc_one, one_mul]

def FibHensP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ (hσ : ∀ x, σ (σ x) = x)
    (hJ : ∀ i j, σ (J j i) = J i j),
    ∀ y ∈ PrimT v Λ a, PI.VolStabSW.gramH (Fv F v) σ hσ J hJ y -
        PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y ∈ hN σ v ϖ a 0 →
      ∃ D : TupV (E := E) v n a →+ HermR (Fv F v) σ a,
        (∀ k, (lamN v Λ ϖ a k).map D = hN σ v ϖ a k) ∧
        ∀ k, ∀ Z ∈ lamN v Λ ϖ a 0, ∀ W ∈ lamN v Λ ϖ a k,
          PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z + W) -
            PI.VolStabSW.gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈ hN σ v ϖ a (k + 1)

theorem fibP_of (a : ℕ) (Y : TupV (E := E) v n a) (hC : PrimCos σ J ψ v Λ a) (h3 : FibHensP σ J ψ v Λ a Y) :
    FibP σ J ψ v Λ a Y := by
  intro hG hW hH hfib ϖ hϖ
  have hG' := hG
  obtain ⟨hS, hL, hSD, hUn, ha, hP⟩ := hG
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  have hFG : (latLoc (E := E) v Λ).FG := by
    obtain ⟨L, hLat, rfl⟩ := hL
    exact basLat_fg v L hLat
  have hLo' := LocMassOrdLat.isOpen_latLoc σ J v Λ hSD hFG
  have hLc' := isCompact_latLoc v Λ hL
  have hLam : LamT v Λ a = Set.pi Set.univ fun _ =>
      (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
    ext X
    exact ⟨fun h i _ => h i, fun h i => h i trivial⟩
  have hLo : IsOpen (LamT v Λ a) := by
    rw [hLam]
    exact isOpen_set_pi Set.finite_univ fun _ _ => hLo'
  have hLc : IsCompact (LamT v Λ a) := by
    rw [hLam]
    exact isCompact_univ_pi fun _ => hLc'
  obtain ⟨hHo', hHc'⟩ := hermOC_holds v σ a
  have := PI.VolStabSW.secondCountable_Fv F v
  have := PI.VolStabSW.locallyCompact_Fv F v
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hμ : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    unfold dX; rw [dite_eq_left hW]; exact hW.choose_spec
  have hν : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    unfold dT; rw [dite_eq_left hH]; exact hH.choose_spec
  have := hμ.1
  have := hν.1
  have hfibC : IsOm σ J ψ v a (omFam σ J ψ v a) := by
    unfold omFam; rw [dite_eq_left hfib]; exact hfib.choose_spec
  have hTm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ Y
  have hom : omAt σ J ψ v (gramR (Fv F v) σ J Y) =
      omFam σ J ψ v a (PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y) := by
    unfold omAt; rw [dite_eq_left hTm]; rfl
  rw [hom]
  set G := PI.VolStabSW.gramH (n := a) (Fv F v) σ hσ J hJ with hGdef
  set T := G Y with hTdef
  set fb := omFam σ J ψ v a with hfb

  have hΛL : lamN v Λ ϖ a 0 ≤ lamS v Λ a := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hx
    exact lamS_smul v Λ (pow_mem hint _) hp
  have hΛo : ∀ k, IsOpen (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hLo
  have hΛc : ∀ k, IsCompact (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hLc
  have hΛa : Antitone (lamN v Λ ϖ a) := by
    intro m k hmk x hx
    simp only [lamN, PI.VolStabSW.mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨ϖ ^ (k - m) • p, lamS_smul v Λ (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  have hHo : ∀ k, IsOpen (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hHo'
  have hHc : ∀ k, IsCompact (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hHc'
  have hHb : ∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ k, (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) ⊆ N' := by
    intro N hN'
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (hermOE σ v a : Set (HermR (Fv F v) σ a))
      hHc' (fun k => ϖ ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN'
    refine ⟨k, ?_⟩
    simp only [hN, PI.VolStabSW.coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

  have hPcos : ∀ y ∈ PrimT v Λ a, ∀ Z ∈ lamN v Λ ϖ a 0, y + Z ∈ PrimT v Λ a := hC hS hL hSD hUn ϖ hϖ
  have hPsub : PrimT v Λ a ⊆ LamT v Λ a := fun x hx => hx.1
  have hPo : IsOpen (PrimT v Λ a) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds
      (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_
    intro x hx
    have := hPcos y hy (x - y) hx
    rwa [show y + (x - y) = x by abel] at this
  have hPcl : IsClosed (PrimT v Λ a) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    refine Filter.mem_of_superset (((hΛo 0).preimage (continuous_id.sub continuous_const)).mem_nhds
      (show y - y ∈ (lamN v Λ ϖ a 0 : Set (TupV (E := E) v n a)) by rw [sub_self]; exact zero_mem _)) ?_
    intro x hx hxP
    apply hy
    have := hPcos x hxP (-(x - y)) (neg_mem hx)
    rwa [show x + -(x - y) = y by abel] at this
  have hPc : IsCompact (PrimT v Λ a) := hLc.of_isClosed_subset hPcl hPsub
  have hPU : PrimT v Λ a ⊆ IndepV (E := E) (n := n) v a := fun x hx => prim_indep v Λ x hx
  have e := PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1
    (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G
    (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a)
    Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo hLc (lamN v Λ ϖ a) (hN σ v ϖ a) hΛL hΛo hΛc
    hΛa hHo hHc hHb (PrimT v Λ a) hPsub hPcos
    hPo hPcl Set.univ Filter.univ_mem (fun x hx _ => hPU hx) (fun y hy hyT => h3 hG' ϖ hϖ hσ hJ y hy hyT)
  have hA : PrimT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} =
      PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_uniformizer_hermitian_ideal σ v ϖ h0]
    rfl
  have hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ := by
    ext z
    exact mem_uniformizer_hermitian_ideal σ v ϖ h0 a z
  rw [hA, hHP] at e
  have hPm : MeasurableSet (PrimT v Λ a) := hPo.measurableSet
  have hind : (PrimT v Λ a).indicator (1 : TupV (E := E) v n a → ℂ) =
      fun x => (((PrimT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ PrimT v Λ a <;> simp [Set.indicator, hx]
  rw [hind, integral_complex_ofReal, integral_indicator_one hPm] at e
  have e' := Complex.ofReal_injective e
  set φ : TupV (E := E) v n a → ℝ := (PrimT v Λ a).indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hPcl, hPo⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hPc hPcl fun x hx => Set.indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ IndepV (E := E) (n := n) v a :=
    (closure_minimal Set.support_indicator_subset hPcl).trans hPU
  obtain ⟨hint', -⟩ := hfibC.2.2 φ hφc hφs hφU
  have hfin : fb T (PrimT v Λ a) ≠ ⊤ := by
    have h := hint' T (Set.mem_univ _)
    rw [hφdef, integrable_indicator_iff hPm] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne
  have hR : dX σ J ψ v a (PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) /
      dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ?_ ?_).ne
    · exact ((measure_mono Set.inter_subset_left).trans_lt hPc.measure_lt_top).ne
    · rw [← hHP]
      exact ((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'
  rw [measureReal_def] at e'
  exact (ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimDual (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∃ W ∈ LamT v Λ a, ∀ i j,
      hR (Fv F v) σ J (y i) (W j) = (if i = j then 1 else 0) ∧
        hR (Fv F v) σ J (W j) (y i) = (if i = j then 1 else 0)

def HensOntoP (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∀ S : HermR (Fv F v) σ a, S ∈ hermOE σ v a →
      ∃ W0 ∈ LamT v Λ a, crossM σ J y W0 = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))

theorem henselSurjective_of_primitiveDual (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : HensOntoP σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy S hS'
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL y hy
  obtain ⟨L, -, hLΛ⟩ := hL
  have hTr : TrOnto σ v := PI.OmLocU.Red.trOnto_holds σ J ψ v hS
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hUn _ (hS' i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS' i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  subst hLΛ
  refine ⟨fun j => ∑ k, A k j • W k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hA k j) (hW k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, A k j * hR (Fv F v) σ J (y i) (W k) = A i j := by
      simp only [fun k => (hd i k).1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e2 : ∑ k, sigR (Fv F v) σ (A k i) * hR (Fv F v) σ J (W k) (y j) = sigR (Fv F v) σ (A j i) := by
      simp only [fun k => (hd j k).2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e1, e2, hAS]

theorem fiberHensel_of_henselOnto (a : ℕ) (Y : TupV (E := E) v n a) (h : HensOntoP σ J ψ v Λ a) :
    FibHensP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ hσ hJ y hy hyT
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  refine ⟨dH σ J v hσ hJ y, fun k => ?_, fun k Z hZ W hW => ?_⟩
  · ext S
    constructor
    · rintro ⟨W, hW, rfl⟩
      obtain ⟨W0, hW0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hW
      rw [mem_hN σ v ϖ h0]
      intro i j
      refine ⟨crossM σ J y W0 i j, ?_, ?_⟩
      · exact oEv_add v (hR_mem_oEv σ J v Λ hSD (hy.1 i) (hW0 j)) (hR_mem_oEv σ J v Λ hSD (hW0 i) (hy.1 j))
      · rw [coe_dH, crossM_smul_right]
    · intro hS
      obtain ⟨S0, hS0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hS
      obtain ⟨W0, hW0, hc⟩ := h hG.1 hSD hG.2.2.2.1 hG.2.1 y hy S0 hS0
      refine AddSubgroup.mem_map.2 ⟨ϖ ^ (k + 1) • W0, (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨W0, hW0, rfl⟩, ?_⟩
      apply Subtype.ext
      funext i j
      rw [coe_dH, crossM_smul_right, hc, PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, smul_eq_sc]
  · apply rem_mem σ J v Λ hSD ϖ h0 hint hZ hW
    show gramR (Fv F v) σ J (y + Z + W) - gramR (Fv F v) σ J (y + Z) -
      (gramR (Fv F v) σ J (y + W) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W) = _
    exact gram_rem σ J y Z W

theorem fibP_of_dual (a : ℕ) (Y : TupV (E := E) v n a) (hC : PrimCos σ J ψ v Λ a) (hD : PrimDual σ J ψ v Λ a) :
    FibP σ J ψ v Λ a Y :=
  fibP_of σ J ψ v Λ a Y hC (fiberHensel_of_henselOnto σ J ψ v Λ a Y (henselSurjective_of_primitiveDual σ J ψ v Λ a hD))

end PI.OmVd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFourX
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfStepsX
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OrbPOf
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  obtain ⟨ZX, hbX, heX, hgX, hdX⟩ := hGe X hX hXY
  obtain ⟨ZY, hbY, heY, hgY, hdY⟩ := hGe Y hG.2.2.2.2.2 rfl
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (sigR (Fv F v) σ) N * (cT (sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVdEx_holds : OmVdEx X ψ := fun v hS =>
  ⟨(PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).1,
    (PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS).2.1⟩

theorem omVdUniq_holds : OmVdUniq X ψ := fun v => omUnique X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)

theorem omVdSdW_holds : OmVdSdW X ψ := fun v =>
  SdB.sdVolW_of_perf X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVdSdH_holds : OmVdSdH X ψ := fun v =>
  SdB.sdVolH_of_perf X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)
    (SdB.trPerf_of_res X.B.I.cm.sig X.B.I.J ψ v
      (Red.resAlg_of_sp X.B.I.cm.sig X.B.I.J ψ v (Red.etaSp_holds X.B.I.cm.sig X.B.I.J ψ v)))

theorem omVBadT_of_steps (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hM : ∀ v : PlX X, MeasP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hI : ∀ v : PlX X, IdxP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of X u' ψ hStd hLat hGram (omVdEx_holds X ψ) (omVdUniq_holds X ψ)
    (fun v hv => orbP_of _ _ _ _ _ _ _ (hExt v hv))
    (fun v => fibP_of_dual _ _ _ _ _ _ _ (hPC v) (hPD v))
    (fun v hv => countP_of _ _ _ _ _ _ _ (hM v) (hI v) (hCl v hv) (hPC v))
    (omVdSdW_holds X ψ) (omVdSdH_holds X ψ)

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LatBasOP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∃ b : Fin (2 * n) → (Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
    ∀ x, x ∈ latLoc (E := E) v Λ ↔ ∃ c : Fin (2 * n) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i

def IdxVP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

theorem localLattice_hasBasis
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : LatBasOP σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, -, -⟩
  obtain ⟨L, hLat, rfl⟩ := hFull
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

theorem idxVP_of (a : ℕ) (Y : TupV (E := E) v n a) (hB : LatBasOP σ J ψ v Λ a Y) (hR : ResIdx v) :
    IdxVP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  obtain ⟨b, hb, hmem⟩ := hB hG
  let φ : (Fin (2 * n) → v.adicCompletionIntegers F) →+ latA v Λ :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have key : ((lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · rintro ⟨z, hz, hze⟩ i _
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        have : (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))
            (∑ i, (d i : Fv F v) • b i) = ∑ i, (ϖ * d i) • b i := by
          show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = _
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => sc_smul_smul v ϖ _ _
        rw [← this, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      show sc (E := E) v ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (c i : Fv F v) • b i
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sc_smul_smul, hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [hR ϖ hϖ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem idxP_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxVP σ J ψ v Λ a Y) : IdxP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem MeasP₂
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : MeasP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have := PI.VolStabSW.secondCountable_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hOpen := (lamOC_holds v Λ a hFull hG.2.1).1
  refine ⟨inferInstance, hOpen.measurableSet, ?_⟩
  have e : (lamP v Λ a ϖ : Set (TupV (E := E) v n a)) = (fun X => ϖ • X) '' LamT v Λ a := by
    unfold lamP
    rw [AddSubgroup.coe_map]
    congr 1
    funext X
    funext i p
    show sc (E := E) v ϖ * X i p = ϖ • X i p
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e]
  exact (isOpenMap_smul₀ (unif_ne_zero v hϖ) _ hOpen).measurableSet

theorem idxP_holds
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set _) = Λ) (a : ℕ) (Y : TupV (E := E) v n a) : IdxP σ J ψ v Λ a Y :=
  idxP_of σ J ψ v Λ a Y (idxVP_of σ J ψ v Λ a Y (localLattice_hasBasis σ J ψ v Λ hFull a Y) (resIdx_holds v))

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_primDual_cls (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hPC : ∀ v : PlX X, PrimCos X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hPD : ∀ v : PlX X, PrimDual X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ := by
  have hFull : ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧ (L : Set _) = abelian₂ X :=
    ⟨X.B.I.L, { toIsLattice := Submodule.IsLattice.of_fg _ X.B.I.L_fg, span_eq_top := X.B.I.L_span }, rfl⟩
  exact omVBadT_of_steps X u' ψ hStd hLat hGram hExt hPC hPD (fun v => MeasP₂ _ _ _ _ _ hFull _ _)
    (fun v => idxP_holds _ _ _ _ _ hFull _ _) hCl

end Loc

end PI.OmVd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.PrimCosOf
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem near_int {a : ℕ} (ϖ : Fv F v) (hϖ : IsUnif v ϖ) (A : Fin a → Fin a → Fv F v ⊗[F] E)
    (hA : ∀ i j, A i j ∈ OEv (E := E) v) (d : Fin a → Fv F v ⊗[F] E)
    (hu : ∀ i, d i + sc (E := E) v ϖ * ∑ j, A i j * d j ∈ OEv (E := E) v) : ∀ i, d i ∈ OEv (E := E) v := by
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  have hev : ∀ i, ∀ᶠ k in atTop, ϖ ^ k • d i ∈ OEv (E := E) v := by
    intro i
    have ht : Tendsto (fun k : ℕ => ϖ ^ k • d i) atTop (𝓝 0) := by
      have := hπ.smul_const (d i)
      simpa using this
    exact ht ((isOpen_oEv (E := E) v).mem_nhds (oEv_zero v))
  obtain ⟨N, hN⟩ := (Filter.eventually_all.2 hev).exists
  have key : ∀ m : ℕ, (∀ i, sc (E := E) v (ϖ ^ m) * d i ∈ OEv (E := E) v) → ∀ i, d i ∈ OEv (E := E) v := by
    intro m
    induction m with
    | zero =>
      intro h i
      simpa [sc_one] using h i
    | succ m ih =>
      intro h
      apply ih
      intro i
      have hS : ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) =
          sc (E := E) v (ϖ ^ m) * sc (E := E) v ϖ * ∑ j, A i j * d j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, ← sc_mul]
        ring
      have e : sc (E := E) v (ϖ ^ m) * d i = sc (E := E) v (ϖ ^ m) * (d i + sc (E := E) v ϖ * ∑ j, A i j * d j) -
          ∑ j, A i j * (sc (E := E) v (ϖ ^ (m + 1)) * d j) := by
        rw [hS]
        ring
      rw [e, sub_eq_add_neg]
      exact oEv_add v (sc_mul_mem_oEv v (pow_mem hint m) (hu i))
        (oEv_neg v (oEv_sum v _ _ fun j _ => oEv_mul v (hA i j) (h j)))
  exact key N fun i => by rw [← smul_eq_sc]; exact hN i

theorem primCos_of (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : PrimCos σ J ψ v Λ a := by
  intro hS hL hSD hUn ϖ hϖ X hX Z hZ
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨P, hP, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hZ
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL X hX
  have hPs : ϖ ^ (0 + 1) • P ∈ lamS v Λ a := lamS_smul v Λ (pow_mem hint _) hP
  refine ⟨fun i => (latLoc (E := E) v Λ).add_mem (hX.1 i) (hPs i), fun c hc => ?_⟩
  have hsm : ∀ j i, hR (Fv F v) σ J (W j) ((ϖ ^ (0 + 1) • P) i) = sc (E := E) v ϖ * hR (Fv F v) σ J (W j) (P i) := by
    intro j i
    have := hR_smul_smul σ J v 1 (ϖ ^ (0 + 1)) (W j) (P i)
    rw [one_smul, one_mul, zero_add, pow_one] at this
    rw [zero_add, pow_one]
    exact this
  have hpair : ∀ j, hR (Fv F v) σ J (W j) (∑ i, c i • (X + ϖ ^ (0 + 1) • P) i) =
      c j + sc (E := E) v ϖ * ∑ i, hR (Fv F v) σ J (W j) (P i) * c i := by
    intro j
    rw [hR_sum_smul_right]
    have h1 : ∀ i, c i * hR (Fv F v) σ J (W j) ((X + ϖ ^ (0 + 1) • P) i) =
        c i * (if i = j then 1 else 0) + sc (E := E) v ϖ * (hR (Fv F v) σ J (W j) (P i) * c i) := by
      intro i
      rw [Pi.add_apply, hR_add_right, (hd i j).2, hsm j i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [mul_ite]
  exact near_int v ϖ hϖ (fun j i => hR (Fv F v) σ J (W j) (P i))
    (fun j i => hR_mem_oEv σ J v Λ hSD (hW j) (hP i)) c
    (fun j => by rw [← hpair j]; exact hR_mem_oEv σ J v Λ hSD (hW j) hc)

end PI.OmVd
end
end

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def LeftInvO (a : ℕ) : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v →
  ∀ M : Matrix (Fin n) (Fin a) (Fv F v ⊗[F] E), (∀ k i, M k i ∈ OEv (E := E) v) →
    (∀ c : Fin a → Fv F v ⊗[F] E, (∀ k, Matrix.mulVec M c k ∈ OEv (E := E) v) → ∀ i, c i ∈ OEv (E := E) v) →
    ∃ N : Matrix (Fin a) (Fin n) (Fv F v ⊗[F] E), (∀ i k, N i k ∈ OEv (E := E) v) ∧ N * M = 1

theorem primDual_of (a : ℕ) (hB : Red.OBas1 σ J ψ v Λ) (hLI : LeftInvO σ J ψ v (n := n) a) :
    PrimDual σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  obtain ⟨e, he, hg⟩ := hB hS hL hSD hUn
  have hee : ∀ k l, hR (Fv F v) σ J (e k) (e l) = if k = l then 1 else 0 := by
    intro k l
    have := congrFun (congrFun hg k) l
    simpa [gramR, Matrix.one_apply] using this
  have hcoord : ∀ i, ∃ c : Fin n → Fv F v ⊗[F] E, (∀ k, c k ∈ OEv (E := E) v) ∧ y i = ∑ k, c k • e k :=
    fun i => (he (y i)).1 (hy.1 i)
  choose M hM hyM using hcoord
  obtain ⟨N, hN, hNM⟩ := hLI hS hUn (Matrix.of fun k i => M i k) (fun k i => hM i k) (by
    intro c hc i
    apply hy.2 c _ i
    have e1 : ∑ i, c i • y i = ∑ k, Matrix.mulVec (Matrix.of fun k i => M i k) c k • e k := by
      simp only [hyM, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]
    rw [e1]
    exact (he _).2 ⟨_, hc, rfl⟩)
  have hNM' : ∀ j i, ∑ l, N j l * M i l = if j = i then 1 else 0 := by
    intro j i
    have := congrFun (congrFun hNM j) i
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  refine ⟨fun j => ∑ l, sigR (Fv F v) σ (N j l) • e l,
    fun j => (he _).2 ⟨_, fun l => UnN.sigR_mem σ v (hN j l), rfl⟩, fun i j => ⟨?_, ?_⟩⟩
  · have h1 : ∀ l, hR (Fv F v) σ J (y i) (e l) = sigR (Fv F v) σ (M i l) := by
      intro l
      rw [hyM i, hR_sum_smul_left]
      simp [hee]
    rw [hR_sum_smul_right]
    simp only [h1]
    have e2 : ∑ l, sigR (Fv F v) σ (N j l) * sigR (Fv F v) σ (M i l) =
        sigR (Fv F v) σ (∑ l, N j l * M i l) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul]
    rw [e2, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  · have h2 : ∀ k, hR (Fv F v) σ J (∑ l, sigR (Fv F v) σ (N j l) • e l) (e k) = N j k := by
      intro k
      rw [hR_sum_smul_left]
      simp only [hee, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact PI.VolStabSW.sigR_invol (Fv F v) σ hσ (N j k)
    rw [hyM i, hR_sum_smul_right]
    simp only [h2]
    have e3 : ∑ k, M i k * N j k = ∑ k, N j k * M i k := Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [e3, hNM' j i]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]

theorem oBas1_holds : Red.OBas1 σ J ψ v Λ := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  exact Red.oBas1_of_unitV σ J ψ v Λ
    (Orb.unitV_of σ J ψ v Λ (PI.OmLocU.NormOneUnitFixedPoints.normOne_of σ J ψ v hR) (UnN.unitNorm_of_res σ J ψ v Λ hR))

theorem primDual_of_left (a : ℕ) (hLI : LeftInvO σ J ψ v (n := n) a) : PrimDual σ J ψ v Λ a :=
  primDual_of σ J ψ v Λ a (oBas1_holds σ J ψ v Λ) hLI

end Gen

section Loc

open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_std_lat_gram (hStd : OmVStd X ψ) (hLat : OmVLat X) (hGram : OmVGram X u')
    (hExt : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ExtP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hLI : ∀ v : PlX X, LeftInvO X.B.I.cm.sig X.B.I.J ψ v (n := X.B.I.n) (D.R.rS + 1 + D.R.rS))
    (hCl : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      ClsP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v)) :
    OmVBadT X u' ψ :=
  omVBadT_of_primDual_cls X u' ψ hStd hLat hGram hExt
    (fun v => primCos_of _ _ _ _ _ _ (primDual_of_left _ _ _ _ _ _ (hLI v)))
    (fun v => primDual_of_left _ _ _ _ _ _ (hLI v)) hCl

end Loc

end PI.OmVd
