module

public import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRingEquivAddOne
namespace GlobalTheory.ShiftVariables

noncomputable def shiftVars (ι k : Type) [CommRing k] :
    MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + 1)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - 1)
    (by ext1 i; simp) (by ext1 i; simp)

theorem shiftVars_X (ι k : Type) [CommRing k] (i : ι) :
    shiftVars ι k (MvPolynomial.X i) = MvPolynomial.X i + 1 := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + 1) (MvPolynomial.X i) = _
  simp

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental (↥k) c) :
    ∃ (σ : Ω ≃+* Ω), (∀ a ∈ k, (σ : Ω → Ω) a = a) ∧ (σ : Ω → Ω) c = c + (1 : Ω) := by
  classical
  have hs : AlgebraicIndepOn (↥k) id ({c} : Set Ω) :=
    algebraicIndependent_unique_type_iff.mpr (by simpa using hc)
  obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset hs
  have hind : AlgebraicIndependent (↥k) ((↑) : t → Ω) := ht.1
  set K := IntermediateField.adjoin (↥k) (Set.range ((↑) : t → Ω)) with hK
  let e := hind.aevalEquivField
  let φ : FractionRing (MvPolynomial t ↥k) ≃ₐ[↥k] FractionRing (MvPolynomial t ↥k) :=
    IsFractionRing.algEquivOfAlgEquiv (K := FractionRing (MvPolynomial t ↥k))
      (L := FractionRing (MvPolynomial t ↥k)) (shiftVars t ↥k)
  let τ : K ≃ₐ[↥k] K := e.symm.trans (φ.trans e)
  have hmem : ∀ i : t, (i : Ω) ∈ K := fun i =>
    IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
  have he : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i)) = ⟨i, hmem i⟩ := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have he1 : ∀ i : t, e (algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i + 1)) =
      ⟨i, hmem i⟩ + 1 := by
    intro i
    apply Subtype.ext
    rw [hind.aevalEquivField_algebraMap_apply_coe]
    simp
  have hτ : ∀ i : t, τ ⟨i, hmem i⟩ = ⟨i, hmem i⟩ + 1 := by
    intro i
    have h0 : e.symm ⟨i, hmem i⟩ = algebraMap (MvPolynomial t ↥k) _ (MvPolynomial.X i) := by
      rw [AlgEquiv.symm_apply_eq, he]
    change e (φ (e.symm ⟨i, hmem i⟩)) = _
    rw [h0, IsFractionRing.algEquivOfAlgEquiv_algebraMap, shiftVars_X, he1]
  have : Algebra.IsAlgebraic K Ω := ht.isAlgebraic_field
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let σ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω τ.toRingEquiv
  have hσ : ∀ y : K, σ (y : Ω) = (τ y : Ω) := fun y =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ.toRingEquiv y
  refine ⟨σ, fun a ha => ?_, ?_⟩
  · have hak : a ∈ K := IntermediateField.algebraMap_mem K (⟨a, ha⟩ : ↥k)
    have h1 := hσ ⟨a, hak⟩
    have h2 : τ ⟨a, hak⟩ = ⟨a, hak⟩ := τ.commutes (⟨a, ha⟩ : ↥k)
    rw [h2] at h1
    exact h1
  · have hc' : c ∈ t := hct rfl
    have h1 := hσ ⟨c, hmem ⟨c, hc'⟩⟩
    rw [hτ ⟨c, hc'⟩] at h1
    simpa using h1

end GlobalTheory.ShiftVariables
end

open Polynomial

namespace GlobalTheory.FixedRoots

theorem exists_ringEquiv_add_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] (k : Subfield Ω) (c : Ω)
    (hc : Transcendental k c) :
    ∃ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) ∧ σ c = c + 1 := by
  first
  | exact @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one
  | (apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ShiftVariables.exists_ringEquiv_add_one ..)

theorem mem_of_forall_ringEquiv_fixed {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2

end GlobalTheory.FixedRoots
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInte
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.HaarFactor

section General
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]

theorem slice_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (c : A) : (fun x => G (x, c)) ∈ SB X₀ := by
  refine ⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_fst) fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, c), h, rfl⟩

theorem fiber_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (x : X₀) : (fun a => G (x, a)) ∈ SB A := by
  refine ⟨hG.1.comp_continuous (by fun_prop), HasCompactSupport.intro (hG.2.image continuous_snd) fun a ha => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ha ⟨(x, a), h, rfl⟩

theorem tens_mem {f : X₀ → ℂ} (hf : f ∈ SB X₀) {φ : A → ℂ} (hφ : φ ∈ SB A) :
    (fun z : X₀ × A => f z.1 * φ z.2) ∈ SB (X₀ × A) := by
  refine ⟨(hf.1.comp_continuous continuous_fst).mul (hφ.1.comp_continuous continuous_snd),
    HasCompactSupport.intro (hf.2.prod hφ.2) fun z hz => ?_⟩
  rcases not_and_or.mp (Set.mem_prod.not.mp hz) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem transl_mem {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) (c : A) :
    (fun z : X₀ × A => G (z.1, z.2 - c)) ∈ SB (X₀ × A) := by
  refine ⟨hG.1.comp_continuous (by fun_prop), ?_⟩
  exact hG.2.comp_homeomorph ((Homeomorph.refl X₀).prodCongr (Homeomorph.subRight c))

theorem ind_mem {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (U : Set A).indicator (fun _ => (1 : ℂ)) ∈ SB A := by
  have hcl : IsClopen (U : Set A) := ⟨U.isClosed_of_isOpen hUo, hUo⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hUc fun y hy => Set.indicator_of_notMem hy _⟩
  by_cases hx : x ∈ (U : Set A)
  · filter_upwards [hcl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz]
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with z hz
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]

def tensL (φ : SB A) : SB X₀ →ₗ[ℂ] SB (X₀ × A) where
  toFun f := ⟨fun z => f.1 z.1 * φ.1 z.2, tens_mem f.2 φ.2⟩
  map_add' f g := by ext z; simp [add_mul]
  map_smul' c f := by ext z; simp [mul_assoc]

theorem exists_subgroup_invariant
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A)) :
    ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧
      ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z := by
  have h1 : ∀ᶠ t in 𝓝 (0 : A), ∀ z ∈ tsupport G, G (z.1, z.2 + t) = G z := by
    refine IsCompact.eventually_forall_of_forall_eventually hG.2 fun z _ => ?_
    have h2 : IsLocallyConstant fun q : A × (X₀ × A) => (G (q.2.1, q.2.2 + q.1), G q.2) :=
      (hG.1.comp_continuous (by fun_prop)).prodMk (hG.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, z)] with q hq
    simp only [Prod.mk.injEq, add_zero, Prod.mk.eta] at hq
    rw [hq.1, hq.2]
  obtain ⟨U, hUo, hUc, hUs⟩ := hbasis _ h1
  refine ⟨U, hUo, hUc, fun u hu z => ?_⟩
  by_cases hz : z ∈ tsupport G
  · exact hUs hu z hz
  by_cases hz' : (z.1, z.2 + u) ∈ tsupport G
  · have := hUs (U.neg_mem hu) _ hz'
    simp only [add_neg_cancel_right, Prod.mk.eta] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hz, image_eq_zero_of_notMem_tsupport hz']

theorem exists_decomp {U : AddSubgroup A} (hU : IsOpen (U : Set A)) {G : X₀ × A → ℂ} (hG : G ∈ SB (X₀ × A))
    (hinv : ∀ u ∈ U, ∀ z : X₀ × A, G (z.1, z.2 + u) = G z) :
    ∃ T : Finset (A ⧸ U), ∀ z : X₀ × A,
      G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) := by
  classical
  have hK : IsCompact (Prod.snd '' tsupport G) := hG.2.image continuous_snd
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun a => (fun b => b - a) ⁻¹' (U : Set A))
    (fun a _ => (hU.preimage (by fun_prop)).mem_nhds (by simp))
  refine ⟨t.image (QuotientAddGroup.mk : A → A ⧸ U), fun z => ?_⟩
  have hind : ∀ q : A ⧸ U, (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out) =
      if (z.2 : A ⧸ U) = q then 1 else 0 := by
    intro q
    have : (z.2 : A ⧸ U) = q ↔ z.2 - q.out ∈ U := by
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      exact QuotientAddGroup.eq_iff_sub_mem
    by_cases h : z.2 - q.out ∈ U
    · rw [Set.indicator_of_mem (show z.2 - q.out ∈ (U : Set A) from h), if_pos (this.mpr h)]
    · rw [Set.indicator_of_notMem (show z.2 - q.out ∉ (U : Set A) from h), if_neg (fun h' => h (this.mp h'))]
  simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']
  split_ifs with h
  · have h2 : -z.2 + (z.2 : A ⧸ U).out ∈ U := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have := hinv _ h2 z
    rw [add_neg_cancel_left] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hz => h ?_
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht ⟨z, hz, rfl⟩)
    exact Finset.mem_image.mpr ⟨a, ha, (QuotientAddGroup.eq_iff_sub_mem.mpr hza).symm⟩

section Meas
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]

theorem integrable_of_SB {φ : A → ℂ} (hφ : φ ∈ SB A) : Integrable φ μ :=
  hφ.1.continuous.integrable_of_hasCompactSupport hφ.2

theorem real_ne_zero {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (μ.real (U : Set A) : ℂ) ≠ 0 := by
  have h1 : 0 < μ (U : Set A) := hUo.measure_pos μ ⟨0, U.zero_mem⟩
  have h2 : μ (U : Set A) ≠ ⊤ := hUc.measure_lt_top.ne
  exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'

theorem fiber_integral {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A))
    {G : X₀ × A → ℂ} (T : Finset (A ⧸ U))
    (hT : ∀ z : X₀ × A, G z = ∑ q ∈ T, G (z.1, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (z.2 - q.out))
    (x : X₀) : ∫ a, G (x, a) ∂μ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
  have he := integrable_of_SB μ (ind_mem hUo hUc)
  have hshift : ∀ c : A, ∫ a, (U : Set A).indicator (fun _ => (1 : ℂ)) (a - c) ∂μ = (μ.real (U : Set A) : ℂ) := by
    intro c
    rw [integral_sub_right_eq_self (fun a => (U : Set A).indicator (fun _ => (1 : ℂ)) a) c,
      integral_indicator_const _ hUo.measurableSet]
    simp
  calc ∫ a, G (x, a) ∂μ
      = ∫ a, ∑ q ∈ T, G (x, q.out) * (U : Set A).indicator (fun _ => (1 : ℂ)) (a - q.out) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun a => hT (x, a))
    _ = (∑ q ∈ T, G (x, q.out)) * (μ.real (U : Set A) : ℂ) := by
      rw [MeasureTheory.integral_finsetSum _ fun q _ => (he.comp_sub_right _).const_mul _]
      simp only [integral_const_mul, hshift, ← Finset.sum_mul]

theorem map_eq_zero_of_fiber
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G)
    (G : SB (X₀ × A)) (hG : ∀ x, ∫ a, G.1 (x, a) ∂μ = 0) : L G = 0 := by
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hsum : ∀ x, ∑ q ∈ T, G.1 (x, q.out) = 0 := fun x => by
    have := (fiber_integral μ hUo hUc T hT x).symm.trans (hG x)
    exact (mul_eq_zero.mp this).resolve_right (real_ne_zero μ hUo hUc)
  let e : SB A := ⟨_, ind_mem hUo hUc⟩
  let g : A ⧸ U → SB X₀ := fun q => ⟨_, slice_mem G.2 q.out⟩
  let Gq : A ⧸ U → SB (X₀ × A) := fun q =>
    ⟨fun z => (tensL e (g q)).1 (z.1, z.2 - q.out), transl_mem (tensL e (g q)).2 q.out⟩
  have hdec : G = ∑ q ∈ T, Gq q := by
    apply Subtype.ext
    funext z
    rw [hT z, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have hq : ∀ q, L (Gq q) = L (tensL e (g q)) := fun q =>
    (hL q.out (Gq q) (tensL e (g q)) fun z => by simp [Gq, tensL, g, e]).symm
  have hg : ∑ q ∈ T, g q = 0 := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    exact hsum x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum, Finset.sum_congr rfl fun q _ => hq q, ← map_sum, ← map_sum, hg, map_zero, map_zero]

theorem exists_factor
    (hbasis : ∀ V ∈ 𝓝 (0 : A), ∃ U : AddSubgroup A, IsOpen (U : Set A) ∧ IsCompact (U : Set A) ∧ (U : Set A) ⊆ V)
    {M : Type*} [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × A) →ₗ[ℂ] M)
    (hL : ∀ (a : A) (G G' : SB (X₀ × A)), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) :
    ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G : SB (X₀ × A), ∃ Ψ : SB X₀,
      (∀ x, Ψ.1 x = ∫ a, G.1 (x, a) ∂μ) ∧ L G = l₀ Ψ := by
  obtain ⟨B, hBo, hBc, -⟩ := hbasis Set.univ Filter.univ_mem
  have hpos := real_ne_zero μ hBo hBc
  let φ₀ : SB A := (μ.real (B : Set A) : ℂ)⁻¹ • ⟨_, ind_mem hBo hBc⟩
  have hφ₀ : ∫ a, φ₀.1 a ∂μ = 1 := by
    show ∫ a, (μ.real (B : Set A) : ℂ)⁻¹ * (B : Set A).indicator (fun _ => (1 : ℂ)) a ∂μ = 1
    rw [integral_const_mul, integral_indicator_const _ hBo.measurableSet]
    simp [hpos]
  refine ⟨L ∘ₗ tensL φ₀, fun G => ?_⟩
  obtain ⟨U, hUo, hUc, hinv⟩ := exists_subgroup_invariant hbasis G.2
  obtain ⟨T, hT⟩ := exists_decomp hUo G.2 hinv
  have hΨ : (fun x => ∫ a, G.1 (x, a) ∂μ) ∈ SB X₀ := by
    have := (SB X₀).smul_mem (μ.real (U : Set A) : ℂ)
      (Submodule.sum_mem _ fun q (_ : q ∈ T) => slice_mem G.2 q.out)
    convert this using 1
    funext x
    rw [fiber_integral μ hUo hUc T hT x]
    simp [Finset.sum_apply, mul_comm]
  refine ⟨⟨_, hΨ⟩, fun x => rfl, ?_⟩
  rw [← sub_eq_zero, LinearMap.comp_apply, ← map_sub]
  refine map_eq_zero_of_fiber μ hbasis L hL _ fun x => ?_
  show ∫ a, (G.1 (x, a) - (∫ a', G.1 (x, a') ∂μ) * φ₀.1 a) ∂μ = 0
  rw [integral_sub (integrable_of_SB μ (fiber_mem G.2 x)) ((integrable_of_SB μ φ₀.2).const_mul _),
    integral_const_mul, hφ₀, mul_one, sub_self]

end Meas
end General

section Concrete
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

def boxSub (n : Type*) (s : kˣ) : AddSubgroup (n → k) := AddSubgroup.pi Set.univ fun _ => cballSub s

theorem coe_boxSub (n : Type*) (s : kˣ) : (boxSub n s : Set (n → k)) = FourierPi.box n s := by
  ext x
  simp only [SetLike.mem_coe, boxSub, AddSubgroup.mem_pi, FourierPi.box, Set.mem_pi]
  rfl

theorem basis_prod (m₁ m₂ : Type*) [Fintype m₁] [Fintype m₂] :
    ∀ V ∈ 𝓝 (0 : (m₁ → k) × (m₂ → k)), ∃ U : AddSubgroup ((m₁ → k) × (m₂ → k)),
      IsOpen (U : Set ((m₁ → k) × (m₂ → k))) ∧ IsCompact (U : Set ((m₁ → k) × (m₂ → k))) ∧
        (U : Set ((m₁ → k) × (m₂ → k))) ⊆ V := by
  intro V hV
  rw [Prod.zero_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at hV
  obtain ⟨t₁, h₁, t₂, h₂, hsub⟩ := hV
  obtain ⟨s₁, hs₁⟩ := FourierPi.exists_box_subset h₁
  obtain ⟨s₂, hs₂⟩ := FourierPi.exists_box_subset h₂
  refine ⟨(boxSub m₁ s₁).prod (boxSub m₂ s₂), ?_, ?_, ?_⟩ <;> rw [AddSubgroup.coe_prod, coe_boxSub, coe_boxSub]
  · exact (FourierPi.isOpen_box s₁).prod (FourierPi.isOpen_box s₂)
  · exact (FourierPi.isCompact_box s₁).prod (FourierPi.isCompact_box s₂)
  · exact (Set.prod_mono hs₁ hs₂).trans hsub

end Concrete

theorem translation_invariant_factors : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  intro k _ _ _ _ _ _ ν hν X₀ _ _ _ _ m₁ m₂ _ _ M _ _ L hL
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hν
  haveI : LocallyCompactSpace k := inferInstance
  haveI : SigmaFinite ν := inferInstance
  haveI : (Measure.pi fun _ : m₁ => ν).IsAddHaarMeasure := inferInstance
  haveI : (Measure.pi fun _ : m₂ => ν).IsAddHaarMeasure := inferInstance
  obtain ⟨l₀, hl₀⟩ := exists_factor ((Measure.pi fun _ : m₁ => ν).prod (Measure.pi fun _ : m₂ => ν))
    (basis_prod m₁ m₂) L hL
  refine ⟨l₀, fun G => ?_⟩
  obtain ⟨Ψ, hΨ, hLG⟩ := hl₀ G
  refine ⟨Ψ, fun x => ?_, hLG⟩
  rw [hΨ x, integral_prod _ (integrable_of_SB _ (fiber_mem G.2 x))]

end GlobalTheory.SplitWeil.HaarFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslationInvariantSchwartzBruhatMapFactorsInteStatement
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translationInvariant_schwartzBruhat_map_factors_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (X₀ : Type) [TopologicalSpace X₀] [T2Space X₀] [LocallyCompactSpace X₀] [TotallyDisconnectedSpace X₀] (m₁ m₂ : Type) [Fintype m₁] [Fintype m₂] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (X₀ × ((m₁ → k) × (m₂ → k))) →ₗ[ℂ] M), (∀ (a : (m₁ → k) × (m₂ → k)) (G G' : SB (X₀ × ((m₁ → k) × (m₂ → k)))), (∀ z, G'.1 z = G.1 (z.1, z.2 + a)) → L G' = L G) → ∃ l₀ : SB X₀ →ₗ[ℂ] M, ∀ G, ∃ Ψ : SB X₀, (∀ x, Ψ.1 x = ∫ a₁, ∫ a₂, G.1 (x, (a₁, a₂)) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν)) ∧ L G = l₀ Ψ := by
  first | exact @GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | exact GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors | (intros; apply GlobalTheory.SplitWeil.HaarFactor.translation_invariant_factors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

section Abstract

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}

theorem ind_mem (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩

theorem mem_of_ind_mem (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem eventually_invariant {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) :
    ∀ᶠ u in 𝓝 (0 : Matrix Y Y' k), ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t :=
  hΦ.2.isCompact.eventually_forall_of_forall_eventually (P := fun u t => Φ (t + u) = Φ t) fun x _ => by
    have h1 := ((continuous_snd.add continuous_fst).tendsto' ((0 : Matrix Y Y' k), x) x (add_zero x)).eventually
      (hΦ.1.eventually_eq x)
    have h2 := (continuous_snd.tendsto ((0 : Matrix Y Y' k), x)).eventually (hΦ.1.eventually_eq x)
    filter_upwards [h1, h2] with z a b using a.trans b.symm

theorem invariant_of_tsupport {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']

theorem exists_cosets {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩

theorem sb_le {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩

end GlobalTheory.LocMod.Inhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualOfCovolumeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualOfCovolumeOne
open MeasureTheory Topology

namespace GlobalTheory.CovolumeOneSelfDual

theorem unfold {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G) (hF : IsAddFundamentalDomain Γ 𝓕 μ) (c : G → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : Γ => ‖c (γ + y)‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' γ : Γ, c (γ + y) ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun y => c (γ + y)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_left μ (γ : G)).quasiMeasurePreserving
    exact this.restrict
  have hl : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    rfl
  have hfin : ∑' γ : Γ, ∫⁻ y in 𝓕, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne
  refine ⟨?_, ?_⟩
  · have h1 : ∫⁻ y in 𝓕, ∑' γ : Γ, ‖c (γ + y)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : Γ, ‖c (γ + y)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : Γ, (‖c (γ + y)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  · rw [integral_tsum hm hfin, hF.integral_eq_tsum'' c hc]
    rfl

theorem finite_contributing {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hs : HasCompactSupport f)
    {C : Set G} (hC : IsCompact C) : {γ : Γ | ∃ x ∈ C, f (γ + x) ≠ 0}.Finite := by
  have hK := (hs.isCompact.prod hC).image (f := fun p : G × G => p.1 - p.2) (by fun_prop)
  have ht : Filter.Tendsto ((↑) : Γ → G) Filter.cofinite (Filter.cocompact G) :=
    AddSubgroup.tendsto_coe_cofinite_of_discrete Γ (isDiscrete_iff_discreteTopology.2 inferInstance)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨x, hx, h⟩ hn
  exact hn ⟨(γ + x, x), ⟨subset_tsupport f h, hx⟩, by simp⟩

theorem continuous_periodization {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) : Continuous fun x : G => ∑' γ : Γ, f (γ + x) := by
  have hlf : LocallyFinite fun γ : Γ => Function.support fun x : G => f (γ + x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, (finite_contributing Γ hs hC).subset ?_⟩
    rintro γ ⟨p, h, h1⟩
    exact ⟨p, h1, h⟩
  have h : Continuous fun x : G => ∑ᶠ γ : Γ, f (γ + x) :=
    continuous_finsum (fun γ => by fun_prop) hlf
  refine h.congr fun x => (tsum_eq_finsum ?_).symm
  refine (finite_contributing Γ hs (isCompact_singleton (x := x))).subset ?_
  intro γ hγ
  exact ⟨x, rfl, hγ⟩

section

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
  (B : G → G → ℂ) (hc : ∀ y, Continuous fun x => B x y) (hsy : ∀ x y, B x y = B y x)
  (hadd : ∀ x x' y, B (x + x') y = B x y * B x' y) (hn : ∀ x y, ‖B x y‖ = 1)
  (hker : ∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) (hinj : ∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0)
  (μ : Measure G) (𝓕 : Set G) [hμ : μ.IsAddHaarMeasure] (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1)

include hK hcov hc hsy hadd hn hker hinj hμ hF h1

theorem poisson {f : G → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hsum : Summable fun γ : Γ => ‖∫ x, f x * B x γ ∂μ‖) :
    ∑' ξ : Γ, f ξ = ∑' γ : Γ, ∫ x, f x * B x γ ∂μ := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  have hcoef : ∀ γ : Γ, ∫ x in 𝓕, B γ x * (∑' ξ : Γ, f (ξ + x)) ∂μ = ∫ x, f x * B x γ ∂μ := by
    intro γ
    have hi : Integrable (fun x => f x * B x γ) μ :=
      (hf.mul (hc γ)).integrable_of_hasCompactSupport hs.mul_right
    rw [(unfold Γ μ 𝓕 hF _ hi).2]
    congr 1
    funext x
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    rw [hadd, (hker γ).2 γ.2 ξ ξ.2, one_mul, mul_comm, hsy]
  have key := GlobalTheory.CompactQuotientFourier.inversion_at_zero G Γ K hK hcov Γ (fun γ x => B γ x)
    (fun γ => hc' γ) (fun γ x y => hadd' γ x y) (fun a b x => hadd a b x) (fun a x => hn a x)
    (fun x => by rw [← hker x]; exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    (fun a h => Subtype.ext (hinj a a.2 h)) μ 𝓕 hμ hF h1 (fun x => ∑' ξ : Γ, f (ξ + x))
    (continuous_periodization Γ hf hs)
    (fun γ hγ x => by
      rw [← (Equiv.addRight (⟨γ, hγ⟩ : Γ)).tsum_eq fun ξ : Γ => f (ξ + x)]
      refine tsum_congr fun ξ => ?_
      simp [add_assoc])
    (by simp only [hcoef]; exact hsum)
  simp only [hcoef, add_zero] at key
  exact key

theorem inversion_zero {Φ : G → ℂ} (hΦ : Continuous Φ) (hs : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * B x y ∂μ) μ) :
    ∫ y, (∫ x, Φ x * B x y ∂μ) ∂μ = Φ 0 := by
  classical
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hc' : ∀ y, Continuous (B y) := fun y => (hc y).congr fun x => hsy x y
  have hadd' : ∀ y x x', B y (x + x') = B y x * B y x' := fun y x x' => by
    rw [hsy y, hadd, hsy x, hsy x']
  obtain ⟨hae, hint⟩ := unfold Γ μ 𝓕 hF _ hI
  have he : ∀ (y : G) (γ : Γ), ∫ x, Φ x * B x (γ + y) ∂μ = ∫ x, (Φ x * B x y) * B x γ ∂μ := by
    intro y γ
    congr 1
    funext x
    rw [hadd']
    ring
  have h2 : ∫ y in 𝓕, ∑' γ : Γ, (∫ x, Φ x * B x (γ + y) ∂μ) ∂μ = ∫ y in 𝓕, ∑' ξ : Γ, Φ ξ * B ξ y ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [he] at hy ⊢
    exact (poisson Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1 (hΦ.mul (hc y)) hs.mul_right hy).symm
  have hfin : {ξ : Γ | Φ ξ ≠ 0}.Finite := by
    refine (finite_contributing Γ hs (isCompact_singleton (x := (0 : G)))).subset ?_
    intro ξ hξ
    exact ⟨0, rfl, by simpa using hξ⟩
  have hFi : ∀ ξ : Γ, Integrable (fun y => Φ ξ * B ξ y) (μ.restrict 𝓕) := fun ξ =>
    Integrable.of_bound (continuous_const.mul (hc' ξ)).aestronglyMeasurable ‖Φ ξ‖
      (Filter.Eventually.of_forall fun y => by rw [norm_mul, hn, mul_one])
  have hFs : Summable fun ξ : Γ => ∫ y in 𝓕, ‖Φ ξ * B ξ y‖ ∂μ := by
    refine summable_of_hasFiniteSupport (hfin.subset ?_)
    intro ξ hξ h0
    exact hξ (by simp [h0])
  have horth : ∀ ξ : Γ, ξ ≠ 0 → ∫ y in 𝓕, B ξ y ∂μ = 0 := by
    intro ξ hξ
    obtain ⟨u, hu⟩ : ∃ u, B ξ u ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (Subtype.ext (hinj ξ ξ.2 h))
    have key := GlobalTheory.CompactQuotientFourier.setIntegral_translate Γ μ 𝓕 hF (B ξ)
      (fun γ hγ w => by rw [hadd', (hker γ).2 hγ ξ ξ.2, one_mul]) u
    simp_rw [hadd' _ _ u] at key
    rw [integral_mul_const] at key
    have h3 : (∫ y in 𝓕, B ξ y ∂μ) * (B ξ u - 1) = 0 := by
      rw [mul_sub, key, mul_one, sub_self]
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hu)
  have hB0 : ∀ y, B 0 y = 1 := fun y => by
    rw [hsy]
    have hne : B y 0 ≠ 0 := fun h => by simpa [h] using hn y 0
    have h2 : B y 0 * B y 0 = B y 0 * 1 := by rw [mul_one, ← hadd', add_zero]
    exact mul_left_cancel₀ hne h2
  rw [hint, h2, ← integral_tsum_of_summable_integral_norm hFi hFs, tsum_eq_single (0 : Γ)]
  · simp [hB0, hvol]
  · intro ξ hξ
    rw [integral_const_mul, horth ξ hξ, mul_zero]

end

theorem selfDual_of_covolume_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hμ hF h1
  refine ⟨hμ, fun Φ hΦ hs hI z => ?_⟩
  have he : ∀ y, ∫ x, Φ (x - z) * B x y ∂μ = (∫ x, Φ x * B x y ∂μ) * B y z := by
    intro y
    rw [← integral_add_right_eq_self (fun x => Φ (x - z) * B x y) z, ← integral_mul_const]
    congr 1
    funext x
    rw [add_sub_cancel_right, hadd, hsy z y, mul_assoc]
  have hs' : HasCompactSupport fun x => Φ (x - z) := hs.comp_homeomorph (Homeomorph.subRight z)
  have hI' : Integrable (fun y => ∫ x, Φ (x - z) * B x y ∂μ) μ := by
    simp only [he]
    exact hI.mul_bdd (c := 1) (hc z).aestronglyMeasurable (Filter.Eventually.of_forall fun y => (hn y z).le)
  have key := inversion_zero Γ K hK hcov B hc hsy hadd hn hker hinj μ 𝓕 hF h1
    (Φ := fun x => Φ (x - z)) (by fun_prop) hs' hI'
  simp only [he, zero_sub] at key
  exact key

end GlobalTheory.CovolumeOneSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualOfCovolumeOneStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_of_fundamentalDomain_volume_eq_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ B : G → G → ℂ, (∀ y, Continuous fun x => B x y) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y, ‖B x y‖ = 1) → (∀ x, (∀ γ ∈ Γ, B γ x = 1) ↔ x ∈ Γ) → (∀ γ ∈ Γ, (∀ x, B γ x = 1) → γ = 0) → ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual μ B := by
  first | exact @GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | exact GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one | (intros; apply GlobalTheory.CovolumeOneSelfDual.selfDual_of_covolume_one <;> assumption)
end
end
