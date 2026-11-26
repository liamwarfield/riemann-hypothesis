module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_rankOne_self : Continuous fun w : H => rankOne ℂ w w := by
  have h : (fun w : H => rankOne ℂ w w) =
      fun w => ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ w) w := by
    funext w
    ext z
    simp [rankOne_apply]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
    ((innerSL ℂ).continuous.prodMk continuous_id)

theorem isCompactOperator_rankOne_self (w : H) : IsCompactOperator (rankOne ℂ w w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)

theorem convex_compactOperators : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by
  exact ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex

variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}

theorem isCompactOperator_integral [IsProbabilityMeasure μ] {F : X → H →L[ℂ] H}
    (hFi : Integrable F μ) (hF : ∀ k, IsCompactOperator (F k)) :
    IsCompactOperator (∫ k, F k ∂μ : H →L[ℂ] H) := by
  have hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f} := isClosed_setOfPred_isCompactOperator
  have hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := convex_compactOperators
  have hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f} := Filter.Eventually.of_forall hF
  have hm := hc.integral_mem hs hae hFi
  exact hm

theorem inner_integral_rankOne {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  have hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ :=
    (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]
  simp only [rankOne_apply, inner_smul_right]

theorem isSymmetric_integral_rankOne {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x,
    ← integral_conj]
  congr 1
  funext k
  rw [map_mul, inner_conj_symm, inner_conj_symm, mul_comm]

theorem integral_rankOne_ne_zero {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by
  intro h0
  have h := inner_integral_rankOne hFi v v
  rw [h0, zero_apply, inner_zero_right] at h
  have h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext k
    rw [← inner_conj_symm (w k) v, Complex.conj_mul']
    push_cast
    rfl
  rw [h3] at h
  exact hpos.ne' (by exact_mod_cast h.symm)

end

theorem exists_finiteDimensional_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
      [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) →
      (∀ x, Continuous fun k => π k x) →
      ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  intro K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧
      μ.IsOpenPosMeasure := by
    refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hw : Continuous fun k => π k v := hcont v
  have hFc : Continuous fun k => rankOne ℂ (π k v) (π k v) := continuous_rankOne_self.comp hw
  have hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H) :=
    isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)
  have hTs := isSymmetric_integral_rankOne hFi
  have hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ := by
    have hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2 :=
      ((continuous_const.inner hw).norm).pow 2
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
    simp [hv]
  have hT0 := integral_rankOne_ne_zero hFi v hpos
  set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT
  obtain ⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)
  have hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y
  have hcomm : ∀ g x, T (π g x) = π g (T x) := by
    intro g x
    have hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ :=
      (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
    have hsh := integral_mul_left_eq_self (μ := μ)
      (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g
    rw [hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
      ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]
    congr 1
    funext k
    have hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y) := fun a b y => by rw [map_mul]; rfl
    simp only [rankOne_apply, hm, hinner, map_smul]
  refine ⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩
  intro k x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change T (π k x) = c • π k x
  change T x = c • x at hx
  rw [hcomm, hx, map_smul]

end GlobalTheory.CompactRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
namespace GlobalTheory.ExpPow

theorem int_eq_zero_of_exp_I_mul (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h1 : (m : ℝ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  by_contra hm
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact hm (by exact_mod_cast h1)
  apply irrational_pi
  refine ⟨(m : ℚ) / (2 * n), ?_⟩
  push_cast
  rw [h1]
  field_simp

theorem exp_I_pow_injective (a b : ℕ)
    (h : Complex.exp Complex.I ^ a = Complex.exp Complex.I ^ b) : a = b := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul] at h
  have h2 : Complex.exp (Complex.I * (((a : ℤ) - b : ℤ) : ℂ)) = 1 := by
    have : Complex.I * (((a : ℤ) - b : ℤ) : ℂ) = a * Complex.I - b * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_sub, h, div_self (Complex.exp_ne_zero _)]
  have := int_eq_zero_of_exp_I_mul _ h2
  omega

theorem pow_exp_I_or_inv_injective :
    ∀ (a b : ℕ) (w : ℂ), (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) →
      w ^ a = w ^ b → a = b := by
  rintro a b w (rfl | rfl) h
  · exact exp_I_pow_injective a b h
  · rw [inv_pow, inv_pow, inv_inj] at h
    exact exp_I_pow_injective a b h

end GlobalTheory.ExpPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
namespace GlobalTheory.SymRes

def FreePos (ρ κ i j : ℕ) : Prop :=
  (i < κ ∧ j < κ ∧ i < j) ∨ (κ ≤ i ∧ i < κ + ρ ∧ j < κ) ∨ (i < κ ∧ κ + ρ < j) ∨ (κ ≤ i ∧ i < j)

def IsPat {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) : Prop :=
  ∀ i j : Fin r, ¬ FreePos ρ κ i.val j.val → g.val i j = (1 : Matrix (Fin r) (Fin r) K) i j

theorem isPat_one {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) : IsPat ρ κ (1 : GL (Fin r) K) := fun _ _ _ => rfl

end GlobalTheory.SymRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompact
open MeasureTheory

namespace GlobalTheory.ChainOnto

theorem map_restrict_isHaar : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  intro G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK
  have hpm : Measurable p := hp.measurable
  have hAm : MeasurableSet (A : Set G) := hA.measurableSet
  have happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A) := by
    intro S hS
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]

  have hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1}) := by
    intro S
    ext g
    constructor
    · rintro ⟨hgS, hgA⟩
      refine ⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩
      · exact A.mul_mem (A.inv_mem (hiA _)) hgA
      · simp [hpi]
    · rintro ⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩
      refine ⟨?_, A.mul_mem (hiA s) hyA⟩
      simp [hpi, hy1, hs]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro C hC
    rw [happ C hC.isClosed.measurableSet, hpre C]
    exact ((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top
  · intro b
    ext S hS
    rw [Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]
    have : p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, A.mul_mem (hiA b) h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := A.mul_mem (A.inv_mem (hiA b)) h2
        simpa using this
    rw [this, measure_preimage_mul]
  · intro U hU hne
    rw [happ U hU.measurableSet]
    obtain ⟨u, hu⟩ := hne
    exact (hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompactStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_restrict_isHaar_of_open_product_compact : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  first | exact @GlobalTheory.ChainOnto.map_restrict_isHaar | exact GlobalTheory.ChainOnto.map_restrict_isHaar | (intros; apply GlobalTheory.ChainOnto.map_restrict_isHaar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
open scoped ComplexConjugate

namespace GlobalTheory

theorem hermitian_adjoint_exists_unique :
    ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
      (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ),
      (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) →
      ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  intro A C _ _ _ _ _ ipA ip _hsym hpos io u

  let g : C →ₗ[ℝ] (C →ₗ[ℂ] ℂ) :=
    { toFun := fun x => ip.flip x
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        ext y
        have h1 : (r • x : C) = (r : ℂ) • x := rfl
        have h2 : (r • ip.flip x : C →ₗ[ℂ] ℂ) y = (r : ℂ) * ip y x := by
          show ((r : ℂ) • ip.flip x) y = _
          simp
        simp only [RingHom.id_apply]
        rw [h2, h1, LinearMap.map_smulₛₗ]
        simp [Complex.conj_ofReal] }
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have h0 : ip x x = 0 := by
      have := LinearMap.congr_fun hx x
      simpa [g] using this
    have := hpos x hne
    rw [h0] at this
    simp at this
  have hrank : Module.finrank ℝ C = Module.finrank ℝ (C →ₗ[ℂ] ℂ) := by
    rw [finrank_real_of_complex, finrank_real_of_complex, Module.finrank_linearMap, Module.finrank_self, mul_one]
  have hs : Function.Surjective g := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hg
  obtain ⟨x, hx⟩ := hs ((ipA.flip u).comp io)
  refine ⟨x, fun y => ?_, fun x' hx' => ?_⟩
  · have := LinearMap.congr_fun hx y
    simpa [g] using this
  · apply hg
    ext y
    have hy := LinearMap.congr_fun hx y
    simp only [g, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.flip_apply] at hy ⊢
    rw [hx' y, hy]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDefStatement
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef : ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ), (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by
  first | exact @GlobalTheory.hermitian_adjoint_exists_unique | exact GlobalTheory.hermitian_adjoint_exists_unique | (intros; apply GlobalTheory.hermitian_adjoint_exists_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
namespace GlobalTheory

def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k

instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
noncomputable section

open Matrix ValuativeRel

namespace GlobalTheory.PenVol

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem toBlocks_mul_fin_zero (g h : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) :
    (g * h).toBlocks₁₁ = g.toBlocks₁₁ * h.toBlocks₁₁ := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem toBlocks_one_fin_zero : (1 : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

def cosStab (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    Subgroup (GL (n ⊕ Fin 0) k) where
  carrier := {g | g ∈ J ∧ ∀ y : n → k,
    (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨J.mul_mem hg hh, fun y => ?_⟩
    rw [show (g * h).val = g.val * h.val from rfl, toBlocks_mul_fin_zero, ← Matrix.mulVec_mulVec, hg', hh']
  one_mem' := ⟨J.one_mem, fun y => by
    rw [show (1 : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨J.inv_mem hg, fun y => ?_⟩
    have e : g.val.toBlocks₁₁ *ᵥ ((g⁻¹ : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← toBlocks_mul_fin_zero, show g.val * (g⁻¹ : GL (n ⊕ Fin 0) k).val = 1 from g.mul_inv,
        toBlocks_one_fin_zero, Matrix.one_mulVec]
    rw [← hg', e]

theorem mem_cosStab {J : Subgroup (GL (n ⊕ Fin 0) k)} {M : Submodule 𝒪[k] (n → k)} {c : (n → k) ⧸ M}
    {g : GL (n ⊕ Fin 0) k} : g ∈ cosStab J M c ↔ g ∈ J ∧ ∀ y : n → k,
      (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) : (n → k) ⧸ M) = c ↔ Submodule.Quotient.mk y = c := Iff.rfl

theorem cosStab_le (J : Subgroup (GL (n ⊕ Fin 0) k)) (M : Submodule 𝒪[k] (n → k)) (c : (n → k) ⧸ M) :
    cosStab J M c ≤ J := fun _ h => h.1

end GlobalTheory.PenVol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.ChainOnto

theorem exists_orthonormal_expansion_of_sesq {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by
  let cd : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip y x
      conj_inner_symm := fun x y => by simp [hsym y x]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        change ip x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup C := @InnerProductSpace.Core.toNormedAddCommGroup ℂ C _ _ _ cd
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ C
  refine ⟨_, b, fun i j => ?_, fun x => ?_⟩
  · have h := orthonormal_iff_ite.mp b.orthonormal j i
    have e : ⟪b j, b i⟫_ℂ = ip (b i) (b j) := rfl
    rw [e] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have h := b.sum_repr' x
    exact h.symm

theorem value_of_adjoint_of_mem_span : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  intro X W C _ _ _ _ _ ev K ipD ip pet hD hDpos hsym hpos hpet x F l hF hl hF0
  obtain ⟨n, b, hb, hexp⟩ := exists_orthonormal_expansion_of_sesq ip hsym hpos
  let Φ : (Fin n → W) →ₗ[ℂ] (X → ℂ) := ∑ j, (ev (b j)).comp (LinearMap.proj j)
  have hΦ : ∀ u, Φ u = ∑ j, ev (b j) (u j) := by
    intro u; simp [Φ, LinearMap.sum_apply]
  have hspan : Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} ≤
      (Submodule.pi Set.univ (fun _ : Fin n => K)).map Φ := by
    rw [Submodule.span_le]
    rintro G ⟨y, w, hw, rfl⟩
    refine ⟨fun j => ip y (b j) • w, fun j _ => K.smul_mem _ hw, ?_⟩
    rw [hΦ]
    conv_rhs => rw [hexp y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_smul, LinearMap.smul_apply]
  obtain ⟨u, hu, hFu⟩ := hspan hF
  have huK : ∀ j, u j ∈ K := fun j => hu j (Set.mem_univ j)
  rw [hΦ] at hFu
  have key : ∀ k, ∀ w ∈ K, ipD w (u k) = ip (b k) x * l w := by
    intro k w hw
    have h1 := hl (b k) w hw
    rw [← hFu, hpet] at h1
    simpa only [hb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h1
  have hex : ∃ k, u k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF0
    rw [← hFu]
    simp [h]
  obtain ⟨k, hk⟩ := hex
  have hkpos := hDpos (u k) hk
  rw [key k (u k) (huK k)] at hkpos
  have ha : ip (b k) x ≠ 0 := by
    intro h; rw [h, zero_mul] at hkpos; simp at hkpos
  have hx : x ≠ 0 := by
    rintro rfl; exact ha (by simp)
  refine ⟨hx, ?_⟩
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = (conj (ip (b k) x))⁻¹ • u k := ⟨_, rfl⟩
  have hw₀K : w₀ ∈ K := hw₀def ▸ K.smul_mem _ (huK k)
  have hw₀ : ∀ w ∈ K, ipD w w₀ = l w := by
    intro w hw
    rw [hw₀def, LinearMap.map_smulₛₗ, key k w hw, map_inv₀, Complex.conj_conj, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hu_eq : ∀ j, u j = conj (ip (b j) x) • w₀ := by
    intro j
    have hdK : u j - conj (ip (b j) x) • w₀ ∈ K := K.sub_mem (huK j) (K.smul_mem _ hw₀K)
    have hd0 : ∀ w ∈ K, ipD w (u j - conj (ip (b j) x) • w₀) = 0 := by
      intro w hw
      rw [map_sub, LinearMap.map_smulₛₗ, key j w hw, hw₀ w hw, Complex.conj_conj, smul_eq_mul, sub_self]
    by_contra hne
    have := hDpos _ (sub_ne_zero.mpr hne)
    rw [hd0 _ hdK] at this
    simp at this
  refine ⟨w₀, hw₀K, ?_⟩
  rw [← hFu]
  have hsum : ∑ j, ev (b j) (u j) = ∑ j, ev (b j) (conj (ip (b j) x) • w₀) :=
    Finset.sum_congr rfl (fun j _ => by rw [hu_eq j])
  rw [hsum]
  conv_rhs => rw [hexp x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [map_smul, LinearMap.smul_apply]
  rw [hsym x (b j)]

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValuesStatement
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_adjoint_of_mem_span_evaluation_values : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  first | exact @GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | exact GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span | (intros; apply GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexComapEqOfCosetsHit
namespace GlobalTheory.IndexComapCosets

theorem index_comap_eq_of_cosets_hit {A B : Type} [Group A] [Group B] (f : A →* B)
    (H : Subgroup B) (h : ∀ b : B, ∃ a : A, (f a)⁻¹ * b ∈ H) :
    (H.comap f).index = H.index := by
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  let φ : A ⧸ H.comap f → B ⧸ H :=
    Quotient.map' f (fun a a' hr => by
      rw [QuotientGroup.leftRel_apply] at hr ⊢
      simpa using hr)
  have hφ : ∀ a : A, φ (a : A ⧸ H.comap f) = (f a : B ⧸ H) := fun a => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    rw [hφ, hφ, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]
    exact hxy
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, by rw [hφ, QuotientGroup.eq]; exact ha⟩
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)

end GlobalTheory.IndexComapCosets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixExpSmulMulEqMulExpSmulOfIntertwine
open Matrix

namespace GlobalTheory

theorem matrix_pow_mul_eq_mul_pow_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem matrix_hasSum_exp {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) (NormedSpace.exp X) := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

theorem matrix_exp_mul_eq_mul_exp_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by
  let g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)
  have hg : Continuous g := Continuous.matrix_mul continuous_id continuous_const
  let g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)
  have hg' : Continuous g' := Continuous.matrix_mul continuous_const continuous_id
  have hL := (matrix_hasSum_exp X).map g hg
  have hR := (matrix_hasSum_exp β).map g' hg'
  have key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) =
      (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n) := by
    funext n
    simp only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul,
      matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]
  rw [key] at hL
  exact hL.unique hR

theorem matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine :
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by
  intro m r X ε β h s
  apply matrix_exp_mul_eq_mul_exp_of_intertwine
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory

theorem adicCompletion_valuation_map_uniformiser : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  intro F _ _ v k _ _ _ _ φ hφ ϖ hϖ

  have hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c := by
    intro c hc hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : φ (c : k) * φ (w : k) = 1 := by
      rw [← map_mul, ← map_one φ]
      congr 1
      exact_mod_cast congrArg (fun t : 𝒪[k] => (t : k)) hw
    have h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1 := by
      rw [← map_mul, hw', map_one]
    have h2 : Valued.v (φ (w : k)) ≤ 1 := (hφ _).2 w.2
    have h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1 :=
      by gcongr
    rw [h1, mul_one] at h3
    exact absurd hc (not_lt.2 h3)
  set x := φ (ϖ : k) with hxdef
  have hϖ0 : (ϖ : k) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    simpa [hxdef] using hϖ0
  have hvx0 : Valued.v x ≠ 0 := by
    simpa using hx0
  have hvx1 : Valued.v x < 1 := by
    have hle : Valued.v x ≤ 1 := (hφ _).2 ϖ.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hϖ.not_isUnit
    have hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k] := by
      refine (hφ _).1 ?_
      rw [map_inv₀, map_inv₀, ← hxdef, heq, inv_one]
    refine IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_
    apply Subtype.ext
    simp [mul_inv_cancel₀ hϖ0]
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  have hvπ0 : Valued.v π₀ ≠ 0 := by rw [hπ₀]; exact WithZero.coe_ne_zero
  have hπ0 : π₀ ≠ 0 := by
    intro h; apply hvπ0; rw [h, map_zero]
  set a := φ.symm π₀ with hadef
  have hφa : φ a = π₀ := by simp [hadef]
  have ha0 : a ≠ 0 := by
    intro h; apply hπ0; rw [← hφa, h, map_zero]
  have ha : a ∈ 𝒪[k] := (hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)
  apply le_antisymm
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 hvx0
    rw [← hm] at hvx1 ⊢
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hvx1
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := hvx1
    show Multiplicative.toAdd m ≤ -1
    omega
  · by_contra hcon
    rw [not_le] at hcon
    set b := (ϖ : k) / a with hbdef
    have hφb : Valued.v (φ b) < 1 := by
      rw [hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]
      exact hcon
    have hb : b ∈ 𝒪[k] := (hφ b).1 hφb.le
    have hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩ := by
      apply Subtype.ext
      show (ϖ : k) = a * ((ϖ : k) / a)
      rw [mul_div_cancel₀ _ ha0]
    rcases hϖ.isUnit_or_isUnit hprod with h | h
    · exact hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h
    · exact hnu ⟨b, hb⟩ hφb h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiserStatement
open ValuativeRel NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_v_map_irreducible_eq_ofAdd_neg_one : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  first | exact @GlobalTheory.adicCompletion_valuation_map_uniformiser | exact GlobalTheory.adicCompletion_valuation_map_uniformiser | (intros; apply GlobalTheory.adicCompletion_valuation_map_uniformiser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBound
open Matrix Filter Topology

namespace GlobalTheory.UnitaryLog

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma linftyOp_norm_le_mul_of_entry_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ δ) : ‖A‖ ≤ n * δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : A = 0 := Subsingleton.elim _ _
    simp [this]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (h ⟨0, hn⟩ ⟨0, hn⟩)
  lift δ to NNReal using hδ
  rw [linfty_opNorm_def]
  have key : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ n • δ := by
    refine Finset.sup_le fun i _ => ?_
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => ‖A i j‖₊) δ
      (fun j _ => by exact_mod_cast h i j)
    simpa using this
  have := (NNReal.coe_le_coe.2 key)
  simpa [nsmul_eq_mul] using this

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private lemma norm_entry_le_linftyOp_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ ‖A‖ := by
  rw [linfty_opNorm_def]
  calc ‖A i j‖ = ((‖A i j‖₊ : NNReal) : ℝ) := rfl
    _ ≤ ((∑ k, ‖A i k‖₊ : NNReal) : ℝ) := by
      exact_mod_cast Finset.single_le_sum (f := fun k => ‖A i k‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := by
      exact_mod_cast Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem _root_.GlobalTheory.UnitaryLog.exists_log_unitary (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G.det) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ →
      (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧
        NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 :=
    hasStrictFDerivAt_exp_zero
  set L := hf.localInverse _ _ _ with hL
  set φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => G⁻¹ * Xᴴ * G with hφ
  have hφc : Continuous φ :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  have hφ0 : Tendsto φ (𝓝 0) (𝓝 0) := by
    simpa [φ] using hφc.tendsto 0
  have hleft : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X :=
    hf.eventually_left_inverse
  have hP : ∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X ∧
      L (NormedSpace.exp (φ X)) = φ X ∧ L (NormedSpace.exp (-X)) = -X :=
    hleft.and ((hφ0.eventually hleft).and
      ((continuous_neg.tendsto' (0 : Matrix (Fin n) (Fin n) ℂ) 0 neg_zero).eventually hleft))
  obtain ⟨K, s, hs, hK⟩ := hf.to_localInverse.exists_lipschitzOnWith
  have hQ := hf.eventually_right_inverse.and ((hf.localInverse_tendsto.eventually hP).and hs)
  have hL1 : L (NormedSpace.exp 0) = 0 := hf.localInverse_apply_image
  have hs1 : NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) ∈ s := mem_of_mem_nhds hs
  rw [NormedSpace.exp_zero] at hQ hL1 hs1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hQ
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  refine ⟨ε / (2 * ((n : ℝ) + 1)), K * n, by positivity, ?_⟩
  intro u δ hu hδ hentry
  have hnorm : ‖u - 1‖ ≤ n * δ := linftyOp_norm_le_mul_of_entry_le _ δ hentry
  have hsmall : (n : ℝ) * (ε / (2 * ((n : ℝ) + 1))) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith
  have hdist : dist u 1 < ε := by
    rw [dist_eq_norm]
    calc ‖u - 1‖ ≤ n * δ := hnorm
      _ ≤ n * (ε / (2 * ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg n)
      _ < ε := hsmall
  obtain ⟨hexp, ⟨hX, hXφ, hXneg⟩, hus⟩ := hball hdist
  refine ⟨L u, ?_, hexp, ?_⟩
  · have hGu : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hG
    have hinv : u⁻¹ = G⁻¹ * uᴴ * G := by
      apply Matrix.inv_eq_left_inv
      have hu' := hu
      simp only [Matrix.mul_assoc] at hu' ⊢
      rw [hu', Matrix.nonsing_inv_mul G hG]
    have hexpφ : NormedSpace.exp (φ (L u)) = NormedSpace.exp (-L u) := by
      rw [Matrix.exp_neg, hexp, hinv]
      simp only [φ]
      rw [Matrix.exp_conj' G _ hGu, Matrix.exp_conjTranspose, hexp]
    have heq : φ (L u) = -L u := by
      rw [← hXφ, ← hXneg, hexpφ]
    calc (L u)ᴴ * G + G * L u = G * φ (L u) + G * L u := by
          simp only [φ]
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
            Matrix.one_mul]
      _ = 0 := by rw [heq, Matrix.mul_neg, neg_add_cancel]
  · intro i j
    calc ‖L u i j‖ ≤ ‖L u‖ := norm_entry_le_linftyOp_norm _ i j
      _ = dist (L u) (L 1) := by rw [hL1, dist_zero_right]
      _ ≤ K * dist u 1 := hK.dist_le_mul u hus 1 hs1
      _ ≤ K * (n * δ) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
      _ = K * n * δ := by ring

end GlobalTheory.UnitaryLog
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), IsUnit G.det → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ → (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  first | exact @GlobalTheory.UnitaryLog.exists_log_unitary | exact GlobalTheory.UnitaryLog.exists_log_unitary | (intros; apply GlobalTheory.UnitaryLog.exists_log_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanMultilinearValues
namespace GlobalTheory

theorem finiteDimensional_span_multilinear_values :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : (∀ i, E i) →ₘₗ[ℂ] F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  have := hW
  let T' : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  have hset : {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v} = Set.range T' := by
    ext f
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨fun i => ⟨v i, hv i⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨fun i => (w i : E i), fun i => (w i).2, rfl⟩
  have hle : Submodule.span ℂ (Set.range T') ≤ LinearMap.range (PiTensorProduct.lift T') := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ w, by simp⟩
  rw [hset]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory
end
