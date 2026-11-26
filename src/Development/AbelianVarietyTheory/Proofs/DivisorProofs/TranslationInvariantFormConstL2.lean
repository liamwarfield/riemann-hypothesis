module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantSchwartzUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZero
namespace GlobalTheory.CharInvAtZero

theorem eq_of_eq_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  intro Y _ _ _ ℓ hinv f g h0
  refine GlobalTheory.SchwartzHadamard.eq_of_eqOn (⊥ : Submodule ℝ Y) ℓ (fun L _ => hinv L) f g ?_
  intro p hp
  rw [Submodule.mem_bot] at hp
  subst hp
  exact h0

end GlobalTheory.CharInvAtZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_depends_on_value_at_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  first | exact @GlobalTheory.CharInvAtZero.eq_of_eq_zero | exact GlobalTheory.CharInvAtZero.eq_of_eq_zero | (intros; apply GlobalTheory.CharInvAtZero.eq_of_eq_zero <;> assumption)
end
end

open scoped FourierTransform SchwartzMap InnerProductSpace
open MeasureTheory

namespace GlobalTheory.TransInvSchwartz

theorem fourier_compSubConst {n : ℕ} (h : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (w ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ w h) ξ = GlobalTheory.ArchSch.ech ⟪w, ξ⟫_ℝ * 𝓕 h ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  simp only [SchwartzMap.compSubConstCLM_apply, smul_eq_mul]
  rw [← integral_add_right_eq_self (fun v => Complex.exp (↑(-2 * Real.pi * ⟪v, ξ⟫_ℝ) * Complex.I) * h (v - w)) w]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [add_sub_cancel_right, GlobalTheory.ArchSch.ech, inner_add_left]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem eq_of_fourier_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hμ : ∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f)
    (f g : SchwartzMap V ℂ)
    (hfg : 𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm f) 0 =
      𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm g) 0) :
    μ f = μ g := by
  set T := toEuclidean (E := V)
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm with hC
  let Ci := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  have hCi : ∀ h, Ci (C h) = h := fun h => by ext x; simp [Ci, C]
  let Fe := FourierTransform.fourierCLE ℂ 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ)
  have hFe : ∀ h, Fe h = 𝓕 h := fun h => rfl
  let ℓ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] ℂ :=
    μ.comp (Ci.comp (Fe.symm : _ →L[ℂ] _))
  have hℓ : ∀ h, ℓ (𝓕 (C h)) = μ h := fun h => by
    show μ (Ci (Fe.symm (Fe (C h)))) = μ h
    rw [ContinuousLinearEquiv.symm_apply_apply, hCi]
  have hinv : ∀ L : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ] ℝ, ∀ F G : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ),
      ⇑G = (fun x => GlobalTheory.ArchSch.ech (L x) * F x) → ℓ G = ℓ F := by
    intro L F G hG
    set w := (InnerProductSpace.toDual ℝ _).symm (LinearMap.toContinuousLinearMap L)
    have hw : ∀ x, L x = ⟪w, x⟫_ℝ := fun x => by
      rw [InnerProductSpace.toDual_symm_apply]; rfl
    set h := Fe.symm F
    have hF : 𝓕 h = F := Fe.apply_symm_apply F
    have hG' : Fe (SchwartzMap.compSubConstCLM ℂ w h) = G := by
      ext ξ
      rw [hFe, fourier_compSubConst, hG, ← hF]
      simp only [hw]
    show μ (Ci (Fe.symm G)) = μ (Ci (Fe.symm F))
    rw [← hG', ContinuousLinearEquiv.symm_apply_apply]
    apply hμ (-T.symm w)
    ext x
    simp only [Ci, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
    rw [SchwartzMap.compSubConstCLM_apply, map_add (f := _), map_neg, ContinuousLinearEquiv.apply_symm_apply, sub_eq_add_neg]
  have := GlobalTheory.T.schwartz_functional_depends_on_value_at_zero ℓ hinv (𝓕 (C f)) (𝓕 (C g)) hfg
  rwa [hℓ, hℓ] at this

theorem dim_le_one : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ μ' : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ g = μ f) →
    (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → μ' g = μ' f) →
    μ ≠ 0 → ∃ c : ℂ, μ' = c • μ := by
  intro V _ _ _ μ μ' hμ hμ' h0
  set C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) (toEuclidean (E := V)).symm with hC
  let Fe := FourierTransform.fourierCLE ℂ 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ)
  let Φ : SchwartzMap V ℂ → ℂ := fun f => Fe (C f) 0
  have hΦs : ∀ (c : ℂ) f, Φ (c • f) = c * Φ f := fun c f => by
    show Fe (C (c • f)) 0 = c * Fe (C f) 0
    rw [map_smul, map_smul]; rfl
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, μ f₀ ≠ 0 := by
    by_contra hc; push_neg at hc; exact h0 (ContinuousLinearMap.ext hc)
  have hΦ0 : Φ f₀ ≠ 0 := by
    intro hz
    apply hf₀
    rw [eq_of_fourier_zero μ hμ f₀ 0 (by
      show Φ f₀ = Fe (C 0) 0
      rw [hz]; simp), map_zero]
  have hrep : ∀ ν : SchwartzMap V ℂ →L[ℂ] ℂ,
      (∀ (a : V) (f g : SchwartzMap V ℂ), ⇑g = (fun x => f (x + a)) → ν g = ν f) →
      ∀ f, ν f = (Φ f / Φ f₀) * ν f₀ := fun ν hν f => by
    rw [eq_of_fourier_zero ν hν f ((Φ f / Φ f₀) • f₀) (by
      show Φ f = Φ ((Φ f / Φ f₀) • f₀)
      rw [hΦs, div_mul_cancel₀ _ hΦ0]), map_smul, smul_eq_mul]
  refine ⟨μ' f₀ / μ f₀, ContinuousLinearMap.ext fun f => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hrep μ' hμ' f, hrep μ hμ f, smul_eq_mul]
  field_simp

end GlobalTheory.TransInvSchwartz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDense
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDense
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDenseStatement
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_compact_support_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  first | exact @GlobalTheory.schwartz_mem_closure_hasCompactSupport | exact GlobalTheory.schwartz_mem_closure_hasCompactSupport | (intros; apply GlobalTheory.schwartz_mem_closure_hasCompactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCompactPartitionUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCompactPartitionUnity
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

noncomputable section

namespace GlobalTheory.LatticePartition

def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem bump_contDiff : ContDiff ℝ ∞ bump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem bump_eq_zero {t : ℝ} (h : 1 ≤ |t|) : bump t = 0 := by
  unfold bump
  rcases le_abs'.1 h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le h]
    simp

theorem bump_local (y : ℝ) (k : ℤ) (hk : k ∉ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ)) :
    bump (y - k) = 0 := by
  apply bump_eq_zero
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have : k ≤ ⌊y⌋ - 2 ∨ ⌊y⌋ + 2 ≤ k := by omega
  rcases this with h | h
  · have h' : (k : ℝ) ≤ (⌊y⌋ : ℝ) - 2 := by exact_mod_cast h
    rw [le_abs']; right; linarith
  · have h' : (⌊y⌋ : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast h
    rw [le_abs']; left; linarith

theorem bump_sum (y : ℝ) : ∑ k ∈ ({⌊y⌋ - 1, ⌊y⌋, ⌊y⌋ + 1} : Finset ℤ), bump (y - k) = 1 := by
  rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), Finset.sum_singleton]
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  have e1 : y - ((⌊y⌋ - 1 : ℤ) : ℝ) = y - (⌊y⌋ : ℝ) + 1 := by push_cast; ring
  have e2 : y - ((⌊y⌋ + 1 : ℤ) : ℝ) + 1 = y - (⌊y⌋ : ℝ) := by push_cast; ring
  have ha : Real.smoothTransition (y - (⌊y⌋ : ℝ) + 1 + 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hb : Real.smoothTransition (y - ((⌊y⌋ + 1 : ℤ) : ℝ)) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by push_cast; linarith)
  unfold bump
  rw [e1, e2, ha, hb]
  ring

theorem summable_lattice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}

def bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) : ℝ := ∏ i, bump (e x i)

def latPt (e : V ≃L[ℝ] (Fin n → ℝ)) (j : Fin n → ℤ) : V := e.symm (fun i => (j i : ℝ))

theorem bumpProd_contDiff (e : V ≃L[ℝ] (Fin n → ℝ)) : ContDiff ℝ ∞ (bumpProd e) := by
  unfold bumpProd
  refine contDiff_prod fun i _ => bump_contDiff.comp ?_
  exact (contDiff_apply ℝ (fun _ => ℝ) i).comp e.contDiff

theorem bumpProd_compact (e : V ≃L[ℝ] (Fin n → ℝ)) : HasCompactSupport (bumpProd e) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine HasCompactSupport.intro (hK.image e.symm.continuous) ?_
  intro x hx
  have : ∃ i, 1 ≤ |e x i| := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hx ⟨e x, Set.mem_univ_pi.2 fun i => ⟨(abs_lt.1 (h i)).1.le, (abs_lt.1 (h i)).2.le⟩,
      e.symm_apply_apply x⟩
  obtain ⟨i, hi⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_eq_zero hi)

theorem bumpProd_sub (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) (j : Fin n → ℤ) :
    bumpProd e (x - latPt e j) = ∏ i, bump (e x i - j i) := by
  simp [bumpProd, latPt, map_sub]

theorem hasSum_bumpProd (e : V ≃L[ℝ] (Fin n → ℝ)) (x : V) :
    HasSum (fun j : Fin n → ℤ => bumpProd e (x - latPt e j)) 1 := by
  simp only [bumpProd_sub]
  generalize e x = y
  have hsum : ∑ j ∈ Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ)),
      ∏ i, bump (y i - j i) = 1 := by
    rw [← Finset.prod_univ_sum (t := fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))
      (f := fun i k => bump (y i - k))]
    exact Finset.prod_eq_one fun i _ => bump_sum (y i)
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional _)
    (f := fun j : Fin n → ℤ => ∏ i, bump (y i - j i))
    (s := Fintype.piFinset (fun i => ({⌊y i⌋ - 1, ⌊y i⌋, ⌊y i⌋ + 1} : Finset ℤ))) (by
      intro j hj
      rw [Fintype.mem_piFinset, not_forall] at hj
      obtain ⟨i, hi⟩ := hj
      exact Finset.prod_eq_zero (Finset.mem_univ i) (bump_local _ _ hi))
  rwa [hsum] at h

theorem summable_latPt [FiniteDimensional ℝ V] (b : Module.Basis (Fin n) ℝ V) :
    ∃ M : ℕ, Summable (fun j : Fin n → ℤ => ((1 + ‖latPt b.equivFunL j‖) ^ M)⁻¹) := by
  have hmem : ∀ j, latPt b.equivFunL j ∈ Submodule.span ℤ (Set.range b) := fun j => by
    have : latPt b.equivFunL j = ∑ i, (j i : ℝ) • b i := b.equivFun_symm_apply _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hinj : Function.Injective fun j : Fin n → ℤ =>
      (⟨latPt b.equivFunL j, hmem j⟩ : Submodule.span ℤ (Set.range b)) := by
    intro j k hjk
    have h1 : latPt b.equivFunL j = latPt b.equivFunL k := congrArg Subtype.val hjk
    have h2 : (fun i => (j i : ℝ)) = fun i => (k i : ℝ) := b.equivFunL.symm.injective h1
    funext i
    exact_mod_cast congrFun h2 i
  have h := (summable_lattice (Submodule.span ℤ (Set.range b))).comp_injective hinj
  refine ⟨Module.finrank ℤ (Submodule.span ℤ (Set.range b)) + 1, h.congr fun j => ?_⟩
  simp only [Function.comp_apply, Submodule.coe_norm]

theorem finite_of_summable {ι : Type} (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (M : ℕ)
    (hS : Summable (fun j => ((1 + a j) ^ M)⁻¹)) (R : ℝ) : {j | a j ≤ R}.Finite := by
  have ht := hS.tendsto_cofinite_zero
  have hR : (0 : ℝ) ≤ max R 0 := le_max_right _ _
  have hε : (0 : ℝ) < ((1 + max R 0) ^ M)⁻¹ := by positivity
  have h3 := ht (Iio_mem_nhds hε)
  rw [Filter.mem_map, Filter.mem_cofinite] at h3
  refine h3.subset fun j hj => ?_
  simp only [Set.mem_setOf_eq] at hj
  simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iio, not_lt]
  have hj' : a j ≤ max R 0 := le_trans hj (le_max_left _ _)
  have h0 := ha j
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) _)

end

theorem exists_lattice_partition :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  intro V _ _ _
  obtain ⟨M, hS⟩ := summable_latPt (Module.finBasis ℝ V)
  generalize (Module.finBasis ℝ V).equivFunL = e at hS
  have hc : HasCompactSupport (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    (bumpProd_compact e).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ (fun x => ((bumpProd e x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpProd_contDiff e)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : SchwartzMap V ℂ, (ψ : V → ℂ) = fun x => ((bumpProd e x : ℝ) : ℂ) :=
    ⟨hc.toSchwartzMap hd, rfl⟩
  refine ⟨ψ, hψ ▸ hc, ?_, latPt e, ?_, ?_, M, hS⟩
  · intro x
    rw [hψ]
    exact Complex.conj_ofReal _
  · intro x
    rw [hψ]
    have h := Complex.hasSum_ofReal.2 (hasSum_bumpProd e x)
    rwa [Complex.ofReal_one] at h
  · exact finite_of_summable (fun j => ‖latPt e j‖) (fun _ => norm_nonneg _) M hS

end GlobalTheory.LatticePartition
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCompactPartitionUnityStatement
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_compact_partition_unity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by
  first | exact @GlobalTheory.LatticePartition.exists_lattice_partition | exact GlobalTheory.LatticePartition.exists_lattice_partition | (intros; apply GlobalTheory.LatticePartition.exists_lattice_partition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperator
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory.TransDecay

theorem seminorm_mul_shift_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ h : 𝓢(V, ℂ)) (hχ : HasCompactSupport (χ : V → ℂ)) (l m M : ℕ) :
    ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ l m k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  obtain ⟨r, hr⟩ := hχ.isCompact.isBounded.subset_closedBall (0 : V)
  set R := max r 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ tsupport (χ : V → ℂ), ‖x‖ ≤ R := fun x hx => by
    have := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set S := ((Finset.Iic (M, m)).sup fun p : ℕ × ℕ => SchwartzMap.seminorm ℂ p.1 p.2) h
  have hS0 : 0 ≤ S := apply_nonneg _ _
  set A := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)), fun v k' hk' => ?_⟩
  have hvpos : 0 < (1 + ‖v‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ l m k' (by positivity) fun x => ?_
  have hfun : (k' : V → ℂ) = fun y => χ y * h (y + v) := funext hk'
  rw [hfun]
  have hsh : ContDiff ℝ (⊤ : ℕ∞) (fun y => h (y + v)) :=
    (h.smooth ⊤).comp (contDiff_id.add contDiff_const)
  have hL := norm_iteratedFDeriv_mul_le (χ.smooth ⊤) hsh x (n := m) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
      ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) ≤
      R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) * ((1 + R) ^ M * (2 ^ M * S)) *
        ((1 + ‖v‖) ^ M)⁻¹ := by
    intro i _
    by_cases hx : x ∈ tsupport (χ : V → ℂ)
    · have hx1 := hxR x hx
      rw [iteratedFDeriv_comp_add_right]
      have hj : (1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤ 2 ^ M * S :=
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (M, m)) le_rfl (Nat.sub_le _ _) h (x + v)
      have hv : 1 + ‖v‖ ≤ (1 + R) * (1 + ‖x + v‖) := by
        have : ‖v‖ ≤ ‖x + v‖ + ‖x‖ := by
          calc ‖v‖ = ‖(x + v) - x‖ := by simp
            _ ≤ _ := norm_sub_le _ _
        nlinarith [norm_nonneg (x + v)]
      have hD : ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ ≤
          (1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hvpos]
        calc ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * (1 + ‖v‖) ^ M
            ≤ ‖iteratedFDeriv ℝ (m - i) h (x + v)‖ * ((1 + R) * (1 + ‖x + v‖)) ^ M := by gcongr
          _ = (1 + R) ^ M * ((1 + ‖x + v‖) ^ M * ‖iteratedFDeriv ℝ (m - i) h (x + v)‖) := by
            rw [mul_pow]; ring
          _ ≤ (1 + R) ^ M * (2 ^ M * S) := by gcongr
      have hχi : ‖iteratedFDeriv ℝ i χ x‖ ≤ SchwartzMap.seminorm ℂ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ χ i x
      calc ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
            ‖iteratedFDeriv ℝ (m - i) h (x + v)‖)
          ≤ R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ *
            ((1 + R) ^ M * (2 ^ M * S) * ((1 + ‖v‖) ^ M)⁻¹)) := by gcongr
        _ = _ := by ring
    · have h0 : iteratedFDeriv ℝ i χ x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset i (Function.mem_support.2 hne))
      rw [h0, norm_zero, mul_zero, zero_mul, mul_zero]
      positivity
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => χ y * h (y + v)) x‖
      ≤ ‖x‖ ^ l * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (m + 1), ‖x‖ ^ l * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
          ‖iteratedFDeriv ℝ (m - i) (fun y => h (y + v)) x‖) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), R ^ l * ((m.choose i : ℝ) * SchwartzMap.seminorm ℂ 0 i χ) *
          ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := Finset.sum_le_sum hterm
    _ = R ^ l * A * ((1 + R) ^ M * (2 ^ M * S)) * ((1 + ‖v‖) ^ M)⁻¹ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]

theorem decay : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  intro V _ _ _ _ _ μ _ T hinv χ ψ h hχ M
  have hp : Continuous ((SchwartzMap.seminorm ℂ 0 0 : Seminorm ℂ 𝓢(V, ℂ)).comp
      (T : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))) :=
    ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (0, 0)).comp T.continuous
  obtain ⟨s, C0, -, hC0⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ) _ hp
  have hA : ∀ i : ℕ × ℕ, ∃ C : ℝ, ∀ (v : V) (k' : 𝓢(V, ℂ)), (∀ x, k' x = χ x * h (x + v)) →
      SchwartzMap.seminorm ℂ i.1 i.2 k' ≤ C * ((1 + ‖v‖) ^ M)⁻¹ :=
    fun i => seminorm_mul_shift_le χ h hχ i.1 i.2 M
  choose Cf hCf using hA
  set Cs := ∑ i ∈ s, |Cf i|
  have hCs : 0 ≤ Cs := Finset.sum_nonneg fun i _ => abs_nonneg _
  set I := ∫ x, ‖T ψ x‖ ∂μ
  have hint : Integrable (fun x => ‖T ψ x‖) μ := (SchwartzMap.integrable (T ψ)).norm
  refine ⟨(C0 : ℝ) * Cs * I, fun v k ψv hk hψv => ?_⟩
  set k' := SchwartzMap.compSubConstCLM ℂ (-v) k
  have hk' : ∀ x, k' x = k (x + v) := by
    intro x; simp [k', SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have hk'' : ∀ x, k' x = χ x * h (x + v) := by intro x; rw [hk', hk]; simp
  have hψ : ∀ x, ψ x = ψv (x + v) := by intro x; rw [hψv]; simp
  rw [← hinv v k k' ψv ψ hk' hψ]
  have hsup : (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    calc schwartzSeminormFamily ℂ V ℂ i k' ≤ Cf i * ((1 + ‖v‖) ^ M)⁻¹ := hCf i v k' hk''
      _ ≤ |Cf i| * ((1 + ‖v‖) ^ M)⁻¹ := by gcongr; exact le_abs_self _
      _ ≤ Cs * ((1 + ‖v‖) ^ M)⁻¹ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => |Cf i|) (fun i _ => abs_nonneg _) hi
  have hTk : ∀ x, ‖T k' x‖ ≤ (C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹) := by
    intro x
    have h2 := hC0 k'
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul] at h2
    calc ‖T k' x‖ ≤ SchwartzMap.seminorm ℂ 0 0 (T k') := SchwartzMap.norm_le_seminorm ℂ _ x
      _ ≤ (C0 : ℝ) * (s.sup (schwartzSeminormFamily ℂ V ℂ)) k' := h2
      _ ≤ _ := by gcongr
  calc ‖∫ x, T k' x * starRingEnd ℂ (T ψ x) ∂μ‖
      ≤ ∫ x, ((C0 : ℝ) * (Cs * ((1 + ‖v‖) ^ M)⁻¹)) * ‖T ψ x‖ ∂μ := by
        refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        rw [norm_mul, RCLike.norm_conj]
        gcongr
        exact hTk x
    _ = (C0 : ℝ) * Cs * I * ((1 + ‖v‖) ^ M)⁻¹ := by rw [integral_const_mul]; ring

end GlobalTheory.TransDecay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperatorStatement
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_isometry_schwartz_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.TransDecay.decay | exact GlobalTheory.TransDecay.decay | (intros; apply GlobalTheory.TransDecay.decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctional
open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_pairing_conj_clm_of_borelSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ) :
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ,
      L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  let kc : 𝓢(V, ℂ) := SchwartzMap.postcompCLM (𝕜 := ℝ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) k
  have hkc : ∀ x, kc x = starRingEnd ℂ (k x) := fun x => rfl
  have hg : Function.HasTemperateGrowth (fun x => starRingEnd ℂ (k x)) := by
    have := kc.hasTemperateGrowth
    simpa [funext hkc] using this
  refine ⟨(SchwartzMap.integralCLM ℂ μ).comp
    (SchwartzMap.smulLeftCLM ℂ (fun x => starRingEnd ℂ (k x))), fun u => ?_⟩
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply hg]
  congr 1
  funext x
  simp [smul_eq_mul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctionalStatement
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_pairing_continuous_functional : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (k : SchwartzMap V ℂ),
    ∃ L : SchwartzMap V ℂ →L[ℂ] ℂ, ∀ u : SchwartzMap V ℂ, L u = ∫ x, u x * starRingEnd ℂ (k x) ∂μ := by
  first | exact @GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | exact GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace | (intros; apply GlobalTheory.schwartz_pairing_conj_clm_of_borelSpace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2
open MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def conjS (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjS_apply (f : 𝓢(V, ℂ)) (x : V) : conjS f x = starRingEnd ℂ (f x) := rfl

def mulS (m f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (m : V → ℂ) f

theorem mulS_apply (m f : 𝓢(V, ℂ)) (x : V) : mulS m f x = m x * f x := by
  have := congrFun (SchwartzMap.smulLeftCLM_apply (F := ℂ) m.hasTemperateGrowth f) x
  simpa [mulS, smul_eq_mul] using this

def evS (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)

theorem evS_apply (x : V) (f : 𝓢(V, ℂ)) : evS x f = f x := rfl

theorem sum_apply {ι : Type} (s : Finset ι) (F : ι → 𝓢(V, ℂ)) (x : V) : (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← evS_apply x, map_sum]; rfl

theorem trans_apply (a : V) (f : 𝓢(V, ℂ)) (x : V) : SchwartzMap.compSubConstCLM ℂ a f x = f (x - a) := by
  simp

theorem exists_bump [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K) :
    ∃ χ : 𝓢(V, ℂ), HasCompactSupport (χ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (χ x) = χ x) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have h0 : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  let b : ContDiffBump (0 : V) := ⟨max R 1, max R 1 + 1, h0, by linarith⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, fun x => ?_, fun x hx => ?_⟩
  · change starRingEnd ℂ ((b x : ℝ) : ℂ) = ((b x : ℝ) : ℂ)
    simp
  · change ((b x : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR hx)

end GlobalTheory.TransConstForm

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_lambda [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
    (htr : ∀ (a : V) (f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ)
    (hmul : ∀ (m f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ) :
    ∃ Λ : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f g h : 𝓢(V, ℂ), HasCompactSupport (f : V → ℂ) →
      (∀ x, h x = f x * starRingEnd ℂ (g x)) → ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = Λ h := by
  classical
  set B : 𝓢(V, ℂ) → 𝓢(V, ℂ) → ℂ := fun f g => ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ with hB
  have hL : ∀ g, ∃ L : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f, L f = B f g := fun g => by
    obtain ⟨L, hL⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ (T g)
    exact ⟨L.comp T, fun f => by simp [hL, hB]⟩
  choose L hLB using hL
  obtain ⟨ψ, hψc, hψr, v, hsum1, hfin, M, hsumm⟩ := GlobalTheory.T.real_compact_partition_unity V
  obtain ⟨χ, hχc, hχr, hχ1⟩ := exists_bump (tsupport (ψ : V → ℂ)) hψc
  let tr : V → 𝓢(V, ℂ) → 𝓢(V, ℂ) := fun a f => SchwartzMap.compSubConstCLM ℂ a f
  have htr_apply : ∀ a f x, tr a f x = f (x - a) := fun a f x => trans_apply a f x
  have hχψ : ∀ y, starRingEnd ℂ (χ y) * ψ y = ψ y := by
    intro y
    by_cases hy : ψ y = 0
    · simp [hy]
    · rw [hχr, hχ1 y (subset_tsupport _ hy), one_mul]
  have hterm : ∀ h, ∃ C : ℝ, ∀ j, ‖B h (tr (v j) ψ)‖ ≤ C * ((1 + ‖v j‖) ^ M)⁻¹ := by
    intro h
    obtain ⟨C, hC⟩ := GlobalTheory.T.translation_isometry_schwartz_operator V μ T htr χ ψ h hχc M
    refine ⟨C, fun j => ?_⟩
    have e : B h (tr (v j) ψ) = B (mulS (tr (v j) χ) h) (tr (v j) ψ) :=
      (hmul (tr (v j) χ) h (mulS (tr (v j) χ) h) (tr (v j) ψ) (tr (v j) ψ)
        (fun x => mulS_apply _ _ x) (fun x => by simp only [htr_apply]; exact (hχψ _).symm)).symm
    rw [e]
    exact hC (v j) _ _ (fun x => by rw [mulS_apply, htr_apply]) (fun x => htr_apply _ _ x)
  have hsummable : ∀ h, Summable (fun j => L (tr (v j) ψ) h) := by
    intro h
    obtain ⟨C, hC⟩ := hterm h
    refine Summable.of_norm_bounded (hsumm.mul_left C) (fun j => ?_)
    rw [hLB]; exact hC j
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  obtain ⟨en, hen⟩ := exists_surjective_nat (Fin (Module.finrank ℝ V) → ℤ)
  let S : ℕ → Finset (Fin (Module.finrank ℝ V) → ℤ) := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen w
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  have hlim : Tendsto (fun N h => (∑ j ∈ S N, L (tr (v j) ψ)) h) atTop
      (𝓝 fun h : 𝓢(V, ℂ) => ∑' j, L (tr (v j) ψ) h) := by
    rw [tendsto_pi_nhds]
    intro h
    simp only [ContinuousLinearMap.sum_apply]
    exact (hsummable h).hasSum.comp hS
  refine ⟨continuousLinearMapOfTendsto (fun N => ∑ j ∈ S N, L (tr (v j) ψ)) hlim, fun f g h hf hh => ?_⟩
  show _ = linearMapOfTendsto _ _ hlim h
  rw [linearMapOfTendsto_apply]
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  set J := (hfin (R + r)).toFinset with hJ
  have hout : ∀ j, j ∉ J → ∀ x, ψ (x - v j) * f x = 0 := by
    intro j hj x
    by_contra hne
    have h1 : ψ (x - v j) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : f x ≠ 0 := right_ne_zero_of_mul hne
    have hx : ‖x‖ ≤ R := by simpa using hR (subset_tsupport _ h2)
    have hy : ‖x - v j‖ ≤ r := by simpa using hr (subset_tsupport _ h1)
    apply hj
    rw [hJ, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    calc ‖v j‖ = ‖x - (x - v j)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - v j‖ := norm_sub_le _ _
      _ ≤ R + r := add_le_add hx hy
  have hterm_eq : ∀ j, L (tr (v j) ψ) h = B (mulS (tr (v j) ψ) f) g := by
    intro j
    rw [hLB]
    have ea := hmul (conjS g) f h (tr (v j) ψ) (mulS (tr (v j) ψ) g)
      (fun x => by rw [hh, conjS_apply, mul_comm])
      (fun x => by rw [mulS_apply, conjS_apply, Complex.conj_conj, mul_comm])
    have eb := hmul (tr (v j) ψ) f (mulS (tr (v j) ψ) f) g (mulS (tr (v j) ψ) g)
      (fun x => mulS_apply _ _ x)
      (fun x => by rw [mulS_apply, htr_apply, hψr])
    exact ea.trans eb.symm
  have hzero : ∀ j, j ∉ J → mulS (tr (v j) ψ) f = 0 := by
    intro j hj
    ext x
    rw [mulS_apply, htr_apply]
    exact hout j hj x
  have hsumf : ∑ j ∈ J, mulS (tr (v j) ψ) f = f := by
    ext x
    rw [sum_apply]
    simp only [mulS_apply, htr_apply]
    rw [← Finset.sum_mul]
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hs : HasSum (fun j => ψ (x - v j)) (∑ j ∈ J, ψ (x - v j)) := by
        refine hasSum_sum_of_ne_finset_zero (fun j hj => ?_)
        have := hout j hj x
        exact (mul_eq_zero.1 this).resolve_right hfx
      rw [← (hsum1 x).unique hs, one_mul]
  calc B f g = L g f := (hLB g f).symm
    _ = L g (∑ j ∈ J, mulS (tr (v j) ψ) f) := by rw [hsumf]
    _ = ∑ j ∈ J, B (mulS (tr (v j) ψ) f) g := by rw [map_sum]; simp only [hLB]
    _ = ∑ j ∈ J, L (tr (v j) ψ) h := Finset.sum_congr rfl (fun j _ => (hterm_eq j).symm)
    _ = ∑' j, L (tr (v j) ψ) h := by
      refine (tsum_eq_sum (fun j hj => ?_)).symm
      rw [hterm_eq, hzero j hj, ← hLB, map_zero]

end GlobalTheory.TransConstForm

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem main_of [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
    (htr : ∀ (a : V) (f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ)
    (hmul : ∀ (m f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ) :
    ∃ c : ℂ, ∀ f g : 𝓢(V, ℂ),
      ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  classical
  obtain ⟨Λ, hΛ⟩ := exists_lambda μ T htr hmul
  set B : 𝓢(V, ℂ) → 𝓢(V, ℂ) → ℂ := fun f g => ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ with hB
  have hL : ∀ g, ∃ L : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f, L f = B f g := fun g => by
    obtain ⟨L, hL⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ (T g)
    exact ⟨L.comp T, fun f => by simp [hL, hB]⟩
  choose L hLB using hL
  let tr : V → 𝓢(V, ℂ) → 𝓢(V, ℂ) := fun a f => SchwartzMap.compSubConstCLM ℂ a f
  have htr_apply : ∀ a f x, tr a f x = f (x - a) := fun a f x => trans_apply a f x
  have hΛc : ∀ h : 𝓢(V, ℂ), HasCompactSupport (h : V → ℂ) → ∀ a, Λ (tr a h) = Λ h := by
    intro h hh a
    obtain ⟨χ, hχc, hχr, hχ1⟩ := exists_bump (tsupport (h : V → ℂ)) hh
    have e1 : B h χ = Λ h := hΛ h χ h hh (fun x => by
      by_cases hx : h x = 0
      · simp [hx]
      · rw [hχr, hχ1 x (subset_tsupport _ hx), mul_one])
    have hh' : HasCompactSupport (tr a h : V → ℂ) := by
      have : (tr a h : V → ℂ) = (h : V → ℂ) ∘ (Homeomorph.subRight a) := by
        funext x; simp [htr_apply]
      rw [this]; exact hh.comp_homeomorph _
    have e2 : B (tr a h) (tr a χ) = Λ (tr a h) := hΛ _ _ _ hh' (fun x => by
      rw [htr_apply, htr_apply]
      by_cases hx : h (x - a) = 0
      · simp [hx]
      · rw [hχr, hχ1 _ (subset_tsupport _ hx), mul_one])
    have e3 : B h χ = B (tr a h) (tr a χ) :=
      htr a (tr a h) h (tr a χ) χ (fun x => by rw [htr_apply, add_sub_cancel_right])
        (fun x => by rw [htr_apply, add_sub_cancel_right])
    rw [← e2, ← e1, e3]
  have hΛt : ∀ a h, Λ (tr a h) = Λ h := by
    intro a h
    have hcl : IsClosed {h : 𝓢(V, ℂ) | Λ (tr a h) = Λ h} :=
      isClosed_eq (Λ.continuous.comp (SchwartzMap.compSubConstCLM ℂ a).continuous) Λ.continuous
    exact closure_minimal (fun h hh => hΛc h hh a) hcl (GlobalTheory.T.schwartz_compact_support_dense V h)
  have hΛt' : ∀ (a : V) (f g : 𝓢(V, ℂ)), (⇑g = fun x => f (x + a)) → Λ g = Λ f := by
    intro a f g hg
    have : g = tr (-a) f := by
      ext x; rw [htr_apply, sub_neg_eq_add]; exact congrFun hg x
    rw [this, hΛt]
  let I : 𝓢(V, ℂ) →L[ℂ] ℂ := SchwartzMap.integralCLM ℂ μ
  have hIa : ∀ u, I u = ∫ x, u x ∂μ := fun u => SchwartzMap.integralCLM_apply ℂ u
  have hIt : ∀ (a : V) (f g : 𝓢(V, ℂ)), (⇑g = fun x => f (x + a)) → I g = I f := by
    intro a f g hg
    rw [hIa, hIa, hg]
    exact integral_add_right_eq_self (fun x => f x) a
  have hI0 : I ≠ 0 := by
    intro h0
    let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
    have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have := congrArg (fun F : 𝓢(V, ℂ) →L[ℂ] ℂ => F (h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff))) h0
    simp only [ContinuousLinearMap.zero_apply, hIa] at this
    change ∫ x, ((b x : ℝ) : ℂ) ∂μ = 0 at this
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at this
    exact (ne_of_gt (b.integral_pos (μ := μ))) this
  obtain ⟨c, hc⟩ := GlobalTheory.TransInvSchwartz.dim_le_one I Λ hIt hΛt' hI0
  refine ⟨c, fun f g => ?_⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ g
  have hcl : IsClosed {f : 𝓢(V, ℂ) | B f g = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ} := by
    have e : {f : 𝓢(V, ℂ) | B f g = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ} = {f | L g f = c * P f} := by
      ext f; simp only [Set.mem_setOf_eq, hLB, hP]
    rw [e]; exact isClosed_eq (L g).continuous (continuous_const.mul P.continuous)
  refine closure_minimal (fun f hf => ?_) hcl (GlobalTheory.T.schwartz_compact_support_dense V f)
  have := hΛ f g (mulS f (conjS g)) hf (fun x => by rw [mulS_apply, conjS_apply])
  show B f g = _
  rw [show B f g = Λ (mulS f (conjS g)) from this, hc, ContinuousLinearMap.smul_apply, smul_eq_mul, hIa]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mulS_apply, conjS_apply]

end GlobalTheory.TransConstForm

theorem GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    (∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x))) →
    ∃ c : ℂ, ∀ f g : SchwartzMap V ℂ,
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x)) =
        c * @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => f x * starRingEnd ℂ (g x)) := by
  intro V _ _ _ μ hμ T htr hmul
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  exact GlobalTheory.TransConstForm.main_of μ T htr hmul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2Statement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_invariant_form_const_l2 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    (∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x))) →
    ∃ c : ℂ, ∀ f g : SchwartzMap V ℂ,
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x)) =
        c * @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => f x * starRingEnd ℂ (g x)) := by
  first | exact @GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant | exact GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant | (intros; apply GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant <;> assumption)
end
