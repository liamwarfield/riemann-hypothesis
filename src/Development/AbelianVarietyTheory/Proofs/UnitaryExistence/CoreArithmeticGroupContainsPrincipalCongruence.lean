module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnfGroupContainsCongruenceUptoRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RootOfUnityEqOneOfConjCongruence
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

theorem isIntegral_eigenvalue_sub_one_div {E : Type} [Field E] [NumberField E] {r M : ℕ}
    (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ)
    (hM : (M : ℂ) ≠ 0) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hγ : ∀ x ∈ Λ, ∃ y ∈ Λ, γ *ᵥ x - x = (M : E) • y)
    (w : Fin r → ℂ) (hw : w ≠ 0) (l : ℂ) (hl : w ᵥ* γ.map τ = l • w) :
    IsIntegral ℤ ((l - 1) / M) := by
  let φ : (Fin r → E) →+ ℂ :=
    { toFun := fun x => w ⬝ᵥ (τ ∘ x)
      map_zero' := by simp [dotProduct]
      map_add' := fun x y => by simp [dotProduct, mul_add, Finset.sum_add_distrib] }
  have hφ : ∀ x, φ x = w ⬝ᵥ (τ ∘ x) := fun _ => rfl
  have hsm : ∀ (c : E) x, φ (c • x) = τ c * φ x := by
    intro c x
    simp only [hφ, dotProduct, Finset.mul_sum, Function.comp, Pi.smul_apply, smul_eq_mul, map_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmul : ∀ x, φ (γ *ᵥ x) = l * φ x := by
    intro x
    have : τ ∘ (γ *ᵥ x) = γ.map τ *ᵥ (τ ∘ x) := funext fun i => RingHom.map_mulVec τ γ x i
    rw [hφ, this, Matrix.dotProduct_mulVec, hl, smul_dotProduct, hφ, smul_eq_mul]
  refine isIntegral_of_smul_mem_submodule
    ((Λ.restrictScalars ℤ).map φ.toIntLinearMap) ?_ (hfg.restrictScalars.map _) _ ?_
  · intro h0
    have h1 : ∀ x ∈ Λ, φ x = 0 := by
      intro x hx
      have : φ.toIntLinearMap x ∈ (Λ.restrictScalars ℤ).map φ.toIntLinearMap :=
        Submodule.mem_map_of_mem hx
      rw [h0] at this
      simpa using this
    have h2 : ∀ x ∈ Submodule.span E (Λ : Set (Fin r → E)), φ x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul c x _ hx => rw [hsm, hx, mul_zero]
    apply hw
    funext i
    have h3 := h2 (Pi.single i 1) (hsp ▸ Submodule.mem_top)
    have h4 : τ ∘ (Pi.single i 1 : Fin r → E) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [hφ, h4] at h3
    simpa using h3
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hγ x hx
    refine ⟨y, hy, ?_⟩
    have h := congrArg φ hxy
    rw [map_sub, hmul, hsm, map_natCast] at h
    simp only [AddMonoidHom.coe_toIntLinearMap, smul_eq_mul]
    field_simp
    linear_combination -h

theorem root_of_unity_eq_one_of_isIntegral_div {E : Type} [Field E] [NumberField E] {M n : ℕ}
    (hM : 3 ≤ M) (hn : 0 < n) {u : E} (hu : u ^ n = 1) (h : IsIntegral ℤ ((u - 1) / M)) :
    u = 1 := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (M : E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hlt : ∀ φ : E →+* ℂ, ‖φ ((u - 1) / M)‖ < 1 := by
    intro φ
    have h1 : ‖φ u‖ = 1 := by
      have : ‖φ u‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hu, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h2 : ‖φ u - 1‖ ≤ 2 := by
      have := norm_sub_le (φ u) 1
      rw [h1, norm_one] at this
      linarith
    rw [map_div₀, map_sub, map_one, map_natCast, norm_div, Complex.norm_natCast,
      div_lt_one (by linarith)]
    linarith
  by_contra hne
  have hx : (u - 1) / M ≠ 0 := div_ne_zero (sub_ne_zero.2 hne) hM0
  obtain ⟨k, hk, hk1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx h
    fun φ => (hlt φ).le
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : ‖φ ((u - 1) / M)‖ ^ k = 1 := by rw [← norm_pow, ← map_pow, hk1, map_one, norm_one]
  exact (hlt φ).ne ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3)

theorem root_of_unity_eq_one_of_conj_congruence :
    ∀ (E : Type) [Field E] [NumberField E] (r M n : ℕ) (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (γ δ : Matrix (Fin r) (Fin r) E) (u : E) (τ : E →+* ℂ) (Q : Matrix (Fin r) (Fin r) ℂ), 0 < r → 3 ≤ M → 0 < n → u ^ n = 1 → Λ.FG → Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → (∀ x ∈ Λ', ∃ y ∈ Λ', Matrix.mulVec (δ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) → Q.det ≠ 0 → (u • γ).map τ * Q = Q * δ.map τ → u = 1 := by
  intro E _ _ r M n Λ Λ' γ δ u τ Q hr hM hn hu hfg hfg' hsp hsp' hγ hδ hQ hconj
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (γ.map τ)ᵀ)
  obtain ⟨w, hw⟩ := hl.exists_hasEigenvector
  have hw0 : w ≠ 0 := hw.2
  have hw1 : w ᵥ* γ.map τ = l • w := by
    have := hw.apply_eq_smul
    rwa [Matrix.toLin'_apply, Matrix.mulVec_transpose] at this
  have hwQ : w ᵥ* Q ≠ 0 := fun h => hw0 (Matrix.eq_zero_of_vecMul_eq_zero hQ h)
  have hs : (u • γ).map τ = τ u • γ.map τ := by
    ext i j; simp
  have hw2 : (w ᵥ* Q) ᵥ* δ.map τ = (τ u * l) • (w ᵥ* Q) := by
    rw [Matrix.vecMul_vecMul, ← hconj, ← Matrix.vecMul_vecMul, hs, Matrix.vecMul_smul, hw1,
      smul_smul, Matrix.smul_vecMul]
  have ha := isIntegral_eigenvalue_sub_one_div Λ γ τ hM0 hfg hsp hγ w hw0 l hw1
  have hb := isIntegral_eigenvalue_sub_one_div Λ' δ τ hM0 hfg' hsp' hδ _ hwQ _ hw2
  have hui : IsIntegral ℤ (τ u) := by
    apply IsIntegral.of_pow hn
    rw [← map_pow, hu, map_one]
    exact isIntegral_one
  have hc : τ ((u - 1) / M) = (τ u * l - 1) / M - τ u * ((l - 1) / M) := by
    rw [map_div₀, map_sub, map_one, map_natCast]
    field_simp
    ring
  refine root_of_unity_eq_one_of_isIntegral_div hM hn hu ?_
  refine (isIntegral_algHom_iff τ.toIntAlgHom τ.injective).1 ?_
  change IsIntegral ℤ (τ ((u - 1) / M))
  rw [hc]
  exact hb.sub (hui.mul ha)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfEventuallyDotProductStarEqZero
namespace GlobalTheory.UnitaryOrbitForm

open Matrix Filter Topology

variable {r : ℕ}

private lemma dotProduct_mulVec_star_add_smul_expand (C : Matrix (Fin r) (Fin r) ℂ) (a b : ℂ) (x y : Fin r → ℂ) :
    (a • x + b • y) ⬝ᵥ C *ᵥ star (a • x + b • y) =
      a * star a * (x ⬝ᵥ C *ᵥ star x) + b * star b * (y ⬝ᵥ C *ᵥ star y) +
        a * star b * (x ⬝ᵥ C *ᵥ star y) + b * star a * (y ⬝ᵥ C *ᵥ star x) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem eq_zero_of_forall_dotProduct_star_eq_zero {C : Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ u : Fin r → ℂ, u ⬝ᵥ C *ᵥ star u = 0) : C = 0 := by
  have hS : ∀ x y : Fin r → ℂ, x ⬝ᵥ C *ᵥ star y = 0 := by
    intro x y
    have h1 := h ((1 : ℂ) • x + (1 : ℂ) • y)
    have h2 := h ((1 : ℂ) • x + Complex.I • y)
    rw [dotProduct_mulVec_star_add_smul_expand, h x, h y] at h1 h2
    have hsI : star Complex.I = -Complex.I := by simp
    rw [hsI, star_one] at h2
    rw [star_one] at h1
    linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 +
      ((x ⬝ᵥ C *ᵥ star y) - (y ⬝ᵥ C *ᵥ star x)) / 2 * Complex.I_sq
  ext i j
  have := hS (Pi.single i 1) (Pi.single j 1)
  simpa using this

theorem eq_zero_of_eventually_dotProduct_star_eq_zero {C : Matrix (Fin r) (Fin r) ℂ}
    {v : Fin r → ℂ} (h : ∀ᶠ w in 𝓝 v, w ⬝ᵥ C *ᵥ star w = 0) : C = 0 := by
  apply eq_zero_of_forall_dotProduct_star_eq_zero
  intro u
  have hv : v ⬝ᵥ C *ᵥ star v = 0 := h.self_of_nhds
  have hc : ∀ s : ℝ, Continuous fun t : ℝ => (1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u := fun s =>
    continuous_const.add ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).smul
      continuous_const)
  have e : ∀ s : ℝ, ∀ᶠ t : ℝ in 𝓝 0,
      ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) ⬝ᵥ C *ᵥ star ((1 : ℂ) • v + ((s * t : ℝ) : ℂ) • u) = 0 :=
    fun s => ((hc s).tendsto' 0 v (by simp)).eventually h
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ :=
    (((e 1).and (e (-1))).filter_mono nhdsWithin_le_nhds |>.and
      (self_mem_nhdsWithin : ({0}ᶜ : Set ℝ) ∈ 𝓝[≠] (0 : ℝ))).exists
  rw [dotProduct_mulVec_star_add_smul_expand, hv] at h1 h2
  simp only [star_one, Complex.star_def, Complex.conj_ofReal] at h1 h2
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have key : ((t : ℂ) ^ 2) * (u ⬝ᵥ C *ᵥ star u) = 0 := by
    push_cast at h1 h2
    linear_combination (h1 + h2) / 2
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 ht0)

theorem dotProduct_star_eq_re {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian)
    (w : Fin r → ℂ) : w ⬝ᵥ A *ᵥ star w = ((w ⬝ᵥ A *ᵥ star w).re : ℂ) := by
  have hc : star (w ⬝ᵥ A *ᵥ star w) = w ⬝ᵥ A *ᵥ star w := by
    simp only [dotProduct, mulVec, Finset.mul_sum, star_sum, star_mul', star_star, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hA.apply i j]
    ring
  exact (Complex.conj_eq_iff_re.mp hc).symm

private lemma transpose_col_mul_mul_map_conj_apply (B : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) (i j : Fin 1) :
    ((Matrix.of fun k (_ : Fin 1) => x k)ᵀ * B *
      (Matrix.of fun k (_ : Fin 1) => x k).map (starRingEnd ℂ)) i j = x ⬝ᵥ B *ᵥ star x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply, dotProduct,
    mulVec, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma of_col_mulVec_eq_smul (x : Fin r → ℂ) (a : Fin 1 → ℂ) :
    (Matrix.of fun k (_ : Fin 1) => x k) *ᵥ a = a 0 • x := by
  ext i
  simp [mulVec, dotProduct, mul_comm]

private lemma mul_of_col_eq_of_mulVec (g : Matrix (Fin r) (Fin r) ℂ) (x : Fin r → ℂ) :
    g * (Matrix.of fun k (_ : Fin 1) => x k) = Matrix.of fun k (_ : Fin 1) => (g *ᵥ x) k := by
  ext i j
  simp [Matrix.mul_apply, mulVec, dotProduct]

theorem exists_unitary_mulVec_eq {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) {v w : Fin r → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᵀ * B * g.map (starRingEnd ℂ) = B ∧ g *ᵥ v = w := by
  have hG : ∀ a b, starRingEnd ℂ (B a b) = B b a := fun a b => by
    rw [starRingEnd_apply]
    exact hB.apply b a
  have h0 : ∀ a : Fin 1 → ℂ, (Matrix.of fun k (_ : Fin 1) => v k) *ᵥ a = 0 ↔
      (Matrix.of fun k (_ : Fin 1) => w k) *ᵥ a = 0 := by
    intro a
    rw [of_col_mulVec_eq_smul, of_col_mulVec_eq_smul, smul_eq_zero, smul_eq_zero]
    simp [hv, hw]
  have hXY : (Matrix.of fun k (_ : Fin 1) => w k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => w k).map (starRingEnd ℂ) =
      (Matrix.of fun k (_ : Fin 1) => v k)ᵀ * B *
        (Matrix.of fun k (_ : Fin 1) => v k).map (starRingEnd ℂ) := by
    ext i j
    rw [transpose_col_mul_mul_map_conj_apply, transpose_col_mul_mul_map_conj_apply, h]
  obtain ⟨γ, hγ, hγX⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq two_ne_zero
    (fun t => Complex.conj_conj t) hG hdet h0 hXY
  refine ⟨γ, hγ, ?_⟩
  rw [mul_of_col_eq_of_mulVec] at hγX
  funext i
  simpa using congrFun (congrFun hγX i) 0

private lemma dotProduct_mulVec_star_real_smul (C : Matrix (Fin r) (Fin r) ℂ) (a : ℝ) (x : Fin r → ℂ) :
    ((a : ℂ) • x) ⬝ᵥ C *ᵥ star ((a : ℂ) • x) = ((a ^ 2 : ℝ) : ℂ) * (x ⬝ᵥ C *ᵥ star x) := by
  simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem eq_smul_of_norm_eq_one_on_orbit :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ), A.IsHermitian → B.IsHermitian →
      B.det ≠ 0 → (∀ h : Matrix (Fin r) (Fin r) ℂ, hᵀ * B * h.map (starRingEnd ℂ) = B →
        ‖(h *ᵥ v) ⬝ᵥ (A *ᵥ star (h *ᵥ v))‖ = 1) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by
  intro r A B v hA hB hdet hh
  have hid : (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * B * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      B := by
    simp
  have hv : v ≠ 0 := by
    rintro rfl
    have := hh 1 hid
    simp at this
  have hAre := dotProduct_star_eq_re hA
  have hBre := dotProduct_star_eq_re hB

  have horb : ∀ w : Fin r → ℂ, w ≠ 0 → (w ⬝ᵥ B *ᵥ star w).re = (v ⬝ᵥ B *ᵥ star v).re →
      |(w ⬝ᵥ A *ᵥ star w).re| = 1 := by
    intro w hw hwv
    have hQ : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v := by
      rw [hBre w, hBre v, hwv]
    obtain ⟨g, hg, rfl⟩ := exists_unitary_mulVec_eq hB hdet hv hw hQ
    have := hh g hg
    rwa [hAre (g *ᵥ v), Complex.norm_real, Real.norm_eq_abs] at this
  have hsr : |(v ⬝ᵥ A *ᵥ star v).re| = 1 := horb v hv rfl

  have hcr : (v ⬝ᵥ B *ᵥ star v).re ≠ 0 := by
    intro h0
    have e := horb (((2 : ℝ) : ℂ) • v) (smul_ne_zero (by norm_num) hv)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, h0, mul_zero])
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, abs_mul, hsr] at e
    norm_num at e
  set cr := (v ⬝ᵥ B *ᵥ star v).re with hcr_def
  set sr := (v ⬝ᵥ A *ᵥ star v).re with hsr_def
  have hcont : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      Continuous fun w : Fin r → ℂ => (w ⬝ᵥ M *ᵥ star w).re := fun M =>
    Complex.continuous_re.comp
      (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))

  have hφ : Filter.Tendsto (fun w : Fin r → ℂ =>
      (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 sr) := by
    have h : ContinuousAt (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) v :=
      ((hcont A).continuousAt.mul (continuousAt_const (y := cr))).div (hcont B).continuousAt hcr
    have h2 : Filter.Tendsto (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 (sr * cr / cr)) := h.tendsto
    have hval : sr * cr / cr = sr := by field_simp
    rwa [hval] at h2
  have E1 : ∀ᶠ w in 𝓝 v, w ≠ 0 := eventually_ne_nhds hv
  have E2 : ∀ᶠ w in 𝓝 v, 0 < (w ⬝ᵥ B *ᵥ star w).re * cr :=
    continuousAt_const.eventually_lt ((hcont B).continuousAt.mul continuousAt_const)
      (mul_self_pos.mpr hcr)
  have E3 := hφ.eventually (Ioo_mem_nhds (show sr - 1 < sr by linarith) (show sr < sr + 1 by linarith))
  have key : ∀ᶠ w in 𝓝 v, w ⬝ᵥ (A - ((sr / cr : ℝ) : ℂ) • B) *ᵥ star w = 0 := by
    filter_upwards [E1, E2, E3] with w hw hpos hI
    obtain ⟨hI1, hI2⟩ := hI
    have hqB : (w ⬝ᵥ B *ᵥ star w).re ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hq : 0 < cr / (w ⬝ᵥ B *ᵥ star w).re := by
      rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact div_pos h2 h1
      · exact div_pos_of_neg_of_neg h2 h1
    have ha2 : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ^ 2 = cr / (w ⬝ᵥ B *ᵥ star w).re :=
      Real.sq_sqrt hq.le
    have ha : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'

    have e := horb ((Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) : ℂ) • w)
      (smul_ne_zero (Complex.ofReal_ne_zero.mpr ha) hw)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2]; field_simp)
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2] at e
    have e' : |(w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re| = 1 := by
      rw [← e]
      congr 1
      ring
    have hφw : (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re = sr := by
      rcases (abs_eq zero_le_one).mp e' with h1 | h1 <;>
        rcases (abs_eq zero_le_one).mp hsr with h2 | h2 <;> linarith [hI1, hI2]
    have hreal : (w ⬝ᵥ A *ᵥ star w).re - sr / cr * (w ⬝ᵥ B *ᵥ star w).re = 0 := by
      have h := hφw
      field_simp at h ⊢
      linear_combination h
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, hAre w, hBre w,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, hreal, Complex.ofReal_zero]
  have hC := eq_zero_of_eventually_dotProduct_star_eq_zero key
  refine ⟨sr / cr, div_ne_zero ?_ hcr, sub_eq_zero.mp hC⟩
  intro h0
  rw [h0, abs_zero] at hsr
  exact zero_ne_one hsr

end GlobalTheory.UnitaryOrbitForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Matrix

namespace GlobalTheory.PrincCore

theorem unitary_of_first_minor {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (hr : 0 < r)
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (hG : ∀ a b, cc (G a b) = G b a)
    (J x₀ : Matrix (Fin r) (Fin r) ℂ) (hJ : J.IsHermitian) (hd : J.det ≠ 0)
    (h : ∀ u : Matrix (Fin r) (Fin r) ℂ, (u.map (starRingEnd ℂ))ᵀ * J * u = J →
      ‖lminor (gram τ G (u * x₀)) ⟨1, by omega⟩‖ = 1)
    (w : Matrix (Fin r) (Fin r) ℂ) (hw : wᵀ * G.map τ * w.map (starRingEnd ℂ) = G.map τ) :
    (w.map (starRingEnd ℂ))ᵀ * J * w = J := by
  have hA : (G.map τ).IsHermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hG b a]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  have tr : ∀ u : Matrix (Fin r) (Fin r) ℂ, uᵀ * Jᵀ * u.map (starRingEnd ℂ) = Jᵀ →
      (u.map (starRingEnd ℂ))ᵀ * J * u = J := by
    intro u hu
    have := congrArg Matrix.transpose hu
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using this
  obtain ⟨t, ht, hAt⟩ := GlobalTheory.UnitaryOrbitForm.eq_smul_of_norm_eq_one_on_orbit r (G.map τ) Jᵀ
    (col x₀ ⟨0, hr⟩) hA hJ.transpose (by rwa [Matrix.det_transpose]) (by
      intro u hu
      rw [← h u (tr u hu)]
      congr 1
      unfold lminor
      rw [Matrix.det_unique]
      simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, hermC, dotProduct, Matrix.mulVec, col,
        Matrix.map_apply, Matrix.mul_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]
      rfl)
  apply tr
  rw [hAt, Matrix.mul_smul, Matrix.smul_mul] at hw
  exact smul_right_injective _ (by exact_mod_cast ht : (t : ℂ) ≠ 0) hw

theorem exists_lattice_congr (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n M : ℕ) (hM : M ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hs : Submodule.span E (L : Set (Fin n → E)) = ⊤) (g : GL (Fin n) (GlobalTheory.AdLat.RA F E))
    (κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (δ : Matrix (Fin n) (Fin n) E)
    (hκ : ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      κ *ᵥ z - z = M • y)
    (he : δ.map (inclR (F := F) (Af F)) * g.1 = g.1 * κ) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      ∀ x ∈ Λ, ∃ y ∈ Λ, δ *ᵥ x - x = (M : E) • y := by
  obtain ⟨Λ, h1, h2, h3, -⟩ := GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate F E n L g hL hs
  refine ⟨Λ, h2, h3, fun x hx => ?_⟩
  have hx' : x ∈ GlobalTheory.AdLat.latOf F g.1 (L : Set (Fin n → E)) := h1 ▸ hx
  obtain ⟨z, hz, hzx⟩ := hx'
  obtain ⟨y, hy, hzy⟩ := hκ z hz
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM
  refine ⟨(M : E)⁻¹ • (δ *ᵥ x - x), ?_, by rw [smul_smul, mul_inv_cancel₀ hME, one_smul]⟩
  show _ ∈ (Λ : Set (Fin n → E))
  rw [h1]
  refine ⟨y, hy, ?_⟩
  let i : E →+* GlobalTheory.AdLat.RA F E := inclR (F := F) (Af F)
  have hf : ∀ v : Fin n → E, GlobalTheory.AdLat.fv F v = i ∘ v := fun _ => rfl
  have e1 : i ∘ (δ *ᵥ x) = δ.map i *ᵥ (i ∘ x) := funext fun a => RingHom.map_mulVec i δ x a
  have e2 : i ∘ (δ *ᵥ x) - i ∘ x = M • (g.1 *ᵥ y) := by
    rw [e1, ← hf x, ← hzx, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hzy,
      Matrix.mulVec_smul]
  rw [hf]
  funext a
  have e3 := congrFun e2 a
  simp only [Pi.sub_apply, Function.comp, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_sub] at e3 ⊢
  rw [e3, ← map_natCast i M, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hME, map_one, one_mul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 800000 in
theorem root_eq_one {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (hr0 : 0 < r) {Comp : Type}
    (X : Comp → Data D.host.E r) (dict : GA D V → Σ c, Frame (X c).Ψ r) (mu : GA D V → ℂ)
    (Kf : Subgroup (GA D V)) (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hD : DictIsUnif V dict Kf th hr) (hmu : MuUnit V dict mu)
    (M : ℕ) (hM : 3 ≤ M) (hK : IsLevelK V M Kf) (k : Comp) (γ γ' : GL (Fin r) D.host.E) (hγ' : γ' ∈ (X k).Γ)
    (hc : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (γ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ x - x = (M : D.host.E) • y)
    (u : D.host.E) (n : ℕ) (hn : 0 < n) (hu : u ^ n = 1)
    (he : (γ' : Matrix (Fin r) (Fin r) D.host.E) = u • (γ : Matrix (Fin r) (Fin r) D.host.E)) : u = 1 := by
  classical
  subst hr
  obtain ⟨-, -, ⟨x0, hx0, heq⟩, -, -, hfib⟩ := hD
  obtain ⟨hdom, g, hg⟩ := hx0 k
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := heq g
    rw [hg] at this
    exact this
  have hun : ∀ τ : (X k).Ψ, ((γ'.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ'.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    refine unitary_of_first_minor hr0 τ.1 (X k).Gm (X k).Gm_herm _ (mat (x0 k) τ) ?_ ?_ ?_ _ ?_
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, HSpace.gram]
      rw [← V.herm.eq (V.frame b) (V.frame a)]
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero_iff _ τ.1.injective).2 (gram_det_ne V)
    · intro w hw
      obtain ⟨h, hh, hw'⟩ := hsur (Function.update (fun _ => 1) τ w) (by
        intro τ'
        by_cases e : τ' = τ
        · subst e
          simpa using hw
        · simp [Function.update_of_ne e])
      obtain ⟨γ'', h1, h2⟩ := key h hh
      have h3 := hmu.2.2.2 (g * h)
      rw [h2] at h3
      have h4 := h3 τ ⟨1, by omega⟩
      rw [ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.dmin_lact (X k) h1] at h4
      unfold dmin at h4
      rw [hact, hw', Function.update_self] at h4
      exact h4
    · have hcc : (γ'.1.map τ.1).map (starRingEnd ℂ) =
          (γ'.1.map cc).map τ.1 := by
        ext a b
        exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
      rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
        ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ']
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  obtain ⟨γ'', h1, h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ', mul_mem h1 hγ', ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ').1.map τ.1 * mat (x0 k) τ
    rw [hact, hw, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀
  obtain ⟨hκ1, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have h0 : finHom V h = 1 := hh
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := hκ1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  let f : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.toLinearMap.restrictScalars _
  have hhat : latHat V = GlobalTheory.AdLat.hat D.host.F (V.L0.map f : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hspan : Submodule.span D.host.E (V.L0.map f : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (V.L0.map f : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  rw [hhat] at hκ2
  obtain ⟨Λ', g1, g2, g3⟩ := exists_lattice_congr D.host.F D.host.E V.rank M (by omega) (V.L0.map f)
    (V.standardTuple_isLattice.fg.map f) hspan (finHom V g) (finHom V κ⁻¹).1 δ.1 hκ2 (by
      rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul])
  obtain ⟨τ⟩ : Nonempty (X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases e : τ ∈ (X k).Ψ
    · exact ⟨⟨τ, e⟩⟩
    · exact ⟨⟨_, not_not.1 (fun e' => e (((X k).cmType τ).2 e'))⟩⟩
  have hm : ∀ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h1' : archM V (th k τ) 1 = 1 := by
    unfold archM
    rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine GlobalTheory.root_of_unity_eq_one_of_conj_congruence D.host.E V.rank M n (X k).Λ Λ' γ.1 δ.1 u τ.1
    (archM V (th k τ) g⁻¹) hr0 hM hn hu (X k).Λ_fg g1 (X k).Λ_span g2 hc g3 ?_ ?_
  · have := congrArg Matrix.det (hm g⁻¹ g)
    rw [inv_mul_cancel, h1', Matrix.det_one, Matrix.det_mul] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  · rw [← he, ← hw τ, ← hδ1 τ, ← hm, ← hm]
    have e : infHom V (h * g⁻¹) = infHom V (g⁻¹ * γ₀) := by
      rw [map_mul, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hinf, mul_inv_cancel_right]
    unfold archM
    rw [e]

theorem hasPrinc_core : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M := by
  intro D T h j hj σ hσ k γ hγ hc
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j), ∀ σ, GoodEmb T.Q.c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M := by
  first | exact @GlobalTheory.PrincCore.hasPrinc_core | exact GlobalTheory.PrincCore.hasPrinc_core | (intros; apply GlobalTheory.PrincCore.hasPrinc_core <;> assumption)
end
