module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValues
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry_real (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => (NormedSpace.exp (t • X)) i j := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h2

theorem coord_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) (k : KG ε) : coord ε c (k * expK ε X 0) = coord ε c k := by
  simp [coord, toMK_mul, toMK_expK hX, NormedSpace.exp_zero]

theorem mono_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) (k : KG ε) : mono ε s (k * expK ε X 0) = mono ε s k := by
  simp only [mono, coord_mul_expK_zero hX]

theorem hasDerivAt_coord {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) : ∃ ψ ∈ polyV ε 1, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε X t)) (ψ k) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ k : KG ε, HasDerivAt (fun t : ℝ => (toMK (k * expK ε X t)) a b)
      (∑ l, toMK k a l * X l b) 0 := by
    intro k
    have e : (fun t : ℝ => (toMK (k * expK ε X t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • X)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hX, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real X l b).const_mul _
  cases f
  · refine ⟨∑ l, star (X l b) • coord ε (a, l, false), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have h := (hent k).star
      have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε X t)) =
          fun t => star ((toMK (k * expK ε X t)) a b) := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, star (X l b) • coord ε (a, l, false)) k = star (∑ l, toMK k a l * X l b) := by
        rw [Finset.sum_apply, star_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, Bool.false_eq_true, if_false, star_mul']
        exact mul_comm _ _
      rw [hv]; exact h
  · refine ⟨∑ l, X l b • coord ε (a, l, true), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε X t)) =
          fun t => (toMK (k * expK ε X t)) a b := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, X l b • coord ε (a, l, true)) k = ∑ l, toMK k a l * X l b := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, if_true]
        exact mul_comm _ _
      rw [hv]; exact hent k

theorem hasDerivAt_mono {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) : ∀ d, s.length ≤ d → ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε X t)) (ψ k) 0 := by
  induction s with
  | nil =>
    intro d _
    refine ⟨0, Submodule.zero_mem _, fun k => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    intro d hd
    simp only [List.length_cons] at hd
    obtain ⟨ψc, hψc, hc⟩ := hasDerivAt_coord hX c
    obtain ⟨ψs, hψs, hs⟩ := ih (d - 1) (by omega)
    refine ⟨ψc * mono ε s + coord ε c * ψs, ?_, fun k => ?_⟩
    · have hle : 1 + (d - 1) ≤ d := by omega
      exact add_mem (polyV_mono ε hle (mul_mem hψc (mono_mem (by omega))))
        (polyV_mono ε hle (mul_mem (coord_mem ε c) hψs))
    · have h := (hc k).mul (hs k)
      have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε X t)) =
          fun t => coord ε c (k * expK ε X t) * mono ε s (k * expK ε X t) := by
        funext t; simp [mono]
      rw [e]
      rw [coord_mul_expK_zero hX, mono_mul_expK_zero hX] at h
      exact h

theorem hasDerivAt_of_mem {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (ψ k) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hasDerivAt_mono hX s d hs
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ₁, h₁, d₁⟩ := hx
    obtain ⟨ψ₂, h₂, d₂⟩ := hy
    exact ⟨ψ₁ + ψ₂, add_mem h₁ h₂, fun k => (d₁ k).add (d₂ k)⟩
  | smul a x _ hx =>
    obtain ⟨ψ, h, dψ⟩ := hx
    exact ⟨a • ψ, Submodule.smul_mem _ a h, fun k => by simpa using (dψ k).const_mul a⟩

theorem rder_mem_and_hasDerivAt (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    (X : Mx n) (hX : inK ε X) : rder ε [X] φ ∈ polyV ε d ∧
      ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (rder ε [X] φ k) 0 := by
  obtain ⟨ψ, hψ, hd⟩ := hasDerivAt_of_mem hX hφ
  have e : rder ε [X] φ = ψ := by
    funext k
    rw [rder_cons, rder_nil]
    exact (hd k).deriv
  rw [e]
  exact ⟨hψ, hd⟩

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivativeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_matrixRightInvariantDerivative : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ X : Mx n, inK ε X → GlobalTheory.KFourier.rder ε [X] φ ∈ GlobalTheory.KFourier.polyV ε d ∧ ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (GlobalTheory.KFourier.rder ε [X] φ k) 0 := by
  first | exact @GlobalTheory.KFourier.rder_mem_and_hasDerivAt | exact GlobalTheory.KFourier.rder_mem_and_hasDerivAt | (intros; apply GlobalTheory.KFourier.rder_mem_and_hasDerivAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayField
set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRay

set_option autoImplicit false in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.InRay.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, Odd n → 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  fun K _ _ h2 hd L hL n _ hn R _ _ hR =>
    weberSet_subset_of_isRay_span_natCast K h2 hd L hL n hn R hR

end GlobalTheory.FieldSize.InRay
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integral_conjK (ε : Fin n → Bool) (f : KG ε → ℂ) (a : KG ε) :
    ∫ k, f (a * k * a⁻¹) ∂(muK ε) = ∫ k, f k ∂(muK ε) := by
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  have h1 := integral_mul_right_eq_self (μ := muK ε) (fun k => f (a * k)) a⁻¹
  have h2 := integral_mul_left_eq_self (μ := muK ε) f a
  simp only [mul_assoc] at h1 ⊢
  exact h1.trans h2

theorem integrable_of_continuousK {ε : Fin n → Bool} {f : KG ε → ℂ} (hf : Continuous f) :
    Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem lowV_le (ε : Fin n → Bool) (i : ℕ) : lowV ε i ≤ polyV ε i := by
  cases i with
  | zero => exact bot_le
  | succ j => exact polyV_mono ε (Nat.le_succ j)

theorem integral_sub_mulK {ε : Fin n → Bool} {f g h : KG ε → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    ∫ k, (f - g) k * h k ∂(muK ε) = ∫ k, f k * h k ∂(muK ε) - ∫ k, g k * h k ∂(muK ε) := by
  rw [← integral_sub (integrable_of_continuousK (f := fun k => f k * h k) (hf.mul hh))
    (integrable_of_continuousK (f := fun k => g k * h k) (hg.mul hh))]
  congr 1; funext k; simp [sub_mul]

theorem isKer_unique {ε : Fin n → Bool} {i : ℕ} {e e' : KG ε → ℂ} (he : IsKer ε i e) (he' : IsKer ε i e') :
    e = e' := by
  have hdmem : (e - e') ∈ polyV ε i := sub_mem he.1 he'.1
  have hc : Continuous (e - e') := continuous_of_mem hdmem
  have hce : Continuous e := continuous_of_mem he.1
  have hce' : Continuous e' := continuous_of_mem he'.1
  have hp : (fun k => star ((e - e') k)) ∈ polyV ε i := star_mem hdmem
  have horth : ∀ q ∈ lowV ε i, ∫ k, star (q k) * star ((e - e') k) ∂(muK ε) = 0 := by
    intro q hq
    have hqc : Continuous q := continuous_of_mem (lowV_le ε i hq)
    have h1 := he.2.1 q hq
    have h2 := he'.2.1 q hq
    have h3 : ∫ k, (e - e') k * q k ∂(muK ε) = 0 := by
      rw [integral_sub_mulK hce hce' hqc, h1, h2, sub_self]
    calc ∫ k, star (q k) * star ((e - e') k) ∂(muK ε)
        = ∫ k, (starRingEnd ℂ) ((e - e') k * q k) ∂(muK ε) := by
          congr 1; funext k; rw [map_mul, mul_comm]; rfl
      _ = (starRingEnd ℂ) (∫ k, (e - e') k * q k ∂(muK ε)) := integral_conj
      _ = 0 := by rw [h3, map_zero]
  have h0 : ∫ k, (e - e') k * star ((e - e') k) ∂(muK ε) = 0 := by
    have a1 := he.2.2 _ hp horth
    have a2 := he'.2.2 _ hp horth
    have hs : Continuous (fun k => star ((e - e') k)) := continuous_star.comp hc
    rw [integral_sub_mulK hce hce' hs, a1, a2, sub_self]
  have hns : Continuous (fun k => Complex.normSq ((e - e') k)) := Complex.continuous_normSq.comp hc
  have h1 : ∫ k, Complex.normSq ((e - e') k) ∂(muK ε) = 0 := by
    have : (fun k => (e - e') k * star ((e - e') k)) = fun k => ((Complex.normSq ((e - e') k) : ℝ) : ℂ) :=
      funext fun k => Complex.mul_conj _
    rw [this, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have h2 : (fun k => Complex.normSq ((e - e') k)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h1
  have h3 : (fun k => Complex.normSq ((e - e') k)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
  funext k
  have := congrFun h3 k
  simp only [Pi.zero_apply, map_eq_zero, Pi.sub_apply] at this
  exact sub_eq_zero.1 this

theorem conj_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k * a⁻¹)) ∈ polyV ε d := by
  have := mul_right_mem a⁻¹ (mul_left_mem a h)
  simpa only [mul_assoc] using this

theorem conj_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k * a⁻¹)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact conj_mem a h

theorem isKer_conj {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) (a : KG ε) :
    IsKer ε i (fun k => e (a * k * a⁻¹)) := by
  have key : ∀ f g : KG ε → ℂ, ∫ k, f (a * k * a⁻¹) * g k ∂(muK ε) = ∫ k, f k * g (a⁻¹ * k * a) ∂(muK ε) := by
    intro f g
    rw [← integral_conjK ε (fun k => f k * g (a⁻¹ * k * a)) a]
    congr 1; funext k
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨conj_mem a he.1, ?_, ?_⟩
  · intro q hq
    rw [key]
    have := conj_mem_low a⁻¹ hq
    simpa only [inv_inv] using he.2.1 _ this
  · intro p hp horth
    rw [key]
    have hp' : (fun k => p (a⁻¹ * k * a)) ∈ polyV ε i := by simpa only [inv_inv] using conj_mem a⁻¹ hp
    have horth' : ∀ q ∈ lowV ε i, ∫ k, star (q k) * p (a⁻¹ * k * a) ∂(muK ε) = 0 := by
      intro q hq
      rw [← integral_conjK ε (fun k => star (q k) * p (a⁻¹ * k * a)) a]
      have := horth _ (conj_mem_low a hq)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [he.2.2 _ hp' horth']
    simp

theorem isKer_class : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  intro n ε i e he a k
  have := isKer_unique (isKer_conj he a) he
  exact congrFun this k

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), GlobalTheory.KFourier.IsKer ε i e → ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  first | exact @GlobalTheory.KFourier.isKer_class | exact GlobalTheory.KFourier.isKer_class | (intros; apply GlobalTheory.KFourier.isKer_class <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRichSmall
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberIn

theorem finite_mem {K : Type} [Field K] [NumberField K] {a : 𝓞 K} (ha : a ≠ 0) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | a ∈ 𝔭.asIdeal}.Finite := by
  have h : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  refine (Ideal.finite_factors h).subset ?_
  intro 𝔭 h𝔭
  exact Ideal.dvd_span_singleton.2 h𝔭

theorem finite_norm_mem {K : Type} [Field K] [NumberField K] (S : Finset ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.absNorm 𝔭.asIdeal ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 K) | Ideal.absNorm I ≠ 0 ∧ Ideal.absNorm I ∈ S}.Finite := by
    refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (S.sup id)).subset ?_
    intro I hI
    exact Finset.le_sup (f := id) hI.2
  refine (h.preimage (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro 𝔭 h𝔭
  exact ⟨fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), h𝔭⟩

theorem numberField_adjoin (K L : IntermediateField ℚ ℂ) [NumberField L] (S : Set ℂ)
    [NumberField (IntermediateField.adjoin K S)] : NumberField (IntermediateField.adjoin L S) := by
  have h1 : FiniteDimensional ℚ ((IntermediateField.adjoin K S).restrictScalars ℚ) :=
    (inferInstance : FiniteDimensional ℚ (IntermediateField.adjoin K S))
  have hle : IntermediateField.adjoin ℚ S ≤ (IntermediateField.adjoin K S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin K S)
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have h3 : FiniteDimensional ℚ ((IntermediateField.adjoin L S).restrictScalars ℚ) := by
    have e := IntermediateField.restrictScalars_adjoin_eq_sup ℚ L S
    have h5 : FiniteDimensional ℚ (L ⊔ IntermediateField.adjoin ℚ S : IntermediateField ℚ ℂ) := inferInstance
    rw [← e] at h5
    exact h5
  have h4 : FiniteDimensional ℚ (IntermediateField.adjoin L S) := h3
  exact NumberField.mk

theorem weberSet_subset : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [_root_.NumberField.IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  intro K L _ _ _ h h2 hd P hP n hn hR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd P hP n hn
  haveI := numberField_adjoin K L (weberSet P n)
  have hn0 : (n : 𝓞 L) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  haveI : NumberField (⊥ : IntermediateField L ℂ) := NumberField.of_module_finite L _
  have hle : IntermediateField.adjoin L (weberSet P n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split L ℂ ⊥ (IntermediateField.adjoin L (weberSet P n)) ?_
    refine ((finite_mem hn0).union (finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hR 𝔓 hc.1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K L h (weberSet P n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1)
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin L _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberIn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFiStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [_root_.NumberField.IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  first | exact @GlobalTheory.FieldSize.WeberIn.weberSet_subset | exact GlobalTheory.FieldSize.WeberIn.weberSet_subset | (intros; apply GlobalTheory.FieldSize.WeberIn.weberSet_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {f | ∃ d, ⇑f ∈ polyV ε d}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using mul_mem ha hb⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by simpa using add_mem (polyV_mono ε (le_max_left a b) ha) (polyV_mono ε (le_max_right a b) hb)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨0, ?_⟩
    convert const_mem ε 0 c using 1
    funext k; simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert star_mem ha using 1
    funext k; rfl

theorem toMK_injective (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  have h1 : ((a : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((b : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := Units.ext h
  exact Subtype.ext (Subtype.ext h1)

theorem polyAlg_separatesPoints (ε : Fin n → Bool) : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective ε h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  refine ⟨_, ⟨⟨coord ε (i, j, true), continuous_coord ε _⟩, ⟨1, show coord ε (i, j, true) ∈ polyV ε 1 from coord_mem ε _⟩, rfl⟩, ?_⟩
  simpa [coord] using hij

theorem polyAlg_dense (ε : Fin n → Bool) : (polyAlg ε).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_separatesPoints ε)

theorem integrable_cont (ε : Fin n → Bool) (F : C(KG ε, ℂ)) : Integrable F (muK ε) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_integral_cont (ε : Fin n → Bool) :
    Continuous fun F : C(KG ε, ℂ) => ∫ k, F k ∂(muK ε) := by
  refine (LipschitzWith.of_dist_le_mul fun F G => ?_).continuous (K := 1)
  rw [dist_eq_norm, ← integral_sub (integrable_cont ε F) (integrable_cont ε G)]
  have h := norm_integral_le_of_norm_le_const (μ := muK ε) (C := ‖F - G‖)
    (Filter.Eventually.of_forall fun k => by
      simpa using ContinuousMap.norm_coe_le_norm (F - G) k)
  simpa [probReal_univ, dist_eq_norm] using h

theorem eq_zero_of_orth_poly : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  intro n ε h hc horth
  let H : C(KG ε, ℂ) := ⟨h, hc⟩
  let Φ : C(KG ε, ℂ) → ℂ := fun F => ∫ k, star (F k) * h k ∂(muK ε)
  have hΦ : Continuous Φ := by
    have : Continuous fun F : C(KG ε, ℂ) => star F * H := (continuous_star).mul continuous_const
    exact (continuous_integral_cont ε).comp this
  have hclosed : IsClosed {F : C(KG ε, ℂ) | Φ F = 0} := isClosed_eq hΦ continuous_const
  have hsub : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {F | Φ F = 0} := by
    rintro F ⟨d, hd⟩
    exact horth d _ hd
  have hcl : closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) = Set.univ := by
    have := polyAlg_dense ε
    rw [← StarSubalgebra.topologicalClosure_coe, this]
    rfl
  have hH : Φ H = 0 := by
    have : H ∈ closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by rw [hcl]; trivial
    exact hclosed.closure_subset_iff.mpr hsub this

  have hint : ∫ k, (Complex.normSq (h k) : ℂ) ∂(muK ε) = 0 := by
    have e : (fun k => (Complex.normSq (h k) : ℂ)) = fun k => star (h k) * h k := by
      funext k; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [e]; exact hH
  have hint' : ∫ k, Complex.normSq (h k) ∂(muK ε) = 0 := by
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hnn : 0 ≤ᵐ[muK ε] fun k => Complex.normSq (h k) := Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
  have hcn : Continuous fun k => Complex.normSq (h k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint'
  have hz : (fun k => Complex.normSq (h k)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hcn continuous_const).mp hae
  funext k
  have := congrFun hz k
  simpa using this

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFunStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_compactUnitaryPolyFun : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  first | exact @GlobalTheory.KFourier.eq_zero_of_orth_poly | exact GlobalTheory.KFourier.eq_zero_of_orth_poly | (intros; apply GlobalTheory.KFourier.eq_zero_of_orth_poly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integrable_of_continuous' {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem eq_zero_of_integral_mul_star {ε : Fin n → Bool} {φ : KG ε → ℂ} (hc : Continuous φ)
    (h : ∫ k, φ k * star (φ k) ∂(muK ε) = 0) : φ = 0 := by
  have e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ) := by
    funext k; exact Complex.mul_conj (φ k)
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hcs : Continuous fun k => Complex.normSq (φ k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k))
    (integrable_of_continuous' hcs)).1 h
  have h2 : (fun k => Complex.normSq (φ k)) = 0 := (Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae
  funext k
  have := congrFun h2 k
  simpa using this

theorem exists_isKer (ε : Fin n → Bool) (i : ℕ) : ∃ e, IsKer ε i e := by
  classical
  have hlow : lowV ε i ≤ polyV ε i := by
    cases i with
    | zero => simp [lowV]
    | succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)
  let W : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun q hq => ?_⟩
        have hq' := continuous_of_mem (hlow hq)
        have h1 := integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k)
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha)))
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))
        simp only [Pi.add_apply, mul_add]
        rw [h1, ha' q hq, hb' q hq, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ha' q hq, mul_zero] }
  have hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0 :=
    fun p => Iff.rfl

  let B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i) :=
    LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε))
      (fun e e' p => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuous_of_mem p.2)))
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e p p' => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p'.2)))
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro e he
    have h0 := hB e ⟨_, star_mem e.2⟩
    rw [he] at h0
    have hz : (e : KG ε → ℂ) = 0 := eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm
    exact Subtype.ext hz
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj

  let f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i := (lowV ε i).mkQ ∘ₗ W.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwl : (w : KG ε → ℂ) ∈ lowV ε i := (Submodule.Quotient.mk_eq_zero _).1 hw
    have h0 := ((hW w).1 w.2).2 _ hwl
    have hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) =
        fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k) := funext fun k => mul_comm _ _
    rw [hc] at h0
    exact Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let g : (KG ε → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ
  have hgW : ∀ w ∈ W, g w = w 1 := by
    intro w hw
    have := LinearMap.congr_fun hr ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]
  have hgU : ∀ q ∈ lowV ε i, g q = 0 := by
    intro q hq
    simp only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero,
      LinearMap.proj_apply]
  obtain ⟨e, he⟩ := hsurj (g ∘ₗ (polyV ε i).subtype)
  refine ⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩
  · have := LinearMap.congr_fun he ⟨q, hlow hq⟩
    rw [hB] at this
    rw [this]
    exact hgU q hq
  · have := LinearMap.congr_fun he ⟨p, hp⟩
    rw [hB] at this
    rw [this]
    exact hgW p ⟨hp, hpo⟩

end GlobalTheory.KFourier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactUnitary_fourierKernel : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ), ∃ e, GlobalTheory.KFourier.IsKer ε i e := by
  first | exact @GlobalTheory.KFourier.exists_isKer | exact GlobalTheory.KFourier.exists_isKer | (intros; apply GlobalTheory.KFourier.exists_isKer <;> assumption)
end
end
