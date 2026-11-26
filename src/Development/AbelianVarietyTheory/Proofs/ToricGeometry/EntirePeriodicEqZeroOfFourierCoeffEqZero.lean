module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
open Complex Matrix Filter Topology
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory

theorem apply_add_intCast_of_periodic_single {g : ℕ} {β : Type*} {A : (Fin g → ℝ) → β}
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x) (n : Fin g → ℤ) (x : Fin g → ℝ) :
    A (x + fun i => (n i : ℝ)) = A x := by
  have h1 : (fun i => (n i : ℝ)) = ∑ i, n i • (Pi.single i 1 : Fin g → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1]
  have h2 : ∀ s : Finset (Fin g),
      Function.Periodic A (∑ i ∈ s, n i • (Pi.single i 1 : Fin g → ℝ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Function.Periodic.zsmul (hA a) (n a)).add_period ih
  exact h2 _ x

theorem eq_zero_of_cube_fourierCoeff_eq_zero {g : ℕ} {A : (Fin g → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x)
    (h : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) (y : Fin g → ℝ) :
    A y = 0 := by
  set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← apply_add_intCast_of_periodic_single hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus (Fin g), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = 0 := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, ← h n]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact summable_zero) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hcoeff, zero_smul, hfp] at hsum
  exact hsum.unique hasSum_zero

theorem entire_periodic_eq_zero_of_fourierCoeff_eq_zero :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) := by
  intro H g f hf hper h0
  funext w
  have hc := hf.continuous
  have := eq_zero_of_cube_fourierCoeff_eq_zero (A := fun x => f ((fun i => (x i : ℂ)) + w))
    (by fun_prop) (fun i x => by
      rw [← hper i ((fun i => (x i : ℂ)) + w)]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp; ring
      · simp [hj])
    (fun m => by rw [H g f hf hper m w, h0 m, mul_zero]) 0
  have h1 : (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ)) + w = w := by
    funext j; simp
  rw [h1] at this
  exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ClassicalTheta

theorem forall_of_box_of_translate {g n : ℕ} (hn : 1 ≤ n) (P : (Fin g → ℤ) → Prop)
    (hP : ∀ m j, P (m + Pi.single j (n : ℤ)) ↔ P m)
    (hbox : ∀ r : Fin g → Fin n, P (fun i => ((r i : ℕ) : ℤ))) (m : Fin g → ℤ) : P m := by
  have h1 : ∀ (j : Fin g) (k : ℤ) (m : Fin g → ℤ), P (m + Pi.single j (k * n)) ↔ P m := by
    intro j k
    induction k using Int.induction_on with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have : m + Pi.single j (((k : ℤ) + 1) * n) =
          (m + Pi.single j ((k : ℤ) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [this, hP, ih]
    | pred k ih =>
      intro m
      have : m + Pi.single j ((-(k : ℤ)) * n) =
          (m + Pi.single j ((-(k : ℤ) - 1) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [← ih m, this, hP]
  have h2 : ∀ (k : Fin g → ℤ) (s : Finset (Fin g)) (m : Fin g → ℤ),
      P (m + ∑ j ∈ s, Pi.single j (k j * n)) ↔ P m := by
    intro k s
    induction s using Finset.induction_on with
    | empty => intro m; simp
    | insert a s ha ih =>
      intro m
      rw [Finset.sum_insert ha, add_comm (Pi.single a _), ← add_assoc, h1, ih]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let r : Fin g → Fin n := fun i => ⟨(m i % n).toNat, by
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    have h1 := Int.emod_lt_of_pos (m i) hn'
    omega⟩
  have hm : m = (fun i => ((r i : ℕ) : ℤ)) + ∑ j, Pi.single j (m j / n * n) := by
    rw [Finset.univ_sum_single (fun j => m j / n * n)]
    funext i
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    simp only [r, Pi.add_apply, Int.toNat_of_nonneg h0]
    have := Int.emod_add_mul_ediv (m i) n
    linarith
  rw [hm, h2]
  exact hbox r

theorem card_le_pow_of_linearIndependent :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro hshift huniq g n τ b hn hb N f hf hli
  let c : ((Fin g → ℂ) → ℂ) → (Fin g → ℤ) → ℂ := fun F m =>
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, F (fun i => (x i : ℂ)) *
      cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))
  have key : ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F →
      (∀ (i : Fin g) z, F (z + Pi.single i 1) = F z) →
      (∀ (j : Fin g) z, F (z + τ.mulVec (Pi.single j 1)) =
        b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * F z) →
      (∀ r : Fin g → Fin n, c F (fun i => ((r i : ℕ) : ℤ)) = 0) → F = 0 := by
    intro F hd hp hl hbox
    refine huniq g F hd hp (forall_of_box_of_translate hn (fun m => c F m = 0) ?_ hbox)
    intro m j
    have h := hshift g F hd hp m (τ.mulVec (Pi.single j 1))
    have h' : (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
        F ((fun i => (x i : ℂ)) + τ.mulVec (Pi.single j 1)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
        b j ^ n * c F (m + Pi.single j (n : ℤ)) := by
      simp only [c]
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext x
      have hs : ∑ i, (((m + Pi.single j (n : ℤ) : Fin g → ℤ) i : ℤ) : ℂ) * (x i : ℂ) =
          n * (x j : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ) := by
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · simp
      rw [hl, hs, mul_add, Complex.exp_add, mul_assoc (-(2 * Real.pi * I) : ℂ)]
      ring
    rw [h'] at h
    change _ = _ * c F m at h
    have hb' : b j ^ n ≠ 0 := pow_ne_zero _ (hb j)
    constructor
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (Complex.exp_ne_zero _)
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hb'
  let v : Fin N → (Fin g → Fin n) → ℂ := fun k r => c (f k) (fun i => ((r i : ℕ) : ℤ))
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    apply hli a
    apply key
    · exact Differentiable.sum fun k _ => (hf k).1.const_smul (a k)
    · intro i z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.1]
    · intro j z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.2, Finset.mul_sum, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    · intro r
      have har := congrFun ha r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, c] at har
      rw [← har]
      simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← MeasureTheory.integral_const_mul]
        simp only [mul_assoc]
      · intro k _
        have hk := (hf k).1.continuous
        refine ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)
        fun_prop
  have := hv.fintype_card_le_finrank
  simpa using this

end GlobalTheory.ClassicalTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory
namespace AppellHumbert


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.AppellHumbert.exists_real_extension {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : Λ →+ W) : ∃ F : (Fin g → ℂ) →ₗ[ℝ] W, ∀ l : Λ, F l = f l := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  refine ⟨bR.constr ℝ (fun i => f (b i)), fun l => ?_⟩
  have key : ((bR.constr ℝ (fun i => f (b i))).restrictScalars ℤ ∘ₗ Λ.subtype) =
      f.toIntLinearMap := by
    refine b.ext fun i => ?_
    show bR.constr ℝ (fun i => f (b i)) (b i : Fin g → ℂ) = f (b i)
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key l

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.AppellHumbert.eq_sum_re_im {g : ℕ} (u : Fin g → ℂ) :
    u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin g → ℂ)
      + (u j).im • (Pi.single j I : Fin g → ℂ)) := by
  ext i
  simp [Finset.sum_apply, Finset.sum_add_distrib, Pi.single_apply, Complex.re_add_im]

end AppellHumbert


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.appellHumbert_normal_form_of_linear_exponent :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) := by
  intro g Λ hdisc hΛ a B ha hcoc
  classical
  haveI := hdisc
  let b : Λ →+ (Fin g → ℂ) :=
    { toFun := fun l j => B l (Pi.single j 1)
      map_zero' := by ext j; simp
      map_add' := fun l m => by ext j; simp }
  obtain ⟨F, hF0⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ b
  have hF : ∀ (l : Λ) z, B l z = F l ⬝ᵥ z := by
    intro l z
    rw [hF0]
    conv_lhs => rw [show z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) by ext i; simp [Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, dotProduct, b, mul_comm]
  have hskew : ∀ l m : Λ, ∃ n : ℤ, B l m = B m l + n * (2 * π * I) := by
    intro l m
    have h := hcoc l m
    rw [add_comm, hcoc m l, mul_comm (a m) (a l)] at h
    exact Complex.exp_eq_exp_iff_exists_int.mp (mul_left_cancel₀ (mul_ne_zero (ha l) (ha m)) h).symm
  have hlin : ∀ (P : (Fin g → ℂ) → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ (c : ℝ) x, P x → P (c • x)) → (∀ l : Λ, P l) → ∀ x, P x := by
    intro P h0 hadd hsmul hl x
    have hx : x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact hl ⟨y, hy⟩
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd y z hy hz
    | smul c y _ hy => exact hsmul c y hy
  have hD1 : ∀ u (m : Λ), (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0 := by
    intro u m
    refine hlin (fun u => (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun l => ?_) u
    · simp only [map_add (f := _), add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
    · obtain ⟨n, hn⟩ := hskew l m
      rw [← hF, ← hF, hn]; simp
  have hD : ∀ u v, (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0 := by
    intro u v
    refine hlin (fun v => (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun m => hD1 u m) v
    · simp only [map_add (f := _), add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
  let M : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j - I * F (Pi.single k I) j)
  let N : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j + I * F (Pi.single k I) j)
  have hFMN : ∀ u, F u = u ᵥ* M + star u ᵥ* N := by
    intro u; ext j
    conv_lhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, vecMul,
      dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply Complex.ext <;> simp [M, N, Complex.mul_re, Complex.mul_im] <;> ring
  have hsym : ∀ k j, (F (Pi.single k 1) j).re = (F (Pi.single j 1) k).re ∧
      (F (Pi.single k I) j).im = (F (Pi.single j I) k).im ∧
      (F (Pi.single k I) j).re = -(F (Pi.single j 1) k).im := by
    intro k j
    have h1 := hD (Pi.single k 1) (Pi.single j 1)
    have h2 := hD (Pi.single k I) (Pi.single j I)
    have h3 := hD (Pi.single k I) (Pi.single j 1)
    simp only [dotProduct_single, mul_one, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub, sub_zero] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hMsym : Mᵀ = M := by
    ext k j
    rw [transpose_apply]
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [M, Complex.mul_re, Complex.mul_im] <;> linarith
  have hNherm : ∀ i j, (starRingEnd ℂ) (N i j) = N j i := by
    intro k j
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [N, Complex.mul_re, Complex.mul_im] <;> linarith

  let A : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun u v => u ⬝ᵥ M *ᵥ v
  let K : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z u => z ⬝ᵥ Nᵀ *ᵥ star u
  have hAsym : ∀ u v, A u v = A v u := by
    intro u v
    simp only [A]
    conv_rhs => rw [← hMsym]
    rw [mulVec_transpose, dotProduct_comm v, ← dotProduct_mulVec]
  have hBF : ∀ (l : Λ) z, B l z = A l z + K z l := by
    intro l z
    simp only [A, K]
    rw [hF, hFMN, add_dotProduct, dotProduct_mulVec, mulVec_transpose, dotProduct_comm z]
  have hKherm : ∀ u v, K v u = (starRingEnd ℂ) (K u v) := by
    intro u v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [K, dotProduct, mulVec, transpose_apply, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj, hNherm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAadd : ∀ u v, A (u + v) (u + v) = A u u + A u v + A u v + A v v := by
    intro u v
    have := hAsym v u
    simp only [A, mulVec_add, dotProduct_add, add_dotProduct] at this ⊢
    rw [this]; ring
  have hKadd : ∀ u v, K (u + v) (u + v) = K u u + K u v + K v u + K v v := by
    intro u v
    simp only [K, star_add, mulVec_add, dotProduct_add, add_dotProduct]
    ring

  let Hm : Matrix (Fin g) (Fin g) ℂ := (Real.pi⁻¹ : ℝ) • Nᵀ
  have hHmK : ∀ x y, (Real.pi : ℂ) * (x ⬝ᵥ Hm *ᵥ star y) = K x y := by
    intro x y
    simp only [Hm, K, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.ofReal_inv]
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hHerm : Hm.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [Hm, hNherm]
  have hint : ∀ l m : Λ, ∃ n : ℤ, ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = n := by
    intro l m
    obtain ⟨n, hn⟩ := hskew l m
    rw [hBF, hBF, hAsym m l, hKherm l m] at hn
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have h1 : Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = (K l m).im := by
      rw [← hHmK]; simp
    refine ⟨-n, ?_⟩
    push_cast
    apply mul_left_cancel₀ Real.pi_pos.ne'
    rw [h1]; linarith
  choose e he using hint
  have headd1 : ∀ l l' m, e (l + l') m = e l m + e l' m := by
    intro l l' m
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, add_dotProduct, Complex.add_im]
  have headd2 : ∀ l m m', e l (m + m') = e l m + e l m' := by
    intro l m m'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, star_add, mulVec_add, dotProduct_add, Complex.add_im]
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ e headd1
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun l => e l m) (fun l l' => headd1 l l' m)) c l)
    headd2
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun m => e l m) (fun m m' => headd2 l m m')) c m)
  have ha0 : a 0 = 1 := by
    have h := hcoc 0 0
    rw [add_zero, map_zero, LinearMap.zero_apply, Complex.exp_zero, mul_one] at h
    exact mul_left_cancel₀ (ha 0) (h.symm.trans (mul_one (a 0)).symm)
  let φ0 : Λ →+ ℝ :=
    { toFun := fun l => Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2
      map_zero' := by simp [ha0, A, K]
      map_add' := fun l m => by
        rw [hcoc, norm_mul, norm_mul, Complex.norm_exp,
          Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)))
            (Real.exp_pos _).ne',
          Real.log_mul (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)), Real.log_exp,
          Submodule.coe_add, hAadd, hKadd, hBF, hKherm (l : Fin g → ℂ) m]
        simp only [Complex.add_re, Complex.conj_re]
        ring }
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ φ0
  let c : Fin g → ℂ := fun j => (φ (Pi.single j 1) : ℂ) - I * φ (Pi.single j I)
  have hc : ∀ u, (c ⬝ᵥ u).re = φ u := by
    intro u
    conv_rhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_add (f := _), map_smul, smul_eq_mul, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [c, Complex.mul_re]
    ring
  let χ : Λ → ℂ := fun l => a l * cexp (-(A l l) / 2 - K l l / 2) * cexp (-(c ⬝ᵥ (l : Fin g → ℂ)))
  have hχ : ∀ l, ‖χ l‖ = 1 := by
    intro l
    have h1 : (c ⬝ᵥ (l : Fin g → ℂ)).re = Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2 := by
      rw [hc, hφ]; rfl
    simp only [χ, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re,
      h1, mul_assoc, ← Real.exp_add]
    rw [show -(A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2 +
        -(Real.log ‖a l‖ - (A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2) = -Real.log ‖a l‖ by ring,
      Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (ha l))]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ha l))
  let Q : (Fin g → ℂ) → ℂ := fun z => A z z / 2 + c ⬝ᵥ z
  refine ⟨Hm, χ, Ef, Q, hHerm, hχ, fun l m => (he l m).symm, ?_, by simp [Q, A], ?_⟩
  · simp only [Q, A, dotProduct, mulVec]
    fun_prop
  · intro l z
    have hQ : Q z - Q (z + l) = -A l z - A l l / 2 - c ⬝ᵥ l := by
      simp only [Q, dotProduct_add]
      rw [hAadd, hAsym z l]; ring
    have h2 : (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (l : Fin g → ℂ)) = K l l / 2 := by
      rw [← hHmK]; ring
    rw [hHmK, h2, mul_assoc, ← Complex.exp_add, hBF, hQ]
    simp only [χ]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
theorem _root_.GlobalTheory.card_le_pow_of_linearIndependent_theta_principal :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∃ (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (τ : Matrix (Fin g) (Fin g) ℂ) (Q : (Fin g → ℂ) → ℂ) (b : Fin g → ℂ), τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z, φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ (∀ j, b j ≠ 0) ∧ (∀ (i : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (Pi.single i 1) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = cexp (Q (z + Pi.single i 1) - Q z)) ∧ (∀ (j : Fin g) (l : Λ) z, (l : Fin g → ℂ) = φ (τ.mulVec (Pi.single j 1)) → (χ l * cexp (Real.pi * (φ z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) = b j * cexp (-(2 * Real.pi * I) * z j) * cexp (Q (z + τ.mulVec (Pi.single j 1)) - Q z))) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro H1 H2 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij n hn N f hf hind
  obtain ⟨φ, τ, Q, b, -, -, hΛ, hQd, -, hb, hQ1, hQ2⟩ :=
    H1 g Λ hdisc hspan Hm χ Ef hH hpos hχ hEf hbij
  let T : ((Fin g → ℂ) → ℂ) →ₗ[ℂ] ((Fin g → ℂ) → ℂ) :=
    { toFun := fun h z => h (φ z) * cexp (-((n : ℂ) * Q z))
      map_add' := fun h h' => by funext z; simp [add_mul]
      map_smul' := fun c h => by funext z; simp [mul_assoc] }
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro h hh
    funext w
    have hw := congr_fun hh (φ.symm w)
    change h (φ (φ.symm w)) * cexp (-((n : ℂ) * Q (φ.symm w))) = 0 at hw
    rw [φ.apply_symm_apply] at hw
    exact (mul_eq_zero.mp hw).resolve_right (Complex.exp_ne_zero _)
  refine H2 g n τ b hn hb N (T ∘ f) (fun k => ⟨?_, fun i z => ?_, fun j z => ?_⟩) (hind.map' T hT)
  · change Differentiable ℂ (fun z => f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hφd : Differentiable ℂ (LinearMap.toContinuousLinearMap φ.toLinearMap) :=
      (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
    exact ((hf k).1.comp hφd).mul ((hQd.const_mul _).neg.cexp)
  · change f k (φ (z + Pi.single i 1)) * cexp (-((n : ℂ) * Q (z + Pi.single i 1))) =
      f k (φ z) * cexp (-((n : ℂ) * Q z))
    have hs : (fun j => (((Pi.single i 1 : Fin g → ℤ) j : ℤ) : ℂ)) = Pi.single i 1 := by
      ext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    have hmem : φ (Pi.single i 1) ∈ Λ := (hΛ _).mpr ⟨Pi.single i 1, 0, by
      rw [hs]; ext j; simp [Matrix.mulVec, dotProduct]⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (Pi.single i 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add (f := _), ← hl, (hf k).2 l, hQ1 i l z hl, ← Complex.exp_nat_mul]
    have key : cexp (↑n * (Q (z + Pi.single i 1) - Q z)) * cexp (-(↑n * Q (z + Pi.single i 1))) =
        cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    linear_combination f k (φ z) * key
  · change f k (φ (z + τ *ᵥ Pi.single j 1)) * cexp (-((n : ℂ) * Q (z + τ *ᵥ Pi.single j 1))) =
      b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k (φ z) * cexp (-((n : ℂ) * Q z)))
    have hs : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
      ext i; by_cases hi : i = j <;> simp [Pi.single_apply, hi]
    have hmem : φ (τ *ᵥ Pi.single j 1) ∈ Λ := (hΛ _).mpr ⟨0, Pi.single j 1, by
      rw [hs]; ext i; simp⟩
    obtain ⟨l, hl⟩ : ∃ l : Λ, (l : Fin g → ℂ) = φ (τ *ᵥ Pi.single j 1) := ⟨⟨_, hmem⟩, rfl⟩
    rw [map_add (f := _), ← hl, (hf k).2 l, hQ2 j l z hl, mul_pow, mul_pow, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul]
    have key : cexp (↑n * (-(2 * ↑Real.pi * I) * z j)) *
        cexp (↑n * (Q (z + τ *ᵥ Pi.single j 1) - Q z)) *
        cexp (-(↑n * Q (z + τ *ᵥ Pi.single j 1))) =
        cexp (-(2 * ↑Real.pi * I) * ↑n * z j) * cexp (-(↑n * Q z)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (b j ^ n * f k (φ z)) * key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaPositivity

variable {g : ℕ}


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    w ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.form_add_self {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    ((z + w) ⬝ᵥ Hm.mulVec (star (z + w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (z ⬝ᵥ Hm.mulVec (star w)).re
        + (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    _root_.GlobalTheory.ThetaPositivity.form_conj hH z w]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma continuous_re_dotProduct_mulVec_star (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ Hm.mulVec (star z)).re) :=
  Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.exists_norm_le (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) :
    ∃ C : ℝ, ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
  classical
  set F : (Fin g → ℂ) → ℝ := fun z =>
    ‖θ z‖ * Real.exp (-(Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)) with hFdef
  have hF : Continuous F :=
    hθ.norm.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_re_dotProduct_mulVec_star Hm)).neg))
  have hper : ∀ (l : Λ) z, F (z + l) = F z := by
    intro l z
    have hre : ∀ a b : ℂ, ((Real.pi : ℂ) * a + Real.pi / 2 * b).re
        = Real.pi * a.re + Real.pi / 2 * b.re := fun a b => by
      simp [Complex.add_re, Complex.re_ofReal_mul]
    simp only [hFdef, htr, norm_mul, hχ, one_mul, Complex.norm_exp, hre,
      _root_.GlobalTheory.ThetaPositivity.form_add_self hH]
    rw [mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  have hK : IsCompact (closure (ZSpan.fundamentalDomain bR)) :=
    (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun z => ?_⟩
  have hmem : ((ZSpan.floor bR z : Submodule.span ℤ (Set.range bR)) : Fin g → ℂ) ∈ Λ := by
    exact (Module.Basis.ofZLatticeBasis_span ℝ Λ b).le (ZSpan.floor bR z).2
  have hz : F z = F (ZSpan.fract bR z) := by
    have := hper ⟨_, hmem⟩ (ZSpan.fract bR z)
    rw [← this, ZSpan.fract_apply]
    simp
  have hbd : F z ≤ C := by
    rw [hz]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain bR z)))
  have hexp := Real.exp_pos (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)
  calc ‖θ z‖ = F z * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
        rw [hFdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) :=
        mul_le_mul_of_nonneg_right hbd hexp.le

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma re_form_add_smul_of_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) (t : ℂ) :
    ((z + t • w) ⬝ᵥ Hm.mulVec (star (z + t • w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (star t * (z ⬝ᵥ Hm.mulVec (star w))).re
        + Complex.normSq t * (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [_root_.GlobalTheory.ThetaPositivity.form_add_self hH]
  have h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) =
      (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]
  rw [h1, h2, Complex.re_ofReal_mul]


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
lemma _root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {C : ℝ}
    (hC : ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re))
    {w : Fin g → ℂ} (hw : (w ⬝ᵥ Hm.mulVec (star w)).re < 0) : θ = 0 := by
  funext z
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have hp := Real.exp_pos (Real.pi / 2 * ((0 : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star 0)).re)
    nlinarith [norm_nonneg (θ 0)]
  set a := -(w ⬝ᵥ Hm.mulVec (star w)).re with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set A := (z ⬝ᵥ Hm.mulVec (star z)).re with hA
  set B := ‖z ⬝ᵥ Hm.mulVec (star w)‖ with hB
  set f : ℂ → ℂ := fun t => θ (z + t • w) with hfdef
  have hf : Differentiable ℂ f :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))
  have hbound : ∀ t, ‖f t‖ ≤ C * Real.exp (Real.pi / 2 * (A + 2 * B * ‖t‖ - a * ‖t‖ ^ 2)) := by
    intro t
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [re_form_add_smul_of_isHermitian hH, Complex.normSq_eq_norm_sq]
    have h : (star t * (z ⬝ᵥ Hm.mulVec (star w))).re ≤ ‖t‖ * B := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
    nlinarith
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (Real.pi / 2 * (A + 2 * B * r - a * r ^ 2)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => (A + 2 * B ^ 2 / a) + (-(a / 2)) * r ^ 2) atTop atBot :=
      tendsto_atBot_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
    have h1 : Tendsto (fun r : ℝ => A + 2 * B * r - a * r ^ 2) atTop atBot := by
      refine tendsto_atBot_mono (fun r => ?_) h2
      have key : 2 * B ^ 2 / a + a / 2 * r ^ 2 - 2 * B * r = (a * r - 2 * B) ^ 2 / (2 * a) := by
        field_simp
        ring
      have : 0 ≤ (a * r - 2 * B) ^ 2 / (2 * a) := by positivity
      nlinarith
    have h3 := Real.tendsto_exp_atBot.comp (h1.const_mul_atBot (by positivity : 0 < Real.pi / 2))
    simpa using h3.const_mul C
  have hf0 : Tendsto f (cocompact ℂ) (𝓝 0) :=
    squeeze_zero_norm hbound (hlim.comp tendsto_norm_cocompact_atTop)
  have := hf.apply_eq_of_tendsto_cocompact 0 hf0
  simpa [hfdef] using this


open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
theorem _root_.GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
        (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
        (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) →
        Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 →
        (∀ (l : Λ) z, θ (z + l) =
          (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
            Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) →
        ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hdisc hspan Hm χ Ef θ hH hχ hE hinj hθ hθ0 htr z hz
  classical
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hpsd : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := by
    intro w
    by_contra hw
    push_neg at hw
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
    exact hθ0 (_root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg hH hθ hC hw)
  refine lt_of_le_of_ne (hpsd z) (fun hz0 => hz ?_)
  have him : ∀ v : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star v)).im = 0 := by
    intro v
    have key : ∀ s : ℝ, 0 ≤ 2 * s * (z ⬝ᵥ Hm.mulVec (star v)).im
        + s ^ 2 * (v ⬝ᵥ Hm.mulVec (star v)).re := by
      intro s
      have h := hpsd (z + ((s : ℂ) * Complex.I) • v)
      rw [re_form_add_smul_of_isHermitian hH, ← hz0] at h
      have e1 : (star ((s : ℂ) * Complex.I) * (z ⬝ᵥ Hm.mulVec (star v))).re =
          s * (z ⬝ᵥ Hm.mulVec (star v)).im := by
        simp [Complex.mul_re]
      have e2 : Complex.normSq ((s : ℂ) * Complex.I) = s ^ 2 := by simp [sq]
      rw [e1, e2] at h
      linarith
    set c := (z ⬝ᵥ Hm.mulVec (star v)).im
    set d := (v ⬝ᵥ Hm.mulVec (star v)).re
    have hd1 : 0 < d + 1 := by linarith [hpsd v]
    have h' : 0 ≤ -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
      have e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
        field_simp
        ring
      linarith [key (-c / (d + 1))]
    rw [neg_div, neg_nonneg, div_le_iff₀ (by positivity), zero_mul] at h'
    have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg c, hpsd v]
    exact (pow_eq_zero_iff two_ne_zero).mp hc2
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  let M : Matrix _ _ ℤ := Matrix.of fun i j => Ef (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have hl : Ef (b.equivFun.symm c) = 0 := by
      refine b.ext fun j => ?_
      have := congrFun hc j
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M] using this
    have := hinj (hl.trans (map_zero Ef).symm)
    have h2 := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  have hr : (fun i => bR.repr z i) ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
    funext j
    have h := him (b j : Fin g → ℂ)
    rw [← bR.sum_repr z] at h
    simp only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im,
      Module.Basis.ofZLatticeBasis_apply, bR, ← hE] at h
    simpa [Matrix.vecMul, dotProduct, M] using h
  have hdetR : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have e : (M.map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ M.det := (RingHom.map_det _ _).symm
    simpa using e ▸ (Int.cast_ne_zero.mpr hdet)
  have hr0 : (fun i => bR.repr z i) = 0 := by
    by_contra hne
    exact hdetR (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hr⟩)
  have hz' : bR.repr z = 0 := by
    ext i
    exact congrFun hr0 i
  simpa using hz'

end GlobalTheory.ThetaPositivity
end
