module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantOneRowExpansion

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def selL {D E : ℕ} (σ : Fin E → Fin D) : (Fin D → ℂ) →L[ℂ] (Fin E → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (σ a)

theorem selL_apply {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) (a : Fin E) :
    selL σ z a = z (σ a) := rfl

theorem jacC_selL {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.A.jacC (selL σ) z = Matrix.of fun a k => if σ a = k then (1 : ℂ) else 0 := by
  ext a k
  simp [ReciprocityTheory.AnForm.A.jacC, ContinuousLinearMap.fderiv, selL_apply, Pi.single_apply]

theorem hessC_selL_apply {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i j : Fin D) :
    hessC (φ ∘ selL σ) z i j = ∑ b, (∑ a, (if σ a = i then (1 : ℂ) else 0) *
      hessC φ (selL σ z) a b) * (if σ b = j then (1 : ℂ) else 0) := by
  rw [ReciprocityTheory.AnForm.A.hessC_comp φ (selL σ) z ((selL σ).analyticAt z) hφ, jacC_selL]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  split_ifs <;> simp

theorem hessC_selL_inj {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) {σ : Fin E → Fin D}
    (hσ : Function.Injective σ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (a b : Fin E) :
    hessC (φ ∘ selL σ) z (σ a) (σ b) = hessC φ (selL σ z) a b := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hσ.eq_iff]

theorem hessC_selL_left {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) {i : Fin D} (hi : ∀ a, σ a ≠ i) (j : Fin D) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hi]

theorem hessC_selL_right {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i : Fin D) {j : Fin D} (hj : ∀ a, σ a ≠ j) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hj]

theorem contDiffAt_comp_selL {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) : ContDiffAt ℝ 2 (φ ∘ selL σ) z :=
  ContDiffAt.comp z hφ ((selL σ).restrictScalars ℝ).contDiff.contDiffAt

def selA {d : ℕ} (c : Fin (d + 2)) : Fin (d + 1) → Fin (d + 2) :=
  Fin.cons c fun i : Fin d => i.succ.succ

def selT {d : ℕ} : Fin d → Fin (d + 2) := fun i => i.succ.succ

theorem selT_injective {d : ℕ} : Function.Injective (selT (d := d)) := fun a b h =>
  Fin.succ_injective _ (Fin.succ_injective _ h)

theorem selA_injective {d : ℕ} {c : Fin (d + 2)} (hc : ∀ i : Fin d, i.succ.succ ≠ c) :
    Function.Injective (selA c) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => exact absurd h.symm (by simpa [selA] using hc b)
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd h (by simpa [selA] using hc a)
    | succ b =>
      have : a.succ.succ = b.succ.succ := by simpa [selA] using h
      rw [Fin.succ_injective _ (Fin.succ_injective _ this)]

theorem selA_eq_cons {d : ℕ} (c : Fin (d + 2)) (z : Fin (d + 2) → ℂ) :
    selL (selA c) z = Fin.cons (z c) (Fin.tail (Fin.tail z)) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [selL_apply, selA]
  | succ a => simp [selL_apply, selA, Fin.tail]

theorem selT_eq_tail {d : ℕ} (z : Fin (d + 2) → ℂ) :
    selL selT z = Fin.tail (Fin.tail z) := rfl

theorem blk_zero_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : blk e B 0 0 = e := rfl

theorem blk_zero_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (q : Fin d) :
    blk e B 0 q.succ = 0 := rfl

theorem blk_succ_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p : Fin d) :
    blk e B p.succ 0 = 0 := rfl

theorem blk_succ_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) :
    blk e B p.succ q.succ = B p q := rfl

theorem blk_assemble {d : ℕ} (T₀ T₁ T₂ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) (e₀ e₁ s t v : ℂ)
    (B₀ B₁ C : Matrix (Fin d) (Fin d) ℂ)
    (a₀ : ∀ a b, T₀ (selA 0 a) (selA 0 b) = blk e₀ B₀ a b)
    (l₀ : ∀ j, T₀ (Fin.succ 0) j = 0) (r₀ : ∀ i, T₀ i (Fin.succ 0) = 0)
    (a₁ : ∀ a b, T₁ (selA (Fin.succ 0) a) (selA (Fin.succ 0) b) = blk e₁ B₁ a b)
    (l₁ : ∀ j, T₁ 0 j = 0) (r₁ : ∀ i, T₁ i 0 = 0)
    (a₂ : ∀ a b, T₂ (selT a) (selT b) = C a b)
    (l₂ : ∀ j, T₂ 0 j = 0) (r₂ : ∀ i, T₂ i 0 = 0)
    (l₂' : ∀ j, T₂ (Fin.succ 0) j = 0) (r₂' : ∀ i, T₂ i (Fin.succ 0) = 0) :
    s • T₀ + t • T₁ + v • T₂ = blk (s * e₀) (blk (t * e₁) (s • B₀ + t • B₁ + v • C)) := by
  have p00 : T₀ 0 0 = e₀ := a₀ 0 0
  have p0k : ∀ k : Fin d, T₀ 0 k.succ.succ = 0 := fun k => a₀ 0 k.succ
  have pk0 : ∀ k : Fin d, T₀ k.succ.succ 0 = 0 := fun k => a₀ k.succ 0
  have pkl : ∀ k l : Fin d, T₀ k.succ.succ l.succ.succ = B₀ k l := fun k l => a₀ k.succ l.succ
  have q11 : T₁ (Fin.succ 0) (Fin.succ 0) = e₁ := a₁ 0 0
  have q1k : ∀ k : Fin d, T₁ (Fin.succ 0) k.succ.succ = 0 := fun k => a₁ 0 k.succ
  have qk1 : ∀ k : Fin d, T₁ k.succ.succ (Fin.succ 0) = 0 := fun k => a₁ k.succ 0
  have qkl : ∀ k l : Fin d, T₁ k.succ.succ l.succ.succ = B₁ k l := fun k l => a₁ k.succ l.succ
  have wkl : ∀ k l : Fin d, T₂ k.succ.succ l.succ.succ = C k l := fun k l => a₂ k l
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp only [p00, l₁, l₂, blk_zero_zero, mul_zero, add_zero]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp only [r₀, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
      | succ k => simp only [p0k, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp only [l₀, r₁, l₂', blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [l₀, q11, l₂', blk_succ_succ, blk_zero_zero, mul_zero, add_zero, zero_add]
        | succ k => simp only [l₀, q1k, l₂', blk_succ_succ, blk_zero_succ, mul_zero, add_zero]
    | succ k =>
      induction j using Fin.cases with
      | zero => simp only [pk0, r₁, r₂, blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [r₀, qk1, r₂', blk_succ_succ, blk_succ_zero, mul_zero, add_zero]
        | succ l =>
          simp only [pkl, qkl, wkl, blk_succ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hessC_row_square : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  intro d f α y p₀ p₁ e₀ e₁ B₀ B₁ s t v hf₀ hf₁ hα h₀ h₁
  have ho : (Fin.succ 0 : Fin (d + 2)) = 1 := by simp
  have hinj₀ : Function.Injective (selA (0 : Fin (d + 2))) :=
    selA_injective fun i => Fin.succ_ne_zero _
  have hinj₁ : Function.Injective (selA (Fin.succ 0 : Fin (d + 2))) :=
    selA_injective fun i h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  have q₀ : selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = Fin.cons p₀ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₁ : selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) =
      Fin.cons p₁ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₂ : selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = y := by
    rw [selT_eq_tail]; simp [Fin.tail_cons]
  have g₀ : ContDiffAt ℝ 2 f (selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₀]
  have g₁ : ContDiffAt ℝ 2 f
      (selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by rwa [q₁]
  have g₂ : ContDiffAt ℝ 2 α (selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₂]
  have c₀ := contDiffAt_comp_selL f _ _ g₀
  have c₁ := contDiffAt_comp_selL f _ _ g₁
  have c₂ := contDiffAt_comp_selL α _ _ g₂
  have E : (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z))) =
      fun z => (fun z => (fun z => s * (f ∘ selL (selA 0)) z) z +
        (fun z => t * (f ∘ selL (selA (Fin.succ 0))) z) z) z +
        (fun z => v * (α ∘ selL selT) z) z := by
    funext z
    simp only [Function.comp, selA_eq_cons, selT_eq_tail, ho]
  rw [E, hessC_add' _ _ _ ((contDiffAt_const.mul c₀).add (contDiffAt_const.mul c₁))
      (contDiffAt_const.mul c₂),
    hessC_add' _ _ _ (contDiffAt_const.mul c₀) (contDiffAt_const.mul c₁),
    hessC_const_mul', hessC_const_mul', hessC_const_mul']
  refine blk_assemble _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b; rw [hessC_selL_inj f hinj₀ _ g₀, q₀, h₀]
  · intro j
    refine hessC_selL_left f _ _ g₀ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro i
    refine hessC_selL_right f _ _ g₀ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro a b; rw [hessC_selL_inj f hinj₁ _ g₁, q₁, h₁]
  · intro j
    refine hessC_selL_left f _ _ g₁ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro i
    refine hessC_selL_right f _ _ g₁ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro a b; rw [hessC_selL_inj α selT_injective _ g₂, q₂]
  · intro j; exact hessC_selL_left α _ _ g₂ (fun a => Fin.succ_ne_zero _) j
  · intro i; exact hessC_selL_right α _ _ g₂ i (fun a => Fin.succ_ne_zero _)
  · intro j
    exact hessC_selL_left α _ _ g₂ (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)) j
  · intro i
    exact hessC_selL_right α _ _ g₂ i (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h))

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombinationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_two_point_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_square <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPower
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPower
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def genLin : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) ℝ) := ∑ i, X i * C (X i)

def coordHom : MvPolynomial (Fin 3) ℝ →+* (S2 → ℝ) :=
  RingHom.pi fun p : S2 => MvPolynomial.eval fun i => (p : E3) i

theorem coordHom_apply (g : MvPolynomial (Fin 3) ℝ) (p : S2) :
    coordHom g p = MvPolynomial.eval (fun i => (p : E3) i) g := rfl

theorem linear_form_eq_map_eval (n : Fin 3 → ℝ) : lin3 n = MvPolynomial.map (MvPolynomial.eval n) genLin := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin3, genLin, map_sum, MvPolynomial.map_X, MvPolynomial.map_C, MvPolynomial.eval_X]

theorem dotPoly_id_eq_map : dotPoly (id : S2 → S2) = MvPolynomial.map coordHom genLin := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotPoly, genLin, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext p
  rw [coordHom_apply, MvPolynomial.eval_X]
  rfl

theorem linear_expand (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (S : Finset (Fin 3 →₀ ℕ))
    (Q : MvPolynomial (Fin 3) ℝ) (hQ : Q.support ⊆ S) :
    ℓ Q = ∑ m ∈ S, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by
  calc ℓ Q = ℓ (∑ m ∈ Q.support, monomial m (AddMonoidAlgebra.coeff Q m)) := by rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ Q.support, AddMonoidAlgebra.coeff Q m * ℓ (monomial m 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show monomial m (AddMonoidAlgebra.coeff Q m) = (AddMonoidAlgebra.coeff Q m) • monomial m (1 : ℝ) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    _ = _ := Finset.sum_subset hQ fun m _ hm => by rw [notMem_support_iff.1 hm, zero_mul]

theorem stereo_one : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  intro ℓ N
  have : IsProbabilityMeasure sphereMeasure := GroundTheory.Heights₂.Heights.Inter.FibreLocal.isProbabilityMeasure_sphere
  have key : ∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : S2 => f fun i => (m : E3) i) sphereMeasure) ∧
      ∫ a : ℂ, f (nS a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) =
        ∫ m : S2, f (fun i => (m : E3) i) ∂sphereMeasure :=
    fun f hf => (GlobalTheory.T.sphere_measure_stereographic_integral).1 f hf
  obtain ⟨G, hG⟩ : ∃ G, G = genLin ^ N := ⟨_, rfl⟩
  have hlin : ∀ a, lin3 (nS a) ^ N = MvPolynomial.map (MvPolynomial.eval (nS a)) G := fun a => by
    rw [hG, map_pow, linear_form_eq_map_eval]
  have hdot : dotPoly (id : S2 → S2) ^ N = MvPolynomial.map coordHom G := by
    rw [hG, map_pow, dotPoly_id_eq_map]
  rw [hdot]
  have hf : ∀ m, Continuous fun x : Fin 3 → ℝ => MvPolynomial.eval x (AddMonoidAlgebra.coeff G m) :=
    fun m => MvPolynomial.continuous_eval _
  have hcoord : Continuous fun p : S2 => fun i => (p : E3) i := by
    fun_prop
  have hsph : ∀ m, Integrable (fun p : S2 => MvPolynomial.eval (fun i => (p : E3) i) (AddMonoidAlgebra.coeff G m))
      sphereMeasure := fun m =>
    ((hf m).comp hcoord).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpl : ∀ m, Integrable (fun a : ℂ => MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) *
      (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) := fun m =>
    (key _ (hf m).measurable).1.2 (hsph m)
  have hsupp : (momentPoly sphereMeasure (fun _ => 1) (MvPolynomial.map coordHom G)).support ⊆ G.support := by
    intro m hm
    by_contra h
    rw [mem_support_iff] at hm
    apply hm
    rw [GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly, coeff_map, notMem_support_iff.1 h]
    simp
  rw [linear_expand ℓ G.support _ hsupp, Finset.mul_sum]
  have hpt : ∀ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) = ∑ m ∈ G.support,
      (MvPolynomial.eval (nS a) (AddMonoidAlgebra.coeff G m) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) *
        (Real.pi * ℓ (monomial m 1)) := fun a => by
    rw [hlin, linear_expand ℓ G.support _ (support_map_subset _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_map, wS]
    have hpi := Real.pi_ne_zero
    field_simp
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => (hpl m).mul_const _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const, (key _ (hf m).measurable).2,
    GroundTheory.Heights₂.Heights.Inter.DiagFibreMoment.coeff_momentPoly]
  simp only [coeff_map, one_mul, coordHom_apply]
  ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPowerStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_moment_power : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansion
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem derivation_prod_erase_xt {σ ι : Type*} [DecidableEq ι]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : ι → MvPolynomial σ ℝ) (S : Finset ι) :
    D (∏ i ∈ S, a i) = ∑ i ∈ S, D (a i) * ∏ j ∈ S.erase i, a j := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, D.leibniz, ih, Finset.sum_insert hi, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, mul_comm (∏ j ∈ S, a j), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij,
      Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    ring

theorem derivation_prod_succAbove_xt {σ : Type*} {n : ℕ}
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) (a : Fin (n + 1) → MvPolynomial σ ℝ) :
    D (∏ r, a r) = ∑ r, D (a r) * ∏ s, a (r.succAbove s) := by
  rw [derivation_prod_erase_xt]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  rw [Fin.univ_succAbove _ r, Finset.cons_eq_insert, Finset.erase_insert (by simp), Finset.prod_map]
  rfl

theorem pderiv_rowW_zero_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 0) (rowW u v) = C (u 0) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_rowW_one_xt (u : Fin 2 → ℝ) (v : ℝ) : pderiv (some 1) (rowW u v) = C (u 1) := by
  simp [rowW, pderiv_X, Pi.single_apply, pderiv_C, Derivation.leibniz]

theorem pderiv_C_mul_xt {σ : Type*} [DecidableEq σ] (j : σ) (a : ℝ) (p : MvPolynomial σ ℝ) :
    pderiv j (C a * p) = C a * pderiv j p := by
  simp [Derivation.leibniz, pderiv_C]

theorem linear_form_linear_combination (a b : ℝ) (n m : Fin 3 → ℝ) :
    lin4 (fun i => a * n i + b * m i) = C a * lin4 n + C b * lin4 m := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin4, lin3, map_sum, map_mul, rename_X, rename_C, Finset.mul_sum,
    ← Finset.sum_add_distrib, map_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem evalW_C_xt (n₀ n₁ : Fin 3 → ℝ) (a : ℝ) : evalW n₀ n₁ (C a) = C a := by
  simp [evalW]

theorem evalW_rowW_xt (n₀ n₁ : Fin 3 → ℝ) (u : Fin 2 → ℝ) (v : ℝ) :
    evalW n₀ n₁ (rowW u v) = lin4 (fun i => u 0 * n₀ i + u 1 * n₁ i) + C v * X none := by
  rw [linear_form_linear_combination]
  simp [evalW, rowW]

theorem mdisc_extract_two : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  intro d T H L hL u v n₀ n₁ e₀ e₁
  have hLC : ∀ (a : ℝ) (p : MvPolynomial (Option (Fin 3)) ℝ), L (C a * p) = (a : ℂ) * L p := by
    intro a p
    rw [← smul_eq_C_mul, map_smul, Complex.real_smul]
  let M : Fin (d + 2) → Matrix (Fin d) (Fin d) ℂ := fun r =>
    (∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H
  have h1 : ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) =
      ∑ r, ((u r 0 : ℂ) * e₀) * (((d + 1).factorial : ℂ) *
        mdisc fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) :=
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion (d + 1)).1 (fun r => (u r 0 : ℂ) * e₀) (fun r => blk ((u r 1 : ℂ) * e₁) (M r))
  have h2 : ∀ r : Fin (d + 2), ((d + 1).factorial : ℂ) *
      mdisc (fun s => blk ((u (r.succAbove s) 1 : ℂ) * e₁) (M (r.succAbove s))) =
      ∑ s, ((u (r.succAbove s) 1 : ℂ) * e₁) * ((d.factorial : ℂ) *
        mdisc fun t => M (r.succAbove (s.succAbove t))) := fun r =>
    (GlobalTheory.T.mixed_discriminant_cofactor_expansion d).1 (fun s => (u (r.succAbove s) 1 : ℂ) * e₁) (fun s => M (r.succAbove s))
  have h3 : ∀ (r : Fin (d + 2)) (s : Fin (d + 1)),
      (d.factorial : ℂ) * mdisc (fun t => M (r.succAbove (s.succAbove t))) =
      L (∏ t, evalW n₀ n₁ (rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))))) := by
    intro r s
    simp only [evalW_rowW_xt]
    exact hL (fun t i => u (r.succAbove (s.succAbove t)) 0 * n₀ i + u (r.succAbove (s.succAbove t)) 1 * n₁ i)
      (fun t => v (r.succAbove (s.succAbove t)))
  have h4 : pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))) =
      ∑ r, C (u r 0) * ∑ s, C (u (r.succAbove s) 1) *
        ∏ t, rowW (u (r.succAbove (s.succAbove t))) (v (r.succAbove (s.succAbove t))) := by
    rw [derivation_prod_succAbove_xt]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pderiv_rowW_zero_xt, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pderiv_C_mul_xt, derivation_prod_succAbove_xt]
    simp only [pderiv_rowW_one_xt]
  show ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁) (M r))) = _
  rw [h1, h4]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h2, h3, map_sum, map_mul, map_prod, evalW_C_xt, hLC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantTwoRowExpansionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_two_row_expansion : ∀ (d : ℕ) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ) (H : Matrix (Fin d) (Fin d) ℂ)
    (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ),
    (∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none))) →
    ∀ (u : Fin (d + 2) → Fin 2 → ℝ) (v : Fin (d + 2) → ℝ) (n₀ n₁ : Fin 3 → ℝ) (e₀ e₁ : ℂ),
      ((d + 2).factorial : ℂ) * mdisc (fun r => blk ((u r 0 : ℂ) * e₀) (blk ((u r 1 : ℂ) * e₁)
        ((∑ i, ((u r 0 * n₀ i + u r 1 * n₁ i : ℝ) : ℂ) • T i) + ((v r : ℝ) : ℂ) • H))) =
      e₀ * e₁ * L (evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r, rowW (u r) (v r))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.mdisc_extract_two <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombination
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombination
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.AnForm.A

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def tailCL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailCL_coe (d : ℕ) : (⇑(tailCL d) : (Fin (d + 1) → ℂ) → (Fin d → ℂ)) = Fin.tail := by
  funext z i
  rfl

theorem jacC_tailCL (d : ℕ) (z : Fin (d + 1) → ℂ) (a : Fin d) (k : Fin (d + 1)) :
    jacC (⇑(tailCL d)) z a k = if a.succ = k then 1 else 0 := by
  have h := ContinuousLinearMap.fderiv (𝕜 := ℂ) (x := z) (tailCL d)
  simp only [jacC, h]
  simp [tailCL, Pi.single_apply, eq_comm]

theorem hessC_comp_tail (d : ℕ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p : ℂ)
    (hα : ContDiffAt ℝ 2 α y) :
    hessC (fun z : Fin (d + 1) → ℂ => α (Fin.tail z)) (Fin.cons p y) = blk 0 (hessC α y) := by
  have ht : (tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ) = y := by
    rw [tailCL_coe]; exact Fin.tail_cons _ _
  have h := hessC_comp α (⇑(tailCL d)) (Fin.cons p y : Fin (d + 1) → ℂ)
    ((tailCL d).analyticAt _) (by rw [ht]; exact hα)
  have hfun : α ∘ ⇑(tailCL d) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
    rw [tailCL_coe]; rfl
  rw [hfun, ht] at h
  rw [h]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, jacC_tailCL, blk,
      Fin.succ_ne_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem hessC_row_fibre : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  intro d f α y p e B s v hf hα hB
  have ht : (Fin.tail (Fin.cons p y : Fin (d + 1) → ℂ) : Fin d → ℂ) = y := Fin.tail_cons _ _
  have htail : ContDiffAt ℝ 2 (fun z : Fin (d + 1) → ℂ => α (Fin.tail z))
      (Fin.cons p y : Fin (d + 1) → ℂ) := by
    have hα' : ContDiffAt ℝ 2 α ((tailCL d) (Fin.cons p y : Fin (d + 1) → ℂ)) := by
      rw [tailCL_coe, ht]; exact hα
    have hl : ContDiffAt ℝ 2 (⇑((tailCL d).restrictScalars ℝ))
        (Fin.cons p y : Fin (d + 1) → ℂ) := ((tailCL d).restrictScalars ℝ).contDiff.contDiffAt
    have := ContDiffAt.comp (g := α) (f := ⇑((tailCL d).restrictScalars ℝ))
      (Fin.cons p y : Fin (d + 1) → ℂ) hα' hl
    have hfun : α ∘ ⇑((tailCL d).restrictScalars ℝ) = fun z : Fin (d + 1) → ℂ => α (Fin.tail z) := by
      funext z
      simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [tailCL_coe]
    rwa [hfun] at this
  rw [ReciprocityTheory.AnForm.M.hessC_add' (fun z => s * f z) (fun z => v * α (Fin.tail z)) _
    (contDiffAt_const.mul hf) (contDiffAt_const.mul htail),
    ReciprocityTheory.AnForm.M.hessC_const_mul' s f, ReciprocityTheory.AnForm.M.hessC_const_mul' v (fun z => α (Fin.tail z)), hB, hessC_comp_tail d α y p hα]
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blk]

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianBlockCombinationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_hessian_block_combination : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p e : ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (s v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p y) → ContDiffAt ℝ 2 α y → hessC f (Fin.cons p y) = blk e B →
    hessC (fun z : Fin (d + 1) → ℂ => s * f z + v * α (Fin.tail z)) (Fin.cons p y) =
    blk ((s : ℂ) * e) ((s : ℂ) • B + (v : ℂ) • hessC α y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.hessC_row_fibre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RowProductFirstDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RowProductFirstDerivative
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

theorem prod_fin_ite_lt {R : Type*} [CommMonoid R] (a b : R) (m N : ℕ) (h : m ≤ N) :
    (∏ r : Fin N, (if (r : ℕ) < m then a else b)) = a ^ m * b ^ (N - m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < m then a else b) (m + j),
    Finset.prod_range_add]
  have h1 : (∏ x ∈ Finset.range m, (if x < m then a else b)) = a ^ m := by
    rw [Finset.prod_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx))]
    simp
  have h2 : (∏ x ∈ Finset.range j, (if m + x < m then a else b)) = b ^ j := by
    rw [Finset.prod_congr rfl (fun x _ => if_neg (by omega))]
    simp
  rw [h1, h2, Nat.add_sub_cancel_left]

theorem rowW_ite (c : Prop) [Decidable c] :
    rowW ![if c then 1 else 0, 0] (if c then 0 else 1) =
      if c then (X (some 0) : MvPolynomial (Option (Fin 2)) ℝ) else X none := by
  split_ifs <;> simp [rowW]

theorem evalW_X_some_zero (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X (some 0)) = rename some (lin3 n₀) := by
  simp [evalW, lin4]

theorem evalW_X_none (n₀ n₁ : Fin 3 → ℝ) :
    evalW n₀ n₁ (X none) = X none := by
  simp [evalW]

theorem evalW_pderiv_prod_rowW : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  intro d k hk hkd n
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hm : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
  have hm2 : 2 * (t + 1) - 2 = 2 * t := by omega
  have hj : d + 2 - 2 * (t + 1) = d + 1 - (2 * t + 1) := by omega
  have hprod : (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * (t + 1) - 1 then 1 else 0, 0]
        (if (r : ℕ) < 2 * (t + 1) - 1 then 0 else 1)) =
      X (some 0) ^ (2 * t + 1) * X none ^ (d + 1 - (2 * t + 1)) := by
    simp only [rowW_ite, hm]
    exact prod_fin_ite_lt _ _ _ _ (by omega)
  rw [hprod, hm2, hj, Derivation.leibniz, Derivation.leibniz_pow, Derivation.leibniz_pow]
  have hne : (none : Option (Fin 2)) ≠ some 0 := by simp
  simp only [pderiv_X_self, pderiv_X_of_ne hne, smul_eq_mul, smul_zero, zero_add, mul_zero,
    add_zero, mul_one, Nat.add_sub_cancel, nsmul_eq_mul]
  simp only [map_mul, map_pow, map_natCast, evalW_X_some_zero, evalW_X_none]
  have hc : (C (2 * ((t + 1 : ℕ) : ℝ) - 1) : MvPolynomial (Option (Fin 3)) ℝ) =
      ((2 * t + 1 : ℕ) : MvPolynomial (Option (Fin 3)) ℝ) := by
    rw [← map_natCast (C : ℝ →+* MvPolynomial (Option (Fin 3)) ℝ)]
    congr 1
    push_cast
    ring
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RowProductFirstDerivativeStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_product_first_derivative : ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ n : Fin 3 → ℝ,
    evalW n n (pderiv (some 0) (∏ r : Fin (d + 1),
      rowW ![if (r : ℕ) < 2 * k - 1 then 1 else 0, 0] (if (r : ℕ) < 2 * k - 1 then 0 else 1))) =
    C (2 * (k : ℝ) - 1) * rename some (lin3 n ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.evalW_pderiv_prod_rowW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalized
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

theorem densW (d k i : ℕ) (hi : i < k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z =
      (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 0 *
          f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0 : Fin 2 → ℝ) 1 *
          f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) +
        (if (r : ℕ) < 2 * k then (0 : ℝ) else 1) * α (Fin.tail (Fin.tail z)))
    (p₀ p₁ : ℂ) :
    maDens φ (Fin.cons p₀ (Fin.cons p₁ y)) = (2 / Real.pi) ^ (d + 2) * (wS p₀ * wS p₁ *
      (L (rename some (aeval ![lin3 (nS p₀), lin3 (nS p₁)]
        (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) *
          X none ^ (d + 2 - 2 * k))).re) := by
  set uu : Fin (d + 2) → Fin 2 → ℝ := fun r => if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0
  set vv : Fin (d + 2) → ℝ := fun r => if (r : ℕ) < 2 * k then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons p₀ (Fin.cons p₁ y))) = fun r =>
      blk ((uu r 0 : ℂ) * -(wS p₀ : ℂ)) (blk ((uu r 1 : ℂ) * -(wS p₁ : ℂ))
        ((∑ j, ((uu r 0 * nS p₀ j + uu r 1 * nS p₁ j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H)) := by
    funext r
    have e : φ r = fun z : Fin (d + 2) → ℂ => uu r 0 * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        uu r 1 * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + vv r * α (Fin.tail (Fin.tail z)) :=
      funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_two_point_combination d f α y p₀ p₁ _ _ _ _ (uu r 0) (uu r 1) (vv r) (hfc _) (hfc _) hα (hfh _) (hfh _), ← hH]
    congr 3
    simp only [Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib, ← add_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_two_row_expansion d T H L hL uu vv (nS p₀) (nS p₁) (-(wS p₀ : ℂ)) (-(wS p₁ : ℂ))
  rw [GlobalTheory.T.word_coefficient_second_derivative d k i hi hkd (nS p₀) (nS p₁)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  rw [show (((d + 2).factorial : ℕ) : ℂ) = (((d + 2).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, neg_mul_neg, ← Complex.ofReal_mul, Complex.re_ofReal_mul] at hre
  rw [mul_right_comm, hre]
  ring

theorem densY (d k : ℕ) (hk : 1 ≤ k) (hkd : 2 * k ≤ d + 2) (T : Fin 3 → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) (L : MvPolynomial (Option (Fin 3)) ℝ →ₗ[ℝ] ℂ)
    (hL : ∀ (c : Fin d → Fin 3 → ℝ) (v : Fin d → ℝ),
      (d.factorial : ℂ) * mdisc (fun t => (∑ i, ((c t i : ℝ) : ℂ) • T i) + ((v t : ℝ) : ℂ) • H) =
        L (∏ t, (lin4 (c t) + C (v t) * X none)))
    (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y)) (hα : ContDiffAt ℝ 2 α y)
    (hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j))
    (hH : H = hessC α y) (φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ)
    (hφ : ∀ r z, φ r z = (if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0) * f z +
        (if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1) * α (Fin.tail z))
    (a : ℂ) :
    maDens φ (Fin.cons a y) = (2 / Real.pi) ^ (d + 1) * (-(wS a) * (2 * (k : ℝ) - 1) *
      (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re) := by
  set cc : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (1 : ℝ) else 0
  set vv : Fin (d + 1) → ℝ := fun r => if (r : ℕ) < 2 * k - 1 then (0 : ℝ) else 1
  have hrow : (fun r => hessC (φ r) (Fin.cons a y)) = fun r =>
      blk ((cc r : ℂ) * -(wS a : ℂ))
        ((∑ j, ((cc r * nS a j : ℝ) : ℂ) • T j) + ((vv r : ℝ) : ℂ) • H) := by
    funext r
    have e : φ r = fun z : Fin (d + 1) → ℂ => cc r * f z + vv r * α (Fin.tail z) := funext (hφ r)
    rw [e, GlobalTheory.T.complex_hessian_block_combination d f α y a _ _ (cc r) (vv r) (hfc _) hα (hfh _), ← hH]
    congr 2
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  have hB := GlobalTheory.T.mixed_discriminant_one_row_expansion d T H L hL cc vv (nS a) (-(wS a : ℂ))
  rw [GlobalTheory.T.row_product_first_derivative d k hk hkd (nS a)] at hB
  rw [maDens, hrow]
  have hre := congrArg Complex.re hB
  have hR : (-(wS a : ℂ) * L (C (2 * (k : ℝ) - 1) * rename some (lin3 (nS a) ^ (2 * k - 2)) *
      X none ^ (d + 2 - 2 * k))).re = -(wS a) * (2 * (k : ℝ) - 1) *
        (L (rename some (lin3 (nS a) ^ (2 * k - 2)) * X none ^ (d + 2 - 2 * k))).re := by
    rw [mul_assoc (C _), C_mul', map_smul, Complex.real_smul, ← Complex.ofReal_neg, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [show (((d + 1).factorial : ℕ) : ℂ) = (((d + 1).factorial : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, hR] at hre
  rw [mul_right_comm, hre]
  ring

theorem fibre_integral_normal : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro h d k hk hkd G α y hPD hG2 hα hG1 hGd
  obtain ⟨T, hT⟩ := GlobalTheory.T.xi_potential_hessian_decomposition d G y hPD hG2 hG1 hGd
  obtain ⟨L, hL⟩ := GlobalTheory.T.mixed_discriminant_linear_functional d T (hessC α y)
  set f : (Fin (d + 1) → ℂ) → ℝ := fun z => xiPot (G (Fin.tail z)) (z 0) with hf
  have hfc : ∀ a : ℂ, ContDiffAt ℝ 2 f (Fin.cons a y) := fun a => (hT a).1
  have hfh : ∀ a : ℂ, hessC f (Fin.cons a y) = blk (-(wS a : ℂ)) (∑ j, ((nS a j : ℝ) : ℂ) • T j) := by
    intro a
    rw [(hT a).2]
    ext p q
    refine Fin.cases ?_ (fun p' => ?_) p <;> refine Fin.cases ?_ (fun q' => ?_) q
    · simp [blk, wS]
    · simp [blk]
    · simp [blk]
    · simp [blk, nS, Matrix.sum_apply]
  let ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ L ∘ₗ
    (LinearMap.mulRight ℝ (X none ^ (d + 2 - 2 * k) : MvPolynomial (Option (Fin 3)) ℝ)) ∘ₗ
      (rename some : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ).toLinearMap
  have hℓ : ∀ p, (L (rename some p * X none ^ (d + 2 - 2 * k))).re = ℓ p := fun p => rfl
  have hword : ∀ i ∈ Finset.range k, (∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) =
      (2 / Real.pi) ^ (d + 2) * (Real.pi ^ 2 * ℓ (diagWordMomentPoly k i)) := by
    intro i hi
    have hik := Finset.mem_range.1 hi
    have hpt : ∀ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 / Real.pi) ^ (d + 2) * (logSin 1 p.1 p.2 * (wS p.1 * wS p.2 *
          ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)]
            (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))))) := by
      intro p
      rw [densW d k i hik hkd T _ L hL f α y hfc hα hfh rfl _ ?_ p.1 p.2, hG1, hℓ]
      · ring
      · intro r z
        have hcoef : ∀ c : Fin 2, (if (r : ℕ) = 0 then (![1, -1] : Fin 2 → ℝ) c else if (r : ℕ) = 1 then (![0, 1] : Fin 2 → ℝ) c else if (r : ℕ) < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) = DiagonalFibreFubini.wordCoef i r c := by
          intro c
          simp only [DiagonalFibreFubini.wordCoef]
          split_ifs <;> rfl
        by_cases hr : (r : ℕ) < 2 * k
        · simp only [hr, if_true, hcoef, hf, Fin.tail, Fin.cons_zero, Fin.cons_succ]
          simp
        · simp [hr]
    simp_rw [hpt]
    rw [integral_const_mul, GlobalTheory.T.sphere_pair_log_sine_moment, DiagonalFibreFubini.linProd_word k i hik]
    rfl
  have hY : ∀ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) =
      (2 / Real.pi) ^ (d + 1) * (-(2 * (k : ℝ) - 1)) * (wS a * ℓ (lin3 (nS a) ^ (2 * k - 2))) := by
    intro a
    rw [densY d k hk hkd T _ L hL f α y hfc hα hfh rfl _ ?_ a, hℓ]
    · ring
    · intro r z
      by_cases hr : (r : ℕ) < 2 * k - 1
      · simp [hr, hf]
      · simp [hr]
  have hfib : fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.1 k (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h2
  have hpush : pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
    have h2 := h.2.2.2.1 k hk (MvPolynomial (Fin 3) ℝ) X
    rwa [aeval_X_left_apply] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl hword, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum,
    DiagFibreMoment.sum_diagWordMomentPoly, hfib]
  simp_rw [hY]
  rw [integral_const_mul, GlobalTheory.T.sphere_moment_power]
  have hp : (-(2 * (k : ℝ) - 1)) * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ (2 * k - 2))) =
      -ℓ ((∑ i, X i ^ 2) ^ (k - 1)) := by
    rw [← map_neg, ← hpush, pushMomentPoly, map_smul, smul_eq_mul]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [C_mul', map_smul, smul_eq_mul]
  calc _ = (2 / Real.pi) ^ (d + 1) * (2 / Real.pi) * Real.pi ^ 2 * (-kappa k * ℓ ((∑ i, X i ^ 2) ^ (k - 1))) := by
        rw [pow_succ]; ring
    _ = 2 * kappa k * ((2 / Real.pi) ^ (d + 1) * (Real.pi * (-ℓ ((∑ i, X i ^ 2) ^ (k - 1))))) := by
        field_simp
    _ = _ := by
        rw [← hp]; ring

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalizedStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_monge_ampere_normalized : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → G y = 1 → (∀ p q, fderiv ℝ (fun y' => G y' p q) y = 0) → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.fibre_integral_normal <;> assumption)
end
