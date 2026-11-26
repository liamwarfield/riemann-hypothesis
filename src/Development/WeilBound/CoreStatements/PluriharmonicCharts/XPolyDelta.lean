module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.TripleDeriv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyDelta
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_delta

theorem eval_toWt {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (Q : MvPolynomial (Ψ × Fin N) ℝ) :
    eval lam (toWt Q) = eval (fun p => eval lam (gapX p)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [toWt]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, toWt, aeval_X] at *; rw [eval_X]

theorem tele_nat (f : ℕ → ℝ) (i l : ℕ) (h : i ≤ l) :
    ∑ m ∈ Finset.Ico i l, (f m - f (m + 1)) = f i - f l := by
  induction l, h using Nat.le_induction with
  | base => simp
  | succ l h ih => rw [Finset.sum_Ico_succ_top h, ih]; ring

theorem tele {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (τ : Ψ) (i l : Fin N) (h : i ≤ l) :
    ∑ m ∈ Finset.Ico i l, eval lam (gapX (τ, m)) = lam (τ, i) - lam (τ, l) := by
  classical
  let f : ℕ → ℝ := fun n => if hn : n < N then lam (τ, ⟨n, hn⟩) else 0
  have hg : ∀ m : Fin N, eval lam (gapX (τ, m)) = f m - f ((m : ℕ) + 1) := by
    intro m
    by_cases hm : (m : ℕ) + 1 < N
    · simp [gapX, f, hm, m.isLt]
    · simp [gapX, f, hm, m.isLt]
  rw [Finset.sum_congr rfl (fun m _ => hg m)]
  rw [show ∑ m ∈ Finset.Ico i l, (f m - f ((m : ℕ) + 1))
      = ∑ n ∈ Finset.Ico (i : ℕ) (l : ℕ), (f n - f (n + 1)) by
    rw [← Fin.map_valEmbedding_Ico, Finset.sum_map]
    rfl]
  rw [tele_nat f i l (by exact_mod_cast h)]
  simp [f, i.isLt, l.isLt]

end PositivityTheory.Xgp.poly_delta

theorem PositivityTheory.Xgp.t_poly_delta : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  intro Ψ _ _ N Q v h
  constructor
  · apply MvPolynomial.funext
    intro lam
    rw [PositivityTheory.Xgp.poly_delta.eval_toWt, h]
    simp only [antisymDelta, map_mul, map_prod, eval_C, map_sub, eval_X]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ =>
      Finset.prod_congr rfl fun l hl => ?_
    exact PositivityTheory.Xgp.poly_delta.tele lam τ i l (Finset.mem_Ioi.mp hl).le
  · simp only [antisymDelta, map_prod, map_sub, eval_X, rhoWt]
    refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l hl => ?_
    have : (i : ℕ) < l := Fin.lt_def.mp (Finset.mem_Ioi.mp hl)
    have : ((i : ℕ) : ℝ) < (l : ℕ) := by exact_mod_cast this
    linarith
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyTowtBound
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_towt_bound

theorem abs_coeff_le {σ : Type} (P : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |P.coeff m| ≤ ∑ d ∈ P.support, |P.coeff d| := by
  by_cases h : m ∈ P.support
  · exact Finset.single_le_sum (f := fun d => |P.coeff d|) (fun _ _ => abs_nonneg _) h
  · rw [notMem_support_iff.mp h, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem gen {σ : Type} [Fintype σ] (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsHomogeneous 1) (n : ℕ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
      (aeval f Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
        ∀ m, |(aeval f Q).coeff m| ≤ Cst * M) := by
  classical
  let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) n).toFinset
  let image (d : σ →₀ ℕ) := aeval f (monomial d (1 : ℝ))
  let B (d : σ →₀ ℕ) : ℝ := ∑ e ∈ (image d).support, |(image d).coeff e|
  have hB : ∀ d, 0 ≤ B d := fun d => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ d ∈ S, B d, Finset.sum_nonneg fun d _ => hB d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
  · simpa only [one_mul] using hQ.aeval f hf
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hsub : Q.support ⊆ S := by
      intro d hd
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      by_contra hne
      exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero (by omega))
    have e : (aeval f Q).coeff m = ∑ d ∈ Q.support, Q.coeff d * (image d).coeff m := by
      conv_lhs => rw [Q.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      have hmonomial : monomial d (Q.coeff d) = C (Q.coeff d) * monomial d (1 : ℝ) := by
        rw [C_mul_monomial, mul_one]
      rw [hmonomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul]
    rw [e]
    calc _ ≤ ∑ d ∈ Q.support, |Q.coeff d * (image d).coeff m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (abs_coeff_le _ m) (hM d) (abs_nonneg _) (hB d)
      _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
      _ = _ := by rw [Finset.sum_mul]

theorem gapX_hom {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) : (gapX p).IsHomogeneous 1 := by
  unfold gapX
  refine (isHomogeneous_X ℝ p).sub ?_
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero _ _ _

end PositivityTheory.Xgp.poly_towt_bound

theorem PositivityTheory.Xgp.t_poly_towt_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) := by
  intro Ψ _ N n
  obtain ⟨C1, h1, H1⟩ := PositivityTheory.Xgp.poly_towt_bound.gen (gapX (Ψ := Ψ) (N := N))
    PositivityTheory.Xgp.poly_towt_bound.gapX_hom n
  obtain ⟨C2, h2, H2⟩ := PositivityTheory.Xgp.poly_towt_bound.gen
    (fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (PositivityTheory.Xgp.poly_towt_bound.gapX_hom p).rename_isHomogeneous) n
  refine ⟨C1 + C2, fun Q M hQ => ⟨(H1 Q M hQ).1, fun hM m => ?_⟩,
    fun Q M hQ => ⟨(H2 Q M hQ).1, fun hM m => ?_⟩⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H1 Q M hQ).2 hM m
    have h3 := mul_nonneg h2 hM0
    unfold toWt
    linarith
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H2 Q M hQ).2 hM m
    have h3 := mul_nonneg h1 hM0
    unfold toWtS
    linarith
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.ProjectiveLineNormalFrame
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace PositivityTheory.Xgp.ProjectiveLineNormal

theorem holo_part {E M : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup M] [Module ℂ M]
    (H : E →ₗ[ℝ] M) : ∃ L : E →ₗ[ℂ] M, ∀ v, L v = (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)) := by
  refine ⟨⟨⟨fun v => (1 / 2 : ℂ) • (H v - Complex.I • H (Complex.I • v)), ?_⟩, ?_⟩, fun v => rfl⟩
  · intro v w
    simp only [smul_add, map_add (f := _)]
    module
  · intro c v
    have e1 : c • v = c.re • v + c.im • (Complex.I • v) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
    have e2 : Complex.I • c • v = c.re • (Complex.I • v) - c.im • v := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
      congr 1
      apply Complex.ext <;> simp
    simp only [RingHom.id_apply]
    rw [e2, e1, map_add (f := _), map_sub, H.map_smul, H.map_smul, H.map_smul, H.map_smul]
    generalize H v = A
    generalize H (Complex.I • v) = B
    simp only [← Complex.coe_smul]
    match_scalars
    · apply Complex.ext <;> simp [mul_comm]
    · apply Complex.ext <;> simp [mul_comm]

end PositivityTheory.Xgp.ProjectiveLineNormal

theorem PositivityTheory.Xgp.projective_line_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  intro d G y₀ hpos hherm hC
  have hG : ∀ p q, DifferentiableAt ℝ (fun y => G y p q) y₀ := fun p q =>
    (hC p q).differentiableAt (by norm_num)
  obtain ⟨g0, hg0u, hg0⟩ : ∃ g0 : Matrix (Fin 2) (Fin 2) ℂ, IsUnit g0.det ∧ g0ᴴ * G y₀ * g0 = 1 := by
    open scoped MatrixOrder in
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos.posSemidef.nonneg
    have hdet := hpos.det_pos.ne'
    have hyu : IsUnit y.det := by
      rw [hy, det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    refine ⟨y⁻¹, isUnit_nonsing_inv_det y hyu, ?_⟩
    rw [hy, star_eq_conjTranspose, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv y hyu]
    simp
  let Dm : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => Matrix.of fun p q => fderiv ℝ (fun y => G y p q) y₀ v
      map_add' := fun v w => by ext p q; simp
      map_smul' := fun c v => by ext p q; simp }
  have hDm : ∀ v, (Dm v)ᴴ = Dm v := by
    intro v
    ext p q
    have h1 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG q p) v).star
    have h2 := PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v
    have e : (fun s : ℝ => star (G (y₀ + s • v) q p)) = fun s : ℝ => G (y₀ + s • v) p q := by
      funext s
      exact (hherm _).apply p q
    rw [e] at h1
    exact h1.unique h2
  let H : (Fin d → ℂ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun v => g0ᴴ * Dm v * g0
      map_add' := fun v w => by rw [map_add (f := _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hH : ∀ v, (H v)ᴴ = H v := by
    intro v
    show (g0ᴴ * Dm v * g0)ᴴ = g0ᴴ * Dm v * g0
    rw [conjTranspose_mul, conjTranspose_mul, hDm, conjTranspose_conjTranspose, Matrix.mul_assoc]
  obtain ⟨L, hL⟩ := PositivityTheory.Xgp.ProjectiveLineNormal.holo_part H
  have hLL : ∀ v, (L v)ᴴ + L v = H v := by
    intro v
    rw [hL, conjTranspose_smul, conjTranspose_sub, conjTranspose_smul, hH, hH]
    simp only [Complex.star_def, Complex.conj_I, map_div₀, map_one, map_ofNat]
    module
  let Λ : Fin 2 → Fin 2 → (Fin d → ℂ) →L[ℂ] ℂ := fun p q => LinearMap.toContinuousLinearMap
    { toFun := fun v => (g0 * L v) p q
      map_add' := fun v w => by rw [map_add (f := _), Matrix.mul_add]; rfl
      map_smul' := fun c v => by rw [map_smul, Matrix.mul_smul]; rfl }
  refine ⟨fun y => g0 - g0 * L (y - y₀), fun p q => ?_, by simpa using hg0u, by simpa using hg0, fun p q => ?_⟩
  · show Differentiable ℂ fun y => g0 p q - Λ p q (y - y₀)
    fun_prop
  · by_cases hd : DifferentiableAt ℝ
        (fun y => ((g0 - g0 * L (y - y₀))ᴴ * G y * (g0 - g0 * L (y - y₀))) p q) y₀
    swap
    · exact fderiv_zero_of_not_differentiableAt hd
    ext1 v
    have hV : ∀ p q, HasDerivAt (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) ((-(g0 * L v)) p q) 0 := by
      intro p q
      have e : (fun s : ℝ => (g0 - g0 * L (y₀ + s • v - y₀)) p q) =
          fun s : ℝ => g0 p q - s • (g0 * L v) p q := by
        funext s
        rw [add_sub_cancel_left, L.map_smul_of_tower, Matrix.mul_smul]
        rfl
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((g0 * L v) p q)).const_sub (g0 p q)
    have h1 := PositivityTheory.Xgp.gram_grad.triple_deriv (fun s : ℝ => G (y₀ + s • v))
      (fun s : ℝ => g0 - g0 * L (y₀ + s • v - y₀)) (Dm v) (-(g0 * L v)) 0
      (fun p q => PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ (hG p q) v) hV p q
    have h3 := (PositivityTheory.Xgp.gram_grad.line_deriv _ y₀ hd v).unique h1
    rw [h3]
    simp only [zero_smul, add_zero, sub_self, map_zero, Matrix.mul_zero, sub_zero]
    have e1 : (-(g0 * L v))ᴴ * G y₀ * g0 = -(L v)ᴴ := by
      rw [conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (L v)ᴴ,
        Matrix.mul_assoc (L v)ᴴ, hg0, Matrix.mul_one]
    have e2 : g0ᴴ * G y₀ * -(g0 * L v) = -L v := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, hg0, Matrix.one_mul]
    have e3 : g0ᴴ * Dm v * g0 = (L v)ᴴ + L v := (hLL v).symm
    rw [e1, e2, e3]
    simp
end
