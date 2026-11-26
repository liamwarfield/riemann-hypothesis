module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousDen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeSignFormDiagEqSignedSumCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivScale

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StConstHolds
open MeasureTheory MvPolynomial GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3

theorem stConst_holds : StConst := by
  intro ι _ G hG
  obtain ⟨hsmooth, hzero, hnonneg, hpos⟩ := hG
  set N := Fintype.card ι
  set f : ℝ → ℝ := iteratedDeriv N G with hf

  have hf0 : ∀ x : ℝ, 1 < x → f x = 0 := by
    intro x hx
    have hev : G =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hzero y (le_of_lt hy)
    rw [hf, Filter.EventuallyEq.iteratedDeriv_eq N hev]
    simp
  have hfc : Continuous f := hsmooth.continuous_iteratedDeriv N (by exact_mod_cast le_top)
  set F : (ι → ℂ) → ℝ := fun w => f (∑ x, ‖w x‖ ^ 2) with hF
  have hFc : Continuous F := by
    apply hfc.comp
    fun_prop
  have hFs : HasCompactSupport F := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) 1)
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    have : ∃ x, 1 < ‖w x‖ := by
      by_contra h
      push_neg at h
      exact absurd ((pi_norm_le_iff_of_nonneg zero_le_one).2 h) (not_le.2 hw)
    obtain ⟨x, hx⟩ := this
    apply hf0
    calc (1 : ℝ) < ‖w x‖ ^ 2 := by nlinarith
      _ ≤ ∑ y, ‖w y‖ ^ 2 :=
        Finset.single_le_sum (f := fun y => ‖w y‖ ^ 2) (fun y _ => by positivity) (Finset.mem_univ x)
  have hFn : 0 ≤ F := fun w => hnonneg _
  have hF0 : F 0 ≠ 0 := by
    simp only [hF, Pi.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact ne_of_gt hpos
  exact ne_of_gt (hFc.integral_pos_of_hasCompactSupport_nonneg_nonzero hFs hFn hF0)

end GlobalTheory.PsCo.Pc3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StExpDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpConjEntriesHasFDerivAtZero
namespace GlobalTheory

theorem exp_conj_entries_hasFDerivAt_zero : ∀ (n : ℕ) (ι : Type) [Fintype ι] (A : (ι → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (p : ι → Fin n × Fin n), (∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = A w (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0) ∧ ∀ s : Matrix (Fin n) (Fin n) ℂ, ∃ L : (ι → ℂ) →L[ℝ] (ι → ℂ), (∀ w x, L w x = (s * A w - A w * s) (p x).1 (p x).2) ∧ HasFDerivAt (fun (w : ι → ℂ) (x : ι) => (NormedSpace.exp (-A w) * s * NormedSpace.exp (A w) : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2) L 0 := by
  intro n ι _ A p
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ι → ℂ) :=
    { toFun := fun M x => M (p x).1 (p x).2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let Ec := LinearMap.toContinuousLinearMap E
  let Ac := LinearMap.toContinuousLinearMap A
  have hA0 : Ac 0 = 0 := map_zero _
  have hnA0 : (-Ac) 0 = 0 := map_zero _
  have h1 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) (Ac 0) := by
    rw [hA0]; exact hasFDerivAt_exp_zero
  have h1' : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _) ((-Ac) 0) := by
    rw [hnA0]; exact hasFDerivAt_exp_zero
  have hexpA : HasFDerivAt (fun w => NormedSpace.exp (Ac w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp Ac) 0 :=
    h1.comp (0 : ι → ℂ) Ac.hasFDerivAt
  have hexpN : HasFDerivAt (fun w => NormedSpace.exp ((-Ac) w))
      ((1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _).comp (-Ac)) 0 :=
    h1'.comp (0 : ι → ℂ) (-Ac).hasFDerivAt
  refine ⟨⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hexpA⟩, fun s => ?_⟩
  · intro w x; rfl
  · have hprod := (hexpN.mul' (hasFDerivAt_const s (0 : ι → ℂ))).mul' hexpA
    refine ⟨_, ?_, (Ec.hasFDerivAt).comp (0 : ι → ℂ) hprod⟩
    intro w x
    have hA0' : A 0 = 0 := map_zero A
    simp only [Ec, E, Ac, hA0', NormedSpace.exp_zero, Pi.mul_apply, map_zero, neg_zero]
    change ((1 * s) * A w + (1 * 0 + (-(A w)) * s) * 1 : Matrix (Fin n) (Fin n) ℂ) (p x).1 (p x).2 = (s * A w - A w * s) (p x).1 (p x).2
    rw [one_mul, mul_zero, zero_add, mul_one, neg_mul, ← sub_eq_add_neg]

end GlobalTheory
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc3

noncomputable def pBLin {n : ℕ} (ε : Fin n → Bool) : (Mode ε → ℂ) →ₗ[ℝ] Mat n where
  toFun := pB ε
  map_add' B C := by
    funext a b
    simp only [pB, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp [star_add]
  map_smul' r B := by
    funext a b
    simp only [pB, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

theorem pB_mode {n : ℕ} (ε : Fin n → Bool) (B : Mode ε → ℂ) (x : Mode ε) :
    pB ε B x.1.1 x.1.2 = B x := by
  unfold pB
  rw [dite_eq_left x.2]

theorem stExpDeriv : StExpDeriv := by
  intro n ε
  obtain ⟨⟨L, hL, hD⟩, h2⟩ :=
    GlobalTheory.exp_conj_entries_hasFDerivAt_zero n (Mode ε) (pBLin ε) (fun x => x.1)
  refine ⟨?_, fun s => ?_⟩
  · have hLid : L = ContinuousLinearMap.id ℝ (Mode ε → ℂ) := by
      ext1 w; funext x
      rw [hL]
      exact pB_mode ε w x
    rw [← hLid]
    exact hD
  · obtain ⟨L', hL', hD'⟩ := h2 (Matrix.diagonal s)
    refine ⟨L', fun w x => ?_, hD'⟩
    rw [hL']
    change (Matrix.diagonal s * pB ε w - pB ε w * Matrix.diagonal s) x.1.1 x.1.2 = _
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, pB_mode]
    ring

end GlobalTheory.PsCo.Pc3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StR
namespace GlobalTheory.PsCo.Pc3

theorem stR : StR := by
  intro n ε
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε
  exact ⟨hcont, hinv, GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact n ε, GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε⟩

end GlobalTheory.PsCo.Pc3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDiagReNonneg
noncomputable section

open Matrix GlobalTheory.PsCo.Pc1
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc3

variable {n : ℕ}

def prP (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else 0

def sgM (ε : Fin n → Bool) : Mat n := diagonal fun i => if ε i then 1 else -1

def bExt (ε : Fin n → Bool) (B : Mode ε → ℂ) (p : Fin n × Fin n) : ℂ :=
  if h : ε p.1 = true ∧ ε p.2 = false then B ⟨p, h⟩ else 0

theorem sum_mode (ε : Fin n → Bool) (g : Fin n × Fin n → ℂ) :
    ∑ x : Mode ε, g x.1 = ∑ i, ∑ j, if ε i = true ∧ ε j = false then g (i, j) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) g, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

theorem prP_mul_pB_apply (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    (prP ε * pB ε B) i j = if ε i = true ∧ ε j = false then bExt ε B (i, j) else 0 := by
  simp only [prP, diagonal_mul, pB, bExt]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem trace_projection_mul_modeMatrix_mul (ε : Fin n → Bool) (B : Mode ε → ℂ) (M : Mat n) :
    trace (prP ε * pB ε B * M) = ∑ x : Mode ε, B x * M x.1.2 x.1.1 := by
  have : ∀ x : Mode ε, B x * M x.1.2 x.1.1 = (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1) x.1 := by
    intro x; simp [bExt, x.2]
  rw [Finset.sum_congr rfl fun x _ => this x, sum_mode ε (fun p : Fin n × Fin n => bExt ε B p * M p.2 p.1)]
  simp only [trace, diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply (M := prP ε * pB ε B)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prP_mul_pB_apply]
  split_ifs <;> simp

theorem pB_apply_swap (ε : Fin n → Bool) (B : Mode ε → ℂ) (i j : Fin n) :
    pB ε B j i = star (pB ε B i j) := by
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem pB_isHermitian (ε : Fin n → Bool) (B : Mode ε → ℂ) : (pB ε B).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply]
  rw [pB_apply_swap ε B j i]

theorem trace_projection_mul_modeMatrix_mul_self (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * pB ε B) = ((∑ x, ‖B x‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_projection_mul_modeMatrix_mul]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pB_apply_swap]
  have : pB ε B x.1.1 x.1.2 = B x := by simp [pB, x.2.1, x.2.2]
  rw [this, show star (B x) = conj (B x) from rfl, Complex.mul_conj']

theorem sgM_mul_sgM (ε : Fin n → Bool) : sgM ε * sgM ε = 1 := by
  rw [sgM, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; split_ifs <;> simp

theorem sgM_pB_sgM (ε : Fin n → Bool) (B : Mode ε → ℂ) : sgM ε * pB ε B * sgM ε = -pB ε B := by
  ext i j
  simp only [sgM, diagonal_mul, mul_diagonal, Matrix.neg_apply]
  simp only [pB]
  by_cases hi : ε i = true <;> by_cases hj : ε j = true <;> simp [hi, hj]

theorem sgM_prP (ε : Fin n → Bool) : sgM ε * prP ε = prP ε * sgM ε := by
  simp only [sgM, prP, diagonal_mul_diagonal, mul_comm]

theorem exp_neg_pB (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    NormedSpace.exp (-pB ε B) = sgM ε * NormedSpace.exp (pB ε B) * sgM ε := by
  have hu : IsUnit (sgM ε) := ⟨⟨sgM ε, sgM ε, sgM_mul_sgM ε, sgM_mul_sgM ε⟩, rfl⟩
  have hinv : (sgM ε)⁻¹ = sgM ε := inv_eq_left_inv (sgM_mul_sgM ε)
  calc NormedSpace.exp (-pB ε B) = NormedSpace.exp (sgM ε * pB ε B * (sgM ε)⁻¹) := by rw [hinv, sgM_pB_sgM]
    _ = sgM ε * NormedSpace.exp (pB ε B) * (sgM ε)⁻¹ := Matrix.exp_conj _ _ hu
    _ = _ := by rw [hinv]

theorem trace_neg_side (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) = -trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) := by
  have hS := sgM_mul_sgM ε
  have hP : prP ε * sgM ε = sgM ε * prP ε := (sgM_prP ε).symm
  have h1 : prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) =
      (sgM ε * (prP ε * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B))) * sgM ε := by
    calc prP ε * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε)
        = prP ε * (sgM ε * sgM ε) * pB ε B * (sgM ε * NormedSpace.exp (pB ε B) * sgM ε) := by rw [hS, mul_one]
      _ = (prP ε * sgM ε) * (sgM ε * pB ε B * sgM ε) * NormedSpace.exp (pB ε B) * sgM ε := by
        simp only [mul_assoc]
      _ = _ := by rw [hP]; simp only [mul_assoc]
  rw [exp_neg_pB, h1, trace_mul_comm, ← mul_assoc, hS, one_mul, sgM_pB_sgM]
  simp [trace_neg]

theorem trace_conj_diag (U : Mat n) (hU : star U * U = 1) (A : Mat n) (v : Fin n → ℂ) :
    trace (A * (U * diagonal v * star U)) = ∑ i, (star U * A * U) i i * v i := by
  have : A * (U * diagonal v * star U) = (A * U * diagonal v) * star U := by simp only [mul_assoc]
  rw [this, trace_mul_comm, ← mul_assoc, ← mul_assoc]
  simp only [trace, diag, mul_diagonal]

theorem conjDiag_re_nonneg (U : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (i : Fin n) :
    ∃ c : ℝ, 0 ≤ c ∧ (star U * prP ε * U) i i = c := by
  refine ⟨∑ k, (if ε k then 1 else 0) * ‖U k i‖ ^ 2, Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  rw [Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [prP, Matrix.mul_diagonal, Matrix.star_apply, show star (U k i) = conj (U k i) from rfl]
  split_ifs
  · rw [mul_one, mul_comm, Complex.mul_conj']; push_cast; ring
  · simp

theorem re_term (c l : ℝ) (hc : 0 ≤ c) :
    2 * (((c : ℂ) * ((l : ℂ) * (l : ℂ))).re) ≤
      ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re - ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re := by
  have h1 : ((c : ℂ) * ((l : ℂ) * (l : ℂ))).re = c * (l * l) := by norm_cast
  have h2 : ((c : ℂ) * ((l : ℂ) * Complex.exp l)).re = c * (l * Real.exp l) := by
    rw [← Complex.ofReal_exp]; norm_cast
  have h3 : ((c : ℂ) * ((l : ℂ) * Complex.exp (-l))).re = c * (l * Real.exp (-l)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]; norm_cast
  rw [h1, h2, h3]
  have hs : l * l ≤ l * Real.sinh l := by
    rcases le_total 0 l with h | h
    · exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.2 h) h
    · have : Real.sinh l ≤ l := by
        have := Real.self_le_sinh_iff.2 (neg_nonneg.2 h); rw [Real.sinh_neg] at this; linarith
      nlinarith
  rw [Real.sinh_eq] at hs
  nlinarith

theorem two_re_le (ε : Fin n → Bool) (B : Mode ε → ℂ) :
    2 * (trace (prP ε * pB ε B * pB ε B)).re ≤
      (trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) - trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B))).re := by
  have hX := pB_isHermitian ε B
  set U : Matrix (Fin n) (Fin n) ℂ := (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hX.eigenvectorUnitary
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self hX.eigenvectorUnitary
  set l : Fin n → ℝ := hX.eigenvalues
  set d : Fin n → ℂ := fun i => (l i : ℂ) with hd
  have hdec : pB ε B = U * diagonal d * star U := by
    have := hX.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hunit : IsUnit U := ⟨⟨U, star U, hU', hU⟩, rfl⟩
  have hinv : U⁻¹ = star U := inv_eq_left_inv hU
  have hexp : ∀ w : Fin n → ℂ, NormedSpace.exp (U * diagonal w * star U) =
      U * diagonal (fun i => Complex.exp (w i)) * star U := by
    intro w
    rw [← hinv, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
  have hdn : diagonal (fun i => -d i) = -diagonal d := by
    ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
  have hneg : -pB ε B = U * diagonal (fun i => -d i) * star U := by
    rw [hdec, hdn, Matrix.mul_neg, Matrix.neg_mul]
  have hmul : ∀ v w : Fin n → ℂ, (U * diagonal v * star U) * (U * diagonal w * star U) =
      U * diagonal (fun i => v i * w i) * star U := by
    intro v w
    calc (U * diagonal v * star U) * (U * diagonal w * star U) = U * diagonal v * (star U * U) * diagonal w * star U := by
          simp only [mul_assoc]
      _ = _ := by rw [hU, mul_one, mul_assoc U, diagonal_mul_diagonal]
  have hE : NormedSpace.exp (pB ε B) = U * diagonal (fun i => Complex.exp (d i)) * star U := by rw [hdec]; exact hexp d
  have hE' : NormedSpace.exp (-pB ε B) = U * diagonal (fun i => Complex.exp (-d i)) * star U := by
    rw [hneg]; exact hexp _
  have t0 : trace (prP ε * pB ε B * pB ε B) = ∑ i, (star U * prP ε * U) i i * (d i * d i) := by
    rw [mul_assoc, hdec, hmul, trace_conj_diag _ hU]
  have t1 : trace (prP ε * pB ε B * NormedSpace.exp (pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (d i)) := by
    rw [mul_assoc, hE, hdec, hmul, trace_conj_diag _ hU]
  have t2 : trace (prP ε * pB ε B * NormedSpace.exp (-pB ε B)) =
      ∑ i, (star U * prP ε * U) i i * (d i * Complex.exp (-d i)) := by
    rw [mul_assoc, hE', hdec, hmul, trace_conj_diag _ hU]
  rw [t0, t1, t2, Complex.re_sum, Finset.mul_sum, Complex.sub_re, Complex.re_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨c, hc, hci⟩ := conjDiag_re_nonneg U ε i
  rw [hci]
  exact re_term c (l i) hc

theorem le_of_le_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ Real.sqrt a * Real.sqrt b) : a ≤ b := by
  rcases eq_or_lt_of_le ha with h0 | h0
  · rw [← h0]; exact hb
  · have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 h0
    have h1 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * Real.sqrt b := by rwa [Real.mul_self_sqrt ha]
    have h2 : Real.sqrt a ≤ Real.sqrt b := le_of_mul_le_mul_left h1 hs
    have := mul_le_mul h2 h2 (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    rwa [Real.mul_self_sqrt ha, Real.mul_self_sqrt hb] at this

theorem stExpLow : StExpLow := by
  intro n ε B
  set E : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp (pB ε B) with hEdef
  have hH : E.IsHermitian := (pB_isHermitian ε B).exp
  set T := trace (prP ε * pB ε B * E)
  have h2 := two_re_le ε B
  rw [trace_neg_side, trace_projection_mul_modeMatrix_mul_self, Complex.ofReal_re] at h2
  have hT : (∑ x, ‖B x‖ ^ 2) ≤ T.re := by
    have : (T - -T).re = 2 * T.re := by simp [Complex.sub_re, Complex.neg_re]; ring
    rw [this] at h2; linarith
  have hTn : ‖T‖ ≤ ∑ x : Mode ε, ‖B x‖ * ‖E x.1.1 x.1.2‖ := by
    rw [show T = ∑ x : Mode ε, B x * E x.1.2 x.1.1 from trace_projection_mul_modeMatrix_mul ε B E]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, ← hH.apply x.1.1 x.1.2, norm_star]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x : Mode ε => ‖B x‖) (fun x : Mode ε => ‖E x.1.1 x.1.2‖)
  have hr : rM ε E = ∑ x : Mode ε, ‖E x.1.1 x.1.2‖ ^ 2 := rfl
  rw [hr]
  exact le_of_le_sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
    (hT.trans ((Complex.re_le_norm T).trans (hTn.trans hcs)))

end GlobalTheory.PsCo.Pc3
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3
open scoped ContDiff

namespace GlobalTheory.PsCo.Pcd

variable {n : ℕ}

theorem iter_zero {G : ℝ → ℝ} (h1 : ∀ x, 1 ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) (k : ℕ) {y : ℝ}
    (hy : 1 < t * y) : iteratedDeriv k (fun x => G (t * x)) y = 0 := by
  have hev : (fun x => G (t * x)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    have : ∀ᶠ x in 𝓝 y, 1 < t * x :=
      (continuous_const.mul continuous_id).continuousAt.eventually (lt_mem_nhds hy)
    filter_upwards [this] with x hx using h1 _ hx.le
  rw [hev.iteratedDeriv_eq k]
  simp

theorem iter_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (t : ℝ) (k : ℕ) :
    Continuous (iteratedDeriv k fun x => G (t * x)) :=
  (hG.comp (contDiff_const.mul contDiff_id)).continuous_iteratedDeriv k (by exact_mod_cast le_top)

theorem norm_le_sqrt {ι : Type} [Fintype ι] (B : ι → ℂ) : ‖B‖ ≤ Real.sqrt (∑ x, ‖B x‖ ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun x => ?_
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun x => ‖B x‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)

theorem muK_univ (ε : Fin n → Bool) : muK ε Set.univ = 1 := by
  unfold Formalism.REAL.muK
  exact Measure.haarMeasure_self

theorem toM_mul (ε : Fin n → Bool) (a b : UJ ε) : toM (a * b) = toM a * toM b := rfl

theorem continuous_toM (ε : Fin n → Bool) : Continuous fun g : UJ ε => toM g :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_ev (P : Poly n) : Continuous fun M : Mat n => ev M P := by
  unfold ev
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun i => ?_)
  rcases i with x | x
  · simp only [Sum.elim_inl]; fun_prop
  · simp only [Sum.elim_inr]; fun_prop

theorem continuous_rM (ε : Fin n → Bool) : Continuous fun M : Mat n => rM ε M := by
  unfold rM; fun_prop

theorem continuous_famF (ε : Fin n → Bool) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (p : ℕ → Poly n) (t : ℝ) :
    Continuous fun M : Mat n => famF ε G p t M := by
  unfold famF bas
  refine continuous_finsetSum _ fun k _ => ?_
  exact (Complex.continuous_ofReal.comp ((iter_cont hG t k).comp (continuous_rM ε))).mul (continuous_ev _)

theorem famF_eq_zero (ε : Fin n → Bool) {G : ℝ → ℝ} (h1 : ∀ x, 1 ≤ x → G x = 0) (p : ℕ → Poly n) {t : ℝ}
    (ht : 0 < t) {M : Mat n} (hM : 1 < t * rM ε M) : famF ε G p t M = 0 := by
  unfold famF bas
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [iter_zero h1 ht k hM]
  simp

theorem blkM_one (ε : Fin n → Bool) : blkM ε (1 : Mat n) = 0 := by
  funext x
  have : x.1.1 ≠ x.1.2 := fun h => by
    have h1 := x.2.1; have h2 := x.2.2; rw [h] at h1; rw [h1] at h2; exact Bool.noConfusion h2
  simp [blkM, Matrix.one_apply_ne this]

theorem blkM_diag (ε : Fin n → Bool) (d : Fin n → ℂ) : blkM ε (Matrix.diagonal d) = 0 := by
  funext x
  have : x.1.1 ≠ x.1.2 := fun h => by
    have h1 := x.2.1; have h2 := x.2.2; rw [h] at h1; rw [h1] at h2; exact Bool.noConfusion h2
  simp [blkM, Matrix.diagonal_apply_ne _ this]

theorem rM_eq_blk (ε : Fin n → Bool) (M : Mat n) : rM ε M = ∑ x, ‖blkM ε M x‖ ^ 2 := rfl

end GlobalTheory.PsCo.Pcd

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3

namespace GlobalTheory.PsCo.Pcd

variable {n : ℕ}

theorem fam_cs (hR : StR) (ε : Fin n → Bool) {G : ℝ → ℝ} (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) {t : ℝ}
    (ht : 0 < t) (w : UJ ε → ℂ) (hw : Continuous w) :
    Continuous (fun g : UJ ε => famF ε G p t (toM g) * w g) ∧
      HasCompactSupport (fun g : UJ ε => famF ε G p t (toM g) * w g) := by
  refine ⟨((continuous_famF ε hG.1 p t).comp (continuous_toM ε)).mul hw, ?_⟩
  refine HasCompactSupport.intro ((hR n ε).2.2.2 (1 / t)) fun g hg => ?_
  have hg' : 1 < t * rM ε (toM g) := by
    simp only [Set.mem_ofPred_eq, not_le] at hg
    rwa [div_lt_iff₀' ht] at hg
  simp [famF_eq_zero ε hG.2.1 p ht hg']

theorem lim1 (hEB : StEB) (hR : StR) (hL : StExpLow) (hD : StExpDeriv) (hF : StFamBlow)
    (ε : Fin n → Bool) (μ : Measure (UJ ε)) (J : (Mode ε → ℂ) → ℝ) (hJc : Continuous J)
    (hpol : ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (k * eB ε B) ∂(muK ε))
    (G : ℝ → ℝ) (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) (w : UJ ε → ℂ) (hw : Continuous w) :
    Tendsto (fun t : ℝ => ∫ g, famF ε G p t (toM g) * w g ∂μ) atTop
      (𝓝 ((J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ) *
        ∫ k, ev (toMK k) (p (nMode ε)) * w k ∂(muK ε))) := by
  obtain ⟨hcEB, hEB0, hEBm⟩ := hEB n ε
  let β : (Mode ε → ℂ) → (Mode ε → ℂ) := fun B => blkM ε (toM (eB ε B))
  have hβe : β = fun B => blkM ε (NormedSpace.exp (pB ε B)) := funext fun B => by
    simp only [β, (hEBm B).1]
  let ψ : ℕ → (Mode ε → ℂ) → ℂ := fun j B =>
    (J B : ℂ) * ∫ k : KG ε, ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B) ∂(muK ε)
  have hcont2 : ∀ j, Continuous (Function.uncurry fun (B : Mode ε → ℂ) (k : KG ε) =>
      ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B)) := fun j => by
    have hm : Continuous fun q : (Mode ε → ℂ) × KG ε => (q.2 : UJ ε) * eB ε q.1 :=
      (continuous_subtype_val.comp continuous_snd).mul (hcEB.comp continuous_fst)
    exact ((continuous_ev _).comp ((continuous_toM ε).comp hm)).mul (hw.comp hm)
  have hψc : ∀ j, Continuous (ψ j) := fun j => by
    refine (Complex.continuous_ofReal.comp hJc).mul ?_
    have := continuous_parametric_integral_of_continuous (μ := muK ε) (hcont2 j) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hβc : Continuous β := by
    show Continuous fun B => blkM ε (toM (eB ε B))
    have hb : Continuous fun M : Mat n => blkM ε M :=
      continuous_pi fun x => (continuous_apply x.1.2).comp (continuous_apply x.1.1)
    exact hb.comp ((continuous_toM ε).comp hcEB)
  have hβ0 : β 0 = 0 := by
    show blkM ε (toM (eB ε 0)) = 0
    rw [hEB0]; exact blkM_one ε
  have hβd : HasFDerivAt β (ContinuousLinearMap.id ℝ (Mode ε → ℂ)) 0 := by
    rw [hβe]; exact (hD n ε).1
  have hco : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ := by
    intro δ hδ
    refine ⟨δ ^ 2, by positivity, fun B hB => ?_⟩
    have h1 := hL n ε B
    have h2 : rM ε (NormedSpace.exp (pB ε B)) = ∑ x, ‖β B x‖ ^ 2 := by
      rw [hβe]; rfl
    refine (norm_le_sqrt B).trans ?_
    rw [← Real.sqrt_sq hδ.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlim := hF (Mode ε) β (fun _ => 1) (ContinuousLinearMap.id ℝ _) (fun _ => one_ne_zero)
    (fun v x => by simp) hβc hβ0 hβd hco G hG ψ hψc
  have hval : ψ (nMode ε) 0 = (J 0 : ℂ) * ∫ k, ev (toMK k) (p (nMode ε)) * w k ∂(muK ε) := by
    simp only [ψ, hEB0, mul_one]
  have heq : ∀ᶠ t : ℝ in atTop, ∫ g, famF ε G p t (toM g) * w g ∂μ =
      ∫ B, ∑ k ∈ Finset.range (Fintype.card (Mode ε) + 1),
        ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    obtain ⟨hc, hs⟩ := fam_cs hR ε hG p ht w hw
    rw [hpol _ hc hs]
    refine integral_congr_ae (Eventually.of_forall fun B => ?_)
    have hr : ∀ k : KG ε, rM ε (toM ((k : UJ ε) * eB ε B)) = ∑ x, ‖β B x‖ ^ 2 := fun k => by
      have := (hR n ε).2.1 k 1 (eB ε B)
      simp only [OneMemClass.coe_one, mul_one] at this
      rw [this]; rfl
    have hint : ∀ j, Integrable (fun k : KG ε => ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B))
        (muK ε) := fun j => by
      have hm : Continuous fun k : KG ε => (k : UJ ε) * eB ε B := continuous_subtype_val.mul continuous_const
      have hc1 : Continuous fun k : KG ε => ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B) :=
        ((continuous_ev _).comp ((continuous_toM ε).comp hm)).mul (hw.comp hm)
      exact integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
    have hpt : ∀ k : KG ε, famF ε G p t (toM ((k : UJ ε) * eB ε B)) * w (k * eB ε B) =
        ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1),
          ((iteratedDeriv j (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) *
            (ev (toM ((k : UJ ε) * eB ε B)) (p j) * w (k * eB ε B)) := fun k => by
      show (∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1), bas ε (iteratedDeriv j fun x => G (t * x)) (p j)
        (toM ((k : UJ ε) * eB ε B))) * _ = _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bas, hr k]
      ring
    show (J B : ℂ) * ∫ k : KG ε, famF ε G p t (toM ((k : UJ ε) * eB ε B)) * w (k * eB ε B) ∂(muK ε) = _
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun j _ => (hint j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  have h2 := hlim.congr' (heq.mono fun t h => h.symm)
  convert h2 using 2
  rw [show Fintype.card (Mode ε) = nMode ε from rfl, hval]
  simp only [norm_one, one_pow, Finset.prod_const_one, Complex.ofReal_one, div_one]
  ring

theorem lim2 (hEB : StEB) (hR : StR) (hL : StExpLow) (hD : StExpDeriv) (hC : StConjLow) (hF : StFamBlow)
    (ε : Fin n → Bool) (μ : Measure (UJ ε)) (J : (Mode ε → ℂ) → ℝ) (hJc : Continuous J)
    (hpol : ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = ∫ B, (J B : ℂ) * ∫ k : KG ε, f (eB ε B * k) ∂(muK ε))
    (G : ℝ → ℝ) (hG : IsProfile (nMode ε) G) (p : ℕ → Poly n) (θ : Fin n → ℝ) (s : UJ ε)
    (hs : toM s = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)))
    (hinj : Function.Injective (fun a => Complex.exp (θ a * Complex.I)))
    (hinv : ∀ k : KG ε, ev (toM ((k : UJ ε)⁻¹ * s * (k : UJ ε))) (p (nMode ε)) = ev (toM s) (p (nMode ε))) :
    Tendsto (fun t : ℝ => ∫ x, famF ε G p t (toM (x⁻¹ * s * x)) ∂μ) atTop
      (𝓝 ((J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ) *
        ev (toM s) (p (nMode ε)) / (dMode ε θ : ℂ))) := by
  obtain ⟨hcEB, hEB0, hEBm⟩ := hEB n ε
  set d : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I) with hd
  let β : (Mode ε → ℂ) → (Mode ε → ℂ) := fun B => blkM ε (toM ((eB ε B)⁻¹ * s * eB ε B))
  have hβe : β = fun B => blkM ε (NormedSpace.exp (-pB ε B) * Matrix.diagonal d * NormedSpace.exp (pB ε B)) :=
    funext fun B => by simp only [β, toM_mul, (hEBm B).1, (hEBm B).2, hs]
  obtain ⟨L, hLd, hLder⟩ := (hD n ε).2 d
  have hdd : ∀ x : Mode ε, d x.1.1 - d x.1.2 ≠ 0 := fun x h => by
    have hne : x.1.1 ≠ x.1.2 := fun h' => by
      have h1 := x.2.1; have h2 := x.2.2; rw [h'] at h1; rw [h1] at h2; exact Bool.noConfusion h2
    exact hne (hinj (sub_eq_zero.1 h))
  let ψ : ℕ → (Mode ε → ℂ) → ℂ := fun j B =>
    (J B : ℂ) * ∫ k : KG ε, ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) ∂(muK ε)
  have hcont2 : ∀ j, Continuous (Function.uncurry fun (B : Mode ε → ℂ) (k : KG ε) =>
      ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j)) := fun j => by
    have hy : Continuous fun q : (Mode ε → ℂ) × KG ε => (eB ε q.1)⁻¹ * s * eB ε q.1 :=
      ((hcEB.comp continuous_fst).inv.mul continuous_const).mul (hcEB.comp continuous_fst)
    have hk : Continuous fun q : (Mode ε → ℂ) × KG ε => (q.2 : UJ ε) := continuous_subtype_val.comp continuous_snd
    exact (continuous_ev _).comp ((continuous_toM ε).comp ((hk.inv.mul hy).mul hk))
  have hψc : ∀ j, Continuous (ψ j) := fun j => by
    refine (Complex.continuous_ofReal.comp hJc).mul ?_
    have := continuous_parametric_integral_of_continuous (μ := muK ε) (hcont2 j) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hβc : Continuous β := by
    have hb : Continuous fun M : Mat n => blkM ε M :=
      continuous_pi fun x => (continuous_apply x.1.2).comp (continuous_apply x.1.1)
    exact hb.comp ((continuous_toM ε).comp ((hcEB.inv.mul continuous_const).mul hcEB))
  have hβ0 : β 0 = 0 := by
    show blkM ε (toM ((eB ε 0)⁻¹ * s * eB ε 0)) = 0
    rw [hEB0, inv_one, one_mul, mul_one, hs]; exact blkM_diag ε _
  have hβd : HasFDerivAt β L 0 := by rw [hβe]; exact hLder
  have hco : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ := by
    intro δ hδ
    obtain ⟨η, hη, hη'⟩ := hC n ε s d hs hinj (δ ^ 2) (by positivity)
    refine ⟨η, hη, fun B hB => ?_⟩
    have h3 := hη' (eB ε B) (by rw [rM_eq_blk]; exact hB)
    have h1 := hL n ε B
    rw [← (hEBm B).1] at h1
    refine (norm_le_sqrt B).trans ?_
    rw [← Real.sqrt_sq hδ.le]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlim := hF (Mode ε) β (fun x => d x.1.1 - d x.1.2) L hdd hLd hβc hβ0 hβd hco G hG ψ hψc
  have hval : ψ (nMode ε) 0 = (J 0 : ℂ) * ev (toM s) (p (nMode ε)) := by
    simp only [ψ, hEB0, inv_one, one_mul, mul_one]
    rw [integral_congr_ae (Eventually.of_forall hinv)]
    rw [integral_const, Measure.real, muK_univ]
    simp
  obtain ⟨η, hη, hη'⟩ := hC n ε s d hs hinj 1 one_pos
  have heq : ∀ᶠ t : ℝ in atTop, ∫ x, famF ε G p t (toM (x⁻¹ * s * x)) ∂μ =
      ∫ B, ∑ k ∈ Finset.range (Fintype.card (Mode ε) + 1),
        ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B := by
    filter_upwards [eventually_gt_atTop (1 / η)] with t ht
    have ht0 : 0 < t := lt_trans (by positivity) ht
    have hc : Continuous fun x : UJ ε => famF ε G p t (toM (x⁻¹ * s * x)) :=
      (continuous_famF ε hG.1 p t).comp ((continuous_toM ε).comp ((continuous_inv.mul continuous_const).mul
        continuous_id))
    have hcs : HasCompactSupport fun x : UJ ε => famF ε G p t (toM (x⁻¹ * s * x)) := by
      refine HasCompactSupport.intro ((hR n ε).2.2.2 1) fun x hx => ?_
      by_contra hne
      have hle : t * rM ε (toM (x⁻¹ * s * x)) ≤ 1 := by
        by_contra hlt; exact hne (famF_eq_zero ε hG.2.1 p ht0 (not_le.1 hlt))
      have h4 : rM ε (toM (x⁻¹ * s * x)) ≤ η := by
        have h5 : rM ε (toM (x⁻¹ * s * x)) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
        have h6 : 1 / t < η := by rw [div_lt_iff₀ ht0]; rw [div_lt_iff₀ hη] at ht; linarith
        linarith
      exact hx (hη' x h4)
    rw [hpol _ hc hcs]
    refine integral_congr_ae (Eventually.of_forall fun B => ?_)
    have hr : ∀ k : KG ε, rM ε (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) = ∑ x, ‖β B x‖ ^ 2 :=
      fun k => by
        have := (hR n ε).2.1 k⁻¹ k ((eB ε B)⁻¹ * s * eB ε B)
        simp only [InvMemClass.coe_inv] at this
        rw [this]; rfl
    have hint : ∀ j, Integrable (fun k : KG ε =>
        ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j)) (muK ε) := fun j => by
      have hk : Continuous fun k : KG ε => (k : UJ ε) := continuous_subtype_val
      have hc1 : Continuous fun k : KG ε => ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) :=
        (continuous_ev _).comp ((continuous_toM ε).comp ((hk.inv.mul continuous_const).mul hk))
      exact integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
    have hpt : ∀ k : KG ε, famF ε G p t (toM ((eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)))) =
        ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1),
          ((iteratedDeriv j (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) *
            ev (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) (p j) := fun k => by
      have hg : (eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)) = (k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * k := by group
      rw [hg]
      show ∑ j ∈ Finset.range (Fintype.card (Mode ε) + 1), bas ε (iteratedDeriv j fun x => G (t * x)) (p j)
        (toM ((k : UJ ε)⁻¹ * ((eB ε B)⁻¹ * s * eB ε B) * (k : UJ ε))) = _
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bas, hr k]
    show (J B : ℂ) * ∫ k : KG ε, famF ε G p t (toM ((eB ε B * (k : UJ ε))⁻¹ * s * (eB ε B * (k : UJ ε)))) ∂(muK ε) = _
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_finsetSum _ fun j _ => (hint j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  have h2 := hlim.congr' (heq.mono fun t h => h.symm)
  convert h2 using 2
  rw [show Fintype.card (Mode ε) = nMode ε from rfl, hval]
  simp only [dMode, d]
  push_cast
  ring

end GlobalTheory.PsCo.Pcd

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3

namespace GlobalTheory.PsCo.Pcd

theorem stLim_of (hEB : StEB) (hR : StR) (hP : StPolar) (hL : StExpLow) (hD : StExpDeriv) (hC : StConjLow)
    (hF : StFamBlow) (hK : StConst) : StLim := by
  intro n ε μ _ G hG
  obtain ⟨J, hJc, hJ0, hpol⟩ := hP n ε μ
  have hκ := hK (Mode ε) G hG
  refine ⟨(J 0 : ℂ) * ((∫ v : Mode ε → ℂ, iteratedDeriv (nMode ε) G (∑ x, ‖v x‖ ^ 2) : ℝ) : ℂ),
    mul_ne_zero (by exact_mod_cast hJ0.ne') (by exact_mod_cast hκ), fun p => ⟨fun w hw => ?_, ?_⟩⟩
  · have := lim1 hEB hR hL hD hF ε μ J hJc (fun f hf hs => (hpol f hf hs).1) G hG p w hw
    simpa only [mul_assoc] using this
  · intro θ s hs hinj hinv
    have := lim2 hEB hR hL hD hC hF ε μ J hJc (fun f hf hs => (hpol f hf hs).2) G hG p θ s hs hinj hinv
    simpa only [mul_assoc, mul_div_assoc] using this

end GlobalTheory.PsCo.Pcd

end
end

namespace GlobalTheory.PsCo.Pcd

theorem stLim : GlobalTheory.PsCo.Pc1.StLim :=
  stLim_of GlobalTheory.PsCo.Pc3.stEB GlobalTheory.PsCo.Pc3.stR GlobalTheory.PsCo.Pc3.stPolar GlobalTheory.PsCo.Pc3.stExpLow GlobalTheory.PsCo.Pc3.stExpDeriv GlobalTheory.PsCo.Pcd.stConjLow GlobalTheory.PsCo.Pcd.stFamBlow GlobalTheory.PsCo.Pc3.stConst_holds

end GlobalTheory.PsCo.Pcd
