module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSchurBilinearEntry
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

theorem det_schur_bilinear_entry (B : Type) [Fintype B] [DecidableEq B]
    (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ)
    (hq : q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z') (hq0 : q ≠ 0) :
    (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1) := by
  classical
  let e : Option B ≃ B ⊕ Unit := Equiv.optionEquivSumPUnit B
  let R := Matrix.reindex e e Q
  have hR : R.det = Q.det := Matrix.det_reindex_self e Q
  let Pz : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z b) 1
  let Pz' : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z' b) 1
  have hPz : Pz.det = 1 := by simp [Pz, Matrix.det_fromBlocks_zero₁₂]
  have hPz' : Pz'.det = 1 := by simp [Pz', Matrix.det_fromBlocks_zero₁₂]
  let u : B → ℂ := fun a => ∑ c, Q (some a) c * Option.elim c 1 z'
  let v : B → ℂ := fun b => ∑ c, Option.elim c 1 z * Q c (some b)
  let D : Matrix Unit Unit ℂ := Matrix.of fun _ _ => q
  let M : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ :=
    Matrix.fromBlocks (Matrix.of fun a b => Q (some a) (some b)) (Matrix.of fun a _ => u a)
      (Matrix.of fun _ b => v b) D
  have hM : M = Pz * R * Pz'ᵀ := by
    ext i j
    rcases i with a | ⟨⟩ <;> rcases j with b | ⟨⟩ <;>
      simp [M, Pz, Pz', R, e, u, v, D, hq, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_option,
        Matrix.one_apply, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc, add_comm]
    all_goals
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : M.det = Q.det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hPz, hPz', hR]; ring
  letI : Invertible D := ⟨Matrix.of fun _ _ => q⁻¹, by ext; simp [D, Matrix.mul_apply, hq0],
    by ext; simp [D, Matrix.mul_apply, hq0]⟩
  rw [Matrix.det_fromBlocks₂₂] at hdet
  have hD : D.det = q := by simp [D, Matrix.det_unique]
  rw [hD] at hdet
  have hS : (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2) =
      q⁻¹ • ((Matrix.of fun a b => Q (some a) (some b)) - (Matrix.of fun a (_ : Unit) => u a) * ⅟D *
        (Matrix.of fun (_ : Unit) b => v b)) := by
    ext a b
    simp [u, v, D, Matrix.mul_apply, invOf_eq_inv]
    field_simp
  rw [hS, Matrix.det_smul, ← hdet, pow_succ, inv_pow]
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogAffForm
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section

namespace GlobalTheory.LogHermHess

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι]

def affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (c j + L j x)

theorem hasFDerivAt_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x : E) :
    HasFDerivAt (fun y => c + L y) L x := L.hasFDerivAt.const_add c

theorem contDiff_aff (c : ℂ) (L : E →L[ℂ] ℂ) : ContDiff ℝ 2 (fun y => c + L y) :=
  contDiff_const.add (L.restrictScalars ℝ).contDiff

theorem contDiff_conj_aff (c : ℂ) (L : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (starRingEnd ℂ) (c + L y)) :=
  Complex.conjCLE.contDiff.comp (contDiff_aff c L)

theorem del_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : del (fun y => c + L y) x v = L v := by
  rw [del_eq_fderiv (hasFDerivAt_aff c L x).differentiableAt, (hasFDerivAt_aff c L x).fderiv]

theorem dbar_aff (c : ℂ) (L : E →L[ℂ] ℂ) (x v : E) : dbar (fun y => c + L y) x v = 0 := by
  rw [dbar_eq_zero (hasFDerivAt_aff c L x).differentiableAt]; rfl

theorem contDiff_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) :=
  ((contDiff_aff c L).mul contDiff_const).mul (contDiff_conj_aff c' L')

theorem del_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    del (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = L v * q * (starRingEnd ℂ) (c' + L' x) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [del_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    del_mul h1 (differentiableAt_const q), del_conj, dbar_aff, del_aff]
  simp

theorem dbar_term (c c' q : ℂ) (L L' : E →L[ℂ] ℂ) (x v : E) :
    dbar (fun y => (c + L y) * q * (starRingEnd ℂ) (c' + L' y)) x v
      = (c + L x) * q * (starRingEnd ℂ) (L' v) := by
  have h1 := (contDiff_aff c L).differentiable two_ne_zero x
  have h2 := (contDiff_conj_aff c' L').differentiable two_ne_zero x
  rw [dbar_mul (a := fun y => (c + L y) * q) (h1.mul_const q) h2,
    dbar_mul h1 (differentiableAt_const q), dbar_conj, dbar_aff, del_aff]
  simp

theorem contDiff_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) :
    ContDiff ℝ 2 (affForm Q c L) :=
  ContDiff.sum fun _ _ => ContDiff.sum fun _ _ => contDiff_term _ _ _ _ _

theorem del_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    del (affForm Q c L) x v = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x) := by
  unfold affForm
  rw [del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => del_term _ _ _ _ _ _ _

theorem dbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v : E) :
    dbar (affForm Q c L) x v = ∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j v) := by
  unfold affForm
  rw [dbar_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dbar_sum fun j _ =>
    (contDiff_term (c i) (c j) (Q i j) (L i) (L j)).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => dbar_term _ _ _ _ _ _ _

theorem ddbar_affForm (Q : Matrix ι ι ℂ) (c : ι → ℂ) (L : ι → E →L[ℂ] ℂ) (x v w : E) :
    ddbar (affForm Q c L) x v w = ∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w) := by
  rw [ddbar_eq_del_dbar (contDiff_affForm Q c L).contDiffAt]
  have : (fun y => dbar (affForm Q c L) y w)
      = affForm Q c L ∘ id - affForm Q c L ∘ id + fun y => ∑ i, ∑ j,
        (c i + L i y) * Q i j * (starRingEnd ℂ) (L j w + (0 : E →L[ℂ] ℂ) y) := by
    funext y; simp [dbar_affForm]
  rw [this, sub_self, zero_add,
    del_sum fun i _ => (ContDiff.sum fun j _ =>
    contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [del_sum fun j _ =>
    (contDiff_term (c i) (L j w) (Q i j) (L i) 0).differentiable two_ne_zero x,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [del_term]; simp

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem ofReal_re_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x : E) : ((affForm Q c L x).re : ℂ) = affForm Q c L x := by
  rw [← Complex.conj_eq_iff_re, affForm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : (starRingEnd ℂ) (Q j i) = Q i j := hQ.apply i j
  rw [this]; ring

theorem leviForm_log_affForm {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ι → ℂ)
    (L : ι → E →L[ℂ] ℂ) (x v w : E) (hx : affForm Q c L x ≠ 0) :
    leviForm (fun y => Real.log (affForm Q c L y).re) x v w
      = (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x
        - (∑ i, ∑ j, L i v * Q i j * (starRingEnd ℂ) (c j + L j x))
          * (∑ i, ∑ j, (c i + L i x) * Q i j * (starRingEnd ℂ) (L j w)) / affForm Q c L x ^ 2 := by
  have hre : (fun y => ((affForm Q c L y).re : ℂ)) = affForm Q c L :=
    funext (ofReal_re_affForm hQ c L)
  have hx' : (affForm Q c L x).re ≠ 0 := fun h => hx (by
    rw [← ofReal_re_affForm hQ c L x, h]; simp)
  have ht : ContDiffAt ℝ 2 (fun y => (affForm Q c L y).re) x :=
    (Complex.reCLM.contDiff.comp (contDiff_affForm Q c L)).contDiffAt
  rw [leviForm_real_comp (h := Real.log) (t := fun y => (affForm Q c L y).re)
    (Real.contDiffAt_log.2 hx') ht, leviForm, hre, ddbar_affForm, del_affForm, dbar_affForm,
    Real.deriv_log', deriv_inv]
  push_cast
  rw [ofReal_re_affForm hQ]
  ring

end General

theorem leviForm_log_herm : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2 := by
  intro n B _ _ e _ Q hQ u z hu h q hq hq0 a b
  let c : Option B → ℂ := fun i => Option.elim i 1 (fun a => z (e a))
  let L : Option B → (B → ℂ) →L[ℂ] ℂ := fun i => Option.elim i 0 (fun a => ContinuousLinearMap.proj a)
  let M : (B → ℂ) →L[ℂ] V n :=
    ∑ a, (ContinuousLinearMap.proj a : (B → ℂ) →L[ℂ] ℂ).smulRight (coordVec (e a))
  have hM : ∀ t, M t = ∑ a, t a • coordVec (e a) := fun t => by
    simp [M, ContinuousLinearMap.sum_apply]
  have hM1 : ∀ a, M (Pi.single a 1) = coordVec (e a) := fun a => by
    rw [hM]; simp [Pi.single_apply, ite_smul]
  have hφ : HasFDerivAt (fun t => z + M t) M 0 := M.hasFDerivAt.const_add z
  have h0 : z + M 0 = z := by simp
  have hc := leviForm_comp_holo (u := u) (φ := fun t => z + M t) (z := 0) (by rw [h0]; exact hu)
    (contDiff_const.add M.contDiff).contDiffAt (Pi.single a 1) (Pi.single b 1)
  rw [hφ.fderiv, hM1, hM1, h0] at hc
  have hw : ∀ (t : B → ℂ) i, Option.elim i 1 (fun a => z (e a) + t a) = c i + L i t := by
    intro t i; cases i <;> simp [c, L]
  have hf : (fun t => u (z + M t)) = fun t => Real.log (affForm Q c L t).re := by
    funext t
    rw [hM, h, affForm]
    simp only [hw]
    rfl
  have hq' : affForm Q c L 0 = q := by
    rw [hq, affForm]; simp [c]
  rw [← hc, hf, leviForm_log_affForm hQ _ _ _ _ _ (hq' ▸ hq0), hq']
  have hL : ∀ (a : B) i, L i (Pi.single a 1) = if i = some a then 1 else 0 := by
    intro a i; cases i <;> simp [L, Pi.single_apply]
  simp only [hL, map_zero, add_zero, apply_ite (starRingEnd ℂ), map_one, ite_mul, mul_ite, one_mul,
    zero_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rfl

end GlobalTheory.LogHermHess
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefGrD
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.SchurRow

theorem schur {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (M : Matrix (A ⊕ B) (A ⊕ B) ℂ)
    (hM : M.PosDef) : ∃ Q : Matrix B B ℂ, Q.PosDef ∧ Q.det * M.toBlocks₁₁.det = M.det ∧ ∀ w : B → ℂ,
      (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b) * M *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 (Matrix.of fun (_ : Unit) b => w b))ᴴ).det =
        M.toBlocks₁₁.det * ∑ a, ∑ b, w a * Q a b * star (w b) := by
  have h11 : M.toBlocks₁₁.PosDef := hM.submatrix Sum.inl_injective
  have e : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    ext (a | a) (b | b) <;> try rfl
    exact (hM.isHermitian.apply _ _).symm
  generalize M.toBlocks₁₁ = P at h11 e
  generalize M.toBlocks₁₂ = R at e
  generalize M.toBlocks₂₂ = S at e
  subst e
  have := h11.isUnit.invertible
  have hd := Matrix.det_fromBlocks₁₁ P R Rᴴ S
  rw [Matrix.invOf_eq_nonsing_inv] at hd
  refine ⟨S - Rᴴ * P⁻¹ * R, ?_, by rw [hd, mul_comm], fun w => ?_⟩
  · refine ((h11.fromBlocks₁₁ R S).1 hM.posSemidef).posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 ?_)
    have := hM.det_pos.ne'
    rw [hd] at this
    exact (right_ne_zero_of_mul this).isUnit
  · generalize hW : (Matrix.of fun (_ : Unit) b => w b) = W
    have : Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W * Matrix.fromBlocks P R Rᴴ S *
        (Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 W)ᴴ = Matrix.fromBlocks P (R * Wᴴ) (W * Rᴴ) (W * S * Wᴴ) := by
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    rw [this, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have e2 : W * S * Wᴴ - W * Rᴴ * P⁻¹ * (R * Wᴴ) = W * (S - Rᴴ * P⁻¹ * R) * Wᴴ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [e2]
    congr 1
    rw [Matrix.det_unique, Finset.sum_comm]
    subst hW
    generalize S - Rᴴ * P⁻¹ * R = Q
    simp [Matrix.mul_apply, Finset.sum_mul]

noncomputable def ixA {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Option {j : Low s // j.1.2 = i} ≃ Fin s :=
  Equiv.ofBijective (Sum.elim Subtype.val fun b => Option.elim b i fun j => j.1.1.1) (by
    constructor
    · rintro (⟨a, ha⟩ | _ | ⟨⟨⟨a, a'⟩, ha⟩, h'⟩) (⟨b, hb⟩ | _ | ⟨⟨⟨b, b'⟩, hb⟩, h⟩) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Option.elim] at e <;> (try dsimp only at h) <;>
        (try dsimp only at h') <;> (try dsimp only at ha) <;> (try dsimp only at hb) <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · intro c
      rcases lt_trichotomy c i with h | h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr none, h.symm⟩, ⟨.inr (some ⟨⟨(c, i), h⟩, rfl⟩), rfl⟩])

noncomputable def ixB {s : ℕ} (i : Fin s) : {a : Fin s // (a : ℕ) < i} ⊕ Unit ≃ {a : Fin s // (a : ℕ) < i + 1} :=
  Equiv.ofBijective (Sum.elim (fun a => ⟨a.1, a.2.trans (Nat.lt_succ_self _)⟩) fun _ => ⟨i, Nat.lt_succ_self _⟩) (by
    constructor
    · rintro (⟨a, ha⟩ | _) (⟨b, hb⟩ | _) e <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at e <;> subst_vars <;>
        first | rfl | (exfalso; omega)
    · rintro ⟨c, hc⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
      exacts [⟨.inl ⟨c, h⟩, rfl⟩, ⟨.inr (), Subtype.ext (Fin.ext h.symm)⟩])

theorem det_upU {s : ℕ} (y : Low s → ℂ) : (upU y).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [upU]
  · intro a b h
    have h : b < a := h
    simp [upU, h.not_gt, h.ne']

theorem row_lt {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) {a : Fin s}
    (ha : a < i) : upU y' a = upU (fun j => if j.1.2 < i then y j else 0) a := by
  funext c
  simp only [upU, Matrix.of_apply]
  split_ifs with h1
  · exact h _ ha
  all_goals rfl

theorem row_ge {s : ℕ} {i : Fin s} (y : Low s → ℂ) {a : Fin s} (ha : i ≤ a) (c : Fin s) :
    upU (fun j => if j.1.2 < i then y j else 0) a c = if a = c then 1 else 0 := by
  simp only [upU, Matrix.of_apply, ha.not_gt, if_false]
  split_ifs with h1 h2
  · exact absurd h2 h1.ne
  all_goals rfl

theorem rows_eq {s : ℕ} {i : Fin s} {y y' : Low s → ℂ} (h : ∀ j : Low s, j.1.2 < i → y' j = y j) :
    (upU y').submatrix (fun a => (ixB i a).1) id =
      Matrix.fromBlocks 1 0 0 (Matrix.of fun (_ : Unit) (b : Option {j : Low s // j.1.2 = i}) =>
        (Option.elim b 1 (fun b => y' b.1) : ℂ)) *
        (upU (fun j => if j.1.2 < i then y j else 0)).submatrix (ixA i) id := by
  refine Matrix.ext ?_
  rintro (a | a) c <;> refine Eq.trans ?_ Matrix.mul_apply.symm
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.submatrix_apply, id]
    exact congrFun (row_lt h a.2) c
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Matrix.submatrix_apply, id, Matrix.of_apply]
    have hr : ∀ b, upU (fun j => if j.1.2 < i then y j else 0) (ixA i (.inr b)) c =
        if ixA i (.inr b) = c then 1 else 0 := by
      rintro (_ | ⟨j, rfl⟩)
      exacts [row_ge y le_rfl c, row_ge y (le_of_lt j.2) c]
    simp only [hr]
    change upU y' i c = _
    obtain ⟨c | c, rfl⟩ := (ixA i).surjective c
    · have h1 : ixA i (.inl c) < i := c.2
      simp [upU, h1.not_gt, h1.ne']
    · simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      obtain _ | ⟨⟨⟨b, a⟩, hab⟩, rfl⟩ := c
      · change upU y' i i = 1
        simp [upU]
      · exact dif_pos hab

theorem conj_mul {A B C : Type} [Fintype B] [Fintype C] (W : Matrix A B ℂ) (R : Matrix B C ℂ) (G : Matrix C C ℂ) :
    W * R * G * (W * R)ᴴ = W * (R * G * Rᴴ) * Wᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.FlagCell2.SchurRow


open GlobalTheory.FlagCell2.SchurRow in
theorem GlobalTheory.FlagCell2.exists_posDef_grD : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re := by
  intro s G hG y i
  set U := upU (fun j : Low s => if j.1.2 < i then y j else 0) with hU
  have hdU : U.det = 1 := det_upU _
  have hM0 : (U * G * Uᴴ).PosDef := hG.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by simp [hdU])))
  have hM : ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).PosDef := hM0.submatrix (ixA i).injective
  obtain ⟨Q, hQ, hdet, hw⟩ := schur _ hM
  have hpos : 0 < ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := (hM.submatrix Sum.inl_injective).det_pos
  have h11 : ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → leadMinor (upU y' * G * (upU y')ᴴ) i =
      ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det := fun y' h => by
    unfold leadMinor
    congr 1
    ext a b
    change (upU y' * G * (upU y')ᴴ) a b = (U * G * Uᴴ) a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, row_lt h a.2, row_lt h b.2, hU]
  refine ⟨Q, hQ, ?_, fun y' h => ?_⟩
  · rw [h11 y fun _ _ => rfl, hdet, Matrix.det_submatrix_equiv_self]
    simp [hdU]
  · have e := hw fun b => Option.elim b 1 (fun b => y' b.1)
    replace e : leadMinor (upU y' * G * (upU y')ᴴ) (i + 1) = _ := Eq.trans (by
      unfold leadMinor
      rw [← Matrix.det_submatrix_equiv_self (ixB i)]
      congr 1
      have e1 : (U * G * Uᴴ).submatrix (ixA i) (ixA i) = U.submatrix (ixA i) id * G * (U.submatrix (ixA i) id)ᴴ := rfl
      have e2 : ((upU y' * G * (upU y')ᴴ).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < i + 1} → Fin s)
          Subtype.val).submatrix (ixB i) (ixB i) =
          (upU y').submatrix (fun a => (ixB i a).1) id * G * ((upU y').submatrix (fun a => (ixB i a).1) id)ᴴ := rfl
      rw [e1, e2, rows_eq h]
      exact conj_mul _ _ _) e
    rw [grD, e, h11 y' h]
    generalize ((U * G * Uᴴ).submatrix (ixA i) (ixA i)).toBlocks₁₁.det = d at hpos
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hpos
    rw [Complex.mul_re, ← h2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h1.ne']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRow
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem card_row_sub (s : ℕ) (i : Fin s) : Fintype.card {j : Low s // j.1.2 = i} = s - 1 - i := by
  rw [← Fin.card_Ioi, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun j => ⟨j.1.1.1, by simpa [Finset.mem_Ioi, ← j.2] using j.1.2⟩
      invFun := fun c => ⟨⟨(c.1, i), Finset.mem_Ioi.mp c.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl⟩; rfl
  · rintro ⟨c, hc⟩; rfl

noncomputable def rowEquiv {ι : Type} (m : ι → ℕ) (τ : ι) (i : Fin (m τ)) :
    {j : Low (m τ) // j.1.2 = i} ≃ {j : Cell m // j.root = ⟨τ, i⟩} :=
  Equiv.ofBijective (fun b => ⟨⟨τ, b.1⟩, by simp [Cell.root, b.2]⟩) (by
    constructor
    · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
      simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact Subtype.ext h
    · rintro ⟨⟨σ, l⟩, h⟩
      simp only [Cell.root, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨⟨l, eq_of_heq h2⟩, rfl⟩)

theorem add_sum_coord_apply {n : ℕ} {B : Type} [Fintype B] (e : B → Fin n) (he : Function.Injective e)
    (z : V n) (t : B → ℂ) (k : Fin n) :
    (z + ∑ a, t a • coordVec (e a)) k = z k + ∑ a, if k = e a then t a else 0 := by
  simp [coordVec, Finset.sum_apply, PiLp.single_apply, Pi.single_apply, mul_ite]

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem quad_pos {B : Type} [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (hQ : Q.PosDef)
    (z : B → ℂ) : 0 < ∑ a, ∑ b, Option.elim a 1 z * Q a b * star (Option.elim b 1 z) := by
  have hv : (fun a => star (Option.elim a 1 z)) ≠ 0 := by
    intro h; have := congrFun h none; simp at this
  have := hQ.dotProduct_mulVec_pos hv
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det_of (hR : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2) (hD : ∀ (B : Type) [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ), q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z' → q ≠ 0 → (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') * (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1)) (hQ : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re) (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) : Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  obtain ⟨τ, i⟩ := x
  have hsm := GlobalTheory.CellPotSmooth.cellPot_contDiffAt ι m n d ε G w ⟨τ, i⟩ hG hs
  have hcard : Fintype.card {j : Cell m // j.root = ⟨τ, i⟩} = m τ - 1 - i := by
    rw [← Fintype.card_congr (rowEquiv m τ i), card_row_sub]
  refine ⟨hcard, ?_⟩
  simp only at hG hs hsm ⊢
  let e : {j : Low (m τ) // j.1.2 = i} → Fin n := fun b => ε.symm (.inr ⟨τ, b.1⟩)
  have he : Function.Injective e := by
    intro b b' h
    have := ε.symm.injective h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact Subtype.ext this
  set y : Low (m τ) → ℂ := fun s => fb ε w ⟨τ, s⟩ with hy
  obtain ⟨Q, hQpd, hQdet, hQg⟩ := hQ (m τ) (G (bsL ε w) τ) hG y i
  set q : ℂ := ∑ a, ∑ b, Option.elim a 1 (fun a => w (e a)) * Q a b * star (Option.elim b 1 (fun b => w (e b))) with hq
  have hqpos : 0 < q := quad_pos Q hQpd _
  have hgr : grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = q.re := hQg y (fun _ _ => rfl)
  have hqre : q = ((grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℝ) : ℂ) := by
    rw [hgr]; exact Complex.ext rfl (by simp [(Complex.pos_iff.mp hqpos).2])
  have hq0 : q ≠ 0 := hqpos.ne'
  have hstar : ∀ c : Option {j : Low (m τ) // j.1.2 = i}, star (Option.elim c 1 (fun c => w (e c))) = Option.elim c 1 (fun c => star (w (e c))) := by
    intro c; cases c <;> simp
  have hres : ∀ t : {j : Low (m τ) // j.1.2 = i} → ℂ, (fun v => -cellPot ε G ⟨τ, i⟩ v) (w + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => w (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => w (e b) + t b))).re) := by
    intro t
    set w' := w + ∑ a, t a • coordVec (e a) with hw'
    have hb : bsL ε w' = bsL ε w := by
      ext c
      simp only [bsL_apply, hw', add_sum_coord_apply e he]
      rw [Finset.sum_eq_zero]
      · simp
      intro a _
      rw [ite_eq_right]
      simp [e]
    have hf : ∀ s : Low (m τ), fb ε w' ⟨τ, s⟩ = y s + if h : s.1.2 = i then t ⟨s, h⟩ else 0 := by
      intro s
      simp only [fb, hy, hw', add_sum_coord_apply e he]
      congr 1
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨s, h⟩]
        · simp [e]
        · intro b _ hb
          rw [ite_eq_right]
          intro h'
          exact hb (he (show e ⟨s, h⟩ = e b from h')).symm
        · simp
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right]
        intro h'
        have := ε.symm.injective h'
        simp only [e, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact h (this ▸ b.2)
    have hfa : ∀ a : Option {j : Low (m τ) // j.1.2 = i}, Option.elim a 1 (fun a => fb ε w' ⟨τ, a.1⟩) = Option.elim a 1 (fun a => w (e a) + t a) := by
      rintro (_ | b)
      · rfl
      · simp only [Option.elim, hf, dite_eq_left b.2]
        rfl
    simp only [cellPot, neg_neg]
    rw [hb, show upM (fb ε w') τ = upU (fun s => fb ε w' ⟨τ, s⟩) from rfl,
      hQg _ (fun j hj => by rw [hf, dite_eq_right (ne_of_lt hj)]; simp)]
    simp only [hfa]
  have hR' := hR n {j : Low (m τ) // j.1.2 = i} e he Q hQpd.1 (fun v => -cellPot ε G ⟨τ, i⟩ v) w hsm.1.neg hres q hq hq0
  have hD' := hD {j : Low (m τ) // j.1.2 = i} Q (fun a => w (e a)) (fun b => star (w (e b))) q (by rw [hq]; simp only [hstar]) hq0
  rw [← Matrix.det_submatrix_equiv_self (rowEquiv m τ i)]
  have hM : (Matrix.of fun a b : {j : Cell m // j.root = ⟨τ, i⟩} => -leviForm (cellPot ε G ⟨τ, i⟩) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).submatrix (rowEquiv m τ i) (rowEquiv m τ i) = Matrix.of fun a b : {j : Low (m τ) // j.1.2 = i} => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 (fun b => star (w (e b)))) * (∑ c, Option.elim c 1 (fun a => w (e a)) * Q c (some b)) / q ^ 2 := by
    ext a b
    have := hR' a b
    simp only [leviForm_neg, ContinuousLinearMap.neg_apply, hstar] at this
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, ← this]
    rfl
  rw [hM, hD', card_row_sub]
  have hQd := hQpd.det_pos
  have hGd := hG.det_pos
  obtain ⟨hQr, hQi⟩ := Complex.pos_iff.mp hQd
  obtain ⟨hGr, hGi⟩ := Complex.pos_iff.mp hGd
  have h1 : Q.det = (Q.det.re : ℂ) := Complex.ext rfl (by simp [hQi])
  have h2 : (G (bsL ε w) τ).det = ((G (bsL ε w) τ).det.re : ℂ) := Complex.ext rfl (by simp [hGi])
  have hQdet' : Q.det * leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (G (bsL ε w) τ).det := hQdet
  have hQ0 : (Q.det.re : ℂ) ≠ 0 := by exact_mod_cast hQr.ne'
  have hL : leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (((G (bsL ε w) τ).det.re / Q.det.re : ℝ) : ℂ) := by
    rw [h1, h2] at hQdet'
    push_cast
    rw [eq_div_iff hQ0, mul_comm]
    exact hQdet'
  rw [hL, Complex.ofReal_re]
  conv_lhs => rw [h1, hqre]
  have hgpos : 0 < grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i := hsm.2
  push_cast
  have : ((G (bsL ε w) τ).det.re : ℂ) ≠ 0 := by exact_mod_cast hGr.ne'
  have : (grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  field_simp

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ)
    (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) :
    Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) :=
  row_levi_det_of GlobalTheory.LogHermHess.leviForm_log_herm GlobalTheory.det_schur_bilinear_entry GlobalTheory.FlagCell2.exists_posDef_grD ι m n d ε G w x hG hs

end GlobalTheory.FlagCell2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRowStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedLine_potential_hessian_det_own_row : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FlagCell2.row_levi_det | exact GlobalTheory.FlagCell2.row_levi_det | (intros; apply GlobalTheory.FlagCell2.row_levi_det <;> assumption)
end
