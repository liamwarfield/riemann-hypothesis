module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariant
open Matrix Polynomial

namespace GlobalTheory

theorem poly_eval_eq_eval_zero_of_eq_inv {k : Type} [Field k] [Infinite k] (p q : k[X]) (c : k)
    (h : ∀ x : k, x ≠ 0 → p.eval x = c * q.eval x⁻¹) : ∀ x : k, p.eval x = p.eval 0 := by
  set N := q.natDegree
  have key : X ^ N * p = C c * reflect N q := by
    apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := ({0}ᶜ : Set k))
    · intro x hx
      have hx0 : x ≠ 0 := hx
      letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
      have hr := eval₂_reflect_mul_pow (RingHom.id k) x⁻¹ N q le_rfl
      rw [invOf_eq_inv, inv_inv] at hr
      simp only [Set.mem_setOf_eq, eval_mul, eval_pow, eval_X, eval_C, h x hx0]
      rw [← eval₂_id, ← eval₂_id, ← hr, inv_pow]
      field_simp
    · exact (Set.finite_singleton (0 : k)).infinite_compl
  by_cases hp : p = 0
  · intro x; simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (C c * reflect N q).natDegree ≤ N :=
    (natDegree_C_mul_le _ _).trans (natDegree_reflect_le.trans (by simp [N]))
  rw [key] at hdeg
  have h0 : p.natDegree = 0 := by omega
  intro x
  rw [eq_C_of_natDegree_eq_zero h0]
  simp

section Lower
variable {k : Type} [Field k] {m : ℕ}

def swapLine (i j : Fin m) (t : k) : Matrix (Fin m) (Fin m) k :=
  (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1) + t • single j j 1

def upperFactor (i j : Fin m) (x : k) : Matrix (Fin m) (Fin m) k :=
  diagonal (Function.update (Function.update (1 : Fin m → k) j x⁻¹) i (-x)) * transvection j i x

theorem transvection_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (transvection j i x).BlockTriangular id := by
  intro a b hba
  simp only [id] at hba
  simp only [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hba), single_apply, zero_add]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hba (not_lt.mpr hji.le)
  · rfl

theorem upperFactor_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (upperFactor i j x).BlockTriangular id :=
  (blockTriangular_diagonal _).mul (transvection_isUpper hji x)

theorem upperFactor_det {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    (upperFactor i j x).det = -1 := by
  have hij : i ≠ j := ne_of_gt hji
  rw [upperFactor, det_mul, det_transvection_of_ne j i (ne_of_lt hji), det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  simp [hx]

theorem transvection_mul_upperFactor {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    transvection i j x * upperFactor i j x = swapLine i j x⁻¹ := by
  have hij : i ≠ j := ne_of_gt hji
  ext a b
  rw [transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases ha : a = i
  · subst ha
    rw [single_mul_apply_same]
    by_cases hb : b = a
    · subst hb
      simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx]
    · by_cases hbj : b = j
      · subst hbj
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx, hb, hbj, Ne.symm hb, Ne.symm hbj]
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha, add_zero]
    by_cases haj : a = j
    · subst haj
      by_cases hb : b = a
      · subst hb
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · by_cases hbi : b = i
        · subst hbi
          simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx]
        · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx, hb, hbi, Ne.symm hb, Ne.symm hbi]
    · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx, ha, haj, Ne.symm ha, Ne.symm haj]

end Lower

section Main
variable {k : Type} [Field k] [Infinite k] {m : ℕ}

theorem rightInv_lower_transvection (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k)
    (hΦ : ∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x)
    (hψ : ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A)
    (hT : ∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      ψ (A * T) = ψ A)
    (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) {i j : Fin m} (hji : j < i) (x : k) :
    ψ (A * transvection i j x) = ψ A := by
  have hij : i ≠ j := ne_of_gt hji
  have hl : ∀ y : k, (transvection i j y).det = 1 := fun y => det_transvection_of_ne i j hij y
  have hAl : ∀ y : k, (A * transvection i j y).det = A.det := fun y => by
    rw [det_mul, hl, mul_one]
  obtain ⟨p, hp⟩ := hΦ A (A * single i j 1)
  obtain ⟨q, hq⟩ := hΦ (A * (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1))
    (A * single j j 1)
  have e1 : ∀ y : k, ψ (A * transvection i j y) = r A.det * p.eval y := by
    intro y
    rw [hψ _ (by rw [hAl]; exact hA), hAl, ← hp]
    congr 2
    rw [transvection, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_smul, smul_single, smul_eq_mul,
      mul_one]
  have e2 : ∀ y : k, y ≠ 0 → r A.det * p.eval y = r (-A.det) * q.eval y⁻¹ := by
    intro y hy
    have hdT : (upperFactor i j y).det ≠ 0 := by rw [upperFactor_det hji hy]; norm_num
    rw [← e1, ← hT _ _ (by rw [hAl]; exact hA) hdT (upperFactor_isUpper hji y), Matrix.mul_assoc,
      transvection_mul_upperFactor hji hy]
    have hdM : (A * swapLine i j y⁻¹).det = -A.det := by
      rw [← transvection_mul_upperFactor hji hy, ← Matrix.mul_assoc, det_mul, hAl,
        upperFactor_det hji hy, mul_neg_one]
    rw [hψ _ (by rw [hdM]; exact neg_ne_zero.mpr hA), hdM, ← hq, swapLine, Matrix.mul_add,
      Matrix.mul_smul]
  by_cases hr : r A.det = 0
  · rw [e1, hr, zero_mul, hψ A hA, hr, zero_mul]
  have hconst := poly_eval_eq_eval_zero_of_eq_inv p q (r (-A.det) / r A.det) (fun y hy => by
    rw [div_mul_eq_mul_div, eq_div_iff hr, mul_comm, e2 y hy])
  rw [e1, hconst x, hψ A hA, ← hp, zero_smul, add_zero]

theorem rightInv_of_upperTriangular_rightInv :
    ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k),
      (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) →
      (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) →
      (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
        ψ (A * T) = ψ A) →
      ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  intro k _ _ m ψ Φ r hΦ hψ hT A B hA hB
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun B => ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ (A * B) = ψ A) B hB ?_ ?_ ?_ A hA
  · intro D hD A hA
    exact hT A _ hA hD (blockTriangular_diagonal D)
  · intro t A hA
    rcases lt_or_gt_of_ne t.hij with h | h
    · have hdet : (t.toMatrix).det ≠ 0 := by
        rw [TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]; exact one_ne_zero
      exact hT A _ hA hdet (transvection_isUpper h t.c)
    · exact rightInv_lower_transvection ψ Φ r hΦ hψ hT A hA h t.c
  · intro B₁ B₂ h₁ h₂ P₁ P₂ A hA
    rw [← Matrix.mul_assoc, P₂ _ (by rw [det_mul]; exact mul_ne_zero hA h₁), P₁ _ hA]

end Main

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantGLOfUpperTriangularRightInvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  first | exact @GlobalTheory.rightInv_of_upperTriangular_rightInv | exact GlobalTheory.rightInv_of_upperTriangular_rightInv | (intros; apply GlobalTheory.rightInv_of_upperTriangular_rightInv <;> assumption)
end
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

open Formalism.L2.LamCM GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.FlatGL

theorem evalFr_update_line {K : Type} [Field K] {B : Type} [DecidableEq B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (b : B)
    (A₀ D : Matrix (Fin (m b)) (Fin (m b)) K) :
    ∃ p : Polynomial K, ∀ x : K, evalFr G (Function.update X b (A₀ + x • D)) = p.eval x := by
  classical
  let α : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update X b A₀
  let β : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := Function.update (fun _ => 0) b D
  have hl : ∀ x : K, Function.update X b (A₀ + x • D) = fun b' => α b' + x • β b' := by
    intro x
    funext b'
    by_cases h : b' = b
    · subst h; simp [α, β]
    · simp [α, β, Function.update_of_ne h]
  refine ⟨MvPolynomial.aeval (fun v : FrVar m => Polynomial.C (α v.1 v.2.2 v.2.1) +
    Polynomial.C (β v.1 v.2.2 v.2.1) * Polynomial.X) G, fun x => ?_⟩
  have key : ∀ (a c : FrVar m → K) (P : MvPolynomial (FrVar m) K),
      MvPolynomial.eval (fun v => a v + x * c v) P =
        (MvPolynomial.aeval (fun v => Polynomial.C (a v) + Polynomial.C (c v) * Polynomial.X) P).eval x := by
    intro a c P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), Polynomial.eval_add, hp, hq]
    | mul_X p v hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp]
      simp only [MvPolynomial.aeval_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, MvPolynomial.eval_X]
      ring
  rw [hl, ← key]
  rfl

end GlobalTheory.FlatGL

namespace GlobalTheory.FlatGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def wr {K : Type} [Field K] (τ : Psi H) (δ : (E →+* ℂ) → K) : K :=
  δ τ.1 / ((∏ b, δ b) * δ (conjEmb τ.1))

def hfun (Dw : Datum H) {K : Type} [Field K] (τ : Psi H) (G : MvPolynomial (FrVar Dw.mult) K)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) : K :=
  wr τ (fun b => (X b).det) * evalFr G X

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Fixed

open Classical

variable {k : Type} [Field k] [Algebra c.F k] (τ : Psi H) {f : Rul Xo c} (y₀ : FrPt Xo c k)
  (G : MvPolynomial (FrVar Dw.mult) k)

theorem hfun_eq
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hY : ∀ b, (Y b).det ≠ 0) (y' : FrPt Xo c k)
    (h : FrChg (fun b => (Y b).transpose) 1 y₀ y') :
    hfun Dw τ G Y = evR Xo c f y' * (Y τ.1).det / (Y (conjEmb τ.1)).det := by
  have hD : (∏ b, (Y b).det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hY b
  have h2 := hY (conjEmb τ.1)
  unfold hfun wr
  rw [← hGY y' Y hY h]
  field_simp

theorem hfun_upper (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hT : T.det ≠ 0) (htri : T.BlockTriangular id) :
    hfun Dw τ G (Function.update X b (X b * T)) = hfun Dw τ G X := by
  classical
  let Tf : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k := Function.update (fun _ => 1) b T
  have hTb : Tf b = T := Function.update_self ..
  have hTo : ∀ b', b' ≠ b → Tf b' = 1 := fun b' h => Function.update_of_ne h ..
  have hTtri : ∀ b', (Tf b').BlockTriangular id := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact htri
    · rw [hTo b' h]; exact Matrix.blockTriangular_one
  have hTd : ∀ b', (Tf b').det ≠ 0 := by
    intro b'
    by_cases h : b' = b
    · subst h; rw [hTb]; exact hT
    · rw [hTo b' h]; simp
  have hup : Function.update X b (X b * T) = fun b' => X b' * Tf b' := by
    funext b'
    by_cases h : b' = b
    · subst h; rw [hTb, Function.update_self]
    · rw [hTo b' h, Function.update_of_ne h, _root_.mul_one]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k z₁ (fun b => (Tf b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  have hXT : ∀ b', (X b' * Tf b').det ≠ 0 := fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')
  have e₁ := hfun_eq τ y₀ G hGY X hX z₁ h₁
  have e₂ := hfun_eq τ y₀ G hGY (fun b' => X b' * Tf b') hXT z₂ h₃
  have e₃ := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun σ => (Tf σ).transpose) 1 z₁ z₂ h₂
    (fun σ i j hij => hTtri σ hij) (fun σ => by rw [Matrix.det_transpose]; exact (hTd σ).isUnit) one_ne_zero
  rw [hup, e₂, e₁, e₃]
  simp only [Matrix.det_transpose, Matrix.det_mul]
  have a1 := hTd τ.1
  have a2 := hTd (conjEmb τ.1)
  have a3 := hX (conjEmb τ.1)
  field_simp

theorem hfun_update_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) (b : E →+* ℂ) :
    hfun Dw τ G X = hfun Dw τ G (Function.update X b 1) := by
  have hψ : ∀ A : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 →
      hfun Dw τ G (Function.update X b A) =
        wr τ (Function.update (fun b' => (X b').det) b A.det) * evalFr G (Function.update X b A) := by
    intro A _
    unfold hfun
    congr 2
    funext b'
    by_cases h : b' = b
    · subst h; simp
    · simp [Function.update_of_ne h]
  have hT : ∀ A T : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      hfun Dw τ G (Function.update X b (A * T)) = hfun Dw τ G (Function.update X b A) := by
    intro A T hA hT htri
    have hX' : ∀ b', (Function.update X b A b').det ≠ 0 := by
      intro b'
      by_cases h : b' = b
      · subst h; simpa using hA
      · rw [Function.update_of_ne h]; exact hX b'
    have := hfun_upper τ y₀ G hf hGY (Function.update X b A) hX' b T hT htri
    simpa [Function.update_idem, Function.update_self] using this
  have key := GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant (fun A => hfun Dw τ G (Function.update X b A))
    (fun A => evalFr G (Function.update X b A)) (fun d => wr τ (Function.update (fun b' => (X b').det) b d))
    (fun A₀ D => evalFr_update_line G X b A₀ D) hψ hT 1 (X b) (by simp) (hX b)
  simp only [_root_.one_mul, Function.update_eq_self] at key
  exact key

theorem hfun_eq_one [Infinite k] (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y₀ y' → (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y)
    (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k) (hX : ∀ b, (X b).det ≠ 0) :
    hfun Dw τ G X = hfun Dw τ G (fun _ => 1) := by
  suffices h : ∀ s : Finset (E →+* ℂ), ∀ X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k,
      (∀ b, (X b).det ≠ 0) → (∀ b, b ∉ s → X b = 1) → hfun Dw τ G X = hfun Dw τ G (fun _ => 1) from
    h Finset.univ X hX fun b hb => absurd (Finset.mem_univ b) hb
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro X _ h1
    have : X = fun _ => 1 := funext fun b => h1 b (Finset.notMem_empty b)
    rw [this]
  | insert b s hb ih =>
    intro X hX h1
    rw [hfun_update_one τ y₀ G hf hGY X hX b]
    refine ih _ (fun b' => ?_) (fun b' hb' => ?_)
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hX b'
    · by_cases h : b' = b
      · subst h; simp
      · rw [Function.update_of_ne h]; exact h1 b' (by simp [h, hb'])

end Fixed

theorem evR_flat_chg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (τ : Psi H) {f : Rul Xo c}, f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0) →
    ∀ {k : Type} [Field k] [Algebra c.F k] (z y : FrPt Xo c k), z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) k),
      (∀ i, IsCombAt y.x (y.u τ.1) (g₁ i) (z.u τ.1 i)) →
      (∀ i, IsCombAt y.x (y.u (conjEmb τ.1)) (g₂ i) (z.u (conjEmb τ.1) i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c τ f hf k _ _ z y hx g₁ g₂ h₁ h₂
  classical
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have : Infinite k := Infinite.of_injective (Nat.cast : ℕ → k) Nat.cast_injective
  obtain ⟨G, -, hG⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c k y (exOf Dw (flatWt Dw τ) 0)
    (fun _ => 1) (fun b i => (exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1).toNat)
    (GlobalTheory.FlatFrameLaw.exOf_flatWt_none τ) (fun b i => by
      have h0 : 0 ≤ exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) + 1 := by
        rw [GlobalTheory.FlatFrameLaw.exOf_flatWt_some]; split_ifs <;> norm_num
      rw [Int.toNat_of_nonneg h0]; simp) f hf
  have hGY : ∀ (y' : FrPt Xo c k) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k),
      (∀ b, (Y b).det ≠ 0) → FrChg (fun b => (Y b).transpose) 1 y y' →
        (∏ b, (Y b).det) * evR Xo c f y' = evalFr G Y := fun y' Y hY h => by
    have := hG y' Y 1 hY (by simpa using h)
    simpa using this
  obtain ⟨g, a, hg, hc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c k y z).1 hx
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c k y g 1 hg
  rw [Units.val_one] at hw
  have hwz : FrChg (fun _ => 1) (a : k) w z :=
    ((GlobalTheory.Frames.frChg_calculus E H Dw l Xo c k).1 g (fun _ => 1) 1 a y w z hw).2 (by simpa using hc)
  have e1 := GlobalTheory.FlatFrameLaw.evR_flat_frChg τ hf (fun _ => 1) (a : k) w z hwz
    (fun σ i j hij => Matrix.one_apply_ne hij.ne) (fun σ => by simp) a.ne_zero
  simp only [Matrix.det_one, inv_one, _root_.one_mul] at e1
  have hgt : ∀ b, ((g b).transpose).det ≠ 0 := fun b => by rw [Matrix.det_transpose]; exact (hg b).ne_zero
  have e2 := hfun_eq τ y G hGY (fun b => (g b).transpose) hgt w (by simpa using hw)
  have hr : FrChg (fun b => (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) k).transpose) 1 y y := by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c k y y y).1
  have e3 := hfun_eq τ y G hGY (fun _ => 1) (fun b => by simp) y hr
  have e4 := hfun_eq_one τ y G hf hGY (fun b => (g b).transpose) hgt
  have hg1 : g τ.1 = g₁ := funext fun i =>
    (y.basis τ.1 (z.u τ.1 i) (by rw [← hx]; exact z.tan τ.1 i) (z.eig τ.1 i)).unique (hc.2.1 τ.1 i) (h₁ i)
  have hg2 : g (conjEmb τ.1) = g₂ := funext fun i =>
    (y.basis (conjEmb τ.1) (z.u (conjEmb τ.1) i) (by rw [← hx]; exact z.tan (conjEmb τ.1) i)
      (z.eig (conjEmb τ.1) i)).unique (hc.2.1 (conjEmb τ.1) i) (h₂ i)
  rw [e2, e3] at e4
  simp only [Matrix.det_transpose, Matrix.det_one, div_one, _root_.mul_one] at e4
  rw [e1, ← hg1, ← hg2]
  have a2 := hgt (conjEmb τ.1)
  rw [Matrix.det_transpose] at a2
  field_simp at e4
  linear_combination e4

end GlobalTheory.FlatGL
