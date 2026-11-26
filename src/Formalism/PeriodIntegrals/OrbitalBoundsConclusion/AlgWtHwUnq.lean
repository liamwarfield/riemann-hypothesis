module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStepSubstitution

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensityFirstBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensStepOf
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix

namespace PI.UnitaryGroupMassFormula.HwConjInf

open scoped Classical in
open Classical in
def repPt {L : Type} [Field L] [NumberField L] {n : ℕ} (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) :
    (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else (Y (InfinitePlace.mk p.1))⁻¹ p.2.2 p.2.1

def DensA : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0) →
    ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0

def DensB : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * Y w = 1) → (∀ w, (1 + Y w).det ≠ 0) →
      MvPolynomial.eval (repPt Y) F = 0) →
    ∀ y, InV y → MvPolynomial.eval y F = 0

theorem densStep_of (ha : DensA) (hb : DensB) : DensStep :=
  fun L _ _ _ n F h => hb L n F (ha L n F h)

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DensitySecondBound
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix MvPolynomial
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

def coords (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : InfinitePlace L × Fin n × Fin n → ℂ :=
  fun q => Y q.1 q.2.1 q.2.2

def Mx (w : InfinitePlace L) : Matrix (Fin n) (Fin n) (MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => X (w, i, j)

theorem eval_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    (eval (coords Y)).mapMatrix (Mx w) = Y w := by
  ext i j
  simp [Mx, coords]

theorem eval_det_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (Mx w).det = (Y w).det := by
  rw [RingHom.map_det, eval_Mx]

theorem eval_det_one_add_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) :
    eval (coords Y) (1 + Mx w).det = (1 + Y w).det := by
  rw [RingHom.map_det, map_add (f := _), map_one, eval_Mx]

theorem eval_adj_Mx (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace L) (i j : Fin n) :
    eval (coords Y) ((Mx w).adjugate i j) = (Y w).adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (eval (coords Y)) (Mx w)) i) j
  rw [eval_Mx] at h
  simpa using h

def Dl (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : ℂ := ∏ w, (Y w).det

def DlP : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ := ∏ w, (Mx w).det

theorem eval_DlP (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : eval (coords Y) (DlP (L := L) (n := n)) = Dl Y := by
  simp [DlP, Dl, map_prod, eval_det_Mx]

theorem var_hom (v : (L →+* ℂ) × Fin n × Fin n) :
    ∃ N : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ, ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y * repPt Y v = eval (coords Y) N := by
  obtain ⟨σ, i, j⟩ := v
  by_cases h : σ = (InfinitePlace.mk σ).embedding
  · refine ⟨X (InfinitePlace.mk σ, i, j) * DlP, fun Y _ => ?_⟩
    simp only [repPt, if_pos h, map_mul, eval_X, eval_DlP, coords]
    ring
  · refine ⟨(Mx (InfinitePlace.mk σ)).adjugate j i *
      ∏ w ∈ Finset.univ.erase (InfinitePlace.mk σ), (Mx w).det, fun Y hY => ?_⟩
    simp only [repPt, if_neg h, map_mul, map_prod, eval_adj_Mx, eval_det_Mx]
    rw [Matrix.inv_def, Matrix.smul_apply, Dl,
      ← Finset.mul_prod_erase Finset.univ (fun w => (Y w).det) (Finset.mem_univ (InfinitePlace.mk σ)),
      Ring.inverse_eq_inv', smul_eq_mul]
    have := hY (InfinitePlace.mk σ)
    field_simp

theorem hom_exists (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    ∃ (K : ℕ) (P : MvPolynomial (InfinitePlace L × Fin n × Fin n) ℂ), ∀ Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ,
      (∀ w, (Y w).det ≠ 0) → Dl Y ^ K * eval (repPt Y) F = eval (coords Y) P := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, fun Y _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K1, P1, h1⟩ := hp
    obtain ⟨K2, P2, h2⟩ := hq
    refine ⟨K1 + K2, P1 * DlP ^ K2 + P2 * DlP ^ K1, fun Y hY => ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, eval_DlP, ← h1 Y hY, ← h2 Y hY]
    ring
  | mul_X p v hp =>
    obtain ⟨K, P, h⟩ := hp
    obtain ⟨N, hN⟩ := var_hom (L := L) v
    refine ⟨K + 1, P * N, fun Y hY => ?_⟩
    rw [map_mul, map_mul, ← h Y hY, ← hN Y hY, eval_X]
    ring

theorem repPt_of_InV [IsCMField L] (y : (L →+* ℂ) × Fin n × Fin n → ℂ) (hy : InV y) :
    repPt (fun w => Matrix.of fun i j => y (w.embedding, i, j)) = y ∧
      ∀ w : InfinitePlace L, (Matrix.of fun i j => y (w.embedding, i, j)).det ≠ 0 := by
  refine ⟨?_, fun w => ?_⟩
  · funext p
    obtain ⟨σ, i, j⟩ := p
    simp only [repPt]
    split_ifs with h
    · exact congrArg (fun s => y (s, i, j)) h.symm
    · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
        rcases InfinitePlace.embedding_mk_eq σ with h' | h'
        · exact absurd h'.symm h
        · rw [h']; exact (star_star σ).symm
      obtain ⟨B, hB⟩ := hy (InfinitePlace.mk σ).embedding
      have hYB : (Matrix.of fun i j => y ((InfinitePlace.mk σ).embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
        ext a b; exact (hB a b).1
      rw [hYB, ← Matrix.coe_units_inv]
      conv_rhs => rw [hc]
      exact ((hB i j).2).symm
  · obtain ⟨B, hB⟩ := hy w.embedding
    have hYB : (Matrix.of fun i j => y (w.embedding, i, j)) = (B : Matrix (Fin n) (Fin n) ℂ) := by
      ext a b; exact (hB a b).1
    rw [hYB]
    exact (Matrix.isUnits_det_units B).ne_zero

theorem density_second_bound : DensB := by
  intro L _ _ _ n F hF y hy
  obtain ⟨K, P, hP⟩ := hom_exists (L := L) F
  have hG : (∏ w, (1 + Mx (L := L) (n := n) w).det) * P = 0 := by
    apply productFramesDense_holds (InfinitePlace L) n (fun _ => 1) (fun _ => Matrix.PosDef.one)
    intro Y hY
    have hY' : ∀ w, (Y w)ᴴ * Y w = 1 := fun w => by simpa using hY w
    have hdet : ∀ w, (Y w).det ≠ 0 := fun w h0 => by
      have := congrArg Matrix.det (hY' w)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    change eval (coords Y) _ = 0
    rw [map_mul, map_prod]
    simp only [eval_det_one_add_Mx]
    by_cases h1 : ∀ w, (1 + Y w).det ≠ 0
    · rw [← hP Y hdet, hF Y hY' h1]
      simp
    · push Not at h1
      obtain ⟨w, hw⟩ := h1
      rw [Finset.prod_eq_zero (Finset.mem_univ w) hw, zero_mul]
  have hne : (∏ w, (1 + Mx (L := L) (n := n) w).det) ≠ 0 := by
    intro h0
    have := congrArg (eval (coords (fun _ : InfinitePlace L => (0 : Matrix (Fin n) (Fin n) ℂ)))) h0
    rw [map_prod] at this
    simp only [eval_det_one_add_Mx, add_zero, Matrix.det_one, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hP0 : P = 0 := (mul_eq_zero.mp hG).resolve_left hne
  obtain ⟨hYy, hYdet⟩ := repPt_of_InV y hy
  have := hP _ hYdet
  rw [hP0, map_zero, hYy] at this
  exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun w _ => hYdet w))

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.CayMulConjTranspose
noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

section cx

variable {n : ℕ}

def cay {R : Type*} [CommRing R] (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := (1 - X) * (1 + X)⁻¹

theorem det_one_add_ne_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : (1 + X).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hXv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : X *ᵥ v = -v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hXv
    exact (neg_eq_of_add_eq_zero_right hXv).symm
  have h2 : Xᴴ *ᵥ v = v := by rw [hX, Matrix.neg_mulVec, h1, neg_neg]
  have h3 : star v ᵥ* X = star v := by
    have := Matrix.star_mulVec Xᴴ v
    rw [Matrix.conjTranspose_conjTranspose, h2] at this
    exact this.symm
  have h4 : star v ⬝ᵥ v = -(star v ⬝ᵥ v) := by
    calc star v ⬝ᵥ v = (star v ᵥ* X) ⬝ᵥ v := by rw [h3]
      _ = star v ⬝ᵥ (X *ᵥ v) := (Matrix.dotProduct_mulVec _ _ _).symm
      _ = -(star v ⬝ᵥ v) := by rw [h1, dotProduct_neg]
  have h5 : star v ⬝ᵥ v = 0 := by linear_combination h4 / 2
  exact hv (dotProduct_star_self_eq_zero.1 h5)

theorem isUnit_det_one_add {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : IsUnit (1 + X).det := isUnit_iff_ne_zero.mpr (det_one_add_ne_zero hX)

theorem isUnit_det_one_sub {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : IsUnit (1 - X).det := by
  have h : (-X)ᴴ = -(-X) := by rw [Matrix.conjTranspose_neg, hX]
  rw [sub_eq_add_neg]
  exact isUnit_det_one_add h

theorem cay_mul_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = -X) : cay X * (cay X)ᴴ = 1 := by
  have h1 : (1 + X)ᴴ = 1 - X := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX, sub_eq_add_neg]
  have h2 : (1 - X)ᴴ = 1 + X := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hX, sub_neg_eq_add]
  have hu1 := isUnit_det_one_add hX
  have hu2 := isUnit_det_one_sub hX
  have hc : Commute (1 - X) (1 + X) :=
    (Commute.one_right (1 - X)).add_right ((Commute.one_left X).sub_left (Commute.refl X))
  have e : (1 + X)⁻¹ * (1 - X)⁻¹ = (1 - X)⁻¹ * (1 + X)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hc.eq, Matrix.mul_inv_rev]
  unfold cay
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, h1, h2]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 + X)⁻¹ (1 - X)⁻¹, e, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1,
    Matrix.mul_one, Matrix.mul_nonsing_inv _ hu2]

theorem cay_eq (X : Matrix (Fin n) (Fin n) ℂ) :
    cay X = ((1 + X).det)⁻¹ • ((1 - X) * (1 + X).adjugate) := by
  unfold cay
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]

theorem exists_cay {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ * Y = 1) (h1 : (1 + Y).det ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X ∧ cay X = Y := by
  have hA : IsUnit (1 + Y).det := isUnit_iff_ne_zero.mpr h1
  have hYY : Y * Yᴴ = 1 := by
    first
      | exact mul_eq_one_comm.1 hY
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hY
  have hc : Commute (1 + Y) (Y - 1) :=
    ((Commute.one_left Y).add_left (Commute.refl Y)).sub_right (Commute.one_right _)
  have hcinv : (1 + Y)⁻¹ * (Y - 1) = (Y - 1) * (1 + Y)⁻¹ := by
    calc (1 + Y)⁻¹ * (Y - 1) = (1 + Y)⁻¹ * (Y - 1) * ((1 + Y) * (1 + Y)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
      _ = (1 + Y)⁻¹ * ((1 + Y) * (Y - 1)) * (1 + Y)⁻¹ := by
          rw [hc.eq]
          simp only [Matrix.mul_assoc]
      _ = (Y - 1) * (1 + Y)⁻¹ := by
          rw [← Matrix.mul_assoc (1 + Y)⁻¹, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  refine ⟨(1 - Y) * (1 + Y)⁻¹, ?_, ?_⟩
  · have hinv : ((1 + Y)ᴴ)⁻¹ = (1 + Y)⁻¹ * Y := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, ← Matrix.mul_assoc]
      have e : 1 + Yᴴ = Yᴴ * (1 + Y) := by
        rw [Matrix.mul_add, Matrix.mul_one, hY, add_comm]
      rw [e, Matrix.mul_assoc Yᴴ, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one, hY]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hinv, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hYY, hcinv,
      ← neg_mul, neg_sub]
  · have hsum : 1 + (1 - Y) * (1 + Y)⁻¹ = (2 : ℂ) • (1 + Y)⁻¹ := by
      calc 1 + (1 - Y) * (1 + Y)⁻¹ = (1 + Y) * (1 + Y)⁻¹ + (1 - Y) * (1 + Y)⁻¹ := by
            rw [Matrix.mul_nonsing_inv _ hA]
        _ = ((1 + Y) + (1 - Y)) * (1 + Y)⁻¹ := (Matrix.add_mul _ _ _).symm
        _ = (2 : ℂ) • (1 + Y)⁻¹ := by
            rw [show (1 + Y) + (1 - Y) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) by
              rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
    have hdiff : 1 - (1 - Y) * (1 + Y)⁻¹ = (2 : ℂ) • (Y * (1 + Y)⁻¹) := by
      calc 1 - (1 - Y) * (1 + Y)⁻¹ = (1 + Y) * (1 + Y)⁻¹ - (1 - Y) * (1 + Y)⁻¹ := by
            rw [Matrix.mul_nonsing_inv _ hA]
        _ = ((1 + Y) - (1 - Y)) * (1 + Y)⁻¹ := (Matrix.sub_mul _ _ _).symm
        _ = (2 : ℂ) • (Y * (1 + Y)⁻¹) := by
            rw [show (1 + Y) - (1 - Y) = (2 : ℂ) • Y by rw [two_smul]; abel, Matrix.smul_mul]
    have hinv2 : ((2 : ℂ) • (1 + Y)⁻¹)⁻¹ = (2 : ℂ)⁻¹ • (1 + Y) := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hA,
        mul_inv_cancel₀ two_ne_zero, one_smul]
    unfold cay
    rw [hsum, hdiff, hinv2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ two_ne_zero,
      one_smul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]

end cx

section pts

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

def cpt (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) : (L →+* ℂ) × Fin n × Fin n → ℂ := fun p =>
  if p.1 = (InfinitePlace.mk p.1).embedding then Y (InfinitePlace.mk p.1) p.2.1 p.2.2
  else star (Y (InfinitePlace.mk p.1) p.2.1 p.2.2)

theorem repPt_eq_cpt (Y : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ) (hY : ∀ w, (Y w)ᴴ * Y w = 1) :
    repPt Y = cpt Y := by
  unfold repPt
  funext p
  simp only [cpt]
  split_ifs
  · rfl
  · rw [Matrix.inv_eq_left_inv (hY _), Matrix.conjTranspose_apply]

theorem denseRange_emb [IsCMField L] :
    DenseRange (fun x : L => fun w : InfinitePlace L => w.embedding x) := by
  have hcx : ∀ w : InfinitePlace L, w.IsComplex := fun w => by
    first
    | exact NumberField.IsTotallyComplex.isComplex w
    | exact IsTotallyComplex.isComplex w
  have hd : DenseRange (algebraMap L (InfiniteAdeleRing L)) :=
    InfiniteAdeleRing.denseRange_algebraMap L
  let g : InfiniteAdeleRing L → (InfinitePlace L → ℂ) := fun a w =>
    InfinitePlace.Completion.extensionEmbedding w (a w)
  have hg : Continuous g :=
    continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_apply w)
  have hs : Function.Surjective g := by
    intro y
    have h : ∀ w, ∃ a : w.Completion, InfinitePlace.Completion.extensionEmbedding w a = y w := fun w =>
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex (hcx w) (y w)
    choose a ha using h
    exact ⟨a, funext ha⟩
  have h := hs.denseRange.comp hd hg
  convert h using 1
  funext x
  funext w
  simp only [Function.comp_apply, g]
  first
  | exact (InfinitePlace.Completion.extensionEmbedding_coe w _).symm
  | exact (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.equiv w |>.symm x)).symm
  | simp [InfinitePlace.Completion.extensionEmbedding_coe]
  | rfl

theorem denseRange_matEmb [IsCMField L] :
    DenseRange (fun b : Matrix (Fin n) (Fin n) L => fun (i j : Fin n) (w : InfinitePlace L) => w.embedding (b i j)) := by
  exact DenseRange.piMap fun _ => DenseRange.piMap fun _ => denseRange_emb

def skewOf (z : Fin n → Fin n → InfinitePlace L → ℂ) (w : InfinitePlace L) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (fun i j => z i j w) - (Matrix.of (fun i j => z i j w))ᴴ

theorem skewOf_skew (z : Fin n → Fin n → InfinitePlace L → ℂ) (w : InfinitePlace L) :
    (skewOf z w)ᴴ = -(skewOf z w) := by
  unfold skewOf
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem continuous_cpt_cay :
    Continuous (fun z : Fin n → Fin n → InfinitePlace L → ℂ => cpt (fun w => cay (skewOf z w))) := by
  have hs : ∀ w : InfinitePlace L,
      Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => skewOf z w := by
    intro w
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [skewOf, Matrix.sub_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
    have hc : ∀ a b : Fin n, Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => z a b w :=
      fun a b => (continuous_apply w).comp ((continuous_apply b).comp (continuous_apply a))
    first
      | exact (hc i j).sub (hc j i).star
      | fun_prop
  have hA : ∀ (w : InfinitePlace L) (i j : Fin n),
      Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => cay (skewOf z w) i j := by
    intro w i j
    have e : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => cay (skewOf z w) i j) = fun z =>
        ((1 + skewOf z w).det)⁻¹ * ((1 - skewOf z w) * (1 + skewOf z w).adjugate) i j := by
      funext z
      rw [cay_eq, Matrix.smul_apply, smul_eq_mul]
    rw [e]
    have hd : Continuous fun z : Fin n → Fin n → InfinitePlace L → ℂ => (1 + skewOf z w).det :=
      (continuous_const.add (hs w)).matrix_det
    refine (hd.inv₀ fun z => det_one_add_ne_zero (skewOf_skew z w)).mul ?_
    exact (((continuous_const.sub (hs w)).matrix_mul
      (continuous_const.add (hs w)).matrix_adjugate)).matrix_elem i j
  refine continuous_pi fun p => ?_
  simp only [cpt]
  split_ifs
  · exact hA _ _ _
  · exact (hA _ _ _).star

end pts

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

noncomputable section

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Matrix
open scoped ComplexOrder
open Classical

namespace PI.UnitaryGroupMassFormula.HwConjInf

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

theorem mapMatrix_inv (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) (h : M.det ≠ 0) :
    f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h), map_one]

theorem det_mapMatrix (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) : (f.mapMatrix M).det = f M.det :=
  (RingHom.map_det f M).symm

variable [IsCMField L]

def skewL (b : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  b - ((IsCMField.complexConj L : L →+* L).mapMatrix b)ᵀ

def zOf (b : Matrix (Fin n) (Fin n) L) : Fin n → Fin n → InfinitePlace L → ℂ :=
  fun i j w => w.embedding (b i j)

theorem map_skewL (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (skewL b) = skewOf (zOf b) w := by
  ext i j
  simp [skewL, skewOf, zOf, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

theorem det_one_add_skewL (b : Matrix (Fin n) (Fin n) L) : (1 + skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply det_one_add_ne_zero (skewOf_skew (zOf b) w0)
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_add (f := _), det_mapMatrix, h0, map_zero]

theorem det_one_sub_skewL (b : Matrix (Fin n) (Fin n) L) : (1 - skewL b).det ≠ 0 := by
  intro h0
  let w0 : InfinitePlace L := Classical.arbitrary _
  apply (isUnit_det_one_sub (skewOf_skew (zOf b) w0)).ne_zero
  rw [← map_skewL, ← map_one w0.embedding.mapMatrix, ← map_sub, det_mapMatrix, h0, map_zero]

theorem map_cay (b : Matrix (Fin n) (Fin n) L) (w : InfinitePlace L) :
    w.embedding.mapMatrix (cay (skewL b)) = cay (skewOf (zOf b) w) := by
  unfold cay
  rw [map_mul, mapMatrix_inv _ _ (det_one_add_skewL b), map_sub, map_add (f := _), map_one, map_skewL]

theorem map_conjT (f : L →+* ℂ) (M : Matrix (Fin n) (Fin n) L) :
    f.mapMatrix (conjT (IsCMField.complexConj L : L →+* L) M) = (f.mapMatrix M)ᴴ := by
  ext i j
  simp [conjT, conjTranspose_apply, IsCMField.complexEmbedding_complexConj]

theorem cay_skewL_mem (b : Matrix (Fin n) (Fin n) L) :
    cay (skewL b) * conjT (IsCMField.complexConj L : L →+* L) (cay (skewL b)) = 1 := by
  let w0 : InfinitePlace L := Classical.arbitrary _
  have hinj : Function.Injective (w0.embedding.mapMatrix : Matrix (Fin n) (Fin n) L →+* _) := by
    intro M N h
    ext i j
    exact w0.embedding.injective (congrFun (congrFun h i) j)
  apply hinj
  rw [map_mul, map_conjT, map_cay, map_one]
  exact cay_mul_conjTranspose (skewOf_skew (zOf b) w0)

theorem det_cay_skewL (b : Matrix (Fin n) (Fin n) L) : (cay (skewL b)).det ≠ 0 := by
  unfold cay
  rw [det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (det_one_sub_skewL b) (inv_ne_zero (det_one_add_skewL b))

theorem ratPt_cay (b : Matrix (Fin n) (Fin n) L) :
    ratPt (cay (skewL b)) = cpt (fun w => cay (skewOf (zOf b) w)) := by
  funext p
  obtain ⟨σ, i, j⟩ := p
  simp only [ratPt, cpt]
  split_ifs with h
  · rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_rhs => rw [← h]
  · have hc : σ = ComplexEmbedding.conjugate (InfinitePlace.mk σ).embedding := by
      rcases InfinitePlace.embedding_mk_eq σ with h' | h'
      · exact absurd h'.symm h
      · rw [h']; exact (star_star σ).symm
    rw [← map_cay b (InfinitePlace.mk σ), RingHom.mapMatrix_apply, Matrix.map_apply]
    conv_lhs => rw [hc]
    rw [ComplexEmbedding.conjugate_coe_eq]
    rfl

theorem rat_zero (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ ∈ GQ0 L n, MvPolynomial.eval (ratPt (γ₀ : Matrix (Fin n) (Fin n) L)) F = 0)
    (b : Matrix (Fin n) (Fin n) L) :
    MvPolynomial.eval (cpt (fun w => cay (skewOf (zOf b) w))) F = 0 := by
  have hu : IsUnit (cay (skewL b)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_cay_skewL b))
  have hmem : hu.unit ∈ GQ0 L n := by
    show ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      conjT (IsCMField.complexConj L : L →+* L) ((hu.unit : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1
    rw [IsUnit.unit_spec]
    exact cay_skewL_mem b
  have := hF _ hmem
  rwa [IsUnit.unit_spec, ratPt_cay] at this

theorem density_first_bound : DensA := by
  intro L _ _ _ n F hF Y hYu hY1
  have hH : (fun z : Fin n → Fin n → InfinitePlace L → ℂ => MvPolynomial.eval (cpt (fun w => cay (skewOf z w))) F) =
      fun _ => 0 :=
    (denseRange_matEmb (L := L) (n := n)).equalizer ((MvPolynomial.continuous_eval F).comp continuous_cpt_cay)
      continuous_const (funext fun b => rat_zero F hF b)
  choose X hXs hXc using fun w => exists_cay (hYu w) (hY1 w)
  let z : Fin n → Fin n → InfinitePlace L → ℂ := fun i j w => ((2 : ℂ)⁻¹ • X w) i j
  have hz : ∀ w, cay (skewOf z w) = Y w := by
    intro w
    have hs : skewOf z w = X w := by
      ext i j
      have h1 := congrArg (fun M => M i j) (hXs w)
      simp only [conjTranspose_apply, Matrix.neg_apply] at h1
      have h2 : (starRingEnd ℂ) (X w j i) = -X w i j := h1
      simp only [skewOf, z, Matrix.sub_apply, Matrix.of_apply, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul,
        star_mul']
      simp [h2]
      ring
    rw [hs, hXc]
  rw [repPt_eq_cpt Y hYu]
  have := congrFun hH z
  rwa [show (fun w => cay (skewOf z w)) = Y from funext hz] at this

theorem density_induction : DensStep := densStep_of density_first_bound density_second_bound

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GeneralLinearReduction
noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

def mPt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then M p.2.1 p.2.2 else (M⁻¹) p.2.2 p.2.1

theorem gPt_eq {n : ℕ} (g : GL (Fin n) ℂ) : gPt g = mPt g.val := by
  funext p
  unfold gPt mPt
  rw [Matrix.coe_units_inv]

theorem mPt_continuousAt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt mPt M := by
  rw [continuousAt_pi]
  rintro ⟨b, i, j⟩
  cases b
  · simp only [mPt, Bool.false_eq_true, if_false]
    have h1 : ContinuousAt (fun N : Matrix (Fin n) (Fin n) ℂ => N⁻¹) M :=
      continuousAt_matrix_inv M (by simpa [isUnit_iff_ne_zero] using hM)
    exact (continuous_apply_apply j i).continuousAt.comp h1
  · simp only [mPt, if_true]
    exact (continuous_apply_apply i j).continuousAt

def Rm {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix ι ι ℂ := fun i j => MvPolynomial.eval (mPt M) (Q i j)

theorem Rm_continuousAt {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt (Rm Q) M := by
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact ((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp (mPt_continuousAt M hM)

def dd {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t), Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)),
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add],
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add]⟩

theorem dd_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    (dd c t).val = Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t) := rfl

theorem dd_inv_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    ((dd c t)⁻¹).val = Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)) := rfl

theorem dd_tri {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : (dd c t).val.BlockTriangular id := by
  rw [dd_val]
  exact Matrix.blockTriangular_diagonal _

def phi {n : ℕ} (c lam : Fin n → ℤ) : ℤ := ∑ i, c i * lam i

theorem char_dd {n : ℕ} (c lam : Fin n → ℤ) (t : ℝ) :
    ∏ i, (dd c t).val i i ^ lam i = Complex.exp ((phi c lam : ℂ) * t) := by
  rw [dd_val]
  simp only [Matrix.diagonal_apply_eq]
  rw [show (phi c lam : ℂ) * t = ∑ i, (lam i : ℂ) * ((c i : ℂ) * t) by
    unfold phi
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Complex.exp_int_mul ((c i : ℂ) * t) (lam i)).symm

theorem tendsto_exp_neg {k : ℤ} (hk : k < 0) :
    Tendsto (fun t : ℝ => Complex.exp ((k : ℂ) * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun t : ℝ => ‖Complex.exp ((k : ℂ) * t)‖) = fun t => Real.exp ((k : ℝ) * t) := by
    funext t
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [h]
  apply Real.tendsto_exp_atBot.comp
  exact Filter.tendsto_id.const_mul_atTop_of_neg (by exact_mod_cast hk)

theorem wt_le {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j))
    (hmul : ∀ g h, R (g * h) = R g * R h)
    (S : Set (Matrix ι ι ℂ)) (hS : ∀ s ∈ S, ∀ g, s * R g = R g * s)
    (v u : ι → ℂ) (lam mu : Fin n → ℤ)
    (hv : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v)
    (hu : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u)
    (hmem : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)})
    (hu0 : u ≠ 0) (c : Fin n → ℤ) (hc : ∀ i j, i < j → c j < c i) :
    phi c mu ≤ phi c lam := by
  have hR : ∀ g : GL (Fin n) ℂ, R g = Rm Q g.val := by
    intro g; ext i j; rw [hRQ, Rm, gPt_eq]
  set f : (ι → ℂ) → ℝ → (ι → ℂ) := fun w t => Complex.exp (-((phi c lam : ℂ) * t)) • (R (dd c t) *ᵥ w) with hf
  let P : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∃ y, Tendsto (f w) atTop (𝓝 y)}
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        refine ⟨ya + yb, ?_⟩
        have e : f (a + b) = fun t => f a t + f b t := by funext t; simp [hf, Matrix.mulVec_add, smul_add]
        rw [e]; exact ha.add hb
      zero_mem' := ⟨0, by
        have e : f 0 = fun _ => 0 := by funext t; simp [hf]
        rw [e]; exact tendsto_const_nhds⟩
      smul_mem' := by
        rintro r a ⟨ya, ha⟩
        refine ⟨r • ya, ?_⟩
        have e : f (r • a) = fun t => r • f a t := by funext t; simp [hf, Matrix.mulVec_smul, smul_comm r]
        rw [e]; exact ha.const_smul r }

  have hgenL : ∀ s ∈ S, ∀ large₂ : GL (Fin n) ℂ, LowUni large₂.val → s *ᵥ (R large₂ *ᵥ v) ∈ P := by
    intro s hs large₂ hL
    have comm : ∀ g y, R g *ᵥ (s *ᵥ y) = s *ᵥ (R g *ᵥ y) := by
      intro g y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS s hs]
    have key : ∀ t, f (s *ᵥ (R large₂ *ᵥ v)) t = s *ᵥ (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
      intro t
      have e2 : dd c t * large₂ = (dd c t * large₂ * (dd c t)⁻¹) * dd c t := by group
      have inner : R (dd c t) *ᵥ (R large₂ *ᵥ v) =
          Complex.exp ((phi c lam : ℂ) * t) • (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← hmul, show R (dd c t * large₂) = R (dd c t * large₂ * (dd c t)⁻¹) * R (dd c t) by
          rw [← hmul, ← e2], ← Matrix.mulVec_mulVec, hv (dd c t) (dd_tri c t),
          char_dd, Matrix.mulVec_smul, hR]
      simp only [hf]
      rw [comm, inner, Matrix.mulVec_smul, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    have hM : Tendsto (fun t => (dd c t * large₂ * (dd c t)⁻¹).val) atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have hentry : ∀ t, (dd c t * large₂ * (dd c t)⁻¹).val i j =
          Complex.exp (((c i - c j : ℤ) : ℂ) * t) * large₂.val i j := by
        intro t
        rw [Units.val_mul, Units.val_mul, dd_val, dd_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
        rw [mul_comm (Complex.exp _) (large₂.val i j), mul_assoc, ← Complex.exp_add, mul_comm]
        congr 2; push_cast; ring
      simp only [hentry]
      rcases lt_trichotomy i j with h | h | h
      · rw [hL.1 i j h, Matrix.one_apply_ne h.ne]; simp
      · subst h; simp [hL.2]
      · rw [Matrix.one_apply_ne h.ne']
        simpa using (tendsto_exp_neg (sub_neg.2 (hc j i h))).mul_const (large₂.val i j)
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    refine ⟨s *ᵥ (Rm Q 1 *ᵥ v), ?_⟩
    rw [show f (s *ᵥ (R large₂ *ᵥ v)) = _ from funext key]
    exact (hcs.tendsto _).comp ((Rm_continuousAt Q 1 (by simp)).tendsto.comp hM)

  have hgen : ∀ s ∈ S, ∀ g : GL (Fin n) ℂ, s *ᵥ (R g *ᵥ v) ∈ P := by
    intro s hs g
    have hclosed : IsClosed (P : Set (ι → ℂ)) := Submodule.closed_of_finiteDimensional P
    have hdet : g.val.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun x : ℂ => s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v)) (𝓝[≠] 0) (𝓝 (s *ᵥ (R g *ᵥ v))) := by
      rw [hR]
      exact (hcs.tendsto _).comp ((Rm_continuousAt Q g.val hdet).tendsto.comp (tendsto_add_smul g.val))
    apply hclosed.mem_of_tendsto hlim
    filter_upwards [dense_LU g.val] with x hx
    obtain ⟨hdx, L, U, hL, hU, hLU⟩ := hx
    have hdL : L.det ≠ 0 := by rw [det_lowUni hL]; exact one_ne_zero
    have hdU : U.det ≠ 0 := by intro h; apply hdx; rw [hLU, Matrix.det_mul, h, mul_zero]
    set large₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdL
    set Ug := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdU
    have e : g.val + x • 1 = (large₂ * Ug).val := by rw [hLU]; rfl
    have hUg : Ug.val.BlockTriangular id := fun i j h => hU i j h
    show s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v) ∈ P
    rw [e, ← hR, hmul, ← Matrix.mulVec_mulVec, hv Ug hUg, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact P.smul_mem _ (hgenL s hs large₂ hL)
  have huP : u ∈ P := by
    refine Submodule.span_le.2 ?_ hmem
    rintro w ⟨s, hs, g, rfl⟩
    exact hgen s hs g
  obtain ⟨y, hy⟩ := huP
  by_contra hlt
  push Not at hlt
  have hfu : ∀ t, f u t = Complex.exp (((phi c mu - phi c lam : ℤ) : ℂ) * t) • u := by
    intro t
    simp only [hf]
    rw [hu (dd c t) (dd_tri c t), char_dd, smul_smul, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hnorm : Tendsto (fun t => ‖f u t‖) atTop atTop := by
    have e : (fun t => ‖f u t‖) = fun t => Real.exp (((phi c mu - phi c lam : ℤ) : ℝ) * t) * ‖u‖ := by
      funext t; rw [hfu, norm_smul, Complex.norm_exp]; simp
    rw [e]
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by exact_mod_cast sub_pos.2 hlt))).atTop_mul_const
      (norm_pos_iff.2 hu0)
  exact not_tendsto_atTop_of_tendsto_nhds hy.norm hnorm

theorem general_linear_reduction : GLStep := by
  intro n ι _ _ R Q hRQ hmul S hS v u lam mu hv hu hspv hspu hv0 hu0
  have memu : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} := by
    rw [hspv]; exact Submodule.mem_top
  have memv : v ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} := by
    rw [hspu]; exact Submodule.mem_top
  have key : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j < c i) → phi c mu = phi c lam := fun c hc =>
    le_antisymm (wt_le R Q hRQ hmul S hS v u lam mu hv hu memu hu0 c hc)
      (wt_le R Q hRQ hmul S hS u v mu lam hu hv memv hv0 c hc)
  funext k
  let c0 : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ)
  let ck : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ) + if i = k then 1 else 0
  have h0 := key c0 (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [c0]; omega)
  have h1 := key ck (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [ck]; split_ifs <;> omega)
  have hk : ∀ x : Fin n → ℤ, phi ck x = phi c0 x + x k := by
    intro x
    simp [phi, ck, c0, add_mul, Finset.sum_add_distrib]
  rw [hk, hk] at h1
  linarith

end PI.UnitaryGroupMassFormula.HwConjInf
end
end

section -- merged from Formalism.PeriodIntegrals.AlgWtHwUnq
namespace PI.AlgWtHwUnq

open NumberField IsDedekindDomain Formalism.L2.NG ReciprocityTheory.Aut

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

def Stmt : Prop :=
  ∀ (a : AlgWt L n) (τ : L →+* ℂ) (lam lam' : Fin n → ℤ), a.HWAt τ lam → a.HWAt τ lam' → lam = lam'

end PI.AlgWtHwUnq
end

theorem algebraic_weight_highest_unique (L : Type) [Field L] [NumberField L] [NumberField.IsCMField L] (n : ℕ) : PI.AlgWtHwUnq.Stmt L n :=
  fun a τ lam lam' h1 h2 =>
    PI.UnitaryGroupMassFormula.HwConjInf.glue_holds_var PI.UnitaryGroupMassFormula.HwConjInf.density_induction PI.UnitaryGroupMassFormula.HwConjInf.general_linear_reduction L n a τ lam lam' h1 h2
