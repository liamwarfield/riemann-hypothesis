module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Assembly
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.StabPairsOf
open Matrix

noncomputable section

namespace PI.StabPairsW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

theorem stabPairs_of (h1 : MapsStep) (h2 : PairFormula) (h3 : ConverseStep) (h4 : CompDet) :
    Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree := by
  intro k r z z' γ hs hp
  have hinj : ∀ ρ1 ∈ Rst k r z z' γ, ∀ ρ2 ∈ Rst k r z z' γ,
      pairMap k r z z' γ ρ1 = pairMap k r z z' γ ρ2 → ρ1 = ρ2 := by
    intro ρ1 h1' ρ2 h2' heq
    calc ρ1 = rhoOf k r z z' γ (pairMap k r z z' γ ρ1).1 (pairMap k r z z' γ ρ1).2 :=
          h2 k r z z' γ hs hp ρ1 h1'
      _ = rhoOf k r z z' γ (pairMap k r z z' γ ρ2).1 (pairMap k r z z' γ ρ2).2 := by rw [heq]
      _ = ρ2 := (h2 k r z z' γ hs hp ρ2 h2').symm
  refine ⟨⟨fun ρ hρ => h1 k r z z' γ hs hp ρ hρ, fun ρ1 h1' ρ2 h2' heq => hinj ρ1 h1' ρ2 h2' heq,
    fun p hp' => ⟨rhoOf k r z z' γ p.1 p.2, (h3 k r z z' γ hs hp p hp').1,
      (h3 k r z z' γ hs hp p hp').2⟩⟩, ?_, ?_⟩
  · intro ρ1 h1' ρ2 h2' heq
    apply hinj ρ1 h1' ρ2 h2'
    exact ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
      (h1 k r z z' γ hs hp ρ2 h2')).1 heq)
  · intro ρ1 h1' ρ2 h2' heq
    apply hinj ρ1 h1' ρ2 h2'
    exact ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
      (h1 k r z z' γ hs hp ρ2 h2')).2 heq)

end PI.StabPairsW
end
end

namespace PI.StabPairsW

theorem gram_matrix_invariance : GramInv := gramInv_of frameInd

theorem stabilizer_pair_formula : PairFormula := pairFormula_of gram_matrix_invariance

theorem stabPairs_of_converse (h : ConverseStep) : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs_of mapsStep stabilizer_pair_formula h compDet

end PI.StabPairsW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStepOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.HermBvecFvec
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.UtSubOneLast
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConvAlg
open Matrix

noncomputable section
namespace PI.StabPairs.ConvAlg

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def rhoOf (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ) : Matrix n n ℂ :=
  1 + F * ((W - 1) * ((Fᴴ * H * F)⁻¹ * (Fᴴ * H)))

theorem rhoOf_mul (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hG : IsUnit (Fᴴ * H * F).det) : rhoOf H F W * F = F * W := by
  have hinv : (Fᴴ * H * F)⁻¹ * (Fᴴ * H * F) = 1 := Matrix.nonsing_inv_mul _ hG
  rw [rhoOf, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc F, Matrix.mul_assoc (W - 1),
    Matrix.mul_assoc (Fᴴ * H * F)⁻¹, hinv, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]
  abel

theorem rhoOf_mulVec_of_ker (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (v : n → ℂ) (hv : (Fᴴ * H) *ᵥ v = 0) : rhoOf H F W *ᵥ v = v := by
  rw [rhoOf, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hv]
  simp

theorem rhoOf_unitary (H : Matrix n n ℂ) (F : Matrix n m ℂ) (W : Matrix m m ℂ)
    (hH : Hᴴ = H) (hG : IsUnit (Fᴴ * H * F).det) (hW : Wᴴ * (Fᴴ * H * F) * W = Fᴴ * H * F) :
    (rhoOf H F W)ᴴ * H * rhoOf H F W = H := by
  have hGh : (Fᴴ * H * F)ᴴ = Fᴴ * H * F := by
    simp [Matrix.conjTranspose_mul, hH, Matrix.mul_assoc]
  have hinvh : ((Fᴴ * H * F)⁻¹)ᴴ = (Fᴴ * H * F)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hGh]
  have hFHh : (Fᴴ * H)ᴴ = H * F := by simp [Matrix.conjTranspose_mul, hH]
  have hGi : (Fᴴ * H * F) * (Fᴴ * H * F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hiG : (Fᴴ * H * F)⁻¹ * (Fᴴ * H * F) = 1 := Matrix.nonsing_inv_mul _ hG
  have hKh : ((Fᴴ * H * F)⁻¹ * (Fᴴ * H))ᴴ = H * F * (Fᴴ * H * F)⁻¹ := by
    rw [Matrix.conjTranspose_mul, hinvh, hFHh]
  have e1 : H * F = ((Fᴴ * H * F)⁻¹ * (Fᴴ * H))ᴴ * (Fᴴ * H * F) := by
    rw [hKh, Matrix.mul_assoc, hiG, Matrix.mul_one]
  have e2 : Fᴴ * H = (Fᴴ * H * F) * ((Fᴴ * H * F)⁻¹ * (Fᴴ * H)) := by
    rw [← Matrix.mul_assoc, hGi, Matrix.one_mul]
  unfold rhoOf
  generalize hKd : (Fᴴ * H * F)⁻¹ * (Fᴴ * H) = K at e1 e2 ⊢
  generalize hGd : Fᴴ * H * F = G at e1 e2 hW
  have t3 : Kᴴ * (W - 1)ᴴ * Fᴴ * H * F * (W - 1) * K = Kᴴ * (W - 1)ᴴ * G * (W - 1) * K := by
    rw [← hGd]; simp only [Matrix.mul_assoc]
  have t1 : H * F * (W - 1) * K = Kᴴ * G * (W - 1) * K := by rw [e1]
  have t2 : Kᴴ * (W - 1)ᴴ * Fᴴ * H = Kᴴ * (W - 1)ᴴ * G * K := by
    rw [Matrix.mul_assoc (Kᴴ * (W - 1)ᴴ) Fᴴ H, e2, ← Matrix.mul_assoc]
  have inner : G * (W - 1) + (W - 1)ᴴ * G + (W - 1)ᴴ * G * (W - 1) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    calc G * (W - 1) + (Wᴴ - 1) * G + (Wᴴ - 1) * G * (W - 1) = Wᴴ * G * W - G := by noncomm_ring
      _ = 0 := by rw [hW, sub_self]
  calc (1 + F * ((W - 1) * K))ᴴ * H * (1 + F * ((W - 1) * K))
      = H + H * F * (W - 1) * K + Kᴴ * (W - 1)ᴴ * Fᴴ * H
        + Kᴴ * (W - 1)ᴴ * Fᴴ * H * F * (W - 1) * K := by
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_mul]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = H + Kᴴ * (G * (W - 1) + (W - 1)ᴴ * G + (W - 1)ᴴ * G * (W - 1)) * K := by
        rw [t3, t1, t2]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
    _ = H := by rw [inner]; simp

end PI.StabPairs.ConvAlg
end
end

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem ut_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (j : Fin (r + 1)) :
    u (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  split_ifs with h
  · subst h; exact hu.2 _
  · exact hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

theorem ut_det {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) : u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

theorem ut_sub_one_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (x : Fin (r + 1) → ℂ) : ((u - 1) *ᵥ x) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, ut_last hu, Matrix.one_apply]
  by_cases h : j = Fin.last r
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ut_conj_fix {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp only [ha, if_false, star_zero, zero_mul]
      exact (hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm
  · intro b _ hb
    rw [hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]
  · simp

theorem cancel_of_pair {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by
  have hA : IsUnit (uᴴ * Z).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]; exact hZ
  have h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]
  calc (u' - 1) *ᵥ c = ((uᴴ * Z)⁻¹ * (uᴴ * Z)) *ᵥ ((u' - 1) *ᵥ c) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem ut_adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hu : u ∈ UTset (r + 1)) : uᴴ * Adiag k r z * u = Adiag k r z := by
  ext a b
  rw [Adiag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu a, ut_last hu b, Matrix.diagonal_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
    · subst ha; subst hb; simp
    · subst ha; simp [hb, Ne.symm hb]
    · subst hb; simp [ha]
    · simp [ha, hb]
  · intro c _ hc; simp [hc]
  · simp

end PI.StabPairs.Conv
end
end

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem rho_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' =
      PI.StabPairs.ConvAlg.rhoOf (Hpk k r) (Fm k r z z' γ) (Wm u u') := by
  have hG : gramM k r z z' γ = (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    ext i j
    simp only [gramM, herm, Fm, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf PI.StabPairs.ConvAlg.rhoOf PI.StabPairsW.Km
  rw [hG]
  simp only [Matrix.mul_assoc]

theorem Wm_sub_one {r : ℕ} (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Wm u u' - 1 = Matrix.fromBlocks (u - 1) 0 0 (u' - 1) := by
  unfold Wm
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

theorem rho_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    PI.StabPairsW.rhoOf k r z z' γ u u' *ᵥ v =
      v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
        (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
  have hF : ∀ (x y : Fin (r + 1) → ℂ), Fm k r z z' γ *ᵥ Sum.elim x y =
      Ff k r z *ᵥ x + (γ * Ff k r z') *ᵥ y := by
    intro x y
    rw [← Matrix.mulVec_mulVec]
    ext i
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fm,
      Matrix.of_apply, gramVec, Ff, Pi.add_apply, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  unfold PI.StabPairsW.rhoOf
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Wm_sub_one, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  rw [hF, ← add_assoc]

theorem gram_Km (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ) :
    gramM k r z z' γ *ᵥ (Km k r z z' γ *ᵥ v) = ((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v := by
  unfold PI.StabPairsW.Km
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (gramM k r z z' γ)⁻¹, ← Matrix.mul_assoc (gramM k r z z' γ),
    Matrix.mul_nonsing_inv _ hGi, Matrix.one_mul]

theorem FH_apply (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ)
    (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem Z_cR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hS : Std k r z z')
    (hP : PosPt k r z z' γ) (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a : Fin (r + 1), a.val < r → herm (Hpk k r) v (fvec k r z a) = 0) :
    ∀ a : Fin (r + 1), a.val < r → (Zhat k r z z' γ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) a = 0 := by
  have hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0 := by
    intro e c he hc
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r →
      ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) →
      herm (Hpk k r) x (fvec k r y a) = 0 := by
    intro y a ha x hx
    unfold fvec
    rw [dite_eq_left ha]
    simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]
    · simp only [Pi.single_eq_same, star_one, one_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : r + k < c.val
      · rw [hx c hc, mul_zero]
      · rw [hHz _ _ ha (by omega), zero_mul]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)),
      r + k < c.val → fvec k r y b c = 0 := by
    intro y hy b c hc
    unfold fvec
    split_ifs with hb
    · exact Pi.single_eq_of_ne (fun h' => by
        have := congrArg Fin.val h'
        simp [eI] at this
        omega) _
    · exact hy c (Or.inr hc)
  intro a ha
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inl a)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inl a)) = 0 := hv a ha
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = 0 :=
    fun b => hrow z a ha _ (hfz z hS.2.1.1 b)
  simp only [h1, zero_mul, Finset.sum_const_zero, zero_add] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp]
  exact hK

theorem Z_cL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hS : Std k r z z')
    (hP : PosPt k r z z' γ) (hGi : IsUnit (gramM k r z z' γ).det) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin (r + 1), b.val < r → herm (Hpk k r) v (γ *ᵥ fvec k r z' b) = 0) :
    ∀ b : Fin (r + 1), b.val < r → ((Zhat k r z z' γ)ᴴ *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) b = 0 := by
  have hHz : ∀ e c : Fin (2 * r + k + 1), e.val < r → c.val ≤ r + k → Hpk k r e c = 0 := by
    intro e c he hc
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.2 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hrow : ∀ (y : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)), a.val < r →
      ∀ x : Fin (2 * r + k + 1) → ℂ, (∀ c : Fin (2 * r + k + 1), r + k < c.val → x c = 0) →
      herm (Hpk k r) x (fvec k r y a) = 0 := by
    intro y a ha x hx
    unfold fvec
    rw [dite_eq_left ha]
    simp only [herm, bvec, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [Finset.sum_eq_single (eI k r ⟨a.val, ha⟩)]
    · simp only [Pi.single_eq_same, star_one, one_mul]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : r + k < c.val
      · rw [hx c hc, mul_zero]
      · rw [hHz _ _ ha (by omega), zero_mul]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfz : ∀ (y : Fin (2 * r + k + 1) → ℂ), inWb k r y → ∀ (b : Fin (r + 1)) (c : Fin (2 * r + k + 1)),
      r + k < c.val → fvec k r y b c = 0 := by
    intro y hy b c hc
    unfold fvec
    split_ifs with hb
    · exact Pi.single_eq_of_ne (fun h' => by
        have := congrArg Fin.val h'
        simp [eI] at this
        omega) _
    · exact hy c (Or.inr hc)
  intro b hb
  have hK := congrFun (gram_Km k r z z' γ hGi v) (Sum.inr b)
  rw [FH_apply] at hK
  generalize Km k r z z' γ *ᵥ v = w at hK ⊢
  have h0 : herm (Hpk k r) v (gramVec k r z z' γ (Sum.inr b)) = 0 := hv b hb
  rw [h0] at hK
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type] at hK
  have h1 : ∀ a, gramM k r z z' γ (Sum.inr b) (Sum.inr a) = 0 := by
    intro a
    show herm (Hpk k r) (γ *ᵥ fvec k r z' a) (γ *ᵥ fvec k r z' b) = 0
    rw [herm_GV hP.1]
    exact hrow z' b hb _ (hfz z' hS.2.2.1 a)
  simp only [h1, zero_mul, Finset.sum_const_zero, add_zero] at hK
  simp only [Matrix.mulVec, dotProduct, Function.comp, Matrix.conjTranspose_apply]
  rw [← hK]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  show star (herm (Hpk k r) (γ *ᵥ fvec k r z' b) (fvec k r z a)) =
    herm (Hpk k r) (fvec k r z a) (γ *ᵥ fvec k r z' b)
  rw [herm_swap (fvec k r z a)]

theorem herm_bvec_fvec (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1))
    (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) (a : Fin (r + 1)) (ha : a.val < r) :
    herm (Hpk k r) (bvec j) (fvec k r z a) = 0 := by
  have hH : ∀ (e j : Fin (2 * r + k + 1)), e.val < r → r ≤ j.val → j.val ≤ r + k →
      Hpk k r e j = 0 := by
    intro e j he hj1 hj2
    unfold Hpk
    rw [if_neg (fun h => absurd h.2 (by omega)), if_neg (fun h => absurd h.1 (by omega)),
      if_neg (fun h => absurd h.1 (by omega))]
  have hf : fvec k r z a = bvec (eI k r ⟨a.val, ha⟩) := by
    unfold fvec
    rw [dite_eq_left ha]
  rw [hf]
  have h1 : herm (Hpk k r) (bvec j) (bvec (eI k r ⟨a.val, ha⟩)) = Hpk k r (eI k r ⟨a.val, ha⟩) j := by
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  exact hH _ _ ha hj1 hj2

theorem N2gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r)
    {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (hM : M * Ff k r z = Ff k r z * u)
    (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    M i (eI k r a) = if i = eI k r a then 1 else 0 := by
  classical
  have hfa : fvec k r z (Fin.castSucc a) = bvec (eI k r a) := by
    unfold fvec
    rw [dite_eq_left (by simp)]
    rfl
  have h1 := congrFun (congrFun hM i) (Fin.castSucc a)
  have hL : (M * Ff k r z) i (Fin.castSucc a) = M i (eI k r a) := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply, hfa]
    simp [bvec, Pi.single_apply]
  have hR : (Ff k r z * u) i (Fin.castSucc a) = if i = eI k r a then 1 else 0 := by
    simp only [Matrix.mul_apply, Ff, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.castSucc a)]
    · rw [hu.2, mul_one, hfa]
      simp [bvec, Pi.single_apply]
    · intro b _ hb
      by_cases hba : Fin.castSucc a < b
      · rw [hu.1 _ _ hba, mul_zero]
      · have hlt : b.val < a.val := by
          have h2 : b < Fin.castSucc a := lt_of_le_of_ne (not_lt.mp hba) hb
          exact h2
        have hbr : b.val < r := by omega
        have : fvec k r z b i = 0 := by
          unfold fvec
          rw [dite_eq_left hbr]
          exact Pi.single_eq_of_ne (fun h' => by
            have := congrArg Fin.val h'
            simp [eI] at this
            omega) _
        rw [this, zero_mul]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  rw [← hL, h1, hR]

theorem N3gen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (M : B.Mat k r) (i j : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) (x : Fin (r + 1) → ℂ) (hx : x (Fin.last r) = 0)
    (h : M *ᵥ bvec j = bvec j + Ff k r z *ᵥ x) : M i j = if i = j then 1 else 0 := by
  classical
  have h1 := congrFun h i
  have hMj : (M *ᵥ bvec j) i = M i j := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hMj] at h1
  rw [h1, Pi.add_apply]
  have h2 : (Ff k r z *ᵥ x) i = 0 := by
    simp only [Matrix.mulVec, dotProduct, Ff, Matrix.of_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b.val < r
    · have : fvec k r z b i = 0 := by
        unfold fvec
        rw [dite_eq_left hb]
        exact Pi.single_eq_of_ne (fun h' => by
          have := congrArg Fin.val h'
          simp [eI] at this
          omega) _
      rw [this, zero_mul]
    · have hbl : b = Fin.last r := Fin.ext (by have := b.isLt; simp; omega)
      rw [hbl, hx, mul_zero]
  rw [h2, add_zero]
  simp [bvec, Pi.single_apply]

end PI.StabPairs.Conv
end
end

open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem one_mem_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  all_goals simp

theorem converseStep_of (hG : GramInv) : ConverseStep := by
  intro k r z z' γ hS hP p hp
  obtain ⟨u, u'⟩ := p
  obtain ⟨hu, hu', hZp⟩ := hp
  simp only at hu hu' hZp
  have hGi := hG k r z z' γ hS hP
  have hγ : γ ∈ B.GV k r := hP.1
  have hγu : IsUnit γ.det := isUnit_det_of_mem_GV hγ
  have hZ : IsUnit (Zhat k r z z' γ).det := isUnit_iff_ne_zero.mpr (det_Zhat_ne z z' hS γ hP)
  have hZh : IsUnit (Zhat k r z z' γ)ᴴ.det := by
    rw [Matrix.det_conjTranspose]; exact hZ.star
  have hZp' : u'ᴴ * (Zhat k r z z' γ)ᴴ * u = (Zhat k r z z' γ)ᴴ := by
    have := congrArg Matrix.conjTranspose hZp
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  have hGi' : IsUnit ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ).det := by rwa [← gramM_eq]
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = PI.StabPairsW.rhoOf k r z z' γ u u' := ⟨_, rfl⟩
  rw [← hρ]

  have hρF : ρ * Fm k r z z' γ = Fm k r z z' γ * Wm u u' := by
    rw [hρ, rho_eq]; exact PI.StabPairs.ConvAlg.rhoOf_mul _ _ _ hGi'
  have hcols := hρF
  rw [Fm_eq, Matrix.mul_fromCols, Wm, Matrix.fromCols_mul_fromBlocks] at hcols
  simp only [Matrix.mul_zero, add_zero, zero_add] at hcols
  obtain ⟨hA, hB⟩ := (Matrix.fromCols_ext_iff _ _ _ _).mp hcols
  have hs' : γ⁻¹ * ρ * γ * Ff k r z' = Ff k r z' * u' := by
    calc γ⁻¹ * ρ * γ * Ff k r z' = γ⁻¹ * (ρ * (γ * Ff k r z')) := by simp only [Matrix.mul_assoc]
      _ = γ⁻¹ * (γ * Ff k r z' * u') := by rw [hB]
      _ = Ff k r z' * u' := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγu, Matrix.one_mul]

  have hWG : (Wm u u')ᴴ * ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ) * Wm u u' =
      (Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ := by
    rw [← gramM_eq, gramM_blocks z z' hS.2.1.1 hS.2.2.1 γ hγ, Wm, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [ut_adiag k r z hu, ut_adiag k r z' hu', hZp, hZp']
  have hUH : ρ ∈ B.GV k r := by
    rw [mem_GV_iff, hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_unitary _ _ _ hpk_conjTranspose hGi' hWG
  have hexp : ∀ v, ρ *ᵥ v = v + Ff k r z *ᵥ ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inl)) +
      (γ * Ff k r z') *ᵥ ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ v) ∘ Sum.inr)) := by
    intro v; rw [hρ]; exact rho_mulVec k r z z' γ u u' v

  have hN : ρ ∈ Nset k r := by
    refine ⟨hUH, fun a i hi => N2gen k r z ρ hu hA a i hi, fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z ρ i j hi ((u - 1) *ᵥ ((Km k r z z' γ *ᵥ bvec j) ∘ Sum.inl)) (ut_sub_one_last hu _) ?_
    have hc := cancel_of_pair hu hZ hZp _
      (Z_cR k r z z' γ hS hP hGi (bvec j) (fun a ha => herm_bvec_fvec k r z j hj1 hj2 a ha))
    rw [hexp, hc, Matrix.mulVec_zero, add_zero]

  have hN' : γ⁻¹ * ρ * γ ∈ Nset k r := by
    refine ⟨mul_mem_GV (mul_mem_GV (inv_mem_GV hγ) hUH) hγ, fun a i hi => N2gen k r z' _ hu' hs' a i hi,
      fun i j hj1 hj2 hi => ?_⟩
    refine N3gen k r z' _ i j hi ((u' - 1) *ᵥ ((Km k r z z' γ *ᵥ (γ *ᵥ bvec j)) ∘ Sum.inr))
      (ut_sub_one_last hu' _) ?_
    have hc := cancel_of_pair hu' hZh hZp' _
      (Z_cL k r z z' γ hS hP hGi (γ *ᵥ bvec j) (fun b hb => by
        rw [herm_GV hγ]; exact herm_bvec_fvec k r z' j hj1 hj2 b hb))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hexp, hc, Matrix.mulVec_zero, add_zero,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hγu, Matrix.one_mulVec, Matrix.one_mul]
  refine ⟨⟨⟨⟨1, one_mem_UW k r z, ρ, hN, (Matrix.one_mul ρ).symm⟩,
    γ⁻¹ * ρ * γ, ⟨1, one_mem_UW k r z', _, hN', (Matrix.one_mul _).symm⟩, ?_⟩, ?_⟩, ?_⟩
  · calc ρ = (γ * γ⁻¹) * ρ * (γ * γ⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul, Matrix.mul_one]
      _ = γ * (γ⁻¹ * ρ * γ) * γ⁻¹ := by simp only [Matrix.mul_assoc]
  · intro v hv
    rw [mem_Uperp_iff] at hv
    rw [hρ, rho_eq]
    exact PI.StabPairs.ConvAlg.rhoOf_mulVec_of_ker _ _ _ v hv
  · show (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ)) = (u, u')
    rw [uMap_eq z hS.2.1 ρ u hA, uMap_eq z' hS.2.2 _ u' hs']

end PI.StabPairs.Conv
end
end

theorem stabPairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  PI.StabPairsW.stabPairs_of_converse (PI.StabPairs.Conv.converseStep_of PI.StabPairsW.gram_matrix_invariance)
