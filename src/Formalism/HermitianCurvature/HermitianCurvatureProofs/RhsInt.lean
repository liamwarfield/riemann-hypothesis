module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RhsInt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisConjInt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisMeasConjInv
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

private theorem iotaLev_one_eq_blk3 (ρ : ℕ) (g : B.Mat k ρ) :
    ιLev k 1 ρ g = U.blk3 (j := 1) 1 0 0 0 g 0 0 0 1 := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective q
  rw [Ux3.block3_apply]
  have vX : ∀ x : Fin 1, ((U.eB k 1 ρ) (Sum.inl (Sum.inl x))).val = 0 := fun x => by
    simp [U.eB]
  have vV : ∀ v : Fin (2 * ρ + k + 1), ((U.eB k 1 ρ) (Sum.inl (Sum.inr v))).val = 1 + v.val := fun v => by
    simp [U.eB]
  have vS : ∀ b : Fin 1, ((U.eB k 1 ρ) (Sum.inr b)).val = 2 * ρ + k + 2 := fun b => by
    simp [U.eB] <;> omega
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp only [Formalism.QuantumDeterminants.ιLev, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, vX, vV, vS, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | (congr <;> (try apply Fin.ext) <;> simp [vV])

theorem lev_mMap (ρ : ℕ) (g g' : B.Mat k ρ) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    ιLev k 1 ρ g * U.mMap k 1 ρ Z γ * ιLev k 1 ρ g' = U.mMap k 1 ρ Z (g * γ * g') := by
  rw [iotaLev_one_eq_blk3, iotaLev_one_eq_blk3]
  simp only [U.mMap]
  rw [Ux5.block3_mul_blocks, Ux5.block3_mul_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem sgs_alg (ρ : ℕ) (h0 y h0' y' : B.Mat k ρ) (hh0 : IsUnit h0.det) (hy : IsUnit y.det) (hh0' : IsUnit h0'.det)
    (hy' : IsUnit y'.det) (a a' : B.Mat k (1 + ρ)) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    (ιLev k 1 ρ h0)⁻¹ * (a * ιLev k 1 ρ y)⁻¹ * U.mMap k 1 ρ Z γ * (a' * ιLev k 1 ρ y') * ιLev k 1 ρ h0' =
      ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0))⁻¹ *
        U.mMap k 1 ρ Z ((y * h0)⁻¹ * γ * (y' * h0')) * ((ιLev k 1 ρ (y' * h0'))⁻¹ * a' * ιLev k 1 ρ (y' * h0')) := by
  have hL0 := PI.QnLevBasicsW.level_group_homomorphism
  have hL := hL0
  unfold Formalism.QuantumDeterminants.LevHom at hL
  have ιmul : ∀ g h : B.Mat k ρ, ιLev k 1 ρ (g * h) = ιLev k 1 ρ g * ιLev k 1 ρ h := (hL k 1 ρ).2
  have ιone : ιLev k 1 ρ (1 : B.Mat k ρ) = 1 := (hL k 1 ρ).1
  have ιinv : ∀ g : B.Mat k ρ, IsUnit g.det → (ιLev k 1 ρ g)⁻¹ = ιLev k 1 ρ g⁻¹ :=
    fun g hg => PIQnLT.ιLev_inv hL0 g hg
  have hW : IsUnit (y * h0).det := by
    rw [Matrix.det_mul]
    exact hy.mul hh0
  have hW' : IsUnit (y' * h0').det := by
    rw [Matrix.det_mul]
    exact hy'.mul hh0'
  have hW1 : ∀ X, ιLev k 1 ρ (y * h0) * (ιLev k 1 ρ (y * h0)⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW, ιone, one_mul]
  have hW2 : ∀ X, ιLev k 1 ρ (y' * h0') * (ιLev k 1 ρ (y' * h0')⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW', ιone, one_mul]
  have hLw : ∀ X, ιLev k 1 ρ h0⁻¹ * (ιLev k 1 ρ y⁻¹ * X) = ιLev k 1 ρ (y * h0)⁻¹ * X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_inv_rev]
  have hRw : ιLev k 1 ρ y' * ιLev k 1 ρ h0' = ιLev k 1 ρ (y' * h0') := (ιmul _ _).symm
  rw [Matrix.mul_inv_rev a, ιinv _ hh0, ιinv _ hy, ιinv _ hW, ιinv _ hW', ← lev_mMap]
  rw [Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹ * a) (ιLev k 1 ρ (y * h0)),
    Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹) a, ιinv _ hW, ιinv _ (Matrix.isUnit_nonsing_inv_det _ hW),
    Matrix.nonsing_inv_nonsing_inv _ hW]
  simp only [mul_assoc]
  rw [hLw, hRw, hW1, hW2]

theorem psi_Qm (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : Mt k (1 + ρ)} {y : Mt k ρ}
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (hy : Matrix.of y ∈ Nset k ρ) :
    psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (D.castM (Nat.add_comm 1 ρ) (Matrix.of a)) *
        psi k ρ z0 cStd (Matrix.of y) := by
  show psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd
      (D.castM (Nat.add_comm 1 ρ) (Matrix.of a * ιLev k 1 ρ (Matrix.of y))) = _
  rw [psi_castM, psi_castM, Qx4.psi_mul (Qx4.lift_inWb hz0) ha (B2x6.lev_n hy), Qx4.psi_lev]

theorem psi_conjLev (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : B.Mat k (1 + ρ)}
    {y h0 : B.Mat k ρ} (ha : a ∈ Nset k (1 + ρ)) (hy : y ∈ Nset k ρ) (hh0 : h0 ∈ UWset k ρ z0) :
    psi k (1 + ρ) (liftVec k 1 ρ z0) cStd ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0)) =
      psi k (1 + ρ) (liftVec k 1 ρ z0) cStd a := by
  have hz1 := Qx4.lift_inWb hz0
  have hyN : ιLev k 1 ρ y ∈ Nset k (1 + ρ) := B2x6.lev_n hy
  have hhW : ιLev k 1 ρ h0 ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := Dx2.Tower.lev_UW 1 ρ z0 h0 hh0
  have hu : (ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y ∈ Nset k (1 + ρ) :=
    WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hyN) ha) hyN
  have e : (ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0) =
      (ιLev k 1 ρ h0)⁻¹ * ((ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y) * ιLev k 1 ρ h0 := by
    rw [Dx2.Tower.lev_mul, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [e, Qx4.psi_conjW' hz1 hhW hu, Qx4.psi_conjN' hz1 hyN ha]

theorem heis_meas_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    (B2.μHeis k ρ).map (conjM ((ιLev k 1 ρ g)⁻¹)) = B2.μHeis k ρ := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure k ρ g⁻¹ hgi
  rwa [LongWeylElement.lev_inv _ hu] at h

end Formalism.FourierDecayAlt.P.PBH
end
end

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem phi_cont (ρ : ℕ) : Continuous (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  have e : (Dx2.MN.phi (k := k) (ρ := ρ)) = fun x => Dx2.MN.phi x := rfl
  rw [e]
  simp only [Dx2.MN.phi]
  fun_prop

def heisT (ρ : ℕ) (x : B2.HPar k ρ) : Mt k (1 + ρ) := Matrix.of.symm (B2.heis0 k ρ x)

theorem heis_cont (ρ : ℕ) : Continuous (heisT (k := k) ρ) := B2x5.continuous_heis0 k ρ

theorem heis_emb (ρ : ℕ) : MeasurableEmbedding (heisT (k := k) ρ) :=
  (heis_cont ρ).measurableEmbedding (Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed k ρ).1

def phiE (ρ : ℕ) : U.RC k 1 ρ ≃ᵐ B2.HPar k ρ where
  toFun := Dx2.MN.phi
  invFun p := (fun i _ => p.1 i, (fun _ => 0, fun _ => p.2))
  left_inv x := by
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Dx2.MN.phi, Prod.mk.injEq]
    refine ⟨?_, Subsingleton.elim _ _, ?_⟩
    · funext i a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
    · funext a; have : a = 0 := Subsingleton.elim _ _; subst this; rfl
  right_inv p := by simp [Dx2.MN.phi]
  measurable_toFun := (phi_cont ρ).measurable
  measurable_invFun := by
    apply Continuous.measurable
    exact (continuous_pi fun i => continuous_pi fun _ => (continuous_apply i).comp continuous_fst).prodMk
      (continuous_const.prodMk (continuous_pi fun _ => continuous_snd))

theorem phi_emb (ρ : ℕ) : MeasurableEmbedding (Dx2.MN.phi (k := k) (ρ := ρ)) := by
  exact (phiE ρ).measurableEmbedding

theorem heis_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : B.Mat k (1 + ρ) → B.Mat k (1 + ρ) → E) :
    ∫ p : Mt k (1 + ρ) × Mt k (1 + ρ), Φ (Matrix.of p.1) (Matrix.of p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, Φ (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
        ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) := by
  have e0 : B2.μHeis k ρ = (volume : Measure (B2.HPar k ρ)).map (heisT ρ) := rfl
  have e1 : (B2.μHeis k ρ).prod (B2.μHeis k ρ) =
      ((volume : Measure (B2.HPar k ρ)).prod volume).map (Prod.map (heisT (k := k) ρ) (heisT ρ)) := by
    rw [e0, Measure.map_prod_map _ _ (heis_emb ρ).measurable (heis_emb ρ).measurable]
  rw [e1, ((heis_emb ρ).prodMap (heis_emb ρ)).integral_map]
  have hmp : MeasurePreserving (Prod.map (Dx2.MN.phi (k := k) (ρ := ρ)) (Dx2.MN.phi (k := k) (ρ := ρ)))
      ((U.muRC k 1 ρ).prod (U.muRC k 1 ρ)) ((volume : Measure (B2.HPar k ρ)).prod volume) := by
    have := (Dx2.MN.phi_mp (k := k) (ρ := ρ)).prod (Dx2.MN.phi_mp (k := k) (ρ := ρ))
    simpa [U.muRC] using this
  rw [← hmp.integral_comp ((phi_emb ρ).prodMap (phi_emb ρ))]
  apply integral_congr_ae
  filter_upwards with xx
  rw [Dx2.MN.rn_heis, Dx2.MN.rn_heis]
  rfl

def conjE {r : ℕ} (b : B.Mat k r) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM b
  invFun := conjM b⁻¹
  left_inv x := by
    show b⁻¹ * (b * Matrix.of x * b⁻¹) * b⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hb, Matrix.nonsing_inv_mul _ hb, Matrix.mul_one]
  right_inv x := by
    show b * (b⁻¹ * Matrix.of x * b⁻¹⁻¹) * b⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hb]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hb, Matrix.mul_nonsing_inv _ hb, Matrix.mul_one]
  measurable_toFun := B2x5.measurable_conjM b
  measurable_invFun := B2x5.measurable_conjM b⁻¹

theorem heis_conj_int (ρ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g g' : B.Mat k ρ}
    (hg : g ∈ B.GV k ρ) (hg' : g' ∈ B.GV k ρ) (Φ : Mt k (1 + ρ) × Mt k (1 + ρ) → E) :
    ∫ p, Φ (conjM ((ιLev k 1 ρ g)⁻¹) p.1, conjM ((ιLev k 1 ρ g')⁻¹) p.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) =
      ∫ p, Φ p ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
  have := sf_heis (k := k) ρ
  have hu : IsUnit ((ιLev k 1 ρ g)⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg))
  have hu' : IsUnit ((ιLev k 1 ρ g')⁻¹).det :=
    Matrix.isUnit_nonsing_inv_det_iff.2 (LongWeylElement.lev_unit _ (HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg'))
  have m1 : MeasurePreserving (conjE _ hu) (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu).measurable, heis_meas_conj_inv ρ hg⟩
  have m2 : MeasurePreserving (conjE _ hu') (B2.μHeis k ρ) (B2.μHeis k ρ) :=
    ⟨(conjE _ hu').measurable, heis_meas_conj_inv ρ hg'⟩
  have := (m1.prod m2).integral_comp ((conjE _ hu).measurableEmbedding.prodMap (conjE _ hu').measurableEmbedding) Φ
  exact this

end Formalism.FourierDecayAlt.P.PBH
end
end

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem rhs_int {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef Bs F) (g : B.Mat k r) (hg : g ∈ JF.Om k r Bs.z Bs.z') :
    Integrable (JF.integrand Bs F g) Bs.μSS := by
  obtain ⟨hFs, ⟨R, hR⟩, -⟩ := hF
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  set A : ℝ := 9 * ((r : ℝ) + 1) * (n ^ 2 + 1) with hA
  have hthr : JF.TransportedAlt k r A 0 := by
    unfold JF.TransportedAlt
    have hpos : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
    have e : (A - 6 * (r : ℝ) * ((0 : ℕ) : ℝ)) / (9 * ((r : ℝ) + 1)) = n ^ 2 + 1 := by
      rw [hA]; push_cast; field_simp; ring
    rw [← hn, e]; linarith
  have hcc : B.InCC A 0 F := JFxG.cptInCC_G hFs (PBE.isCompact_gN_le k r R)
    (fun g hg hgC => by
      by_contra h0
      exact hgC (hR g hg h0)) A 0
  exact (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq Bs A F hthr hcc).1 g hg

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalProof
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.FourierDecayAlt.P.MAx2.Adj Formalism.FourierDecayAlt.P.MAx1.An Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section deriv

variable {k r : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']

theorem ldV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    B.LdV X (fun g => L (f g)) = fun g => L (B.LdV X f g) := by
  funext g
  unfold B.LdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0

theorem rdV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    Formalism.REAL.RdV X (fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X f g) := by
  funext g
  unfold Formalism.REAL.RdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) :
    ∀ (v : List (B.Mat k r)) (f : B.Mat k r → F), B.Rw v (fun g => L (f g)) = fun g => L (B.Rw v f g)
  | [], _ => rfl
  | X :: v, f => by
    show Formalism.REAL.RdV X (B.Rw v fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X (B.Rw v f) g)
    rw [rw_rl L L' hL v f, rdV_rl L L' hL X]

theorem dLR_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (w : List (B.Mat k r)) :
    ∀ (u : List (B.Mat k r)) (f : B.Mat k r → F), B.dLR u w (fun g => L (f g)) = fun g => L (B.dLR u w f g)
  | [], f => rw_rl L L' hL w f
  | X :: u, f => by
    show B.LdV X (B.dLR u w fun g => L (f g)) = fun g => L (B.LdV X (B.dLR u w f) g)
    rw [dLR_rl L L' hL w u f, ldV_rl L L' hL X]

theorem dLR_conj (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => conj (f g)) = fun g => conj (B.dLR u w f g) :=
  dLR_rl (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fun y => by simp) w u f

theorem dLR_smulc (A : F) (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => f g • A) = fun g => B.dLR u w f g • A := by
  by_cases hA : A = 0
  · subst hA; simp only [smul_zero]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero u w
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ A (norm_ne_zero_iff.2 hA)
  have hn : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hA
  let L : ℂ →L[ℝ] F := ((ContinuousLinearMap.id ℂ ℂ).smulRight A).restrictScalars ℝ
  let L' : F →L[ℝ] ℂ := ((((‖A‖ : ℝ) : ℂ))⁻¹ • ℓ).restrictScalars ℝ
  have hL : ∀ y, L' (L y) = y := fun y => by
    simp only [L, L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul, hℓ, smul_eq_mul]
    field_simp
    norm_cast
  exact dLR_rl L L' hL w u f

end deriv

theorem scalar_conjugation_transfer : JAScalConj := by
  intro k r Wp Wq _ _ _ _ D Bg φ hφ
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε m => ?_⟩
  · obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    refine ⟨U, fun g => conj (φ' g), hU, hg, ?_, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφ'
  · obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_conj, Complex.norm_conj]
    exact hC u w hu hw hl g hg hG

section real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem scal_real (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (Cb : ℝ)
    (φ : B.Mat S.G.k S.G.r → ℂ) (hφ : ScalOK (T v).base (Cb * ((S.G.r : ℝ) + 1)) φ)
    (hinv : ∀ p, (T v).base.inSS p → ∀ g, φ (B.sgs p g) = φ g)
    (β : (DQ (D.parOf S v)).R)
    (hval : ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      φ (B.gq (T v).base q) = evD (D.parOf S v) ⟨q, hq⟩ β) :
    BddReal S T v e Cb (Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP β (cjD (D.parOf S v) β))) := by
  have hφc := scalar_conjugation_transfer _ _ _ _ (T v).base _ φ hφ
  refine SSn.real_to_bounded_holds E Wp Wq S T v hPl e Cb
    (fun g => φ g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun g => conj (φ g) • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun ρ π q => if ρ = π then evD (D.parOf S v) q β else 0) _ hFr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · intro x A B'
    simp only [B.hsInner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      P.TBBx2.Tri.hsVec_smul, inner_smul_left, inner_smul_right, Complex.conj_conj]
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφc.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by
        show conj (φ g) • _ = φ' g • _
        rw [show conj (φ g) = φ' g from he g hgU hgG]⟩
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφc.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro q hq ρ π
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul,
      inner_smul_right, (hFr.2 q.2 hq.2).2.1 ρ π, hval q hq]
    split_ifs <;> simp
  · intro ρ π
    by_cases h : ρ = π
    · subst h
      exact ⟨β, by rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq], fun q => by simp⟩
    · refine ⟨0, ?_, fun q => by simp [h]⟩
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, cjD_zero, multiplierPair_zero]

end real

section main

theorem phiR_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiR k r D.z D.z' (B.sgs p g) = phiR k r D.z D.z' g := by
  unfold phiR; rw [P.BigCellZetaMinors.dmin_sgs D hp, P.BigCellZetaMinors.dmin_sgs D hp]

theorem phiD_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiD k r D.z D.z' (B.sgs p g) = phiD k r D.z D.z' g := by
  unfold phiD; rw [P.BigCellZetaMinors.dmin_sgs D hp]

theorem dmin_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') :
    Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a ∧
      Dmin k r D.z D.z' (B.gq D q) (Fin.last (r + 1)) = q.2 * ∏ a, q.1 a := by
  have h1 : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a := by
    have := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).1 (Fin.last r)
    simp only [Fin.val_last] at this
    rw [show B.gq D q = bigCell k r q.1 (D.μsec q.2) from rfl, this]
    exact Finset.prod_congr (by ext a; simp) fun _ _ => rfl
  refine ⟨h1, ?_⟩
  have hz := P.BigCellZetaMinors.zeta_gq D hq
  have hne : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ ≠ 0 := by
    rw [h1]; exact Finset.prod_ne_zero_iff.2 fun a _ => hq.1 a
  unfold zeta at hz
  rw [← hz, ← h1, div_mul_cancel₀ _ hne]

theorem bounded_scalar_transfer_holds : JABddScal := by
  obtain ⟨K, hK0, hK⟩ := scalar_transfer_bound_holds
  refine ⟨K, hK0, fun Cc Cb _ hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hL b hb => ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' = (D.parOf S v).TT := by
    rw [hT, hT']; rfl
  have hTpos : 0 < (D.parOf S v).TT := by
    rw [← hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hT0 := hTpos.le
  have hQD : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun q hq => ⟨hq.1, by rw [hTT]; exact hq.2⟩
  have hBg : K * ((S.G.r : ℝ) + 1) ≤ Cb * ((S.G.r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCb (by positivity)
  obtain ⟨hR, hD⟩ := hK S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ hBg
  have hRc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hR
  have hDc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hD
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩ := hL

  have vR : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiR S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (q.2)⁻¹ := fun q hq => by
    have hz' := P.BigCellZetaMinors.zeta_gq (T v).base (hQD q hq)
    unfold zeta at hz'
    unfold phiR
    rw [← hz', inv_div]
  have vD : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiD S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) =
        (∏ a, q.1 a) * q.2 * ((conj q.2)⁻¹ * ∏ a, (conj (q.1 a))⁻¹) := fun q hq => by
    have h := (dmin_gq (T v).base (hQD q hq)).2
    have hz0 : q.2 ≠ 0 := BStar.z_ne hT0 ⟨q, hq⟩
    have hc0 : ∀ a, q.1 a ≠ 0 := hq.1
    unfold phiD
    rw [h, map_mul, map_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]
    ring
  rcases hb with rfl | rfl | rfl | rfl
  · rw [BStar.rep_zi hzi, ← BStar.cjD_izi hT0]
    refine scal_real S T v hPl e hFr Cb _ hR (fun p hp g => phiR_sgs _ hp g) _ fun q hq => ?_
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vz]
  · rw [BStar.rep_zbi hzbi, ← BStar.cjD_izbi hT0]
    refine scal_real S T v hPl e hFr Cb _ hRc (fun p hp g => by simp only [phiR_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vzb, map_inv₀]
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βD (D.parOf S v)) (βDb (D.parOf S v))) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e1, ← BStar.cjD_βD hT0]
    refine scal_real S T v hPl e hFr Cb _ hD (fun p hp g => phiD_sgs _ hp g) _ fun q hq => ?_
    rw [vD q hq]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]
  · have e2 : L.Db * L.Di = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βDb (D.parOf S v)) (βD (D.parOf S v))) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e2, ← BStar.cjD_βDb hT0]
    refine scal_real S T v hPl e hFr Cb _ hDc (fun p hp g => by simp only [phiD_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vD q hq, ← BStar.cjD_βD hT0, evD_cjD]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
