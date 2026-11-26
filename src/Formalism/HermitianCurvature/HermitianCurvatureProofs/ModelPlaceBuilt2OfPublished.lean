module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymbolLevi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRSSnRep

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfRest
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeActionHolds
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RightTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_right (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z') : g * h ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg (Qx8.uw_one z) (Qx8.nlev_one _) hh (Qx8.nlev_one _)
  simpa using this

theorem J_right (hπ' : IsCRepOn (UWset k r z') π') (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z') : J (g * h) = (J g).comp (π' h) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) h hh
  rw [Matrix.one_mul, Matrix.mul_one, hπ'.1] at e1
  rw [Matrix.one_mul] at e2
  have e3 : (J g).comp (1 : Wq →L[ℂ] Wq) = J g := ContinuousLinearMap.comp_id _
  rw [e3] at e1
  rw [e2, ← ContinuousLinearMap.comp_assoc, ← e1]

theorem rd_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {X : Mx k r} (hX : QrD.InLieW k r z' X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : RdV X F g = (J g).comp ((QrD.dOp π' X).comp B) := by
  have h := QrD.dOp_hasDeriv hπ' hc hX
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (J g)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wq).flip B)
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_right hD hg (QrD.exp_uw hX t)), J_right hπ' hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold RdV
  rw [h3]
  exact h2.deriv

theorem rz_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wq →L[ℂ] Wq}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = (J g).comp B) {Z : Mx k r}
    (h1 : QrD.InLieW k r z' (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z' (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    RZ (Hpk k r) Z F g = (J g).comp ((QrD.ecOp π' Z).comp B) := by
  unfold RZ QrD.ecOp
  rw [rd_right hD hπ' hc hJ hF h1 hg, rd_right hD hπ' hc hJ hF h2 hg]
  ext v
  simp

theorem fold_right (hD : IsDom k r z z' i D) (hπ' : IsCRepOn (UWset k r z') π')
    (hc : ContinuousOn π' (UWset k r z')) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z' (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z' (hpart2 (Hpk k r) p.2)) :
    ∃ B : Wq →L[ℂ] Wq,
      (∀ g ∈ Glev k r i ∩ D,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + RZ (Hpk k r) p.2 y).foldr (fun T h => T h) J g =
          (J g).comp B) ∧
      ∀ v, B v = (L.map fun p => fun y : Wq => p.1 • y + EcRep (Hpk k r) π' p.2 y).foldr (fun T h => T h) v := by
  induction L with
  | nil => exact ⟨1, fun g _ => (ContinuousLinearMap.comp_id _).symm, fun v => rfl⟩
  | cons p L ih =>
    obtain ⟨B, hB1, hB2⟩ := ih fun q hq => hL q (by simp [hq])
    have hp := hL p (by simp)
    refine ⟨p.1 • B + (QrD.ecOp π' p.2).comp B, fun g hg => ?_, fun v => ?_⟩
    · simp only [List.map_cons, List.foldr_cons, Pi.add_apply, Pi.smul_apply]
      rw [rz_right hD hπ' hc hJ hB1 hp.1 hp.2 hg, hB1 g hg]
      ext v
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [← hB2 v, QrD.ecRep_eq hπ' hc hp.1 hp.2]
      rfl

end RightTypeActionHermitianCurvature

theorem right_type_action_holds : RightTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ' hc J hJ g hg Bs hB w v
  unfold capR capRep qmF
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  obtain ⟨B, hB1, hB2⟩ := RightTypeActionHermitianCurvature.fold_right hD hπ' hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j)
  have e1 := hB1 g hg
  have e2 := hB2 v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1 e2
  simp only [id]
  rw [e1, ← e2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDomainIsDomain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem positive_domain_is_domain : IsDomOmPlus := fun _ _ _ _ hz hz' =>
  Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus hz hz'

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBasisHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LieBasisConstruction

def lieSubR (k r : ℕ) : Submodule ℝ (B.Mat k r) where
  carrier := {X | B.inLie k r X}
  add_mem' := by
    intro X Y hX hY
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * _ + _ * X) + (Yᴴ * _ + _ * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by
    unfold B.inLie
    simp
  smul_mem' := by
    intro c X hX
    unfold B.inLie at *
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

end LieBasisConstruction

theorem lie_basis_holds : LieBasis := by
  intro k r
  let S := LieBasisConstruction.lieSubR k r
  let b := Module.finBasis ℝ S
  let L0 : (Fin (Module.finrank ℝ S) → ℝ) →ₗ[ℝ] B.Mat k r := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hinj : LinearMap.ker L0 = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact S.injective_subtype.comp b.equivFun.symm.injective
  obtain ⟨M0, hM0⟩ := L0.exists_leftInverse_of_injective hinj
  have hML : ∀ y, M0 (L0 y) = y := fun y => LinearMap.congr_fun hM0 y
  refine ⟨Module.finrank ℝ S, LinearMap.toContinuousLinearMap L0, LinearMap.toContinuousLinearMap M0,
    fun x => (b.equivFun.symm x).2, fun x => hML x, fun X hX => ?_⟩
  have e : L0 (b.equivFun ⟨X, hX⟩) = X := by simp [L0]
  show L0 (M0 X) = X
  calc L0 (M0 X) = L0 (M0 (L0 (b.equivFun ⟨X, hX⟩))) := by rw [e]
    _ = X := by rw [hML, e]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleyAlgebraicHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace UnitInverseArithmetic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mul_inv_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem inv_mul_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem isUnit_of_mul_one {A B : Matrix n n ℂ} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem half_two : ((2 : ℂ)⁻¹) • ((1 : Matrix n n ℂ) + 1) = 1 := by
  rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul]; norm_num

theorem half_double (A : Matrix n n ℂ) : ((2 : ℂ)⁻¹) • (A + A) = A := by
  rw [← two_smul ℂ A, smul_smul]; norm_num

theorem fwd {H X : Matrix n n ℂ} (hX : Xᴴ * H + H * X = 0) (hu : IsUnit (1 - X)) :
    ((1 + X) * (1 - X)⁻¹)ᴴ * H * ((1 + X) * (1 - X)⁻¹) = H ∧ IsUnit ((1 + X) * (1 - X)⁻¹ + 1) ∧
      ((1 + X) * (1 - X)⁻¹ - 1) * ((1 + X) * (1 - X)⁻¹ + 1)⁻¹ = X := by
  set V := (1 - X)⁻¹ with hV
  have h1 : (1 - X) * V = 1 := mul_inv_of_isUnit hu
  have h2 : V * (1 - X) = 1 := inv_mul_of_isUnit hu
  have hXV : X * V = V - 1 := by
    have e := h1
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hg1 : (1 + X) * V + 1 = V + V := by
    rw [Matrix.add_mul, Matrix.one_mul, hXV]; abel
  have hq : (V + V) * ((2⁻¹ : ℂ) • (1 - X)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  refine ⟨?_, ?_, ?_⟩
  · have ha : (1 + Xᴴ) * H = H * (1 - X) := by
      have e : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
      rw [Matrix.add_mul, Matrix.one_mul, e, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    have hb : H * (1 + X) = (1 - Xᴴ) * H := by
      have e : H * X = -(Xᴴ * H) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hX)
      rw [Matrix.mul_add, Matrix.mul_one, e, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg]
    have hc : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by noncomm_ring
    have hW : Vᴴ * (1 - Xᴴ) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] at e
    calc ((1 + X) * V)ᴴ * H * ((1 + X) * V)
        = Vᴴ * (((1 + Xᴴ) * H) * ((1 + X) * V)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * (((1 - X) * (1 + X)) * V)) := by rw [ha]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * ((1 + X) * ((1 - X) * V))) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = (Vᴴ * (1 - Xᴴ)) * H := by
          rw [h1, Matrix.mul_one, hb]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hW, Matrix.one_mul]
  · rw [hg1]; exact isUnit_of_mul_one hq
  · rw [hg1, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : ((1 + X) * V - 1) * (1 - X) = X + X := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.one_mul]; abel
    rw [e, half_double]

theorem bwd {H g : Matrix n n ℂ} (hg : gᴴ * H * g = H) (hu : IsUnit (g + 1)) :
    ((g - 1) * (g + 1)⁻¹)ᴴ * H + H * ((g - 1) * (g + 1)⁻¹) = 0 ∧ IsUnit (1 - (g - 1) * (g + 1)⁻¹) ∧
      (1 + (g - 1) * (g + 1)⁻¹) * (1 - (g - 1) * (g + 1)⁻¹)⁻¹ = g := by
  set P := (g + 1)⁻¹ with hP
  have h1 : (g + 1) * P = 1 := mul_inv_of_isUnit hu
  have h2 : P * (g + 1) = 1 := inv_mul_of_isUnit hu
  have hgP : g * P = 1 - P := by
    have e := h1
    rw [Matrix.add_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hX : (g - 1) * P = 1 - P - P := by rw [Matrix.sub_mul, Matrix.one_mul, hgP]
  have hOne : (1 : Matrix n n ℂ) - (1 - P - P) = P + P := by abel
  have hq : (P + P) * ((2⁻¹ : ℂ) • (g + 1)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · have hQ : Pᴴ * (gᴴ + 1) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one] at e
    have hm : H * (g + 1) + (gᴴ + 1) * H = (gᴴ + 1) * H * (g + 1) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hg]; abel
    have key : Pᴴ * H + H * P = H := by
      calc Pᴴ * H + H * P = Pᴴ * (H * ((g + 1) * P)) + (Pᴴ * (gᴴ + 1)) * (H * P) := by
            rw [h1, hQ, Matrix.mul_one, Matrix.one_mul]
        _ = Pᴴ * ((H * (g + 1) + (gᴴ + 1) * H) * P) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (Pᴴ * (gᴴ + 1)) * H * ((g + 1) * P) := by rw [hm]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hQ, h1, Matrix.one_mul, Matrix.mul_one]
    have key' : Pᴴ * H = H - H * P := eq_sub_of_add_eq key
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, key']
    abel
  · rw [hOne]; exact isUnit_of_mul_one hq
  · rw [hOne, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : (1 + (1 - P - P)) * (g + 1) = g + g := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [e, half_double]

end UnitInverseArithmetic

theorem cayley_algebraic_holds : CayAlg := by
  intro k r
  refine ⟨fun X hX hu => ?_, fun g hg hu => ?_⟩
  · exact UnitInverseArithmetic.fwd hX hu
  · exact UnitInverseArithmetic.bwd hg hu

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CayleySmoothnessHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def MC (m : ℕ) : Type := Matrix (Fin m) (Fin m) ℂ

noncomputable instance instNRMC (m : ℕ) : NormedRing (MC m) := Matrix.linftyOpNormedRing

noncomputable instance instNAMC (m : ℕ) : NormedAlgebra ℝ (MC m) := Matrix.linftyOpNormedAlgebra

instance instFDMC (m : ℕ) : FiniteDimensional ℝ (MC m) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin m) (Fin m) ℂ))

instance instCSMC (m : ℕ) : CompleteSpace (MC m) := FiniteDimensional.complete ℝ (MC m)

def toMC (m : ℕ) : Matrix (Fin m) (Fin m) ℂ ≃L[ℝ] MC m :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.refl ℝ (Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℝ] MC m)

def cayMC {m : ℕ} (g₀ X : MC m) : MC m := g₀ * ((1 + X) * Ring.inverse (1 - X))

def cinvMC {m : ℕ} (a Y : MC m) : MC m := (a * Y - 1) * Ring.inverse (a * Y + 1)

theorem cay_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun X : B.Mat k r => g₀ * cay X) = fun X => (toMC _).symm (cayMC (toMC _ g₀) (toMC _ X)) := by
  funext X
  show g₀ * ((1 + X) * (1 - X)⁻¹) = g₀ * ((1 + X) * Ring.inverse (1 - X))
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem cayInv_eq_MC {k r : ℕ} (g₀ : B.Mat k r) :
    (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) = fun m => (toMC _).symm (cinvMC (toMC _ g₀⁻¹) (toMC _ m)) := by
  funext m
  show (g₀⁻¹ * m - 1) * (g₀⁻¹ * m + 1)⁻¹ = (g₀⁻¹ * m - 1) * Ring.inverse (g₀⁻¹ * m + 1)
  rw [Matrix.nonsing_inv_eq_ringInverse (g₀⁻¹ * m + 1)]

theorem cayMC_contDiffAt {m : ℕ} (g₀ X : MC m) (hX : IsUnit (1 - X)) : ContDiffAt ℝ ∞ (cayMC g₀) X := by
  obtain ⟨u, hu⟩ := hX
  have h1 : ContDiffAt ℝ ∞ (fun Y : MC m => Ring.inverse (1 - Y)) X := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp X (contDiffAt_const.sub contDiffAt_id)
  exact contDiffAt_const.mul ((contDiffAt_const.add contDiffAt_id).mul h1)

theorem cinvMC_contDiffAt {m : ℕ} (a Y : MC m) (hY : IsUnit (a * Y + 1)) : ContDiffAt ℝ ∞ (cinvMC a) Y := by
  obtain ⟨u, hu⟩ := hY
  have h1 : ContDiffAt ℝ ∞ (fun Z : MC m => Ring.inverse (a * Z + 1)) Y := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) u
    rw [hu] at this
    exact this.comp Y ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  exact ((contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const).mul h1

theorem cayley_smoothness_holds : CaySmooth := by
  intro k r g₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      (continuous_const.sub continuous_id)).preimage (toMC _).continuous
  · exact ((Units.isOpen (R := MC (2 * r + k + 1))).preimage
      ((continuous_const.mul continuous_id).add continuous_const)).preimage (toMC _).continuous
  · rw [cay_eq_MC g₀]
    intro X hX
    have hX' : IsUnit (1 - toMC _ X) := hX
    exact ((toMC _).symm.contDiff.contDiffAt.comp X
      ((cayMC_contDiffAt (toMC _ g₀) _ hX').comp X (toMC _).contDiff.contDiffAt)).contDiffWithinAt
  · rw [cayInv_eq_MC g₀]
    intro m hm
    have hm' : IsUnit (toMC _ g₀⁻¹ * toMC _ m + 1) := hm
    exact ((toMC _).symm.contDiff.contDiffAt.comp m
      ((cinvMC_contDiffAt (toMC _ g₀⁻¹) _ hm').comp m (toMC _).contDiff.contDiffAt)).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftTypeActionHolds
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace LeftTypeActionHermitianCurvature

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} {D : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)} {i : Fin (r + 1)} {mm : ℕ∞}

theorem mem_left (hD : IsDom k r z z' i D) {g h : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hh : h ∈ UWset k r z) : h * g ∈ Glev k r i ∩ D := by
  have := Qx8.dom_mem hD hg hh (Qx8.nlev_one _) (Qx8.uw_one z') (Qx8.nlev_one _)
  simpa using this

theorem J_left (hπ : IsCRepOn (UWset k r z) π) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D) {g h : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) (hh : h ∈ UWset k r z) : J (h * g) = (π h).comp (J g) := by
  have e1 := hJ.2.2.2 g hg 1 (Qx8.uw_one z) 1 (Qx8.uw_one z')
  have e2 := hJ.2.2.2 g hg h hh 1 (Qx8.uw_one z')
  rw [Matrix.one_mul, Matrix.mul_one, hπ.1] at e1
  rw [Matrix.mul_one] at e2
  have e3 : (1 : Wp →L[ℂ] Wp).comp ((J g).comp (π' 1)) = (J g).comp (π' 1) := ContinuousLinearMap.id_comp _
  rw [e3] at e1
  rw [e2, ← e1]

theorem ld_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {X : Mx k r} (hX : QrD.InLieW k r z X)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : LdV X F g = (B.comp (QrD.dOp π X)).comp (J g) := by
  have h := QrD.dOp_hasDeriv hπ hc hX
  let L : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wp Wp B).comp ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (J g))
  have h2 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have h3 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      (L.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    rw [hF _ (mem_left hD hg (QrD.exp_uw hX t)), J_left hπ hJ hg (QrD.exp_uw hX t)]
    rfl
  unfold LdV
  rw [h3]
  exact h2.deriv

theorem lz_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    {F : Mx k r → (Wq →L[ℂ] Wp)} {B : Wp →L[ℂ] Wp}
    (hF : ∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) {Z : Mx k r}
    (h1 : QrD.InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : QrD.InLieW k r z (hpart2 (Hpk k r) Z))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    LZ (Hpk k r) Z F g = (B.comp (QrD.ecOp π Z)).comp (J g) := by
  unfold LZ QrD.ecOp
  rw [ld_left hD hπ hc hJ hF h1 hg, ld_left hD hπ hc hJ hF h2 hg]
  ext v
  simp

theorem fold_left (hD : IsDom k r z z' i D) (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) (hJ : J ∈ Gr.FFlM mm k r z z' π π' i D)
    (L : List (ℂ × Mx k r))
    (hL : ∀ p ∈ L, QrD.InLieW k r z (hpart1 (Hpk k r) p.2) ∧ QrD.InLieW k r z (hpart2 (Hpk k r) p.2)) :
    ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (B : Wp →L[ℂ] Wp), (∀ g ∈ Glev k r i ∩ D, F g = B.comp (J g)) →
      ∀ g ∈ Glev k r i ∩ D, ∀ v,
        (L.map fun p => fun y : Mx k r → (Wq →L[ℂ] Wp) => p.1 • y + LZ (Hpk k r) p.2 y).foldl (fun h T => T h) F g v =
          B ((L.map fun p => fun y : Wp => p.1 • y + EcRep (Hpk k r) π p.2 y).foldr (fun T h => T h) (J g v)) := by
  induction L with
  | nil =>
    intro F B hF g hg v
    simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
    rw [hF g hg]
    rfl
  | cons p L ih =>
    intro F B hF g hg v
    have hp := hL p (by simp)
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons]
    rw [ih (fun q hq => hL q (by simp [hq])) (p.1 • F + LZ (Hpk k r) p.2 F) (p.1 • B + B.comp (QrD.ecOp π p.2))
      (fun x hx => by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [lz_left hD hπ hc hJ hF hp.1 hp.2 hx, hF x hx]
        ext v
        simp) g hg v, QrD.ecRep_eq hπ hc hp.1 hp.2]
    simp

end LeftTypeActionHermitianCurvature

theorem left_type_action_holds : LeftTypeAction0 := by
  intro Wp Wq _ _ _ _ _ k r m z z' π π' D mm _ _ hD hπ hc J hJ g hg Bs hB w v
  unfold capLft capRep qmFrev qmF
  simp only [Finset.sum_apply, Pi.smul_apply, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have e1 := LeftTypeActionHermitianCurvature.fold_left hD hπ hc hJ
    (List.ofFn fun j : Fin m => ((if σ j = j then w - ((j : ℕ) : ℂ) else 0 : ℂ), unitB (Hpk k r) Bs (σ j) j))
    (by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨j, rfl⟩ := hp
      exact QrD.frame_lie hB (σ j) j) J 1 (fun x _ => (ContinuousLinearMap.id_comp _).symm) g hg v
  simp only [List.map_ofFn, Function.comp_def, ite_smul, zero_smul] at e1
  simp only [id]
  rw [e1]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupVectorSpace
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ClassicalToWeakSolution
open scoped ContDiff
open MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

section ctw

variable {d : ℕ}

theorem ctw_pdc_append (l₁ l₂ : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    pdc (l₁ ++ l₂) f = pdc l₁ (pdc l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, pdc, ih]

theorem ctw_contDiffOn_pdc {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (m n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length + m ≤ n →
      ContDiffOn ℝ m (pdc l f) U
  | [], m, n, f, hf, hl => hf.of_le (by simp only [List.length_nil, zero_add] at hl; exact_mod_cast hl)
  | i :: l, m, n, f, hf, hl => by
      have ih := ctw_contDiffOn_pdc hU l (m + 1) n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact (ih.fderiv_of_isOpen hU (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

theorem ctw_pdc_congr {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (f g : (Fin d → ℝ) → ℂ), Set.EqOn f g U → Set.EqOn (pdc l f) (pdc l g) U
  | [], _, _, h => h
  | i :: l, f, g, h => by
      intro x hx
      have ih := ctw_pdc_congr hU l f g h
      simp only [pdc]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)]

theorem ctw_swap {U : Set (Fin d → ℝ)} (hU : IsOpen U) {g : (Fin d → ℝ) → ℂ} (hg : ContDiffOn ℝ 2 g U)
    {x : Fin d → ℝ} (hx : x ∈ U) (v w : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hga : ContDiffAt ℝ 2 g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hga.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hga.isSymmSndFDerivAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp [hs w v]

theorem ctw_pdc_perm {U : Set (Fin d → ℝ)} (hU : IsOpen U) {l₁ l₂ : List (Fin d)} (hp : l₁.Perm l₂) :
    ∀ (n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l₁.length ≤ n →
      Set.EqOn (pdc l₁ f) (pdc l₂ f) U := by
  induction hp with
  | nil => intro n f _ _; exact Set.eqOn_refl _ _
  | @cons a m₁ m₂ hp ih =>
      intro n f hf hl
      have h := ih n f hf (by simp only [List.length_cons] at hl; omega)
      have e1 := ctw_pdc_append [a] m₁ f
      have e2 := ctw_pdc_append [a] m₂ f
      simp only [List.singleton_append] at e1 e2
      rw [e1, e2]
      exact ctw_pdc_congr hU [a] _ _ h
  | swap a b l =>
      intro n f hf hl x hx
      have hg : ContDiffOn ℝ 2 (pdc l f) U :=
        ctw_contDiffOn_pdc hU l 2 n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact ctw_swap hU hg hx _ _
  | trans h₁ _ ih₁ ih₂ =>
      intro n f hf hl
      exact (ih₁ n f hf hl).trans (ih₂ n f hf (h₁.length_eq ▸ hl))

theorem ctw_integrable {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F G : (Fin d → ℝ) → ℂ}
    (hF : ContinuousOn F U) (hG : Continuous G) (hGc : HasCompactSupport G) (hGU : tsupport G ⊆ U) :
    Integrable (fun x => F x * G x) := by
  have hc : Continuous (fun x => F x * G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hF.continuousAt (hU.mem_nhds hx)).mul hG.continuousAt
    · have h0 : G =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hGU h))
      have h1 : (fun x => F x * G x) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
      exact continuousAt_const.congr h1.symm
  have hcs : HasCompactSupport (F * G) := hGc.mul_left
  exact hc.integrable_of_hasCompactSupport hcs

theorem ctw_tsupport_pdc (l : List (Fin d)) (ψ : (Fin d → ℝ) → ℂ) : tsupport (pdc l ψ) ⊆ tsupport ψ := by
  induction l with
  | nil => exact subset_rfl
  | cons i l ih =>
      refine subset_trans ?_ ((tsupport_fderiv_subset ℝ).trans ih)
      refine closure_mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      apply hx
      simp only [pdc, h, zero_apply]

theorem ctw_contDiff_pdc (l : List (Fin d)) {ψ : (Fin d → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (pdc l ψ) := by
  induction l with
  | nil => exact hψ
  | cons i l ih =>
      simp only [pdc]
      exact contDiff_infty.2 fun n =>
        ((contDiff_infty.1 ih (n + 1)).fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem ctw_ibp {U : Set (Fin d → ℝ)} (hU : IsOpen U) (l : List (Fin d)) :
    ∀ (n : ℕ) (f ψ : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length ≤ n → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, f x * pdc l ψ x = (-1 : ℂ) ^ l.length * ∫ x, pdc l.reverse f x * ψ x := by
  induction l with
  | nil => intro n f ψ _ _ _ _ _; simp [pdc]
  | cons i l ih =>
      intro n f ψ hf hl hψ hψc hψU
      have hl' : l.length + 1 ≤ n := by simpa using hl
      have hgs : ContDiff ℝ ∞ (pdc l ψ) := ctw_contDiff_pdc l hψ
      have hgt : tsupport (pdc l ψ) ⊆ tsupport ψ := ctw_tsupport_pdc l ψ
      have hgc : HasCompactSupport (pdc l ψ) := hψc.mono' ((subset_tsupport _).trans hgt)
      have hg's : ContDiff ℝ ∞ (pdc (i :: l) ψ) := ctw_contDiff_pdc (i :: l) hψ
      have hg't : tsupport (pdc (i :: l) ψ) ⊆ tsupport ψ := ctw_tsupport_pdc (i :: l) ψ
      have hg'c : HasCompactSupport (pdc (i :: l) ψ) := hψc.mono' ((subset_tsupport _).trans hg't)
      have hf1 : ContDiffOn ℝ ((n - 1 : ℕ)) (pdc [i] f) U :=
        ctw_contDiffOn_pdc hU [i] (n - 1) n f hf (by simp only [List.length_cons, List.length_nil]; omega)
      have hf0 : ContinuousOn (pdc [i] f) U :=
        (ctw_contDiffOn_pdc hU [i] 0 n f hf (by simp only [List.length_cons, List.length_nil]; omega)).continuousOn
      have hstep : ∫ x, f x * pdc (i :: l) ψ x = -∫ x, pdc [i] f x * pdc l ψ x := by
        have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
          (f := f) (g := pdc l ψ) (v := (Pi.single i 1 : Fin d → ℝ))
          (ctw_integrable hU hf0 hgs.continuous hgc (hgt.trans hψU))
          (ctw_integrable hU hf.continuousOn hg's.continuous hg'c (hg't.trans hψU))
          (ctw_integrable hU hf.continuousOn hgs.continuous hgc (hgt.trans hψU))
          (fun x hx => (hf.contDiffAt (hU.mem_nhds (hψU (hgt hx)))).differentiableAt
            (by exact_mod_cast (show n ≠ 0 by omega)))
          (fun x _ => hgs.differentiable (by simp) x)
        exact h
      rw [hstep, ih (n - 1) (pdc [i] f) ψ hf1 (by omega) hψ hψc hψU, List.reverse_cons, ctw_pdc_append,
        List.length_cons, pow_succ]
      ring

theorem ctw_smooth_mul {U : Set (Fin d → ℝ)} (hU : IsOpen U) {a φ : (Fin d → ℝ) → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => a y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (ha.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have h0 : φ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))
    have h1 : (fun y => a y * φ y) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

end ctw

theorem classical_to_weak_solution : ClassToWeak := by
  intro d N P U u hU ha hord hu hPu φ hφ hφc hφU
  have hφ0 : ∀ x, x ∉ U → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
  have hψ : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ContDiff ℝ ∞ (fun y => P.a k w y * φ y) ∧ HasCompactSupport (fun y => P.a k w y * φ y) ∧
        tsupport (fun y => P.a k w y * φ y) ⊆ U := fun k w =>
    ⟨ctw_smooth_mul hU (ha k w) hφ hφU, hφc.mul_left, tsupport_mul_subset_right.trans hφU⟩
  have hk : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), (List.ofFn w).length ≤ N := fun k w => by
    rw [List.length_ofFn]; have := k.isLt; omega
  have hint : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)) :=
    fun k w => by
      obtain ⟨h1, h2, h3⟩ := hψ k w
      refine ctw_integrable hU hu.continuousOn (continuous_const.mul (ctw_contDiff_pdc _ h1).continuous)
        ((h2.mono' ((subset_tsupport _).trans (ctw_tsupport_pdc _ _))).mul_left)
        (tsupport_mul_subset_right.trans ((ctw_tsupport_pdc _ _).trans h3))
  have hint2 : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => P.a k w x * pdc (List.ofFn w) u x * φ x) := fun k w =>
    ctw_integrable hU (((ha k w).continuousOn).mul
      (ctw_contDiffOn_pdc hU (List.ofFn w) 0 N u hu (by simpa using hk k w)).continuousOn) hφ.continuous hφc hφU
  have hterm : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
    intro k w
    obtain ⟨h1, h2, h3⟩ := hψ k w
    have hI := ctw_ibp hU (List.ofFn w) N u _ hu (hk k w) h1 h2 h3
    have hperm := ctw_pdc_perm hU (List.reverse_perm (List.ofFn w)) N u hu
      (by rw [List.length_reverse]; exact hk k w)
    calc ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)
        = (-1 : ℂ) ^ (k : ℕ) * ∫ x, u x * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x := by
          rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ∫ x, pdc (List.ofFn w).reverse u x * (P.a k w x * φ x) := by
          rw [hI, List.length_ofFn, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
      _ = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
          congr 1; funext x
          by_cases hx : x ∈ U
          · rw [hperm hx]; ring
          · simp [hφ0 x hx]
  have hsplit : (fun x => u x * P.tr φ x) = fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
      u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) := by
    funext x; simp only [SOp.tr, Finset.mul_sum]
  have hinner : ∀ k : Fin (P.ord + 1),
      ∫ x, ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x := fun k => by
    rw [integral_finsetSum _ (fun w _ => hint k w), integral_finsetSum _ (fun w _ => hint2 k w)]
    exact Finset.sum_congr rfl (fun w _ => hterm k w)
  rw [hsplit, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint k w)),
    Finset.sum_congr rfl (fun k _ => hinner k),
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint2 k w))]
  have h0 : (fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x) =
      fun _ => (0 : ℂ) := by
    funext x
    have e : ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x =
        P.app u x * φ x := by simp only [SOp.app, Finset.sum_mul]
    rw [e]
    by_cases hx : x ∈ U
    · rw [hPu x hx, zero_mul]
    · rw [hφ0 x hx, mul_zero]
  rw [h0, integral_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_chart_holds : GChart := gChart_of lie_basis_holds cayley_algebraic_holds group_vector_space cayley_smoothness_holds

theorem unitary_capelli_holds : UCap := uCap_of positive_domain_is_domain right_type_action_holds left_type_action_holds

theorem jfSmoothBuilt_of_rest (hN : NDiff) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hE : ChartEqs) (hR : EllRegW) :
    JfSmoothBuilt :=
  jfSmoothBuilt_of_leaves hN unitary_capelli_holds hP hC group_chart_holds hE classical_to_weak_solution hR JfS.symbol_nilpotent_holds lie_stabilizer_splitting

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_of_coefficients_holds : SmoothOfCoeffs := by
  intro k r E _ _ _ Dm J h g₀ hg₀
  let b := Module.finBasis ℂ E
  let ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    exact ((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const
  · intro g hg hgG
    have hg' := Set.mem_iInter.1 hg
    conv_lhs => rw [← b.sum_repr (J g)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hJF i g (hg' i) hgG]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NilpotentDerivative
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem nd_deriv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : ℝ → ℂ) (v : E) :
    deriv (fun t => φ t • v) 0 = deriv φ 0 • v := by
  by_cases hφ : DifferentiableAt ℝ φ 0
  · exact deriv_smul_const hφ v
  by_cases hv : v = 0
  · simp [hv]
  rw [deriv_zero_of_not_differentiableAt hφ, zero_smul]
  apply deriv_zero_of_not_differentiableAt
  intro hd
  apply hφ
  obtain ⟨ℓ, -, hℓv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  have h1 : DifferentiableAt ℝ (fun t => ℓ (φ t • v)) 0 :=
    (ℓ.restrictScalars ℝ).differentiableAt.comp 0 hd
  have hn : ℓ v ≠ 0 := by
    rw [hℓv]; exact RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have h2 : φ = fun t => ℓ (φ t • v) * (ℓ v)⁻¹ := by
    funext t
    rw [map_smul, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  rw [h2]
  exact h1.mul_const _

theorem nd_exp_mem {k r : ℕ} {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Q.Nlev k r 0 :=
  ⟨hX t, (hX t).1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem nd_om_mem {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z' :=
  ⟨⟨hg.1, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩

theorem nilpotent_derivative : NDiff := by
  intro k r Wp Wq _ _ _ _ D m J hJ
  obtain ⟨_, hL, hR, _⟩ := hJ
  constructor
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    have e : (fun t : ℝ => J (g * NormedSpace.exp ((t : ℂ) • X))) =
        fun t : ℝ => psi k r D.z' cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hR g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]
  · intro X hX
    refine ⟨deriv (fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X))) 0, fun g hg => ?_⟩
    show deriv (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) 0 = _
    have e : (fun t : ℝ => J (NormedSpace.exp ((t : ℂ) • X) * g)) =
        fun t : ℝ => psi k r D.z cStd (NormedSpace.exp ((t : ℂ) • X)) • J g :=
      funext fun t => hL g (nd_om_mem hg) _ (nd_exp_mem hX t)
    rw [e, nd_deriv_smul_const]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem jfSmoothBuilt_of_chart (hE : ChartEqs) (hR : EllRegW) : JfSmoothBuilt :=
  jfSmoothBuilt_of_rest nilpotent_derivative group_equations_post_holds smooth_of_coefficients_holds hE hR

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

namespace Formalism.FourierDecayAlt.P.CutMP

end Formalism.FourierDecayAlt.P.CutMP
