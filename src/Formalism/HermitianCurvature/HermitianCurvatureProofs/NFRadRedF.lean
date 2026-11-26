module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedLocSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionOperator
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedL
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedR
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LocLog : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g

variable {k r : ℕ}

def lieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

def dOpL {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    lieW k r z →ₗ[ℝ] (Wp →L[ℂ] Wp) where
  toFun X := dOp π (X : Q.Mx k r)
  map_add' X Y := (P.differential_operator_linear Wp k r z π hπ X Y X.2 Y.2).1
  map_smul' s X := by
    have h := (P.differential_operator_linear Wp k r z π hπ X X X.2 X.2).2 s
    show dOp π (s • (X : Q.Mx k r)) = s • dOp π (X : Q.Mx k r)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact h

private lemma rep_exp_smul_eq_exp_dOp {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) {X : Q.Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (t • dOp π X) := by
  set A := dOp π X with hA
  set f : ℝ → (Wp →L[ℂ] Wp) := fun s => π (NormedSpace.exp ((s : ℂ) • X)) with hf
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    simp only [hf]
    rw [show ((s + u : ℝ) : ℂ) • X = (s : ℂ) • X + (u : ℂ) • X by push_cast; rw [add_smul],
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _),
      hπ.2 _ (exp_uw hX s) _ (exp_uw hX u), ContinuousLinearMap.mul_def]
  have h0 : HasDerivAt f A 0 := dOp_hasDeriv hπ hc hX
  have hd : ∀ s, HasDerivAt f (f s * A) s := by
    intro s
    have h2 : HasDerivAt (fun u => f s * f u) (f s * A) (s - s) := by
      rw [sub_self]
      exact h0.const_mul (f s)
    have h1 : HasDerivAt (fun u => f s * f (u - s)) (f s * A) s := HasDerivAt.comp_sub_const s s h2
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show f u = f s * f (u - s)
    rw [← hmul]
    congr 1
    ring
  have hg : ∀ s, HasDerivAt (fun u => f u * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hasDerivAt_exp_smul_const (-A) s)
    have hcomm : Commute A (NormedSpace.exp (s • -A)) :=
      ((Commute.refl A).neg_right.smul_right s).exp_right
    have h0' : f s * A * NormedSpace.exp (s • -A) + f s * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, hcomm.eq, mul_neg, mul_neg, add_neg_cancel]
    exact this.congr_deriv h0'
  have hconst : ∀ s, f s * NormedSpace.exp (s • -A) = 1 := by
    intro s
    have hdiff : Differentiable ℝ (fun u => f u * NormedSpace.exp (u • -A)) := fun u => (hg u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hg u).deriv) s 0
    rw [this]
    simp only [hf, zero_smul, Complex.ofReal_zero, NormedSpace.exp_zero, mul_one, hπ.1]
  have hk : ∀ s, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) 0 s := by
    intro s
    have := (hasDerivAt_exp_smul_const (-A) s).mul (hasDerivAt_exp_smul_const A s)
    have hcomm2 : Commute A (NormedSpace.exp (s • A)) := ((Commute.refl A).smul_right s).exp_right
    have h0' : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
        NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
      rw [mul_assoc, neg_mul, hcomm2.eq, mul_neg, neg_add_cancel]
    exact this.congr_deriv h0'
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hdiff : Differentiable ℝ (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) :=
      fun u => (hk u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hk u).deriv) t 0
    rw [this]
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  calc f t = f t * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst t, one_mul]

private lemma contDiff_exp_hermitian_curvature {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    ContDiff ℝ ∞ (NormedSpace.exp : A → A) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem repSmooth_of (hLL : LocLog) : NFRadRedS.RepSmooth := by
  unfold NFRadRedS.RepSmooth
  intro Wp _ _ _ k r z π hz hTz hπ hc h₀ hh₀
  obtain ⟨O, hO, h1O, Λ, hΛ, hΛe⟩ := hLL k r z hz hTz
  have hrep : Qr.IsRepW k r z π := ⟨hπ, hc⟩
  have hdetH : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hdet0 : IsUnit h₀.det := ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hdetH).2.2 h₀ hh₀.1).1
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieW k r z)
  let T : Q.Mx k r →ₗ[ℝ] (Wp →L[ℂ] Wp) := (dOpL z π hrep).comp (Submodule.linearProjOfIsCompl _ q hq)
  have hT1 : ∀ Y, InLieW k r z Y → T Y = dOp π Y := by
    intro Y hY
    have hp := Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
    show dOpL z π hrep (Submodule.linearProjOfIsCompl _ q hq Y) = dOp π Y
    rw [show Submodule.linearProjOfIsCompl _ q hq Y = ⟨Y, hY⟩ from hp]
    rfl
  let Tc := LinearMap.toContinuousLinearMap T
  let Lm : Q.Mx k r →ₗ[ℝ] Q.Mx k r :=
    { toFun := fun h => h₀⁻¹ * h
      map_add' := fun a b => Matrix.mul_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mul_smul] }
  let Lc := LinearMap.toContinuousLinearMap Lm
  have hV : IsOpen {h : Q.Mx k r | h₀⁻¹ * h ∈ O} := hO.preimage Lc.continuous
  refine ⟨{h : Q.Mx k r | h₀⁻¹ * h ∈ O}, hV, ?_, fun h => π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))), ?_, ?_⟩
  · show h₀⁻¹ * h₀ ∈ O
    rw [Matrix.nonsing_inv_mul h₀ hdet0]
    exact h1O
  · have h1 : ContDiffOn ℝ ∞ (fun h => Λ (Lc h)) {h : Q.Mx k r | h₀⁻¹ * h ∈ O} :=
      hΛ.comp Lc.contDiff.contDiffOn (fun h hh => hh)
    exact contDiffOn_const.mul (contDiff_exp_hermitian_curvature.comp_contDiffOn (Tc.contDiff.comp_contDiffOn h1))
  · intro h hV' hU
    have hg : h₀⁻¹ * h ∈ UWset k r z := Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh₀) hU
    obtain ⟨hlie, hexp⟩ := hΛe _ hV' hg
    have hpi := rep_exp_smul_eq_exp_dOp hπ hc hlie 1
    simp only [Complex.ofReal_one, one_smul] at hpi
    rw [hexp] at hpi
    calc π h = π (h₀ * (h₀⁻¹ * h)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv h₀ hdet0, Matrix.one_mul]
      _ = (π h₀).comp (π (h₀⁻¹ * h)) := hπ.2 _ hh₀ _ hg
      _ = π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))) := by
          rw [ContinuousLinearMap.mul_def, hpi,
            show Tc (Λ (h₀⁻¹ * h)) = dOp π (Λ (h₀⁻¹ * h)) from hT1 _ hlie]

end Formalism.FourierDecayAlt.P.NFRadRedR

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth_of_log : NFRadRedR.LocLog → NFRadRedS.RepSmooth := fun h => NFRadRedR.repSmooth_of h

end Formalism.FourierDecayAlt.P
end
end

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

variable {k r : ℕ}

def cinv (g : Q.Mx k r) : Q.Mx k r := (g + 1)⁻¹ * (g - 1)

theorem cinv_one : cinv (1 : Q.Mx k r) = 0 := by
  simp [cinv]

theorem add_one_mul_cinv {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : (g + 1) * cinv g = g - 1 := by
  rw [cinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

theorem cinv_mul_add_one {g : Q.Mx k r} (hg : IsUnit (g + 1).det) : cinv g * (g + 1) = g - 1 := by
  rw [cinv, Matrix.mul_assoc, show (g - 1) * (g + 1) = (g + 1) * (g - 1) by noncomm_ring,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]

theorem cinv_inj {g₁ g₂ : Q.Mx k r} (h₁ : IsUnit (g₁ + 1).det) (h₂ : IsUnit (g₂ + 1).det)
    (he : cinv g₁ = cinv g₂) : g₁ = g₂ := by
  have k1 : g₁ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₁
    rw [add_mul, Matrix.one_mul] at h
    rw [mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have k2 : g₂ * (1 - cinv g₁) = 1 + cinv g₁ := by
    have h := add_one_mul_cinv h₂
    rw [add_mul, Matrix.one_mul] at h
    rw [he, mul_sub, mul_one, eq_sub_of_add_eq h]; abel
  have hL : ((1 / 2 : ℂ) • (g₁ + 1)) * (1 - cinv g₁) = 1 := by
    rw [Matrix.smul_mul, mul_sub, mul_one, add_one_mul_cinv h₁,
      show g₁ + 1 - (g₁ - 1) = (2 : ℂ) • (1 : Q.Mx k r) by rw [two_smul]; abel, smul_smul]
    norm_num
  have hR : (1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1)) = 1 := mul_eq_one_comm.mp hL
  calc g₁ = g₁ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [hR, mul_one]
    _ = g₂ * ((1 - cinv g₁) * ((1 / 2 : ℂ) • (g₁ + 1))) := by rw [← mul_assoc, k1, ← k2, mul_assoc]
    _ = g₂ := by rw [hR, mul_one]

theorem cinv_lie {z : Fin (2 * r + k + 1) → ℂ} {g : Q.Mx k r} (hg : g ∈ UWset k r z) (hu : IsUnit (g + 1).det) :
    InLieW k r z (cinv g) := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have fixv : ∀ v, g *ᵥ v = v → cinv g *ᵥ v = 0 := by
    intro v hv
    simp only [cinv]
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self, Matrix.mulVec_zero]
  refine ⟨⟨?_, fun a _ => ⟨fixv _ (hfix a).1, fixv _ (hfix a).2⟩⟩, fixv _ hz⟩
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hAH : IsUnit (g + 1)ᴴ.det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have e1 : (g + 1) * (g + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e2 : ((g + 1)ᴴ)⁻¹ * (g + 1)ᴴ = 1 := Matrix.nonsing_inv_mul _ hAH
  have hc : cinv g = (g - 1) * (g + 1)⁻¹ := by
    calc cinv g = cinv g * ((g + 1) * (g + 1)⁻¹) := by rw [e1, mul_one]
      _ = (g - 1) * (g + 1)⁻¹ := by rw [← mul_assoc, cinv_mul_add_one hu]
  have mid : (g - 1)ᴴ * Hpk k r * (g + 1) + (g + 1)ᴴ * Hpk k r * (g - 1) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
    have : (gᴴ - 1) * Hpk k r * (g + 1) + (gᴴ + 1) * Hpk k r * (g - 1) =
        (gᴴ * Hpk k r * g - Hpk k r) + (gᴴ * Hpk k r * g - Hpk k r) := by noncomm_ring
    rw [this, hU', sub_self, add_zero]
  have t1 : ((g + 1)ᴴ)⁻¹ * ((g - 1)ᴴ * Hpk k r * (g + 1)) * (g + 1)⁻¹ = ((g + 1)ᴴ)⁻¹ * (g - 1)ᴴ * Hpk k r := by
    simp only [Matrix.mul_assoc]; rw [e1, Matrix.mul_one]
  have t2 : ((g + 1)ᴴ)⁻¹ * ((g + 1)ᴴ * Hpk k r * (g - 1)) * (g + 1)⁻¹ = Hpk k r * ((g - 1) * (g + 1)⁻¹) := by
    simp only [← Matrix.mul_assoc]; rw [e2, Matrix.one_mul]
  rw [hc, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← t1, ← t2, ← add_mul, ← mul_add, mid,
    Matrix.mul_zero, Matrix.zero_mul]

end Formalism.FourierDecayAlt.P.NFRadRedL
end
end

open Matrix Filter Topology Set
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionUnitary

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD Formalism.FourierDecayAlt.P.NFRadRedL

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k r : ℕ}

theorem inv_eq_ring_inverse (A : Q.Mx k r) : A⁻¹ = Ring.inverse A := by
  first
    | exact Matrix.nonsing_inv_eq_ringInverse A
    | exact Matrix.nonsing_inv_eq_ring_inverse A

def lieU (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

theorem cinv_eq (g : Q.Mx k r) : cinv g = Ring.inverse (g + 1) * (g - 1) := by
  rw [cinv, inv_eq_ring_inverse]

theorem cinv_contDiffAt {g : Q.Mx k r} (hu : IsUnit (g + 1)) : ContDiffAt ℝ ∞ cinv g := by
  have h1 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => Ring.inverse (x + 1)) g := by
    obtain ⟨u, hu⟩ := hu
    have : ContDiffAt ℝ ∞ Ring.inverse (u : Q.Mx k r) := contDiffAt_ringInverse ℝ u
    rw [hu] at this
    exact this.comp g (contDiffAt_id.add contDiffAt_const)
  have h2 : ContDiffAt ℝ ∞ (fun x : Q.Mx k r => x - 1) g := contDiffAt_id.sub contDiffAt_const
  have : (cinv : Q.Mx k r → Q.Mx k r) = fun x => Ring.inverse (x + 1) * (x - 1) := funext cinv_eq
  rw [this]
  exact h1.mul h2

theorem two_mul_half : ((1 : Q.Mx k r) + 1) * ((1 / 2 : ℂ) • 1) = 1 := by
  rw [mul_smul_comm, mul_one, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

theorem half_mul_two : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (1 + 1) = 1 := by
  rw [smul_mul_assoc, one_mul, ← two_smul ℂ (1 : Q.Mx k r), smul_smul]
  norm_num

def twoU (k r : ℕ) : (Q.Mx k r)ˣ := ⟨1 + 1, (1 / 2 : ℂ) • 1, two_mul_half, half_mul_two⟩

theorem cinv_hasFDerivAt_one :
    HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r) (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1)) 1 := by
  have hinv : Ring.inverse ((1 : Q.Mx k r) + 1) = (1 / 2 : ℂ) • 1 := Ring.inverse_unit (twoU k r)
  have h1 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (twoU k r)).comp (1 : Q.Mx k r)
    ((hasFDerivAt_id (𝕜 := ℝ) (1 : Q.Mx k r)).add_const 1)
  have h2 : HasFDerivAt (fun x : Q.Mx k r => x - 1) (ContinuousLinearMap.id ℝ (Q.Mx k r)) 1 :=
    (hasFDerivAt_id (1 : Q.Mx k r)).sub_const 1
  have h3 := h1.mul' h2
  have hfun : (cinv : Q.Mx k r → Q.Mx k r) =
      (fun x : Q.Mx k r => Ring.inverse (id x + 1)) * (fun x : Q.Mx k r => x - 1) := by
    funext x; rw [cinv_eq]; rfl
  rw [hfun]
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp [hinv]
  change ((2 : ℂ)⁻¹ • (1 : Q.Mx k r)) * h = (2 : ℂ)⁻¹ • h
  rw [smul_mul_assoc, one_mul]

private theorem exp_mulVec_eq_self_of_mulVec_eq_zero {X : Q.Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (hv : X *ᵥ v = 0) :
    NormedSpace.exp X *ᵥ v = v := by
  let Lv : Q.Mx k r →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
  let Lc := LinearMap.toContinuousLinearMap Lv
  have hs : Summable (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • X ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) X
  have hpow : ∀ n : ℕ, (X ^ (n + 1)) *ᵥ v = 0 := fun n => by
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have key : Lc (∑' n : ℕ, ((n.factorial : ℂ))⁻¹ • X ^ n) =
      ∑' n : ℕ, Lc (((n.factorial : ℂ))⁻¹ • X ^ n) := Lc.map_tsum hs
  simp only [Lc, LinearMap.coe_toContinuousLinearMap', Lv, LinearMap.coe_mk, AddHom.coe_mk] at key
  rw [NormedSpace.exp_eq_tsum ℂ]
  simp only
  rw [key, tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [Matrix.smul_mulVec, hpow, smul_zero]

private theorem exp_mem_uwset_of_inLieW {z : Fin (2 * r + k + 1) → ℂ} {X : Q.Mx k r} (hX : InLieW k r z X) :
    NormedSpace.exp X ∈ UWset k r z := by
  obtain ⟨hX1, hX2⟩ := hX
  have h1 : (1 : Q.Mx k r) ∈ Glev k r (Fin.last r) := by
    simp [Glev, UH]
  have h := Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_lev h1 hX1 1
  simp only [Complex.ofReal_one, one_smul, mul_one, Glev, Set.mem_setOf_eq] at h
  simp only [UWset, Set.mem_setOf_eq]
  exact ⟨h.1, fun a => h.2 a (by simp), exp_mulVec_eq_self_of_mulVec_eq_zero hX2⟩

theorem locLogOp (z : Fin (2 * r + k + 1) → ℂ) :
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g := by
  classical

  let L := lieU k r z
  haveI : FiniteDimensional ℝ (Q.Mx k r) := inferInstance
  haveI : CompleteSpace L := (Submodule.complete_of_finiteDimensional L).completeSpace_coe
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective L.subtype (Submodule.ker_subtype L)
  let P : Q.Mx k r →L[ℝ] L := LinearMap.toContinuousLinearMap p
  have hP : ∀ Y : L, P (Y : Q.Mx k r) = Y := fun Y => by
    show p (L.subtype Y) = Y
    rw [← LinearMap.comp_apply, hp, LinearMap.id_apply]
  have hPmem : ∀ x, InLieW k r z x → (P x : Q.Mx k r) = x := fun x hx => by
    have := hP ⟨x, hx⟩
    rw [this]

  let Φ : L → L := fun Y => (2 : ℝ) • P (cinv (NormedSpace.exp (Y : Q.Mx k r)))
  have hu1 : IsUnit ((1 : Q.Mx k r) + 1) := ⟨twoU k r, rfl⟩
  have he0 : NormedSpace.exp ((0 : L) : Q.Mx k r) = 1 := by simp
  have hexp : ∀ x : Q.Mx k r, ContDiffAt ℝ ∞ (NormedSpace.exp : Q.Mx k r → Q.Mx k r) x :=
    fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hΦc : ∀ Y : L, IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) → ContDiffAt ℝ ∞ Φ Y := by
    intro Y hY
    have a1 : ContDiffAt ℝ ∞ (fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      (hexp _).comp Y L.subtypeL.contDiff.contDiffAt
    have a0 : ContDiffAt ℝ ∞ (cinv : Q.Mx k r → Q.Mx k r) (NormedSpace.exp (Y : Q.Mx k r)) :=
      cinv_contDiffAt (k := k) (r := r) hY
    have a2 : ContDiffAt ℝ ∞ ((cinv : Q.Mx k r → Q.Mx k r) ∘ fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y :=
      ContDiffAt.comp (g := (cinv : Q.Mx k r → Q.Mx k r)) (f := fun Y : L => NormedSpace.exp (Y : Q.Mx k r)) Y a0 a1
    exact (P.contDiff.contDiffAt.comp Y a2).const_smul (2 : ℝ)
  have hΦ0c : ContDiffAt ℝ ∞ Φ 0 := hΦc 0 (by rw [he0]; exact hu1)
  have hΦ0d : HasFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ L : L ≃L[ℝ] L) : L →L[ℝ] L) 0 := by
    have hE : HasFDerivAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r))
        ((1 : Q.Mx k r →L[ℝ] Q.Mx k r).comp L.subtypeL) 0 := by
      convert HasFDerivAt.comp_continuousLinearMap L.subtypeL (0 : L)
        (hasFDerivAt_exp_zero (𝕂 := ℝ)) using 1 <;> rfl
    have hC : HasFDerivAt (cinv : Q.Mx k r → Q.Mx k r)
        (ContinuousLinearMap.mul ℝ (Q.Mx k r) ((1 / 2 : ℂ) • 1))
        (NormedSpace.exp ((0 : L) : Q.Mx k r)) := by
      rw [he0]; exact cinv_hasFDerivAt_one
    have h := ((P.hasFDerivAt).comp (0 : L) (hC.comp (0 : L) hE)).const_smul (2 : ℝ)
    refine HasFDerivAt.congr_fderiv h ?_
    refine ContinuousLinearMap.ext fun Y => ?_
    have hh : ((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r) = (1 / 2 : ℝ) • (Y : Q.Mx k r) := by
      rw [smul_mul_assoc, one_mul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      norm_num
    change (2 : ℝ) • P (((1 / 2 : ℂ) • (1 : Q.Mx k r)) * (Y : Q.Mx k r)) = Y
    rw [hh, P.map_smul, hP, smul_smul]
    norm_num
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let f := ContDiffAt.toOpenPartialHomeomorph Φ hΦ0c hΦ0d hn
  have hfc : (f : L → L) = Φ := rfl

  have hU : ∀ᶠ Y : L in 𝓝 (0 : L), IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1) := by
    have hc : ContinuousAt (fun Y : L => NormedSpace.exp (Y : Q.Mx k r) + 1) 0 :=
      (((hexp _).continuousAt).comp L.subtypeL.continuous.continuousAt).add continuousAt_const
    have h0 : IsUnit (NormedSpace.exp ((0 : L) : Q.Mx k r) + 1) := by rw [he0]; exact hu1
    exact hc.eventually_mem (Units.isOpen.mem_nhds h0)
  have hD : ∀ᶠ Y : L in 𝓝 (0 : L), fderiv ℝ Φ Y ∈
      Set.range (ContinuousLinearEquiv.toContinuousLinearMap : (L ≃L[ℝ] L) → L →L[ℝ] L) := by
    have hcont : ContinuousAt (fderiv ℝ Φ) 0 := (hΦ0c.fderiv_right (m := 0) (by simp)).continuousAt
    exact hcont.eventually_mem (ContinuousLinearEquiv.isOpen.mem_nhds
      ⟨ContinuousLinearEquiv.refl ℝ L, hΦ0d.fderiv.symm⟩)
  obtain ⟨V, hVsub, hVo, hV0⟩ := eventually_nhds_iff.mp (hU.and hD)
  have hsym : ∀ a ∈ f.target ∩ f.symm ⁻¹' V, ContDiffAt ℝ ∞ f.symm a := by
    rintro a ⟨ha, haV⟩
    obtain ⟨hu, e, he⟩ := hVsub _ haV
    have hcd := hΦc _ hu
    have hd : HasFDerivAt Φ (e : L →L[ℝ] L) (f.symm a) := by
      rw [show (e : L →L[ℝ] L) = fderiv ℝ Φ (f.symm a) from he]
      exact (hcd.differentiableAt (by simp)).hasFDerivAt
    exact f.contDiffAt_symm ha (by rw [hfc]; exact hd) (by rw [hfc]; exact hcd)

  let w : Q.Mx k r → L := fun g => (2 : ℝ) • P (cinv g)
  have hw : ∀ g : Q.Mx k r, IsUnit (g + 1) → ContDiffAt ℝ ∞ w g := fun g hg =>
    ((P.contDiff.contDiffAt).comp g (cinv_contDiffAt (k := k) (r := r) hg)).const_smul (2 : ℝ)
  have hGU : IsOpen {g : Q.Mx k r | IsUnit (g + 1)} :=
    Units.isOpen.preimage (continuous_id.add continuous_const)
  have hT : IsOpen (f.target ∩ f.symm ⁻¹' V) := f.isOpen_inter_preimage_symm hVo
  have hwc : ContinuousOn w {g : Q.Mx k r | IsUnit (g + 1)} := fun g hg =>
    (hw g hg).continuousAt.continuousWithinAt
  have hΦ00 : Φ 0 = 0 := by simp [Φ, cinv_one]
  have hw1 : w 1 = 0 := by simp [w, cinv_one]
  refine ⟨{g : Q.Mx k r | IsUnit (g + 1)} ∩ w ⁻¹' (f.target ∩ f.symm ⁻¹' V),
    hwc.isOpen_inter_preimage hGU hT, ⟨hu1, ?_⟩, fun g => ((f.symm (w g) : L) : Q.Mx k r), ?_, ?_⟩
  · have h0t : Φ 0 ∈ f.target := ContDiffAt.image_mem_toOpenPartialHomeomorph_target hΦ0c hΦ0d hn
    have h0s : (0 : L) ∈ f.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hΦ0c hΦ0d hn
    rw [hΦ00] at h0t
    refine ⟨?_, ?_⟩
    · show w 1 ∈ f.target
      rw [hw1]; exact h0t
    · show f.symm (w 1) ∈ V
      rw [hw1, ← hΦ00, ← hfc, f.left_inv h0s]
      exact hV0
  · intro g hg
    exact (L.subtypeL.contDiff.contDiffAt.comp g ((hsym (w g) hg.2).comp g (hw g hg.1))).contDiffWithinAt
  · intro g hg hgU
    set Y := f.symm (w g) with hYdef
    have hY : InLieW k r z (Y : Q.Mx k r) := Y.2
    refine ⟨hY, ?_⟩
    obtain ⟨huY, -⟩ := hVsub _ hg.2.2
    have h1 : Φ Y = w g := f.right_inv hg.2.1
    have hdg : IsUnit (g + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hg.1
    have hdY : IsUnit (NormedSpace.exp (Y : Q.Mx k r) + 1).det := (Matrix.isUnit_iff_isUnit_det _).mp huY
    have h2 : P (cinv (NormedSpace.exp (Y : Q.Mx k r))) = P (cinv g) :=
      smul_right_injective L (two_ne_zero' ℝ) h1
    have h3 := congrArg Subtype.val h2
    rw [hPmem _ (cinv_lie (exp_mem_uwset_of_inLieW hY) hdY), hPmem _ (cinv_lie hgU hdg)] at h3
    exact cinv_inj hdY hdg h3

end Formalism.FourierDecayAlt.P.RadicalReductionUnitary
end
end

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

def MxOp (k r : ℕ) : Type := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

instance (k r : ℕ) : NormedRing (MxOp k r) := Matrix.linftyOpNormedRing

instance (k r : ℕ) : NormedAlgebra ℂ (MxOp k r) := Matrix.linftyOpNormedAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toOp (k r : ℕ) : Q.Mx k r ≃ₗ[ℝ] MxOp k r where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c • x : Q.Mx k r) = (c • (@id (MxOp k r) x))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c x, RCLike.real_smul_eq_coe_smul (K := ℂ) c (@id (MxOp k r) x)]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem locLog : NFRadRedR.LocLog := by
  intro k r z _ _
  obtain ⟨O, hO, h1, Λ, hΛ, hΛg⟩ := RadicalReductionUnitary.locLogOp (k := k) (r := r) z
  have hΛ' : ContDiffOn ℝ ∞ (fun x : MxOp k r => @id (MxOp k r) (Λ x)) (@id (Set (MxOp k r)) O) := hΛ
  have hO' : IsOpen (O : Set (Q.Mx k r)) := hO
  refine ⟨O, hO', h1, Λ, ?_, hΛg⟩
  have hL1 := (toOp k r).toContinuousLinearEquiv.toContinuousLinearMap.contDiff (n := ∞)
  have hL2 := (toOp k r).toContinuousLinearEquiv.symm.toContinuousLinearMap.contDiff (n := ∞)
  have h := hL2.comp_contDiffOn (hΛ'.comp (s := (O : Set (Q.Mx k r))) hL1.contDiffOn (fun x hx => hx))
  exact h.congr (fun x _ => rfl)

end Formalism.FourierDecayAlt.P.RadicalReductionOperator

namespace Formalism.FourierDecayAlt.P

theorem local_logarithm_unitary : NFRadRedR.LocLog := RadicalReductionOperator.locLog

end Formalism.FourierDecayAlt.P
end
end

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth : NFRadRedS.RepSmooth := representation_smooth_of_log local_logarithm_unitary

theorem radical_reduction_surjective : Formalism.FourierDecayAlt.NF.RadRedSurj :=
  radical_surjective_of_parts local_smooth_section representation_smooth

end Formalism.FourierDecayAlt.P
