module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.SmoothTranslate
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.ContDiffMulRight
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.Development
open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Deriv

end PI.PhMeasCore.UnitaryGroupMassFormula

end
end

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

theorem mul_mem_UH {n : ℕ} {Hm a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UH Hm) (hb : b ∈ UH Hm) :
    a * b ∈ UH Hm := by
  have ha' : aᴴ * Hm * a = Hm := ha
  have hb' : bᴴ * Hm * b = Hm := hb
  show (a * b)ᴴ * Hm * (a * b) = Hm
  calc (a * b)ᴴ * Hm * (a * b) = bᴴ * (aᴴ * Hm * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Hm := by rw [ha', hb']

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_matMul {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a => LinearMap.toContinuousLinearMap
          { toFun := fun b => a * b
            map_add' := fun b c => Matrix.mul_add a b c
            map_smul' := fun r b => by simp }
        map_add' := fun a b => by
          ext c : 1
          simp [Matrix.add_mul]
        map_smul' := fun r a => by
          ext c : 1
          simp }
  have h : ContDiff ℝ ∞ (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => L p.1 p.2) :=
    L.isBoundedBilinearMap.contDiff
  exact h

theorem contDiff_mulRight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * g) :=
  (@contDiff_matMul n).comp (contDiff_id.prodMk contDiff_const)

end Smooth

end PI.PhMeasCore.UnitaryGroupMassFormula

end
end

open Matrix
open scoped ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by
  have hw' : PI.PhMeasCore.SmoothOnH Hm (fun x => σ x w) := hw
  show PI.PhMeasCore.SmoothOnH Hm (fun x => σ x (σ g w))
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hFeq⟩ := hw' (g₀ * g) (mul_mem_UH (a := g₀) hg₀ hg)
  refine ⟨(fun x => x * g) ⁻¹' U, fun x => F (x * g),
    hU.preimage (contDiff_mulRight g).continuous, hmem, ?_, ?_⟩
  · exact hF.comp (contDiff_mulRight g).contDiffOn (fun x hx => hx)
  · intro x hx hxI
    have e : σ (x * g) w = F (x * g) := hFeq (x * g) hx (mul_mem_UH hxI hg)
    show σ x (σ g w) = F (x * g)
    rw [← e, hmul.2 x hxI g hg, ContinuousLinearMap.comp_apply]

end PI.PhMeasCore.UnitaryGroupMassFormula

end
end

noncomputable section

namespace Formalism.L2.SG.BesselSplit

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory Finset
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Period

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end Period

section Chain

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end Chain

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hPu : IsUnit P) (hPJ : Matrix.conjTranspose P * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) {a : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hJ : Formalism.REAL.Jm ε = Matrix.conjTranspose P⁻¹ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ := by
    rw [← hPJ]
    rw [show Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose P * Formalism.REAL.Jm ε * P) * P⁻¹ = Matrix.conjTranspose (P * P⁻¹) * Formalism.REAL.Jm ε * (P * P⁻¹) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hPP : Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have ha' : Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  calc Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = Matrix.conjTranspose P⁻¹ * Matrix.conjTranspose a * (Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹) * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * P) * a * P⁻¹ := by
        rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a) * P⁻¹ := by
        rw [hPP, h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hJ]

theorem mulOnUH_of_dsHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    PI.PhMeasCore.UnitaryGroupMassFormula.MulOnUH (Formalism.QuantumDeterminants.Hpk k r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨⟨hone, hmul⟩, -, -⟩ := hDS.2.2.1
  have conj : ∀ a : Mat k r, P⁻¹ * (P * a * P⁻¹) * P = a := fun a => by
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have mem : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * a * P⁻¹ ∈ UJset ε := fun a ha => conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH hPu hPJ ha
  refine ⟨?_, fun a ha b hb => ?_⟩
  · simpa [h1] using hone
  · have e := hmul _ (mem a ha) _ (mem b hb)
    have e3 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, h1, Matrix.one_mul]
    simp only [e3, conj] at e
    exact e

theorem smooth_translate_ds {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {w : H} (hw : w ∈ smoothVecs (k := k) (r := r) σ)
    {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : σ x w ∈ smoothVecs (k := k) (r := r) σ := by
  exact PI.PhMeasCore.UnitaryGroupMassFormula.smooth_translate (mulOnUH_of_dsHpk hσ) hw hx

end Smooth

section GGP

end GGP

end Formalism.L2.SG.BesselSplit
