module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAt
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjoint
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesParameterUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModel
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModel
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hDS hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hm : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    simpa [Set.compl_setOf] using this
  have key : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := hφ
    have := hc.aestronglyMeasurable (μ := νq) hm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}) hae] at this
  refine ⟨hae, key, fun a => ?_, fun l hl w hw => ?_⟩
  · exact (key ℝ (fun g => lenA k r z g a) (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · haveI : SecondCountableTopology Wp := by
      haveI : ProperSpace Wp := FiniteDimensional.proper ℂ Wp
      infer_instance
    exact key Wp (fun g => l (R.σ g w))
      (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hDS Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuotientMeasureAeMemAndMeasurableBesselModelStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  first | exact @GlobalTheory.quotMeas_ae_mem_and_measurable | exact GlobalTheory.quotMeas_ae_mem_and_measurable | (intros; apply GlobalTheory.quotMeas_ae_mem_and_measurable <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModule
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModule
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * (X * Y) * Q := by
    intro X Y
    calc (Q⁻¹ * X * Q) * (Q⁻¹ * Y * Q) = Q⁻¹ * X * (Q * Q⁻¹) * Y * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (X * Y) * Q := by
          rw [hQQ, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  rw [key, key, ← Matrix.sub_mul, ← Matrix.mul_sub]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst hbc hda
    simp [Matrix.single_mul_single_same, Matrix.mul_sub, Matrix.sub_mul]
  · subst hbc
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Matrix.mul_sub, Matrix.sub_mul]
  · subst hda
    simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Matrix.mul_sub, Matrix.sub_mul]
  · simp [Matrix.single_mul_single_of_ne, hbc, hda]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hR Q hQ
  obtain ⟨hsm, hlinv, hlinY, -, hcomm, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hzero : ∀ Y : Mx k r, R.dC Y 0 = 0 := by
    intro Y
    have h := hlinv Y 1 0 R.smSub.zero_mem 0 R.smSub.zero_mem
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := by
    intro v hv
    have h := hlinY 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z : Mx k r, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := by
    intro Y Z v hv
    have h := hlinY Z Y (-1) v hv
    rw [neg_one_smul, neg_add_eq_sub, neg_one_smul, neg_add_eq_sub] at h
    exact h
  let Em : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hsm _ v v.2⟩
      map_add' := fun v w => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) 1 v v.2 w w.2
        simpa using h
      map_smul' := fun c v => by
        apply Subtype.ext
        have h := hlinv (Q⁻¹ * Matrix.single a b 1 * Q) c v v.2 0 R.smSub.zero_mem
        simpa [hzero] using h }
  have hE : ∀ a b (v : R.smSub), ((Em a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v :=
    fun _ _ _ => rfl
  refine ⟨Em, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have hv : (v : R.H) ∈ R.sm := v.2
  have key := hcomm (Q⁻¹ * Matrix.single a b 1 * Q) (Q⁻¹ * Matrix.single c d 1 * Q) v hv
  rw [conj_single_comm Q hQ a b c d, hsub _ _ _ hv] at key
  split_ifs at key ⊢ <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE, LinearMap.zero_apply,
      Submodule.coe_zero, sub_zero, zero_sub, hY0 _ hv] at key ⊢ <;>
    exact key

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModuleStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnits
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnits
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hl : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have key : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hM : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ) = Q * Y * Q⁻¹ := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single (Q * Y * Q⁻¹)]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [key, hM]
  simp only [Matrix.mul_assoc, hl, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hl, Matrix.one_mul]

theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hr : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have e1 : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
    calc (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
        = Q⁻¹ * (Matrix.single a b (1 : ℂ) * ((Q * Q⁻¹) * Matrix.single c d (1 : ℂ))) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
          rw [hr, Matrix.one_mul]
  rw [e1]
  by_cases hbc : b = c
  · subst hbc
    simp [Matrix.single_mul_single_same]
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc (1 : ℂ)]
    simp [hbc]

theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hDG Q E hQ hE
  obtain ⟨-, -, hlinY, hLie, hbr, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDG
  have hv0 : ∀ v : R.smSub, (v : R.H) ∈ R.sm := fun v => v.2
  have hE' : ∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
      ((E a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v := hE
  have h0 : ∀ v : R.smSub, R.dC 0 (v : R.H) = 0 := fun v => by
    have := hlinY 0 0 1 v (hv0 v)
    simpa using this
  let f : R.smSub → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] R.H := fun v =>
    { toFun := fun Y => R.dC Y v
      map_add' := fun Y Z => by
        have := hlinY Y Z 1 v (hv0 v)
        simpa using this
      map_smul' := fun a Y => by
        have := hlinY Y 0 a v (hv0 v)
        simpa [h0 v] using this }
  have hsub : ∀ (Y Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (Y - Z) (v : R.H) = R.dC Y v - R.dC Z v := fun Y Z v => map_sub (f v) Y Z
  have hsm : ∀ (a : ℂ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (a • Y) (v : R.H) = a • R.dC Y v := fun a Y v => map_smul (f v) a Y
  have hexpP : ∀ (P Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsUnit P →
      (∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
        ((E a b v : R.smSub) : R.H) = R.dC (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v) →
      ∀ v : R.smSub, R.dC Y v = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro P Y hP hPE v
    calc R.dC Y v = f v Y := rfl
      _ = f v (∑ a, ∑ b, (P * Y * P⁻¹) a b • (P⁻¹ * Matrix.single a b (1 : ℂ) * P)) :=
          congrArg (f v) (conj_expand_units P Y hP)
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • f v (P⁻¹ * Matrix.single a b (1 : ℂ) * P) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_smul]
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
          simp only [hPE]
          rfl
  have hexp : ∀ (Y : Mx k r) (v : R.smSub),
      R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) :=
    fun Y v => hexpP Q Y hQ hE v
  have hGl : Formalism.REAL.GlRel E := by
    intro a b c d
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hb := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v (hv0 v)
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ] at hb
    have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
        R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v)
        - R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v) := by
      simp [hE']
    rw [lhs, hb, hsub, hsm, hsm]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, hE']
  refine ⟨hGl, hexp, fun X hX v => ?_⟩
  rw [← hLie X hX v (hv0 v)]
  exact hexp X v

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionExpandMatrixUnitsStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParameters
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensOrth

variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem hh_smul (Γ : Matrix ι ι ℂ) (R : Rep k r) (a b : ℂ) (x y : ι → R.H) :
    hh Γ R (fun c => a • x c) (fun c => b • y c) = a * star b * hh Γ R x y := by
  simp only [hh, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (x : ι → R.H) (y : κ → ι → R.H) :
    hh Γ R x (fun c => ∑ J, y J c) = ∑ J, hh Γ R x (y J) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem hh_star (Γ : Matrix ι ι ℂ) (hΓ : Γᴴ = Γ) (R : Rep k r) (x y : ι → R.H) :
    star (hh Γ R x y) = hh Γ R y x := by
  simp only [hh, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (Γ j i) = Γ i j := by
    have := congrFun (congrFun hΓ i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]
  congr 1
  exact inner_conj_symm _ _

theorem eq_zero_of_hh (Γ : Matrix ι ι ℂ) (hΓ : Γ * Γ = 1) (R : Rep k r) (x : ι → R.H)
    (h : hh Γ R x (fun c => ∑ j, Γ c j • x j) = 0) (c : ι) : x c = 0 := _root_.GlobalTheory.TensOrth.eq_zero_of_hh Γ hΓ R x h c

theorem SmMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have := hT.smul 0 0 R.smSub.zero_mem
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
theorem raw_scale {ρ : Mx k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (h : TensRaw ρ R RI io pr)
    (a : κ → ℂ) (ha : ∀ I, a I ≠ 0)
    (h1 : ∀ I c, SmMap (RI I) R (fun v => a I • io I c v))
    (h2 : ∀ I c, SmMap R (RI I) (fun v => (a I)⁻¹ • pr I c v)) :
    TensRaw ρ R RI (fun I c v => a I • io I c v) (fun I c v => (a I)⁻¹ • pr I c v) := by
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · intro I g hg y hy
    funext c
    have := congrFun (h.io_eq I g hg y hy) c
    simp only [act] at this ⊢
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  · intro I g hg x hx
    rw [← Finset.smul_sum, ← Finset.smul_sum, map_smul, h.pr_eq I g hg x hx]
  · intro x hx c
    rw [← h.sum_io_pr x hx c]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hm : ∑ d, pr I d (x d) ∈ (RI I).smSub :=
      Submodule.sum_mem _ fun d _ => (h.pr_sm I d).mem _ (hx d)
    rw [← Finset.smul_sum, (h.io_sm I c).smul _ _ hm, smul_smul, mul_inv_cancel₀ (ha I), one_smul]
  · intro I y hy
    conv_rhs => rw [← h.pr_io I y hy]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h.pr_sm I c).smul _ _ ((h.io_sm I c).mem _ hy), smul_smul, inv_mul_cancel₀ (ha I), one_smul]
  · intro I J hIJ y hy
    have : ∀ c, (a I)⁻¹ • pr I c (a J • io J c y) = ((a I)⁻¹ * a J) • pr I c (io J c y) := fun c => by
      rw [(h.pr_sm I c).smul _ _ ((h.io_sm J c).mem _ hy), smul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h.pr_io_ne I J hIJ y hy, smul_zero]

theorem tensH_of_raw : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hinj hF hT
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : PoulsenG := hH.2.2.2.2.2.1
  have hform := GlobalTheory.T.tensor_decomposition_parameters hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  have horth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm,
      hh Γ R (fun c => io I c y) (fun c => io J c y') = 0 := by
    intro I J hIJ
    rcases (hP k r ε _ _ _ _ (hRI I) (hRI J)).2 _ (hform I J) with h | ⟨U, hU⟩
    · exact h
    · exact absurd (hinj (GlobalTheory.T.discrete_series_parameter_unique hH k r ε _ _ _ _ (hRI I) (hRI J) U hU)) hIJ
  choose cI hc using fun I => (hP k r ε _ _ _ _ (hRI I) (hRI I)).1 _ (hform I I)
  have hunit : ∀ I, ∃ w ∈ (RI I).sm, ‖w‖ = 1 := fun I => by
    obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hRI I)
    exact ⟨w, h5 w (h7 w hwK), hw⟩
  have hreal : ∀ I, ((cI I).re : ℂ) = cI I := fun I => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have h1 := hc I w hw w hw
    have h2 := hh_star Γ hF.1 R (fun c => io I c w) (fun c => io I c w)
    rw [inner_self_eq_norm_sq_to_K, hn] at h1
    simp only [map_one, one_pow, mul_one] at h1
    rw [h1] at h2
    exact Complex.conj_eq_iff_re.1 h2
  have hne : ∀ I, cI I ≠ 0 := fun I h0 => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have hx : ∀ c, (∑ j, Γ c j • io I j w) ∈ R.smSub := fun c =>
      Submodule.sum_mem _ fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ hw)
    have hz : hh Γ R (fun c => io I c w) (fun c => ∑ j, Γ c j • io I j w) = 0 := by
      have e : (fun c => ∑ j, Γ c j • io I j w) =
          fun c => ∑ J, io J c (∑ e, pr J e (∑ j, Γ e j • io I j w)) :=
        funext fun c => (hT.sum_io_pr _ hx c).symm
      rw [e, hh_sum_right]
      refine Finset.sum_eq_zero fun J _ => ?_
      have hm : ∑ e, pr J e (∑ j, Γ e j • io I j w) ∈ (RI J).smSub :=
        Submodule.sum_mem _ fun e _ => (hT.pr_sm J e).mem _ (hx e)
      by_cases hIJ : I = J
      · subst hIJ
        have := hc I w hw _ hm
        rw [h0, zero_mul] at this
        exact this
      · exact horth I J hIJ w hw _ hm
    have h0' := eq_zero_of_hh Γ hF.2.1 R _ hz
    have h1 := hT.pr_io I w hw
    simp only [h0', SmMap_zero (hT.pr_sm I _), Finset.sum_const_zero] at h1
    rw [← h1, norm_zero] at hn
    exact zero_ne_one hn
  have hre : ∀ I, (cI I).re ≠ 0 := fun I h => hne I (by rw [← hreal I, h]; simp)
  have hsc : ∀ (m m' : Fin (2 * r + k + 1) → ℝ) (S S' : Rep k r), S.IsDG ε m → S'.IsDG ε m' →
      ∀ (T : S.H → S'.H) (a : ℂ), SmMap S S' T → SmMap S S' (fun v => a • T v) := by
    intro m m' S S' hS hS' T a h
    have := (GlobalTheory.T.smooth_maps_closure hK k r ε _ _ _ S S' S' hS hS' hS').2.2.1 T T (a - 1) h h
    simpa only [sub_smul, one_smul, sub_add_cancel] using this
  set a : κ → ℂ := fun I => (((Real.sqrt |(cI I).re|)⁻¹ : ℝ) : ℂ) with ha
  have hane : ∀ I, a I ≠ 0 := fun I => by
    simp only [ha, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hre I))).ne'
  refine ⟨fun I c v => a I • io I c v, fun I c v => (a I)⁻¹ • pr I c v,
    fun I => (cI I).re / |(cI I).re|, ⟨raw_scale hT a hane
      (fun I c => hsc _ _ _ _ (hRI I) hR _ _ (hT.io_sm I c))
      (fun I c => hsc _ _ _ _ hR (hRI I) _ _ (hT.pr_sm I c)), fun I => ?_, fun I y hy y' hy' => ?_,
      fun I J hIJ y hy y' hy' => ?_⟩⟩
  · rcases lt_or_gt_of_ne (hre I) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (hre I)]
    · left
      rw [abs_of_pos h, div_self (hre I)]
  · have h1 := hc I y hy y' hy'
    rw [hh_smul, h1, ← mul_assoc]
    congr 1
    have h2 : (Real.sqrt |(cI I).re|)⁻¹ * (Real.sqrt |(cI I).re|)⁻¹ * (cI I).re = (cI I).re / |(cI I).re| := by
      rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_inv_mul]
    rw [← h2]
    simp only [ha, RCLike.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hreal I]
  · rw [hh_smul, horth I J hIJ y hy y' hy', mul_zero]

end GlobalTheory.TensOrth
end
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionInjectiveParametersStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_decomposition_injective_parameters : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  first | exact @GlobalTheory.TensOrth.tensH_of_raw | exact GlobalTheory.TensOrth.tensH_of_raw | (intros; apply GlobalTheory.TensOrth.tensH_of_raw <;> assumption)
end Gp91
end
end
