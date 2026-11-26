module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatLinkPoints
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

theorem exists_coord_fibres : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n
  have hfd : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨laminf, hinf⟩ := GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdInf F
  choose lam hlam using GlobalTheory.CompanionTheory.SW.StdEx.exists_isStdV F
  have hB : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) _ b laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ
    (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M)
    (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) (hWi n M) (hHi n)
  have hfV : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      ∃ fib : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n →
        Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E),
      IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M)
        (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) fib := fun v => by
    have := PI.VolStabS.secondCountable_Fv F v
    have := PI.VolStabS.locallyCompact_Fv F v
    have hBv : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) := ⟨rfl⟩
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) _ b (lam v) (hlam v).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hWv n M) (hHv n)
  choose m hm using hfV
  exact ⟨_, b, laminf, lam, minf, m, hinf, hlam, hminf, hm⟩

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalizationStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tamagawa_measure_normalization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartz
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WSum

theorem mul_mem_schwartzA : ∀ (D : D7) (θ : InfFam D) (m n : ℕ) (q : (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ), q.HasTemperateGrowth → ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → (fun x => q (fun τ i j => compAt θ τ x i j) * φ x) ∈ schwartzA θ m n := by
  intro D θ m n q hq φ hφ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine Submodule.subset_span ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) hq f, g, hg, ?_⟩
    funext x
    simp [mul_assoc]
    exact mul_left_comm _ _ _
  | zero =>
    convert (schwartzA θ m n).zero_mem using 1
    funext x
    simp
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    have := (schwartzA θ m n).add_mem h₁ h₂
    convert this using 1
    funext x
    simp [mul_add]
  | smul c Φ _ h =>
    have := (schwartzA θ m n).smul_mem c h
    convert this using 1
    funext x
    simp [mul_left_comm]

end GlobalTheory.CompanionTheory.WSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperateMultiplierPreservesSchwartzStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.temperate_multiplier_preserves_schwartz : ∀ (D : D7) (θ : InfFam D) (m n : ℕ) (q : (D.what₂.Tau → Fin m → Fin n → ℂ) → ℂ), q.HasTemperateGrowth → ∀ φ : Mx D m n → ℂ, φ ∈ schwartzA θ m n → (fun x => q (fun τ i j => compAt θ τ x i j) * φ x) ∈ schwartzA θ m n := by
  first | exact @GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA | exact GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2Bounded
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.CuspForms

theorem memL2_and_bounded_of_normalised : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  intro hB E _ _ _ a μ _ _ π hπ φ hφ
  have hc := π.cusp φ hφ
  obtain ⟨C, hC⟩ := hB.of_invariant hc (hπ φ hφ)
  exact ⟨memL2_of_isAutForm hc.1 (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC), C, hC⟩

end GlobalTheory.CompanionTheory.CuspForms
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedCuspFormL2BoundedStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_cusp_form_L2_bounded : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 ∧ ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | exact GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised | (intros; apply GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct ComplexConjugate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsCoord (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
    (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph Θ ∧ (∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) ∧
    (∀ x w, Θ ((1 : Ainf F) ⊗ₜ[F] x) w = τ w x) ∧
    ∀ z w, ((e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w : ℝ) : ℂ) = Θ z w + conj (Θ z w)

def tupC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n M : ℕ} (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    InfinitePlace F → Fin n → Fin M → ℂ :=
  fun w a i => Θ (X a i) w

def matC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) : Matrix (Fin n) (Fin n) ℂ :=
  fun a c => Θ (b a c) w

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Eop_add_conjugate (τ : E →+* ℂ) (i : Fin a) :
    Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  simp only [Eop, e1, e2, map_neg]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (1 + 1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) (1 : ℂ) := fun τ => by
    unfold atEmb
    split_ifs <;> simp
  funext w
  simp only [e, Finset.sum_apply, Pi.single_apply, Pi.add_apply, Pi.one_apply]
  simp only [eq_comm (a := w)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    IsTotallyComplex.mult_eq]
  norm_num

theorem sum_Eop_diag (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  have hs : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i i = ∑ τ : E →+* ℂ, Eop τ i i :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (fun τ : E →+* ℂ => star_star τ))
      (fun τ => Eop τ i i)
  have h : (∑ τ : E →+* ℂ, Eop τ i i) + ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 + lieS E a i i 1 := by
    nth_rw 2 [← hs]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conjugate τ i, ← map_sum,
      sum_atEmb_one, map_add]
  have h2 : (2 : ℂ) • (∑ τ : E →+* ℂ, Eop τ i i) = (2 : ℂ) • lieS E a i i 1 := by
    rw [two_smul, two_smul, h]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem lie_oneL_eq_sum_Eop (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop_diag i]
  simp only [lieS_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  have hm : ∑ i : Fin a, Matrix.single i i (1 : Cinf E) = 1 := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp [Matrix.single_apply]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  congr 1
  exact (congrArg Matrix.of.symm hm).symm

end GlobalTheory.CompanionTheory.ClozelLie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTraceStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_central_element_trace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  exact @GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliTrace

open Polynomial Formalism.REAL GroundTheory.BlockD.FourierDecayAlt.GaugeExists

theorem coeff_prod_lin {A : Type} [Ring A] (l : List A) (k : ℕ) (hk : k + 1 = l.length) :
    ((l.map fun b => (X + C b : A[X])).prod).coeff k = l.sum := by
  have h := prod_linear l.length (fun i => l.get i)
  have e : (List.ofFn fun i : Fin l.length => (X + C (l.get i) : A[X])) = l.map fun b => (X + C b : A[X]) := by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  rw [e] at h
  rw [h.2.2 k hk]
  conv_rhs => rw [← List.ofFn_get l, List.sum_ofFn]

theorem coeff_eq_zero_of_forall {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ) (w : ℕ → V)
    (h : ∀ u : ℂ, ∑ j ∈ Finset.range N, u ^ j • w j = 0) (i : ℕ) (hi : i < N) : w i = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  have hP : (∑ j ∈ Finset.range N, C (f (w j)) * X ^ j : ℂ[X]) = 0 := by
    refine Polynomial.funext fun u => ?_
    have := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p : ℂ[X] => p.coeff i) hP
  rw [finsetSum_coeff, Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hji
    simp [coeff_C_mul_X_pow, Ne.symm hji]
  · simp [hi]

section Gen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evU_prod_lin (l : List ℂ) (c v : ℂ) :
    evU v (((l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).map fun b => (X + C b)).prod) =
      algebraMap ℂ (Module.End ℂ V) (l.map (v - c + ·)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    congr 1
    simp only [evU_apply, eval₂_add, eval₂_X, eval₂_C, RingHom.id_apply, ← map_add (f := _)]
    congr 1
    ring

theorem sum_map_lin (l : List ℂ) (c : ℂ) :
    (l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c)).sum =
      algebraMap ℂ (Module.End ℂ V) (l.sum - l.length * c) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, ← map_add (f := _)]
    congr 1
    push_cast
    ring

theorem trace_of_qdet {n : ℕ} (Eo : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : List ℂ)
    (hl : l.length = n + 1) (φ : V)
    (h : ∀ v : ℂ, qdet Eo v φ = (l.map (v - (n : ℂ) / 2 + ·)).prod • φ) :
    (∑ i, Eo i i) φ = l.sum • φ := by
  set c : ℂ := (n : ℂ) / 2 with hc
  set L : List (Module.End ℂ V) := l.map fun x => algebraMap ℂ (Module.End ℂ V) (x - c) with hL
  set R : (Module.End ℂ V)[X] := (L.map fun b => (X + C b)).prod with hR
  set D : (Module.End ℂ V)[X] := qdetPoly Eo - R with hD
  have hev : ∀ v, (evU v D) φ = 0 := fun v => by
    rw [hD, map_sub, evU_qdetPoly, hR, hL, evU_prod_lin, LinearMap.sub_apply, h, Module.algebraMap_end_apply,
      sub_self]
  have hsum : ∀ v : ℂ, ∑ j ∈ Finset.range (D.natDegree + 1 + (n + 1)), v ^ j • (D.coeff j) φ = 0 := fun v => by
    have := hev v
    rw [evU_apply, eval₂_eq_sum_range' _ (show D.natDegree < D.natDegree + 1 + (n + 1) by omega),
      LinearMap.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_pow, RingHom.id_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have h0 := coeff_eq_zero_of_forall _ (fun j => (D.coeff j) φ) hsum n (by omega)
  have hq : (qdetPoly Eo).coeff n = ∑ k, Eo k k - algebraMap ℂ _ (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_qdetPoly_top Eo n (by omega), (prod_linear (n + 1) _).2.2 n rfl, Finset.sum_sub_distrib, ← map_sum,
      sum_fin_cast]
  have hr : R.coeff n = algebraMap ℂ _ (l.sum - l.length * c) := by
    rw [hR, coeff_prod_lin L n (by simp [hL, hl]), hL, sum_map_lin]
  simp only [hD, coeff_sub, hq, hr] at h0
  have hs : (∑ k, Eo k k) - algebraMap ℂ (Module.End ℂ V) (((n + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - 1) / 2) -
      algebraMap ℂ _ (l.sum - l.length * c) = (∑ k, Eo k k) - algebraMap ℂ _ l.sum := by
    rw [sub_sub, ← map_add (f := _)]
    congr 2
    rw [hl, hc]
    push_cast
    ring
  rw [hs, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h0
  exact h0

end Gen

theorem trace_Eop_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  intro E _ _ _ a π τ m hm φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases a with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CapelliTrace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSumStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_operator_eigenvalue_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | exact GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | (intros; apply GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsAsm

section Compl

variable {K : Type} [Field K]

theorem exists_isCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (hc : LinearIndependent K c) :
    ∃ a : Matrix (Fin n) (Fin n) K, IsCompl c a := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hrW : Module.finrank K W = r := by
    rw [hW, finrank_span_eq_card hc, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hWW'
  rw [hrW, Module.finrank_fin_fun] at hsum
  set m := Module.finrank K W' with hm
  have hn : n = r + m := hsum.symm
  let bW : Module.Basis (Fin m) K W' := Module.finBasisOfFinrankEq K W' hm.symm
  let d : Fin m → (Fin n → K) := fun j => (bW j : Fin n → K)
  have hd : LinearIndependent K d :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span K (Set.range c)) (Submodule.span K (Set.range d)) := by
    refine hWW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hv : LinearIndependent K (Sum.elim c d) := hc.sum_type hd hdisj
  let e : Fin n ≃ Fin r ⊕ Fin m := (finCongr hn).trans finSumFinEquiv.symm
  refine ⟨fun i => Sum.elim c d (e i), ?_, ?_⟩
  · have hli : LinearIndependent K (fun i => Sum.elim c d (e i)) := hv.comp e e.injective
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · intro i hi
    have he : e i = Sum.inl ⟨i, hi⟩ := by
      have : finCongr hn i = Fin.castAdd m ⟨i, hi⟩ := Fin.ext rfl
      simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]
    change Sum.elim c d (e i) = c ⟨i, hi⟩
    rw [he]
    rfl

end Compl

variable {D : D7} {n : ℕ}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sg_sg (D : D7) (x : D.host.E) : sg D (sg D x) = x := by
  show star (star x) = x
  exact star_star x

theorem mat_mul' (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_inv_of (x : G D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (hg : IsUnit g.det)
    (h : mat x = g.map (incA D)) : mat x⁻¹ = g⁻¹.map (incA D) := by
  have h1 : mat x⁻¹ = (mat x)⁻¹ := by
    simp only [mat, map_inv, Matrix.coe_units_inv]
  rw [h1, h]
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul g hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mk_eq_iff_siegel (hR : RatPts) (x y : GF D n) {gx gy : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (hx : IsUnit gx.det) (mx : mat x.1 = gx.map (incA D)) (my : mat y.1 = gy.map (incA D)) :
    mk ((P D n).subgroupOf (GF D n)) x = mk ((P D n).subgroupOf (GF D n)) y ↔ IsSiegelP (gy * gx⁻¹) := by
  have hmem : y.1 * x.1⁻¹ ∈ GF D n := mul_mem y.2 (inv_mem x.2)
  have hmat : mat (y.1 * x.1⁻¹) = (gy * gx⁻¹).map (incA D) := by
    rw [mat_mul', mat_inv_of x.1 hx mx, my, Matrix.map_mul]
  rw [← (hR D n).2.2 _ hmem _ hmat]
  show Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSiegelParabolic_one (K : Type) [Field K] (n : ℕ) : IsSiegelP (1 : Matrix (Fin (n + n)) (Fin (n + n)) K) := by
  unfold IsSiegelP
  intro i j
  exact Matrix.one_apply_ne (finSumFinEquiv.injective.ne Sum.inr_ne_inl)

theorem eisCells_of : Bruhat → RatPts → PInv → Term2 → EisCells := by
  intro hBr hRat hPInv hT2 D n V ψ χ θ μ ω hS Φ hconv μr hμr c hc
  classical
  have ha : ∀ U : Submodule D.host.E (Fin n → D.host.E), ∃ a, IsCompl (c U) a :=
    fun U => exists_isCompl (c U) (hc U).1
  choose a haU using ha
  obtain ⟨hU, huniq⟩ := hBr D.host.E (sg D) (sg_sg D) two_ne_zero n c hc a haU
  have hq : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      ∃ γ ∈ GF D n, mat γ = (repMat (sg D) q.2.1 (a q.1)).map (incA D) :=
    fun q => (hRat D n).2.1 _ (hU q.1 q.2.1 q.2.2).1 (hU q.1 q.2.1 q.2.2).2
  choose γ hγGF hγmat using hq
  have hdet : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      IsUnit (repMat (sg D) q.2.1 (a q.1)).det := fun q => (hU q.1 q.2.1 q.2.2).1
  let f : ((U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U)) →
      GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun q => mk ((P D n).subgroupOf (GF D n)) ⟨γ q, hγGF q⟩
  have hinj : Function.Injective f := by
    intro q q' hqq
    have h1 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q.2.1 (a q.1))⁻¹) :=
      (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ ⟨γ q', hγGF q'⟩ (hdet q) (hγmat q) (hγmat q')).mp hqq
    have h2 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q'.2.1 (a q'.1))⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (hdet q')]
      exact isSiegelParabolic_one _ n
    exact (huniq _ (hdet q') (hU q'.1 q'.2.1 q'.2.2).2).unique h1 h2
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨g, hg, hgu, hgm⟩ := (hRat D n).1 _ (Quotient.out z).2
    obtain ⟨q, hqs, -⟩ := huniq g hg hgu
    refine ⟨q, ?_⟩
    rw [← Quotient.out_eq z]
    exact (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ (Quotient.out z) (hdet q) (hγmat q) hgm).mpr hqs
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hrle : ∀ U : Submodule D.host.E (Fin n → D.host.E), Module.finrank D.host.E U ≤ n := fun U =>
    (Submodule.finrank_le U).trans_eq (Module.finrank_fin_fun _)
  have hsum : Summable (GlobalTheory.Eis.term (P D n) (GF D n) (fun γ => ((ω γ) Φ).1 0) 1) := Summable.of_norm hconv
  have h3 := (e.hasSum_iff).mpr hsum.hasSum
  unfold GlobalTheory.Eis.cosetSum
  convert h3 using 1
  funext q
  have hrel : (⟨γ q, hγGF q⟩ : GF D n) * (Quotient.out (e q))⁻¹ ∈ (P D n).subgroupOf (GF D n) := by
    have h0 : Quotient.mk _ (Quotient.out (e q)) = Quotient.mk _ (⟨γ q, hγGF q⟩ : GF D n) :=
      Quotient.out_eq (f q)
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have hp : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ ∈ (P D n ⊓ GF D n : Subgroup (G D n)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, (GF D n).mul_mem (Quotient.out (e q)).2 ((GF D n).inv_mem (hγGF q))⟩
    have h2 : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ =
        (γ q * ((Quotient.out (e q) : GF D n) : G D n)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [h2]
    exact (P D n).inv_mem hrel
  have hw' := hPInv D n V ψ χ θ μ ω hS Φ _ hp (γ q)
  simp only [inv_mul_cancel_right] at hw'
  simp only [Function.comp_apply, GlobalTheory.Eis.term, mul_one]
  rw [hw']
  exact (hT2 D n V ψ χ θ μ ω hS Φ _ (hrle q.1) (μr _) (hμr _) (c q.1) (a q.1) (haU q.1) q.2
    (γ q) (hγGF q) (hγmat q)).symm

end GlobalTheory.CompanionTheory.EisCellsAsm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecompositionStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_cells_decomposition : PositivityTheory.GramSchwartzFunctions.EC.Bruhat → PositivityTheory.GramSchwartzFunctions.EC.RatPts → PositivityTheory.GramSchwartzFunctions.EC.PInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 → PositivityTheory.GramSchwartzFunctions.EisCells := by
  first | exact @GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | exact GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of | (intros; apply GlobalTheory.CompanionTheory.EisCellsAsm.eisCells_of <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.UnitaryBC PositivityTheory.PRW.GKD

namespace GlobalTheory.CompanionTheory.TwistNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem val_expId (ω : HChar E) (t : ℝ) :
    ((ω.1 (GlobalTheory.DiscChar.expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
  refine (chiInf_expU ω _).trans (congrArg _ ?_)
  rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
  simp

theorem isNormalised_rank_zero (π : CuspSub E 0) : IsNormalised π := fun φ _ t g => by
  rw [Subsingleton.elim (splitCentre E 0 t * g) g]

theorem isNormalised_twist {π : CuspSub E a} {ω ν : HChar E} (hω : π.HasCentral ω)
    (hν : ∀ t : ℝ, ((chiDet a ν (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (-(t * dchi ω 1))) :
    IsNormalised (π.twist ν) := by
  rintro _ ⟨ψ, hψ, rfl⟩ t g
  change ψ.1 (splitCentre E a t * g) * (chiDet a ν (splitCentre E a t * g) : ℂˣ) = ψ.1 g * (chiDet a ν g : ℂˣ)
  have h1 : ψ.1 (splitCentre E a t * g) = Complex.exp (t * dchi ω 1) * ψ.1 g := by
    rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar, hω.apply hψ]
    exact congrArg (· * ψ.1 g) (val_expId ω t)
  rw [h1, map_mul, Units.val_mul, hν, mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem exists_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a),
    ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  intro E _ _ _ a π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨π, 1, isNormalised_rank_zero π, π.twist_one.symm⟩
  · obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
    refine ⟨π.twist ν, ν⁻¹, isNormalised_twist hω hν, ?_⟩
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

end GlobalTheory.CompanionTheory.TwistNorm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalisedStatement
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_eq_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a), ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  first | exact @GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | exact GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised | (intros; apply GlobalTheory.CompanionTheory.TwistNorm.exists_twist_normalised <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRank

theorem isCompactOperator_repOp_Rcusp_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E 0 → ℂ) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  have := SpecModel.finiteDimensional_zero μ
  have : FiniteDimensional ℂ (L2cusp μ) := inferInstance
  have : ProperSpace (L2cusp μ) := FiniteDimensional.proper ℂ _
  exact isCompactOperator_of_locallyCompactSpace_rng _

end GlobalTheory.CompanionTheory.CuspRank
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner
open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) := Measure.haar
    have : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
    have htransfer := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := htransfer
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep (K := E) (n := a) ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompactStatement
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f) := by
  first | exact @GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | exact GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | (intros; apply GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.Clozel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def scalarCurve (s : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (s : ℂ))

theorem scalarCurve_zero : scalarCurve E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 :=
    Units.ext (funext fun _ => by simp [expU])
  rw [scalarCurve, h, map_one]

theorem hasDerivAt_scalarCurve :
    HasDerivAt (fun s => toL (scalarCurve E a s).val) (oneL E a) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro w
  by_cases h : i = j
  · subst h
    have e : (fun s : ℝ => toL (scalarCurve E a s).val i i w) = fun s : ℝ => Complex.exp (s : ℂ) := by
      funext s
      simp [scalarCurve, toL, expU, Matrix.scalar_apply]
    have d : HasDerivAt (fun s : ℝ => Complex.exp (s : ℂ)) 1 0 := by
      simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    have o : oneL E a i i w = 1 := by simp [oneL, toL]
    rw [e, o]
    exact d
  · have e : (fun s : ℝ => toL (scalarCurve E a s).val i j w) = fun _ : ℝ => 0 := by
      funext s
      simp [scalarCurve, toL, Matrix.scalar_apply, h]
    have o : oneL E a i j w = 0 := by simp [oneL, toL, h]
    rw [e, o]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem eigen_along_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ),
    lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a),
      φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  intro E _ _ _ a φ c hφ t g
  set f : ℝ → ℂ := fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) with hf
  have hd : ∀ u, HasDerivAt f (c * f u) u := by
    intro u
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (scalarCurve E a) (oneL E a)
      scalarCurve_zero hasDerivAt_scalarCurve
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * f u := by
      have := congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
      simpa [hf] using this
    rw [h2] at h1
    have h3 : HasDerivAt (fun x : ℝ => φ.1 ((g * GlobalTheory.UnitaryBC.splitCentre E a u) * infGL E a (scalarCurve E a (x - u))))
        (c * f u) u := by
      have h0 : u - u = (0 : ℝ) := sub_self u
      exact HasDerivAt.comp_sub_const u u (by rw [h0]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e : GlobalTheory.UnitaryBC.splitCentre E a x =
        GlobalTheory.UnitaryBC.splitCentre E a u * infGL E a (scalarCurve E a (x - u)) := by
      have := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
      rw [add_sub_cancel] at this
      exact this
    simp only [hf, e, mul_assoc]
  have hP : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v)
      (Complex.exp (-c * u) * (-c) * f u + Complex.exp (-c * u) * (c * f u)) u := by
    intro u
    have h0 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact h0.cexp.mul (hd u)
  have hconst : ∀ u : ℝ, Complex.exp (-c * u) * f u = Complex.exp (-c * (0 : ℝ)) * f 0 := by
    refine fun u => is_const_of_deriv_eq_zero (f := fun v : ℝ => Complex.exp (-c * v) * f v)
      (fun x => (hP x).differentiableAt) (fun x => ?_) u 0
    rw [(hP x).deriv]
    ring
  have h0 : f 0 = φ.1 g := by
    simp [hf, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  have ht := hconst t
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0] at ht
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]
  change f t = _
  rw [← ht, ← mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.CompanionTheory.Clozel

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponentialStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_eigen_exponential : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (c : ℂ), lie E a (oneL E a) φ = c • φ → ∀ (t : ℝ) (g : GA E a), φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = Complex.exp (c * t) * φ.1 g := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | exact GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre | (intros; apply GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExists
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteConjugacyExistsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_conjugacy_exists : PositivityTheory.Rg.BcB.G8.Fin.CjEx := by
  first | exact @GlobalTheory.CompanionTheory.CjEx.cjEx | exact GlobalTheory.CompanionTheory.CjEx.cjEx | (intros; apply GlobalTheory.CompanionTheory.CjEx.cjEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem EopV_val (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (i j : Fin a) (φ : π.V) : (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  simp [EopV, Eop, lieS_apply, CuspSub.op_val, act]

end GlobalTheory.CompanionTheory.ClozelPurity

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEqStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_operator_vector_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (i j : Fin a) (φ : π.V), (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.ClozelPurity.EopV_val | exact GlobalTheory.CompanionTheory.ClozelPurity.EopV_val | (intros; apply GlobalTheory.CompanionTheory.ClozelPurity.EopV_val <;> assumption)
end
end
