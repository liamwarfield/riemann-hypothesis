module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.IwaAd

def AnisoOfRange : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), InRange V n →
    n + 2 ≤ V.rank ∨ ∀ x : Fin V.rank → D.host.E, HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x = 0 → x = 0

def WhitKAOfGenLt : Prop := PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt → DictKA → AnisoOfRange → WhitKA

end PositivityTheory.PfSWUS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.AnisoRange

theorem bddAbove_isotropic_dims {D : D7} (V : HSp D) :
    BddAbove {k | ∃ W : Submodule D.host.E V.V, Module.finrank D.host.E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, V.hT x y = 0} := by
  haveI := V.fd
  refine ⟨Module.finrank D.host.E V.V, ?_⟩
  rintro k ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

theorem one_le_wittIdx {D : D7} (V : HSp D) {v : V.V} (hv : v ≠ 0) (h : V.hT v v = 0) :
    1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  refine le_csSup (bddAbove_isotropic_dims V) ⟨Submodule.span D.host.E {v}, finrank_span_singleton hv, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [h]

theorem hT_coord {D : D7} (V : HSp D) (x : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm x) =
      HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x := by
  have hσ : ∀ a : D.host.E, ((D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) a = star a :=
    fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, HSpace.gram]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem anisoOfRange : PositivityTheory.PfSWUS.AnisoOfRange := by
  rintro D n V ⟨h1, -, h3⟩
  by_cases h : n + 2 ≤ V.rank
  · exact Or.inl h
  refine Or.inr fun x hx => ?_
  by_contra hne
  have hv : V.frame.equivFun.symm x ≠ 0 := fun h0 => hne ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 h0)
  have := one_le_wittIdx V hv ((hT_coord V x).trans hx)
  omega

end GlobalTheory.CompanionTheory.AnisoRange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRangeStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropy_of_range : PositivityTheory.PfSWUS.AnisoOfRange := by
  first | exact @GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | exact GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange | (intros; apply GlobalTheory.CompanionTheory.AnisoRange.anisoOfRange <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBound
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.DilPush

theorem push_dil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), MeasurableSet P → (∀ S : Set (Fv F v), MeasurableSet S → coordW (Fv F v) b lam 1 M (P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fv F v)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ ((c * ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam P c hP hbound u S hS
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI := hlam.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set Q : (Fin 1 → Fin M → Fv F v ⊗[F] E) → Fv F v := fun X => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hQ
  set D : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun X p k => (u : Fv F v ⊗[F] E) * X p k with hD
  set n : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hn
  have hn0 : n ≠ 0 := (u.isUnit.map (Algebra.norm (Fv F v))).ne_zero
  have hdil : ∀ X, Q (D X) = n * Q X := fun X => GlobalTheory.T.trace_gram_unit_scaling F E σ hσ M J hJ v u X
  set S' : Set (Fv F v) := (fun t => n * t) ⁻¹' S with hS'def
  have hmul : Measurable (fun t : Fv F v => n * t) := (continuous_const_mul n).measurable
  have hS' : MeasurableSet S' := hmul hS
  have hset : D '' P ∩ Q ⁻¹' S = D '' (P ∩ Q ⁻¹' S') := by
    ext Y
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hY⟩
      refine ⟨X, ⟨hX, ?_⟩, rfl⟩
      show n * Q X ∈ S
      rw [← hdil]
      exact hY
    · rintro ⟨X, ⟨hX, hXS⟩, rfl⟩
      refine ⟨⟨X, hX, rfl⟩, ?_⟩
      show Q (D X) ∈ S
      rw [hdil]
      exact hXS
  have hQc : Continuous Q := by
    have h1 : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
      PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)
    have h2 : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X 0 0 :=
      (continuous_apply_apply 0 0).comp (PI.VolStabS.continuous_gramR (Fv F v) σ J)
    exact continuous_const.mul (h1.comp h2)
  have hQm : Measurable Q := hQc.measurable
  have hlamS : lam S' = (‖n‖₊ : ℝ≥0∞)⁻¹ * lam S := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v n hn0 lam hlam.1
    have h2 := congrArg (fun μ : Measure (Fv F v) => μ S) h
    simp only [Measure.smul_apply] at h2
    rw [Measure.map_apply hmul hS] at h2
    rw [hS'def, h2, ENNReal.smul_def, smul_eq_mul]
    simp [ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hn0)]
  rw [hset, GlobalTheory.T.unit_scaling_rank_one_volume F E σ hσ M d b v lam hlam u _ (hP.inter (hQm hS'))]
  set a : ℝ≥0∞ := (‖n‖₊ : ℝ≥0∞) with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hn0
  have hat : a ≠ ⊤ := ENNReal.coe_ne_top
  have hpow : a ^ M = a ^ (M - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel hM]
  have haa : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hat
  calc a ^ M * coordW (Fv F v) b lam 1 M (P ∩ Q ⁻¹' S')
      ≤ a ^ M * ((c : ℝ≥0∞) * lam S') := by gcongr; exact hbound S' hS'
    _ = (c : ℝ≥0∞) * a ^ (M - 1) * (a * a⁻¹) * lam S := by rw [hlamS, hpow]; ring
    _ = ((c * ‖n‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by rw [haa, ha]; push_cast; ring

end GlobalTheory.CompanionTheory.WeilSiegel.DilPush
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBoundStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rank_one_volume_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), MeasurableSet P → (∀ S : Set (Fv F v), MeasurableSet S → coordW (Fv F v) b lam 1 M (P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fv F v)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ ((c * ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.DilPush.push_dil | exact GlobalTheory.CompanionTheory.WeilSiegel.DilPush.push_dil | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.DilPush.push_dil <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolValueAtFinsetSum
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem holValueAt_finset_sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (a : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) :
    HolValueAt (fun z => ∑ i ∈ T, f i z) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert i T hi ih =>
    have h := (a i (Finset.mem_insert_self i T)).add
      (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

end GlobalTheory.CompanionTheory.IwaAd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneral
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

theorem data_zero_of_data {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {ψ} {ι : Type} [Fintype ι] {θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν}
    (h : PositivityTheory.SiegelWeilFormula.Gen.Dat (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν) :
    PositivityTheory.SiegelWeilFormula.Gen.Dat0 (ι := ι) σ J T bs ψ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν :=
  { cm := h.cm, herm := h.herm, hT := h.hT, det := h.det, chr := h.chr, places := h.places,
    frames := h.frames, haar := h.haar, co := h.co, std := h.std, pure := h.pure, prod := h.prod,
    sdW := h.sdW, sdH := h.sdH }

theorem whitKAOfGenLt : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  intro hGen hDict hAn D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (data_zero_of_data hDat) hDat.lt (hAn D n V hR) False.elim
      ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    rw [one_mul] at h
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerMaximalCompactGeneralStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_maximal_compact_general : PositivityTheory.PfSWUS.WhitKAOfGenLt := by
  first | exact @GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | exact GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt | (intros; apply GlobalTheory.CompanionTheory.IwaAd.whitKAOfGenLt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNeg
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNeg
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusAdj

theorem conj_one_add {R : Type} [Ring R] (U A D Di : R) (h1 : D * Di = 1) (h2 : Di * D = 1) :
    D * (1 + (U - 1) * A) * Di = 1 + (D * U * Di - 1) * (D * A * Di) := by
  have k : D * U * Di * (D * A * Di) = D * (U * A) * Di := by
    calc D * U * Di * (D * A * Di) = D * U * (Di * D) * A * Di := by simp only [mul_assoc]
      _ = D * (U * A) * Di := by rw [h2]; simp only [mul_one, mul_assoc]
  calc D * (1 + (U - 1) * A) * Di = D * Di + (D * (U * A) * Di - D * A * Di) := by noncomm_ring
    _ = 1 + (D * U * Di * (D * A * Di) - D * A * Di) := by rw [h1, k]
    _ = 1 + (D * U * Di - 1) * (D * A * Di) := by noncomm_ring

theorem map_det_adj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (A u t D Di : Matrix (Fin n) (Fin n) R)
    (h1 : D * Di = 1) (h2 : Di * D = 1) (hS : D * (u.map σ)ᵀ * Di = t) :
    σ (1 + A * (u - 1)).det = (1 + (t - 1) * (D * (A.map σ)ᵀ * Di)).det := by
  have e1 : (σ.mapMatrix (1 + A * (u - 1)))ᵀ = 1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ := by
    rw [map_add (f := _), map_mul, map_sub, map_one, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
    rfl
  have e2 : (D * (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ) * Di).det = (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm D.det, mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]
  rw [RingHom.map_det, ← Matrix.det_transpose, e1, ← e2, conj_one_add _ _ _ _ h1 h2, hS]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adj_rm (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) :
    rm d.val * ((rm e).map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = rm (sg d e) := by
  have h : ((rm e).map (conjAd E))ᵀ = rm (e.map (conjE E))ᵀ := by
    ext i j
    simp [rm, conjAd_algebraMap]
    rfl
  rw [h, sg, rm_mul, rm_mul]

theorem adj_inv (d : GL (Fin n) E) (t : GA E n) (ht : t ∈ adCent d) :
    rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = t.val := by
  have h : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
  have hv : (t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ = rm d.val :=
    congrArg Units.val h
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  calc rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val
      = t.val * ((t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ) *
          rm (d⁻¹ : GL (Fin n) E).val := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]
    _ = t.val := by rw [hv, mul_assoc, h1, mul_one]

theorem chi_sg (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (t : GA E n) (ht : t ∈ adCent d)
    (hc : t.val * rm (sg d e) = rm (sg d e) * t.val) : GlobalTheory.CompanionTheory.TorusCh.chi (sg d e) t = conjAd E (GlobalTheory.CompanionTheory.TorusCh.chi e t⁻¹) := by
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  have h2 : rm (d⁻¹ : GL (Fin n) E).val * rm d.val = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  have hcom : (t.val - 1) * rm (sg d e) = rm (sg d e) * (t.val - 1) := by
    rw [sub_mul, mul_sub, hc, one_mul, mul_one]
  rw [GlobalTheory.CompanionTheory.TorusCh.chi, GlobalTheory.CompanionTheory.TorusCh.chi, map_det_adj (conjAd E) (rm e) _ t.val _ _ h1 h2 (adj_inv d t ht), adj_rm, hcom]

theorem lam_sg (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t ∈ adCent d)
    (h1 : t.val * rm e = rm e * t.val) (h2 : t.val * rm (sg d e) = rm (sg d e) * t.val) :
    lam (sg d e) t = - lam e t := by
  rw [← lam_inv e he t h1, lam, lam, chi_sg d e t ht h2]
  exact GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces _

end GlobalTheory.CompanionTheory.TorusAdj

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNegStatement
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_involution_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t : GA E n, t ∈ adCent d → t.val * rm e = rm e * t.val → t.val * rm (sg d e) = rm (sg d e) * t.val → lam (sg d e) t = - lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusAdj.lam_sg | exact GlobalTheory.CompanionTheory.TorusAdj.lam_sg | (intros; apply GlobalTheory.CompanionTheory.TorusAdj.lam_sg <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.SiegelWeilFormula.Densx PositivityTheory.Rg.Base1

namespace GlobalTheory.CompanionTheory.Base1

private theorem isClosed_nonnegReal : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

private theorem mul_mem_nonnegReal {z w : ℂ} (hz : z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
    (hw : w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) : z * w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hw0, hw1⟩ := hw
  refine ⟨by simp [Complex.mul_im, hz0, hw0], ?_⟩
  simp only [Complex.mul_re, hz0, hw0, mul_zero, sub_zero]
  exact mul_nonneg hz1 hw1

private theorem tprod_mem_nonnegReal {ι : Type*} (f : ι → ℂ)
    (hf : ∀ i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) :
    ∏' i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  by_cases hm : Multipliable f
  · refine isClosed_nonnegReal.mem_of_tendsto hm.hasProd (Eventually.of_forall fun s => ?_)
    exact Finset.prod_induction f (fun z => z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
      (fun _ _ => mul_mem_nonnegReal) (by simp) (fun i _ => hf i)
  · rw [tprod_eq_one_of_not_multipliable hm]
    simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem factor_mem (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 1 < s) :
    (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∈
      {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = ((q ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0]
    simp [hq]
  have hle : q ^ (-s) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm v.asIdeal) with h | h
    · have : q = 0 := by simp [hq, h]
      rw [this, Real.zero_rpow (by linarith)]
      exact zero_le_one
    · exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 h) (by linarith)
  have hnn : 0 ≤ q ^ (-s) := Real.rpow_nonneg hq0 _
  rw [hc]
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_im]
    linarith
  · refine ⟨by simp, ?_⟩
    simp only [one_mul, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith

theorem lamLim_nonneg {Λ : ℂ} (h : IsLamLim F E Λ) : Λ.im = 0 ∧ 0 ≤ Λ.re := by
  refine isClosed_nonnegReal.mem_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact tprod_mem_nonnegReal _ fun v => factor_mem v hs

theorem lamLim_unique {Λ Λ' : ℂ} (h : IsLamLim F E Λ) (h' : IsLamLim F E Λ') : Λ = Λ' :=
  tendsto_nhds_unique h h'


variable (F E) in
theorem exists_half_lamLim : ∃ c : ℝ≥0, ∀ Λ : ℂ, IsLamLim F E Λ → ((c : ℝ) : ℂ) = Λ / 2 := by
  by_cases h : ∃ Λ, IsLamLim F E Λ
  · obtain ⟨Λ₀, h₀⟩ := h
    obtain ⟨him, hre⟩ := lamLim_nonneg h₀
    refine ⟨Real.toNNReal (Λ₀.re / 2), fun Λ hΛ => ?_⟩
    rw [lamLim_unique hΛ h₀, Real.coe_toNNReal _ (by linarith)]
    apply Complex.ext <;> simp [him]
  · exact ⟨0, fun Λ hΛ => absurd ⟨Λ, hΛ⟩ h⟩

theorem baseOne_of_parts : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 1 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β))) = 0
  · obtain ⟨c', hc'⟩ := exists_half_lamLim F E
    refine ⟨c', ?_, hc'⟩
    rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 0 c' _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hmne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0 := fun v hz =>
    h0.2 v (by rw [hz, smul_zero])
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0 h0.1 hmne
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 ∨
          ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) = 0 := by
        by_contra hz
        push Not at hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ' hz.1
          fun v hv => hz.2 v (by rw [hv, smul_zero]))
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 0 c _ _).2.2 hc'.1 hc'.2.1 hz
  exact ⟨c, hc, hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm c hall⟩

end GlobalTheory.CompanionTheory.Base1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCaseStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_rank_one_base_case : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BaseTest

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_unit_vector (R : Type) [CommRing R] [Algebra F R] {J : Matrix (Fin 1) (Fin 1) E}
    (hJ : IsHermND σ J) : ∃ X : Fin 1 → Fin 1 → R ⊗[F] E, IsUnit (gramR R σ J X).det := by
  have hx : hE σ J (fun _ => 1) (fun _ => 1) ≠ 0 := by
    have h := hJ.2
    rw [Matrix.det_fin_one] at h
    simpa [hE, hform] using h
  refine ⟨ratTup R fun _ _ => 1, ?_⟩
  rw [Matrix.det_fin_one, GlobalTheory.CompanionTheory.SW.MassTest.gramR_ratTup_apply]
  exact (IsUnit.mk0 _ hx).map (inclR R)

end Alg

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isOpen_unit (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (hloc : IsLocR R) (J : Matrix (Fin 1) (Fin 1) E) :
    IsOpen {X : Fin 1 → Fin 1 → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hu, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, -, -, -, -, -, -, -, -, t10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have hO : IsOpen {r : R | IsUnit r} := hu.isOpen_range
  exact (PI.VolStabS.isOpen_isUnit_det R hO 1).preimage (t10 1 1 J)

theorem exists_test_fun (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hl : lam.IsAddHaarMeasure) :
    ∃ φ : (Fin 1 → Fin 1 → R ⊗[F] E) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ (∀ X, 0 ≤ φ X) ∧
      tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det} ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ 0 ∧
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 1) ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_bump _ (isOpen_unit hcm R hloc J) hX

theorem exists_test_set (hcm : IsCMExt F E σ) {J : Matrix (Fin 1) (Fin 1) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    [TotallyDisconnectedSpace R] (hloc : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hl : lam.IsAddHaarMeasure) :
    ∃ A : Set (Fin 1 → Fin 1 → R ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR R σ J X).det} ∧ coordW R b lam 1 1 A ≠ 0 ∧ coordW R b lam 1 1 A ≠ ⊤ := by
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 1 1
  haveI := (coord_measures_haar F E σ hcm R d b lam hl).2.1 1 1
  haveI : TotallyDisconnectedSpace (R ⊗[F] E) := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.totallyDisconnectedSpace
  obtain ⟨X, hX⟩ := exists_unit_vector R hJ
  exact GlobalTheory.CompanionTheory.SW.MassTest.exists_compactOpen _ (isOpen_unit hcm R hloc J) hX

end Loc

theorem testEx : TestEx := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam _ _ _ _ S
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨φ, h1, h2, h3, h4, h5, h6⟩ := exists_test_fun hcm hJ (Ainf F) hLi b li hli.1
  have hA' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ A : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E), IsCompact A ∧ IsOpen A ∧
      A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} ∧ coordW (Fv F v) b (lam v) 1 1 A ≠ 0 ∧
      coordW (Fv F v) b (lam v) 1 1 A ≠ ⊤ := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact exists_test_set hcm hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) b (lam v) (hlam v).1
  choose A0 hc ho hs hn ht using hA'
  classical
  have hv : vol b li lam S φ (fun v => if v ∈ S then A0 v else latV b v) =
      (∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1)) * ∏ v ∈ S, coordW (Fv F v) b (lam v) 1 1 (A0 v) := by
    unfold vol
    congr 1
    exact Finset.prod_congr rfl fun v hvS => by simp [hvS]
  refine ⟨φ, fun v => if v ∈ S then A0 v else latV b v, ⟨h1, h2, h3, h4, ?_, ?_⟩, ?_, ?_⟩
  · intro v hvS
    simp only [hvS, if_true]
    exact ⟨hc v, ho v, hs v⟩
  · intro v hvS
    simp [hvS]
  · rw [hv]
    exact mul_ne_zero h5 (Finset.prod_ne_zero_iff.2 fun v _ => hn v)
  · rw [hv]
    exact ENNReal.mul_ne_top h6 (ENNReal.prod_ne_top fun v _ => ht v)

end GlobalTheory.CompanionTheory.SW.BaseTest
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctionsStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_test_functions : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorant
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem exists_eval_points {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (N : ℕ) (x : Fin N → X) (f : Fin N → X → ℂ), (∀ i, f i ∈ W) ∧
      ∀ w ∈ W, ∀ y, w y = ∑ i, w (x i) * f i y := by
  classical
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have hch : ∀ φ : s, ∃ x, ev x = φ.1 := fun φ => hs φ.2
  choose pt hpt using hch
  let e := s.equivFin
  let x : Fin s.card → X := fun i => pt (e.symm i)
  let T : W →ₗ[ℂ] (Fin s.card → ℂ) := LinearMap.pi fun i => ev (x i)
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hle : Submodule.span ℂ (s : Set (Module.Dual ℂ W)) ≤ LinearMap.ker (Module.Dual.eval ℂ W w) := by
      rw [Submodule.span_le]
      intro φ hφ
      have h1 : T w (e ⟨φ, hφ⟩) = 0 := by rw [hw]; rfl
      have h2 : ev (x (e ⟨φ, hφ⟩)) w = 0 := h1
      have h3 : ev (x (e ⟨φ, hφ⟩)) = φ := by
        show ev (pt (e.symm (e ⟨φ, hφ⟩))) = φ
        rw [Equiv.symm_apply_apply, hpt]
      rw [h3] at h2
      exact h2
    refine Subtype.ext (funext fun y => ?_)
    have hy : ev y ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ W)) :=
      hspan ▸ Submodule.subset_span ⟨y, rfl⟩
    exact hle hy
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hT
  refine ⟨s.card, x, fun i => (L (Pi.single i 1)).1, fun i => (L _).2, ?_⟩
  intro w hw y
  have h1 : L (T ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hL _
  have h2 : T ⟨w, hw⟩ = ∑ i, w (x i) • (Pi.single i (1 : ℂ) : Fin s.card → ℂ) := by
    ext j
    simp [T, ev, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum] at h1
  have h3 := congrArg (fun v : W => v.1 y) h1
  simp only [map_smul] at h3
  simpa [Submodule.coe_sum, Finset.sum_apply] using h3.symm

theorem rank_one_majorant_of_parts : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  intro hCont hFin hOrb hIwa D n ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl hl0 Φ hΦ C hC
  have hcart : ∀ τ, IsCartanInv (gramAt D (V1 D) τ)
      ((fun _ => 1 : D.what₂.Tau → Matrix (Fin (V1 D).rank) (Fin (V1 D).rank) ℂ) τ) :=
    fun τ => GlobalTheory.AdForm.VacStd.cartan_of_gram (GlobalTheory.AdForm.VacStd.gram_of_eq _ _ 1 rfl) τ
  obtain ⟨W, hWfd, hWle, hWK⟩ :=
    hFin D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω l hl (fun _ => 1) hcart Φ hΦ
  haveI := hWfd
  obtain ⟨N, x, f, hfW, hrep⟩ := exists_eval_points W
  have hcont := hCont D n (V1 D) ψ hψ χ hχ hRes θ hθ μ 𝓕 hμ ω hω Φ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ K D n, ‖(ω k Φ).1 (x i)‖ ≤ B := by
    intro i
    have hc : Continuous fun k : G D n => (ω k Φ).1 (x i) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB⟩ := HeightExists.isCompact_K.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩
  choose B hB0 hB using hB
  obtain ⟨A₁, A₂, R, hA₁, hA₂, hiwa⟩ := hIwa D n C hC
  have hM := fun i => hOrb D n θ hθ l hl0 (f i) (hWle (hfW i)) A₁ A₂ hA₁ hA₂
  choose M hMs hMpos hMle using hM
  have hc0 : 0 ≤ (max R 0) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_max_right _ _) _
  refine ⟨(((max R 0) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i,
    Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hMs i)), ?_⟩
  intro h hh y
  obtain ⟨m, t, k, a, b, hk, rfl, hm, ht, ha1, ha2, hR⟩ := hiwa h hh
  set c : ℝ := (max R 0) ^ ((1 : ℝ) / 2) with hc
  have e1 : ‖(ω (m * t * k) Φ).1 y‖ =
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) * ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hω.levi m a hm, hω.unip t b ht,
      norm_mul, norm_mul, norm_mul, hψ.2.1, norm_npow (hom_pos _ _)]
    have hre : (((V1 D).rank : ℂ) / 2).re = (1 : ℝ) / 2 := by
      show ((((1 : ℕ) : ℂ)) / 2).re = (1 : ℝ) / 2
      norm_num
    rw [hre, Circle.norm_coe, one_mul, one_mul]
  have e2 : ‖(ω k Φ).1 (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ∑ i, B i * ‖M i y‖ := by
    rw [hrep _ (hWK k hk)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i k hk) (hMle i a ha1 ha2 y) (norm_nonneg _) (hB0 i)
  have e3 : (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((1 : ℝ) / 2) ≤ c :=
    Real.rpow_le_rpow (NNReal.coe_nonneg _) (hR.trans (le_max_left _ _)) (by norm_num)
  have e4 : ∀ i, M i y = ((‖M i y‖ : ℝ) : ℂ) := by
    intro i
    have h1 := hMpos i y
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      rw [show M i y = (((M i y).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [h1.2])]
      simp [abs_of_nonneg h1.1]
    · simp [h1.2]
  have e5 : ‖((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y‖ = c * ∑ i, B i * ‖M i y‖ := by
    have h1 : ((((c : ℝ) : ℂ) • ∑ i, (B i : ℂ) • M i) : Mx D (V1 D).rank n → ℂ) y =
        ((c * ∑ i, B i * ‖M i y‖ : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [← e4 i]
    rw [h1, Complex.norm_real, Real.norm_of_nonneg]
    exact mul_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hB0 i) (norm_nonneg _))
  rw [e1, e5]
  exact mul_le_mul e3 e2 (norm_nonneg _) hc0

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorantStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_majorant : WeilCont → WeilKFin → OrbitMaj → IwaCpt → FockTranslateSchwartzMajorant := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | exact GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts | (intros; apply GlobalTheory.CompanionTheory.ThTot.rank_one_majorant_of_parts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_integral_mul_of_bdd {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    {f : X → Y → ℂ} (hf : Continuous fun w : X × Y => f w.1 w.2) {B : ℝ} (hB : ∀ x y, ‖f x y‖ ≤ B)
    {g : Y → ℂ} (hg : Integrable g ν) : Continuous fun x => ∫ y, f x y * g y ∂ν := by
  refine continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_)
    (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)
  · have h1 : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    exact h1.aestronglyMeasurable.mul hg.1
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)
  · have h1 : Continuous fun x => f x y := hf.comp (continuous_id.prodMk continuous_const)
    exact h1.mul continuous_const

theorem integral_integral_mul_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {F : X × Y → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {B : ℝ} (hB : ∀ w, ‖F w‖ ≤ B)
    {a : X → ℂ} {c : Y → ℂ} (ha : Integrable a μ) (hc : Integrable c ν) :
    ∫ x, (∫ z, F (x, z) * c z ∂ν) * a x ∂μ = ∫ w, F w * (a w.1 * c w.2) ∂(μ.prod ν) := by
  have hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν) :=
    (ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)
  rw [integral_prod _ hI]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  refine Matrix.ext fun i j => ?_
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  refine Matrix.ext fun i j => ?_
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  refine Matrix.ext fun i j => ?_
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous fun w : Mx D r p × Mx D s p => rowJ w.1 w.2 := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simp only [rowJ, Fin.addCases_left]
    exact continuous_fst.matrix_elem a j
  | right b =>
    simp only [rowJ, Fin.addCases_right]
    exact continuous_snd.matrix_elem b j

theorem continuous_th_one {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {b₀ : HermE D ρ}
    {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) : Continuous (Ω 1) :=
  hΩ.cont.comp (continuous_const.prodMk continuous_id)

theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf

theorem stepTotal : ProdTh → ProdMeas → StepTotal := by
  intro hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth
  obtain ⟨B, hB⟩ := hbd
  have hμ := hM D r s p μr Fr μs Fs μ F hr hs h
  subst hμ
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1
  haveI : FirstCountableTopology (Mx D r p) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1
  haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1
  haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
  haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  have hcJ := continuous_rowJ (D := D) (r := r) (s := s) (p := p)
  have hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2) := hu.comp hcJ
  have key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0 := by
    intro Ωr Ωs hΩr hΩs
    have hT := hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs
    have h0 := horth _ hT
    have hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y)) :=
      hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul
        ((continuous_th_one hΩs).comp continuous_rowB)))
    rw [integral_map hcJ.aemeasurable hm.aestronglyMeasurable] at h0
    rw [integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2))
      hcF.aestronglyMeasurable (fun w => hB _)
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1)))
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1)))]
    simpa only [rowT_rowJ, rowB_rowJ, map_mul] using h0
  have hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0 := by
    intro Ωs hΩs
    have hi : Integrable (fun z => conj (Ωs 1 z)) μs :=
      integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))
    refine congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)
    · exact continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi
    · refine ⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)
      show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact fun Ωr hΩr => key Ωr Ωs hΩr hΩs
  have hz : ∀ x, (fun z => u (rowJ x z)) = 0 := fun x =>
    Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩
      fun Ωs hΩs => hv Ωs hΩs x
  funext y
  rw [← rowJ_rowT_rowB y]
  exact congrFun (hz (rowT y)) (rowB y)

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProductsStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_total_of_products : ProdTh → ProdMeas → StepTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.stepTotal | exact GlobalTheory.CompanionTheory.ThTot.stepTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.stepTotal <;> assumption)
end
end
