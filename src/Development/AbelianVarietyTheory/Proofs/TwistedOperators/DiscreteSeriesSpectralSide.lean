module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IrreducibleKStableFiniteSubspace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissible
open Formalism.MainNotions.S

namespace GlobalTheory.IrrAdm

theorem isIrrAdm_of_irred : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  intro n ε H _ _ _ _ π hU hI
  have hK : ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖π k v‖ = ‖v‖ := fun k hk v =>
    hU.2.1 k (GlobalTheory.GKModule.mem_UJset_of_mem_Kset hk) v
  refine ⟨inferInstance, ⟨hU.1, hU.2.2, hK, ?_⟩, hI⟩
  intro Λ
  classical
  by_cases hne : ∃ S₀ : Submodule ℂ H, S₀ ≤ ⊤ ∧ IsKTypeOf ε π Λ S₀
  · obtain ⟨S₀, -, hS₀⟩ := hne
    haveI : FiniteDimensional ℂ S₀ := hS₀.1
    have hY := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε H π hU hI).1 S₀ hS₀.1 hS₀.2.1
    let b := Module.finBasis ℂ S₀
    choose Y hYf hvY hYB using fun i => hY (b i) (b i).2
    haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYf
    refine Submodule.finiteDimensional_of_le (sSup_le fun S hS => ?_) (S₂ := ⨆ i, Y i)
    obtain ⟨B, hB, rfl⟩ := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H π hU.1 hU.2.2 hK).2 Λ S₀ S hS₀ hS.2
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    have hx' : (⟨x, hx⟩ : S₀) ∈ Submodule.span ℂ (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span S₀.subtype hx'
    rw [← Set.range_comp] at h2
    refine (Submodule.span_le.2 ?_) h2
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.subtype_apply,
      SetLike.mem_coe]
    exact Submodule.mem_iSup_of_mem i (hYB i B hB _ (hvY i))
  · have : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S} = ∅ :=
      Set.eq_empty_of_forall_notMem fun S hS => hne ⟨S, hS⟩
    rw [this, sSup_empty]
    infer_instance

end GlobalTheory.IrrAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissibleStatement
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_irreducible_is_admissible : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  first | exact @GlobalTheory.IrrAdm.isIrrAdm_of_irred | exact GlobalTheory.IrrAdm.isIrrAdm_of_irred | (intros; apply GlobalTheory.IrrAdm.isIrrAdm_of_irred <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTrace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.ArchTrace

open Formalism.MainNotions.S (IsURepOn UJset IsIrredOn)
open GlobalTheory.Orb (ujMat ujRep frameEquiv)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

section Pull

variable {m : ℕ} (ε : Fin m → Bool) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem ujMat_injective : Function.Injective (ujMat ε) := fun _ _ h => Subtype.ext (Units.ext h)

def matRep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (x : Matrix (Fin m) (Fin m) ℂ) : X →L[ℂ] X := by
  classical exact if h : ∃ g, ujMat ε g = x then π h.choose else 1

theorem matRep_ujMat (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (g : Formalism.REAL.UJ ε) : matRep ε π (ujMat ε g) = π g := by
  have h : ∃ g', ujMat ε g' = ujMat ε g := ⟨g, rfl⟩
  rw [matRep, dite_eq_left h, ujMat_injective ε h.choose_spec]

theorem ujMat_mem_UJset (g : Formalism.REAL.UJ ε) : ujMat ε g ∈ UJset ε := g.2

variable {ε}

theorem matRep_isURepOn (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (hπ : GlobalTheory.OpTrace.IsUnitaryRep π)
    (hs : ∀ x ∈ UJset ε, ∃ g, ujMat ε g = x) : IsURepOn (UJset ε) (matRep ε π) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun a ha v => ?_, fun v => ?_⟩
  · rw [← map_one (ujMat ε), matRep_ujMat, map_one]
  · obtain ⟨g, rfl⟩ := hs a ha
    obtain ⟨h, rfl⟩ := hs b hb
    rw [← map_mul, matRep_ujMat, matRep_ujMat, matRep_ujMat, map_mul]
    rfl
  · obtain ⟨g, rfl⟩ := hs a ha
    rw [matRep_ujMat]
    exact hπ.norm_apply g v
  · have hr : UJset ε = Set.range (ujMat ε) :=
      Set.ext fun x => ⟨fun hx => hs x hx, by rintro ⟨g, rfl⟩; exact ujMat_mem_UJset ε g⟩
    rw [hr, continuousOn_iff_continuous_domRestrict]
    let E := (GlobalTheory.Orb.isEmbedding_ujMat ε).toHomeomorph
    have hE : ∀ y, (fun g => π g v) (E.symm y) = matRep ε π (y : Matrix (Fin m) (Fin m) ℂ) v := by
      intro y
      obtain ⟨g, rfl⟩ := E.surjective y
      show π (E.symm (E g)) v = matRep ε π (ujMat ε g) v
      rw [E.symm_apply_apply, matRep_ujMat]
    exact ((hπ.continuous_apply v).comp E.symm.continuous).congr hE

theorem matRep_isIrredOn (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (hπ : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π) :
    IsIrredOn (UJset ε) (matRep ε π) := fun S hS hinv =>
  hπ.2 S ⟨hS, fun g v hv => by simpa [matRep_ujMat] using hinv _ (ujMat_mem_UJset ε g) v hv⟩

theorem groupRep_matRep (π : Formalism.REAL.UJ ε →* (X →L[ℂ] X)) (h : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) (matRep ε π)) :
    groupRep ε h = π := MonoidHom.ext fun g => matRep_ujMat ε π g

end Pull

theorem hasWideGaps_of_gap {r : ℕ} (hr : 0 < r) {lam : Fin r → ℤ} (h : Gap lam) :
    GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.HasWideGaps lam := by
  refine ⟨?_, h⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
  have := h i.castSucc i.succ (by simp)
  push_cast at this
  omega

theorem isHCParam_of_gap {r : ℕ} (hr : Odd r) {lam : Fin r → ℤ} (h : Gap lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i => (lam i : ℝ)) := by
  refine ⟨Int.cast_strictMono.comp_strictAnti (hasWideGaps_of_gap hr.pos h).1, fun a => ?_⟩
  obtain ⟨k, hk⟩ := hr
  subst hk
  refine ⟨lam a - k, ?_⟩
  push_cast
  ring

end GlobalTheory.ArchTrace

namespace GlobalTheory.ArchTrace

open Formalism.MainNotions.S (IsURepOn UJset IsIrredOn)
open GlobalTheory.Orb (ujMat ujRep frameEquiv IsPseudoCoeff isPseudoCoeff_dsRep_iff exists_frameMat_eq repOp_map)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

theorem trace_pseudoCoeff_arch : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ → ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  intro hDS hHC hSep D V lam S M T U μa μf μ _ _ fa ff hT ρ X _ _ _ δ hδ
  obtain ⟨hodd, hgap, hlam, -, hprod, harch, -⟩ := hT
  haveI : (μa (placeOf D ρ)).IsHaarMeasure := hprod.1 (placeOf D ρ)
  haveI := (M.ds ρ).1
  haveI : Nontrivial X := hδ.irred.1
  have hs : ∀ x ∈ UJset (M.ε ρ), ∃ g, ujMat (M.ε ρ) g = x := fun x hx => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ hx
    exact ⟨frameEquiv M ρ g, hg⟩
  haveI : ((μa (placeOf D ρ)).map (frameEquiv M ρ)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map _ (frameEquiv M ρ)
  have hfe : (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm) ∘ frameEquiv M ρ = fa (placeOf D ρ) :=
    funext fun g => by simp
  have hpc : IsPseudoCoeff (ujMat (M.ε ρ)) ((μa (placeOf D ρ)).map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1)
      (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm) :=
    (isPseudoCoeff_dsRep_iff M ρ _ _).2 (by rw [hfe]; exact harch ρ)
  let π := δ.comp ((frameEquiv M ρ).symm : Formalism.REAL.UJ (M.ε ρ) →* _)
  have hπu : GlobalTheory.OpTrace.IsUnitaryRep π :=
    ⟨fun g v => hδ.unitary.norm_apply _ v,
      fun v => (hδ.unitary.continuous_apply v).comp (frameEquiv M ρ).symm.continuous⟩
  have hπi : GlobalTheory.AutomorphicL2Unitary.IsTopIrreducible π :=
    ⟨hδ.irred.1, fun W hW => hδ.irred.2 W ⟨hW.1, fun h v hv => by simpa [π] using hW.2 (frameEquiv M ρ h) v hv⟩⟩
  have hU := matRep_isURepOn π hπu hs
  have hadm : IsIrrAdm (M.ε ρ) (matRep (M.ε ρ) π) := GlobalTheory.T.unitary_irreducible_is_admissible _ _ X _ hU (matRep_isIrredOn π hπi)
  obtain ⟨Θ, hΘ⟩ := hHC.1 V.rank (M.ε ρ) ((μa (placeOf D ρ)).map (frameEquiv M ρ)) X (matRep (M.ε ρ) π) hadm
  obtain ⟨c, htr⟩ : ∃ c, HasTrace (repOp (groupRep (M.ε ρ) hadm.2.1.1) ((μa (placeOf D ρ)).map (frameEquiv M ρ))
      (fa (placeOf D ρ) ∘ (frameEquiv M ρ).symm)) c := ⟨_, hΘ.1.2.2 _ hpc.mem⟩
  have hδe : π.comp ((frameEquiv M ρ) : _ →* Formalism.REAL.UJ (M.ε ρ)) = δ := MonoidHom.ext fun g => by simp [π]
  refine ⟨c, ?_, fun hc => ?_⟩
  · have h2 := htr
    rw [groupRep_matRep, repOp_map, hδe, hfe] at h2
    exact h2
  · have hML : M.lam ρ = fun i => (lam ρ i : ℝ) := funext (hlam ρ)
    have hHCp : Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := by
      rw [hML]
      exact isHCParam_of_gap hodd (hgap ρ)
    have hinf := (GlobalTheory.DiscreteSeriesConsequences.of_classification hDS).2.1 V.rank (M.ε ρ) (M.lam ρ) (M.H ρ) (M.σ ρ) hHCp (M.ds ρ)
    simp only [hlam ρ, Complex.ofReal_intCast] at hinf
    have hD : GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.IsDiscreteWithInfChar (M.ε ρ) (lam ρ) (M.σ ρ) :=
      ⟨⟨(M.ds ρ).1, (M.ds ρ).2.1, (M.ds ρ).2.2.1, (M.ds ρ).2.2.2.1, (M.ds ρ).2.2.2.2.1⟩, hinf⟩
    obtain ⟨-, hb⟩ := hSep V.rank hodd (M.ε ρ) (lam ρ) (hasWideGaps_of_gap hodd.pos (hgap ρ)) (M.H ρ) (M.σ ρ) hD
      ((μa (placeOf D ρ)).map (frameEquiv M ρ)) _ hpc X (matRep (M.ε ρ) π) hadm _ htr hc
    obtain ⟨⟨A, hA⟩, -⟩ := hb hU
    refine ⟨A, fun g v => ?_⟩
    have h3 := hA (ujMat (M.ε ρ) (frameEquiv M ρ g)) (ujMat_mem_UJset _ _) v
    rw [matRep_ujMat] at h3
    simp only [π, MonoidHom.comp_apply, MonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply] at h3
    exact h3

end GlobalTheory.ArchTrace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestFunctionTraceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_test_function_trace : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (ρ : D.what₂.Tau) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* (X →L[ℂ] X)), IsIrrUnitary δ → ∃ c, HasTrace (repOp δ (μa (placeOf D ρ)) (fa (placeOf D ρ))) c ∧ (c ≠ 0 → IsUnitEquiv δ (dsRep M ρ)) := by
  first | exact @GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | exact GlobalTheory.ArchTrace.trace_pseudoCoeff_arch | (intros; apply GlobalTheory.ArchTrace.trace_pseudoCoeff_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory.TrSplit

open MeasureTheory

theorem sigmaFinite_update {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (w : ι) (c : α w) (i : ι) :
    SigmaFinite (Function.update μ w (Measure.dirac c) i) := by
  rcases eq_or_ne i w with rfl | h
  · rw [Function.update_self]; infer_instance
  · rw [Function.update_of_ne h]; infer_instance

theorem map_update_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (w : ι) (c : α w)
    [∀ i, SigmaFinite (Function.update μ w (Measure.dirac c) i)] :
    ((μ w).prod (Measure.pi (Function.update μ w (Measure.dirac c)))).map
      (fun p => Function.update p.2 w p.1) = Measure.pi μ := by
  have hm : Measurable fun p : α w × (∀ i, α i) => Function.update p.2 w p.1 :=
    (measurable_update' (a := w)).comp measurable_swap
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have e : (fun p : α w × (∀ i, α i) => Function.update p.2 w p.1) ⁻¹' Set.univ.pi s =
      s w ×ˢ Set.univ.pi (Function.update s w Set.univ) := by
    ext ⟨x, a⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h w, fun i => ?_⟩
      rcases eq_or_ne i w with rfl | hi
      · simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      rcases eq_or_ne i w with rfl | hi
      · simpa using h1
      · simpa [Function.update_of_ne hi] using h2 i
  rw [e, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl w,
    Fintype.prod_eq_mul_prod_compl w (fun i => μ i (s i))]
  simp only [Function.update_self, Measure.dirac_apply_of_mem (Set.mem_univ c), one_mul]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≠ w := by simpa using hi
  simp [Function.update_of_ne hi']

end GlobalTheory.TrSplit

noncomputable section

namespace GlobalTheory.TrSplit

open MeasureTheory GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem projArch_archFinEquiv_symm (u : InfinitePlace F) (p : (∀ u, GArch σ J u) × GFin σ J) :
    projArch σ J u ((archFinEquiv σ J).symm p) = p.1 u :=
  congrFun (congrArg Prod.fst ((archFinEquiv σ J).apply_symm_apply p)) u

theorem projFin_archFinEquiv_symm (p : (∀ u, GArch σ J u) × GFin σ J) :
    projFin σ J ((archFinEquiv σ J).symm p) = p.2 :=
  congrArg Prod.snd ((archFinEquiv σ J).apply_symm_apply p)

theorem proj_archFinEquiv_symm (v : HeightOneSpectrum (𝓞 F)) (p : (∀ u, GArch σ J u) × GFin σ J) :
    proj σ J v ((archFinEquiv σ J).symm p) = projFinLoc σ J v p.2 := by
  rw [← projFinLoc_projFin, projFin_archFinEquiv_symm]


variable (σ J) in
def killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) :
    ((∀ u, GArch σ J u) × GFin σ J) →* GAd σ J :=
  ((archFinEquiv σ J).symm : ((∀ u, GArch σ J u) × GFin σ J) →* GAd σ J).comp
    (MonoidHom.prodMap
      { toFun := fun a => Function.update a w 1
        map_one' := by simp
        map_mul' := fun a b => by
          funext u
          rcases eq_or_ne u w with rfl | h
          · simp
          · simp [Function.update_of_ne h] }
      (MonoidHom.id _))

theorem killAt_apply [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (z : (∀ u, GArch σ J u) × GFin σ J) :
    killAt σ J w z = (archFinEquiv σ J).symm (Function.update z.1 w 1, z.2) := rfl

theorem continuous_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) : Continuous (killAt σ J w) := by
  change Continuous fun z : (∀ u, GArch σ J u) × GFin σ J => (archFinEquiv σ J).symm (Function.update z.1 w 1, z.2)
  exact (archFinEquiv σ J).symm.continuous.comp ((continuous_fst.update w continuous_const).prodMk continuous_snd)

theorem embArch_mul_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (x : GArch σ J w)
    (a : ∀ u, GArch σ J u) (b : GFin σ J) :
    embArch σ J w x * killAt σ J w (a, b) = (archFinEquiv σ J).symm (Function.update a w x, b) := by
  refine GAd_ext σ J (fun u => ?_) fun v => ?_
  · rw [map_mul, killAt_apply, projArch_archFinEquiv_symm, projArch_archFinEquiv_symm]
    rcases eq_or_ne u w with rfl | h
    · simp
    · simp [Function.update_of_ne h, projArch_embArch_ne σ J h]
  · rw [map_mul, killAt_apply, proj_archFinEquiv_symm, proj_archFinEquiv_symm, proj_embArch, one_mul]

theorem commute_embArch_killAt [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (x : GArch σ J w)
    (z : (∀ u, GArch σ J u) × GFin σ J) :
    embArch σ J w x * killAt σ J w z = killAt σ J w z * embArch σ J w x := by
  refine GAd_ext σ J (fun u => ?_) fun v => ?_
  · rw [map_mul, map_mul, killAt_apply, projArch_archFinEquiv_symm]
    rcases eq_or_ne u w with rfl | h
    · simp
    · simp [Function.update_of_ne h, projArch_embArch_ne σ J h]
  · rw [map_mul, map_mul, proj_embArch, one_mul, mul_one]

end GlobalTheory.TrSplit

namespace GlobalTheory.TrSplit

open MeasureTheory GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_repOp_tensor_eq_mul {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (hfa : ∀ w, fa w ∈ CcArch σ J w) (hff : IsFinFamily σ J L ff)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : GAd σ J →* (H →L[ℂ] H)} (hπ : IsUnitaryRep π) (w : InfinitePlace F) :
    ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch σ J w g) = π (embArch σ J w g) * Q) ∧
      repOp π μ (tensor σ J fa ff) = repOp (π.comp (embArch σ J w)) (μa w) (fa w) * Q := by
  classical
  have := hμ.haar_arch
  have := hμ.haar_loc
  have := hμ.haar
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFin σ J L μf hμ.eventually_eq_one).exists
  haveI : ν.IsHaarMeasure := (isRestrictedProdFin_iff.1 hν).2.1
  have hmap := hμ.map_archFin hν
  let μa' := Function.update μa w (Measure.dirac 1)
  haveI : ∀ u, SigmaFinite (μa' u) := sigmaFinite_update μa w 1
  let ρ := (Measure.pi μa').prod ν
  let fa' : ∀ u, GArch σ J u → ℂ := Function.update fa w (fun _ => 1)
  let Ψ : (∀ u, GArch σ J u) × GFin σ J → ℂ := fun z => (∏ u, fa' u (z.1 u)) * tensorFin σ J ff z.2
  let π' := π.comp (killAt σ J w)
  have hπ' : IsUnitaryRep π' :=
    ⟨fun g v => hπ.norm_apply _ v, fun v => (hπ.continuous_apply v).comp (continuous_killAt w)⟩
  have hπw : IsUnitaryRep (π.comp (embArch σ J w)) :=
    ⟨fun g v => hπ.norm_apply _ v, fun v => (hπ.continuous_apply v).comp (continuous_embArch σ J w)⟩
  have hcfa : ∀ u, Continuous (fa u) := fun u => continuous_of_mem_ccSmooth (continuous_archCoord σ J u) (hfa u)
  have h1 : Integrable (fun a : ∀ u, GArch σ J u => ∏ u, fa' u (a u)) (Measure.pi μa') :=
    Integrable.fintype_prod_dep (f := fa') (μ := μa') fun u => by
      rcases eq_or_ne u w with rfl | h
      · simp [fa', μa']
      · rw [show fa' u = fa u from Function.update_of_ne h _ _, show μa' u = μa u from Function.update_of_ne h _ _]
        exact (hcfa u).integrable_of_hasCompactSupport (hfa u).1
  have h2 : Integrable (tensorFin σ J ff) ν :=
    hff.tensorFin_mem.1.continuous.integrable_of_hasCompactSupport hff.tensorFin_mem.2
  have hΨint : Integrable Ψ ρ := h1.mul_prod h2
  have hQ := hπ'.isRepOp_of_integrable hΨint
    (fun v => hΨint.aestronglyMeasurable.smul (hπ'.continuous_apply v).aestronglyMeasurable)
  refine ⟨repOp π' ρ Ψ, fun x => ?_, ?_⟩
  · ext v
    simp only [ContinuousLinearMap.mul_apply]
    rw [(hQ _).2, (hQ v).2, ← ContinuousLinearMap.integral_comp_comm _ (hQ v).1]
    congr 1
    funext g
    rw [map_smul]
    congr 1
    change (π (killAt σ J w g)) (π (embArch σ J w x) v) =
      (π (embArch σ J w x)) (π (killAt σ J w g) v)
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul,
      commute_embArch_killAt]
  · have hfc := continuous_of_mem_ccAd (tensor_mem_ccAd hfa hff)
    set f := tensor σ J fa ff with hfdef
    let e := archFinEquiv σ J
    ext v
    rw [ContinuousLinearMap.mul_apply, hπ.repOp_apply hfc.1 hfc.2, hπw.repOp_apply (hcfa w) (hfa w).1, (hQ v).2]
    let Fn : (∀ u, GArch σ J u) × GFin σ J → H := fun y => f (e.symm y) • π (e.symm y) v
    have hFc : Continuous Fn :=
      (hfc.1.comp e.symm.continuous).smul ((hπ.continuous_apply v).comp e.symm.continuous)
    have hFint : Integrable Fn ((Measure.pi μa).prod ν) := by
      rw [← hmap]
      have : Integrable (fun g => f g • π g v) μ :=
        (hfc.1.smul (hπ.continuous_apply v)).integrable_of_hasCompactSupport hfc.2.smul_right
      refine (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv Fn).2 ?_
      convert this using 1
      funext g
      change f (e.symm (e g)) • π (e.symm (e g)) v = _
      rw [e.symm_apply_apply]
    have h1 : ∫ g, f g • π g v ∂μ = ∫ y, Fn y ∂((Measure.pi μa).prod ν) := by
      rw [← hmap]
      rw [show (e : GAd σ J → _) = e.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
      congr 1
      funext g
      change _ = f (e.symm (e g)) • π (e.symm (e g)) v
      rw [e.symm_apply_apply]
    let T : GArch σ J w × ((∀ u, GArch σ J u) × GFin σ J) → (∀ u, GArch σ J u) × GFin σ J :=
      fun p => (Function.update p.2.1 w p.1, p.2.2)
    have hU : Measurable fun p : GArch σ J w × (∀ u, GArch σ J u) => Function.update p.2 w p.1 :=
      (measurable_update' (a := w)).comp measurable_swap
    have hTm : Measurable T :=
      ((measurable_update' (a := w)).comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)
    have hT : MeasurePreserving T ((μa w).prod ρ) ((Measure.pi μa).prod ν) := by
      refine ⟨hTm, ?_⟩
      have hA := map_update_prod_pi μa w (1 : GArch σ J w)
      have hassoc := (measurePreserving_prodAssoc (μa w) (Measure.pi μa') ν).map_eq
      show Measure.map T ((μa w).prod ((Measure.pi μa').prod ν)) = _
      rw [← hassoc, Measure.map_map hTm MeasurableEquiv.prodAssoc.measurable]
      have e1 : T ∘ MeasurableEquiv.prodAssoc =
          Prod.map (fun p : GArch σ J w × (∀ u, GArch σ J u) => Function.update p.2 w p.1) id := by
        funext ⟨⟨x, a⟩, b⟩
        rfl
      rw [e1, ← Measure.map_prod_map _ _ hU measurable_id, hA, Measure.map_id]
    have hpt : ∀ x (z : (∀ u, GArch σ J u) × GFin σ J),
        Fn (T (x, z)) = fa w x • π (embArch σ J w x) (Ψ z • π' z v) := by
      rintro x ⟨a, b⟩
      have hg : e.symm (Function.update a w x, b) = embArch σ J w x * killAt σ J w (a, b) :=
        (embArch_mul_killAt w x a b).symm
      have hf : f (e.symm (Function.update a w x, b)) = fa w x * Ψ (a, b) := by
        simp only [hfdef, e, tensor, projArch_archFinEquiv_symm, proj_archFinEquiv_symm, Ψ, fa', tensorFin]
        rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
          (fun u => Function.update fa w (fun _ => (1 : ℂ)) u (a u))]
        simp only [Function.update_self, one_mul]
        rw [Finset.prod_congr rfl fun u hu => (show fa u (Function.update a w x u) =
          Function.update fa w (fun _ => (1 : ℂ)) u (a u) by
            have hu' : u ≠ w := by simpa using hu
            simp [Function.update_of_ne hu'])]
        ring
      change f (e.symm (Function.update a w x, b)) • π (e.symm (Function.update a w x, b)) v = _
      rw [hf, hg, map_mul, mul_smul, ContinuousLinearMap.mul_apply, map_smul]
      rfl
    rw [h1, ← hT.map_eq, integral_map hT.measurable.aemeasurable (hT.map_eq ▸ hFc.aestronglyMeasurable),
      integral_prod _ (by
        have := (hT.map_eq ▸ hFint : Integrable Fn (((μa w).prod ρ).map T))
        exact this.comp_aemeasurable hT.measurable.aemeasurable)]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [hpt]
    rw [integral_smul, ContinuousLinearMap.integral_comp_comm _ (hQ v).1]
    rfl

end GlobalTheory.TrSplit

namespace GlobalTheory.TrSplit

theorem repOp_tensor_split : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ w, ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch D.sp.cm.sig V.gram w g) = π (embArch D.sp.cm.sig V.gram w g) * Q) ∧ repOp π μ (tensor D.sp.cm.sig V.gram fa ff) = repOp (π.comp (embArch D.sp.cm.sig V.gram w)) (μa w) (fa w) * Q := by
  intro D V μa μf μ hμ fa ff hfa hff H _ _ _ π hπ w
  exact exists_repOp_tensor_eq_mul hμ hfa hff hπ w

end GlobalTheory.TrSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlaceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensorOperator_split_oneRealPlace : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ w, ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch D.sp.cm.sig V.gram w g) = π (embArch D.sp.cm.sig V.gram w g) * Q) ∧ repOp π μ (tensor D.sp.cm.sig V.gram fa ff) = repOp (π.comp (embArch D.sp.cm.sig V.gram w)) (μa w) (fa w) * Q := by
  first | exact @GlobalTheory.TrSplit.repOp_tensor_split | exact GlobalTheory.TrSplit.repOp_tensor_split | (intros; apply GlobalTheory.TrSplit.repOp_tensor_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypic
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypic
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

theorem exists_homIn_ne_zero (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) {U : Submodule ℂ H}
    (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ S ∈ homIn δ π U, S ≠ 0 := by
  have := hU.completeSpace
  by_contra hn
  push_neg at hn
  apply h0
  have hle : isoPart δ π ⊤ ≤ Uᗮ := isoPart_le U.isClosed_orthogonal fun T hT x => by
    have hS : U.starProjection ∘L T ∈ homIn δ π U :=
      ⟨fun x => U.starProjection_apply_mem _, fun g x => by
        simp only [comp_apply, hT.2 g x, hU.starProjection_apply hπ]⟩
    have := DFunLike.congr_fun (hn _ hS) x
    rw [comp_apply, zero_apply] at this
    exact (Submodule.starProjection_apply_eq_zero_iff _).1 this
  rw [hiso, top_le_iff, Submodule.orthogonal_eq_top_iff] at hle
  exact hle

theorem exists_isCopy_le (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {U : Submodule ℂ H} (hU : IsSubrep π U) (h0 : U ≠ ⊥) : ∃ W ≤ U, IsCopy δ π W := by
  obtain ⟨S, hS, hS0⟩ := exists_homIn_ne_zero hπ hiso hU h0
  exact ⟨_, by rintro _ ⟨x, rfl⟩; exact hS.1 x, isCopy_range hδ hπ hS hS0⟩

theorem isCopy_of_isIrredSubrep (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π)
    {W : Submodule ℂ H} (hW : IsIrredSubrep π W) : IsCopy δ π W := by
  obtain ⟨V, hVW, hV⟩ := exists_isCopy_le hδ hπ hiso hW.1 hW.2.1
  have hV' := hV.isIrredSubrep hδ.irred
  rcases hW.2.2 V hVW hV'.1 with h | h
  · exact absurd h hV'.2.1
  · exact h ▸ hV

theorem exists_hilbertBasis (hδ : IsIrrUnitary δ) (hπ : IsUnitaryRep π) (hiso : IsIsotypic δ π) :
    ∃ (ι : Type) (e : ι → (X →ₗᵢ[ℂ] H)) (b : HilbertBasis (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) ℂ H),
      (∀ i g x, e i (δ g x) = π g (e i x)) ∧ ∀ p, b p = e p.1 (GlobalTheory.OpTrace.stdBasis (H := X) p.2) := by
  obtain ⟨ι, W, hW, hs⟩ := GlobalTheory.DiscreteSum.exists_isHilbertSum hπ fun U hU h0 => by
    obtain ⟨V, hV, hc⟩ := exists_isCopy_le hδ hπ hiso hU h0
    exact ⟨V, hV, hc.isIrredSubrep hδ.irred⟩
  choose e he hr using fun i => isCopy_iff.1 (isCopy_of_isIrredSubrep hδ hπ hiso (hW i))
  have hmem : ∀ i x, e i x ∈ W i := fun i x => hr i ▸ ⟨x, rfl⟩
  let v : (Σ _ : ι, GlobalTheory.OpTrace.stdIndex X) → H := fun p => e p.1 (GlobalTheory.OpTrace.stdBasis (H := X) p.2)
  have hon : Orthonormal ℂ v := by
    refine ⟨fun p => by simp [v, (GlobalTheory.OpTrace.stdBasis (H := X)).orthonormal.1], fun p q hpq => ?_⟩
    obtain ⟨i, a⟩ := p
    obtain ⟨j, c⟩ := q
    by_cases hij : i = j
    · subst hij
      have hac : a ≠ c := fun h => hpq (by rw [h])
      simp only [v, LinearIsometry.inner_map_map]
      exact (GlobalTheory.OpTrace.stdBasis (H := X)).orthonormal.2 hac
    · exact hs.OrthogonalFamily hij ⟨_, hmem i _⟩ ⟨_, hmem j _⟩
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    refine GlobalTheory.DiscreteSum.eq_zero_of_isHilbertSum hs fun i y hy => ?_
    obtain ⟨z, rfl⟩ : y ∈ LinearMap.range (e i).toLinearMap := (hr i).symm ▸ hy
    have h1 : ∀ a, ⟪GlobalTheory.OpTrace.stdBasis (H := X) a, adjoint (e i).toContinuousLinearMap x⟫_ℂ = 0 := fun a => by
      rw [adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self (f := v) ⟨i, a⟩)) hx
    have h2 : adjoint (e i).toContinuousLinearMap x = 0 := by
      have := (GlobalTheory.OpTrace.stdBasis (H := X)).hasSum_repr (adjoint (e i).toContinuousLinearMap x)
      simp only [HilbertBasis.repr_apply_apply, h1, zero_smul] at this
      exact (hasSum_zero.unique this).symm
    change ⟪(e i).toContinuousLinearMap z, x⟫_ℂ = 0
    rw [← adjoint_inner_right, h2, inner_zero_right]
  exact ⟨ι, e, HilbertBasis.mkOfOrthogonalEqBot hon hsp, he, fun p => by simp [v]⟩

end GlobalTheory.IsotypicTrace

noncomputable section

namespace GlobalTheory.IsotypicTrace

open ContinuousLinearMap MeasureTheory

variable {G X H : Type} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {π : G →* (H →L[ℂ] H)}

theorem hasSum_copy [MeasurableSpace G] {μ : Measure G} {f : G → ℂ} (hδ : IsIrrUnitary δ)
    (hπ : IsUnitaryRep π) (hR : IsRepOp π μ f (repOp π μ f)) (e : X →ₗᵢ[ℂ] H)
    (he : ∀ g x, e (δ g x) = π g (e x)) (Q : H →L[ℂ] H) (hQ : ∀ g, Q * π g = π g * Q)
    (htr : trace (repOp δ μ f) = 0) (hA : IsTraceClass (repOp π μ f * Q)) :
    HasSum (fun a => ⟪e (stdBasis (H := X) a), (repOp π μ f * Q) (e (stdBasis (H := X) a))⟫_ℂ) 0 := by
  let E : X →L[ℂ] H := e.toContinuousLinearMap
  have he' : ∀ g x, E (δ g x) = π g (E x) := he
  have hEE : ∀ x, adjoint E (E x) = x := fun x => ext_inner_left ℂ fun y => by
    rw [adjoint_inner_right]
    exact e.inner_map_map y x
  have hEa : ∀ g y, adjoint E (π g y) = δ g (adjoint E y) := fun g y =>
    (GlobalTheory.DiscreteSum.adjoint_mem_homIn hδ.unitary hπ (T := E) (mem_homIn_top.2 he')).2 g y
  have hRδ' : IsRepOp δ μ f (adjoint E ∘L repOp π μ f ∘L E) := fun x => by
    have hk : ∀ g, f g • δ g x = adjoint E (f g • π g (E x)) := fun g => by
      rw [map_smul, hEa, hEE]
    simp only [hk]
    refine ⟨(adjoint E).integrable_comp (hR (E x)).1, ?_⟩
    rw [comp_apply, comp_apply, (hR (E x)).2, (adjoint E).integral_comp_comm (hR (E x)).1]
  have hRδ : IsRepOp δ μ f (repOp δ μ f) := by rw [hRδ'.repOp_eq]; exact hRδ'
  have hcomm : ∀ y, adjoint E (repOp π μ f y) = repOp δ μ f (adjoint E y) := fun y => by
    rw [(hR y).2, ← (adjoint E).integral_comp_comm (hR y).1, (hRδ (adjoint E y)).2]
    simp only [map_smul, hEa]
  have hQ' : ∀ g y, Q (π g y) = π g (Q y) := fun g y => DFunLike.congr_fun (hQ g) y
  obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur X G δ hδ.unitary.norm_apply (fun S hS h => hδ.irred.2 S ⟨hS, h⟩)
    (adjoint E ∘L Q ∘L E) fun g => by
      ext x
      change δ g (adjoint E (Q (E x))) = adjoint E (Q (E (δ g x)))
      rw [he', hQ', hEa]
  have hP : adjoint E ∘L (repOp π μ f * Q) ∘L E = c • repOp δ μ f := by
    ext x
    have hx : adjoint E (Q (E x)) = c • x := DFunLike.congr_fun hc x
    change adjoint E (repOp π μ f (Q (E x))) = c • repOp δ μ f x
    rw [hcomm, hx, map_smul]
  have htr' : trace (adjoint E ∘L (repOp π μ f * Q) ∘L E) = 0 := by
    rw [hP, trace_smul, htr, mul_zero]
  have h := (hA.comp_comp (adjoint E) E).hasSum_trace (stdBasis (H := X))
  rw [htr'] at h
  refine h.congr_fun fun a => ?_
  change _ = ⟪stdBasis (H := X) a, adjoint E ((repOp π μ f * Q) (E (stdBasis (H := X) a)))⟫_ℂ
  rw [adjoint_inner_right]
  rfl

end GlobalTheory.IsotypicTrace

namespace GlobalTheory

theorem trace_repOp_mul_eq_zero_of_isIsotypic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ), Integrable f μ → ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (π : G →* (H →L[ℂ] H)), IsIrrUnitary δ → IsUnitaryRep π → GlobalTheory.AutMult.IsIsotypic δ π → ∀ [SecondCountableTopology G] (Q : H →L[ℂ] H), (∀ g, Q * π g = π g * Q) → HasTrace (repOp δ μ f) 0 → IsTraceClass (repOp π μ f * Q) → trace (repOp π μ f * Q) = 0 := by
  intro G _ _ _ _ _ μ f hf X _ _ _ H _ _ _ δ π hδ hπ hiso _ Q hQ htr hA
  by_cases hex : ∃ T, IsRepOp π μ f T
  swap
  · have h0 : repOp π μ f = 0 := by rw [repOp, dite_eq_right hex]
    rw [h0, zero_mul, trace_zero]
  have hR : IsRepOp π μ f (repOp π μ f) := by
    obtain ⟨T, hT⟩ := hex
    rw [hT.repOp_eq]; exact hT
  obtain ⟨ι, e, b, he, hb⟩ := IsotypicTrace.exists_hilbertBasis hδ hπ hiso
  have h1 := hA.hasSum_trace b
  have h2 : ∀ i, HasSum (fun a => ⟪b ⟨i, a⟩, (repOp π μ f * Q) (b ⟨i, a⟩)⟫_ℂ) 0 := fun i => by
    simpa only [hb] using IsotypicTrace.hasSum_copy hδ hπ hR (e i) (he i) Q hQ htr.2 hA
  exact (hasSum_zero.unique (h1.sigma h2)).symm

end GlobalTheory
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceIntegratedOpMulEqZeroOfIsotypicStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (f : G → ℂ), Integrable f μ → ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (δ : G →* (X →L[ℂ] X)) (π : G →* (H →L[ℂ] H)), IsIrrUnitary δ → IsUnitaryRep π → GlobalTheory.AutMult.IsIsotypic δ π → ∀ [SecondCountableTopology G] (Q : H →L[ℂ] H), (∀ g, Q * π g = π g * Q) → HasTrace (repOp δ μ f) 0 → IsTraceClass (repOp π μ f * Q) → trace (repOp π μ f * Q) = 0 := by
  first | exact @GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic | exact GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic | (intros; apply GlobalTheory.trace_repOp_mul_eq_zero_of_isIsotypic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

namespace GlobalTheory

theorem isIsotypic_of_uEquiv_left {G X Y K : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {δ : G →* (X →L[ℂ] X)} {δ' : G →* (Y →L[ℂ] Y)} {ρ : G →* (K →L[ℂ] K)}
    (e : ∃ A : X ≃ₗᵢ[ℂ] Y, ∀ g x, A (δ g x) = δ' g (A x)) (h : IsIsotypic δ ρ) : IsIsotypic δ' ρ := by
  obtain ⟨A, hA⟩ := e
  refine eq_top_iff.2 (h.ge.trans (isoPart_le (Submodule.isClosed_topologicalClosure _) fun T hT x => ?_))
  have hs : ∀ g y, A.symm (δ' g y) = δ g (A.symm y) := fun g y => by
    apply A.injective
    rw [hA g, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hx : T x = (T ∘L (A.symm : Y →L[ℂ] X)) (A x) := by simp
  rw [hx]
  refine apply_mem_isoPart (mem_homIn_top.2 fun g y => ?_) _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hs]
  exact (mem_homIn_top.1 hT) g _

theorem hasDSComp_of_trace_ne_zero : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD H _ _ _ π hπ c hc hc0 τ
  obtain ⟨δ, hδ⟩ := hFl.exists_hasCompPl (isCMExt_host D) (isHermND_gram (V := V)) hπ (.inl (placeOf D τ))
  have hδ' : IsIsotypic (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) δ.π
      (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ
  obtain ⟨c', hc', himp⟩ := GlobalTheory.T.discrete_series_test_function_trace hDS hHC hPC D V lam S M T U μa μf μ fa ff hTD τ δ.H δ.π δ.isIrr
  by_cases hc'0 : c' = 0
  · exfalso
    have hRP : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ := hTD.2.2.2.2.1
    have hmem : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hTD.2.2.2.2.2.1.mem
    have hfin : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
    obtain ⟨Q, hQ, hrep⟩ := GlobalTheory.T.pureTensorOperator_split_oneRealPlace D V μa μf μ hRP fa ff hmem hfin H π hπ.unitary (placeOf D τ)
    haveI : (μa (placeOf D τ)).IsHaarMeasure := hRP.1 _
    have hint : Integrable (fa (placeOf D τ)) (μa (placeOf D τ)) :=
      (continuous_of_mem_ccSmooth (continuous_archCoord _ _ _) (hmem _)).integrable_of_hasCompactSupport (hmem _).1
    have hπw : IsUnitaryRep (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) :=
      isUnitaryRep_comp hπ.unitary (continuous_embArch _ _ _)
    have htc : IsTraceClass (repOp (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) (μa (placeOf D τ)) (fa (placeOf D τ)) * Q) := hrep ▸ hc.1
    let δw : GArch D.sp.cm.sig V.gram (placeOf D τ) →* (δ.H →L[ℂ] δ.H) := δ.π
    have hδirr : IsIrrUnitary δw := δ.isIrr
    have hδw : IsIsotypic δw (π.comp (embArch D.sp.cm.sig V.gram (placeOf D τ))) := hδ'
    have hc'w : HasTrace (repOp δw (μa (placeOf D τ)) (fa (placeOf D τ))) 0 := hc'0 ▸ hc'
    have h0 := GlobalTheory.T.trace_integratedOp_mul_eq_zero_of_isotypic (GArch D.sp.cm.sig V.gram (placeOf D τ)) _ _ hint δ.H H δw _ hδirr hπw hδw Q hQ hc'w htc
    exact hc0 (hc.2.symm.trans (hrep ▸ h0))
  · show IsIsotypic (dsRep M τ) (π.comp (embW V (placeOf D τ)))
    exact isIsotypic_of_uEquiv_left (G := GArch D.sp.cm.sig V.gram (placeOf D τ)) (himp hc'0) hδ'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_spectral_side : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  first | exact @GlobalTheory.hasDSComp_of_trace_ne_zero | exact GlobalTheory.hasDSComp_of_trace_ne_zero | (intros; apply GlobalTheory.hasDSComp_of_trace_ne_zero <;> assumption)
end
