module

public import Formalism.LocalToGlobal.Columns.TiedValRat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram

theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

end GlobalTheory.Core.CoefGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSwapR
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPartIso

section Swap

theorem continuous_bc {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (φ : A →+* B) (h : Continuous φ) : Continuous (bc (n := Fin n) φ) :=
  Continuous.units_map _ (continuous_id.matrix_map h)

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') {g : GL (Fin n) A} (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' J' := by
  have hg' : cT σ g.1 * J * g.1 = J := hg
  have h2 := congrArg (fun M => M.map φ) hg'
  simp only [Matrix.map_mul, hJ] at h2
  have e1 : cT σ' (g.1.map φ) = (cT σ g.1).map φ := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, h]
  change cT σ' (g.1.map φ) * J' * g.1.map φ = J'
  rw [e1]; exact h2

def ujEquiv {A B : Type} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (σ : A →+* A) (σ' : B →+* B) (φ : A ≃+* B) (hc : Continuous φ) (hc' : Continuous φ.symm)
    (h : ∀ x, σ' (φ x) = φ (σ x)) (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin n) (Fin n) B)
    (hJ : J.map φ = J') : UJ σ J ≃ₜ* UJ σ' J' where
  toFun g := ⟨bc φ.toRingHom g.1, bc_mem _ _ φ.toRingHom h _ _ hJ g.2⟩
  invFun g := ⟨bc φ.symm.toRingHom g.1, bc_mem _ _ φ.symm.toRingHom (fun x => φ.injective (by
      change φ (σ (φ.symm x)) = φ (φ.symm (σ' x))
      rw [← h, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])) _ _
      (hJ ▸ Matrix.ext fun _ _ => φ.symm_apply_apply _) g.2⟩
  left_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.symm_apply_apply _))
  right_inv g := Subtype.ext (Units.ext (Matrix.ext fun _ _ => φ.apply_symm_apply _))
  map_mul' g h := Subtype.ext (map_mul (bc φ.toRingHom) g.1 h.1)
  continuous_toFun := ((continuous_bc φ.toRingHom hc).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_bc φ.symm.toRingHom hc').comp continuous_subtype_val).subtype_mk _

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

def swapR : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem continuous_swapR :
    @Continuous _ _ _ (tensTopL (F := F) (E := E) R) (swapR (F := F) (E := E) R) ∧
    @Continuous _ _ (tensTopL (F := F) (E := E) R) _ (swapR (F := F) (E := E) R).symm := by
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) R
  haveI : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd R (E ⊗[F] R)
  haveI := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  let L : R ⊗[F] E ≃ₗ[R] E ⊗[F] R :=
    { (swapR (F := F) (E := E) R).toAddEquiv with
      map_smul' := fun c y => by
        change swapR (F := F) (E := E) R (c • y) = c • swapR (F := F) (E := E) R y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl }
  exact ⟨IsModuleTopology.continuous_of_linearMap L.toLinearMap,
    IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [TopologicalSpace R] in
theorem swapR_sig (x : R ⊗[F] E) :
    Formalism.UG.sigR σ R (swapR R x) = swapR R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def swapU : letI := tensTopL (F := F) (E := E) R; HA R σ J ≃ₜ* UPts σ J R :=
  letI := tensTopL (F := F) (E := E) R
  ujEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapR R) (continuous_swapR R).1 (continuous_swapR R).2
    (swapR_sig R σ) (JR R J) (J.map (inclE (F := F) R)) (Matrix.ext fun _ _ => rfl)

end Swap

section Fin

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def finEquiv : finPts σ J ≃ₜ* GFin σ J where
  toFun g := projFin σ J g.1
  invFun y := ⟨ofFin σ J y, mem_finPts.2 (projInf_ofFin σ J y)⟩
  left_inv g := Subtype.ext (ext_inf_fin σ J ((projInf_ofFin σ J _).trans (mem_finPts.1 g.2).symm)
    (projFin_ofFin σ J _))
  right_inv y := projFin_ofFin σ J y
  map_mul' g h := map_mul (projFin σ J) g.1 h.1
  continuous_toFun := (continuous_projFin σ J).comp continuous_subtype_val
  continuous_invFun := (continuous_ofFin σ J).subtype_mk _

end Fin

theorem exists_finIso : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); ∃ e : ↥(GfC V) ≃ₜ* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), ∀ g, (e g).1.1 = finM V hn g.1 := by
  intro D V n hn
  subst hn
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  exact ⟨(finEquiv D.sp.cm.sig V.gram).trans
    (swapU (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.sp.cm.sig V.gram), fun g => rfl⟩

end GlobalTheory.FinPartIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParam
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section
namespace GlobalTheory.CoverDS

theorem unitEquiv_of_dsUnique : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  intro hU p q hn T R R' lam hl hR hR'
  have h0 : 0 < p + q := hn
  obtain ⟨P, e, -, h, rfl | rfl⟩ := GlobalTheory.RealPar.isParam_cases hl
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_iff_factors R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x]
    exact hV _ (h.cov_mem T x) v
  · obtain ⟨σ, hσ, hP⟩ := (GlobalTheory.RealPar.hasParam_half_iff R h0 P h).1 hR
    obtain ⟨σ', hσ', hP'⟩ := (GlobalTheory.RealPar.hasParam_half_iff R' h0 P h).1 hR'
    obtain ⟨V, hV⟩ := hU (p + q) P.sgn P.lam R.U.H σ R'.U.H σ' P.hc hP hP'
    refine ⟨V, fun x v => ?_⟩
    rw [hσ x, hσ' x, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul]
    rw [hV _ (h.cov_mem T x) v]

end GlobalTheory.CoverDS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam : GlobalTheory.Dec.DSUnique → ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R R' : DSRep T) (lam : Ix p q → ℚ), IsParam lam → HasParam R lam → HasParam R' lam → UnitEquiv R R' := by
  first | exact @GlobalTheory.CoverDS.unitEquiv_of_dsUnique | exact GlobalTheory.CoverDS.unitEquiv_of_dsUnique | (intros; apply GlobalTheory.CoverDS.unitEquiv_of_dsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
noncomputable section

namespace GlobalTheory.SatBc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem satU_eq_of_bcParam_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ,
      GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' →
      ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU α α' e φ hφ
  have e1 := congrArg (Multiset.map fun z : ℂˣ => (z : ℂ)) (add_right_cancel e)
  refine GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq _ (SatU ϖ q φ)
    (fun γ hγ => GlobalTheory.SatakeWeyl.satWeyl L ϖ σ q n (n / 2) hU (by omega) (by omega) γ hγ φ hφ) _ _
    (fun i => (α i).ne_zero) ?_
  simpa [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParameStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' → ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  first | exact @GlobalTheory.SatBc.satU_eq_of_bcParam_eq | exact GlobalTheory.SatBc.satU_eq_of_bcParam_eq | (intros; apply GlobalTheory.SatBc.satU_eq_of_bcParam_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.GelfandTwo

theorem sum_rhoStd_sq (n : ℕ) :
    ∑ a : Fin n, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) = ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.rhoStd, Formalism.BasicNotions.TH.rhoSq]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => (((n : ℂ) - 1) / 2 - (i : ℂ)) * (((n : ℂ) - 1) / 2 - (i : ℂ))) n]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

theorem gelfVal_two (n : ℕ) (lam : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, sum_rhoStd_sq]
  simp only [sq]

end GlobalTheory.GelfandTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEqStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondGelfandInvariant_value_eq : ∀ (n : ℕ) (lam : Fin n → ℂ), GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((rhoSq n : ℚ) : ℂ) := by
  first | exact @GlobalTheory.GelfandTwo.gelfVal_two | exact GlobalTheory.GelfandTwo.gelfVal_two | (intros; apply GlobalTheory.GelfandTwo.gelfVal_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem elementary_size_bounds_of_size_hypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ),
    thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧
    M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧
    (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  intro M
  refine ⟨max 1000 (2 * |M|), ?_⟩
  intro D large₂ C' Cl Cg cb Cu cT CT hC' hCl h
  have hMabs : M ≤ |M| := le_abs_self M
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hCl1000 : 1000 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2M : 2 * |M| ≤ Cl := le_trans (le_max_right _ _) hCl
  have hC'M : M ≤ C' := by linarith [le_trans (le_max_right _ _) hC']
  obtain ⟨-, hk, hmf, hfk, -, -, hm2L, -, -, -, hrd, -, -, -, -, hbj, -, -, -, -, -, -, -, hClm, -⟩ := h
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Formalism.MainNotions.S.log_scb large₂
  have hb2 : 2 ≤ large₂.sc.b := Formalism.MainNotions.S.two_le_scb large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hmkR : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hmk
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hcard : 0 < Fintype.card D.what₂.Tau := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.card_places D, Formalism.MainNotions.LatticeGluingRadicals.d_card D]; omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hcard
  have hb1 := hbj τ 1 le_rfl (by omega)

  have hkb2 : (D.R.k : ℝ) ^ Cl ≤ large₂.sc.b ^ (2 : ℝ) := le_trans (le_trans (le_max_left _ _) hb1.1) hb1.2
  have hb0 : 0 ≤ large₂.sc.b := by linarith

  have hkhalf : (D.R.k : ℝ) ^ (Cl / 2) ≤ large₂.sc.b := by
    have e1 : (D.R.k : ℝ) ^ (Cl / 2) = ((D.R.k : ℝ) ^ Cl) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (by linarith)]; ring_nf
    have e2 : large₂.sc.b = (large₂.sc.b ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hb0]; norm_num
    rw [e1, e2]
    exact Real.rpow_le_rpow (by positivity) hkb2 (by norm_num)
  have hkM : (D.R.k : ℝ) ^ M ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  have hk2 : (D.R.k : ℝ) ^ (2 : ℝ) ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  rw [Real.rpow_two] at hk2
  have hr : (D.R.r : ℝ) ≤ large₂.sc.b := by
    have e : (D.R.r : ℝ) = (D.R.k : ℝ) + D.R.m - 1 := by
      unfold Formalism.BasicNotions.Ranks.r; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring
    rw [e]; nlinarith
  have hmL : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
    have a1 : (D.R.m : ℝ) ^ 2 ≤ Cl * (D.R.m : ℝ) ^ 2 := le_mul_of_one_le_left h0 (by linarith)
    have a2 : Cl * (D.R.m : ℝ) ^ 2 ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by
      have : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right h0 hL.le
      exact mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    rcases le_or_gt D.host.rdE 0 with hneg | hpos
    · linarith
    · have hLCl : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
      have hlog : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlogb]; linarith
      exact (Real.log_le_log_iff hpos (by linarith)).1 hlog
  have hX0 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hMk : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    have a : M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right hC'M hX0
    have e1 : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    have e2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    linarith
  exact ⟨hCl1000, by linarith, by linarith, by linarith, hrdb, hkM, hr, hmL, hMk⟩

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypothesesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_bounds_of_standingHypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧ M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧ (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  first | exact @GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | exact GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses | (intros; apply GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassLatticeSelfDual
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.ClassLatticeSelfDual

section General

open Formalism.UG Formalism.UG.P
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]


omit [NumberField F] [DecidableEq n] [Fintype n] in
theorem mem_span_of_mem_latS (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] (S : Subring (E ⊗[F] R))
    (L : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : (fun i => inclE (F := F) R (x i)) ∈ latS (F := F) R S L) :
    x ∈ Submodule.span E (L : Set (n → E)) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R →ₗ[F] F, φ 1 = 1 := Module.Projective.exists_dual_eq_one F one_ne_zero
  let π : E ⊗[F] R →ₗ[E] E :=
    (TensorProduct.AlgebraTensorModule.rid F E E).toLinearMap ∘ₗ (φ.baseChange E)
  have hπ : ∀ (s : E ⊗[F] R) (a : E), π (s * inclE (F := F) R a) = π s * a := by
    intro s a
    have : s * inclE (F := F) R a = a • s := by
      rw [mul_comm, Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have hπ1 : π 1 = 1 := by
    simp [π, Algebra.TensorProduct.one_def, hφ]
  have key : ∀ u ∈ latS (F := F) R S L, ∀ s : E ⊗[F] R,
      (fun i => π (s * u i)) ∈ Submodule.span E (L : Set (n → E)) := by
    intro u hu
    unfold latS at hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      intro s
      have : (fun i => π (s * inclE (F := F) R (y i))) = π s • y := by
        funext i; rw [hπ]; rfl
      exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span hy)
    | zero =>
      intro s
      have : (fun i => π (s * (0 : n → E ⊗[F] R) i)) = 0 := by funext i; simp
      exact this ▸ zero_mem _
    | add u u' _ _ h h' =>
      intro s
      have : (fun i => π (s * (u + u') i)) = (fun i => π (s * u i)) + fun i => π (s * u' i) := by
        funext i; simp [mul_add]
      exact this ▸ add_mem (h s) (h' s)
    | smul r u _ h =>
      intro s
      have : (fun i => π (s * (r • u) i)) = fun i => π ((s * (r : E ⊗[F] R)) * u i) := by
        funext i; rw [mul_assoc]; rfl
      exact this ▸ h _
  have h := key _ hx 1
  have e : (fun i => π (1 * inclE (F := F) R (x i))) = x := by
    funext i; rw [hπ, hπ1, one_mul]
  rwa [e] at h

theorem eq_globLat (Λ L : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (hL : Module.Finite (𝓞 E) L)
    (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : ∀ x : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔
      (g⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ) :
    L = CS.globLat g Λ := by
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    obtain ⟨p, hp⟩ := Ideal.exists_maximal (𝓞 F)
    let v : HeightOneSpectrum (𝓞 F) :=
      ⟨p, hp.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField F)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h1 : (0 : FiniteAdeleRing (𝓞 F) F) v = (1 : FiniteAdeleRing (𝓞 F) F) v := by rw [h]
    exact (zero_ne_one : (0 : v.adicCompletion F) ≠ 1) h1
  have hG := csGlob_lattice (F := F) Λ hfin hspan g
  have hLs : Submodule.span E (L : Set (n → E)) = ⊤ := by
    rw [eq_top_iff, ← hG.span_eq_top, Submodule.span_le]
    intro x hx
    exact mem_span_of_mem_latS (F := F) _ _ L x ((h _).2 hx)
  ext x
  conv_lhs => rw [← global_lattice_one_holds F E n L hL hLs]
  refine Iff.trans ?_ (h _)
  show ((1⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ _
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

end General

theorem classLattice_selfDual : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (c : (D.fm u).clsP), Submodule.IsLattice D.host.E (K.lat c) ∧ ∀ y, y ∈ K.lat c ↔ ∀ x ∈ K.lat c, Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  intro D u K c
  have e := eq_globLat (F := D.host.F) K.lev.Lb (K.lat c) K.lev.Lb_fin K.lev.Lb_span (K.lat_fin c) (K.y c).1 (K.y_lat c)
  have hdual : ∀ x, x ∈ K.lev.Lb ↔ ∀ y ∈ K.lev.Lb,
      Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramP D) y x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro x
    refine ⟨fun hx => K.lev.Lb_int x hx, fun hx => ?_⟩
    have := K.lev.Lb_dual x hx
    rwa [Nat.cast_one, one_smul] at this
  rw [e]
  exact ⟨(Formalism.UG.P.csGlob_lattice (F := D.host.F) _ K.lev.Lb_fin K.lev.Lb_span _).toIsLattice,
    fun y => GlobalTheory.PointLattice.globLat_selfDual (sigD D) (gramP D) _ hdual K.lev.Lb_fin K.lev.Lb_span _ (K.y c).2 y⟩

end GlobalTheory.ClassLatticeSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumEqGenVal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEq
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCard

section general
variable {G : Type} [Group G]

def dcos (J : Subgroup G) (g : G) : Set G := {x | ∃ a ∈ J, ∃ b ∈ J, x = a * g * b}

theorem dcos_eq_iUnion (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    dcos J g = ⋃ j ∈ R, (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G) := by
  ext x
  simp only [dcos, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨j', ⟨hj'R, hj'⟩, -⟩ := h2 a ha
    refine ⟨j', hj'R, ?_⟩
    have e : (j' * g)⁻¹ * (a * g * b) = ((j' * g)⁻¹ * (a * g)) * b := by group
    rw [e]; exact J.mul_mem hj' hb
  · rintro ⟨j, hjR, hj⟩
    exact ⟨j, h1 j hjR, (j * g)⁻¹ * x, hj, by group⟩

theorem pairwiseDisjoint_cosets (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    (R : Set G).PairwiseDisjoint (fun j => (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G)) := by
  intro j₁ hj₁ j₂ hj₂ hne
  refine Set.disjoint_left.2 fun x hx₁ hx₂ => hne ?_
  simp only [Set.mem_preimage, SetLike.mem_coe] at hx₁ hx₂
  have hm : (j₁ * g)⁻¹ * (j₂ * g) ∈ J := by
    have e : (j₁ * g)⁻¹ * (j₂ * g) = ((j₁ * g)⁻¹ * x) * ((j₂ * g)⁻¹ * x)⁻¹ := by group
    rw [e]; exact J.mul_mem hx₁ (J.inv_mem hx₂)
  have hself : (j₂ * g)⁻¹ * (j₂ * g) ∈ J := by simp
  exact (h2 j₂ (h1 j₂ (Finset.mem_coe.1 hj₂))).unique ⟨Finset.mem_coe.1 hj₁, hm⟩ ⟨Finset.mem_coe.1 hj₂, hself⟩

theorem dcos_inv (J : Subgroup G) (g : G) : dcos J g⁻¹ = Inv.inv ⁻¹' dcos J g := by
  ext x
  simp only [dcos, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by group⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, ?_⟩
    rw [← inv_inv x, h]; group

theorem measure_dcos [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (J : Subgroup G) (hJ : MeasurableSet (J : Set G)) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    μ (dcos J g) = R.card * μ J := by
  rw [dcos_eq_iUnion J g R h1 h2, measure_biUnion_finset (pairwiseDisjoint_cosets J g R h1 h2)
    (fun j _ => measurable_const_mul _ hJ)]
  simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]

theorem card_eq_of_unimodular [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (J : Subgroup G) (hJo : IsOpen (J : Set G)) (hJt : μ J ≠ ⊤) (g : G) (R R' : Finset G)
    (h1 : ∀ j ∈ R, j ∈ J) (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J)
    (h1' : ∀ j ∈ R', j ∈ J) (h2' : ∀ j ∈ J, ∃! j', j' ∈ R' ∧ (j' * g⁻¹)⁻¹ * (j * g⁻¹) ∈ J) :
    R.card = R'.card := by
  haveI : μ.IsInvInvariant := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have h0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have e1 := measure_dcos μ J hJo.measurableSet g R h1 h2
  have e2 := measure_dcos μ J hJo.measurableSet g⁻¹ R' h1' h2'
  rw [dcos_inv, Measure.measure_preimage_inv, e1] at e2
  have h := (ENNReal.mul_left_inj h0 hJt).1 e2
  exact_mod_cast h

end general

theorem card_isReps_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k)
    (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ) :
    IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  intro hR hR'
  letI : MeasurableSpace (GL (A ⊕ D) k) := borel _
  haveI : BorelSpace (GL (A ⊕ D) k) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GL (A ⊕ D) k) := inferInstance
  haveI : LocallyCompactSpace (GL (A ⊕ D) k) := inferInstance
  haveI : SecondCountableTopology (GL (A ⊕ D) k) := inferInstance
  haveI : T2Space (GL (A ⊕ D) k) := inferInstance
  obtain ⟨hJo, hJc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric k A D

  have hRI : ∀ (μ : Measure (GL (A ⊕ D) k)) [μ.IsHaarMeasure] [μ.InnerRegular], μ.IsMulRightInvariant := by
    intro μ _ _
    refine ⟨fun g => ?_⟩
    have h : Measure.modularCharacter g = 1 := by
      refine GlobalTheory.SplitFlip.hom_eq_one_of_center Measure.modularCharacter (fun z hz => ?_) g
      have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
      rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
        Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
      have h2 := congrArg (fun m : Measure (GL (A ⊕ D) k) => m (KO k (A ⊕ D))) h1
      have hne : μ (KO k (A ⊕ D)) ≠ 0 := (GlobalTheory.SplitFlip.isOpen_KO.measure_pos μ ⟨1, one_mem _⟩).ne'
      have hnt : μ (KO k (A ⊕ D)) ≠ ⊤ := GlobalTheory.SplitFlip.isCompact_KO.measure_lt_top.ne
      simp only [Measure.coe_nnreal_smul_apply] at h2
      have h3 : (Measure.modularCharacterFun z : ENNReal) = 1 :=
        (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
      exact_mod_cast h3
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]
  haveI := hRI (Measure.haar : Measure (GL (A ⊕ D) k))
  refine ⟨card_eq_of_unimodular (Measure.haar : Measure (GL (A ⊕ D) k)) (parahoric k A D) hJo
    hJc.measure_lt_top.ne g R R' (fun j hj => (hR.1 j hj).1) hR.2
    (fun j hj => (hR'.1 j hj).1) hR'.2, ?_⟩
  obtain ⟨j', ⟨hj', -⟩, -⟩ := hR.2 1 (one_mem _)
  exact ⟨j', hj'⟩

end GlobalTheory.ParHeckeCard
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardParahoricDoubleCosetRepsInvEqStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ), IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  first | exact @GlobalTheory.ParHeckeCard.card_isReps_inv | exact GlobalTheory.ParHeckeCard.card_isReps_inv | (intros; apply GlobalTheory.ParHeckeCard.card_isReps_inv <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem mtor_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ (-e) : GL (A ⊕ D) k) = (mtor ϖ e)⁻¹ := by
  unfold mtor torusElt
  rw [← map_inv]
  congr 1
  funext i
  rcases i with i | i <;> simp [_root_.zpow_neg]

theorem sum_eq_genVal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ) (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ), IsReps (mtor ϖ (-indic s)) R d → ∑ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * mtor ϖ (-indic s)) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b ⟨datum ξ⁻¹, hΦ⟩ x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR
  set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg
  have hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹ := mtor_neg ϖ (indic s)
  rw [hginv] at hR ⊢
  set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef

  have h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x) := by
    intro j hj
    obtain ⟨hjJ, hdj⟩ := hR.1 j hj
    have hjiJ : j⁻¹ ∈ parahoric k A D := inv_mem hjJ
    have hne := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1
    have hprod := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl
    have hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x := hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl
    have he := hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)
    have hone : (j * g⁻¹) * (g * j⁻¹) = 1 := by group
    rw [← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      map_mul, Module.End.mul_apply, hx1, map_smul, map_smul] at he
    rw [show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl,
      he, smul_smul, hprod, one_smul]

  have htame : IsTame ξ⁻¹ := fun y hy => by simp [hξ y hy]
  have hunr : IsUnram (μT⁻¹ * ξ) := fun y hy => by
    have := hμ y hy
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
    rw [← inv_inv (ξ y), ← mul_inv, this, inv_one]
  have h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z := by
    intro j hj dd hdd z
    have hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹ := by
      have := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd
      rw [show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]] at this
      unfold omTwo
      rw [this]
      funext y
      simp
    have he := hb j 1 Φ z
    have hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ := Subtype.ext hom
    rw [hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply] at he
    rw [← he, smul_smul]
    simp

  obtain ⟨R'', d'', hR''⟩ := (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g
  have hcard := (GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1
  have hT := hx.2.2 s R'' d'' hR''
  have hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_smul, hT, map_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjJ, hdj⟩ := hR''.1 j hj
    rw [map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply,
      h2 j hjJ (d'' j) hdj, smul_smul]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]

end GlobalTheory.ParHeckeTransfer
end
end
