module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialBoundSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalStepObjectsOfCyclotomicGeneratorIner
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalSlotDataOffExceptionalPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfLargeResidueChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParametersExcludedPrimesFewAndSmallAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremECorollaryAClosingAllData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJointBCD
public import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
public import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
public import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
public import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsADInSettingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
def RowCAlt (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowAt (Fm.L x i) X.ρ A B
def StarSelfDualCondition : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      StarS (Fm.L x i) X.ρ C
end UpperTheory.N
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NStarS
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfSetup
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.n_at_bounds_of_setup (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) :
    UpperTheory.N.RowAt L X.ρ 6000 30000 := by
  intro i hTw hs h2 π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hgk : ∀ k, D.nd.l i ≠ D.host.g k := fun k e =>
    UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k) (e ▸ hs)
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hgk 0, hgk 1⟩
  have hL : EmbeddingTypes.hypL i := ⟨by have := hl.two_le; omega, Or.inr hs, fun h => absurd hs h, hgk 0, hgk 1⟩
  have hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1 :=
    D.host.QS_split _ hl h2 (Nat.dvd_of_mem_primeFactors hs)
  obtain ⟨dc, -, h⟩ := _root_.UpperTheory.N.conclusion_split_alt hP D L P nch HW F Cm X C₂ S i hg D.host.condN
    (UpperTheory.N.cycAt_of i fun e => absurd e h2) hL (UpperTheory.N.decl_split D i h2 hj) (UpperTheory.N.locAll hP D HW F Cm (D.nd.l i))
  obtain ⟨hB, hW, hz⟩ := h π hπ
  have hs1 : 1 ≤ D.nd.s0 i := by rw [D.nd.restNLevelExponent_of_odd i h2]; exact le_max_left _ _
  have hh := UpperTheory.N.h0_le D i dc.col (fun e => absurd e h2) hs1 (fun u hu => (dc.cover u).1 (Or.inr hu))
  have hb := UpperTheory.N.Num.one_le_b L
  have hbB : L.sc.b ≤ RowSmall.hB L := (UpperTheory.N.Num.hB_bounds L P).1
  have hf : (⌊2 * L.sc.b⌋₊ : ℝ) ≤ 2 * L.sc.b := Nat.floor_le (by linarith)
  refine UpperTheory.N.bound_smallPrime_of_splitBound_cyclotomic L P X.ρ S.kill S.sha i hTw hs π hπ dc _ _ _ ?_ ?_ ?_ hW (by exact_mod_cast hh) hz hB
  · have : (Formalism.MainNotions.N.hN L : ℝ) ≤ RowSmall.hB L := Nat.floor_le (by
      show 0 ≤ RowSmall.hB L
      linarith)
    linarith
  · unfold GlobalTheory.HubX.hOf
    push_cast
    linarith
  · linarith
theorem UpperTheory.N.exists_nonneg_c_constants_of_prints : Hypotheses₂ → ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.RowCAlt A B :=
  fun hP => ⟨6000, 30000, by norm_num, by norm_num, fun Fm => ⟨0, fun x _ hx i HW F Cm X C₂ S =>
    _root_.UpperTheory.N.n_at_bounds_of_setup hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ S⟩⟩
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowGlue
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
variable {D : D7}
end UpperTheory.N
theorem UpperTheory.N.starSF_of_rowC_alt (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) : _root_.UpperTheory.N.RowCAlt A B → _root_.UpperTheory.N.StarSelfDualCondition := by
  intro h eps Fm
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1),
    fun x hxx hx i HW F Cm X C₂ hS k hTw hs h2 π hπ => ?_⟩
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hs h2 π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hc : UpperTheory.N.costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    UpperTheory.N.Num.cost_le (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hs le_rfl
  unfold Bd at hb ⊢
  linarith
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.starSF_of_prints (hP : Hypotheses₂) : _root_.UpperTheory.N.StarSelfDualCondition := by
  obtain ⟨A, B, hA, hB, h⟩ := _root_.UpperTheory.N.exists_nonneg_c_constants_of_prints hP
  exact _root_.UpperTheory.N.starSF_of_rowC_alt A B hA hB h
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PolynomialBoundSetup
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfAltAlt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherSide
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.HostJumpWin
open Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
open Classical in
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  intro _ D L P nch HW F Cm X C₂ S ep hJa
  obtain ⟨-, hJb, hJc, -⟩ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (S.facts.admJ L S.par)
  intro i _ w hw C τ
  obtain ⟨g, ρ, hR, hjx, -⟩ := hJa i (X.r i) (S.canon.fam.good i) w hw C τ
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  obtain ⟨hlo, hhi⟩ := sz_bounds L P S.par (D.nd.j i) hj1 hj2 ρ
  have hUp : EmbeddingTypeJumps.UpAt ep C τ → AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ =>
    typeU_of_emb i C τ g ρ hR ep τ₀ h0 e0
  have hDn : EmbeddingTypeJumps.DownAt ep C τ → ¬ AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ h => by
    have h' := typeU_of_emb i C τ g ρ hR (!ep) τ₀ h0 e0
    unfold AdmissibleParameterJ.TypeU at h h'
    cases ep <;> simp_all
  obtain ⟨s, Jc, Jl, h1, h2, h3, h4, h5, hpos, hneg, hJJ⟩ :=
    key_sets L hJb hJc (D.nd.j i) hj1 hj2 ρ (decide (AdmissibleParameterJ.TypeU D ep g)) hlo hhi
  refine ⟨s, Jc, Jl, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_⟩
  · by_cases ht : AdmissibleParameterJ.TypeU D ep g
    · left; exact hpos (by simp [ht])
    · right; exact hneg (by simp [ht])
  · intro hu; exact hpos (by simp [hUp hu])
  · intro hd; exact hneg (by simp [hDn hd])
  · intro x a
    exact ((hjx x a).1).trans (hJJ a)
end GlobalTheory.HostJumpWin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherSideStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeJumpParameters_of_setup : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  first | exact @_root_.GlobalTheory.HostJumpWin.main_alt_alt | exact _root_.GlobalTheory.HostJumpWin.main_alt_alt | (intros; apply _root_.GlobalTheory.HostJumpWin.main_alt_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.TheoremBQD
open MvPolynomial
theorem main_of_alt (hc : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp) : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  refine ⟨2080, polyB, ?_⟩
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : (0 : ℝ) ≤ L.sc.b := (Real.exp_pos _).le
  have hX := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by have := hS.big; linarith) le_rfl (by simpa using hb) (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  have hSet := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS
  have hpt : ∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := fun i hi π hπ =>
    hSet i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ
  obtain ⟨ep, hep⟩ := (_root_.GlobalTheory.JumpStatement.holds_all_alt D L (hS.facts.admJ L hS.par)).1
  have hJ := _root_.GlobalTheory.T.hodgeJumpParameters_of_setup hP D L P nch HW F Cm X C₂ hS ep hep
  have hSt := GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems hP.artin hP.bk hP.tate hP.euler D (GlobalTheory.DesignUnconditional.main D hS.facts.large.2.2)
  have hN5 : EmbeddingTypeJumps.GlobalIndexAwayFromTypes X.r X.ρ := fun i π dc lenRow e' cB hA =>
    hSt.1 i (X.r i) (X.ρ i) π dc lenRow e' cB (hX.1 i) hA
  have hKill : EmbeddingTypeJumps.KillingTwistedPlaces X.ρ := by
    intro i hl htw _ π hπ
    have hk := hS.kill i htw
    have h2 := UpperTheory.KStar.nuL_eq_zero_of_qd D _ hl
    refine ⟨?_, ?_⟩
    · have := (hk.1 π hπ).2
      simpa [h2, TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div] using this
    · simpa [TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div, EmbeddingTypeJumps.vZeta] using hk.2
  refine (hc hP.artin hP.bk hP.tate hP.euler D HW F Cm X.r X.ρ L ep 2080 polyB le_rfl polyB_val hN5
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).1)
    (fun i hi π hπ => (hpt i hi π hπ).2.1)
    (fun i hi π hπ => (hpt i hi π hπ).2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.2.1)
    (fun i hi π hπ => by
      obtain ⟨-, -, -, -, -, -, -, -, hc1, hs1, hd1, he1, -⟩ := hpt i hi π hπ
      exact ⟨hc1, hs1, hd1, he1⟩)
    hKill hJ hX.2.2.1
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.1)
    hS.par67).2.2
theorem main_alt_alt : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q :=
  _root_.GlobalTheory.TheoremBQD.main_of_alt GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality
end GlobalTheory.TheoremBQD
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_jumps_aux2_of_setup : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  first | exact @_root_.GlobalTheory.TheoremBQD.main_alt_alt | exact _root_.GlobalTheory.TheoremBQD.main_alt_alt | (intros; apply _root_.GlobalTheory.TheoremBQD.main_alt_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleParameterEventually
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraMore
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraMore
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
noncomputable section
namespace GlobalTheory.AdmGTwoLarge
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  intro hF D L nch i r π ρ hf hP _ hg _ hr hπ hρ
  have hJ := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (hf.admJ L hP)
  have hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := by
    obtain ⟨-, e, he⟩ := hρ
    exact ⟨e, fun g u => he g u⟩
  exact _root_.GlobalTheory.GTwoTheta.main_alt_alt hF D L hf.g2.1 hJ.1 hJ.2.2.1 i r (fun _ => ρ) π hr (hg 0) (hg 1) hπ hD
end GlobalTheory.AdmGTwoLarge
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraMoreStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG2_of_isRankR_of_lStar_lt : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → AdmissibleParameterJ.AdmPar L → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG2 i r (fun _ => ρ) π := by
  first | exact @_root_.GlobalTheory.AdmGTwoLarge.main_alt_alt | exact _root_.GlobalTheory.AdmGTwoLarge.main_alt_alt | (intros; apply _root_.GlobalTheory.AdmGTwoLarge.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpBoundOfFactsLargeFamily
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpBoundOfFactsLargeFamily
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.LargeJumps
theorem jump_bound_of_facts_large_family_alt : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
    _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  intro eps Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a hF => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  have hA := (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
  exact _root_.GlobalTheory.JumpStatement.holds_all_alt _ _ (hF.admJ _ hA)
end GlobalTheory.LargeJumps
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpBoundOfFactsLargeFamilyStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_prvJ_of_facts : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  first | exact @_root_.GlobalTheory.LargeJumps.jump_bound_of_facts_large_family_alt | exact _root_.GlobalTheory.LargeJumps.jump_bound_of_facts_large_family_alt | (intros; apply _root_.GlobalTheory.LargeJumps.jump_bound_of_facts_large_family_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraTer
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraTer
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
noncomputable section
namespace GlobalTheory.AdmGThreeRest
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  intro D L nch i r π ρ fa _ _ hHG hr _ hρ
  obtain ⟨hcont, e, he⟩ := hρ
  have hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r (fun _ => ρ) π := ⟨e, fun g u => he g u⟩
  exact _root_.Formalism.MainNotions.N.galois_condition_three_of_alt_alt D i r (fun _ => ρ) π fa.Conclusion1.1 hr hdec hcont hHG fa.rhoBar (litBurnside_host D)
    (fa.duties.2.1 i r hr)
end GlobalTheory.AdmGThreeRest
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraTerStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG3_of_isRankR_of_lStar_lt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG3 i r (fun _ => ρ) π := by
  first | exact @_root_.GlobalTheory.AdmGThreeRest.main_alt_alt | exact _root_.GlobalTheory.AdmGThreeRest.main_alt_alt | (intros; apply _root_.GlobalTheory.AdmGThreeRest.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurther
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurther
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurtherStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  first | exact @_root_.GlobalTheory.UnrNoChi.main_alt_alt | exact _root_.GlobalTheory.UnrNoChi.main_alt_alt | (intros; apply _root_.GlobalTheory.UnrNoChi.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraExtra
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraExtra
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.TheoremFiveAtS
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v := by
  intro D L nch i r π ρ hF _ _ hHG hr _ _ v hv
  have hIne : TruncatedSeriesCountingIdentities.admG5 i r := galois_condition_five_of D i r hF.Conclusion2.1 hHG hr
  have hTame : TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := (GlobalTheory.TameDesign.main D i).2
  have hS := ((D.nd.S_def i v).1 hv).1
  have hvI := hIne v (Or.inl hv)
  have hvT := hTame v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hvI.2 hk hv hvT.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hvI.1 (Or.inr hp)) x).1 γ hγ, hvT.2.2.2 hv hp⟩
end GlobalTheory.TheoremFiveAtS
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraExtraStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadAt_unit_zeta_sub_one_or_polyAt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v := by
  first | exact @_root_.GlobalTheory.TheoremFiveAtS.main_alt_alt | exact _root_.GlobalTheory.TheoremFiveAtS.main_alt_alt | (intros; apply _root_.GlobalTheory.TheoremFiveAtS.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraRest
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraRest
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.QuadAtQ
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  intro D L nch i r π ρ fa _ _ hHG hr _ _ v hv
  exact ⟨fun x _ γ hγ => ((galois_condition_five_of D i r fa.Conclusion2.1 hHG hr v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ,
    ((GlobalTheory.TameDesign.main D i).2 v (Or.inr hv)).2.2.1 hv⟩
end GlobalTheory.QuadAtQ
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraRestStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → ∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1 := by
  first | exact @_root_.GlobalTheory.QuadAtQ.main_alt_alt | exact _root_.GlobalTheory.QuadAtQ.main_alt_alt | (intros; apply _root_.GlobalTheory.QuadAtQ.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraBis
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
namespace GlobalTheory.AdmissibleSetting
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  intro D L nch i r π ρ fa _ _ _ hr _ _
  exact ⟨_root_.Formalism.MainNotions.N.galois_condition_one_of_alt D i r fa.Conclusion1.1 hr, Formalism.MainNotions.N.continuous_family_of D i r hr,
    Formalism.MainNotions.N.semisimple_family_of D i r hr⟩
end GlobalTheory.AdmissibleSetting
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraBisStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r := by
  first | exact @_root_.GlobalTheory.AdmissibleSetting.main_alt_alt | exact _root_.GlobalTheory.AdmissibleSetting.main_alt_alt | (intros; apply _root_.GlobalTheory.AdmissibleSetting.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleParameterEventually
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
private theorem admissible_parameter_eventually {eps : ℝ} (Fm : FamP eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (a : Fm.Ix x), AdmissibleParameterJ.AdmPar (Fm.L x a) := by
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  exact (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
theorem GlobalTheory.NLinkE.main_alt_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  intro hP eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.T.exists_localPositionData_off_exceptional_primes Fm
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.T.eventually_prvJ_of_facts Fm
  obtain ⟨x3, h3⟩ := admissible_parameter_eventually Fm
  refine ⟨max (max x1 x2) x3, fun x hx' hx1 a hF => ?_⟩
  have hx : max x1 x2 ≤ x := le_trans (le_max_left _ _) hx'
  have hA := h3 x (le_trans (le_max_right _ _) hx') hx1 a
  have hJ := h2 x (le_trans (le_max_right _ _) hx) hx1 a hF
  intro k hl hg hexc _hW hHG r hr π hπ ρ hρ
  have hlp : (Fm.D x a).nd.l k |>.Prime := ((Fm.D x a).nd.lPrime k).out
  obtain ⟨⟨h5, ht, hq, hd, hsm⟩, hposition⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 a hJ _ hlp hl
  have hur := GlobalTheory.TripleGal.host_ramificationIdx_eq_one (Fm.D x a) _ hlp hsm hq hd
  have heps := GlobalTheory.AdmissibleDictionary.main (Fm.D x a) k
  obtain ⟨g1, gc, gss⟩ := _root_.GlobalTheory.T.admG1_continuous_admSS_of_rank_r_summand _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g3 := _root_.GlobalTheory.T.admG3_of_isRankR_of_lStar_lt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have g2 := _root_.GlobalTheory.T.admG2_of_isRankR_of_lStar_lt hP.font _ _ _ k r π ρ hF hA hl hg hHG hr hπ hρ
  obtain ⟨gno, gunr⟩ := _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gS := _root_.GlobalTheory.T.quadAt_unit_zeta_sub_one_or_polyAt _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gQ := _root_.GlobalTheory.T.quadAt_and_zeta_ne_one_of_large_place _ _ _ k r π ρ hF hl hg hHG hr hπ hρ
  have gdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition k r (fun _ => ρ) π := hρ.2
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_globalStep_objects_of_cyclotomic_generator_inertia _ k r (fun _ => ρ) π hr g1 g3 gc gss gdec heps g3.2.2 hπ hur ht
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x a)
  have hTOP := GlobalTheory.T.blochKatoTop_of_localTateDuality_eulerChar hP.bk hP.tate hP.euler (Fm.D x a) HW F Cm
  have hloc := GlobalTheory.UseLoc.main (Fm.D x a) HW F k r (fun _ => ρ) π hTOP (GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists _ HW F) hJ.1 hr hπ g2 g3 gc gdec heps h5 hsm hq hd
    (fun n _ up τ => hposition hexc _ ((Fm.D x a).nd.j_range k).1 ((Fm.D x a).nd.j_range k).2 n up τ)
  exact GlobalTheory.T.congruenceBound_extended_of_rationalBound _ k π ρ hπ (fun v hv => (gQ v hv).2)
    (fun hs hsha => GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit hP.artin _ k r _ π S hr hS hπ gno gunr gS gQ hloc hs hsha)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleParameterEventuallyStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_congBound_of_facts : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), _root_.GlobalTheory.NFacts.NormChoiceFacts (Fm.D x i) (Fm.ex x hx i).nch → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at (Fm.D x i) (Fm.L x i) := by
  first | exact @_root_.GlobalTheory.NLinkE.main_alt_alt | exact _root_.GlobalTheory.NLinkE.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkE.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaLocLeRhs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaLocLeRhs
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
theorem etaLoc_le_rhs_alt (hPr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) (constantSecondHub : ℝ) (CT : ℕ)
    (hCT : (CT : ℝ) ≤ L.sc.b) (h68 : _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT) (hG : SizeG L)
    (i : D.nd.Loc) (hi : TwistedPlaces.TwLoc D i) (k k' : Fin 2) (hkk : k ≠ k') (hlk : D.nd.l i = D.host.g k) :
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * PairedCharacterCondition.rhs constantSecondHub X.eta i (X.ρ i) π := by
  by_cases hHG : HG D.nd D.naut i
  · have hX := _root_.GlobalTheory.T.split_bound_of_params_alt hPr.font hPr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 CT hS.canon P
      (by linarith [hS.big]) (by norm_num) hCT (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
      hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
      hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hX
    obtain ⟨hgood, hZρ, s, S, sg, U, hs, hCTg, hsg, hHJ⟩ := hT i k hi hlk hHG
    have hAN : SumRepresentations.adm5 D := hS.facts.toCore.admA.2.2.2.2.2.2
    have hl2 : 2 < D.nd.l i := hlk ▸ g_two_lt L hG k
    have hodd : Odd (D.nd.l i) := (D.nd.lPrime i).out.odd_of_ne_two (by omega)
    have hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) := by
      have h1 := (hG k' k).2.1
      have hg0 : (0 : ℝ) < D.host.g k' := by exact_mod_cast (D.host.g_prime k').pos
      have hg2 : (2 : ℝ) ≤ D.host.g k := by exact_mod_cast (D.host.g_prime k).two_le
      have h2 := Real.log_le_log hg0 h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.log 2 ≤ Real.log (D.host.g k : ℝ) := Real.log_le_log (by norm_num) hg2
      linarith
    have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
      intro e he
      rw [Finset.mem_Ioo] at he
      exact lt_top_iff_ne_top.2 (hS.sha (D.nd.l i) e he.1 he.2)
    exact h68 i k k' hkk hlk (X.r i) (X.ρ i) hgood
      (fun π hπ => semisimple_decomposition_of D i (X.r i) (X.ρ i) π hAN hgood (hZρ π hπ).1 (hZρ π hπ).2)
      X.eta s S sg U hs hlog hCTg hsg hHJ (fun π hπ => ((hS.kill i hi).1 π hπ).1) hsha
  · have hZ : D.nd.Zgood i = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx => hHG ⟨x, (D.Zgood_tie i x).1 hx⟩
    have hP := TruncatedSeriesCountingIdentities.endomorphism_index_bound i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) 0 1 one_ne_zero
      (fun f => by simp) (fun x hx => by rw [hZ] at hx; simp at hx) (fun x _ _ u _ => by simp)
    rw [← TruncatedSeriesCountingIdentities.Br.etaLoc_eq, hZ, Finset.sum_empty] at hP
    rw [hZ, Finset.sum_empty]
    exact_mod_cast hP
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  intro hPr D L P nch HW F _ X C₂ hS constantSecondHub C1 CT hC68 hC1 hCT h68 hmult hpar hG
  have heta : (X.eta : ℝ) ≤ L.etaSz := by
    rw [hS.canon.eta]
    exact Nat.floor_le (by linarith [TwistedPlaces.one_le_eta L P])
  have hM : ∀ l ∈ TwistedPlaces.gset D, 0 ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz +
      TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l := by
    intro l _
    have h1 : 0 ≤ L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have h2 : 0 ≤ L.etaSz := by linarith [TwistedPlaces.one_le_eta L P]
    have h3 : 0 ≤ TwistedPlaces.epsL l := by unfold TwistedPlaces.epsL; positivity
    have h4 : 0 ≤ TwistedPlaces.VVr D l := by
      show (0 : ℝ) ≤ ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ)
      exact_mod_cast Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e
    have h5 : 0 ≤ TwistedPlaces.vhE D l := by unfold TwistedPlaces.vhE; positivity
    have h6 : 0 ≤ 2000 * (constantSecondHub + 1) + 5 * C1 := by linarith
    have := mul_nonneg (mul_nonneg h6 h1) h2
    linarith
  refine starH_of_local L _ (fun i hi hl => ?_) hM hmult (hS.facts.toCore.a3 L)
  have hk : ∃ k k' : Fin 2, k ≠ k' ∧ D.nd.l i = D.host.g k := by
    unfold TwistedPlaces.gset at hl
    rcases Finset.mem_insert.1 hl with h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨1, 0, by decide, Finset.mem_singleton.1 h⟩
  obtain ⟨k, k', hkk, hlk⟩ := hk
  have hl2 : D.nd.l i ≠ 2 := by have := g_two_lt L hG k; omega
  refine (_root_.GlobalTheory.NLinkTyp.etaLoc_le_rhs_alt hPr D L P nch HW F X C₂ hS constantSecondHub CT hCT h68 hG i hi k k' hkk hlk).trans ?_
  refine Finset.sum_le_sum fun π hπ => ?_
  exact mul_le_mul_of_nonneg_left (rhs_le L P X constantSecondHub C1 hC68 hC1 hpar heta hS.kill i hi
    (by rw [hlk]; exact UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k))
    (UpperTheory.KStar.nuL_eq_zero_of_g D _ (by rw [hlk]; fin_cases k <;> simp [TwistedPlaces.gset]) hl2) π hπ) (Nat.cast_nonneg _)
end GlobalTheory.NLinkTyp
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaLocLeRhsStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_bound_of_paired_character_condition : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  first | exact @_root_.GlobalTheory.NLinkTyp.main_alt_alt | exact _root_.GlobalTheory.NLinkTyp.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkTyp.main_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHubData
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepsCuspidal
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltTer
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.GaloisFromAdm
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (_root_.UpperTheory.GalS.weak' h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
  rfl
end GlobalTheory.GaloisFromAdm
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepsCusp_of_adm2 : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  first | exact @_root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | exact _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.GaloisFromAdm.main_alt_alt_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem exists_canonical_hubData_with_bounds : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (_root_.GlobalTheory.T.galoisRepsCusp_of_adm2 D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _
end GlobalTheory.HubX
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem exists_setup_large_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  intro hP eps Fm C C₂ CT hTw hF
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨xa, hxa⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) he
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm 1 le_rfl
  obtain ⟨xc, hxc⟩ := hTw
  refine ⟨max xa (max xb xc), fun x hx hx1 i hsha exc => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, N0, S, hgood⟩ := hxc x hxc' hx1 i
  obtain ⟨hfa, -⟩ := hF x hx1 i
  obtain ⟨HW, F, ⟨Cm⟩⟩ := GlobalTheory.T.exists_wachFunctor_comparison_of_bhattScholze hP.bs (Fm.D x i)
  have hCLw : (Fm.params x hx1 i).CLw ≤ Fm.PK.getD 7 0 := by
    rw [← Fm.params_K x hx1 i]
    exact le_refl _
  have hsx : xa ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hxa'
  obtain ⟨hpar, hpar67⟩ := hxa (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i) (Fm.L_eps x i) hCLw hsx
  obtain ⟨X, hcan, -, hexc, hI, -⟩ := _root_.GlobalTheory.HubX.exists_canonical_hubData_with_bounds GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.L x i) HW (rowC C₂)
    hfa.adm.1.1.2.2.2.1 hfa.Conclusion1.1 (fun _ _ _ _ => 0) (fun _ => exc) ⟨twE Fm x hx1 i, N0, S⟩
  obtain ⟨-, hbig, hsplit, -⟩ := hxb x hxb' hx1 i
  have hrow : GlobalTheory.PtCore.GoodPtRow (Fm.D x i) :=
    GlobalTheory.Proof.LocalGlobalAssembly.main _ hfa.adm.1.1.1 hfa.Conclusion1.2.2 hfa.Conclusion2.2.2
  have h6 := GlobalTheory.JointSix.main GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.ex x hx1 i).nch X.r X.ρ hcan.fam hfa.nct hfa.trip
    hfa.same hrow (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar)
  have hkill : KillingConditions.KillAt X.ρ := GlobalTheory.T.chosenTwist_annihilates_selmerGroups (Fm.D x i) (Fm.ex x hx1 i).nch X.I X.ρ hfa.nct (hI ▸ hgood) h6
  exact ⟨HW, F, Cm, X, hexc, hfa.admJ _ hpar, ⟨hfa, hcan, hpar, hpar67, hbig, hsplit, hkill, hsha⟩⟩
end GlobalTheory.NLink
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLargeStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hubData_admJ_setup : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  first | exact @_root_.GlobalTheory.NLink.exists_setup_large_alt | exact _root_.GlobalTheory.NLink.exists_setup_large_alt | (intros; apply _root_.GlobalTheory.NLink.exists_setup_large_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamJointBCDClosed
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.HTW.LJ
end GlobalTheory.HTW.LJ
namespace GlobalTheory.HTW.RecS
theorem fam_jointBCD_closed_alt : GlobalTheory.Published.FontaineBcris → (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → (∀ D : D7, @_root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D) → ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x j) → GlobalTheory.PtCore.PtFam (Fm.D x j) X.r X.ρ → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro hF h7 hFo hJ eps Fm R
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_jointBCD Fm R h7 hFo
  refine ⟨x0, fun x hx h1 j HW X hA hX => h x hx h1 j HW X (hJ _ _ hA).1 fun i _ hi π hπ => ?_⟩
  refine _root_.GlobalTheory.T.ptIn_of_ptFam_deRham_away hF _ X hX hA.1 i ?_ π hπ
  simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨GlobalTheory.T.inert_prime_ne_typePrime _ _ 0 hi, GlobalTheory.T.inert_prime_ne_typePrime _ _ 1 hi⟩
end GlobalTheory.HTW.RecS
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTail
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLinkClose
theorem main_alt_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT →
    _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm → ConclF Fm := by
  intro hP eps Fm C CT hC0 hTw hF h23
  obtain ⟨C₀, h03⟩ := GlobalTheory.T.theoremE_corollaryA_closing_all_data hP.bk hP.tate hP.euler
  obtain ⟨constantFirstHub, Q, h67⟩ := _root_.GlobalTheory.T.embedding_jumps_aux2_of_setup
  obtain ⟨C1, xpar, hC1, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  obtain ⟨Ca, xa, ha⟩ := h23
  obtain ⟨Cb, xb, hb'⟩ := _root_.UpperTheory.N.starSF_of_prints hP Fm
  set ComplexParameterFamilyContinuity : ℝ := max 0 (max Ca Cb) with hC23def
  set x23 : ℝ := max 1 (max xa xb) with hx23def
  set C₂ : ℝ := max C₀ 1 with hC₂def
  set Cs : ℝ := max (3 * C₂ + 1) (max 22365 (max (FamilyRepresentationConstants.CG constantFirstHub Q) (max (2000 * (C + 1) + 5 * C1)
    (max C1 (max ComplexParameterFamilyContinuity (CT : ℝ)))))) with hCsdef
  have hA : 3 * C₂ + 1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hK : (22365 : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hG : FamilyRepresentationConstants.CG constantFirstHub Q ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hT : 2000 * (C + 1) + 5 * C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hP1 : C1 ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have h23C : ComplexParameterFamilyContinuity ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCT : (CT : ℝ) ≤ Cs := by simp only [hCsdef, le_max_iff, le_refl, true_or, or_true]
  have hCs1 : (1 : ℝ) ≤ Cs := by linarith
  have hCs0 : (0 : ℝ) ≤ Cs := by linarith
  have hC₂1 : (1 : ℝ) ≤ C₂ := le_max_right _ _
  have hC₂0 : C₀ ≤ C₂ := le_max_left _ _
  have hRle : (rowC C₂).Le Cs := by
    simp only [KillingConditions.RowK.Le, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃, rowC]
    refine ⟨hC₂1, ?_, ?_, ?_, hCs1, hA, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨xset, hset⟩ := _root_.GlobalTheory.T.exists_hubData_admJ_setup hP Fm C C₂ CT hTw hF
  obtain ⟨xexc, hexc⟩ := GlobalTheory.T.excludedPrimes_few_and_small_along_family Fm
  obtain ⟨xsm, hsm⟩ := GlobalTheory.T.specialPrimes_small_along_family Fm Cs hCs1
  obtain ⟨xE, hE⟩ := _root_.GlobalTheory.T.eventually_congBound_of_facts hP Fm
  obtain ⟨xbcd, hbcd⟩ := _root_.GlobalTheory.HTW.RecS.fam_jointBCD_closed_alt hP.font GlobalTheory.Per.FontaineAll.fontaine_bounds
    GlobalTheory.FontaineAdm.fontaineProperties_all_places _root_.GlobalTheory.JumpStatement.holds_all_alt Fm (rowC C₂)
  refine ⟨Cs, max xset (max xexc (max xsm (max xE (max xbcd (max xpar x23))))), ?_⟩
  intro x hx0 hx i hSha
  simp only [ge_iff_le, max_le_iff] at hx0
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx0
  obtain ⟨exc, hexcEq, hexcOK⟩ := hexc x h2 hx i
  obtain ⟨HW, F, Cm, X, hXexc, hAdmJ, hS⟩ := hset x h1 hx i hSha exc
  obtain ⟨hFa, hEx⟩ := hF x hx i
  obtain ⟨hSm, -, -, hb⟩ := hsm x h3 hx i
  have hBCD := hbcd x h5 hx i HW X hAdmJ hS.canon.fam
  have hmid := _root_.GlobalTheory.T.star_ad_and_bb_le_of_joint_cond hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS hC₂1
    ((h03 (Fm.D x i) HW F Cm).2 C₂ hC₂0) hBCD
  have hparC1 := hpar x h6 hx i
  have hmult := GlobalTheory.T.goodPointMultiplicityLeRank_proof (Fm.D x i) (Fm.L x i) hFa.Conclusion1.2.2 hFa.Conclusion2.2.2 hFa.toCore.isot hFa.c2
  have hSizeG : SizeG (Fm.L x i) := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hCTb : (CT : ℝ) ≤ (Fm.L x i).sc.b := le_trans hCT hb
  have htyp := _root_.GlobalTheory.T.star_bound_of_paired_character_condition hP (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.ex x hx i).nch HW F Cm X C₂ hS C C1 CT
    hC0 hC1 hCTb hEx.2 hmult hparC1 hSizeG
  have hmono := GlobalTheory.T.sizeConditions_mono (Fm.D x i) (Fm.L x i) (Fm.params x hx i) X
  have hCong := hE x h4 hx i hFa
  have hlarge := GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound (Fm.D x i) (Fm.L x i) X.r X.ρ X.exc hCong hFa.toCore.weight hS.canon.fam hS.kill hSha
    hSm.1 (by rw [hXexc]; exact hexcEq)
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h7
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h7
  have hmid23 : ∀ C', C' ≤ ComplexParameterFamilyContinuity → midF (Fm.L x i) C' ≤ midF (Fm.L x i) ComplexParameterFamilyContinuity := fun C' hC' =>
    midF_mono _ hC' (le_max_left _ _)
  have htwo : StarF (Fm.L x i) X.ρ ComplexParameterFamilyContinuity := by
    refine starF_of _ _ _ (fun k hk hl π hπ => ?_) (fun k hk hl h5 π hπ => ?_)
    · have h := ha x hxa hx i HW F Cm X C₂ hS k hk hl π hπ
      have h' := hmid23 Ca (le_trans (le_max_left _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
    · have h := hb' x hxb hx i HW F Cm X C₂ hS k hk hl h5 π hπ
      have h' := hmid23 Cb (le_trans (le_max_right _ _) (le_max_right _ _))
      unfold Bd at h ⊢; linarith
  refine ⟨X, ?_⟩
  exact
    { pos := hCs0
      pass := GlobalTheory.EtaPassage.main _ hEx.1
      mult := hmult
      rank := hFa.toCore.a3 _
      kill := hS.kill
      num := ⟨GlobalTheory.NLink.RowA.main _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        GlobalTheory.NLink.localBoundTableFromData_rowB_rowEntries _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle,
        (GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).1,
        (GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle).2,
        GlobalTheory.T.localBoundTableFromData_bandCondition _ _ (Fm.params x hx i) HW X _ Cs hS.canon.data hRle hS.par67⟩
      mid := hmid.1
      bb := ((hmono 7200 Cs (by linarith) hCs0).2.2.1) hmid.2
      large := hlarge
      exc := by rw [hXexc]; exact hexcOK
      two := ((hmono ComplexParameterFamilyContinuity Cs h23C hCs0).1) htwo
      ram := GlobalTheory.NLink.starG_of_thmB _ _ (Fm.params x hx i) X.ρ constantFirstHub Cs Q hG
        (h67 hP _ _ (Fm.params x hx i) _ HW F Cm X C₂ hS) hS.kill hSha
      typ := ((hmono _ Cs hT hCs0).2.1) htyp
      par := ((hmono C1 Cs hP1 hCs0).2.2.2) hparC1
      small := hSm }
end GlobalTheory.NLinkClose
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTailStatement
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclF_of_family_facts_and_bound_at_two_three : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C : ℝ) (CT : ℕ), 0 ≤ C → TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm → ConclF Fm := by
  first | exact @_root_.GlobalTheory.NLinkClose.main_alt_alt | exact _root_.GlobalTheory.NLinkClose.main_alt_alt | (intros; apply _root_.GlobalTheory.NLinkClose.main_alt_alt <;> assumption)
end
end
