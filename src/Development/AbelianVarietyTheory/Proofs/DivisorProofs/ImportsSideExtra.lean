module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideExtra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem isNilpotent_of_isDPNilpotent : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D}
    (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  intro D _ _ J dl hdl
  obtain ⟨N, h⟩ := hdl
  have h0 : ∀ l : List D, (∀ b ∈ l, b ∈ J) → N ≤ l.length → l.prod = 0 := by
    intro l hl hN
    have k := h (l.map fun b ↦ (1, b)) (by simpa using hl)
      (by simpa [List.map_map, Function.comp_def] using hN)
    rw [List.map_map] at k
    have e : l.map ((fun p : ℕ × D ↦ dl.dpow p.1 p.2) ∘ fun b ↦ (1, b)) = l.map id :=
      List.map_congr_left fun b hb ↦ dl.dpow_one (hl b hb)
    rwa [e, List.map_id] at k
  have key : ∀ n : ℕ, ∀ x ∈ J ^ n, ∀ l : List D, (∀ b ∈ l, b ∈ J) →
      N ≤ n + l.length → x * l.prod = 0 := by
    intro n
    induction n with
    | zero => intro x _ l hl hN; rw [h0 l hl (by simpa using hN), mul_zero]
    | succ n ih =>
      intro x hx l hl hN
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_)
        fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero]
      have := ih a ha (b :: l) (by simpa using ⟨hb, hl⟩) (by simp; omega)
      rwa [List.prod_cons, ← _root_.mul_assoc] at this
  refine ⟨N, eq_bot_iff.2 fun x hx ↦ ?_⟩
  simpa using key N x hx [] (by simp) (by simp)

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdealStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D} (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  first | exact @GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | exact GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | (intros; apply GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCo
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem isSeparated_left_of_isAbelianScheme {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have h1 : IsProper A.hom := h.proper
  have h2 : IsSeparated A.hom := inferInstance
  rw [Scheme.isSeparated_iff, ← terminal.comp_from A.hom]
  infer_instance

theorem pTaylor : PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ hφ₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP₀ D _ _ π κ hκ hπ N t ht htN
    j hj A' _ φ' _ m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g hφ₀ hA hg
  have hspan := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hmem : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨n, f, v, hv⟩ := Submodule.mem_span_set'.1 hmem
  choose a ha using fun r : Fin n ↦ (v r).2
  have hsum : (liftMor κ h).pull (m'.pull c) = ∑ r, f r • k.pull (a r) := by
    rw [← hv]; exact Finset.sum_congr rfl fun r _ ↦ by rw [ha]
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  have M := (m'.comp (liftMor κ h)).isMor
  have nn : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    rw [RingHom.id_comp, hi] at M
    exact M
  have hpull : nn.pull1 c.1 = ∑ r ∈ Finset.univ, f r • k.isMor.pull1 (a r).1 := by
    have e1 := IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor nn (fun _ ↦ rfl) hi c.1
    have e2 := congrArg (Submodule.subtype _) hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    exact e1.symm.trans e2
  have key := GlobalTheory.T.taylor_period_eq_period_over_thickening_alt (F := F) (F₀ := fibFam u₀) e (fibUnif u₀)
    (isSeparated_left_of_isAbelianScheme 𝒜 hA) (isSeparated_left_of_isAbelianScheme A₀ hA₀) h0
    (fun _ ↦ trivial) (fun l _ ↦ (hτ l).symm) φ₀ (fun p ↦ (hE p.2).symm) πa (GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal κ hκ) κ
    (fun _ hd ↦ hd) N t ht htN (j : B →+* D) hj (A₀.hom ≫ spMap π)
    (by rw [Category.comp_id]; rfl) nn _ k.isMor rfl c.1 per hper Finset.univ f (fun r ↦ (a r).1)
    (fun r l ↦ P₀ l (a r)) _ (fun _ _ ↦ rfl) (fun r ↦ hP₀ (a r)) hpull x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [crysToDR_apply, hsum, map_sum, ← key]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [map_smul, hd (a r), smul_eq_mul]

end GlobalTheory.AnPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCoStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison : GlobalTheory.AnPer.PTaylor := by
  first | exact @GlobalTheory.AnPer.pTaylor | exact GlobalTheory.AnPer.pTaylor | (intros; apply GlobalTheory.AnPer.pTaylor <;> assumption)
end
end

namespace GlobalTheory.GaussManinTop

theorem main : GlobalTheory.Published.GaussManinPeriods :=
  GlobalTheory.T.gaussManinPeriods_of_span_and_taylor_clauses GlobalTheory.T.periods_span_deRhamHomology_rank_two_g GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison

end GlobalTheory.GaussManinTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstCom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstCom
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section
namespace GlobalTheory.RatioConst


open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont _root_.Formalism.L2.Pj in
theorem rcoef_one_const {D : D7} {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    GlobalTheory.Core.Rk.IP.rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]

theorem integral_const_coef : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  intro D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0
  have hF := hX.1
  haveI := hF.haarA
  set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef
  have hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k := by
    intro g
    obtain ⟨h, hh, k, hk, rfl⟩ := Formalism.IndefR.TopMult.ga_decomp g
    rw [← hF.rangeA] at hh
    obtain ⟨x, rfl⟩ := hh
    exact ⟨x, k, hk, rfl⟩
  have hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1 := by
    intro k hk v
    show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1
    rw [← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]
    exact GlobalTheory.AdelicU.proj_ofInf _ _ v _
  have hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1 := by
    intro k hk
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom X.A k = 1 from hk, map_one]
  have hmem : ∀ x k S, k ∈ GinfC X.A →
      (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S) := by
    intro x k S hk
    simp only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]
  have hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    by_cases hx : x ∈ intG D P.a
    · rw [Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]
    · rw [Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))),
        h0 x hx ((hmem x k Sf hk).1 hg) k hk]
  have hKsub : K ⊆ openOff X.A (stdLat X.A) Sf := fun g hg v _ => hg v (Finset.notMem_empty v)
  have hKm : MeasurableSet K := (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet
  have hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet
  have hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A)) := by
    ext g
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]
  have hKvol : X.m K = 1 := by
    rw [hKeq]; exact GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1
  have hKc : IsCompact K := by
    have hG : IsCompact (GinfC X.A : Set (GA D X.A)) :=
      GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA
    refine (hF.levA.2.mul hG).of_isClosed_subset ?_ ?_
    · rw [hKeq]; exact Subgroup.isClosed_of_isOpen _ hF.levA.1
    · intro g hg
      obtain ⟨x, k, hk, rfl⟩ := hdec g
      rw [hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one] at hg
      refine Set.mul_mem_mul ?_ hk
      exact Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩
  obtain ⟨hcont, hpos, -⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha
  refine ⟨fun s => ?_, ?_⟩
  · let F : GA D X.A → ℂ := fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g)
        (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)
    have hFc : Continuous F := by
      refine (continuous_const.mul ?_).mul continuous_const
      simp only [GlobalTheory.Doubling.npow]
      refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_
      exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)
    have hI : Integrable (K.indicator F) X.m :=
      (integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)
    refine hI.integrableOn.congr_fun (fun g hg => ?_) hSm
    have hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ) := by
      exact rcoef_one_const X.m g
    simp only [integrand, hr, hw g hg]
    by_cases hgK : g ∈ K
    · simp [Set.indicator_of_mem hgK, F]
    · simp [Set.indicator_of_notMem hgK]
  · rw [setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]
    simp

end GlobalTheory.RatioConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstComStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  first | exact @GlobalTheory.RatioConst.integral_const_coef | exact GlobalTheory.RatioConst.integral_const_coef | (intros; apply GlobalTheory.RatioConst.integral_const_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlipVacB

open GlobalTheory.RouteSeesaw GlobalTheory.SquareDict.AlgSmall GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heis_rd (hψ : IsStdChar D ψ (-1)) (S V : HSp D) (w : WO S V) (g : WO (negSp V) S → ℂ) :
    heisO ψ S V w (rd S V g) = rd S V (heisO ψ (negSp V) S (adjO (negSp V) S w) g) := by
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, GlobalTheory.AdjLawPf.adj_heis ψ hψ.1.2.1, ← rd_eq]

theorem heisenbergOperator_externalProductOnHermitianSum (S A B : HSp D) (u : WO S (GlobalTheory.Doubling.hsum A B)) (f : WO S A → ℂ) (g : WO S B → ℂ) :
    heisO ψ S (GlobalTheory.Doubling.hsum A B) u (box2 f g) =
      box2 (heisO ψ S A (topR (A := A) (B := B) u) f) (heisO ψ S B (botR (A := A) (B := B) u) g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.MixModel.OrthDec.heisO_boxT, GlobalTheory.SeesawSumTarget.boxT_sumDec,
    GlobalTheory.MixModel.OrthDec.resT_apply, GlobalTheory.SeesawSumTarget.pA_sumDec, GlobalTheory.SeesawSumTarget.pB_sumDec]

theorem externalProduct_latticeVacua_adjoint_isLatticeVacuum (hψ : IsStdChar D ψ (-1)) {S A B : HSp D} {Λ : AddSubgroup (WO S (GlobalTheory.Doubling.hsum A B))}
    {ΛA : AddSubgroup (WO S A)} {ΛB : AddSubgroup (WO (negSp B) S)}
    (h : ∀ u ∈ Λ, topR (A := A) (B := B) u ∈ ΛA ∧ adjO (negSp B) S (botR (A := A) (B := B) u) ∈ ΛB)
    {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : IsLatVac (heisO ψ S A) ΛA f)
    (hg : IsLatVac (heisO ψ (negSp B) S) ΛB g) :
    IsLatVac (heisO ψ S (GlobalTheory.Doubling.hsum A B)) Λ (box2 f (rd S B g)) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have e1 : topR (A := A) (B := B) (2 • u) = 2 • topR (A := A) (B := B) u := rfl
    have e2 : adjO (negSp B) S (botR (A := A) (B := B) (2 • u)) = 2 • adjO (negSp B) S (botR (A := A) (B := B) u) := by
      have e3 : botR (A := A) (B := B) (2 • u) = botR (A := A) (B := B) u + botR (A := A) (B := B) u := by
        rw [two_nsmul]; rfl
      rw [e3, two_nsmul]
      exact GlobalTheory.AdjLawPf.adj_add (negSp B) S _ _
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, e1, e2, hf.1 _ (h u hu).1, hg.1 _ (h u hu).2]
  · have h1 : IsHalf e (topR (A := A) (B := B) u) := fun a b => hh _ _
    have h2 : IsHalf e (botR (A := A) (B := B) u) := fun a b => hh _ _
    have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
    rw [heisenbergOperator_externalProductOnHermitianSum, heis_rd hψ, hf.2 e he _ (h u hu).1 h1,
      hg.2 _ he' _ (h u hu).2 (GlobalTheory.AdjLawPf.adj_half (negSp B) S e _ h2)]

theorem vac_ne_zero {θ : InfFam D} {S T : HSp D} {sS sT LS LT} {f : WO S T → ℂ} (hf : IsVacO ψ θ S T sS sT LS LT f) :
    f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem externalProduct_readThroughAdjoint_ne_zero {S A B : HSp D} {f : WO S A → ℂ} {g : WO (negSp B) S → ℂ} (hf : f ≠ 0) (hg : g ≠ 0) :
    box2 f (rd S B g) ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hf
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  intro h0
  have := congrFun h0 (((GlobalTheory.BiTransfer.sumDec A B).resT S).symm (x, adjO S (negSp B) y))
  simp only [GlobalTheory.MixModel.OrthDec.boxT, AddEquiv.apply_symm_apply, Pi.zero_apply, rd] at this
  erw [GlobalTheory.AdjLawPf.adj_invol] at this
  exact mul_ne_zero hx hy this

theorem vac_eq_smul_vacB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  intro D T L sc G μ₀ hL W ρ i j AV AV₁ hV hV₁ Λ hΛ hlat f hf
  obtain ⟨A₁, h₁⟩ := exists_isGridFr W (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩
  have v1 := ρ.vT_is μ₀ i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have w1 : IsVacF W.ψ W.θ A₁ AV (ρ.vT i j) := ⟨v1.2.theta, fun s => by rw [c₁, cV]; exact v1.2.fock s⟩
  have w2 : IsVacF W.ψ W.θ (negFr AV₁) A₁ (ρ.vX i j) := ⟨v2.2.theta, fun s => by rw [c₁, cV₁]; exact v2.2.fock s⟩
  have w2' := rd_vac W.ψ_std W.θ_is A₁ AV₁ w2
  have key : IsVacF W.ψ W.θ A₁ (frSum AV AV₁) (box2 (ρ.vT i j) (rd _ _ (ρ.vX i j))) := by
    rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
    let o := GlobalTheory.BiTransfer.sumDec (spV G i j) (spV₁ G i j)
    refine ⟨o.isThetaFunO_boxT w1.1 w2'.1, fun τ z => ?_⟩
    have h1 := w1.2 τ (o.qA.map (tauE D τ) * z)
    have h2 := w2'.2 τ (o.qB.map (tauE D τ) * z)
    have e1 : o.qA.map (tauE D τ) = prL (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qA_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prL, Matrix.one_apply, apply_ite (tauE D τ)]
    have e2 : o.qB.map (tauE D τ) = prR (spV G i j).rank (spV₁ G i j).rank := by
      rw [GlobalTheory.SeesawSumTarget.qB_sumDec]
      ext a b
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective b
      rcases s with s | s <;> simp [prR, Matrix.one_apply, apply_ite (tauE D τ)]
    unfold annih at h1 h2 ⊢
    rw [GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o W.θ_is W.ψ_std τ _ w1.1 w2'.1,
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e1]; exact prL_cart AV AV₁ τ),
      GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (by rw [e2]; exact prR_cart AV AV₁ τ)]
    funext x
    have k1 := congrFun h1 (o.resT _ x).1
    have k2 := congrFun h2 (o.resT _ x).2
    simp only [GlobalTheory.MixModel.OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at k1 k2 ⊢
    linear_combination (rd _ _ (ρ.vX i j)) (o.resT _ x).2 * k1 + (ρ.vT i j) (o.resT _ x).1 * k2
  have e : vacB ρ i j = box2 (ρ.vT i j) (rd (spW₁ G i j) (spV₁ G i j) (ρ.vX i j)) := rfl
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have hl : IsLatVac (heisO W.ψ (spW₁ G i j) (spX G i j))
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ fun _ => True) (vacB ρ i j) := by
    rw [e]
    refine externalProduct_latticeVacua_adjoint_isLatticeVacuum W.ψ_std (fun u hu => ?_) v1.2.lat v2.2.lat
    have hu' : u ∈ orderingsOnSpWOne G i j := by rw [← hlat]; exact hu
    exact hu'
  obtain ⟨a, ha⟩ := GlobalTheory.LevelSeries.eq_smul_vacuum W.ψ_std W.θ_is (W.cart_is (.grid i j) ⟨i.2.le, j.2.le⟩)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (frSum AV AV₁)) s0 hΛ hf (f' := vacB ρ i j) key.1 hl
    (fun s => by have := key.2 s; rw [c₁] at this; exact this)
  have hne : vacB ρ i j ≠ 0 := by rw [e]; exact externalProduct_readThroughAdjoint_ne_zero (vac_ne_zero v1) (vac_ne_zero v2)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hne (by rw [ha, zero_smul])
  exact ⟨a⁻¹, inv_ne_zero ha0, by rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]⟩

end GlobalTheory.TopFlipVacB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitVacuumEqSmulProductArrowVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitVacuum_eq_smul_product_arrow_vacua : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (ρ : RealMatch W) (i j : Fin D.R.m) (AV : Fr (spV G i j)) (AV₁ : Fr (spV₁ G i j)),
      IsGridFr W _ AV → IsGridFr W _ AV₁ → ∀ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E), IsSelfDualC (spX G i j) Λ →
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j →
      ∀ f, IsVacO W.ψ W.θ (spW₁ G i j) (spX G i j) (W.cart (.grid i j)) (frSum AV AV₁).cart
        (G.Λ (.grid i j)) Λ f → ∃ c : ℂ, c ≠ 0 ∧ f = c • vacB ρ i j := by
  first | exact @GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | exact GlobalTheory.TopFlipVacB.vac_eq_smul_vacB | (intros; apply GlobalTheory.TopFlipVacB.vac_eq_smul_vacB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuum
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.CosetNorm

open Formalism.MainNotions.TaylorLogMetric (VC tor0 La Iop U al YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt La0 Wd wdPh Crv)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := by
  have e : symplO S T x y + symplOH S T y x = symplOH S T x y := by
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
    unfold symplOH
    rw [GlobalTheory.OrientedHeis.symplO_skew x y]
    linear_combination (-symplO S T x y) * h2
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, e, add_comm]

theorem heisO_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_heisO_eq_zero {ΛS : Lat S} {ΛT : Lat T} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {u u' : WO S T}
    (hu : u.map (infPart D) = 0) (hu' : u'.map (infPart D) = 0) (hn : u - u' ∉ latO S T ΛS ΛT fun _ => True) :
    GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f) = 0 := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have h0 : (u - u').map (infPart D) = 0 := by
    funext i j
    have a : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    have b : infPart D (u' i j) = 0 := congrFun (congrFun hu' i) j
    show infPart D (u i j - u' i j) = 0
    rw [RingHom.map_sub, a, b, sub_self]
  rw [h1 _ h0] at hn
  push_neg at hn
  obtain ⟨l, hl, hne⟩ := hn
  obtain ⟨ε, hε, hεf⟩ := h3 f hv l hl
  have t1 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu
  have t2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu'
  have e := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 t1 t2 l
  rw [heisO_comm l u, heisO_comm l u', hεf f hv, heisO_smul, heisO_smul, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left,
    GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right] at e
  have hεε : ε * starRingEnd ℂ ε = 1 := by rcases hε with rfl | rfl <;> simp
  have n1 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplO S T l u'))
  have e2 : ψ (symplO S T (u - u') l) * ψ (symplO S T l u) = ψ (symplO S T l u') := by
    rw [← AddChar.map_add_eq_mul, GlobalTheory.OrientedHeis.symplO_skew u l, GlobalTheory.OrientedHeis.symplO_skew u' l]
    congr 1
    have : symplO S T (u - u' + u') l = symplO S T (u - u') l + symplO S T u' l := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    rw [sub_add_cancel] at this
    linear_combination -this
  refine (mul_eq_zero.1 (?_ : (ψ (symplO S T (u - u') l) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hne)
  set I := GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f)
  set A := ψ (symplO S T (u - u') l)
  set B := ψ (symplO S T l u)
  set C := ψ (symplO S T l u')
  linear_combination (-A) * e + (ε * starRingEnd ℂ C * starRingEnd ℂ ε * I) * e2 +
    (C * starRingEnd ℂ C * I) * hεε + I * n1

theorem ip_sum (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (h : ι → WO S T → ℂ) (c : ℂ) (ht : ∀ i, IsThetaFunO ψ S T (h i))
    (ha : ∀ i, a i * starRingEnd ℂ (a i) = 1)
    (ho : ∀ i j, i ≠ j → GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) = 0) (hc : ∀ i, GlobalTheory.Ker.ipO μ 𝓕 (h i) (h i) = c) :
    GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) = s.card * c := by
  have e : ∀ w, (∑ i ∈ s, a i • h i) w * starRingEnd ℂ ((∑ i ∈ s, a i • h i) w) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w)) := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hi : ∀ i j, Integrable (fun w => (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w))) (μ.restrict 𝓕) :=
    fun i j => Integrable.const_mul (GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (ht i) (ht j)) _
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) := by
    unfold GlobalTheory.Ker.ipO
    simp only [e]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e2, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hj => by rw [ho i j hj.symm, mul_zero], ha, hc, one_mul]

theorem selfDual_stdLat (hS : S.gram = 1) : IsSelfDualC S (stdLat S) := by
  convert GlobalTheory.Ker.Base.selfDualC_stdL hS using 1
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL, stdLat, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h trivial)
    rw [← hb]
    exact b.2
  · exact Submodule.mem_one.2 ⟨⟨x i, h⟩, rfl⟩

theorem reads_sum {θ : InfFam D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}
    {ι : Type} (s : Finset ι) {G : ι → VC D a d → ℂ} {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem finPt_sub {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z z' : Matrix (Fin d) (Fin a) D.host.E) :
    finPt hS hT r (z - z') = finPt hS hT r z - finPt hS hT r z' := by
  unfold finPt
  rw [← AddMonoidHom.map_sub]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply]
  ring_nf

theorem pt_sub_mem {a d : ℕ} (δ : ℂ) {z z' : Matrix (Fin d) (Fin a) D.host.E} (h : z - z' ∈ YYl D (stdL D a) (stdL D d)) :
    pt D (tor0 D ⊤ δ) δ z - pt D (tor0 D ⊤ δ) δ z' ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, h, ?_⟩
  funext τ i j
  simp only [pt, embV, tor0, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub]
  ring


set_option maxHeartbeats 1000000 in
theorem ip_cosetVec : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ hf₀ hsph hφ ν 𝓕 hcov
  have hset := hX.setup
  have hψ := hset.std
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ P.crv 𝔪 hG.1 (Ideal.isCoprime_iff_sup_eq.2 hG.2.1) P.a P.d
  have hpts := fun y hy => GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ P.crv 𝔪 hG.1 (a := P.a) (d := P.d) y hy
  unfold cosetVec at hφ
  generalize La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d) = L at hidx hpts hφ
  have hne : ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index ≠ 0 := by rw [hidx]; positivity
  haveI : Finite (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  letI : Fintype (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := Fintype.ofFinite _
  choose z hz _ using fun q : L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L => hpts _ (Quotient.out q).2
  have hlv : IsLatVac (heisO X.ψ X.A X.B) (latO X.A X.B (stdLat X.A) LB fun _ => True) f₀ := by
    have e : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by funext v; simp
    rw [← e]
    exact hsph
  have hfin : ∀ y, (finPt X.rkA X.rkB r y).map (infPart D) = 0 := fun y => GlobalTheory.VacUnique.finRat_inf _ _ _
  have hrd := GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hset
  set n := ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index with hn
  have eI : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) L P.e0 = ((Real.sqrt (n : ℝ) : ℂ))⁻¹ •
      ∑ q, al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) • U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) P.e0 := by
    funext y
    simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hz, ← hn]
  have hg := reads_sum Finset.univ fun q => (hrd _ _ hf₀ (z q)).smul (al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
  have hg2 := hg.smul ((Real.sqrt (n : ℝ) : ℂ))⁻¹
  rw [← eI] at hg2
  have hw := ((hrd _ _ hg2 (unitBlock D o P.a P.d)).smul
    (wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  have hsum := ip_sum hψ hcov Finset.univ (fun q => al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
    (fun q => heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (z q)) f₀) (GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀) (fun q => (hrd _ _ hf₀ (z q)).1)
    (fun q => by
      rw [al, map_zpow₀, ← mul_zpow]
      simp)
    (fun q q' hq => ip_heisO_eq_zero hψ (selfDual_stdLat hset.gS) hLB hf₀.1 hlv hcov (hfin _) (hfin _) fun h => hq (by
      rw [← finPt_sub, ← hY] at h
      have h2 := pt_sub_mem δ h
      rw [← hz, ← hz] at h2
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
      exact h2))
    fun q => GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hf₀.1 hf₀.1 _
  have hph : ∀ x : VC D P.a P.d, wdPh D (tor0 D ⊤ δ) x * starRingEnd ℂ (wdPh D (tor0 D ⊤ δ) x) = 1 := fun x =>
    GlobalTheory.HeisOrtho.mul_conj_of_norm_one (by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.norm_exp])
  have hsq : ∀ t : ℝ, 0 ≤ t → ((Real.sqrt t : ℂ))⁻¹ * starRingEnd ℂ ((Real.sqrt t : ℂ))⁻¹ = (t : ℂ)⁻¹ := fun t ht => by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have e1 := hsq n (Nat.cast_nonneg n)
  have e2 := hsq ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) (by positivity)
  have e3 := hph (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
  have e4 : ((n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1 := by
    rw [Complex.ofReal_natCast]; exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hne)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← hn] at hsum
  have eW : ∀ (x : VC D P.a P.d) G, Wd D (tor0 D ⊤ δ) x G = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G := fun _ _ => rfl
  rw [eW] at hφ
  rw [Reads.unique hφ hw]
  show GlobalTheory.Ker.ipO ν 𝓕 _ _ = _ * GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀
  rw [GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right,
    GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hg2.1 hg2.1, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, hsum,
    ← mul_assoc, e2, ← mul_assoc (wdPh _ _ _), e3, one_mul, ← mul_assoc _ (starRingEnd ℂ _), e1, ← mul_assoc _ (n : ℂ), e4, one_mul]
  push_cast
  rfl

end GlobalTheory.NormRatio.CosetNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingNormSqEqVacuumStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  first | exact @GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | exact GlobalTheory.NormRatio.CosetNorm.ip_cosetVec | (intros; apply GlobalTheory.NormRatio.CosetNorm.ip_cosetVec <;> assumption)
end
end
