module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateRowBoundOfDictionary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HodgeDominates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_sec_detOm (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (hr : 1 ≤ Dw.p + Dw.q) (Y : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (w : Xo.XF c) {A : LB Y.X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow (FlagMod.detOm Y) m) A).Sec, Y.j w ∈ nonzeroLocus s := by
  obtain ⟨φs, hs, -⟩ := hS (max 1 (Module.finrank ℚ E * min Dw.p Dw.q)) (le_max_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y', BD, d, k, -, hk, hsm, -, hBD, -, hamp⟩ := hF E H Dw hr φ h₁ h₂ l Xo c
  have hY' := GlobalTheory.FanTheta.isLB_detOm_of_smooth Y' hr hsm
  obtain ⟨N, _, _, u, p, p', hu, hu', hp, hpt, e⟩ := exists_common_modification hE Y Y' hY hY'
  have e₁ : p (u w) = Y.j w := by rw [← hu]; rfl
  have e₂ : p' (u w) = Y'.j w := by rw [← hu']; rfl
  rw [← e₁]
  refine exists_sec_of_common p p' hp (u w) (fun W hW => ⟨Y'.j ''ᵁ (Y.j ⁻¹ᵁ W), ⟨w, (show Y.j w ∈ W from e₁ ▸ hW), e₂.symm⟩, ?_⟩) hY hY'
    (hamp hY') BD.isLB_lb e hk ?_ BD.canonical ?_ hA
  · rintro n ⟨w', hw', h⟩
    show p n ∈ W
    rw [hpt n w' h.symm]
    exact hw'
  · have h := cls_tens (isLB_lbPow hY' k) (isLB_dual BD.isLB_lb) (hamp hY').isLB
    rw [cls_lbPow hY', cls_dual BD.isLB_lb] at h
    exact (congrArg (· + _) h).trans (by abel)
  · rw [← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical, e₂]
    refine fun h => hBD _ h ?_
    have h' : Y'.jQ w ∈ pullback.fst Y'.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y'.t.G := by
      rw [Y'.ab_gen]; exact ⟨w, rfl⟩
    exact h'

theorem exists_lb_dominates (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (TF : TorFlag Xo c) :
    ∃ (ω : LB TF.Y.X) (hω : ω.IsLB), cls _ (TF.X.isLB_Llam (FlagMod.mu0 Dw)) = CechPic.pull TF.X.π (cls ω hω) ∧
      ∀ (w : Xo.XF c) (A : LB TF.Y.X), A.IsLB →
        ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, TF.Y.j w ∈ nonzeroLocus s := by
  have := TF.smooth
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hr
  · have hd : Dw.dim = 0 := by rw [Datum.dim, show Dw.q = 0 by omega, mul_zero]
    rw [hd] at this
    have : Etale TF.Y.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 this
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver TF.Y.proj
    have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified TF.Y.s
    have := IsFinite.of_isProper_of_locallyQuasiFinite TF.Y.s
    have : IsAffine TF.Y.X := isAffine_of_isAffineHom TF.Y.s
    refine ⟨_, LB.isLB_triv _, ?_, fun w A hA => ⟨1, one_pos, ?_⟩⟩
    · have he : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = 0 := by
        rw [FlagMod.unitaryWeightExponentVector_signatureWeightMuZero]
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · rfl
        · have := i.2
          have : Dw.mult σ = 0 := by unfold Datum.mult; split_ifs <;> omega
          omega
      refine Eq.trans (b := 0) ((cls_eq_zero_iff _).2 ⟨⟨fun _ => 1⟩, fun k k' => ?_⟩) (map_zero _).symm
      have hg : (TF.X.Llam (FlagMod.mu0 Dw)).g k k' = 1 :=
        Finset.prod_eq_one fun ix _ => by rw [he]; exact zpow_zero _
      rw [hg, map_one, map_one, mul_one]
    · obtain ⟨s, hs, -⟩ := exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_div (isLB_lbPow (LB.isLB_triv _) 1) hA)
        (Set.finite_singleton (TF.Y.j w)) (U := ⊤) (Set.subset_univ _)
      exact ⟨s, hs rfl⟩
  · have hY := GlobalTheory.FanTheta.isLB_detOm_of_smooth TF.Y hr
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) this)
    refine ⟨_, hY, ?_, fun w A hA => exists_sec_detOm hE hS hF hr TF.Y hY w hA⟩
    rw [← cls_pull hY _ (pull_isLB hY _), ← (cls_eq_iff TF.X.F.isLB_detOm _).2 (TF.X.F.detOm_iso_pull hY)]
    exact ((cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)).symm

end GlobalTheory.HodgeDominates
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AbLocusProperNormal

theorem isProper_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth (Sp V) G
  have p : Sp (ResidueField V) := IsLocalRing.closedPoint (ResidueField V)
  refine GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr V G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance ?_
  exact GlobalTheory.AbelianTrait.isProper_snd_of_mem_abLocus G (K := ResidueField V)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) p (by rw [hab]; trivial)

theorem isProper_of_abLocus_eq_univ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R))
    [GrpObj G] (hG : IsSemiAbelian G) (hab : abLocus G = Set.univ) : IsProper G.hom := by
  haveI : IsSemiAbelian G := hG
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI := hG.smooth
  haveI : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R G.left G.hom ?_
  intro V K _ _ _ _ _ _ _ x y _ hxy
  have hGV : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have habV : abLocus ((Over.pullback y).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom y) z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper (pullback.snd G.hom y) := isProper_dvr V _ hGV habV
  let xV : Sp K ⟶ pullback G.hom y := pullback.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence (pullback.snd G.hom y) := by
    have h : UniversallyClosed (pullback.snd G.hom y) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq (pullback.snd G.hom y) :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by rw [Category.comp_id]; exact pullback.lift_snd _ _ _⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ pullback.fst G.hom y, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact pullback.lift_fst _ _ _

theorem isProper_restrict_of_subset_abLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ W : (Sp R).Opens, (W : Set (Sp R)) ⊆ abLocus G → IsProper (G.hom ∣_ W) := by
  intro R _ _ _ _ G _ hG W hW
  let I := {r : R // r ≠ 0 ∧ ((PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) : Set (Sp R)) ⊆ (W : Set (Sp R))}
  let t : ∀ i : I, Sp (Localization.Away i.1) ⟶ Sp R := fun i => spMap (algebraMap R (Localization.Away i.1))
  have hrange : ∀ i : I, Set.range (t i) = (PrimeSpectrum.basicOpen i.1 : Set (PrimeSpectrum R)) := fun i =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away i.1) i.1
  have hprop : ∀ i : I, IsProper (pullback.snd G.hom (t i) ∣_ ⊤) := by
    intro i
    haveI : IsDomain (Localization.Away i.1) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors i.2.1)
    haveI : IsNoetherianRing (Localization.Away i.1) :=
      IsLocalization.isNoetherianRing (Submonoid.powers i.1) _ inferInstance
    have hGi : IsSemiAbelian ((Over.pullback (t i)).obj G) := IsSemiAbelian.pullback (t i) G hG
    have hab : abLocus ((Over.pullback (t i)).obj G) = Set.univ := Set.eq_univ_of_forall fun z =>
      (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G.hom (t i)) z).1
        (hW (i.2.2 (by rw [← hrange i]; exact ⟨z, rfl⟩)))
    have : IsProper (pullback.snd G.hom (t i)) := isProper_of_abLocus_eq_univ _ _ hGi hab
    infer_instance
  refine GlobalTheory.AbLocusLocal.isProper_restrict_of_cover G.hom t (fun i => pullback.snd G.hom (t i))
    (fun i => pullback.fst G.hom (t i)) (fun i => IsPullback.of_hasPullback G.hom (t i)) (fun _ => ⊤) hprop W
    (fun i => ?_) (fun z hz => ?_)
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine i.2.2 ?_
    rw [← hrange i]
    exact ⟨_, rfl⟩
  · obtain ⟨_, ⟨r, rfl⟩, hzr, hrW⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz W.isOpen
    have hr : r ≠ 0 := fun h0 => hzr (by rw [h0]; exact zero_mem _)
    let i : I := ⟨r, hr, hrW⟩
    obtain ⟨y, hy⟩ : z ∈ Set.range (t i) := by rw [hrange i]; exact hzr
    exact ⟨i, ⟨y, trivial⟩, by first | exact hy | (erw [Scheme.Hom.comp_apply]; exact hy) | simpa using hy⟩

end GlobalTheory.AbLocusProperNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isLocalizedModule_ratTensor (M : Type) [AddCommGroup M] :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)

theorem toEnd0_apply {K : Type} [Field K] (A : AbVar K) (f : End A) :
    toEnd0 A f = TensorProduct.mk ℤ ℚ (End A) 1 f := rfl

theorem toEnd0_injective_and_fraction : ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Injective (toEnd0 A) ∧ ∀ x : End0 A, ∃ (n : ℕ) (f : End A), 0 < n ∧ n • x = toEnd0 A f := by
  intro K _ A
  haveI := isLocalizedModule_ratTensor (End A)
  refine ⟨fun f g h => ?_, fun x => ?_⟩
  · rw [toEnd0_apply, toEnd0_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    have h1 : (c : ℤ) • (f - g) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [Submonoid.smul_def] using hc
    apply sub_eq_zero.1
    apply End.addEquiv.injective
    apply GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero K A A (c : ℤ) _ hc0
    have hh := congrArg (End.addEquiv (X := A)) h1
    rw [map_zsmul, map_zero] at hh
    exact hh
  · obtain ⟨⟨m, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    simp only [Submonoid.smul_def] at hc
    rcases Int.natAbs_eq (c : ℤ) with h | h
    · refine ⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩
      rw [toEnd0_apply, ← hc, ← natCast_zsmul, ← h]
    · refine ⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩
      have h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ) := by omega
      rw [toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DimLogTop

theorem log_size_le (f r L kap S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hk0 : 0 ≤ kap)
    (hk : Real.log kap ≤ 2 * L) (hfr : Real.log (f * r) ≤ L) (hS0 : 0 ≤ S)
    (hS : S ≤ (f * r * L) ^ 2 * kap + 6 * f * r ^ 2) : Real.log S ≤ 20 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hfr0 : 0 < f * r := by positivity
  have e1 : f * r ≤ Real.exp L := (Real.log_le_iff_le_exp hfr0).1 hfr
  have e2 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e3 : kap ≤ Real.exp (2 * L) := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h0).1 hk
  have e4 : (7 : ℝ) ≤ Real.exp (6 * L) := by linarith [Real.add_one_le_exp (6 * L)]
  have hE : Real.exp (6 * L) = Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp (2 * L) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp L ^ 2 ≤ Real.exp (6 * L) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have a1 : (f * r * L) ^ 2 * kap ≤ Real.exp (6 * L) := by
    rw [hE, mul_pow]
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    have : L ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    gcongr
  have a2 : 6 * f * r ^ 2 ≤ 6 * Real.exp (6 * L) := by
    have : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    nlinarith
  have a3 : S ≤ Real.exp (12 * L) := by
    have : Real.exp (12 * L) = Real.exp (6 * L) * Real.exp (6 * L) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (6 * L)
    nlinarith
  have := (Real.log_le_iff_le_exp h).2 a3
  linarith

theorem cube_le (Cb L Zb : ℝ) (hL : Cb ≤ L) (hL1 : 1 ≤ L) (hZ : L ≤ Zb) : Cb * Zb ^ 3 ≤ Zb ^ 12 := by
  have h1 : 1 ≤ Zb := hL1.trans hZ
  have h9 : Zb ≤ Zb ^ 9 := le_self_pow₀ h1 (by norm_num)
  have h3 : 0 ≤ Zb ^ 3 := by positivity
  calc Cb * Zb ^ 3 ≤ Zb ^ 9 * Zb ^ 3 := mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Zb ^ 12 := by ring

theorem rkK_eq_finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) (h : Submodule.span K (L : Set V) = ⊤) :
    Formalism.HN.rkK L = Module.finrank K V := by
  unfold Formalism.HN.rkK
  rw [h, finrank_top]

end GlobalTheory.CovTop.DimLogTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecond
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option maxHeartbeats 1000000

namespace GlobalTheory.HSShortRoad

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) :
    Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dite_eq_right hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt {P : WtPar Dw} (h : WtBig P) (j : ℕ) : GapGe (FlagTan.dimFlag Dw + 1) (P.wt j) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  have gap_add : ∀ (v w : Fin (Dw.p + Dw.q) → ℤ) (k : ℕ), gap (v + w) k = gap v k + gap w k := fun v w k => by
    unfold gap
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  have gap_nsmul : ∀ (n : ℕ) (v : Fin (Dw.p + Dw.q) → ℤ) (k : ℕ), gap (n • v) k = n * gap v k := fun n v k => by
    unfold gap
    split_ifs
    · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
    · simp
  have gap_kap : ∀ (τ : Psi H) {k : ℕ}, k + 1 < Dw.p + Dw.q → gap (FlagTan.kap Dw τ) k =
      if k + 1 = Dw.p then 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 else -2 := fun τ k h => by
    unfold FlagTan.kap gap
    simp only [dif_pos h]
    split_ifs <;> push_cast <;> omega
  intro τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg j) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

noncomputable abbrev sz (la : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)|

theorem one_le_sz {la : AllWt.Weight Dw} (h : 0 < sz la) : 1 ≤ sz la := by
  have e : sz la = ((∑ τ, ∑ k, |la τ k| : ℤ) : ℝ) := by push_cast; rfl
  rw [e] at h ⊢
  exact_mod_cast (show (0 : ℤ) < _ by exact_mod_cast h)

end Weights

theorem log_le_of_le_exp {s y : ℝ} (h0 : 0 ≤ s) (hy : 0 ≤ y) (h : s ≤ Real.exp y) : Real.log s ≤ y := by
  rcases h0.eq_or_lt with rfl | h0
  · simpa using hy
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_size_le {a L κ s : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (h₁ : Real.log a ≤ L) (hκ : 1 ≤ κ)
    (h₂ : Real.log κ ≤ 2 * L) (h0 : 0 ≤ s) (h : s ≤ 2 * ((a * L) ^ 2 * κ)) : Real.log s ≤ 10 * L := by
  have hp : 0 < 2 * ((a * L) ^ 2 * κ) := by positivity
  refine log_le_of_le_exp h0 (by linarith) (h.trans ((Real.log_le_iff_le_exp hp).1 ?_))
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul ha.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
  push_cast
  linarith

theorem span_of_shortGen {F V κ : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : κ → V → ℝ} {M : Submodule (𝓞 F) V} {n : ℕ} {w : Fin n → V} {Λ : ℝ} (h : CompHt.IsShortGen Nm M w Λ)
    (hM : Submodule.span F (M : Set V) = ⊤) : (∀ i, w i ∈ M) ∧ Submodule.span F (Set.range w) = ⊤ :=
  ⟨fun i => (h.gen _).2 (Submodule.subset_span ⟨i, rfl⟩), top_le_iff.1 (hM.ge.trans (Submodule.span_le.2 fun x hx =>
    Submodule.span_subset_span ℤ F _ ((h.gen x).1 hx)))⟩

theorem sum_univ_inst {α : Type} {i1 i2 : Fintype α} (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i1) f = @Finset.sum α ℝ _ (@Finset.univ α i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

theorem bound_le {C Z PP κ : ℝ} (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hCZ : 6 * C ≤ Z) (hP : Z ^ 12 ≤ PP) (hκ : 1 ≤ κ) :
    C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) ≤ PP * κ := by
  have h5 : 0 ≤ Z ^ 5 := by positivity
  have e : C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) = C * Z ^ 5 * (κ + 1) := by ring
  have a1 : C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : 2 * C * Z ^ 5 ≤ Z * Z ^ 5 := mul_le_mul_of_nonneg_right (by linarith) h5
  have a3 : Z * Z ^ 5 ≤ Z ^ 12 := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hZ (by norm_num)
  have a4 : 2 * C * Z ^ 5 ≤ PP := a2.trans (a3.trans hP)
  rw [e]
  calc C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := a1
    _ = (2 * C * Z ^ 5) * κ := by ring
    _ ≤ PP * κ := mul_le_mul_of_nonneg_right a4 (by linarith)

end GlobalTheory.HSShortRoad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatFrameOfIsShortGen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem exists_latFrame_of_isShortGen : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (Nm : (F →+* ℂ) → V → ℝ) (M : Submodule (𝓞 F) V) (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), Nonempty (LatFrame Nm M) → CompHt.IsShortGen Nm M w abelian₂ → ∃ f : LatFrame Nm M, f.n = n ∧ (∀ x ∈ Submodule.span (𝓞 F) (Set.range f.w.col), x ∈ Submodule.span ℤ (Set.range f.w.col)) ∧ ∀ i σ, ChowHt.frameNorm (f.A σ) (fun a => σ (f.w.col i a)) ≤ abelian₂ := by
  intro F V _ _ _ _ _ _ Nm M n w abelian₂ hf hw
  obtain ⟨f⟩ := hf
  classical
  let e := f.b.equivFun
  let w' : Matrix (Fin f.N) (Fin n) F := Matrix.of fun j k => e (w k) j
  have hcol : w'.col = fun k => e (w k) := rfl
  have hmemM : ∀ i, w i ∈ M := fun i => (hw.gen (w i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hspanO : Submodule.span (𝓞 F) (Set.range w) = M := by
    refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩; exact hmemM i
    · have hz := (hw.gen x).1 hx
      exact Submodule.span_le_restrictScalars ℤ (𝓞 F) _ hz
  have hsum : ∀ k, (∑ j, w' j k • f.b j) = w k := fun k => by
    simp only [w', Matrix.of_apply, e, Module.Basis.equivFun_apply, Module.Basis.sum_repr]
  have hfullV : Submodule.span F (Set.range w) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← f.isFull.2]
    refine Submodule.span_le.2 fun x hx => ?_
    have hz := (hw.gen x).1 hx
    exact Submodule.span_le_restrictScalars ℤ F _ (Submodule.span_mono (le_refl _) hz)
  refine ⟨⟨f.N, n, f.b, w', f.A, ⟨?_, ?_, f.isFrame.herm, f.isFrame.conj, f.isFrame.norm⟩⟩, rfl, ?_, ?_⟩
  · simp only [hsum]; exact hspanO
  · rw [hcol, Set.range_comp', show (⇑e '' Set.range w) = (e.toLinearMap) '' Set.range w from rfl,
      Submodule.span_image, hfullV, Submodule.map_top, LinearEquiv.range]
  · intro x hx
    let eO : V →ₗ[𝓞 F] (Fin f.N → F) := e.toLinearMap.restrictScalars (𝓞 F)
    let eZ : V →ₗ[ℤ] (Fin f.N → F) := e.toLinearMap.restrictScalars ℤ
    have hO : Submodule.span (𝓞 F) (Set.range w'.col) = (Submodule.span (𝓞 F) (Set.range w)).map eO := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    have hZ : Submodule.span ℤ (Set.range w'.col) = (Submodule.span ℤ (Set.range w)).map eZ := by
      rw [Submodule.map_span, hcol, Set.range_comp']; rfl
    rw [hO] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hZ]
    exact ⟨y, (hw.gen y).1 (hspanO ▸ hy), rfl⟩
  · intro i σ
    show ChowHt.frameNorm (f.A σ) (fun a => σ (e (w i) a)) ≤ abelian₂
    simp only [e, Module.Basis.equivFun_apply]
    rw [f.isFrame.norm σ (w i)]
    exact hw.le i σ

end GlobalTheory.HSApp
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameBerg

theorem one_le_gap_of_strictAnti {N : ℕ} {v : Fin N → ℤ} (hv : StrictAnti v) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ gap v k := by
  rw [gap, dite_eq_left hk]
  have := hv (show (⟨k, by omega⟩ : Fin N) < ⟨k + 1, hk⟩ from Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
  omega

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem antitone_of_gap_nonneg {N : ℕ} {v : Fin N → ℤ} (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  have key : ∀ d (a b : Fin N), (b : ℕ) = a + d → v b ≤ v a := by
    intro d
    induction d with
    | zero =>
      intro a b hab
      have e : b = a := Fin.ext (by simpa using hab)
      rw [e]
    | succ d ih =>
      intro a b hab
      have hc : (a : ℕ) + d < N := by omega
      have h1 := ih a ⟨(a : ℕ) + d, hc⟩ rfl
      have h2 := h ((a : ℕ) + d) (by omega)
      rw [gap, dite_eq_left (by omega)] at h2
      have e : b = ⟨(a : ℕ) + d + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e]
      linarith
  intro a b hab
  exact key ((b : ℕ) - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

end GlobalTheory.FrameBerg

namespace GlobalTheory.FrameBerg


end GlobalTheory.FrameBerg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirst
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.ShortSpanUnitCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem abs_kap_le (Dw : Datum H) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(FlagTan.kap Dw τ k : ℝ)| ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
  have hk := k.2
  have h : |FlagTan.kap Dw τ k| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
    simp only [FlagTan.kap]
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> omega
  rw [← Int.cast_abs]; exact_mod_cast h

theorem sum_abs_kap_le (Dw : Datum H) :
    ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
  calc ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ ∑ _τ : Psi H, ∑ _k : Fin (Dw.p + Dw.q), ((Dw.p + Dw.q : ℕ) : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => abs_kap_le Dw τ k
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sum_abs_weightZero_le_components (Dw : Datum H) (P : WtPar Dw) :
    ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| ≤ ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| + ∑ τ, ∑ k, |(P.u₂ τ k : ℝ)| +
      (FlagTan.dimFlag Dw : ℝ) * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => ?_
  have e : (P.wt 0 τ k : ℝ) = (FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ) + (FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ) := by
    simp only [WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [e]
  calc _ ≤ |(FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ)| + |(FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, Nat.abs_cast]
      linarith [abs_add_le (FlagTan.kap Dw τ k : ℝ) (P.u₂ τ k : ℝ)]

theorem consecutiveGap_weightZero_ge (Dw : Datum H) (P : WtPar Dw) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) (g : ℤ)
    (hg : g ≤ gap (P.u₁ τ) k) : ((FlagTan.dimFlag Dw : ℤ) + 1) * g - 2 ≤ gap (P.wt 0 τ) k := by
  have hr := (P.gap_rem τ k).1
  have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
    simp only [FlagTan.kap, Fin.val_mk]
    split_ifs <;> push_cast <;> omega
  rw [gap, dite_eq_left h] at hr hg ⊢
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply] at hr ⊢
  simp only [nsmul_eq_mul] at hr ⊢
  have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

theorem final_le {C Zr S Dc PP X abelian₂ L : ℝ} (hC : 0 ≤ C) (hL : 4 * C + 1 ≤ L) (hZL : L ≤ Zr) (hPP : Zr ^ 12 ≤ PP)
    (hDc : 1 ≤ Dc) (hX : 1 ≤ X) (hS : S ≤ 3 * Dc * Zr ^ 2 * X) (hLam : Real.log abelian₂ ≤ C * (Zr ^ 3 * S + Zr ^ 5)) :
    Real.log abelian₂ ≤ Dc * PP * X := by
  have hZ1 : 1 ≤ Zr := by linarith
  have hZ0 : 0 ≤ Zr := by linarith
  have hZ5 : 0 ≤ Zr ^ 5 := by positivity
  have hDX : 1 ≤ Dc * X := by nlinarith
  have h1 : Zr ^ 3 * S ≤ 3 * (Dc * X) * Zr ^ 5 := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ Zr ^ 3)
    nlinarith
  have h2 : Zr ^ 5 ≤ (Dc * X) * Zr ^ 5 := by nlinarith
  have h3 : C * (Zr ^ 3 * S + Zr ^ 5) ≤ (Dc * X) * (4 * C * Zr ^ 5) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    nlinarith
  have h4 : 4 * C * Zr ^ 5 ≤ PP := by
    have a : Zr ≤ Zr ^ 7 := by
      calc Zr = Zr ^ 1 := (pow_one _).symm
        _ ≤ Zr ^ 7 := pow_le_pow_right₀ hZ1 (by norm_num)
    have b : 4 * C ≤ Zr ^ 7 := by linarith
    have c : 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := mul_le_mul_of_nonneg_right b hZ5
    calc 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := c
      _ = Zr ^ 12 := by ring
      _ ≤ PP := hPP
  have h5 : (Dc * X) * (4 * C * Zr ^ 5) ≤ (Dc * X) * PP := mul_le_mul_of_nonneg_left h4 (by linarith)
  calc Real.log abelian₂ ≤ _ := hLam
    _ ≤ _ := h3
    _ ≤ _ := h5
    _ = Dc * PP * X := by ring

theorem sum_le {S K A1 A2 Dc W : ℝ} (hSle : S ≤ K + A2 + Dc * A1) (hK : K ≤ W) (h1 : A1 ≤ W) (h2 : A2 ≤ W)
    (hDc : 1 ≤ Dc) (hW : 0 ≤ W) : S ≤ 3 * Dc * W := by
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Dc)
  nlinarith

theorem log_sum_le {S k fr L : ℝ} (hS0 : 0 ≤ S) (hSk : S ≤ (fr * L) ^ 2 * k) (hk : Real.log k ≤ 2 * L)
    (hfr : Real.log fr ≤ L) (hL1 : 1 ≤ L) (hfr1 : 1 ≤ fr) : Real.log S ≤ 10 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hZ : 0 < fr * L := by positivity
  have hk0 : 0 < k := by
    by_contra hk0
    push_neg at hk0
    have : (fr * L) ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk0
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc Real.log S ≤ Real.log ((fr * L) ^ 2 * k) := Real.log_le_log h hSk
    _ = 2 * (Real.log fr + Real.log L) + Real.log k := by
      rw [Real.log_mul (by positivity) hk0.ne', Real.log_pow, Real.log_mul (by linarith) (by linarith)]; push_cast; ring
    _ ≤ 10 * L := by linarith

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover


end GlobalTheory.CovTop.ShortSpanUnitCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstants
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem ratRowAt_big : BigC fun _ ch _ _ => RatRowAt ch := by
  refine ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ hK
  intro Φ β d hd c i
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hd
  have hr := (hK.isRatAt hβ hτ hdτ c).2 i
  refine GlobalTheory.RatTop.exists_linearMap_of_repr_mem_range D.what₂.embLL (GlobalTheory.CoefModel.mapVV D.what₂.embLL _)
    (GlobalTheory.CoefModel.mapVV D.what₂.embLL _) (bVV D.what₂.LL _) (bVV ℂ _) (bVV ℂ _)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩)
    (fun k => ⟨_, (GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.1⟩) ?_ ?_ _ ?_
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k
    apply Subtype.ext
    rw [GlobalTheory.CoefModel.mapVV_coe, bVV_coe]
    exact ((GlobalTheory.Proof.TensorMapDescent.bVVfun_desc D.what₂.embLL _ k).choose_spec.2).symm
  · intro k l
    have h := hr k l
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at h

end GlobalTheory.KerConjMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstantsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants : BigC fun _ ch _ _ => RatRowAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratRowAt_big | exact GlobalTheory.KerConjMean.ratRowAt_big | (intros; apply GlobalTheory.KerConjMean.ratRowAt_big <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean GlobalTheory.SumSize.OppConj

namespace GlobalTheory.KerConjMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem le_of_ext (D : D7) (δ t0 : ℂ) (σ : D.what₂.LL →+* ℂ) (hfin : (ext D δ t0 σ).Finite) (hne : (ext D δ t0 σ).Nonempty)
    (a n G a' n' G' : ℝ) (ha : a ≤ a') (hn : n ≤ n') (hG : G ≤ G') (x B : ℝ) (hB : 0 ≤ B)
    (h : ∀ ρ ∈ ext D δ t0 σ, x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B) :
    x ≤ Real.exp (a' + n' * avg D δ t0 σ (hArea D δ t0) + G' * avg D δ t0 σ (hTh D δ t0)) * B := by
  obtain ⟨ρ, hρ, h1⟩ := (exists_avg _ hfin hne a' n' G' (hArea D δ t0) (hTh D δ t0)).1
  have hA : 0 ≤ hArea D δ t0 ρ := by unfold hArea; exact Real.posLog_nonneg
  have hT : 0 ≤ hTh D δ t0 ρ := by unfold hTh; exact Real.posLog_nonneg
  calc x ≤ Real.exp (a + n * hArea D δ t0 ρ + G * hTh D δ t0 ρ) * B := h ρ hρ
    _ ≤ Real.exp (a' + n' * hArea D δ t0 ρ + G' * hTh D δ t0 ρ) * B :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h1) hB

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem mapVV_conj_embLL {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (x : VV D.what₂.LL lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam x) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL lam (mapF (starRingEnd D.what₂.LL) lam x) := by
  rw [mapVV_mapF, embLL_comp_star, mapVV_mapVV]

theorem pairStdAt_of (C b C1 : ℝ)
    (hmA : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hmT : Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0)) ≤
      C1 * Real.log b)
    (hfin : ∀ σ : D.what₂.LL →+* ℂ, (ext D ch.S.Z.δ ch.S.Z.t0 σ).Finite ∧ (ext D ch.S.Z.δ ch.S.Z.t0 σ).Nonempty)
    (hRT : RatTopAt ch) (hCT : ConjTopAt ch (C / 2) b C1) (hRR : RatRowAt ch) (hCR : ConjRowAt ch (C / 2) b C1) :
    PairStdAt ch C b := by
  obtain ⟨a1, n1, G1, ha1, hn1, hG1, hs1, hb1⟩ := hCT
  obtain ⟨a2, n2, G2, ha2, hn2, hG2, hs2, hb2⟩ := hCR
  refine ⟨fun p => (a1 + a2) + (n1 + n2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    (G1 + G2) * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · have eA : aOne ch.G (C / 2) b + aOne ch.G (C / 2) b = aOne ch.G C b := by unfold aOne; ring
    refine (meanInf_affine _ (a1 + a2) (n1 + n2) (G1 + G2) _ _ (by linarith)).trans ?_
    have e1 := mul_le_mul_of_nonneg_left hmA (add_nonneg hn1 hn2)
    have e2 := mul_le_mul_of_nonneg_left hmT (add_nonneg hG1 hG2)
    nlinarith
  · intro p Φ β d hO c
    obtain ⟨hf0, hne⟩ := hfin p.embedding
    refine ⟨fun j B v hv => ?_, fun i B v hv => ?_⟩
    · obtain ⟨f, hf⟩ := hRT Φ β d hO c j
      obtain ⟨u, rfl, hu⟩ := hv
      refine ⟨f u, (hf u).symm, ?_⟩
      exact le_of_ext D _ _ p.embedding hf0 hne a1 n1 G1 _ _ _ (by linarith) (by linarith) (by linarith) _ B
        ((nrm_one_nonneg _ _).trans hu) (fun ρ hρ => hb1 Φ β d hO c j f hf p.embedding ρ hρ u B hu)
    · obtain ⟨f, hf⟩ := hRR Φ β d hO c i
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨mapF (starRingEnd D.what₂.LL) _ (f (mapF (starRingEnd D.what₂.LL) _ w)), ?_, ?_⟩
      · rw [conjMap, mapVV_conj_embLL, hf, mapVV_conj_embLL]
      · have hu : nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV (p.embedding.comp (starRingEnd D.what₂.LL)) _
            (mapF (starRingEnd D.what₂.LL) _ w)) ≤ B := by
          rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
        rw [mapVV_mapF]
        exact le_of_ext D _ _ p.embedding hf0 hne a2 n2 G2 _ _ _ (by linarith) (by linarith) (by linarith) _ B
          ((nrm_one_nonneg _ _).trans hw) (fun ρ hρ => hb2 Φ β d hO c i f hf p.embedding ρ hρ _ B hu)

end Std

end GlobalTheory.KerConjMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan
namespace GlobalTheory.Published

theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.AdjCalc

variable {K : Type} [Field K]

theorem comp_zpow' {X Y G : Over (Sp K)} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (m : ℤ) :
    f ≫ g ^ m = (f ≫ g) ^ m :=
  map_zpow (MonoidHom.mk' (fun g : Y ⟶ G => f ≫ g) (MonObj.comp_mul f)) g m

theorem isAdj_pt {A B : AbVar K} {c : Pic A.X.left} {d : Pic B.X.left} {f : A ⟶ B} {n : ℤ} {h : B ⟶ A}
    (H : IsAdj c d f n h) {Y : Over (Sp K)} (x : Y ⟶ A.X) (y : Y ⟶ B.X) :
    n • lam d (x ≫ f.hom) y = lam c x (y ≫ h.hom) := by
  have H' := congrArg (CechPic.pull (lift x y).left) H
  rw [map_zsmul, (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K A A c c c (𝟙 A) _ Y (lift x y) _ _).2.1,
    (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K B B d d d (𝟙 B) _ Y (lift x y) _ _).2.1] at H'
  simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using H'

end GlobalTheory.AV.AbVar.AdjCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiAwayIm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.XiAway

theorem xi_awayIm : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T, LocIn D.what₂.embLL (L.xiH t) →
      ∀ (m : ℕ) (y : (AE D)ˣ), GlobalTheory.KappaArith.AwayIm D m ((L.xi t y : Circle) : ℂ) := by
  intro D T L μ₀ hL t hx m y
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h := hL.xi t
  have h1 : L.xi t y ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (L.xi t ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D _ _ h n ho) y
  obtain ⟨ζ, hζ⟩ := GlobalTheory.TwistValues.char_mem (L.xi t) (L.xiH t) h hn ho D.what₂.embLL.fieldRange
    (fun P k => hx P (Formalism.L2.Host.atFin P k)) y
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by
    rw [map_pow, map_one]
    erw [hζ]
    have := congrArg (fun w : Circle => (w : ℂ)) h1
    simpa using this)
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.XiAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibres
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodRedProper

theorem isProper_of_proper_fibres :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  intro W L _ _ _ _ _ _ G _ h _ h2
  obtain ⟨a, b, c, d, e⟩ := h
  have := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  exact GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr W G.left G.hom inferInstance inferInstance inferInstance inferInstance inferInstance h2

end GlobalTheory.GoodRedProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupSchemeDvrOfProperFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → IsProper (GlobalTheory.SS.spFibre G).hom → IsProper G.hom := by
  first | exact @GlobalTheory.GoodRedProper.isProper_of_proper_fibres | exact GlobalTheory.GoodRedProper.isProper_of_proper_fibres | (intros; apply GlobalTheory.GoodRedProper.isProper_of_proper_fibres <;> assumption)
end
end
