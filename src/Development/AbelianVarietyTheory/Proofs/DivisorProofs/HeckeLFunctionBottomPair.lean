module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideExtra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualLatticeVacuumReading
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineReadingAdelicNormEqTorusMeanSquare

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEulerFactorOfRamified
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.IndefR.Links (ChrEq)

noncomputable section

namespace GlobalTheory.UnrCharZeta

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open _root_.Formalism.L2.Host (HChar aboveF)
open GlobalTheory.CMVal (eulerFactor IsHeckeL)

section Seg

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

end Seg

variable {D : D7}

section Char

variable {E : Type} [Field E] [NumberField E]

theorem loc_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (ν⁻¹).loc w x = (ν.loc w x)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_single, ← GlobalTheory.CMVal.finPart_single, GlobalTheory.CMVal.finPart_inv]

theorem unrAt_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).UnrAt w ↔ ν.UnrAt w := by
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [loc_inv, inv_eq_one]

theorem val_inv (ν : HChar E) (w : HeightOneSpectrum (𝓞 E)) : (ν⁻¹).val w = (ν.val w)⁻¹ := by
  rw [← GlobalTheory.CMVal.finPart_unifAt, ← GlobalTheory.CMVal.finPart_unifAt, GlobalTheory.CMVal.finPart_inv]

end Char

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Global

section Bottom

open GlobalTheory.FunObj.SqNum (botBig botSmall)

end Bottom

end GlobalTheory.UnrCharZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitive
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

namespace GlobalTheory.NuOffPair

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  intro D T L sc μ₀ hL hF G t i j χ hχ
  classical
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ sfB G t → (nuH G t i j).UnrAt w := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw (GlobalTheory.BottomIPData.mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
    have hQ : ∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
      hw (e ▸ GlobalTheory.BottomIPData.under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
    have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hv
    have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hv (by
      have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
      fin_cases k
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
    have hxi : (L.xiH t).UnrAt w := by
      by_contra hn
      rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
      · exact hQ w hq rfl
      · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
    rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv
  have hram : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∈ sfB G t → ¬ (nuH G t i j).UnrAt w := by
    intro w hw
    by_cases h0 : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · exact GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j w h0
    · unfold GlobalTheory.BottomIPData.sfB at hw
      obtain ⟨P, hP, hPw⟩ := Finset.mem_image.1 hw
      have hP' : P ∈ L.Q t := by
        unfold locPl GlobalTheory.ChiGrid.Places.W0 at hP
        rcases Finset.mem_union.1 hP with h | h
        · exfalso
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
          apply h0
          rw [← hPw, G.pl.under_w hv]
          exact hv
        · exact h
      have := GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w P hP' hPw h0
      have e0 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
        mul_div_mul_right_eq_div _ _ _
      rwa [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)] at this
  refine ⟨fun w hw => (GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w).2 (hunr w ?_), fun Λ hΛ s => ?_⟩
  · exact hw
  have hT : GlobalTheory.CMVal.TrivOnF (nuH G t i j) := by
    have h := ((L.C.isMu0 j).triv.mul (hL.xi_triv t)).mul (G.ch.triv _ hm.1 hm.2).inv
    rw [nuH, div_eq_mul_inv]
    exact h
  have hu : ∀ w, GlobalTheory.LFun.UnrAt χ⁻¹ w ↔ (nuH G t i j)⁻¹.UnrAt w := fun w => by
    rw [GlobalTheory.UnrCharZeta.unrAt_inv, ← GlobalTheory.LFun.unrAt_iff_of_chrEq hχ w]
    exact ⟨fun h => inv_inv χ ▸ h.inv, fun h => h.inv⟩
  have hfam : GlobalTheory.LFun.charFam χ⁻¹ = GlobalTheory.LFun.heckeFam (nuH G t i j)⁻¹ := funext fun w => by
    by_cases h : (nuH G t i j)⁻¹.UnrAt w
    · rw [GlobalTheory.LFun.heckeFam_of_unrAt h, GlobalTheory.LFun.charFam, if_pos ((hu w).2 h), GlobalTheory.LFun.val_inv,
        GlobalTheory.LFun.val_eq_of_chrEq hχ, GlobalTheory.UnrCharZeta.val_inv]
    · rw [GlobalTheory.LFun.heckeFam_of_not_unrAt h, GlobalTheory.LFun.charFam, if_neg (mt (hu w).1 h)]
  have hΛ' := GlobalTheory.CMVal.isHeckeL_inv_of_trivOnF D.host.E (nuH G t i j) Λ hT hΛ
  have hr' : ∀ w ∈ GlobalTheory.LFun.above D.host.E ((sfB G t : Finset (FinPl D)) : Set (FinPl D)),
      ¬ (nuH G t i j)⁻¹.UnrAt w := fun w hw h =>
    hram w hw ((GlobalTheory.UnrCharZeta.unrAt_inv _ w).1 h)
  have heq : GlobalTheory.Cont.EqRight Λ (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) := ⟨1, fun z hz => by
    change Λ z = GlobalTheory.LFun.eulerProd _ (GlobalTheory.LFun.charFam χ⁻¹) z
    rw [hfam]
    exact (GlobalTheory.SqStep.heckeL_eq_of_ram hr' hΛ' hz).symm⟩
  exact (GlobalTheory.Cont.holValueAt_self (σ := s.re - 1) (fun z _ => hΛ.1.analyticAt z) (by linarith)).congr heq

end GlobalTheory.NuOffPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitiveStatement
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
theorem _root_.GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → D.host.F = maximalRealSubfield D.host.E →
  ∀ (G : GridData L sc) (t : T) (i j : Fin D.R.m) (χ : (AE D)ˣ →* Circle), ChrEq χ (nuH G t i j) →
    GlobalTheory.LFun.UnrOff χ ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) ∧
    ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ∀ s : ℂ,
      GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL χ⁻¹ ((sfB G t : Finset (FinPl D)) : Set (FinPl D))) s (Λ s) := by
  first | exact @GlobalTheory.NuOffPair.main | exact GlobalTheory.NuOffPair.main | (intros; apply GlobalTheory.NuOffPair.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIndexLocalNormNormalizingFactorEqPartial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIndexLocalNormNormalizingFactorEqPartial
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

namespace GlobalTheory.NormRatio

theorem conj_smul_le {D : D7} {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J :=
  EigUnit.conj_smul_mono D h

theorem exists_conj_place {D : D7} (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
      w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ∧
      ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w'' = w ∨ w'' = w' := by
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hp := w.isPrime
  have hpr : (D.host.conj • w.asIdeal).IsPrime := inferInstance
  have hnb : D.host.conj • w.asIdeal ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  let w' : HeightOneSpectrum (𝓞 D.host.E) := ⟨D.host.conj • w.asIdeal, hpr, hnb⟩
  have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv w w' := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have hiff := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w
  refine ⟨w', rfl, (hiff w').2 (Or.inr hc), fun w'' h => ?_⟩
  rcases (hiff w'').1 h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h1 hc)

theorem eq_top_of_eq_conj {D : D7} {𝔪 A B : Ideal (𝓞 D.host.E)} (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hA : 𝔪 ≤ A)
    (hB : 𝔪 ≤ B) (h : A = D.host.conj • B) : A = ⊤ :=
  top_le_iff.1 (hcop ▸ sup_le hA (h ▸ conj_smul_le hB))

theorem prod_Ioc_shift {M : Type} [CommMonoid M] (g : ℕ → M) (a a' : ℕ) :
    ∏ n ∈ Finset.Ioc a' (a + a'), g n = ∏ i ∈ Finset.Icc 1 a, g (a' + i) := by
  have e : Finset.Ioc a' (a + a') = (Finset.Icc 1 a).image (a' + ·) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro h; exact ⟨n - a', by omega, by omega⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; omega
  rw [e, Finset.prod_image fun x _ y _ h => by simpa using h]

theorem locIdx_mul_locNorm_mul_dSfun : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf →
    ∀ a a' : ℕ, 1 ≤ a' →
    (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  intro D 𝔪 Sf hG a a' ha'
  classical
  obtain ⟨hne, hcop, -, hS⟩ := hG
  set s : ℂ := (a' : ℂ) / 2 with hs_def
  have hs : 0 < s.re := by
    have : (1 : ℝ) ≤ a' := by exact_mod_cast ha'
    simp only [hs_def, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + a') v s with hf
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') hs).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Sf f)
  have hsplitf : Set.mulIndicator {v | v ∉ (∅ : Set (HeightOneSpectrum (𝓞 D.host.F)))} f =
      Set.mulIndicator {v | v ∉ (Sf : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Sf : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_setOf_eq, Finset.mem_coe, Set.mem_empty_iff_false]
    by_cases hv : v ∈ Sf <;> simp [hv]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E (∅ : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s =
      GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s * ∏ v ∈ Sf, f v :=
    h0.unique (h1.mul h2)
  set P := (normalizedFactors 𝔪).toFinset with hP
  have hw : ∀ I ∈ P, I.IsPrime ∧ I ≠ ⊥ ∧ 𝔪 ≤ I := by
    intro I hI
    obtain ⟨hp, hle⟩ := (Ideal.mem_normalizedFactors_iff hne).1 (Multiset.mem_toFinset.1 hI)
    exact ⟨hp, fun h => hne (le_bot_iff.1 (h ▸ hle)), hle⟩
  let W : P → HeightOneSpectrum (𝓞 D.host.E) := fun x => ⟨x.1, (hw x.1 x.2).1, (hw x.1 x.2).2.1⟩
  have hbij : ∏ v ∈ Sf, f v = ∏ x ∈ P.attach, f ((W x).under (𝓞 D.host.F)) := by
    symm
    refine Finset.prod_bij (fun x _ => (W x).under (𝓞 D.host.F)) (fun x _ => (hS _).2 ⟨W x, (hw x.1 x.2).2.2, rfl⟩)
      (fun x _ y _ hxy => ?_) (fun v hv => ?_) (fun x _ => rfl)
    · obtain ⟨w', hw', -, hall⟩ := exists_conj_place (W x)
      rcases hall (W y) hxy.symm with h | h
      · exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal h).symm
      · have h' : y.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
        exact absurd (eq_top_of_eq_conj hcop (hw y.1 y.2).2.2 (hw x.1 x.2).2.2 h') (hw y.1 y.2).1.ne_top
    · obtain ⟨w, hmw, rfl⟩ := (hS v).1 hv
      have hmem : w.asIdeal ∈ P := Multiset.mem_toFinset.2 ((Ideal.mem_normalizedFactors_iff hne).2 ⟨w.isPrime, hmw⟩)
      exact ⟨⟨w.asIdeal, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hloc : ∀ x : P, ((blockIdx (Ideal.absNorm x.1 : ℝ) ((normalizedFactors 𝔪).count x.1) a a' : ℝ) : ℂ) *
      ((((Ideal.absNorm x.1 : ℝ) ^ ((normalizedFactors 𝔪).count x.1 * a * a'))⁻¹ * glVol (Ideal.absNorm x.1 : ℝ) a : ℝ) : ℂ) *
      f ((W x).under (𝓞 D.host.F)) = 1 := by
    intro x
    obtain ⟨w', hw', hu, -⟩ := exists_conj_place (W x)
    have hne' : W x ≠ w' := by
      intro h
      have h' : x.1 = D.host.conj • x.1 := (congrArg HeightOneSpectrum.asIdeal h).trans hw'
      exact (hw x.1 x.2).1.ne_top (eq_top_of_eq_conj hcop (hw x.1 x.2).2.2 (hw x.1 x.2).2.2 h')
    have hsp : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((W x).under (𝓞 D.host.F)) :=
      ⟨W x, w', hne', rfl, congrArg HeightOneSpectrum.asIdeal hu⟩
    have hN : Ideal.absNorm ((W x).under (𝓞 D.host.F)).asIdeal = Ideal.absNorm x.1 :=
      GlobalTheory.ChainTw.TwPlaces.absNorm_under_of_ne hu.symm hne'
    have hq : (1 : ℝ) < (Ideal.absNorm x.1 : ℝ) := by
      have h1 : Ideal.absNorm x.1 ≠ 1 := fun h => (hw x.1 x.2).1.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      have h2 : Ideal.absNorm x.1 ≠ 0 := fun h => (hw x.1 x.2).2.1 (Ideal.absNorm_eq_zero_iff.1 h)
      exact_mod_cast (by omega : 1 < Ideal.absNorm x.1)
    have hd := GlobalTheory.ChainTw.dv_center_of_isSplit D.sp.cm.deg2 hsp a a'
    have hst := congrArg (fun r : ℝ => (r : ℂ)) (GlobalTheory.StdLoc.stdLoc_product hq ((normalizedFactors 𝔪).count x.1) a a')
    simp only [hf, hs_def, hd, hN, prod_Ioc_shift (fun n => (1 - (((Ideal.absNorm x.1 : ℕ) : ℂ) ^ n)⁻¹)) a a']
    push_cast at hst ⊢
    linear_combination hst
  rw [key]
  have hmain : (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * ∏ v ∈ Sf, f v = 1 := by
    rw [hbij, locIdx, locNorm, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_attach P,
      ← Finset.prod_attach P, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun x _ => hloc x
  linear_combination (GlobalTheory.LFun.dSfun D.host.E (Sf : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + a') s) * hmain

end GlobalTheory.NormRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIndexLocalNormNormalizingFactorEqPartialStatement
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
theorem _root_.GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ a a' : ℕ, 1 ≤ a' →
  (locIdx D 𝔪 a a' : ℂ) * (locNorm D 𝔪 a a' : ℂ) * GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) =
    GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) a (a + a') ((a' : ℂ) / 2) := by
  first | exact @GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun | exact GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun | (intros; apply GlobalTheory.NormRatio.locIdx_mul_locNorm_mul_dSfun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTransversalCongruenceMulNormEqLocalNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTransversalCongruenceMulNormEqLocalNorm
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

namespace GlobalTheory.NormRatio

theorem card_transversal_mul : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  intro D 𝔪 h𝔪 hcop a a' R hR hRu
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_reduction_maxLevel_unitary_mod_ideal D 𝔪 h𝔪 a

  have hker : ∀ k : ↥(intG D a), ρ k = 1 ↔ CongOne D 𝔪 (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) := by
    intro k
    constructor
    · intro h i j
      have h1 := (hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).1 (by
        rw [h]
        by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij])
      by_cases hij : i = j
      · subst hij; simpa [Matrix.sub_apply] using h1
      · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
    · intro h
      apply Units.ext
      ext i j
      refine ((hρ k i j (((1 : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) i j))).2 ?_).trans ?_
      · have h1 := h i j
        by_cases hij : i = j
        · subst hij; simpa [Matrix.sub_apply] using h1
        · simpa [Matrix.sub_apply, Matrix.one_apply_ne hij] using h1
      · by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.one_apply_ne hij]
  have hsurj : Function.Surjective ρ := by
    intro g'
    choose g hg using fun i j => Ideal.Quotient.mk_surjective (I := 𝔪)
      (((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) i j)
    have hgm : (Matrix.of g).map (Ideal.Quotient.mk 𝔪) =
        ((g' : GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) : Matrix (Fin a) (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
      ext i j; simp [hg]
    obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.exists_maxLevel_unitary_congr_mod_ideal D 𝔪 h𝔪 hcop a (Matrix.of g) (by rw [hgm]; exact Matrix.isUnits_det_units g')
    simp only [Matrix.of_apply] at hk'
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Units.ext
    ext i j
    exact ((hρ ⟨k, hk⟩ i j (g i j)).2 (hk' i j)).trans (hg i j)

  let f : R → GL (Fin a) (𝓞 D.host.E ⧸ 𝔪) := fun r => ρ ⟨r.1, hR r.1 r.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, hr⟩ ⟨r', hr'⟩ h
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * ⟨r', hR r' hr'⟩) = 1 := by
        rw [map_mul, map_inv]; exact inv_mul_eq_one.2 h
      have h2 : CongOne D 𝔪 (r⁻¹ * r') := (hker _).1 h1
      have h3 : CongOne D 𝔪 (r'⁻¹ * r') := by
        rw [inv_mul_cancel]
        exact (hker 1).1 (map_one ρ)
      obtain ⟨r₀, -, hu⟩ := hRu r' (hR r' hr')
      exact Subtype.ext ((hu r ⟨hr, h2⟩).trans (hu r' ⟨hr', h3⟩).symm)
    · intro g'
      obtain ⟨k, rfl⟩ := hsurj g'
      obtain ⟨r, ⟨hr, hc⟩, -⟩ := hRu k.1 k.2
      refine ⟨⟨r, hr⟩, ?_⟩
      have h1 : ρ (⟨r, hR r hr⟩⁻¹ * k) = 1 := (hker _).2 hc
      rw [map_mul, map_inv] at h1
      exact (inv_mul_eq_one.1 h1)
  have hcard : R.card = Nat.card (GL (Fin a) (𝓞 D.host.E ⧸ 𝔪)) := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.ofBijective f hf)]
  rw [hcard, GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors _ 𝔪 h𝔪 a, GlobalTheory.StdLoc.absNorm_eq_prod h𝔪, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, locNorm]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hq : (Ideal.absNorm w : ℝ) ≠ 0 := by
    have hw0 : w ≠ ⊥ := fun h => by
      rw [h] at hw; exact zero_notMem_normalizedFactors _ (Multiset.mem_toFinset.1 hw)
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hw0)
  set q : ℝ := (Ideal.absNorm w : ℝ)
  set c := (normalizedFactors 𝔪).count w
  have e : (q ^ c) ^ (a * (a + a')) = q ^ (c * a ^ 2) * q ^ (c * a * a') := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [e, mul_inv, ← mul_assoc, mul_comm (q ^ (c * a ^ 2)) _, mul_assoc, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq)]
  ring

end GlobalTheory.NormRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTransversalCongruenceMulNormEqLocalNormStatement
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
theorem _root_.GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (a a' : ℕ) (R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D a)),
  (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) →
    (R.card : ℝ) * ((Ideal.absNorm 𝔪 : ℝ) ^ (a * (a + a')))⁻¹ = locNorm D 𝔪 a a' := by
  first | exact @GlobalTheory.NormRatio.card_transversal_mul | exact GlobalTheory.NormRatio.card_transversal_mul | (intros; apply GlobalTheory.NormRatio.card_transversal_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartan
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

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartanStatement
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
theorem _root_.GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  first | exact @GlobalTheory.NormRatio.exists_ipPair_one | exact GlobalTheory.NormRatio.exists_ipPair_one | (intros; apply GlobalTheory.NormRatio.exists_ipPair_one <;> assumption)
end
end

section
noncomputable section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compact
open Formalism.MainNotions.StandardLattice Matrix
open scoped TensorProduct ComplexOrder MatrixOrder

private theorem negDef_of_signature_aux {n q : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature G 0 q) : (-G).PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Formalism.UG.Jpq 0 q = -1 := by
    ext (i | i) (j | j)
    · exact i.elim0
    · exact i.elim0
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
  have h2 : (star P.1 * (-G).reindex e e * P.1).PosDef := by
    have e1 : (-G).reindex e e = -(G.reindex e e) := by ext i j; simp
    have : star P.1 * (-G).reindex e e * P.1 = 1 := by
      have hP' : star P.1 * G.reindex e e * P.1 = Formalism.UG.Jpq 0 q := hP
      rw [e1, Matrix.mul_neg, Matrix.neg_mul, hP', h1, neg_neg]
    rw [this]; exact Matrix.PosDef.one
  have h3 := ((Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h2).submatrix e.injective
  simpa using h3

private theorem exists_bound_definite_aux {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) :
    ∃ R : ℝ, ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → ∀ i j, ‖g i j‖ ≤ R := by
  rcases hG with hG | hG
  · exact GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
  · obtain ⟨R, hR⟩ := GlobalTheory.DefiniteQuotient.exists_bound_unitary hG
    refine ⟨R, fun g hg => hR g ?_⟩
    rw [Matrix.mul_neg, Matrix.neg_mul, hg]

private theorem definite_gramAt_aux {D : D7} (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.what₂.Tau) :
    (gramAt D V τ).PosDef ∨ (-gramAt D V τ).PosDef := by
  have h1 := hs (tauE D τ)
  rcases hd (tauE D τ) with h | h
  · left; rw [h] at h1; exact GlobalTheory.DefiniteQuotient.posDef_of_signature h1
  · right; rw [h] at h1; exact negDef_of_signature_aux h1

private theorem exists_compact_def_aux {D : D7} (V : HSp D) (hs : V.SigOK) (hd : V.IsDefinite) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : GlobalTheory.Mass.FiniteClasses (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) := by
    refine (GlobalTheory.Mass.finiteClasses_comap π (GlobalTheory.Mass.ratIn _ _ _) _ hπ.surjective hπ.injOn).2 ?_
    rw [hπ.map_ratIn]
    exact GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D) (GlobalTheory.DefiniteQuotient.gram_hermND V)
      (Formalism.L2.G.gram_totDef D.sp.cm V hs hd)
      (GlobalTheory.Mass.isCompact_stdLevel _ _ (GlobalTheory.DefiniteQuotient.gram_hermND V).2) (GlobalTheory.Mass.isOpen_stdLevel _ _)
  choose R hR using fun τ => exists_bound_definite_aux (definite_gramAt_aux V hs hd τ)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact D.host.F D.host.E).2
  obtain ⟨C', hC', hCe'⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ (∑ τ, |R τ|) C hC
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V).2 C' hC'
  have hsub : ∀ k : GA D V, π k ∈ GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram → k ∈ K := by
    intro k hk
    refine hKe k fun i j => hCe' _ (hCe _ ?_) fun τ => ?_
    · have := ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 hk i j).1
      rwa [hπ k] at this
    · have hJ : (V.gram.map (incA D)).map ((θ τ).comp (infPart D)) = gramAt D V τ := by
        ext i j; exact GlobalTheory.FockCompare.comp_incA hθ τ _
      have hu : Formalism.UG.cT (cA D) (mt V k) * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
      have e : (Formalism.UG.cT (cA D) (mt V k)).map ((θ τ).comp (infPart D)) =
          ((mt V k).map ((θ τ).comp (infPart D)))ᴴ := by
        ext i j; exact GlobalTheory.FockCompare.comp_cA hθ τ _
      have := congrArg (fun M => M.map ((θ τ).comp (infPart D))) hu
      simp only [Matrix.map_mul, e, hJ] at this
      exact ((hR τ _ this i j).trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun τ => |R τ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  haveI := hf.1
  refine ⟨⋃ c : Formalism.UG.ClassSet (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π),
    (fun k => c.out * k) '' K, isCompact_iUnion fun c => hK.image (continuous_const_mul _), fun h => ?_⟩
  obtain ⟨γ, hγ, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul (GQ V) ((GlobalTheory.Mass.stdLevel D.sp.cm.sig V.gram).comap π) h
  refine ⟨γ⁻¹, inv_mem hγ, _, Set.mem_iUnion.2 ⟨DoubleCoset.mk _ _ h, k⁻¹, hsub _ (inv_mem hk), rfl⟩, ?_⟩
  simp only [e]
  group

end Compact

set_option maxHeartbeats 4000000 in
private theorem integral_definiteUnitaryQuotient_eq_classSum_aux : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → Function.Injective ι → ι.range = GfC V →
  (∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n) →
  GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → Links.IsMeasDef V K μ 𝓕 →
  ∀ Φ : GA D V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsClassFun V K Φ →
    Finite (Cls D n J) ∧ Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ) (GlobalTheory.AutomorphicL2Unitary.autMeasure V μ) ∧
    ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V μ =
      ∑ᶠ x : Cls D n J, ((gam D J x.out : ℂ))⁻¹ * Φ (ι x.out) := by
  intro D V n ι J K μ 𝓕 hV hinj hran hrat hK hJ hμ Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.1
  haveI : μ.IsHaarMeasure := hμ.1.1
  have hF : IsFundamentalDomain (GQ V) 𝓕 μ := hμ.2
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) Φ := hΦ.left
  let Ψ : Formalism.MainNotions.StandardLatticesGL3.GA D n →* Bridge.Gf V := (finHom V).rangeRestrict.comp ι
  have hΨi : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ GinfC V := congrArg Subtype.val hx
    have h2 : ι x ∈ GfC V := by rw [← hran]; exact ⟨x, rfl⟩
    exact hinj ((GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V h2 h1).trans (map_one ι).symm)
  have hΨs : Function.Surjective Ψ := by
    intro g
    obtain ⟨α, hα, e⟩ := GlobalTheory.Mem.FinPartLift.exists_gfC_finHom_eq V g
    rw [← hran] at hα
    obtain ⟨x, rfl⟩ := hα
    exact ⟨x, Subtype.ext e⟩
  have hratΨ : ∀ x, x ∈ ratG D n ↔ ∃ γ : GQ V, Bridge.ratF V γ = Ψ x := by
    intro x
    rw [← hrat x]
    constructor
    · rintro ⟨γ, hγ, h⟩; exact ⟨⟨γ, hγ⟩, Subtype.ext h⟩
    · rintro ⟨γ, h⟩; exact ⟨γ, γ.2, congrArg Subtype.val h⟩
  have hJΨ : ∀ x, x ∈ J ↔ Ψ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K := fun x =>
    (hJ x).symm.trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.mem_levelFin (ι x)).symm
  have hΨdef : ∀ x, Ψ x = (finHom V).rangeRestrict (ι x) := fun _ => rfl
  clear_value Ψ
  obtain ⟨e, he⟩ : ∃ e : Formalism.MainNotions.StandardLatticesGL3.GA D n ≃* Bridge.Gf V, ∀ x, e x = Ψ x :=
    ⟨MulEquiv.ofBijective Ψ ⟨hΨi, hΨs⟩, fun _ => rfl⟩
  have hre : ∀ y, Ψ (e.symm y) = y := fun y => (he _).symm.trans (e.apply_symm_apply y)
  obtain ⟨C, hC, hCe⟩ := exists_compact_def_aux V hV.1 hV.2
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover_of_compact (GQ V) (finHom V).rangeRestrict
    (finHom V).rangeRestrict_surjective (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) hK.1 hC hCe
  have hsurj : Function.Surjective fun a : Fin m => (DoubleCoset.mk (ratG D n) J (e.symm (c a)) : Cls D n J) := by
    intro q
    obtain ⟨a, γ, k, hk⟩ := hc (Ψ q.out)
    refine ⟨a, ?_⟩
    show DoubleCoset.mk (ratG D n) J (e.symm (c a)) = q
    conv_rhs => rw [← DoubleCoset.out_eq' q]
    rw [DoubleCoset.eq]
    refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
      (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
    apply hΨi
    simp only [map_mul, hre]
    exact hk
  haveI hfin : Finite (Cls D n J) := Finite.of_surjective _ hsurj
  haveI : Fintype (Cls D n J) := Fintype.ofFinite _
  have hreps : Bridge.IsReps (Bridge.ratF V) (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) (fun q : Cls D n J => Ψ q.out) := by
    intro g
    refine (hΨs g).elim fun x hx => ?_
    rw [← hx]
    refine ⟨DoubleCoset.mk (ratG D n) J x, ?_, ?_⟩
    · obtain ⟨h, hh, k, hk, hout⟩ := DoubleCoset.mk_out_eq_mul (ratG D n) J x
      obtain ⟨γ, hγ⟩ := (hratΨ h⁻¹).1 (inv_mem hh)
      refine ⟨γ, ⟨Ψ k⁻¹, (hJΨ _).1 (inv_mem hk)⟩, ?_⟩
      show Ψ x = Bridge.ratF V γ * Ψ (DoubleCoset.mk (ratG D n) J x).out * Ψ k⁻¹
      rw [hγ, hout, ← map_mul Ψ, ← map_mul Ψ]
      congr 1
      group
    · rintro q ⟨γ, k, hq⟩
      rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
      refine ⟨e.symm (Bridge.ratF V γ), (hratΨ _).2 ⟨γ, (hre _).symm⟩, e.symm k,
        (hJΨ _).2 (by rw [hre]; exact k.2), ?_⟩
      apply hΨi
      simp only [map_mul, hre]
      exact hq
  obtain ⟨-, hIO, hsum⟩ := GlobalTheory.DefiniteClassSum.classSumIntegral D V hV K hK μ 𝓕 hμ (Cls D n J)
    (fun q => Ψ q.out) hreps (fun q => ι q.out) (fun q => (hΨdef _).symm) Φ hΦ
  have hcard : ∀ x, Nat.card (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.classGroupAt V K (Ψ x)) = gam D J x := by
    intro x
    unfold gam
    refine Nat.card_eq_of_bijective (fun γ => ⟨e.symm (Bridge.ratF V γ.1), (hratΨ _).2 ⟨γ.1, (hre _).symm⟩,
      (hJΨ _).2 ?_⟩) ⟨?_, ?_⟩
    · simp only [map_mul, map_inv, hre]
      exact (Bridge.mem_stab _).1 γ.2
    · intro a b hab
      have h1 := congrArg (fun s : {γ : Formalism.MainNotions.StandardLatticesGL3.GA D n // γ ∈ ratG D n ∧ x⁻¹ * γ * x ∈ J} => Ψ s.1) hab
      simp only [hre] at h1
      exact Subtype.ext (GlobalTheory.FormInner.ratF_injective V h1)
    · rintro ⟨y, hy1, hy2⟩
      refine ((hratΨ y).1 hy1).elim fun γ hγ => ?_
      refine ⟨⟨γ, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
      · rw [hγ, ← map_inv Ψ, ← map_mul Ψ, ← map_mul Ψ]
        exact (hJΨ _).1 hy2
      · apply Subtype.ext
        apply hΨi
        exact (hre _).trans hγ
  refine ⟨hfin, ?_, ?_⟩
  · have h1 : MemLp (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ)) 1 (μ.restrict 𝓕) := by
      rw [hL.lift_descend]; exact memLp_one_iff_integrable.2 hIO
    exact memLp_one_iff_integrable.1 ((GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hF).2 h1)
  · show ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) Φ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) μ = _
    rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hF]
    simp only [hL.descend_mk]
    rw [hsum, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcard]

end
end

noncomputable section

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

namespace GlobalTheory.NormRatio

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_sum {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type}
    (s : Finset ι) (G : ι → Formalism.MainNotions.TaylorLogMetric.VC D a d → ℂ) (f : ι → WO S T → ℂ) (h : ∀ i ∈ s, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ip_eq (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) : ip S T ν 𝓕 f g = GlobalTheory.Ker.ipO ν 𝓕 f g := rfl

theorem ip_sum_left (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 (∑ i ∈ s, f i) g = ∑ i ∈ s, ip S T ν 𝓕 (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_left hψ hν.1 hν.2.1 (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j) hg

theorem ip_sum_right (hψ : IsStdChar D ψ (-1)) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) : ip S T ν 𝓕 g (∑ i ∈ s, f i) = ∑ i ∈ s, ip S T ν 𝓕 g (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact GlobalTheory.Size.ipO_add_right hψ hν.1 hν.2.1 hg (hf i) ((GlobalTheory.FinWeilO.thetaSub ψ S T).sum_mem fun j _ => hf j)

theorem isSphOff_sum {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {ι : Type} (s : Finset ι) (f : ι → WO S T → ℂ)
    (hf : ∀ i ∈ s, IsSphOff ψ S T LS LT Sf (f i)) : IsSphOff ψ S T LS LT Sf (∑ i ∈ s, f i) := by
  have key : ∀ u, (∀ i ∈ s, heisO ψ S T u (f i) = f i) → heisO ψ S T u (∑ i ∈ s, f i) = ∑ i ∈ s, f i := by
    intro u hu
    funext w
    simp only [heisO, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => congrFun (hu i hi) w
  exact ⟨fun u hu => key _ fun i hi => (hf i hi).1 u hu, fun e he u hu hh => key _ fun i hi => (hf i hi).2 e he u hu hh⟩

theorem isSphOff_pure (hθ : IsInfFam θ) {LS : Lat S} {LT : Lat T} {Sf : Finset (FinPl D)} {f : WO S T → ℂ}
    (hf : IsSphOff ψ S T LS LT Sf f) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (p : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f p) :=
  ⟨fun u hu => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any (nsmul_mem hu 2)), hf.1 u hu],
   fun e he u hu hh => by
    rw [← GlobalTheory.VacPairSchur.pT_heisO hθ sS BS sT BT f (GlobalTheory.FockLatVac.infPart_latO_any hu), hf.2 e he u hu hh]⟩

theorem volQ_eq_mass (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V) (h2 : Function.Injective ι) (h3 : ι.range = GfC V)
    (h4 : ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n)
    (h5 : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K) (h6 : ∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ intG D n)
    (h7 : Links.IsMeasDef V K μ 𝓕) : (volQ V μ : ℂ) = mass D n := by
  have h := (integral_definiteUnitaryQuotient_eq_classSum_aux V n ι (intG D n) K μ 𝓕 h1 h2 h3 h4 h5 h6 h7 (fun _ => 1)
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩).2.2
  simpa [GlobalTheory.AutomorphicL2Unitary.descend, volQ, mass] using h

theorem openOff_conj {V : HSp D} {L : Lat V} {Sf : Finset (FinPl D)} {a g b : GA D V} (ha : a ∈ openOff V L ∅)
    (hg : g ∈ openOff V L Sf) (hb : b ∈ openOff V L ∅) : a⁻¹ * g * b ∈ openOff V L Sf := fun v hv => by
  rw [map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem (ha v (Finset.notMem_empty v))) (hg v hv)) (hb v (Finset.notMem_empty v))

end General

section Translates

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)

theorem om_mul_one (om : GlobalTheory.Core.Rk.IP.WRep S T) (g g' : GA D S) (f : WO S T → ℂ) :
    om (g * g', 1) f = om (g, 1) (om (g', 1) f) := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem coef_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G) (x : G) :
    ip S T ν 𝓕 (om (ι x, 1) (∑ y ∈ R, om (ι y, 1) φ)) (∑ y ∈ R, om (ι y, 1) φ) =
      ∑ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * x * y), 1) φ) φ := by
  have hth : ∀ g : GA D S, IsThetaFunO ψ S T (om (g, 1) φ) := fun g => hom.om_pres _ _ hφ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [← om_mul_one]
  rw [ip_sum_left hom.std hν R _ (fun _ => hth _) ((GlobalTheory.FinWeilO.thetaSub _ _ _).sum_mem fun j _ => hth _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ip_sum_right hom.std hν R _ (fun _ => hth _) (hth _)]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have e : ι x * ι y = ι y' * ι (y'⁻¹ * x * y) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [ip_eq, ip_eq, ← GlobalTheory.Size.ipO_om hom hν.1 hν.2.1 (hth (ι (y'⁻¹ * x * y))) hφ (ι y', 1), ← om_mul_one, e]

theorem norm_sum (hom : IsWeilDatumO ψ S T χS χT om) (hν : IsCovolOne (ratL T S) ν 𝓕) {φ : WO S T → ℂ}
    (hφ : IsThetaFunO ψ S T φ) (R : Finset G)
    (h : ∀ y ∈ R, ∀ y' ∈ R, y' ≠ y → ip S T ν 𝓕 (om (ι (y'⁻¹ * y), 1) φ) φ = 0) :
    ip S T ν 𝓕 (∑ y ∈ R, om (ι y, 1) φ) (∑ y ∈ R, om (ι y, 1) φ) = (R.card : ℂ) * ip S T ν 𝓕 φ φ := by
  have h1 := coef_sum ι hom hν hφ R 1
  rw [map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h1
  have h2 : ∀ y ∈ R, ∑ y' ∈ R, ip S T ν 𝓕 (om (ι (y'⁻¹ * 1 * y), 1) φ) φ = ip S T ν 𝓕 φ φ := by
    intro y hy
    rw [Finset.sum_eq_single_of_mem y hy]
    · rw [mul_one, inv_mul_cancel, map_one, Prod.mk_one_one, map_one, Module.End.one_apply]
    · intro y' hy' hne
      rw [mul_one]
      exact h y hy y' hy' hne
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]

theorem mem_of_conj_mem {H : Subgroup G} {a b x : G} (ha : a ∈ H) (hb : b ∈ H) (h : a⁻¹ * x * b ∈ H) : x ∈ H := by
  have := mul_mem (mul_mem ha h) (inv_mem hb)
  rwa [show a * (a⁻¹ * x * b) * b⁻¹ = x by group] at this

theorem openOff_conj_hom {L : Lat S} {Sf : Finset (FinPl D)} {a g b : G} (ha : ι a ∈ openOff S L ∅)
    (hg : ι g ∈ openOff S L Sf) (hb : ι b ∈ openOff S L ∅) : ι (a⁻¹ * g * b) ∈ openOff S L Sf := by
  rw [map_mul, map_mul, map_inv]
  exact openOff_conj ha hg hb

theorem norm_arith {A B C : ℂ} {c N e : ℕ} {n v L : ℝ} (h1 : A = (c : ℂ) * B) (h2 : B = ((N : ℂ) ^ e)⁻¹ * C) (h3 : C = n)
    (h4 : n = v) (h5 : (c : ℝ) * ((N : ℝ) ^ e)⁻¹ = L) : A = (L : ℂ) * (v : ℂ) := by
  rw [h1, h2, h3, h4, ← h5]
  push_cast
  ring

end Translates

section Exact

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

theorem congOne_one (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : CongOne D 𝔪 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D N) := fun i j => by simp

theorem vac_eq_of_reads (h : IsExact P X r) {G : Formalism.MainNotions.TaylorLogMetric.VC D P.a P.d → ℂ} {f : WO X.A X.B → ℂ} (hF : P.F = G)
    (h1 : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r G f) : X.vac = f := by
  subst hF
  exact h.read.unique h1

theorem vac_eq_sum (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) {o : ℕ}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hF : P.F = ∑ y ∈ R, P.W.Om y 1 (cosetVec P 𝔪 o)) {φ : WO X.A X.B → ℂ}
    (hφ : Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ) : X.vac = ∑ y ∈ R, X.om (X.ιA y, 1) φ := by
  have h1 : ∀ y, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (P.W.Om y 1 (cosetVec P 𝔪 o)) (X.om (X.ιA y, 1) φ) := fun y => by
    have := h.reads_om hI y 1 (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o) hφ
    rwa [X.ιB.map_one] at this
  exact vac_eq_of_reads h hF (reads_sum R (fun y => P.W.Om y 1 (cosetVec P 𝔪 o)) (fun y => X.om (X.ιA y, 1) φ) fun y _ => h1 y)

theorem exists_reads_coset (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} (hm : 𝔪 ≠ ⊥) (o : ℕ) :
    ∃ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup (cosetVec P 𝔪 o) (GlobalTheory.FunObj.CosetTheta.cosetVec_mem_TT P hm o)

theorem exists_reads_vacuum (h : IsExact P X r) : ∃ f₀, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ :=
  GlobalTheory.T.exists_adelicTheta_reads_curveThetaFunction X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r h.setup P.e0
    (GlobalTheory.NormSum.VacMove.vac_TT (GlobalTheory.InducedType.induced_type D).1 P.crv P.vac.1)

theorem mem_openOff (h : IsExact P X r) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∈ intG D P.a) (Sf : Finset (FinPl D)) :
    X.ιA x ∈ openOff X.A (stdLat X.A) Sf := fun v _ =>
  (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)).2.1 hx v (Finset.notMem_empty v)

theorem norm_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a)
    (hRu : ∀ k ∈ intG D P.a, ∃! y, y ∈ R ∧ CongOne D 𝔪 (y⁻¹ * k)) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) :
    ip X.A X.B ν 𝓕 (∑ y ∈ R, X.om (X.ιA y, 1) φ) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = (R.card : ℂ) * ip X.A X.B ν 𝓕 φ φ := by
  refine norm_sum X.ιA h.weil hν hφ R fun y hy y' hy' hne =>
    horth _ (mem_openOff h (mul_mem (inv_mem (hR y' hy')) (hR y hy)) Sf) fun hc => hne ?_
  have h1 : CongOne D 𝔪 (y⁻¹ * y) := by rw [inv_mul_cancel]; exact congOne_one 𝔪 _
  exact (hRu y (hR y hy)).unique ⟨hy', hc.2⟩ ⟨hy, h1⟩

theorem supp_transl (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)}
    {R : Finset (Formalism.MainNotions.StandardLatticesGL3.GA D P.a)} (hR : ∀ y ∈ R, y ∈ intG D P.a) {φ : WO X.A X.B → ℂ} (hφ : IsThetaFunO X.ψ X.A X.B φ)
    {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (horth : ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
      ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0) {x : Formalism.MainNotions.StandardLatticesGL3.GA D P.a} (hx : x ∉ intG D P.a)
    (hx' : X.ιA x ∈ openOff X.A (stdLat X.A) Sf) :
    ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) (∑ y ∈ R, X.om (X.ιA y, 1) φ)) (∑ y ∈ R, X.om (X.ιA y, 1) φ) = 0 := by
  refine (coef_sum X.ιA h.weil hν hφ R x).trans ?_
  refine Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun y' hy' => horth _ ?_ fun hc => hx ?_
  · exact openOff_conj_hom X.ιA (mem_openOff h (hR y' hy') ∅) hx' (mem_openOff h (hR y hy) ∅)
  · exact mem_of_conj_mem (hR y' hy') (hR y hy) hc.1

theorem finite_data (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ}
    (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o) (ho : o + P.a ≤ P.d) :
    (∃ LB : Lat X.B, IsSelfDualC X.B LB ∧ IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf X.vac) ∧
    ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
      ip X.A X.B ν 𝓕 X.vac X.vac = (locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ) ∧
      ∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ip X.A X.B ν 𝓕 (X.om (X.ιA x, 1) X.vac) X.vac = 0 := by
  obtain ⟨R, hR, hRu, hF⟩ := hstd
  refine (exists_reads_coset h hm.1 o).elim fun φ hφ => ?_
  refine (exists_reads_vacuum h).elim fun f₀ hf₀ => ?_
  refine (GlobalTheory.T.exists_selfDualLattice_vacuumReading X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup).elim fun LB ⟨hLB, hz, hsph⟩ => ?_
  have hs₀ := hsph P.e0 P.vac.1 f₀ hf₀
  have hsd := (GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA 1) 1 h.std.frame.gramA X.rkA (h.std.ptA 1)).1
  have hv := vac_eq_sum hI h hm.1 hF hφ
  have hsφ := GlobalTheory.T.thetaCosetIndicatorReading_spherical_off_modulus P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ
  have hs := isSphOff_sum R (fun y => X.om (X.ιA y, 1) φ) fun y hy =>
    GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer X.ψ X.A X.B X.χA X.χB X.om h.weil _ _ hsd hLB Sf _ (mem_openOff h (hR y hy) Sf) φ hφ.1 hsφ
  refine ⟨⟨LB, hLB, by rw [hv]; exact hs⟩, fun ν 𝓕 hν => ?_⟩
  have horth := GlobalTheory.T.cosetVector_orthogonal_translate_finite_point P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ho ν 𝓕 hν
  refine ⟨?_, fun x hx hx' => by rw [hv]; exact supp_transl h hR hφ.1 hν horth hx hx'⟩
  have h3 := GlobalTheory.T.thetaCosetIndicatorReading_normSq_eq_absNorm_inv_mul_vacuum P X r h 𝔪 Sf o hm LB hLB hz f₀ φ hf₀ hs₀ hφ ν 𝓕 hν
  have h4 := GlobalTheory.T.thetaLineReading_adelicNorm_eq_torusMeanSquare X.ψ X.θ X.A X.B X.rkA X.rkB δ r h.setup LB hLB hz P.e0 P.vac.1 f₀ hf₀ hs₀ ν 𝓕 hν
  have h5 := GlobalTheory.T.card_transversal_congruence_mul_norm_eq_localNorm D 𝔪 hm.1 hm.2.1 P.a (P.d - P.a) R hR hRu
  rw [Nat.add_sub_cancel' P.a_le] at h5
  have h6 := norm_transl h hR hRu hφ.1 hν horth
  exact norm_arith (by rw [hv]; exact h6) h3 h4 P.vac.2.2.1 h5

end Exact

section Fock

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}

theorem var_injective (X : Data P) : Function.Injective X.var := by
  rintro ⟨τ, i, j⟩ ⟨τ', i', j'⟩ e
  simp only [Data.var, Prod.mk.injEq, Fin.cast_inj] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

theorem ip_fock (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) : ip X.A X.B ν 𝓕 (X.fock T) (X.fock T) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) * ip X.A X.B ν 𝓕 X.vac X.vac := by
  have h := GlobalTheory.FockIsometry.ipO_pureTensorO D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank) (fun _ => le_rfl) (fun _ => le_rfl)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) X.vac hX.2.vac_theta hX.2.vac_fock
    ν 𝓕 hν (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T)) =
      GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) := by
    rw [GlobalTheory.FockCoefReal.fockIp_eq_fock, GlobalTheory.LowRowFock.fock_rename_inj (var_injective X), ← GlobalTheory.FockCoefReal.fockIp_eq_fock]
  have e2 : ip X.A X.B ν 𝓕 X.vac X.vac = (nrm2 ν 𝓕 X.vac : ℂ) := GlobalTheory.Size.ipO_self ν 𝓕 X.vac
  exact h.trans (by rw [e, e2])

theorem ip_fock_zero (hX : IsDict P X) {ν : Measure (WO X.A X.B)} {𝓕 : Set (WO X.A X.B)} (hν : IsCovolOne (ratL X.B X.A) ν 𝓕)
    (T : Tup D P.a P.d P.n) {g : GA D X.A} (hg : g ∈ GfC X.A) (h0 : ip X.A X.B ν 𝓕 (X.om (g, 1) X.vac) X.vac = 0) :
    ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) = 0 := by
  refine (GlobalTheory.FockCoefSplit.pair_eq_inf D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => X.A.rank) (fun _ => X.B.rank)
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB)
    (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramA) (GlobalTheory.FockPolyInj.isONBasis_one hX.1.gramB) ν 𝓕 hν 1 (one_mem _) 1 (one_mem _)
    (MvPolynomial.rename X.var (minorPol D T)) (MvPolynomial.rename X.var (minorPol D T))).elim fun c hc => ?_
  have h1 := hc X.vac (X.om (g, 1) X.vac) hX.2.vac_theta (hX.2.weil.om_pres _ _ hX.2.vac_theta) hX.2.vac_fock
    fun τ => GlobalTheory.FockCoefSplit.fockVac_om_fin hX.2.weil hX.2.inf hg (one_mem _) τ _ hX.2.vac_theta (hX.2.vac_fock τ)
  have h2 := GlobalTheory.FockCoefSplit.om_fin_pureTensorO hX.2.weil hX.2.inf (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) hg
    (one_mem (GfC X.B)) hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  rw [GlobalTheory.VacPairSchur.thetaIP_eq_ipO, GlobalTheory.VacPairSchur.thetaIP_eq_ipO, ← h2, Prod.mk_one_one, X.om.map_one,
    Module.End.one_apply, ← ip_eq, ← ip_eq, h0, mul_zero] at h1
  exact h1

theorem isFockVec_fock (hX : IsDict P X) (T : Tup D P.a P.d P.n) :
    IsFockVec X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (X.fock T) :=
  GlobalTheory.FockSph.isFockVec_pureTensorO (sS := fun _ => 1) (sT := fun _ => 1) hX.2.weil.std hX.2.inf
    (GlobalTheory.SmoothVac.isCartanInv_one X.A hX.1.gramA) (GlobalTheory.SmoothVac.isCartanInv_one X.B hX.1.gramB) (fun _ => 1) (fun _ => 1)
    hX.2.vac_theta hX.2.vac_fock _

theorem wcoef_fock (hX : IsDict P X) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)) (T : Tup D P.a P.d P.n)
    (g : GA D X.A) {k : GA D X.A} (hk : k ∈ GinfC X.A) : wcoef X.om ν 𝓕 (X.fock T) (X.fock T) (g * k) =
      ip X.A X.B ν 𝓕 (X.om (g, 1) (X.fock T)) (X.fock T) := by
  rw [wcoef, om_mul_one, GlobalTheory.T.weilRep_real_fixes_fock_maximal_minors P X hX hX.2.infB k hk T]

end Fock

section Norm

variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}

def normFactor (D : D7) (δ t0 : ℂ) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  (normConst D ⊤ δ a n : ℂ) * mass D d * mass D a * fockSum D a d n * (vacNorm D ⊤ δ t0 a d : ℂ) /
    GlobalTheory.LFun.dSfun D.host.E (∅ : Set (FinPl D)) a d (((d - a : ℕ) : ℂ) / 2)

theorem collect {c I mB mA L dS d0 F l v : ℂ} (h : I * l * d0 = dS) (h0 : d0 ≠ 0) (hS : dS ≠ 0) :
    c * I * (mB * mA * (L / dS) * (F * (l * v))) = c * mB * mA * F * v / d0 * L := by
  rw [← h] at hS ⊢
  have h1 : I ≠ 0 := fun e => hS (by rw [e]; simp)
  have h2 : l ≠ 0 := fun e => hS (by rw [e]; simp)
  field_simp

end Norm

end GlobalTheory.NormRatio
