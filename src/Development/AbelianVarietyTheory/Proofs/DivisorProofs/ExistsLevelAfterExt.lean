module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelAfterExt

theorem weilIs_of_ext {O C : Type} [Field O] [Field C] (β : O →+* C) {Q : PolAV (Sp O)}
    {Q' : PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left} (hQ : IsPolFibre β Q Q' ψ)
    (n : ℕ) (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (u : Oˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hw : WeilIs Q'.A Q'.L n (ObjPull.secPull hQ.2.1 x) (ObjPull.secPull hQ.2.1 y)
      (unitOn (Units.map β.toMonoidHom u))) : WeilIs Q.A Q.L n x y (unitOn u) := by
  have H := hQ.2.1
  have := Q.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (spMap β) (Category.comp_id _)
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hQ.2.2.symm _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (ObjPull.secPull_left H x) (ObjPull.secPull_left H y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (β.injective h₅)
  exact hc

theorem exists_ext_torsion (K : Type) [Field K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (σ : K'' →+* Ω) (Q : PolAV (Sp Ω)) (ψσ : Q.A.left ⟶ P.A.left) (hQ : IsPolFibre σ P Q ψσ),
        ∀ y, y ^ N = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y := by
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points K (torsion P₀.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp K) P₀.A P₀.isAb N hN).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro K'' Ω _ _ i f hf P ψ hP σ Q ψσ hQ y hy
  letI : Algebra K' K'' := i.toAlgebra
  letI : Algebra K K'' := f.toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq' hf.symm
  have hPg : IsGrpPullback P.A P₀.A (spMap f) ψ := hP.2.1
  have hQg : IsGrpPullback Q.A P.A (spMap σ) ψσ := hQ.2.1
  let x0 := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hx0 : x0 ^ N = 1 := by simp only [x0, ← map_pow, hy, map_one]
  have hx0l : x0.left = (y.left ≫ ψσ) ≫ ψ := rfl
  have hmul : x0 ≫ mulN P₀.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx0, Hom.one_def]
  let t0 : _ ⟶ torsion P₀.A N := pullback.lift x0 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι P₀.A N = x0 := pullback.lift_fst _ _ _
  have hs : ((𝟙_ (Over (Sp Ω))).hom ≫ spMap σ) ≫ spMap f = spMap (σ.comp f) := by
    rw [Category.assoc, spMap_comp_spMap]
    exact Category.id_comp _
  obtain ⟨w, hw⟩ := H K'' Ω σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion P₀.A N).hom = (𝟙_ (Over (Sp K''))).hom ≫ spMap f := by
    haveI : Epi (spMap σ) := by
      letI := σ.toAlgebra
      haveI : Flat (spMap σ) := by
        rw [HasRingHomProperty.Spec_iff (P := @Flat)]
        exact RingHom.flat_algebraMap_iff.2 inferInstance
      haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
      exact Flat.epi_of_flat_of_surjective _
    apply (cancel_epi (spMap σ)).1
    rw [← Category.assoc, hw, Over.w t0]
    refine hs.trans ?_
    rw [← spMap_comp_spMap]
    exact congrArg (spMap σ ≫ ·) (Category.id_comp _).symm
  let w1 : Over.mk ((𝟙_ (Over (Sp K''))).hom ≫ spMap f) ⟶ P₀.A :=
    Over.homMk (w ≫ (torsion.ι P₀.A N).left) (by rw [Category.assoc, Over.w, hw2]; rfl)
  let x := (ObjPull.pushEquiv hPg (𝟙_ _)).symm w1
  have hxl : x.left ≫ ψ = w ≫ (torsion.ι P₀.A N).left := ObjPull.pushEquiv_symm_left hPg _ w1
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← Category.assoc, hw, ← Over.comp_left, ht0, hx0l]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem exists_ext_level (K : Type) [Field K] [CharZero K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' : Type) [Field K''] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (g : ℕ), P.g = g → ∀ ze : K''ˣ, IsPrimitiveRoot (ze : K'') N →
      ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K'')) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
        (∀ x, lev x ^ N = 1) ∧ ∀ x y, WeilIs P.A P.L N (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_torsion K P₀ N hN
  refine ⟨K', inferInstance, inferInstance, hfin, fun K'' _ i f hf P ψ hP g hg ze hze => ?_⟩
  let Ω := AlgebraicClosure K''
  let σ : K'' →+* Ω := algebraMap K'' Ω
  haveI : CharZero Ω := (σ.comp f).charZero_iff (σ.comp f).injective |>.1 inferInstance
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 σ P
  obtain ⟨l, h₁, h₂, h₃⟩ := SiegPt.exists_level (O := Ω) (C := Ω) Q g N (Units.map σ.toMonoidHom ze) (hQ.1.trans hg)
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))) (hze.map_of_injective σ.injective)
  haveI : Epi (spMap σ) := by
    letI := σ.toAlgebra
    haveI : Flat (spMap σ) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext ((cancel_epi (spMap σ)).1 (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H K'' Ω i f hf P ψ hP σ Q φ hQ (l a) (h₂ a)
  have tors : ∀ a, t a ^ N = 1 := fun a => hinj (by rw [map_pow, ht, map_one, h₂])
  refine ⟨t, fun a b => hinj ?_, tors, fun a b => weilIs_of_ext σ hQ N _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, h₁]
  · rw [ht, ht, map_zpow]
    exact h₃ a b


end GlobalTheory.LevelAfterExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOne
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory


open IsLocalRing in
theorem valuationRing_atPrime_of_minimal {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ValuationRing (Localization.AtPrime q) := by
  have hT := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)
  have h1 : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime →
      Q' = maximalIdeal (Localization.AtPrime q) := by
    intro Q' hQ' hQ'p
    have hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q := by
      intro x hx
      by_contra hxq
      exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
    have hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥ := by
      intro h0
      apply hQ'
      rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
      rw [Ideal.under, h0, Ideal.map_bot]
    have heq := hmin _ hc hne hle
    rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
    rw [Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]
  have h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q),
      Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q) := ⟨h1, h2⟩
  exact (hT.out 4 2).mp h12

theorem mul_eq_mul_of_atPrime {A : Type} [CommRing A] [IsDomain A] (q : Ideal A) [q.IsPrime]
    (x y a : A) (s : q.primeCompl)
    (h : algebraMap A (Localization.AtPrime q) x * IsLocalization.mk' _ a s =
      algebraMap A (Localization.AtPrime q) y) : x * a = y * s := by
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  exact IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h

end GlobalTheory

namespace GlobalTheory

theorem exists_div_of_center_height_le_one : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring →
    (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) →
      ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) →
    ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  intro K _ R _ _ _ E hRE hyp e he
  classical
  let φ : R →+* E :=
    { toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : Ideal R := (IsLocalRing.maximalIdeal E).comap φ
  have hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1 := fun r => E.valuation_lt_one_iff (φ r)
  have hRv : ∀ r : R, E.valuation (r : K) ≤ 1 := fun r => (E.valuation_le_one_iff _).2 (hRE r.2)
  have hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1 := fun s hs =>
    le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))
  have hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E := by
    intro s hs
    rw [← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]
  have hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0 := by
    intro s hs h
    have := hv1 s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e
  dsimp only at hxy
  rw [IsFractionRing.mk'_eq_div] at hxy
  have hy0 : (algebraMap R K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  change ((x : R) : K) / ((y : R) : K) = e at hxy
  change ((y : R) : K) ≠ 0 at hy0
  by_cases hq : q = ⊥
  · have hyq : (y : R) ∉ q := by
      rw [hq, Ideal.mem_bot]
      intro h; apply hy0; rw [h]; rfl
    exact ⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩
  · have hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q := by
      intro p hp hp0 hpq
      refine le_antisymm hpq ?_
      intro r hr
      refine hyp p hp hp0 (fun t ht => ?_) r ?_
      · exact E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))
      · exact E.mem_nonunits_iff.2 ((hqmem r).1 hr)
    haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime q) x)
      (algebraMap R (Localization.AtPrime q) y)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c
    dsimp only at hc
    have hsq : (s : R) ∉ q := s.2
    rcases hc with hc | hc
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      by_cases haq : a ∈ q
      · exfalso
        have hea : e * (a : K) = ((s : R) : K) := by
          rw [← hxy]
          field_simp
          linear_combination hK
        have h1 := hv1 _ hsq
        rw [← hea, map_mul] at h1
        have hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K) :=
          mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)
        have := (hqmem a).1 haq
        rw [h1] at hle
        exact absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)
      · refine ⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩
        rw [← hxy, div_eq_div_iff hy0 (hne0 a haq)]
        linear_combination hK
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      refine ⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩
      rw [← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]
      linear_combination -hK

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDense
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDense
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AffineDense

theorem sInf_minimalPrimes_eq_bot (R : Type) [CommRing R] [IsReduced R] :
    sInf (minimalPrimes R) = ⊥ := by
  rw [minimalPrimes, Ideal.sInf_minimalPrimes]
  exact nilradical_eq_zero R

theorem exists_minimal_ge_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (P : Ideal R) (hP : Disjoint (P : Set R) (nonZeroDivisors R)) :
    ∃ q ∈ minimalPrimes R, P ≤ q := by
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hsub : (P : Set R) ⊆ ⋃ i ∈ (↑t : Set (Ideal R)), ((fun I : Ideal R => I) i : Set R) := by
    intro a ha
    have hnz : a ∉ nonZeroDivisors R := fun h => Set.disjoint_left.1 hP ha h
    rw [mem_nonZeroDivisors_iff] at hnz
    push_neg at hnz
    obtain ⟨b, hba, hb⟩ : ∃ b, b * a = 0 ∧ b ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨x, hx, hx0⟩ := hnz (fun x hx => h x (by rw [mul_comm]; exact hx))
      exact hx0 (h x hx)
    have hb' : b ∉ sInf (minimalPrimes R) := by
      rw [sInf_minimalPrimes_eq_bot]; exact hb
    rw [Ideal.mem_sInf] at hb'
    push_neg at hb'
    obtain ⟨q, hq, hbq⟩ := hb'
    have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
    have haq : a ∈ q := (hqp.mem_or_mem (hba ▸ q.zero_mem)).resolve_left hbq
    simp only [Set.mem_iUnion]
    exact ⟨q, by rw [ht]; exact hq, haq⟩
  obtain ⟨q, hqt, hPq⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i ∈ minimalPrimes R := by rw [← ht]; exact hi
    exact Ideal.minimalPrimes_isPrime this)).1 hsub
  exact ⟨q, by rw [← ht]; exact hqt, hPq⟩

theorem exists_annihilator_of_minimal {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : ∃ s ∉ q, ∀ a ∈ q, s * a = 0 := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  have hqp : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  have hnle : ¬ (t.erase q).inf (fun I : Ideal R => I) ≤ q := by
    rw [hqp.inf_le']
    rintro ⟨i, hi, hiq⟩
    have him : i ∈ minimalPrimes R := by rw [← ht]; exact Finset.mem_of_mem_erase hi
    have : q ≤ i := hq.2 ⟨Ideal.minimalPrimes_isPrime him, bot_le⟩ hiq
    exact Finset.ne_of_mem_erase hi (le_antisymm hiq this)
  obtain ⟨s, hs, hsq⟩ := Set.not_subset.1 hnle
  refine ⟨s, hsq, fun a ha => ?_⟩
  have : s * a ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro I hI
    by_cases hIq : I = q
    · subst hIq; exact I.mul_mem_left s ha
    · have hIt : I ∈ t.erase q := Finset.mem_erase.2 ⟨hIq, by rw [← Finset.mem_coe, ht]; exact hI⟩
      exact I.mul_mem_right a (Finset.inf_le (f := fun I : Ideal R => I) hIt hs)
  rw [sInf_minimalPrimes_eq_bot] at this
  exact this

theorem mem_of_dense_of_disjoint {R : Type} [CommRing R] [IsReduced R] [IsNoetherianRing R]
    (D : Set (PrimeSpectrum R)) (hDo : IsOpen D) (hD : Dense D) (P : PrimeSpectrum R)
    (hP : Disjoint (P.asIdeal : Set R) (nonZeroDivisors R)) : P ∈ D := by
  obtain ⟨q, hq, hPq⟩ := exists_minimal_ge_of_disjoint P.asIdeal hP
  obtain ⟨s, hsq, hs⟩ := exists_annihilator_of_minimal q hq
  let Q : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  obtain ⟨Q', hQ', hQ'D⟩ := hD.inter_open_nonempty (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen s).isOpen ⟨Q, hsq⟩
  have hle : Q ≤ Q' := by
    intro a ha
    have h0 : s * a ∈ Q'.asIdeal := by rw [hs a ha]; exact Q'.asIdeal.zero_mem
    exact (Q'.isPrime.mem_or_mem h0).resolve_left hQ'
  have hQD : Q ∈ D := ((PrimeSpectrum.le_iff_specializes Q Q').1 hle).mem_open hDo hQ'D
  exact ((PrimeSpectrum.le_iff_specializes P Q).1 hPq).mem_open hDo hQD

end GlobalTheory.AffineDense


open GlobalTheory.AffineDense in
theorem GlobalTheory.affineOpen_injects_to_dense : ∀ (X : Scheme.{0}) [IsReduced X] [IsLocallyNoetherian X] (U : X.Opens), Dense (U : Set X) → ∀ (W : X.Opens) (hW : IsAffineOpen W), ∃ (K : Type) (_ : CommRing K) (ρ : Γ(X, W) →+* K), Function.Injective ρ ∧ ⊤ ≤ (spMap ρ ≫ (show Sp Γ(X, W) ⟶ X from hW.fromSpec)) ⁻¹ᵁ U := by
  intro X _ _ U hU W hW
  haveI : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  refine ⟨Localization (nonZeroDivisors Γ(X, W)), inferInstance, algebraMap _ _,
    IsLocalization.injective _ le_rfl, ?_⟩
  intro x _
  have hD : Dense ((hW.fromSpec ⁻¹ᵁ U : (Spec Γ(X, W)).Opens) : Set (Spec Γ(X, W))) :=
    hU.preimage hW.fromSpec.isOpenEmbedding.isOpenMap
  have key := mem_of_dense_of_disjoint (R := Γ(X, W)) _ (hW.fromSpec ⁻¹ᵁ U).isOpen hD
    ((spMap (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))))).base x) ?_
  · exact key
  · rw [Set.disjoint_left]
    intro a ha hnzd
    have hu : IsUnit (algebraMap Γ(X, W) (Localization (nonZeroDivisors Γ(X, W))) a) :=
      IsLocalization.map_units _ (⟨a, hnzd⟩ : nonZeroDivisors Γ(X, W))
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingInjectsToRingMappingToDenseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_ring_injects_to_ring_mapping_to_dense : ∀ (X : Scheme.{0}) [IsReduced X] [IsLocallyNoetherian X] (U : X.Opens), Dense (U : Set X) → ∀ (W : X.Opens) (hW : IsAffineOpen W), ∃ (K : Type) (_ : CommRing K) (ρ : Γ(X, W) →+* K), Function.Injective ρ ∧ ⊤ ≤ (spMap ρ ≫ (show Sp Γ(X, W) ⟶ X from hW.fromSpec)) ⁻¹ᵁ U := by
  first | exact @GlobalTheory.affineOpen_injects_to_dense | exact GlobalTheory.affineOpen_injects_to_dense | (intros; apply GlobalTheory.affineOpen_injects_to_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DilChi
open GlobalTheory.ChiUnit

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (m : ℕ) :
    (m : 𝓞 E) ∈ (conjPl P).asIdeal ↔ (m : 𝓞 E) ∈ P.asIdeal := by
  show Formalism.L2.DIV.starOHom (m : 𝓞 E) ∈ P.asIdeal ↔ _
  rw [map_natCast]

theorem conjO_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (a : 𝓞 E) :
    Formalism.L2.DIV.starO a ∈ (conjPl P).asIdeal ↔ a ∈ P.asIdeal := by
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO a) ∈ P.asIdeal ↔ _
  rw [Formalism.L2.DIV.starO_starO]

theorem conjO_not_mem_sq {E : Type} [Field E] [NumberField E] [StarRing E] {P : Pl E} {a : 𝓞 E}
    (h : a ∉ P.asIdeal ^ 2) : Formalism.L2.DIV.starO a ∉ (conjPl P).asIdeal ^ 2 := by
  intro ha
  apply h
  have h1 : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) ∈ Ideal.map Formalism.L2.DIV.starOHom ((conjPl P).asIdeal ^ 2) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 : Ideal.map Formalism.L2.DIV.starOHom (conjPl P).asIdeal ≤ P.asIdeal := Ideal.map_comap_le
  have h3 := Ideal.pow_right_mono h2 2 h1
  rwa [show Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) = a from Formalism.L2.DIV.starO_starO a] at h3

theorem natCard_mem {E : Type} [Field E] [NumberField E] (P : Pl E) (h : Nat.card (kP P) ≠ 0) :
    ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := Nat.finite_of_card_ne_zero h
  letI := Fintype.ofFinite (kP P)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem units_mul_relation_rearrange_commRing {Rg : Type*} [CommRing Rg] (c e i s : Rg) (n : ℕ) (hc2 : c * c = c) (hce : c * e = 0) :
    c * (e * i + c * s + (1 - e - c)) ^ n + (1 - c) = 1 + c * (s ^ n - 1) := by
  have hca : c * (e * i + c * s + (1 - e - c)) = c * s := by
    linear_combination (i - 1) * hce + (s - 1) * hc2
  have hpow : ∀ m : ℕ, c * (e * i + c * s + (1 - e - c)) ^ m = c * s ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c * (e * i + c * s + (1 - e - c)) ^ (m + 1) = (c * (e * i + c * s + (1 - e - c)) ^ m) * (e * i + c * s + (1 - e - c)) := by ring
        _ = s ^ m * (c * (e * i + c * s + (1 - e - c))) := by rw [ih]; ring
        _ = c * s ^ (m + 1) := by rw [hca]; ring
  linear_combination hpow n

theorem detIdele_eq_locE (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (eQ : AE D) (heQ : IsIdemSum eQ Q)
    (ϖ : D.host.E) (z : GA D V)
    (hz : mt V z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)))
    (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) V z x) :
    (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (star ϖ ^ V.rank) := by
  have he : eQ * eQ = eQ := by
    classical
    obtain ⟨es, hes, hsum, horth⟩ := Formalism.IndefR.Fin.idemSum_orth Q eQ heQ
    rw [hsum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j hj hji => (horth i hi j hj (Ne.symm hji)).1) (fun h => absurd hi h)]
    exact (hes i hi).1
  have hc2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he]
  have hce : cA D eQ * eQ = 0 := by rw [mul_comm]; exact heQ.2
  have hs : incA D (star ϖ) = cA D (incA D ϖ) := rfl
  rw [hx, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Formalism.L2.JoinChr.locE
  rw [map_pow, hs]
  exact units_mul_relation_rearrange_commRing _ _ _ _ V.rank hc2 hce

theorem chi_unitOff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hK.chr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hK.pl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hK.fin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

end GlobalTheory.DilChi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_splitting_character_unit_off_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  first | exact @GlobalTheory.DilChi.chi_unitOff | exact GlobalTheory.DilChi.chi_unitOff | (intros; apply GlobalTheory.DilChi.chi_unitOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRing
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

namespace GlobalTheory.FlagMod.FieldFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem spMap_comp_spMap_cell {R R' U : Type} [CommRing R] [CommRing R'] [CommRing U] (f : R →+* R')
    (f' : R' →+* U) : spMap f' ≫ spMap f = spMap (f'.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom f')).symm

theorem base_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp MvPolynomial.C) ≫ tau (A.aff k.1) := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap_cell]
  rfl

theorem le_cellPt (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V := by
  rw [← hx, base_cellPt hZ k z hz]
  exact le_preimage_comp _ (tau_le (A.aff k.1) le_rfl)

theorem g_cellPt (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hV : ⊤ ≤ x ⁻¹ᵁ (A.k k.1).V)
    (en : En Dw.mult) :
    ∃ hu, z ≫ g en = pt (str x) (plk (fun (t : Let Dw.mult) r =>
      ((A.A k.1).map (ev x _ hV) * (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from
        (cellFrames hZ ht).uAt k z hz t.1)) r t.2) en.2.1) hu := by
  have hb := base_cellPt hZ k z hz
  set φ := (ev z _ hz).comp (cellθ κ k).toRingHom with hφ
  have hev : ev x _ hV = φ.comp MvPolynomial.C := by
    subst hx
    rw [ev_congr hb _ hV (hb ▸ hV)]
    exact ev_spMap_tau _ _ _
  have hstr : str x = (φ.comp MvPolynomial.C).comp (A.alpha k.1) := by
    refine LowRank.str_eq ?_
    rw [← hx, hb, Category.assoc, ← spMap_comp_spMap_cell (A.alpha k.1) (φ.comp MvPolynomial.C)]
    congr 1
    exact (spMap_ev_top _).symm
  obtain ⟨hu, e⟩ := hZ.plk.plk k.1 k.2 en
  have key : ∀ (f f' : c.F →+* S) (v v' : Fin (plN A.N en.1 + 1) → S) hv, f = f' → v = v' →
      ∃ hv', pt f v hv = pt f' v' hv' := by
    rintro f _ v _ hv rfl rfl
    exact ⟨hv, rfl⟩
  conv => enter [1, hu']; lhs; rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, e]
  have hspan : Ideal.span (Set.range (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)) = ⊤ := by
    rw [Set.range_comp, ← Ideal.map_span, hu, Ideal.map_top]
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (plN A.N en.1 + 1)) c.F) := MvPolynomial.gradedAlgebra
  have hmap : spMap φ ≫ pt (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F)))
      (plk (uvec (A.cv k.1) k.2) en.2.1) hu =
      pt (φ.comp (MvPolynomial.C.comp ((A.alpha k.1).comp (RingHom.id c.F))))
        (φ ∘ plk (uvec (A.cv k.1) k.2) en.2.1)
        hspan := by
    refine (ProjPoint.SpecMap_ofHom _ _ _ φ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  rw [hmap]
  refine key _ _ _ _ _ (by rw [hstr]; rfl) ?_
  rw [map_plk]
  congr 1
  funext t r
  rw [Function.comp_apply, uvec_cv]
  show φ _ = _
  rw [← Matrix.map_apply (f := φ), Matrix.map_mul, Matrix.map_map, hev]
  rfl

end GlobalTheory.FlagMod.FieldFlag

namespace GlobalTheory.FlagMod.FieldFlag

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ z z' x hx hx' hst
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z
  obtain ⟨k', hz'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover z'
  have hV := le_cellPt hZ k z hz hx
  have hV' := le_cellPt hZ k' z' hz' hx'
  have hM : ⊤ ≤ x ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    le_preimage_inf ((cellFrames hZ ht).inM hz hx) ((cellFrames hZ ht).inM hz' hx')

  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, (cellFrames hZ ht).vecAt k' z' hz' hx' σ i = ∑ j, b j i • (cellFrames hZ ht).vecAt k z hz hx σ j :=
    fun σ => exists_tri_of_eq ((cellFrames hZ ht).linearIndependent_vecAt k z hz hx σ) fun i => by
      rw [← (cellFrames hZ ht).step_eq k z hz hx, ← (cellFrames hZ ht).step_eq k' z' hz' hx', hst]
  choose B hB hBu hBe using ex
  obtain ⟨a, ha⟩ := A.tw S x k'.1 k.1 hV' hV hM

  have hU : ∀ σ, (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev x _ hM) *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k' z' hz' σ) =
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult σ)) S from (cellFrames hZ ht).uAt k z hz σ) * B σ := by
    intro σ
    ext r i
    have e := hBe σ i
    rw [(cellFrames hZ ht).sum_vecAt k z hz hx σ (fun j => B σ j i)] at e
    have e2 := vec_chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart x ((cellFrames hZ ht).inM hz hx)
      ((cellFrames hZ ht).inM hz' hx') hM (fun j => (cellFrames hZ ht).uAt k' z' hz' σ j i)
    have e3 := congrFun ((vec _ _ _).injective (e2.trans e)) r
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using e3

  have hc : ∀ (t : Let Dw.mult), (fun r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2) =
      ∑ j, (a * B t.1 j t.2 : S) • fun r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r j := by
    intro t
    funext r
    rw [ha, Matrix.smul_mul, Matrix.mul_assoc, hU t.1, ← Matrix.mul_assoc]
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have htri : Tri (fun (t : Let Dw.mult) r => ((A.A k.1).map (ev x _ hV) *
      (show Matrix (Fin (A.k k.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k z hz t.1)) r t.2)
      (fun (t : Let Dw.mult) r => ((A.A k'.1).map (ev x _ hV') *
      (show Matrix (Fin (A.k k'.1).M.n) (Fin (Dw.mult t.1)) S from (cellFrames hZ ht).uAt k' z' hz' t.1)) r t.2)
      (fun t => a * B t.1 t.2 t.2) := by
    rintro ⟨σ, i⟩
    have h1 := hc ⟨σ, i⟩
    dsimp only at h1 ⊢
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, h, rfl⟩)
    · rw [hB σ (show id i < id j from h), mul_zero, zero_smul]
      exact Submodule.zero_mem _
  refine hZ.ext _ z z' (hx.trans hx'.symm) fun en => ?_
  obtain ⟨hu, e⟩ := g_cellPt hZ ht k z hz hx hV en
  obtain ⟨hu', e'⟩ := g_cellPt hZ ht k' z' hz' hx' hV' en
  rw [e, e']
  have hd : IsUnit (∏ l, a * B (en.2.1 l).1 (en.2.1 l).2 (en.2.1 l).2) :=
    IsUnit.prod_univ_iff.2 fun l => a.isUnit.mul (hBu _ _)
  exact (pt_eq_pt_iff _ hu hu').2 ⟨hd.unit, by rw [plk_tri _ _ S A.N _ _ _ en.1 en.2.1 htri en.2.2]; rfl⟩

end GlobalTheory.FlagMod.FieldFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsEqOfSameStepsLocalRingStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_points_eq_of_same_steps_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ Z) (x : Sp S ⟶ Y.X) (hx : z ≫ π = x) (hx' : z' ≫ π = x), (∀ σ i, (cellFrames hZ ht).step z hx σ i = (cellFrames hZ ht).step z' hx' σ i) → z = z' := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.cell_sep | exact GlobalTheory.FlagMod.FieldFlag.cell_sep | (intros; apply GlobalTheory.FlagMod.FieldFlag.cell_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObject
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHom
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecLocalRingHomExtOfInjectiveLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R'), IsLocalHom φ → Function.Injective φ → ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), spMap φ ≫ x = spMap φ ≫ y → x = y := by
  first | exact @GlobalTheory.spec_local_hom_ext_of_injective | exact GlobalTheory.spec_local_hom_ext_of_injective | (intros; apply GlobalTheory.spec_local_hom_ext_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjection
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiftLocal

theorem toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective

theorem isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f :=
  ⟨fun a ha => by
    have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a
    rw [← h2]
    exact ha.map _⟩

theorem lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [AlgebraicGeometry.Spec.fromSpecStalk_eq']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

end GlobalTheory.LiftLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftLocalPointAlongAffineFlatSurjectionStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π] [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'), IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  first | exact @GlobalTheory.LiftLocal.lift | exact GlobalTheory.LiftLocal.lift | (intros; apply GlobalTheory.LiftLocal.lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem GlobalTheory.SiegLev.SQuot.eq_of_siegPB : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  intro h n N o o' _ _ ζ ζ' F j Q R _ _ x y s' c hxy hx hy
  haveI := Q.fin; haveI := Q.etale; haveI := Q.onto
  obtain ⟨R1, _, _, φ1, hl1, hφ1, x1, hx1⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R Q.X F.X Q.π x
  obtain ⟨R2, _, _, φ2, hl2, hφ2, y2, hy2⟩ := GlobalTheory.T.exists_lift_localPoint_along_affine_flat_surjection R1 Q.X F.X Q.π (spMap φ1 ≫ y)
  set g : Sp R2 ⟶ Sp R := spMap φ2 ≫ spMap φ1 with hg
  set x2 : Sp R2 ⟶ F.X := spMap φ2 ≫ x1 with hx2d
  have hx2 : x2 ≫ Q.π = g ≫ x := by simp only [x2, g, Category.assoc, hx1]
  have hy2' : y2 ≫ Q.π = g ≫ y := by simp only [g, Category.assoc, hy2]
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c2, hc2⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n o o ζ ζ (RingHom.id o) (Sp R) (Sp R2) s' (g ≫ s') g rfl (by rw [hid, Category.comp_id])).1 c
  have key : ∀ z : Sp R ⟶ Q.X, ∀ z2 : Sp R2 ⟶ F.X, z2 ≫ Q.π = g ≫ z → SiegPB c Q.univ z → SRel c2 F.univ 1 (N / n) z2 := by
    intro z z2 hz hcz
    have A := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n n n o o o ζ ζ ζ Q.X (Sp R) (Sp R2) Q.s s' (g ≫ s') Q.univ c c2 z g 1 1 1 ((sRel_one_one_iff _ _ _).2 hcz)).1
    have B : SRel c2 Q.univ 1 1 (g ≫ z) := A.1 ((sRel_one_one_iff _ _ _).2 hc2)
    have C := (GlobalTheory.T.siegelObjectPullbackLevelPower_calculus h n N n o o' o ζ ζ' ζ Q.X F.X (Sp R2) Q.s F.s (g ≫ s') Q.univ F.univ c2 Q.π z2 1 (N / n) 1 Q.low).1
    rw [hz] at C
    exact C.2 B
  have e := Q.fibre R2 x2 y2 (g ≫ s') c2 (by
      rw [← Q.base, ← Category.assoc, ← Category.assoc y2, hx2, hy2', Category.assoc, Category.assoc, hxy]; simp only [g, Category.assoc])
    (key x x2 hx2 hx) (key y y2 hy2' hy)
  rw [hx2, hy2'] at e
  have hcomp : spMap (φ2.comp φ1) = g := by
    simp only [g, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  exact GlobalTheory.T.spec_localRing_hom_ext_of_injective_localHom R R2 (φ2.comp φ1) inferInstance (hφ2.comp hφ1) Q.X x y (by rw [hcomp]; exact e)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelQuotientFamilyLocalPointsEqOfObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelQuotientFamily_local_points_eq_of_object : ∀ (h n N : ℕ) (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (ζ' : o') (F : SFam h N ζ') (j : o →+* o') (Q : SQuot F n ζ j) (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ Q.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'), x ≫ Q.s = y ≫ Q.s → SiegPB c Q.univ x → SiegPB c Q.univ y → x = y := by
  first | exact @GlobalTheory.SiegLev.SQuot.eq_of_siegPB | exact GlobalTheory.SiegLev.SQuot.eq_of_siegPB | (intros; apply GlobalTheory.SiegLev.SQuot.eq_of_siegPB <;> assumption)
end
end
