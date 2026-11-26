module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapSingleAtEmb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfSurjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.GeomConnConst

theorem algX_top_strHom (K : Type) [Field K] (C : Scheme.{0}) [Algebra K Γ(C, ⊤)] (c : K) :
    algX (strHom K C) ⊤ c = algebraMap K Γ(C, ⊤) c := by
  rw [algebraMap_eq_strHom K C c]
  simp [algX, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]

end GlobalTheory.GeomConnConst
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cxPts_eq_of_pt_eq {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {y y' : CxPts p (RingHom.id ℂ)}
    (h : y.1 (closedPoint ℂ) = y'.1 (closedPoint ℂ)) : y = y' := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X)
    (x := y.1 (closedPoint ℂ)) (U := ⊤) trivial
  have hy : y ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 hx
  have hy' : y' ∈ ptsIn p (RingHom.id ℂ) U := mem_ptsIn.2 (h ▸ hx)
  have hv : ∀ g : Γ(X, U), ev p (RingHom.id ℂ) U g y = 0 → ev p (RingHom.id ℂ) U g y' = 0 := by
    intro g hg
    by_contra hne
    have h₁ := (mem_ptsIn_basicOpen hy' g).2 hne
    have h₂ : y ∈ ptsIn p (RingHom.id ℂ) (X.basicOpen g) := mem_ptsIn.2 (h ▸ mem_ptsIn.1 h₁)
    exact (mem_ptsIn_basicOpen hy g).1 h₂ hg
  refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU hy hy' fun f => ?_)
  have e₀ : ev p (RingHom.id ℂ) U
      (f - ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U (ev p (RingHom.id ℂ) U f y)) y = 0 := by
    rw [ev_eq hy, map_sub, ← ev_eq hy, ← ev_eq hy, ev_algX hy]
    simp
  have e₁ := hv _ e₀
  rw [ev_eq hy', map_sub, ← ev_eq hy', ← ev_eq hy', ev_algX hy'] at e₁
  exact (sub_eq_zero.1 e₁).symm

theorem exists_cxPts_pt_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    ∃ y : CxPts p (RingHom.id ℂ), y.1 (closedPoint ℂ) = x := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨⟨y, -, hs⟩, -⟩ :=
    GlobalTheory.SpecialisationPts.nonempty_and_isPreconnected X p inferInstance U hU x hxU
  exact ⟨y, (hs.mem_closed hx rfl : _ ∈ ({x} : Set X))⟩

theorem ncard_cxPts_over_closed : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  intro Y Z hZ
  have : LocallyOfFiniteType Y.str := inferInstance
  have him : (fun y : CxPts Y.str (RingHom.id ℂ) => y.1 (closedPoint ℂ)) ''
      {y : CxPts Y.str (RingHom.id ℂ) | y.1 (closedPoint ℂ) ∈ Z} = Z := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := exists_cxPts_pt_eq Y.str (hZ x hx)
      exact ⟨y, hx, rfl⟩
  conv_rhs => rw [← him]
  exact (Set.InjOn.ncard_image fun _ _ _ _ h => cxPts_eq_of_pt_eq h).symm

end GlobalTheory.CompanionTheory.KoszulCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedPointsCountComplexStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_points_count_complex : ∀ (Y : Var ℂ) (Z : Set Y.X), (∀ x ∈ Z, IsClosed ({x} : Set Y.X)) → ({y : CxPts Y.str (RingHom.id ℂ) | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}).ncard = Z.ncard := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | exact GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.ncard_cxPts_over_closed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupport
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNumRed_eq_one_of_eq_singleton {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K (X := X))) (Z : Closeds X) {w : X}
    (hZ : (Z : Set X) = {w}) (P : Fin 0 → LB X) : interNumRed K Z P = 1 := by
  letI := algebraΓAlong K (redι Z)
  have hk := appTop_algebraMap_along K (redι Z)
  have hX : IsProper (strHom K (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hrange : Set.range (redι Z) = {w} := (range_redι Z).trans hZ

  have hsub : Subsingleton (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨fun a b => (redι Z).isEmbedding.injective ?_⟩
    have ha : redι Z a = w := by
      have : redι Z a ∈ Set.range (redι Z) := ⟨a, rfl⟩
      rwa [hrange] at this
    have hb : redι Z b = w := by
      have : redι Z b ∈ Set.range (redι Z) := ⟨b, rfl⟩
      rwa [hrange] at this
    rw [ha, hb]
  have hne : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have : w ∈ Set.range (redι Z) := by rw [hrange]; rfl
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  obtain ⟨p⟩ := hne
  have hAff : IsAffine (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    have hUt : U = ⊤ := top_le_iff.1 fun q _ => (Subsingleton.elim q p) ▸ hpU
    subst hUt
    haveI : IsAffine (⊤ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens).toScheme := hU
    exact IsAffine.of_isIso (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.topIso.inv
  haveI : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := ⟨p⟩
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    isIntegral_red (hZ ▸ isIrreducible_singleton)
  have hpr : IsProper (strHom K (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom hk]
    infer_instance
  haveI : IsFinite (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : Module.Finite K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    have hf := IsFinite.finite_app (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ⊤
      (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    have hc := hf.comp hi
    have e : algebraMap K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) =
        ((strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).app ⊤).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom :=
      RingHom.ext (algebraMap_eq_strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    rw [← RingHom.finite_algebraMap, e]
    exact hc
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤))
  have e1 : interNumRed K Z P =
      chi K (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    change interNumOn K (redι Z) P = _
    exact (interNumOn_eq_interNum_pull hk isEmptyElim).trans (interNum_of_isEmpty K _ _)
  rw [e1, chi_structureModule_of_isAffine]
  have e2 := (LinearEquiv.ofBijective (Algebra.linearMap K
    Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)) hbij).finrank_eq
  rw [← e2]
  simp

theorem chi_eq_ncard_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  intro K _ _ X _ hp F _ hd hlen
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hdim0 : ∀ w ∈ support F,
      topologicalKrullDim (closure ({w} : Set X)) = ((0 : ℕ) : WithBot ℕ∞) := by
    intro w hw
    have hle := (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.dim_closure_le_suppDim hw).trans hd
    have hne : topologicalKrullDim (closure ({w} : Set X)) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff]
      exact not_isEmpty_of_nonempty (α := (closure ({w} : Set X) : Set X))
        (h := ⟨⟨w, subset_closure rfl⟩⟩)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    rw [← ha] at hle ⊢
    have : a ≤ 0 := by exact_mod_cast hle
    have : a = 0 := le_antisymm this bot_le
    subst this
    rfl
  have hcl : ∀ x ∈ support F, IsClosed ({x} : Set X) := by
    intro x hx
    refine isClosed_of_closure_subset fun y hy => ?_
    have hys : y ∈ support F :=
      (isClosed_support F).closure_subset_iff.2 (Set.singleton_subset_iff.2 hx) hy
    exact (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.eq_of_mem_closure hd (hdim0 y hys) x hx hy).symm
  have hfin : (support F).Finite := by
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_support F)
    rw [hS]
    refine hSf.sUnion fun t ht => ?_
    have hg := (hSi t ht).isGenericPoint_genericPoint_closure
    have hgt : (hSi t ht).genericPoint ∈ t := by
      have := hg.mem
      rwa [(hSc t ht).closure_eq] at this
    have hgs : (hSi t ht).genericPoint ∈ support F := by
      rw [hS]
      exact ⟨t, ht, hgt⟩
    have e : t = {(hSi t ht).genericPoint} := by
      have := hg.def
      rw [(hSc t ht).closure_eq, (hcl _ hgs).closure_eq] at this
      exact this.symm
    rw [e]
    exact Set.finite_singleton _
  refine ⟨?_, hcl⟩
  have hP : ∀ i : Fin 0, ((finZeroElim : Fin 0 → LB X) i).IsLB := isEmptyElim
  have h := GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed K X hp (Fin 0)
    finZeroElim hP F (by simpa using hd) hfin.toFinset (fun w hw _ => hfin.mem_toFinset.2 hw)
  rw [interNum_of_isEmpty] at h
  rw [h, Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hws : w ∈ support F := hfin.mem_toFinset.1 hw
  have hlen1 : Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 1 := by
    refine le_antisymm (hlen w) (ENat.one_le_iff_ne_zero.2 fun h0 => ?_)
    have := Module.length_eq_zero_iff.1 h0
    exact (mem_support_iff.1 hws).exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  rw [hlen1, interNumRed_eq_one_of_eq_singleton hp _ (w := w) (hcl w hws).closure_eq]
  simp

end GlobalTheory.CompanionTheory.KoszulCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupportStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_char_zero_dim_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | exact GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDim
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDim
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem stalk_isRegularLocalRing_and_ringKrullDim_le :
    ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧
      ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  intro Y x
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  haveI hAr : IsRegularRing (Y.X.presheaf.stalk x) :=
    ExtendRig.isRegularRing_stalk isRegularRing_of_smooth ℂ Y.str x
  refine ⟨IsRegularLocalRing.of_isRegularRing_of_isLocalRing _, ?_⟩
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.X.isBasis_affineOpens (Opens.mem_top x)
  have hdim : ringKrullDim Γ(Y.X, U) = Y.dim :=
    SmoothDim.ringKrullDim_affineOpen ℂ _ Y.str _ inferInstance U hU ⟨x, hx⟩
  letI : Algebra Γ(Y.X, U) (Y.X.presheaf.stalk x) := (Y.X.presheaf.germ U x hx).hom.toAlgebra
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← hdim, IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (Y.X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

end GlobalTheory.CompanionTheory.KoszulCount
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VarietyStalkRegularDimStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variety_stalk_regular_dim : ∀ (Y : Var ℂ) (x : Y.X), IsRegularLocalRing (Y.X.presheaf.stalk x) ∧ ringKrullDim (Y.X.presheaf.stalk x) ≤ Y.dim := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | exact GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.stalk_isRegularLocalRing_and_ringKrullDim_le <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalks
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalks
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

section Alg

open Pointwise

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem smul_top_eq_ker (π : M →ₗ[R] N) (a : R) (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) :
    a • (⊤ : Submodule R M) = LinearMap.ker π := by
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker, hk]
  simp

theorem isWeaklyRegular_of_quotSMulTop (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop a M) l) :
    RingTheory.Sequence.IsWeaklyRegular N l :=
  (((Submodule.quotEquivOfEq _ _ (smul_top_eq_ker π a hk)).trans
    (π.quotKerEquivOfSurjective hπ)).isWeaklyRegular_congr l).1 h

theorem length_quot_eq_of_cut (π : M →ₗ[R] N) (hπ : Function.Surjective π) (a : R)
    (hk : ∀ t, π t = 0 ↔ ∃ u, a • u = t) (J : Ideal R) :
    Module.length R (N ⧸ (J • ⊤ : Submodule R N)) =
      Module.length R (M ⧸ ((Ideal.span {a} ⊔ J) • ⊤ : Submodule R M)) := by
  have hf : Function.Surjective ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) :=
    (Submodule.mkQ_surjective _).comp hπ
  have hker : (Ideal.span {a} ⊔ J) • (⊤ : Submodule R M) =
      LinearMap.ker ((J • ⊤ : Submodule R N).mkQ ∘ₗ π) := by
    have hmap : (J • ⊤ : Submodule R N) = (J • ⊤ : Submodule R M).map π := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hmap, Submodule.comap_map_eq, Submodule.sup_smul,
      Submodule.ideal_span_singleton_smul, smul_top_eq_ker π a hk, sup_comm]
  exact (((Submodule.quotEquivOfEq _ _ hker).trans
    (((J • ⊤ : Submodule R N).mkQ ∘ₗ π).quotKerEquivOfSurjective hf)).length_eq).symm

end Alg

section Cut

variable {X : Scheme.{0}} {L : LB X}

theorem germSec_cons {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec) {i : L.ι} {x : X} (hx : x ∈ L.U i) :
    (fun j => germSec ((Fin.cons s t : Fin (d + 1) → L.Sec) j) hx) =
      (Fin.cons (germSec s hx) (fun j => germSec (t j) hx) :
        Fin (d + 1) → X.presheaf.stalk x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp

theorem mono_cutHom_of_isSMulRegular [IsLocallyNoetherian X] (hL : L.IsLB) (F : X.Modules)
    [F.IsQuasicoherent] (s : L.Sec)
    (h : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i), IsSMulRegular (F.presheaf.stalk x :) (germSec s hx)) :
    Mono (cutHom F hL s) := by
  refine (mono_cutHom_iff F hL s).2 fun x hx => ?_
  obtain ⟨i, hi⟩ := GlobalTheory.ThickeningDetermines.exists_mem_chart hL x
  obtain ⟨u, hu⟩ := mem_assPoints_iff_exists.1 hx
  refine (Cartier.mem_nonzeroLocus_iff s i hi).2 ((X.mem_basicOpen _ x hi).2 ?_)
  by_contra hn
  have hm : germSec s hi ∈ maximalIdeal (X.presheaf.stalk x) := hn
  have h0 : u = 0 := (h x i hi).right_eq_zero_of_smul ((hu _).2 hm)
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 ((hu 1).1 (by simp [h0])))

end Cut

theorem mono_cutHom_and_goodStalks_cut {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB)
    (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec)
    (h : GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec)) :
    Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  have key : ∀ (x : X) (i : L.ι) (hx : x ∈ L.U i),
      IsSMulRegular (F.presheaf.stalk x :) (germSec s hx) ∧
        RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop (germSec s hx) (F.presheaf.stalk x :))
          (List.ofFn fun j => germSec (t j) hx) := fun x i hx => by
    have h₁ := (h x i hx).1
    rw [germSec_cons, List.ofFn_succ, RingTheory.Sequence.isWeaklyRegular_cons_iff] at h₁
    exact h₁
  refine ⟨mono_cutHom_of_isSMulRegular hL F s fun x i hx => (key x i hx).1, fun x i hx => ?_⟩
  have hπ := stalkLinear_surjective (cutπ F hL s) x
  have hk := (isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx
  refine ⟨isWeaklyRegular_of_quotSMulTop (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk _
    (key x i hx).2, ?_⟩
  have h₂ := (h x i hx).2
  rw [germSec_cons, Fin.range_cons, Ideal.span_insert] at h₂
  rw [length_quot_eq_of_cut (stalkLinear (cutπ F hL s) x) hπ (germSec s hx) hk]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperplaneCutGoodStalksStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplane_cut_good_stalks : ∀ {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} (hL : L.IsLB) (F : X.Modules) [IsFiniteQC F] {d : ℕ} (s : L.Sec) (t : Fin d → L.Sec), GoodStalks F (Fin.cons s t : Fin (d + 1) → L.Sec) → Mono (cutHom F hL s) ∧ GoodStalks (cut F hL s) t := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | exact GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.mono_cutHom_and_goodStalks_cut <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndep
open IsLocalRing RingTheory.Sequence

namespace GlobalTheory.CompanionTheory.RegSeq

theorem exists_ofList_append_eq_maximalIdeal {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    ∃ ys : List R, Ideal.ofList (List.ofFn f ++ ys) = maximalIdeal R ∧
      (List.ofFn f ++ ys).length = (maximalIdeal R).spanFinrank := by
  classical
  let W : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) (Set.range (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R)))
  let c := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ W)
  have hsurj : ∀ q : CotangentSpace R ⧸ W, ∃ x : maximalIdeal R,
      W.mkQ ((maximalIdeal R).toCotangent x : CotangentSpace R) = q := by
    intro q
    obtain ⟨w, rfl⟩ := W.mkQ_surjective q
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective w
    exact ⟨x, rfl⟩
  choose g hg using hsurj
  let s : Set (maximalIdeal R) :=
    Set.range (fun i => (⟨f i, hf i⟩ : maximalIdeal R)) ∪ Set.range (fun j => g (c j))
  let T : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s)
  have hWT : W ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨f i, hf i⟩, Or.inl ⟨i, rfl⟩, rfl⟩
  have hT : T = ⊤ := by
    have h1 : Submodule.map W.mkQ T = ⊤ := by
      rw [eq_top_iff, ← c.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨(maximalIdeal R).toCotangent (g (c j)), Submodule.subset_span ⟨g (c j), Or.inr ⟨j, rfl⟩, rfl⟩, hg _⟩
    have h2 := Submodule.comap_map_mkQ W T
    rw [h1, Submodule.comap_top] at h2
    rw [eq_top_iff, h2]
    exact sup_le hWT le_rfl
  have hspan : Submodule.span R s = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hT
  have hm : maximalIdeal R = Ideal.span (Subtype.val '' s) := by
    have h3 := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top, Submodule.coe_subtype] at h3
    exact h3.symm
  refine ⟨List.ofFn (fun j => (g (c j)).val), ?_, ?_⟩
  · apply le_antisymm
    · unfold Ideal.ofList
      rw [Ideal.span_le]
      intro x hx
      have hx' : x ∈ List.ofFn f ++ List.ofFn (fun j => (g (c j)).val) := hx
      rcases List.mem_append.mp hx' with h | h
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        exact hf i
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
        exact (g (c j)).2
    · refine le_trans hm.le ?_
      unfold Ideal.ofList
      apply Ideal.span_mono
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · obtain ⟨j, rfl⟩ := hx
        exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · rw [List.length_append, List.length_ofFn, List.length_ofFn,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = r := by
      simpa using finrank_span_eq_card hli
    omega

theorem isWeaklyRegular_ofFn {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    IsWeaklyRegular R (List.ofFn f) := by
  obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal f hf hli
  exact ((isWeaklyRegular_append_iff R _ _).1
    (GlobalTheory.isRegular_of_length_eq_spanFinrank h1 h2).toIsWeaklyRegular).1

theorem isWeaklyRegular_and_length_quotient_le_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ)
      (a : Fin d → R), ringKrullDim R ≤ d →
      LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
        ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧
        Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  intro R _ _ _ _ d a hd hli
  classical
  by_cases hall : ∀ j, a j ∈ maximalIdeal R
  · have hli' : LinearIndependent (ResidueField R)
        (fun i => ((maximalIdeal R).toCotangent ⟨a i, hall i⟩ : CotangentSpace R)) :=
      hli.comp (fun i => ⟨i, hall i⟩) (fun i j h => congrArg Subtype.val h)
    refine ⟨isWeaklyRegular_ofFn a hall hli', ?_⟩
    obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal a hall hli'
    have hsf : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    have hle : (maximalIdeal R).spanFinrank ≤ d := by
      have h3 := hsf.trans_le hd
      exact_mod_cast h3
    have hys : ys = [] := by
      rw [List.length_append, List.length_ofFn] at h2
      apply List.eq_nil_of_length_eq_zero
      omega
    subst hys
    rw [List.append_nil] at h1
    have hspan : Ideal.span (Set.range a) = maximalIdeal R := by
      rw [← h1]
      unfold Ideal.ofList
      congr 1
      ext x
      exact List.mem_ofFn.symm
    rw [hspan]
    have hs : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
    exact (Module.length_eq_one_iff.mpr hs).le
  · push_neg at hall
    obtain ⟨j1, hj1⟩ := hall
    have hex : ∃ n, ∃ h : n < d, a ⟨n, h⟩ ∉ maximalIdeal R := ⟨j1.val, j1.isLt, hj1⟩
    obtain ⟨n, hn, han, hmin⟩ : ∃ n, ∃ hn : n < d, a ⟨n, hn⟩ ∉ maximalIdeal R ∧
        ∀ k (hk : k < n), a ⟨k, lt_trans hk hn⟩ ∈ maximalIdeal R := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
      by_contra hc
      exact Nat.find_min hex hk ⟨lt_trans hk (Nat.find_spec hex).1, hc⟩
    have hu : IsUnit (a ⟨n, hn⟩) := by
      by_contra h
      exact han ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
    have htop : ∀ i, n < i → Ideal.ofList ((List.ofFn a).take i) = ⊤ := by
      intro i hi
      apply Ideal.eq_top_of_isUnit_mem _ _ hu
      apply Ideal.subset_span
      show a ⟨n, hn⟩ ∈ (List.ofFn a).take i
      refine List.mem_take_iff_getElem.mpr ⟨n, ?_, ?_⟩
      · rw [List.length_ofFn]
        exact lt_min hi hn
      · rw [List.getElem_ofFn]
    have hsub : ∀ (N : Submodule R R), N = ⊤ → ∀ r : R, IsSMulRegular (R ⧸ N) r := by
      rintro N rfl r x y _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    have hpre : IsWeaklyRegular R (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)) :=
      isWeaklyRegular_ofFn _ (fun k => hmin k k.2)
        (hli.comp (fun k : Fin n => ⟨⟨k, lt_trans k.2 hn⟩, hmin k k.2⟩) (fun x y h => by
          have h5 := congrArg (fun z : {j : Fin d // a j ∈ maximalIdeal R} => (z.1 : Fin d).val) h
          exact Fin.ext h5))
    have hpre' : List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩) = (List.ofFn a).take n := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_take]
        omega
      · intro i h1 h2
        simp [List.getElem_ofFn, List.getElem_take]
    refine ⟨(isWeaklyRegular_iff R _).2 (fun i hi => ?_), ?_⟩
    · rw [List.length_ofFn] at hi
      rcases lt_trichotomy i n with h | h | h
      · have hg := (isWeaklyRegular_iff R _).1 hpre i (by rw [List.length_ofFn]; exact h)
        have e1 : (List.ofFn a).take i =
            (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)).take i := by
          rw [hpre', List.take_take, min_eq_left h.le]
        rw [e1]
        simp only [List.getElem_ofFn] at hg ⊢
        exact hg
      · subst h
        simp only [List.getElem_ofFn]
        exact IsUnit.isSMulRegular _ hu
      · exact hsub _ (by rw [htop i h, Submodule.top_smul]) _
    · have hspan : Ideal.span (Set.range a) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨n, hn⟩, rfl⟩) hu
      rw [hspan]
      have hss : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.length_eq_zero_iff.mpr hss]
      exact zero_le_one

end GlobalTheory.CompanionTheory.RegSeq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndepStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakly_regular_of_cotangent_indep : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ) (a : Fin d → R), ringKrullDim R ≤ d → LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} => ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) → RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧ Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | exact GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | (intros; apply GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AePolynomialNonvanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AePolynomialNonvanishing
open MeasureTheory

namespace GlobalTheory.CompanionTheory.AePoly

theorem ae_eval_ne_zero_fin : ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin d → ℂ)), MvPolynomial.eval x Q ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro Q hQ
    have hex : ∃ x : Fin 0 → ℂ, MvPolynomial.eval x Q ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ (MvPolynomial.funext fun x => by simpa using h x)
    obtain ⟨x, hx⟩ := hex
    refine Filter.Eventually.of_forall fun y => ?_
    rwa [Subsingleton.elim y x]
  | succ d ih =>
    intro Q hQ
    have hP0 : MvPolynomial.finSuccEquiv ℂ d Q ≠ 0 :=
      (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv ℂ d).injective).2 hQ
    have hlc := ih _ (Polynomial.leadingCoeff_ne_zero.2 hP0)
    have hF : Continuous fun z : ℂ × (Fin d → ℂ) => (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simpa using (by fun_prop : Continuous fun a : ℂ × (Fin d → ℂ) => a.2 j)
    have hS : MeasurableSet
        {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0} :=
      (isClosed_eq ((MvPolynomial.continuous_eval Q).comp hF) continuous_const).measurableSet
    have hprod : ∀ᵐ z ∂((volume : Measure ℂ).prod (volume : Measure (Fin d → ℂ))),
        MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      rw [Measure.prod_apply_symm hS]
      have hz : (fun s : Fin d → ℂ => (volume : Measure ℂ) ((fun y => (y, s)) ⁻¹'
          {z : ℂ × (Fin d → ℂ) | MvPolynomial.eval (Fin.cons z.1 z.2 : Fin (d + 1) → ℂ) Q = 0}))
          =ᵐ[volume] 0 := by
        refine hlc.mono fun s hs => ?_
        have hR : (MvPolynomial.finSuccEquiv ℂ d Q).map (MvPolynomial.eval s) ≠ 0 := by
          intro h0
          apply hs
          have := congrArg (fun (p : Polynomial ℂ) => p.coeff
            (MvPolynomial.finSuccEquiv ℂ d Q).natDegree) h0
          simpa [Polynomial.coeff_map] using this
        refine measure_mono_null ?_ ((Polynomial.finite_setOfPred_isRoot hR).measure_zero volume)
        intro y hy
        simpa [Polynomial.IsRoot, MvPolynomial.eval_eq_eval_mv_eval'] using hy
      rw [lintegral_congr_ae hz]
      simp
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).quasiMeasurePreserving.ae hprod
    filter_upwards [h] with x hx
    have hc : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).1
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0 x).2 : Fin (d + 1) → ℂ) = x := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    rwa [hc] at hx

theorem measurePreserving_uncurry (M n : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm
      (volume : Measure (Fin M → Fin n → ℂ)) (volume : Measure (Fin M × Fin n → ℂ)) := by
  refine ⟨(MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : Fin M × Fin n => (volume : Measure ℂ)) fun s hs => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have h : (MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a => Set.univ.pi fun k => s (a, k) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall]
    rfl
  rw [h, volume_pi, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

theorem ae_eval_matrix_ne_zero : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 →
    ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  intro M n Q hQ
  have hQ' : MvPolynomial.rename (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n)) Q ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.rename_injective _ finProdFinEquiv.injective)).2 hQ
  have h1 := ae_eval_ne_zero_fin _ _ hQ'
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (M * n) => ℂ)
    (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))).quasiMeasurePreserving.ae h1
  have h3 := (measurePreserving_uncurry M n).quasiMeasurePreserving.ae h2
  filter_upwards [h3] with C hC
  rw [MvPolynomial.eval_rename] at hC
  have hfun : (MeasurableEquiv.piCongrLeft (fun _ : Fin (M * n) => ℂ)
      (finProdFinEquiv : Fin M × Fin n ≃ Fin (M * n))
      ((MeasurableEquiv.curry (Fin M) (Fin n) ℂ).symm C)) ∘ finProdFinEquiv =
      fun p => C p.1 p.2 := by
    funext p
    simp only [Function.comp]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rfl
  rwa [hfun] at hC

end GlobalTheory.CompanionTheory.AePoly
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AePolynomialNonvanishingStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_polynomial_nonvanishing : ∀ (M n : ℕ) (Q : MvPolynomial (Fin M × Fin n) ℂ), Q ≠ 0 → ∀ᵐ C ∂(volume : Measure (Fin M → Fin n → ℂ)), MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | exact GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero | (intros; apply GlobalTheory.CompanionTheory.AePoly.ae_eval_matrix_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersection
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem goodStalks_structureModule {X : Scheme.{0}} [IsLocallyNoetherian X] {L : LB X} {d : ℕ}
    (t : Fin d → L.Sec) (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) (h : CotIndep t) :
    GoodStalks (structureModule X) t := by
  intro x i hx
  have := hreg x
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.weakly_regular_of_cotangent_indep (X.presheaf.stalk x) d (fun j => germSec (t j) hx) (hdim x)
    (h x i hx)
  have e : ((structureModule X).presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    structureModuleStalkEquiv x
  refine ⟨(LinearEquiv.isWeaklyRegular_congr e _).2 h₁, ?_⟩
  set I := Ideal.span (Set.range fun j => germSec (t j) hx) with hI
  have hmap : (I • (⊤ : Submodule (X.presheaf.stalk x) ((structureModule X).presheaf.stalk x :))).map
      e.toLinearMap = I := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective,
      smul_eq_mul, Ideal.mul_top]
  rw [(Submodule.Quotient.equiv _ I e hmap).length_eq]
  exact h₂

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNum_eq_ncard {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K (X := X))) {L : LB X} (hL : L.IsLB) (d : ℕ) :
    ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists K F → suppDim F ≤ (d : ℕ) →
      ∀ t : Fin d → L.Sec, GoodStalks F t →
        interNum K F (fun _ : Fin d => L) =
            ((support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}).ncard : ℤ) ∧
          ∀ x ∈ support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)}, IsClosed ({x} : Set X) := by
  have := isNoetherian_of_isProjOver hp
  induction d with
  | zero =>
    intro F _ hF hd t hg
    have hlen : ∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1 := by
      intro x
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
      have h := (hg x i hi).2
      have e : Ideal.span (Set.range fun j : Fin 0 => germSec (t j) hi) = ⊥ := by simp
      rw [e, Submodule.bot_smul] at h
      rwa [(Submodule.quotEquivOfEqBot _ rfl).length_eq] at h
    obtain ⟨h₁, h₂⟩ := GlobalTheory.T.euler_char_zero_dim_support hp F hd hlen
    have e : support F ∩ {x | ∀ j : Fin 0, x ∉ nonzeroLocus (t j)} = support F := by simp
    rw [e, interNum_of_isEmpty]
    exact ⟨h₁, h₂⟩
  | succ d ih =>
    intro F _ hF hd t hg
    have hg' : GoodStalks F (Fin.cons (t 0) (Fin.tail t) : Fin (d + 1) → L.Sec) := by
      rwa [Fin.cons_self_tail]
    obtain ⟨hm, hc⟩ := GlobalTheory.T.hyperplane_cut_good_stalks hL F (t 0) (Fin.tail t) hg'
    have e : (fun _ : Fin (d + 1) => L) = Fin.cons L (fun _ : Fin d => L) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hS : support F ∩ {x | ∀ j, x ∉ nonzeroLocus (t j)} =
        support (cut F hL (t 0)) ∩ {x | ∀ j, x ∉ nonzeroLocus (Fin.tail t j)} := by
      rw [support_cut]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Fin.forall_fin_succ, Fin.tail]
      tauto
    rw [e, interNum_cons_eq_interNum_cut hL (t 0) (fun _ => hL) hF, hS]
    exact ih (cut F hL (t 0)) (FiniteCohTwists.cut hL _ hF) (suppDim_cut_le F hL (t 0) hd) _ hc

end GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem secVal_comb (Y : Var ℂ) (L : LB Y.X) {n : ℕ} (c : Fin n → ℂ) (b : Fin n → L.Sec) (i : L.ι)
    (y : CxPts Y.str (RingHom.id ℂ)) :
    secVal Y.str (RingHom.id ℂ) (∑ j, algebraMap ℂ Γ(Y.X, ⊤) (c j) • b j) i y =
      ∑ j, c j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
  have e : ∀ a : ℂ, algebraMap ℂ Γ(Y.X, ⊤) a = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str ⊤ a := fun a => by
    rw [← GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact (GlobalTheory.GeomConnConst.algX_top_strHom ℂ Y.X a).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, map_sum, secVal_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem koszul_count : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  intro Y Δ L r hL n b hb hP
  obtain ⟨Q, hQ, hC⟩ := GlobalTheory.T.generic_sections_cotangent_indep Y L hL n Y.dim b hb
  filter_upwards [GlobalTheory.T.ae_polynomial_nonvanishing _ _ Q hQ] with C hCQ
  have hct := hC C hCQ
  set t : Fin Y.dim → L.Sec := fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j with ht
  have hp : IsProjOver (strHom ℂ (X := Y.X)) := by
    rw [GlobalTheory.strHom_eq Y.algebraMap_Γ]
    exact Y.isProjOver
  have hg : GoodStalks (structureModule Y.X) t :=
    goodStalks_structureModule t (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).1) (fun x => (GlobalTheory.T.variety_stalk_regular_dim Y x).2) hct
  obtain ⟨h₁, h₂⟩ := interNum_eq_ncard hp hL Y.dim (structureModule Y.X)
    (Y.isAmple_projective_O_one.finiteCohTwists Y.algebraMap_Γ _)
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq]) t hg
  rw [support_structureModule, Set.univ_inter] at h₁ h₂
  have hset : {y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι),
      y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0} =
      {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ {x | ∀ j, x ∉ nonzeroLocus (t j)}} := by
    ext y
    simp only [Set.mem_setOf_eq]
    have key : ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) →
        (∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 ↔
          y.1 (IsLocalRing.closedPoint ℂ) ∉ nonzeroLocus (t k)) := fun k i hi => by
      rw [← secVal_comb Y L (C k) b i y, ← mem_ptsIn, ← secVal_ne_zero_iff (t k) hi, not_not]
    constructor
    · intro h k
      obtain ⟨i, hi⟩ := exists_mem_ptsIn hL.cover y
      exact (key k i hi).1 (h k i hi)
    · intro h k i hi
      exact (key k i hi).2 (h k)
  rw [hset, GlobalTheory.T.closed_points_count_complex Y _ h₂, ← h₁]
  exact (Var.inter_eq_of_toPic_eq (fun _ => hL) (fun _ => hP.toPic_eq)).symm

end GlobalTheory.CompanionTheory.KoszulCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_zero_count_eq_intersection : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.koszul_count | exact GlobalTheory.CompanionTheory.KoszulCount.koszul_count | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.koszul_count <;> assumption)
end
