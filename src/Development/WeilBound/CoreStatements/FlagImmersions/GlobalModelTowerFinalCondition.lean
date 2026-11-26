module

public import Development.WeilBound.CoreStatements.FlagImmersions.RootFlatOnHodgeOf
public import Development.WeilBound.CoreStatements.VolumeEquality.OnePieceB
public import Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan
public import Development.WeilBound.CoreStatements.VolumeEquality.PrimeIdealOfFromSpec
public import Development.WeilBound.CoreStatements.FlagImmersions.MemGenFibre
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntProj
public import Development.WeilBound.CoreStatements.FlagImmersions.LocalCmpOf
public import Development.WeilBound.CoreStatements.FlagImmersions.LogIdealNonpos

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RangeSubIff
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_sub_iff {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : Set X) : Set.range y ⊆ U ↔ centre y ∈ U := by
  refine ⟨fun h => h ⟨_, rfl⟩, ?_⟩
  rintro h _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact h

theorem mem_of_period {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty)
    (hty : IsTypeFn H D.p D.q ty) (j : c.F →+* ℂ) {U : Set (Xo.XF c)} (hU : IsClopen U) (i : Fin F.n)
    {P P' : (F.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    {x x' : Sp ℂ ⟶ Xo.XF c} (hx1 : x ≫ pullback.fst _ _ = F.u i P) (hx2 : x ≫ pullback.snd _ _ = spMap j)
    (hx1' : x' ≫ pullback.fst _ _ = F.u i P') (hx2' : x' ≫ pullback.snd _ _ = spMap j) (hx : centre x ∈ U) :
    centre x' ∈ U := by
  classical
  have hty' : IsTypeFn H (F.Di i).p (F.Di i).q ty := by
    rw [(F.sig i).1, (F.sig i).2]
    exact hty
  obtain ⟨B, Q, hBo, hBc, hQ, huniq⟩ := GlobalTheory.exists_period_domain_param E H (F.Di i) g ty hty'
  have hcond : spMap σ = spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [← F.over_σ i P hP, ← hx1, ← hx2, Category.assoc, Category.assoc, pullback.condition]
  let y : (Fin (F.Di i).dim → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b =>
    if hb : b ∈ B then pullback.lift (F.u i (Q b)) (spMap j) ((F.over_σ i _ (hQ.1 b hb)).trans hcond) else x
  have hy1 : ∀ b ∈ B, y b ≫ pullback.fst _ _ = F.u i (Q b) := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_fst]
  have hy2 : ∀ b ∈ B, y b ≫ pullback.snd _ _ = spMap j := fun b hb => by
    simp only [y, dif_pos hb, pullback.lift_snd]
  have hhol : IsHolTo B y :=
    GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback _ _)
      (GlobalTheory.LocLift.isHolTo_congr (F.hol i _ B Q hBo hQ).1 hy1)
      (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.HolFibre.isHolTo_const hBo (spMap j)) hy2)
  have hfind : ∀ R, IsPeriod (F.Di i) ty R → ∀ z : Sp ℂ ⟶ Xo.XF c, z ≫ pullback.fst _ _ = F.u i R →
      z ≫ pullback.snd _ _ = spMap j → ∃ b ∈ B, y b = z := by
    intro R hR z hz1 hz2
    obtain ⟨b, ⟨hb, h, hh⟩, -⟩ := huniq R hR
    refine ⟨b, hb, pullback.hom_ext ?_ ?_⟩
    · rw [hy1 b hb, hz1]
      exact (F.fibre i _ _ (hQ.1 b hb) hR).2 ⟨LinearEquiv.refl _ _, h, fun _ _ => rfl,
        fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hh⟩
    · rw [hy2 b hb, hz2]
  obtain ⟨b, hb, e⟩ := hfind P hP x hx1 hx2
  obtain ⟨b', hb', e'⟩ := hfind P' hP' x' hx1' hx2'
  by_contra hn
  let W : (Xo.XF c).Opens := ⟨U, hU.isOpen⟩
  let W' : (Xo.XF c).Opens := ⟨Uᶜ, hU.compl.isOpen⟩
  obtain ⟨t, -, ht, ht'⟩ := hBc.isPreconnected _ _ (hhol W 0).1 (hhol W' 0).1
    (fun t ht => by
      by_cases h : centre (y t) ∈ U
      · exact Or.inl ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W from h)⟩
      · exact Or.inr ⟨ht, GagaRat.top_le_of_centre_mem (show centre (y t) ∈ W' from h)⟩)
    ⟨b, hb, hb, GagaRat.top_le_of_centre_mem (show centre (y b) ∈ W from e ▸ hx)⟩
    ⟨b', hb', hb', GagaRat.top_le_of_centre_mem (show centre (y b') ∈ W' from e' ▸ hn)⟩
  exact (GagaRat.centre_mem ht'.2 : centre (y t) ∈ W') (GagaRat.centre_mem ht.2 : centre (y t) ∈ W)

theorem over_const [NumberField c.F] {m : ℕ} {T : Set (Fin m → ℂ)} {y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)}
    (hTc : IsPreconnected T) (hy : IsHolTo T y) {b b' : Fin m → ℂ} (hb : b ∈ T) (hb' : b' ∈ T) :
    y b ≫ pullback.snd _ _ = y b' ≫ pullback.snd _ _ := by
  have hemb : ∀ p : Sp ℂ ⟶ Xo.XF c, ∃ κ : c.F →+* ℂ, p ≫ pullback.snd _ _ = spMap κ := fun p =>
    ⟨(Spec.preimage (p ≫ pullback.snd _ _)).hom, by
      unfold spMap
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  choose κ hκy using fun b => hemb (y b)
  have hd : ∀ r : 𝓞 c.F, DifferentiableOn ℂ (fun b => κ b (r : c.F)) T := fun r => by
    have h3 := (GagaRat.isHolTo_comp (pullback.snd _ _) hy ⊤ ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv (r : c.F))).2
    have hset : T ⊆ {b ∈ T | ⊤ ≤ (y b ≫ pullback.snd _ _) ⁻¹ᵁ ⊤} := fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (r : c.F) = valAt' (y b ≫ pullback.snd _ _) ⊤ _
    rw [hκy b]
    exact (PullbackSections.valAt'_spMap (κ b) (r : c.F)).symm
  rw [hκy, hκy, GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected hTc κ hd hb hb']

theorem periodOf : PeriodOf := by
  intro hG E _ _ _ H D l Xo c _ Y U Z hp hq hU _ hgeom
  classical
  have hN : N1c := hG.1.2.2.1
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l Xo (algebraMap (KA l) ℂ) g ty (by omega) rfl hty
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  have hsm : SmoothOfRelativeDimension D.dim s :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hsm' : Smooth s := SmoothOfRelativeDimension.smooth D.dim s
  haveI := Y.jQ_open
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  haveI : IsPreimmersion Y.j := by
    show IsPreimmersion (Y.jQ ≫ pullback.fst _ _)
    infer_instance
  have hξ : IsCptGen Z.ξ₀ := GlobalTheory.T.generic_of_smooth_surjective c.F _ _ _ _ _ Y.j s hsm' rfl Z.gen (Y.j.stalkMap_surjective _)
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hcl : ConstClosed c.F Z.Ω := by
    rintro a ⟨f, hf, hfa⟩
    obtain ⟨x, hx⟩ := hgeom a ⟨f, hf, hfa⟩
    exact ⟨x, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx.symm⟩
  have hover : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ s = spMap (algebraMap c.F ℂ) →
      under x ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    intro x hx
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    erw [hx]
    exact GagaRat.spMap_comp _ _
  have hexF : ∀ x : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (x ≫ s ≠ spMap (algebraMap c.F ℂ) → r = 0) ∧
      (x ≫ s = spMap (algebraMap c.F ℂ) → ∀ k P, IsPeriod (FU.Di k) ty P → FU.u k P = under x → r = ((k : ℕ) : ℂ)) := by
    intro x
    by_cases hx : x ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover x hx)
      exact ⟨((k : ℕ) : ℂ), fun h => absurd hx h, fun _ k' P' hP' e' => by rw [FU.disj k k' P P' hP hP' (e.trans e'.symm)]⟩
    · exact ⟨0, fun _ => rfl, fun h => absurd h hx⟩
  choose F hF0 hF using hexF
  have hconst := SheetDecomposition.One.const_of_hol (algebraMap c.F ℂ) s Z.ξ₀ ⊤ F D.dim hsm Z.over_inc hξ hcl (by
    intro m T y hT hc hy _ b₁ hb₁ b₂ hb₂
    have hall : ∀ b ∈ T, y b ≫ s = y b₁ ≫ s := fun b hb => over_const hc hy hb hb₁
    by_cases h : y b₁ ≫ s = spMap (algebraMap c.F ℂ)
    · obtain ⟨i, hi⟩ := GlobalTheory.T.family_uniformisation_local_period E H D l Xo _ g ty FU m T (fun b => under (y b)) hT hc ⟨b₁, hb₁⟩
        (fun b hb => hover _ ((hall b hb).trans h)) (GagaRat.isHolTo_comp _ hy)
      have key : ∀ b ∈ T, F (y b) = ((i : ℕ) : ℂ) := fun b hb => by
        obtain ⟨B', P, -, m1, -, hP, e⟩ := hi b hb
        exact hF _ ((hall b hb).trans h) i (P b) (hP.1 b m1) (e b m1)
      rw [key b₁ hb₁, key b₂ hb₂]
    · rw [hF0 _ h, hF0 _ (by rw [hall b₂ hb₂]; exact h)])
  obtain ⟨x, hx, hxU⟩ := SheetDecomposition.One.exists_point (algebraMap c.F ℂ) s ⟨U, hU.isOpen⟩ (q := genPt Z.ξ₀) Z.genPt_mem
  have hxU' : centre x ∈ U := GagaRat.centre_mem hxU
  obtain ⟨i, P₀, hP₀, e₀⟩ := FU.onto _ (hover x hx)
  refine ⟨g, ty, FU, i, hty, fun y hy => ?_⟩
  rw [range_sub_iff]
  constructor
  · intro hyU
    obtain ⟨k, P, hP, e⟩ := FU.onto _ (hover y hy)
    have := hconst y x hy hx le_top le_top ((Z.closure _).1 hyU) ((Z.closure _).1 hxU')
    rw [hF _ hy k P hP e, hF _ hx i P₀ hP₀ e₀] at this
    obtain rfl : k = i := Fin.ext (Nat.cast_injective this)
    exact ⟨P, hP, e.symm⟩
  · rintro ⟨P, hP, e⟩
    exact mem_of_period FU hty _ hU i hP₀ hP e₀.symm hx e hy hxU'

end RootFieldNumerics.RF
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.CptEx
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

private theorem noetherianSpace_projectiveSpectrum {A σ : Type} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [IsNoetherianRing A] : TopologicalSpace.NoetherianSpace (ProjectiveSpectrum 𝒜) := by
  let f : ProjectiveSpectrum 𝒜 → PrimeSpectrum A := fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
  have hf : Topology.IsInducing f := by
    refine ⟨TopologicalSpace.ext_iff_isClosed.2 fun s => ?_⟩
    rw [isClosed_induced_iff, ProjectiveSpectrum.isClosed_iff_zeroLocus]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨PrimeSpectrum.zeroLocus t, PrimeSpectrum.isClosed_zeroLocus t, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).1 ht
      refine ⟨u, ?_⟩
      ext x
      simp [f, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  exact hf.noetherianSpace

theorem cptEx : CptEx := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐
  have hfr : ∀ x : ↥c.F, ∃ (a b : 𝓞 ↥c.F), (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 ∧ x * (algebraMap (𝓞 ↥c.F) ↥c.F) b = (algebraMap (𝓞 ↥c.F) ↥c.F) a := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥c.F) x
    have hb' : (algebraMap (𝓞 ↥c.F) ↥c.F) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩
  have hinj : Function.Injective (algebraMap (𝓞 ↥c.F) ↥c.F) := IsFractionRing.injective _ _
  obtain ⟨hpre, hflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.spMap_flat_preimmersion (algebraMap (𝓞 ↥c.F) ↥c.F) hinj hfr
  obtain ⟨jpre, jflat⟩ := GlobalTheory.CompanionTheory.Ar.Flat.j_flat_preimmersion Y hinj hfr
  haveI := hpre
  haveI := jpre
  haveI := Y.jQ_open
  haveI : TopologicalSpace.NoetherianSpace Y.X := by
    obtain ⟨N, i, hi, -⟩ := Y.proj
    have : TopologicalSpace.NoetherianSpace (PSpace (𝓞 ↥c.F) N) := by
      unfold PSpace
      letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := 𝓞 ↥c.F)
      exact noetherianSpace_projectiveSpectrum _
    exact i.isClosedEmbedding.isInducing.noetherianSpace
  have hfx : 𝔐.f (genPt 𝔐.ξ) = genPt 𝔐.ξ₀ := GlobalTheory.CompanionTheory.Ar.Dominates.map_genPt 𝔐.fn_over
  have hsx : Y.s (genPt 𝔐.ξ₀) ∈ Set.range (spMap (algebraMap (𝓞 ↥c.F) ↥c.F)) := by
    refine ⟨spMap 𝔐.cst (IsLocalRing.closedPoint Ω), ?_⟩
    have h2 := congrArg (fun g => g (IsLocalRing.closedPoint Ω)) 𝔐.cst_over
    have h3 : spMap (𝔐.cst.comp (algebraMap (𝓞 ↥c.F) ↥c.F)) = spMap 𝔐.cst ≫ spMap (algebraMap (𝓞 ↥c.F) ↥c.F) := by
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [h3] at h2
    simp only [Scheme.Hom.comp_apply] at h2
    rw [← hfx]
    exact h2.symm
  have hsx2 : genPt 𝔐.ξ₀ ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))) := by
    rw [Scheme.Pullback.range_fst]
    exact hsx
  obtain ⟨x', hx'⟩ := hsx2
  have hgen : ∀ {p z : ↥Y.X}, genPt 𝔐.ξ₀ ⤳ p → z ⤳ p → genPt 𝔐.ξ₀ ⤳ z := fun hp hz =>
    GlobalTheory.CompanionTheory.Ar.Flat.genPt_specializes_of_specializes 𝔐.ξ₀ 𝔐.gen₀ hp hz
  have hopen : IsOpen (closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.isOpen_of_isClosed_of_generizing _ isClosed_closure ?_
    intro a b hab hb
    exact specializes_iff_mem_closure.1 (hgen (specializes_iff_mem_closure.2 hb) hab)
  have hV : IsOpen ((pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base ⁻¹' closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)) :=
    hopen.preimage (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).continuous
  obtain ⟨q, hqV, u0, rfl⟩ := Y.jQ_dense.inter_open_nonempty _ hV
    ⟨x', by
      show (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base x' ∈ closure ({genPt 𝔐.ξ₀} : Set ↥Y.X)
      rw [hx']
      exact subset_closure rfl⟩
  have hsp : x' ⤳ Y.jQ u0 := by
    rw [← (pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).isEmbedding.isInducing.specializes_iff, hx']
    exact specializes_iff_mem_closure.2 hqV
  obtain ⟨u, hu⟩ := hsp.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨u0, rfl⟩
  have hju : Y.j u = genPt 𝔐.ξ₀ := by
    show (Y.jQ ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 ↥c.F) ↥c.F))).base u = genPt 𝔐.ξ₀
    rw [Scheme.Hom.comp_apply, hu, hx']
  have hmin : ∀ z, z ⤳ u → z = u := by
    intro z hz
    have h1 : Y.j z ⤳ genPt 𝔐.ξ₀ := hju ▸ hz.map Y.j.continuous
    have h2 : genPt 𝔐.ξ₀ ⤳ Y.j z := hgen (specializes_refl _) h1
    exact Y.j.isEmbedding.injective ((h1.antisymm h2).eq.trans hju.symm)
  obtain ⟨U, hU, huU⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {u} isIrreducible_singleton
  obtain ⟨Z⟩ := GlobalTheory.CompanionTheory.Ar.Flat.nonempty_cptOver_of_fraction hinj hfr Y U hU
  have hZu : genPt Z.ξ₀ = u := hmin _ ((Z.closure u).1 (huU rfl))
  obtain ⟨U', hU', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.cptOver_isOpen_isDomain E H D l Xo c (𝓞 ↥c.F) (algebraMap (𝓞 ↥c.F) ↥c.F) Y U Z
    ⟨hinj, inferInstance, hfr⟩
  refine ⟨U, Z, ⟨isClosed_of_mem_irreducibleComponents U hU, hU' ▸ U'.isOpen⟩, hU.1, ?_⟩
  have : genPt (Z.ξ₀ ≫ Y.j) = Y.j (genPt Z.ξ₀) := by
    unfold genPt
    exact Scheme.Hom.comp_apply _ _ _
  rw [this, hZu, hju]

end RootFieldNumerics.RF
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ExistsLiftGenFibre
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

namespace Pt

theorem numberField_of (L : Type) [Field L] (f : ℚ →+* L) (hf : f.FiniteType) : NumberField L := by
  haveI : CharZero L := charZero_of_injective_ringHom f.injective
  have e : f = algebraMap ℚ L := Subsingleton.elim _ _
  haveI : Algebra.FiniteType ℚ L := RingHom.finiteType_algebraMap.1 (e ▸ hf)
  exact { to_finiteDimensional := finite_of_finite_type_of_isJacobsonRing ℚ L }

theorem exists_quot (B : Type) [CommRing B] [Nontrivial B] [Algebra ℚ B] [Algebra.FiniteType ℚ B] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L), Nonempty (B →+* L) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  have h1 : (algebraMap ℚ B).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  haveI : NumberField (B ⧸ m) := numberField_of _ ((Ideal.Quotient.mk m).comp (algebraMap ℚ B))
    (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) h1)
  exact ⟨B ⧸ m, inferInstance, inferInstance, ⟨Ideal.Quotient.mk m⟩⟩

theorem exists_numberField {A Ω κ : Type} [CommRing A] [Field Ω] [CharZero Ω] [Finite κ] (e : A →+* Ω) (t : κ → Ω)
    (he : ∀ a, e a ∈ Algebra.adjoin ℤ (Set.range t)) (s : A) (hs : e s ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ε : A →+* L), ε s ≠ 0 := by
  classical
  let B : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (e s)⁻¹ (Set.range t))
  have hB : ∀ x ∈ Algebra.adjoin ℤ (Set.range t), x ∈ B := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
    | algebraMap r => simpa using intCast_mem B r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  haveI : Algebra.FiniteType ℚ B := by
    refine (Subalgebra.fg_iff_finiteType _).1 ⟨((Set.finite_range t).insert (e s)⁻¹).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset]
  obtain ⟨L, _, _, ⟨g⟩⟩ := exists_quot B
  let e' : A →+* B := e.codRestrict B fun a => hB _ (he a)
  refine ⟨L, inferInstance, inferInstance, g.comp e', ?_⟩
  have h1 : e' s * ⟨(e s)⁻¹, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hs)
  exact ((IsUnit.of_mul_eq_one _ h1).map g).ne_zero

theorem exists_point {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    [Finite κ] {x : κ → Ω} (hT : CoordTie ℤ ξ x) (W : X.Opens) (hW : genPt ξ ∈ W) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (z : Spec (CommRingCat.of L) ⟶ X), centre z ∈ W := by
  obtain ⟨c, hc⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨U, hU, hg, -, -, hr⟩ := SheetDecomposition.BBase.chart hT c hc.1
  obtain ⟨s, hsW, hsη⟩ := hU.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hg
  have h0 : SheetDecomposition.BBase.ev ξ U hg s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hg).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨L, _, _, ε, hε⟩ := exists_numberField (SheetDecomposition.BBase.ev ξ U hg) _ (fun a => (hr _).1 ⟨a, rfl⟩) s h0
  let φ : Γ(X, U) ⟶ CommRingCat.of L := CommRingCat.ofHom ε
  have hz : centre (Spec.map φ ≫ hU.fromSpec) ∈ U := by
    change _ ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨L, inferInstance, inferInstance, Spec.map φ ≫ hU.fromSpec, hsW ?_⟩
  have h1 := congrArg (fun g => g.hom s) (SheetDecomposition.ChartForm.germ_point hU φ hz)
  refine (Scheme.mem_basicOpen X s _ hz).2
    (isUnit_of_map_unit (Scheme.stalkClosedPointTo (Spec.map φ ≫ hU.fromSpec)).hom _ (IsUnit.mk0 _ ?_))
  intro h
  exact hε (h1.symm.trans h)

def primeOf {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : Ideal (𝓞 F) :=
  { carrier := {b | ‖κ (b : F)‖ < 1}
    add_mem' := fun {a b} ha hb => by
      have := IsUltrametricDist.norm_add_le_max (κ (a : F)) (κ (b : F))
      show ‖κ ((a + b : 𝓞 F) : F)‖ < 1
      push_cast
      rw [map_add (f := _)]
      exact this.trans_lt (max_lt ha hb)
    zero_mem' := by simp
    smul_mem' := fun a b hb => by
      show ‖κ ((a * b : 𝓞 F) : F)‖ < 1
      have h1 : ‖κ (a : F)‖ ≤ 1 := by
        have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
        exact_mod_cast this
      push_cast
      rw [map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans_lt hb }

theorem norm_int_le {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) (a : 𝓞 F) :
    ‖κ (a : F)‖ ≤ 1 := by
  have := HT.LatBasic.val_le_one (NormedField.valuation (K := ℂ_[p])) κ a
  exact_mod_cast this

theorem norm_eq_one {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : 𝓞 F}
    (h : a ∉ primeOf κ) : ‖κ (a : F)‖ = 1 := le_antisymm (norm_int_le κ a) (not_lt.1 h)

instance primeOf_isPrime {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : (primeOf κ).IsPrime where
  ne_top' := by
    rw [Ideal.ne_top_iff_one]
    show ¬ ‖κ ((1 : 𝓞 F) : F)‖ < 1
    simp
  mem_or_mem' := fun {a b} h => by
    by_contra hn
    rw [not_or] at hn
    have h' : ‖κ ((a * b : 𝓞 F) : F)‖ < 1 := h
    push_cast at h'
    rw [map_mul, norm_mul, norm_eq_one κ hn.1, norm_eq_one κ hn.2] at h'
    simp at h'

theorem primeOf_ne_bot {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) : primeOf κ ≠ ⊥ := by
  intro h
  have h1 : ((p : ℕ) : 𝓞 F) ∈ primeOf κ := by
    show ‖κ (((p : ℕ) : 𝓞 F) : F)‖ < 1
    have : κ (((p : ℕ) : 𝓞 F) : F) = algebraMap ℚ_[p] ℂ_[p] ((p : ℕ) : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rw [h, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

theorem exists_frac {F : Type} [Field F] [NumberField F] {p : Nat.Primes} (κ : F →+* ℂ_[p]) {a : F} (ha : ‖κ a‖ ≤ 1) :
    ∃ u s : 𝓞 F, s ∉ primeOf κ ∧ a = (u : F) * (s : F)⁻¹ := by
  let V := Localization.subalgebra.ofField F (primeOf κ).primeCompl (primeOf κ).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) (primeOf_ne_bot κ) V
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨x, hx⟩ | ⟨x, hx⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    exact ⟨u, s, hs, hx.symm.trans e⟩
  · obtain ⟨u, s, hs, e⟩ := x.2
    have e' : a⁻¹ = (u : F) * (s : F)⁻¹ := hx.symm.trans e
    by_cases h0 : a = 0
    · exact ⟨0, 1, (primeOf κ).primeCompl.one_mem, by simp [h0]⟩
    refine ⟨s, u, fun hu => ?_, ?_⟩
    · have h1 : ‖κ (u : F)‖ < 1 := hu
      have h2 := congrArg (fun t => ‖κ t‖) e'
      simp only [map_inv₀, map_mul, norm_mul, norm_inv, norm_eq_one κ hs, inv_one, mul_one] at h2
      have h3 : 0 < ‖κ a‖ := norm_pos_iff.2 ((map_ne_zero κ).2 h0)
      have := one_le_inv₀ h3 |>.2 ha
      linarith
    · rw [← inv_inv a, e', mul_inv, inv_inv, mul_comm]

theorem exists_dvr {L : Type} [Field L] [NumberField L] {p : Nat.Primes} (j : L →+* ℂ_[p]) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra V L)
      (_ : IsFractionRing V L), ∀ a : L, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V L).range := by
  let V := Localization.subalgebra.ofField L (primeOf j).primeCompl (primeOf j).primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (primeOf_ne_bot j) V
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, fun a => ⟨fun ha => ?_, ?_⟩⟩
  · obtain ⟨u, s, hs, e⟩ := exists_frac j ha
    exact ⟨⟨a, u, s, hs, e⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨u, s, hs, e⟩ := x.2
    have e' : algebraMap V L x = (u : L) * (s : L)⁻¹ := e
    rw [e', map_mul, map_inv₀, norm_mul, norm_inv, norm_eq_one j hs, inv_one, mul_one]
    exact norm_int_le j u

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem normalCpt_of_tie {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    (hX : ∀ q : X, IsDomain (X.presheaf.stalk q) ∧ IsIntegrallyClosed (X.presheaf.stalk q)) : NormalCpt ξ := by
  intro p a ha
  have hξ := hT.gen
  obtain ⟨hd, hc⟩ := hX p.1
  letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk p.1) Ω) := hξ.inj p
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : IsFractionRing (X.presheaf.stalk p.1) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨c, hc⟩ := hT.cover p
    obtain ⟨U, hU, hg, hm, -, -⟩ := SheetDecomposition.BBase.chart hT c hc.1
    have hp : p.1 ∈ U := (hm _).2 ⟨p.2, hc⟩
    obtain ⟨s, t, ht, e⟩ := SheetDecomposition.BBase.exists_frac hU ⟨genPt ξ, specializes_rfl⟩ hg hg (SheetDecomposition.BBase.mem_regAt_gen hξ z)
    have h0 := ((SheetDecomposition.BBase.unitAt_ev_iff hξ hU ⟨genPt ξ, specializes_rfl⟩ hg hg t).2 ht).1
    refine ⟨X.presheaf.germ U p.1 hp s, X.presheaf.germ U p.1 hp t, ?_⟩
    show z = genMap ξ p _ / genMap ξ p _
    rw [SheetDecomposition.BBase.genMap_germ p U hp hg, SheetDecomposition.BBase.genMap_germ p U hp hg, ← e, mul_div_cancel_left₀ _ h0]
  letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
  haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
    Algebra.IsIntegral.of_surjective (R := X.presheaf.stalk p.1) (A := X.presheaf.stalk p.1)
      (Algebra.ofId _ _) (genMap ξ p).rangeRestrict_surjective
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk p.1) (K := Ω)).1
    (isIntegral_trans (R := X.presheaf.stalk p.1) (A := regAt ξ p) a ha)
  exact ⟨b, hb⟩

theorem int_reg (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω) (q : Cpt ξ) (b : 𝓞 F) :
    ψ (b : F) ∈ regAt ξ q := hN q _ ((map_isIntegral_int ψ (RingOfIntegers.isIntegral_coe b)).tower_top)

theorem inv_reg {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z)
    {a : Ω} {r : R} (hv : ValAt ξ z a r) (hr : IsUnit r) : a⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  obtain ⟨h', g, rfl, rfl⟩ := hv
  obtain ⟨u, rfl⟩ : IsUnit g :=
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit g hr
  exact ⟨u⁻¹.val, map_units_inv _ u⟩

theorem exists_const (hξ : IsCptGen ξ) (hN : NormalCpt ξ) {F : Type} [Field F] [NumberField F] (ψ : F →+* Ω)
    {L : Type} [Field L] [CharZero L] (z : Spec (CommRingCat.of L) ⟶ X) (h : genPt ξ ⤳ centre z) :
    ∃ ψL : F →+* L, ∀ a, ValAt ξ z (ψ a) (ψL a) := by
  have hreg : ∀ a, ψ a ∈ regAt ξ ⟨centre z, h⟩ := by
    intro a
    have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
    haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
    have h1 := int_reg hN ψ ⟨centre z, h⟩ ⟨n • a, hi⟩
    have h2 : ValAt ξ z (n : Ω) (n : L) := ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩
    have h3 := inv_reg h h2 (IsUnit.mk0 _ (by exact_mod_cast hn))
    have e : ψ a = (n : Ω)⁻¹ * ψ (n • a) := by
      rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ (by exact_mod_cast hn)]
    rw [e]
    exact mul_mem h3 h1
  let e : X.presheaf.stalk (centre z) ≃+* regAt ξ ⟨centre z, h⟩ :=
    RingEquiv.ofBijective (genMap ξ ⟨centre z, h⟩).rangeRestrict
      ⟨fun a b hab => hξ.inj ⟨centre z, h⟩ (congrArg Subtype.val hab), (genMap ξ ⟨centre z, h⟩).rangeRestrict_surjective⟩
  refine ⟨(Scheme.stalkClosedPointTo z).hom.comp (e.symm.toRingHom.comp (ψ.codRestrict _ hreg)), fun a =>
    ⟨h, e.symm ⟨ψ a, hreg a⟩, congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hreg a⟩), rfl⟩⟩

theorem val_unique (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨_, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

end Val

theorem exists_lift_genFibre {F L : Type} [Field F] [NumberField F] [Field L] [CharZero L] {W : Scheme.{0}}
    (s : W ⟶ Spec (CommRingCat.of (𝓞 F))) (z : Spec (CommRingCat.of L) ⟶ W) :
    ∃ u : Spec (CommRingCat.of L) ⟶ pullback s (spMap (algebraMap (𝓞 F) F)), u ≫ pullback.fst _ _ = z := by
  let r : 𝓞 F →+* L := (Spec.preimage (z ≫ s)).hom
  have hr : z ≫ s = spMap r := by
    simp [r, spMap]
  have hinj : Function.Injective r := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
    have : (n : L) = 0 := by simpa using h0
    simpa using this
  have hr' : (IsFractionRing.lift (K := F) hinj : F →+* L).comp (algebraMap (𝓞 F) F) = r :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hinj a
  refine ⟨pullback.lift z (spMap (IsFractionRing.lift (K := F) hinj)) ?_, pullback.lift_fst _ _ _⟩
  rw [hr]
  conv_lhs => rw [← hr']
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end Pt

open Pt in
theorem pointEx : PointEx := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 F' _ _ ψ p κ' hgen
  classical
  haveI : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hN : NormalCpt 𝔐.ξ := normalCpt_of_tie 𝔐.tie (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩)
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  have hind : Topology.IsInducing (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing
  have hopen : IsOpen (Set.range Y.jQ) := by
    haveI := Y.jQ_open
    exact Y.jQ.isOpenEmbedding.isOpen_range
  obtain ⟨C, hC, hCe⟩ := hind.isClosed_iff.1 hopen.isClosed_compl
  let W : 𝔐.X.Opens := ⟨(𝔐.f ⁻¹' C)ᶜ, (hC.preimage 𝔐.f.continuous).isOpen_compl⟩
  have hW : genPt 𝔐.ξ ∈ W := by
    change 𝔐.f (genPt 𝔐.ξ) ∉ C
    rw [CptIn.Intr.genPt_dominates 𝔐.fn_over, hgen]
    have h1 : genPt (Z.ξ₀ ≫ Y.j) = pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) (Y.jQ (genPt Z.ξ₀)) := by
      simp [genPt, Model.j, Scheme.Hom.comp_apply]
      rfl
    rw [h1]
    intro hin
    have : Y.jQ (genPt Z.ξ₀) ∈ (Set.range Y.jQ)ᶜ := by
      rw [← hCe]
      exact hin
    exact this ⟨_, rfl⟩
  obtain ⟨L, _, _, zL, hzW⟩ := exists_point 𝔐.tie W hW
  have hint : 𝔐.Interior zL := by
    refine (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (centre zL)).1 ?_
    obtain ⟨u, hu⟩ := exists_lift_genFibre Y.s (zL ≫ 𝔐.f)
    let u₀ := u (IsLocalRing.closedPoint (CommRingCat.of L))
    have hfu : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) u₀ = 𝔐.f (centre zL) := by
      have := congrArg (fun g => g (IsLocalRing.closedPoint (CommRingCat.of L))) hu
      exact this
    have hr : u₀ ∈ Set.range Y.jQ := by
      by_contra hn
      have : u₀ ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' C := by
        rw [hCe]
        exact hn
      apply hzW
      rw [Set.mem_preimage, hfu] at this
      exact this
    rw [← Y.ab_gen] at hr
    rw [← hfu]
    exact hr
  obtain ⟨ψL, hψL⟩ := exists_const 𝔐.tie.gen hN ψ zL (𝔐.all _)
  obtain ⟨j, hj⟩ : ∃ j : L →+* ℂ_[p], j.comp ψL = κ' := by
    letI := ψL.toAlgebra
    letI := κ'.toAlgebra
    haveI : Algebra.IsAlgebraic F' L := Algebra.IsAlgebraic.tower_top (K := ℚ) F'
    let φ : L →ₐ[F'] ℂ_[p] := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩
  obtain ⟨V, _, _, _, _, _, hV⟩ := exists_dvr j
  obtain ⟨s₀, hft, hqc, -⟩ := ChartFType.main 𝔐.X Ω 𝔐.ξ _ _ 𝔐.all 𝔐.tie
  haveI : IsProper s₀ := LocModel.isProper_of_coordTie 𝔐.all 𝔐.tie s₀
  obtain ⟨z, ⟨hz, -⟩, -⟩ := existsUnique_valuationRing_lift ℤ V L (Int.castRingHom V) 𝔐.X s₀ zL
    (specZIsTerminal.hom_ext _ _)
  subst hz
  refine ⟨V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    j, ψL, z, hV, hj, hint, hψL, fun a ha => ?_⟩
  obtain ⟨u, s, hs, rfl⟩ := exists_frac κ' ha
  rw [map_mul, map_inv₀]
  refine mul_mem (int_reg hN ψ _ u) ?_
  obtain ⟨g, hg⟩ := int_reg hN ψ ⟨centre z, 𝔐.all _⟩ s
  have hv : ValAt 𝔐.ξ z (ψ (s : F')) ((Scheme.stalkClosedPointTo z).hom g) := ⟨𝔐.all _, g, hg, rfl⟩
  refine inv_reg _ hv ?_
  have h1 := val_unique 𝔐.tie.gen
    (ChangeRing.valAt_change _ _ _ V L (algebraMap V L) z _ _ hv (𝔐.all _)) (hψL s)
  have h2 : ‖j (ψL s)‖ = 1 := by
    have : j (ψL s) = κ' s := by rw [← hj]; rfl
    rw [this]
    exact norm_eq_one κ' hs
  have h0 : ψL s ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at h2
    exact zero_ne_one h2
  obtain ⟨w, hw⟩ := (hV (ψL s)⁻¹).1 (by rw [map_inv₀, norm_inv, h2, inv_one])
  refine IsUnit.of_mul_eq_one w (IsFractionRing.injective V L ?_)
  rw [map_mul, map_one, hw]
  exact (congrArg (· * _) h1).trans (mul_inv_cancel₀ h0)

end RootFieldNumerics.RF
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.HostRd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace RootFieldNumerics.RF

theorem chiEx : ChiEx := by
  intro E _ _ _ H _
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  have h4 : H.d % 4 = 3 := by
    have := H.d_mod
    omega
  refine ⟨(quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ), GlobalTheory.isKroneckerChar_quadraticChar h4, ?_⟩
  have hr : rootDiscr E = hostRd E := by
    simp [rootDiscr_def, hostRd, Int.cast_abs, one_div]
  have hpos : 0 < hostRd E := by
    unfold hostRd
    apply Real.rpow_pos_of_pos
    exact abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
  simp only [GlobalTheory.CM.logOm, hostLval]
  rw [Complex.sub_re, Complex.ofReal_re, hr, Real.log_div (by positivity) hpos.ne']
  ring

end RootFieldNumerics.RF
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.ValAtOfExtends
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CompanionTheory.Ar.LieTangent

namespace RootFieldNumerics.RF.IntFr

section Gen

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem exists_bc {R R' : Type} [CommRing R] [CommRing R'] {x : Spec (CommRingCat.of R) ⟶ X}
    {x' : Spec (CommRingCat.of R') ⟶ X} (φ : R →+* R') (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E)
    (M' : LieModel G x' E') : ∃ j : E →+ E', (∀ e, M'.pt (j e) = epsBase φ h ≫ M.pt e) ∧
      ∀ a e, j (a • e) = φ a • j e := by
  choose j hj using fun e => M'.onto _ (isTanAt_base φ h (M.tan e))
  refine ⟨AddMonoidHom.mk' j fun a b => M'.inj ?_, hj, fun a e => M'.inj ?_⟩
  · rw [M'.add, hj, hj, hj, M.add, MonObj.comp_mul]
  · show M'.pt (j (a • e)) = M'.pt (φ a • j e)
    rw [M'.pt_smul, hj, hj, M.pt_smul, ← Category.assoc, base_scale, Category.assoc]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

variable {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Em : Type} [AddCommGroup Em] [Module Ω Em]

theorem valAt_of_extends (M : LieModel G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q) {V L : Type} [CommRing V] [IsLocalRing V]
    [CommRing L] [IsLocalRing L] (φ : V →+* L) (z : Spec (CommRingCat.of V) ⟶ X) {e : Em}
    {v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G}
    (hv : M.Extends ⟨centre z, hall _⟩ e v) {w : epsAt (Spec.map (CommRingCat.ofHom φ) ≫ z) ⟶ G}
    (hw : w.left = Spec.map (CommRingCat.ofHom (dualMap
      (RingHom.comp (α := X.presheaf.stalk (centre z)) φ (Scheme.stalkClosedPointTo z).hom))) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom φ) ≫ z) e w := by
  have hs := centre_specializes φ z
  let s : X.presheaf.stalk (centre z) →+* X.presheaf.stalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    (X.presheaf.stalkSpecializes hs).hom
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  refine ⟨hall _, epsBase s h1 ≫ v, ⟨isTanAt_base s h1 hv.1, ?_⟩, ?_⟩
  · refine hv.2.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact RingHom.ext fun a => (genMap_specializes ⟨centre z, hall _⟩ (hall _) hs a).symm
  · refine hw.trans ?_
    change _ = _ ≫ Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap s)) ≫ v.left
    rw [← Category.assoc, dual_comp]
    congr 4
    exact (congrArg (fun t => t.hom) (stalk_base φ z)).symm

end Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_coords {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Em : Type} [AddCommGroup Em] [Module Ω Em] (M : LieModel t.G ξ Em) (hall : ∀ q : X, genPt ξ ⤳ q)
    (hξ : IsCptGen ξ) (V L : Type) [CommRing V] [IsLocalRing V] [Field L] [Algebra V L]
    (z : Spec (CommRingCat.of V) ⟶ X) :
    ∃ (g : ℕ) (MV : LieModel t.G z (Fin g → V)) (ρV : 𝓞 E →+* Module.End V (Fin g → V))
      (MC : LieModel t.G (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z) (Fin g → L))
      (ρC : 𝓞 E →+* Module.End L (Fin g → L)), MV.IsActOf t.act.act ρV ∧ MC.IsActOf t.act.act ρC ∧
      (∀ u, (MC.pt (algebraMap V L ∘ u)).left = spMap (dualMap (algebraMap V L)) ≫ (MV.pt u).left) ∧
      (∀ a u, ρC a (algebraMap V L ∘ u) = algebraMap V L ∘ ρV a u) ∧
      ∀ x, x ∈ M.fibAt M.lat z MC ↔ ∀ k, x k ∈ (algebraMap V L).range := by
  classical
  let R : Type := X.presheaf.stalk (centre z)
  let fV : R →+* V := (Scheme.stalkClosedPointTo z).hom
  obtain ⟨g, MR, ρR, -, hbc⟩ := GlobalTheory.T.lie_model_action_base_change E H X t R (X.fromSpecStalk (centre z))
  have hz : spMap fV ≫ X.fromSpecStalk (centre z) = z := spec_centre z
  obtain ⟨MV, ρV, aV, hV, -⟩ := hbc V fV z hz.symm
  obtain ⟨MC, ρC, aC, hC, -⟩ := hbc L ((algebraMap V L).comp fV) (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ z)
    ((congrArg (Spec.map (CommRingCat.ofHom (algebraMap V L)) ≫ ·) hz.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (spec_comp fV (algebraMap V L)))))
  obtain ⟨j, hj, hjs⟩ := exists_bc (algebraMap V L) rfl MV MC
  have sV : ∀ i : Fin g, (fV ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have sC : ∀ i : Fin g, (((algebraMap V L).comp fV) ∘ (Pi.single i 1 : Fin g → R)) = Pi.single i 1 := fun i => by
    ext k; by_cases h : k = i <;> simp [Pi.single_apply, h]
  have hj1 : ∀ i : Fin g, j (Pi.single i 1) = Pi.single i 1 := fun i => MC.inj (Over.OverMorphism.ext (by
    rw [hj, ← sC, hC, ← sV]
    refine (congrArg (Spec.map (CommRingCat.ofHom (dualMap (algebraMap V L))) ≫ ·) (hV (Pi.single i 1))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (MR.pt (Pi.single i 1)).left) (dual_comp _ _))))
  have hju : ∀ u, j u = algebraMap V L ∘ u := fun u => by
    have e : u = ∑ i, u i • (Pi.single i 1 : Fin g → V) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hjs, hj1]
    ext k; simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  have hpt : ∀ u, MC.pt (algebraMap V L ∘ u) = epsBase (algebraMap V L) rfl ≫ MV.pt u := fun u => by
    rw [← hju, hj]
  refine ⟨g, MV, ρV, MC, ρC, aV, aC, fun u => congrArg (fun q => q.left) (hpt u), fun a u => MC.inj ?_, fun x => ?_⟩
  · rw [aC a, hpt, hpt, aV a, Category.assoc]
  · let Λ : Submodule V (Fin g → L) :=
      { carrier := {x | ∀ k, x k ∈ (algebraMap V L).range}
        add_mem' := fun ha hb k => add_mem (ha k) (hb k)
        zero_mem' := fun k => zero_mem _
        smul_mem' := fun a x hx k => by
          show a • x k ∈ _
          rw [Algebra.smul_def]
          exact mul_mem ⟨a, rfl⟩ (hx k) }
    constructor
    · intro hx
      refine (Submodule.span_le (p := Λ)).2 ?_ hx
      rintro w ⟨h, e, he, hv⟩
      obtain ⟨v, hv₀⟩ := (M.mem_lat_iff _ e).1 he
      obtain ⟨r, rfl⟩ := MR.onto v hv₀.1
      have h3 := valAt_of_extends M hall (algebraMap V L) z hv₀ (hC r)
      have e2 := MC.inj (LieModel.ValAt.unique hξ hv h3)
      intro k
      rw [e2]
      exact ⟨_, rfl⟩
    · intro hx
      choose v hv using hx
      have hsum : x = ∑ i, v i • (Pi.single i 1 : Fin g → L) := by
        ext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hv]
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      obtain ⟨e, he⟩ := M.onto _ (isTanAt_base (genMap ξ ⟨centre z, hall _⟩) (spec_genMap ξ ⟨centre z, hall _⟩)
        (MR.tan (Pi.single i 1)))
      have hex : M.Extends ⟨centre z, hall _⟩ e (MR.pt (Pi.single i 1)) :=
        (M.extends_iff _ _ _).2 ⟨MR.tan _, he⟩
      refine Submodule.subset_span ⟨hall _, e, (M.mem_lat_iff _ e).2 ⟨_, hex⟩, ?_⟩
      rw [← sC]
      exact valAt_of_extends M hall (algebraMap V L) z hex (hC _)

theorem exists_sab {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.proved_CubePullSt f t
  exact ⟨_, ⟨m₁⟩⟩

theorem transport {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (h : f = f')
    (m : SABMap t' t f) : ∃ m' : SABMap t' t f', m'.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

theorem act_iff {R : Type} [CommRing R] {X : Scheme.{0}} {t : SAB H X} {t₀ : SAB H (Sp R)} {x : Sp R ⟶ X}
    (m : SABMap t₀ t x) {W : Type} [AddCommGroup W] [Module R W] (M₀ : LieModel t₀.G (𝟙 _) W) (M : LieModel t.G x W)
    (h : ∀ e, (M₀.pt e).left ≫ m.φ = (M.pt e).left) (ρ : 𝓞 E →+* Module.End R W) :
    M₀.IsActOf t₀.act.act ρ ↔ M.IsActOf t.act.act ρ := by
  have key : ∀ a e, (M₀.pt e ≫ t₀.act.act a).left ≫ m.φ = (M.pt e ≫ t.act.act a).left := fun a e => by
    rw [Over.comp_left, Over.comp_left, ← h, Category.assoc, Category.assoc, m.act]
  refine ⟨fun h₀ a e => Over.OverMorphism.ext ?_, fun h₁ a e => Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ?_)⟩
  · rw [← h, h₀ a e, key]
  · rw [key, h, h₁ a e]
  · rw [Over.w, Over.w]

end RootFieldNumerics.RF.IntFr

namespace RootFieldNumerics.RF

open IntFr

theorem intFrames : IntFrames := by
  intro E _ _ _ H D l Xo c _ Y S Ω _ K _ J _ y 𝔐 V L _ _ _ _ _ _ _ z y₀ hz
  obtain ⟨g, MV, ρV, MC, ρC, aV, aC, hVC, hρ, hfib⟩ := exists_coords 𝔐.t 𝔐.M 𝔐.all 𝔐.tie.gen V L z
  obtain ⟨T, ⟨mT⟩⟩ := IntFr.exists_sab z 𝔐.t
  obtain ⟨tK, ⟨m'⟩⟩ := IntFr.exists_sab (spMap (algebraMap V L)) T
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mT m'
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m n₁
  obtain ⟨n₃, hn₃⟩ := IntFr.transport hz n₂
  obtain ⟨m₃, hm₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₃
  obtain ⟨m, hm⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m₃
  obtain ⟨MK, hK⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) n₁.cart).1 MC
  obtain ⟨MU, hU⟩ := (LieMove.main L _ _ _ _ _ (Fin g → L) m.cart).2 MK
  obtain ⟨MT, hT⟩ := (LieMove.main V _ _ _ _ _ (Fin g → V) mT.cart).1 MV
  have aK := (act_iff n₁ MK MC hK ρC).2 aC
  have aT := (act_iff mT MT MV hT ρV).2 aV
  refine ⟨T, tK, m, m', g, MC, MU, ρC, aC, (act_iff m MK MU hU ρC).1 aK, fun e => ?_, hfib, ?_⟩
  · have w := Over.w (MK.pt e)
    refine ⟨Over.homMk ((MK.pt e).left ≫ n₃.φ) ?_, ⟨(MK.pt e).left ≫ m₃.φ, ?_, ?_, ?_⟩, ?_⟩
    · rw [Category.assoc, n₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, m₃.cart.1.w, ← Category.assoc, w]
      simp
    · rw [Category.assoc, ← hm]; exact hU e
    · rw [Category.assoc]
      exact congrArg ((MK.pt e).left ≫ ·) hm₃.symm
    · show _ = (MK.pt e).left ≫ n₃.φ
      rw [hn₃, hn₂, ← Category.assoc]
      exact congrArg (· ≫ 𝔐.m.φ) (hK e).symm
  · intro σ n x hx hspan
    have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
    have hmem : ∀ k, x k ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap V L).comp σ)).restrictScalars V :=
      fun k => hspan ▸ Submodule.subset_span ⟨k, rfl⟩
    choose xV hxV using fun k => (hfib _).1 (hmem k).1
    have hxe : ∀ k, x k = algebraMap V L ∘ xV k := fun k => funext fun i => (hxV k i).symm
    have cinj : ∀ u u' : Fin g → V, algebraMap V L ∘ u = algebraMap V L ∘ u' → u = u' :=
      fun u u' h => funext fun i => hinj (congrFun h i)
    have heig : ∀ u : Fin g → V, u ∈ eigSp ρV σ ↔ algebraMap V L ∘ u ∈ eigSp ρC ((algebraMap V L).comp σ) := fun u => by
      simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, hρ]
      refine forall_congr' fun a => ⟨fun h => ?_, fun h => cinj _ _ ?_⟩
      · rw [h]; ext i; simp
      · rw [h]; ext i; simp
    have hsum : ∀ cf : Fin n → V, algebraMap V L ∘ (∑ k, cf k • xV k) = ∑ k, cf k • x k := fun cf => by
      ext i; simp [Finset.sum_apply, hxe, Algebra.smul_def]
    refine ⟨σ, fun k => MT.pt (xV k), rfl, ?_, fun k => ⟨(MK.pt (x k)).left, hU _, ?_⟩⟩
    · refine (GlobalTheory.T.eigen_frame_iff_eigenspace_basis _ V T.G (𝟙 _) _ MT _ T.act ρV σ n xV aT).2 ⟨fun k => (heig _).2 (hxe k ▸ (hmem k).2), ?_⟩
      intro e he
      have h1 : algebraMap V L ∘ e ∈ Submodule.span V (Set.range x) := by
        rw [hspan]
        exact ⟨(hfib _).2 fun i => ⟨_, rfl⟩, (heig e).1 he⟩
      obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
      refine ⟨cf, cinj _ _ (by rw [hsum, hcf]), fun cf' h => ?_⟩
      have h2 : ∑ k, (algebraMap V L (cf' k) - algebraMap V L (cf k)) • x k = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
        rw [← hsum, ← h, hcf, sub_self]
      exact funext fun k => hinj (sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hx _ h2 k))
    · refine mT.cart.1.hom_ext ?_ ?_
      · rw [Category.assoc, ← hn₁, Category.assoc]
        refine (hK _).trans ?_
        rw [hxe, hVC]
        exact congrArg (_ ≫ ·) (hT _).symm
      · rw [Category.assoc, m'.cart.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
        simpa using (spec_dual_alg (algebraMap V L)).symm

end RootFieldNumerics.RF
end
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem rootFlatOnHodge (hFD : Fl.FlatDegree) (hG : Given) : Flat.RootFlatOnHodge :=
  RF.rootFlatOnHodge_of RF.cptEx RF.periodOf RF.smoothLine
    (RF.localCmp_of RF.pointEx RF.valuePhi RF.intFrames RF.fibSandwich) RF.chiEx RF.numerics hFD hG

theorem global_model_tower_final_condition : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  intro hFD hG E _ _ _ _ H D Xo l c Y _ T o II hY _ _ _ _ a τ
  exact Flat.OnHodge.tower (rootFlatOnHodge hFD hG) hY ⟨o.toTowerOrigin, o.omVB⟩ a τ

end RootFieldNumerics
