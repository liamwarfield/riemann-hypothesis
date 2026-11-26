module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightedProjectiveChartsSplitGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperIffOfSplit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.AbelianLocus

theorem isProper_of_eq {S G G₁ G₂ : Scheme.{0}} (f : G ⟶ S) [IsSeparated f] [LocallyOfFiniteType f]
    {K₁ K₂ : Type} [Field K₁] [Field K₂] {t₁ : Sp K₁ ⟶ S} {t₂ : Sp K₂ ⟶ S}
    {φ₁ : G₁ ⟶ G} {f₁ : G₁ ⟶ Sp K₁} {φ₂ : G₂ ⟶ G} {f₂ : G₂ ⟶ Sp K₂}
    (h₁ : IsPullback φ₁ f₁ f t₁) (h₂ : IsPullback φ₂ f₂ f t₂) (p₁ : Sp K₁) (p₂ : Sp K₂) (hp : t₁ p₁ = t₂ p₂)
    [IsProper f₁] : IsProper f₂ := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t₁) (g := t₂) p₁ p₂ hp
  let j := (pullback t₁ t₂).fromSpecResidueField z
  let u := j ≫ pullback.fst t₁ t₂
  let u' := j ≫ pullback.snd t₁ t₂
  have e : u ≫ t₁ = u' ≫ t₂ := by simp only [u, u', Category.assoc, pullback.condition]
  have P₁ := (IsPullback.of_hasPullback f₁ u).paste_horiz h₁
  have P₂ := (IsPullback.of_hasPullback f₂ u').paste_horiz h₂
  rw [← e] at P₂
  have h₃ : UniversallyClosed (pullback.snd f₂ u') := by
    rw [← (P₂.isoIsPullback _ _ P₁).hom_inv_id_assoc (pullback.snd f₂ u'), P₂.isoIsPullback_inv_snd]
    infer_instance
  have : Subsingleton (Sp K₂) := inferInstanceAs (Subsingleton (PrimeSpectrum K₂))
  have hu' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u' :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed f₂ :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu' h₃
  have : IsSeparated f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  have : LocallyOfFiniteType f₂ := MorphismProperty.of_isPullback h₂ inferInstance
  exact ⟨⟩

theorem mem_abLocus_iff {S G₁ : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] {t : Sp K ⟶ S} {φ : G₁ ⟶ G.left} {f : G₁ ⟶ Sp K} (h : IsPullback φ f G.hom t)
    (p : Sp K) : t p ∈ abLocus G ↔ IsProper f := by
  constructor
  · intro hp
    let K' := AlgebraicClosure K
    let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have q : Sp K' := (default : PrimeSpectrum K')
    have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
    have := hp K' (u ≫ t) ⟨q, e⟩
    exact isProper_of_eq G.hom (IsPullback.of_hasPullback G.hom (u ≫ t)) h q p e
  · rintro hf K' _ _ t' ⟨q, hq⟩
    exact isProper_of_eq G.hom h (IsPullback.of_hasPullback G.hom t') p q hq.symm

theorem isProper_iff_of_split (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom]
    [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (hs : C.Split c) :
    IsProper H.hom ↔ d = 0 := by
  obtain ⟨hc, i, hi⟩ := hs
  obtain ⟨B, _, q, hB, hq, hf, hsu, ha, hp, -⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hi
  have := hi.hom
  constructor
  · intro hH
    have : Mono (η[B]) := ⟨fun a b _ => toUnit_unique _ _⟩
    have : Mono i := MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hp.flip this
    have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mono K (Fin d → ℤ) H i hi.hom
    rcases d with _ | d
    · rfl
    · exact absurd (congrFun (Subsingleton.elim (0 : Fin (d + 1) → ℤ) 1) 0) zero_ne_one
  · rintro rfl
    have : Mono q := ⟨fun {Y} x y hxy => by
      have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
        rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
        rfl
      have h2 : hp.lift _ _ h1 = 1 := by
        apply (splitTorusPointsEquiv (Sp K) (Fin 0 → ℤ) Y).injective
        refine MonoidHom.ext fun a => ?_
        rw [Subsingleton.elim a 1, map_one, map_one]
      have h3 := hp.lift_fst _ _ h1
      rw [h2, MonObj.one_comp] at h3
      exact mul_inv_eq_one.1 h3.symm⟩
    have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
    have := hB.proper
    have := hB.smooth
    have : LocallyOfFinitePresentation (q.left ≫ B.hom) := by rw [Over.w q]; infer_instance
    have : LocallyOfFiniteType (q.left ≫ B.hom) := inferInstance
    have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp _ B.hom
    have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
    have : LocallyOfFinitePresentation q.left := inferInstance
    have : IsOpenImmersion q.left := IsOpenImmersion.of_flat_of_mono _
    have : IsIso q.left := isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext q.left.surjective.range_eq)
    rw [← Over.w q]
    infer_instance

theorem isProper_snd {P Z : Scheme.{0}} (f : P ⟶ Z) [IsProper f] (G : P.Opens) (U : Z.Opens) (h : f ⁻¹ᵁ U ≤ G) :
    IsProper (pullback.snd (G.ι ≫ f) U.ι) := by
  have h₁ := IsPullback.of_hasPullback f U.ι
  have h₂ := IsPullback.of_hasPullback G.ι (pullback.fst f U.ι)
  have h₃ := h₂.paste_vert h₁
  have : IsIso (pullback.snd G.ι (pullback.fst f U.ι)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
    rw [Scheme.Hom.coe_opensRange, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    refine Set.eq_univ_of_forall fun x => h ?_
    have : pullback.fst f U.ι x ∈ Set.range (pullback.fst f U.ι) := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at this
  rw [← h₃.isoPullback_inv_snd]
  infer_instance

theorem abLocus_eq : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → ∀ Zab : C.Z.Opens, (∀ w : C.P.left, IsClosed ({w} : Set C.P.left) → C.P.hom w ∈ Zab → w ∈ C.G) → (∀ z : C.Z, IsClosed ({z} : Set C.Z) → z ∉ Zab → z ∉ abLocus C.GG) → abLocus C.GG = Zab ∧ IsProper (pullback.snd C.GG.hom Zab.ι) := by
  intro C L hT hC Zab h₁ h₂
  let := L.grp
  have := L.comm
  obtain ⟨hsep, hlft, hqc, -⟩ := GlobalTheory.ZJ.core_basic C
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have := C.proper
  have := C.lft
  have hle : C.P.hom ⁻¹ᵁ Zab ≤ C.G := by
    have := (GlobalTheory.jacobson_closedPoints_tools_int C.P.left (C.P.hom ≫ C.π)).2.2.1 (C.P.hom ⁻¹ᵁ Zab)
      (C.P.hom ⁻¹ᵁ Zab ⊓ C.G) fun w hw => ⟨fun h => ⟨h, h₁ w hw h⟩, fun h => h.1⟩
    exact inf_eq_left.1 this.symm
  have hpr : IsProper (pullback.snd C.GG.hom Zab.ι) := isProper_snd C.P.hom C.G Zab hle
  refine ⟨Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_), hpr⟩
  · by_contra hzn
    obtain ⟨R, _, _, _, t, _, ht, Ch, d, c, Sg, hd, hs, hcl⟩ := GlobalTheory.T.exists_dense_closedPoints_chartSplitting C L hT hC z
    have : Smooth ((Over.pullback t).obj C.GG).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : IsSeparated ((Over.pullback t).obj C.GG).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
    have : QuasiCompact ((Over.pullback t).obj C.GG).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have key : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R)
        [IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom s)],
        Charts.Split (H := (Over.pullback s).obj ((Over.pullback t).obj C.GG))
          (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c → ∀ p, (t (s p) ∈ abLocus C.GG ↔ d = 0) := by
      intro K _ s _ hsp p
      have : Smooth ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (Smooth (pullback.snd _ _))
      have : IsSeparated ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (IsSeparated (pullback.snd _ _))
      have : QuasiCompact ((Over.pullback s).obj ((Over.pullback t).obj C.GG)).hom :=
        inferInstanceAs (QuasiCompact (pullback.snd _ _))
      rw [← isProper_iff_of_split K ((Over.pullback s).obj ((Over.pullback t).obj C.GG))
        (Ch.pull (pullback.fst ((Over.pullback t).obj C.GG).hom s)) c hsp]
      exact mem_abLocus_iff C.GG ((IsPullback.of_hasPullback (pullback.snd C.GG.hom t) s).paste_horiz
        (IsPullback.of_hasPullback C.GG.hom t)) p
    have : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom (Out.jK R)) :=
      isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
    have hgen := GlobalTheory.T.weightedProjectiveCharts_split_generic_point R ((Over.pullback t).obj C.GG) Ch d c Sg hd hs
    have p₀ : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
    have hp₀ : Out.jK R p₀ = (⊥ : PrimeSpectrum R) := by
      have : p₀ = (⊥ : PrimeSpectrum (FractionRing R)) := Subsingleton.elim (α := PrimeSpectrum _) _ _
      subst this
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
    have hd0 : d = 0 := (key _ _ hgen p₀).1 (by rw [hp₀, ht]; exact hz)
    have : Nonempty (Sp R) := ⟨(⊥ : PrimeSpectrum R)⟩
    obtain ⟨x, hx⟩ := hd.nonempty
    obtain ⟨K, _, s, _, hr, hsp⟩ := hs x hx
    obtain ⟨p, rfl⟩ : x ∈ Set.range s := hr ▸ rfl
    refine h₂ _ (hcl _ hx) (fun hm => hzn ?_) ((key K s hsp p).2 hd0)
    have hsz : (⊥ : PrimeSpectrum R) ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have := (hsz.map t.continuous).mem_open Zab.2 hm
    rwa [← ht]
  · rintro K _ _ t ⟨p, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have hr : Set.range t ⊆ Set.range Zab.ι := by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim q p]
      exact hz
    have P := (IsPullback.of_hasPullback (pullback.snd C.GG.hom Zab.ι) (IsOpenImmersion.lift Zab.ι t hr)).paste_horiz
      (IsPullback.of_hasPullback C.GG.hom Zab.ι)
    rw [IsOpenImmersion.lift_fac] at P
    rw [← P.isoPullback_inv_snd]
    infer_instance

end GlobalTheory.ZJ.AbelianLocus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusIsAffineHomAndSplitsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialise
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsoFinite

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)}

theorem comm_bcMap (R : Subalgebra k C)
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    (h : bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A'.hom R.val = bcMap A.hom R.val ≫ g.left := by
  have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (bcMap_fst A'.hom R.val)).trans
      (h.symm.trans (Category.assoc _ _ _).symm))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
    have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hg
    have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hf
    exact a₁.trans ((Category.assoc _ _ _).symm.trans
      (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))

variable [GrpObj A] [GrpObj A']

theorem exists_fg_iso [QuasiCompact A.hom] [IsSeparated A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [QuasiCompact A'.hom] [IsSeparated A'.hom] [Flat A'.hom] [LocallyOfFinitePresentation A'.hom]
    (e : (Over.pullback (spMap (algebraMap k C))).obj A ≅ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom e.hom] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g.hom := by
  obtain ⟨R₁, f₁, hR₁, _, h₁⟩ := exists_fg_isMonHom e.hom
  obtain ⟨R₂, f₂, hR₂, _, h₂⟩ := exists_fg_isMonHom e.inv
  let R : Subalgebra k C := R₁ ⊔ R₂
  obtain ⟨g₁, m₁, k₁⟩ := exists_specialise f₁ (Subalgebra.inclusion (le_sup_left : R₁ ≤ R))
  obtain ⟨g₂, m₂, k₂⟩ := exists_specialise f₂ (Subalgebra.inclusion (le_sup_right : R₂ ≤ R))
  have c₁ := comm_bcMap R e.hom g₁ ((congrArg (_ ≫ ·) k₁).trans
    ((bcMap_comp_of_eq_assoc A.hom _ _ R₁.val (fun _ => rfl) _).trans h₁))
  have c₂ := comm_bcMap R e.inv g₂ ((congrArg (_ ≫ ·) k₂).trans
    ((bcMap_comp_of_eq_assoc A'.hom _ _ R₂.val (fun _ => rfl) _).trans h₂))
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
    Subtype.val_injective
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsIso g₁ := ExtUnique.isIso_of_isPullback (isGrpPullback_bcMap A R.val).1
    (isGrpPullback_bcMap A' R.val).1 e g₁ g₂ c₁ c₂
  exact ⟨R, asIso g₁, hR₁.sup hR₂, m₁⟩

theorem exists_iso_specialise {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom g.hom] (ρ : R →ₐ[k] S) :
    ∃ e : (Over.pullback (spMap (algebraMap k S))).obj A ≅ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_bcMap A ρ) (isGrpPullback_pullback _ _)
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback _ _) (isGrpPullback_bcMap A' ρ)
  exact ⟨a ≪≫ (Over.pullback (spMap ρ.toRingHom)).mapIso g ≪≫ b,
    inferInstanceAs (IsMonHom (a.hom ≫ (Over.pullback (spMap ρ.toRingHom)).map g.hom ≫ b.hom))⟩

theorem exists_finite_iso : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (T T' : Over (Spec (CommRingCat.of k))) [GrpObj T] [GrpObj T'], IsAffineHom T.hom → IsAffineHom T'.hom → LocallyOfFiniteType T.hom → LocallyOfFiniteType T'.hom → (∃ e : fieldBaseChange k Ω T ≅ fieldBaseChange k Ω T', IsMonHom e.hom) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k') (e : fieldBaseChange k k' T ≅ fieldBaseChange k k' T'), IsMonHom e.hom := by
  intro k Ω _ _ _ T T' _ _ _ _ _ _ ⟨e, he⟩
  have : LocallyOfFinitePresentation T.hom := inferInstance
  have : LocallyOfFinitePresentation T'.hom := inferInstance
  obtain ⟨R, g, hR, hg⟩ := exists_fg_iso (k := k) (C := Ω) (A := T) (A' := T') e
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := .of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨e', he'⟩ := exists_iso_specialise g (Ideal.Quotient.mkₐ k m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, this, e', he'⟩

end GlobalTheory.IsoFinite
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem torus_isAffineHom_and_splits_finite : NaSt.{0} := by
  intro k _ T _ hT
  obtain ⟨Ω, _, _, X, _, _, _, e, he⟩ := hT.splits
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ⟨fun x => ⟨(default : Spec (.of Ω)), Subsingleton.elim (α := Spec (.of k)) _ _⟩⟩
  have haff : IsAffineHom T.hom := by
    refine isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ T.hom _ hsurj hflat inferInstance ?_
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h : IsAffineHom (e.hom.left ≫ (splitTorus (Spec (.of Ω)) X).hom) := inferInstance
    rw [Over.w] at h
    exact h
  refine ⟨haff, ?_⟩
  obtain ⟨k', _, _, _, e', he'⟩ := IsoFinite.exists_finite_iso k Ω T (splitTorus (Spec (.of k)) X)
    haff inferInstance hT.finiteType inferInstance
    ⟨e ≪≫ (Diag.baseChangeIso _ X).symm,
      inferInstanceAs (IsMonHom (e.hom ≫ (Diag.baseChangeIso _ X).inv))⟩
  exact ⟨k', inferInstance, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
    e' ≪≫ Diag.baseChangeIso _ X, inferInstanceAs (IsMonHom (e'.hom ≫ (Diag.baseChangeIso _ X).hom))⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SS

theorem exists_finite_torusExtension_of_torusExt : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  intro k _ G _ ⟨T⟩
  have := T.q_hom
  have := T.i_hom
  obtain ⟨-, k', _, _, hfin, X, _, hfree, hX, e, he⟩ := GlobalTheory.torus_isAffineHom_and_splits_finite k T.T₀ T.isTorus
  refine ⟨k', inferInstance, inferInstance, hfin, ?_⟩
  let f : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hq := isPullback_overPullback_map_left f T.q
  have : IsMonHom e.inv := inferInstance
  refine ⟨{ X := X
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.inv ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  first | exact @GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | exact GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | (intros; apply GlobalTheory.SS.exists_finite_torusExtension_of_torusExt <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
noncomputable section

namespace GlobalTheory.SS.InvFrame

theorem exists_det_ne_zero {F S : Type} [Field F] {n : ℕ} (D : Fin n → S → F) (h : LinearIndependent F D) :
    ∃ t : Fin n → S, (Matrix.of fun i j => D i (t j)).det ≠ 0 := by
  have hs := span_flip_eq_top_iff_linearIndependent.2 h
  obtain ⟨f, hf, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range (flip D))
  have e : Module.finrank F (Submodule.span F (Set.range (flip D))) = n := by
    rw [hs, finrank_top, Module.finrank_fin_fun]
  choose t ht using hf
  refine ⟨fun j => t (j.cast e.symm), ?_⟩
  have h2 := hli.comp (Fin.cast e.symm) (Fin.cast_injective _)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)).ne_zero
  have e2 : (Matrix.of fun i j : Fin n => D i (t (j.cast e.symm))).col = f ∘ Fin.cast e.symm :=
    funext fun j => ht _
  rw [e2]
  exact h2

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis constFn)
open TrivSqZeroExt (inl inr)
open GlobalTheory.SqZero GlobalTheory.KS GlobalTheory.KS.InvField

theorem value_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {T : CommRingCat.{0}}
    (φ : Γ(X, U) ⟶ T) (f : Γ(X, U)) :
    (Scheme.ΓSpecIso T).hom.hom (pbT (Spec.map φ ≫ hU.fromSpec) f ⊤) = φ.hom f := by
  have ht : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have ht' : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := fun q _ => ht (x := Spec.map φ q) trivial
  rw [pbT_of_le _ ht']
  have h1 : hU.fromSpec.appLE U ⊤ ht = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h2 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ ht' ≫ (Scheme.ΓSpecIso T).hom = φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) _ U ⊤ ⊤ ht le_top, h1, Category.assoc, Iso.inv_comp_eq,
      ← Scheme.ΓSpecIso_naturality]
    congr 1
  exact congrArg (fun q => q.hom f) h2

theorem value_constFn_id {T : Type} [CommRing T] (a : T) :
    (Scheme.ΓSpecIso (.of T)).hom.hom (constFn (𝟙 (Sp T)) ⊤ a) = a := by
  have h : (𝟙 (Sp T) : Sp T ⟶ Sp T).appLE ⊤ ⊤ (fun _ _ => trivial) = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 (Sp T)) (U := ⊤)).trans rfl
  rw [constFn, h]
  exact congrArg (fun q => q.hom a) (Scheme.ΓSpecIso (.of T)).inv_hom_id

variable {K : Type} [Field K] {G : Over (Spec (CommRingCat.of K))} [GrpObj G] [IsCommMonObj G]

theorem exists_independent [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    {S F : Type} [CommRing S] [Algebra K S] [Field F] [Algebra K F] (j : sp (R₀ := K) S ⟶ G)
    [IsOpenImmersion j.left] (u : S →ₐ[K] F) :
    ∃ D : Fin n → S → F, LinearIndependent F D ∧ ∀ k, ∃ φ : S →ₐ[K] DualNumber F,
      spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v k) *
        (spMap ((inlS K F).comp u) ≫ j) ∧ ∀ a, (φ a).snd = D k a := by
  obtain ⟨χ, hχ, hfst⟩ := exists_chart_pt_of_nil j (TrivSqZeroExt.fstHom K F (Fin n → F))
    (fun a => ⟨inl a, rfl⟩) (fun a ha => ⟨2, by
      rw [pow_two]; exact mul_eq_zero_of_sq (ker_fst_sq (R := K) (S := F) (Fin n → F)) ha ha⟩)
    (lieExp v (fun i => inr (Pi.single i 1)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) *
      (spMap ((TrivSqZeroExt.inlAlgHom K F (Fin n → F)).comp u) ≫ j)) u (by
      rw [MonObj.comp_mul, comp_lieExp, lieExp_eq_one hv.1 _ (fun i => by rfl), one_mul, ← Category.assoc,
        spMap_comp]
      rfl)
  have hfst : ∀ a, (χ a).fst = u a := AlgHom.congr_fun hfst
  let φ : (Fin n → F) → (S →ₐ[K] DualNumber F) := fun c => (vecTo (inlS K F) (fun i => inr (c i))
      (fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)).comp χ
  have hφ : ∀ c, spMap (φ c) ≫ j = tanExp v c * (spMap ((inlS K F).comp u) ≫ j) := fun c => by
    rw [← spMap_comp, Category.assoc, ← hχ, MonObj.comp_mul, comp_lieExp, ← Category.assoc, spMap_comp]
    congr 1
    · exact lieExp_congr _ (fun i => vecTo_single _ _ _ i) _ _
    · congr 2
      exact AlgHom.ext fun a => by simp [vecTo_apply]
  have hφ1 : ∀ c a, (φ c a).fst = u a := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.fst_sum, hfst]
  have hφ2 : ∀ c a, (φ c a).snd = ∑ k, c k * (χ a).snd k := fun c a => by
    simp [φ, vecTo_apply, TrivSqZeroExt.snd_sum, mul_comm]
  refine ⟨fun k a => (χ a).snd k, Fintype.linearIndependent_iff.2 fun c hc k => ?_,
    fun k => ⟨φ (Pi.single k 1), ?_, fun a => ?_⟩⟩
  · have : φ c = φ 0 := AlgHom.ext fun a => TrivSqZeroExt.ext (by rw [hφ1, hφ1]) (by
      rw [hφ2, hφ2]
      simpa using congrFun hc a)
    have h3 := mul_right_cancel ((hφ c).symm.trans (this ▸ hφ 0))
    have h4 := (expBij (DualNumber F) hv _ (ker_fst_sq (R := K) (S := F) F)).1 _ _ (fun _ => rfl) (fun _ => rfl) _ _ h3
    exact TrivSqZeroExt.inr_injective (congrFun h4 k)
  · rw [hφ]
    congr 1
    refine (Finset.prod_eq_single k (fun i _ hi => epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
      (by simp [Pi.single_eq_of_ne hi]) _) (by simp)).trans ?_
    congr 3
    simp
  · rw [hφ2]
    simp [Pi.single_apply]


omit [IsCommMonObj G] in
theorem value_invDer {v : epsR K ⟶ G} {dd : ∀ W : G.left.Opens, Γ(G.left, W) → Γ(G.left, W)} (hd : IsInvDer v dd)
    {U : G.left.Opens} (hU : IsAffineOpen U) [Algebra K Γ(G.left, U)] (j : sp (R₀ := K) Γ(G.left, U) ⟶ G)
    (hj : j.left = hU.fromSpec) {F : Type} [Field F] [Algebra K F] (u : Γ(G.left, U) →ₐ[K] F)
    (φ : Γ(G.left, U) →ₐ[K] DualNumber F)
    (hφ : spMap φ ≫ j = (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ v) *
        (spMap ((inlS K F).comp u) ≫ j)) (f : Γ(G.left, U)) : (φ f).snd = u (dd U f) := by
  let w : sp (R₀ := K) (DualNumber F) ⟶ epsR K ⊗ G :=
    lift (spMap (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))) (spMap ((inlS K F).comp u) ≫ j)
  have e1 : w.left ≫ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← hφ, Over.comp_left, hj]
    rfl
  have e2 : w.left ≫ (snd (epsR K) G).left =
      Spec.map (CommRingCat.ofHom ((inlS K F).comp u).toRingHom) ≫ hU.fromSpec := by
    rw [← Over.comp_left, lift_snd, Over.comp_left, hj]
    rfl
  have e3 : w.left ≫ (fst (epsR K) G).left = 𝟙 _ ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
      (epsTo K (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _)).toRingHom := by
    rw [← Over.comp_left, lift_fst, Category.id_comp]
    rfl
  have hw : ⊤ ≤ w.left ⁻¹ᵁ ((snd (epsR K) G).left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, e2]
    exact fun q _ => hU.fromSpec_preimage_self.ge (x := Spec.map _ q) trivial
  have key : ∀ f : Γ(G.left, U), ((Scheme.ΓSpecIso (.of (DualNumber F))).hom.hom (pbT w.left
      (pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left f ((snd (epsR K) G).left ⁻¹ᵁ U)) ⊤) : DualNumber F) =
      inl (u f) + inr 1 * inl (u (dd U f)) := fun f => by
    rw [hd U f, pbT_add, pbT_mul, pbT_pbT _ _ le_rfl hw, pbT_pbT _ _ le_rfl hw, pbT_constFn _ _ hw, e2, e3,
      constFn_spMap, map_add, map_mul]
    refine congrArg₂ _ (value_fromSpec hU _ _) (congrArg₂ _ ?_ (value_fromSpec hU _ _))
    refine Eq.trans ?_ (epsTo_eps (R := K) (inr 1 : DualNumber F) (TrivSqZeroExt.inr_mul_inr _ _ _))
    exact value_constFn_id _
  by_cases h : (snd (epsR K) G).left ⁻¹ᵁ U ≤ ((fst (epsR K) G ≫ v) * snd (epsR K) G).left ⁻¹ᵁ U
  · have := key f
    rw [pbT_pbT _ _ h hw, e1] at this
    have h5 := congrArg TrivSqZeroExt.snd ((value_fromSpec hU _ f).symm.trans this)
    simpa using h5
  · have := key 1
    rw [show pbT ((fst (epsR K) G ≫ v) * snd (epsR K) G).left (1 : Γ(G.left, U))
      ((snd (epsR K) G).left ⁻¹ᵁ U) = 0 from dif_neg h, pbT_zero, map_zero] at this
    simpa using congrArg TrivSqZeroExt.fst this

theorem exists_mem_basicOpen [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR K ⟶ G)} (hv : IsLieBasis v)
    (D : Fin n → VF G) (hd : ∀ i, IsInvDer (v i) fun W f => (D i).D W f) (x : G.left) :
    ∃ (U : G.left.Opens) (t : Fin n → Γ(G.left, U)), x ∈ G.left.basicOpen (jac D U t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  letI : Algebra K Γ(G.left, U) := (Spec.preimage (hU.fromSpec ≫ G.hom)).hom.toAlgebra
  let j : sp (R₀ := K) Γ(G.left, U) ⟶ G := Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hx
  have := PrimeSpectrum.isPrime p
  let u : Γ(G.left, U) →ₐ[K] (PrimeSpectrum.asIdeal p).ResidueField := IsScalarTower.toAlgHom _ _ _
  obtain ⟨δ, hδ, hφ⟩ := exists_independent hv j u
  obtain ⟨t, ht⟩ := exists_det_ne_zero δ hδ
  refine ⟨U, t, ?_⟩
  have h1 : u (jac D U t) ≠ 0 := by
    rw [jac, AlgHom.map_det]
    refine (congrArg Matrix.det (Matrix.ext fun i k => ?_)).trans_ne ht
    obtain ⟨φ, h2, h3⟩ := hφ i
    exact (value_invDer (hd i) hU j rfl u φ h2 (t k)).symm.trans (h3 _)
  have h2 : p ∈ hU.fromSpec ⁻¹ᵁ G.left.basicOpen (jac D U t) := by
    rw [hU.fromSpec_preimage_basicOpen]
    exact fun h => h1 (Ideal.algebraMap_residueField_eq_zero.2 h)
  exact h2

end GlobalTheory.SS.InvFrame

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem GlobalTheory.SS.exists_isFrame : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  intro K _ A _ _ g hg
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  choose dd hdd using fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).1
  have hp := fun i => (GlobalTheory.KS.InvField.main K A (v i) (hv.1 i)).2 _ (hdd i)
  let D : Fin g → VF A := fun i =>
    { D := fun U => AddMonoidHom.mk' (dd i U) ((hp i).1 U)
      leibniz := (hp i).2.1
      const := (hp i).2.2.2.1
      res := fun U V h a => by
        have := (hp i).2.2.1 U V a h
        rw [GlobalTheory.KS.rsT_of_le h, GlobalTheory.KS.rsT_of_le h] at this
        exact this }
  refine ⟨D, by rwa [Fintype.card_fin], fun x => ?_⟩
  obtain ⟨U, t, hx⟩ := InvFrame.exists_mem_basicOpen hv D hdd x
  have hle := A.left.basicOpen_le (jac D U t)
  refine ⟨_, fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i), hx, ?_⟩
  have e : jac D _ (fun i => (A.left.presheaf.map (homOfLE hle).op).hom (t i)) =
      (A.left.presheaf.map (homOfLE hle).op).hom (jac D U t) := by
    exact (congrArg Matrix.det (Matrix.ext fun i k => (D i).res U _ hle (t k))).trans
      (RingHom.map_det (A.left.presheaf.map (homOfLE hle).op).hom (Matrix.of fun i k => (D i).D U (t k))).symm
  rw [e]
  exact A.left.toRingedSpace.isUnit_res_basicOpen (jac D U t)

end

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vectorFieldFrame_smooth_commGrpScheme : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∃ D : Fin g → VF A, IsFrame D := by
  first | exact @GlobalTheory.SS.exists_isFrame | exact GlobalTheory.SS.exists_isFrame | (intros; apply GlobalTheory.SS.exists_isFrame <;> assumption)
end
end
