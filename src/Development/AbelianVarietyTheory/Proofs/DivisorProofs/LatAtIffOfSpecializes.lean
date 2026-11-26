module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat.ClosedLift

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem endo_of_closed {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {V : Type} [CommRing V]
    [IsDomain V] {ξ : Sp V ⟶ S} {G₁ : Over (Sp V)} [GrpObj G₁] {φ₁ : G₁.left ⟶ G.left}
    (h : IsGrpPullback G₁ G ξ φ₁) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (j : splitTorus (Sp V) X ⟶ G₁) [IsMonHom j] {GK : Over (Sp (FractionRing V))} [GrpObj GK]
    {ψ : GK.left ⟶ G₁.left} (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ)
    (hK : IsTorPart (pullTorus hψ j)) {κ : Type} [Field κ] {b : V →+* κ} {G₀ : Over (Sp κ)} [GrpObj G₀]
    {ψ₀ : G₀.left ⟶ G₁.left} (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (h0 : IsTorPart (pullTorus hψ₀ j))
    (u : G ⟶ G) [IsMonHom u] (r : X →+ X)
    (hr : (pullTorus hψ₀ j).left ≫ (ψ₀ ≫ φ₁) ≫ u.left = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁) :
    j.left ≫ φ₁ ≫ u.left = (torusMap _ r ≫ j).left ≫ φ₁ := by
  obtain ⟨u₁, hu₁, pa⟩ := GlobalTheory.SymBaseChange.exists_endo h u
  have hw : u₁.left ≫ φ₁ = φ₁ ≫ u.left := by
    have := congrArg CommaMorphism.left (pa (𝟙 G₁))
    simpa [pushPt] using this
  haveI := hu₁
  obtain ⟨s, hs⟩ := hK.factor (pullTorus hψ (j ≫ u₁)) inferInstance
  rw [← pullTorus_torusMap_comp] at hs
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V (FractionRing V))) ∧
      IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSeparated G₁.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have key : j ≫ u₁ = torusMap _ s ≫ j :=
    GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap (algebraMap V (FractionRing V))) X)
      (by rw [← pullTorus_left hψ, ← pullTorus_left hψ, hs])
  have k0 : torusMap _ s ≫ pullTorus hψ₀ j = torusMap _ r ≫ pullTorus hψ₀ j := by
    apply hom_ext_of_pullback (hψ₀.comp h)
    have e1 := pullTorus_left hψ₀ (j ≫ u₁)
    have e2 := pullTorus_left hψ₀ j
    calc (torusMap _ s ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁
        = ((pullTorus hψ₀ (j ≫ u₁)).left ≫ ψ₀) ≫ φ₁ := by
          rw [← pullTorus_torusMap_comp, ← key, Category.assoc]
      _ = bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ u.left := by
          rw [e1]; simp [Category.assoc, hw]
      _ = ((pullTorus hψ₀ j).left ≫ ψ₀) ≫ φ₁ ≫ u.left := by
          rw [e2]; simp only [Category.assoc]
      _ = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := by
          rw [← hr]; simp only [Category.assoc]
  have hsr : s = r := h0.cancel k0
  subst hsr
  rw [← key, Over.comp_left, Category.assoc, hw]

theorem compat_of_closed : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hLu hf hgγ X _ _ _ m c V _ _ _ ξ a G₁ _ φ₁ h j hj hext GK _ ψ hψ hK
    κ _ b hb G₀ _ ψ₀ hψ₀ h0 hC
  haveI := hG.separated
  haveI := hj
  haveI : NeZero L := ⟨hL.ne'⟩
  refine ⟨fun e => ?_, fun t => ?_⟩
  · haveI := hf e
    exact endo_of_closed h j hψ hK hψ₀ h0 (f e) (m e) (hC.1 e)
  obtain ⟨z₀, hz₀, hv₀⟩ := hC.2 t
  have hζV : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  have hpow : ∀ k : ℕ, ((Units.map a.toMonoidHom ζ) ^ k) ^ L = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζV, one_pow]
  let F : Multiplicative X →* Γ(Sp V, ⊤)ˣ :=
    { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
      map_one' := by simp [unitOn]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add (f := _), ZMod.val_add, ← pow_eq_pow_mod _ hζV, pow_add]
        simp [unitOn] }
  let Z1 : Over (Sp V) := Over.mk (𝟙 (Sp V))
  obtain ⟨z, hz⟩ : ∃ z : Z1 ⟶ splitTorus (Sp V) X, GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z = F :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hzχ : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    show GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z (Multiplicative.ofAdd χ) = _
    rw [hz]; rfl
  have hzL : z ^ L = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1).injective
    rw [map_pow, hz, map_one]
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show unitOn _ ^ L = 1
    rw [unitOn, ← map_pow, hpow, map_one]

  let x : Over.mk (Z1.hom ≫ ξ) ⟶ G := pushPt h.1.w (z ≫ j)
  have hxL : x ^ L = 1 := by
    have e1 : pushPt h.1.w ((z ≫ j) ^ L) = x ^ L := map_pow (pushHom h Z1) (z ≫ j) L
    rw [← e1, ← pow_comp, hzL, one_comp]
    exact map_one (pushHom h Z1)

  obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
  have hvb : spMap b ≫ v = (z₀ ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := ValAt.unique (hv.comp (spMap b)) hv₀
  obtain ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩ := hv
  let H : Over.mk W.ι ⟶ G := Over.homMk hW hW1
  have hne : (W : Set M.Z).Nonempty := ⟨ξ (closedPoint V), by rw [← hs']; exact (s' (closedPoint V)).2⟩
  haveI : Nonempty W.toScheme := ⟨⟨_, hne.some_mem⟩⟩
  haveI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hr : Set.range M.pt ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x₀ := IsOpenImmersion.lift W.ι M.pt hr
  have hx₀ : x₀ ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (x₀ ≫ W.ι) := hx₀ ▸ M.isDominant_pt
  haveI : IsDominant x₀ := IsDominant.of_comp_of_isOpenImmersion x₀ W.ι
  have hHL : H ^ L = 1 := by
    let u : Over.mk M.pt ⟶ Over.mk W.ι := Over.homMk x₀ hx₀
    have hu : u ≫ H = gγ t := Over.OverMorphism.ext (hW2 x₀ hx₀)
    have e : u ≫ H ^ L = u ≫ 1 := by rw [comp_pow, hu, hgγ t, comp_one]
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk W.ι).left := inferInstanceAs (IsReduced W.toScheme)
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x₀ ?_
    · rw [Over.w, Over.w]
    · exact congrArg CommaMorphism.left e
  let σ : Over.mk (Z1.hom ≫ ξ) ⟶ Over.mk W.ι := Over.homMk s' (by
    show s' ≫ W.ι = 𝟙 _ ≫ ξ
    rw [hs', Category.id_comp])
  let y : Over.mk (Z1.hom ≫ ξ) ⟶ G := σ ≫ H
  have hyL : y ^ L = 1 := by
    show (σ ≫ H) ^ L = 1
    rw [← comp_pow, hHL, comp_one]

  have hw' : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
    rw [Category.assoc, Over.w z]; simp [Z1]
  let z' : Over.mk (𝟙 (Sp κ)) ⟶ splitTorus (Sp κ) X :=
    Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw')
      ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
  have hz'l : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
    (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
  have hz'χ : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    ext
    have e := congrArg Units.val (hzχ χ)
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
    rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz'l,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [e]
    simp only [unitOn, Units.coe_map]
    have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.symm.trans ?_
    simp
  have hzz : z₀ = z' := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp κ) X _).injective
    refine MonoidHom.ext fun χ => ?_
    exact (hz₀ (Multiplicative.toAdd χ)).trans (hz'χ (Multiplicative.toAdd χ)).symm
  have hcl : spMap b ≫ x.left = spMap b ≫ y.left := by
    show spMap b ≫ (z ≫ j).left ≫ φ₁ = spMap b ≫ s' ≫ hW
    rw [hsv, hvb, hzz]
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% (pullTorus_left hψ₀ j), reassoc_of% hz'l]
  have hLV : IsUnit (L : V) := by simpa using hLu.map a
  have hxy : x = y := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint M.Z G hG.smooth V (Z1.hom ≫ ξ) L hLV x y
    (by rw [hxL, hyL]) κ b hb hcl
  refine ⟨z, hzχ, ?_⟩
  have e' : (z ≫ j).left ≫ φ₁ = v := (congrArg CommaMorphism.left hxy).trans hsv
  rw [e']
  exact ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩

end GlobalTheory.Poinc.FibLat.ClosedLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCompat_of_compat_closedPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  first | exact @GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed | exact GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed | (intros; apply GlobalTheory.Poinc.FibLat.ClosedLift.compat_of_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem compat_of_compat_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK
  haveI hsep : IsSeparated G.hom := hG.separated
  haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSchemeTheoreticallyDominant (spMap b) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb
  haveI : QuasiCompact (spMap b) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) :=
    IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip
  have hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ := h₁.1.w
  refine ⟨fun e => ?_, fun t => ?_⟩
  · have h1 := hK.1 e
    rw [← pullTorus_torusMap_comp] at h1
    simp only [Category.assoc] at h1
    have e1 := pullTorus_left hψ j
    have e2 := pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_
    · simp only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]
    · calc bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ (f e).left
          = (pullTorus hψ j).left ≫ ψ ≫ φ₁ ≫ (f e).left := by rw [reassoc_of% e1]
        _ = (pullTorus hψ (torusMap (Sp V) (m e) ≫ j)).left ≫ ψ ≫ φ₁ := h1
        _ = bcMap (spMap b) X ≫ (torusMap (Sp V) (m e) ≫ j).left ≫ φ₁ := by rw [reassoc_of% e2]
  · obtain ⟨zK, hzK, hvK⟩ := hK.2 t
    haveI : NeZero L := ⟨hL.ne'⟩
    have huL : Units.map a.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
    let φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ :=
      { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
        map_one' := by simp [unitOn]
        map_mul' := fun x y => by
          simp only [toAdd_mul, map_add (f := _), unitOn]
          rw [ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }
    let z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X := (GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh
    have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
      rfl
    have hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    have hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    have hzz : zK = z' := GlobalTheory.SplitTorus.hom_ext fun χ => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val,
        ← GlobalTheory.UU.chV_val, hzK, hcz']
    have hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁) := by
      convert hvK using 1
      rw [hzz, Over.comp_left, Over.comp_left]
      simp only [Category.assoc]
      rw [reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
    have hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁ := (hv.comp (spMap b)).unique hvK'
    have hveq : v = (z ≫ j).left ≫ φ₁ := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv
      rw [hv.over]
      simp only [Category.assoc, hw, Over.comp_left, Over.w_assoc]
      exact (Category.id_comp _).symm
    exact ⟨z, hz, hveq ▸ hv⟩

end GlobalTheory.Poinc.FibLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCompatOfCompatOverFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCompat_of_compat_over_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  first | exact @GlobalTheory.Poinc.FibLat.compat_of_compat_field | exact GlobalTheory.Poinc.FibLat.compat_of_compat_field | (intros; apply GlobalTheory.Poinc.FibLat.compat_of_compat_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat


open GlobalTheory.NonlocalTrait in
theorem exists_trait_torusPart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  intro Y _ _ G _ _ hG w w' hsp hne
  let s' : Sp (Y.presheaf.stalk w') ⟶ Y := Y.fromSpecStalk w'
  let g : Y.presheaf.stalk w' →+* Y.presheaf.stalk w := (Y.presheaf.stalkSpecializes hsp).hom
  have hgs : spMap g ≫ s' = Y.fromSpecStalk w := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hg : ¬ IsLocalHom g := by
    intro hl
    apply hne
    have h1 : (spMap g) (closedPoint (Y.presheaf.stalk w)) = closedPoint (Y.presheaf.stalk w') :=
      Spec_closedPoint
    calc w = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := Scheme.fromSpecStalk_closedPoint.symm
      _ = (spMap g ≫ s') (closedPoint (Y.presheaf.stalk w)) := by rw [hgs]
      _ = s' ((spMap g) (closedPoint (Y.presheaf.stalk w))) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  let GR := (Over.pullback s').obj G
  have hGR : IsSemiAbelian GR := IsSemiAbelian.pullback _ G hG
  obtain ⟨V, _, _, hV, ψ, Ω, _, α, β, hψ, hβ, e, ⟨E⟩⟩ :=
    GlobalTheory.exists_trait_nonlocal_torusExtension (Y.presheaf.stalk w') GR hGR (Y.presheaf.stalk w) g hg
  let alg := algebraMap V (FractionRing V)
  let ξ : Sp V ⟶ Y := spMap ψ ≫ s'
  let G₁ := (Over.pullback ξ).obj G
  have h₁ : IsGrpPullback G₁ G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback _ G hG
  let GK := (Over.pullback (spMap (alg.comp ψ))).obj GR
  have hK : IsGrpPullback GK G (spMap alg ≫ ξ) _ :=
    ((isGrpPullback_pullback GR (spMap (alg.comp ψ))).comp (isGrpPullback_pullback G s')).congr
      (by rw [spMap_comp', Category.assoc]) rfl
  let ψ' : GK.left ⟶ G₁.left := h₁.1.lift _ (GK.hom ≫ spMap alg) (by rw [hK.1.w, Category.assoc])
  have hψ' : IsGrpPullback GK G₁ (spMap alg) ψ' :=
    h₁.cancel (hK.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _)
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  obtain ⟨j, hj, ej⟩ := GlobalTheory.TorusPart.extend_torus_hom_dvr V G₁ hG₁ GK ψ' hψ' ⟨E⟩ (FractionRing V) (RingHom.id _) GK ψ'
    hψ' E.X E.i E.i_hom
  haveI : IsLocalHom ψ := hψ
  have hαl : IsLocalHom α := ⟨fun x hx => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx⟩
  have hβl : IsLocalHom β := ⟨fun x hx => by
    by_contra hn
    rw [hβ x ((mem_maximalIdeal x).2 hn)] at hx
    exact not_isUnit_zero hx⟩
  have key : spMap α ≫ spMap alg ≫ ξ = spMap β ≫ Y.fromSpecStalk w := by
    calc spMap α ≫ spMap alg ≫ ξ = spMap ((α.comp alg).comp ψ) ≫ s' := by
          simp only [ξ, spMap_comp', Category.assoc]
      _ = spMap (β.comp g) ≫ s' := by rw [e]
      _ = spMap β ≫ Y.fromSpecStalk w := by rw [spMap_comp', Category.assoc, hgs]
  refine ⟨V, inferInstance, inferInstance, hV, ξ, G₁, inferInstance, inferInstance, pullback.fst G.hom ξ, E.X,
    inferInstance, inferInstance, inferInstance, j, GK, inferInstance, ψ', hψ', ?_, ?_, h₁, hj, ?_⟩
  · have h1 : (spMap ψ) (closedPoint V) = closedPoint (Y.presheaf.stalk w') := Spec_closedPoint
    calc ξ (closedPoint V) = s' ((spMap ψ) (closedPoint V)) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  · have h1 : (spMap α) (closedPoint Ω) = closedPoint (FractionRing V) := Spec_closedPoint
    have h2 : (spMap β) (closedPoint Ω) = closedPoint (Y.presheaf.stalk w) := Spec_closedPoint
    calc (spMap alg ≫ ξ) (closedPoint (FractionRing V)) = (spMap alg ≫ ξ) ((spMap α) (closedPoint Ω)) := by rw [h1]
      _ = (spMap α ≫ spMap alg ≫ ξ) (closedPoint Ω) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap β ≫ Y.fromSpecStalk w) (closedPoint Ω) := by rw [key]
      _ = Y.fromSpecStalk w ((spMap β) (closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
      _ = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := by rw [h2]
      _ = w := Scheme.fromSpecStalk_closedPoint
  · have : GlobalTheory.TorusPart.pullTorus hψ' j = E.i := ej
    rw [this]
    exact isTorPart_torusExtension E

end GlobalTheory.Poinc.FibLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitSpreadingTorusPartOfSpecialisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_trait_torusPart | exact GlobalTheory.Poinc.FibLat.exists_trait_torusPart | (intros; apply GlobalTheory.Poinc.FibLat.exists_trait_torusPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

section General

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} {X : Type} [AddCommGroup X]

theorem pullTorus_left_comp_iso (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G) :
    (pullTorus h i).left ≫ h.1.isoPullback.hom = (bcIso f X).hom.left ≫ ((Over.pullback f).map i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullTorus_left, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.fst G.hom f = pullback.fst (splitTorus S X).hom f ≫ i.left := by
      simp
    rw [this, ← Category.assoc, GlobalTheory.SplitTorus.bcIso_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc]
    have : ((Over.pullback f).map i).left ≫ pullback.snd G.hom f = pullback.snd (splitTorus S X).hom f := by
      simp
    rw [this, Over.w (pullTorus h i)]
    exact (Over.w (bcIso f X).hom).symm

theorem mono_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion ((Over.pullback f).map i).left) : Mono (pullTorus h i) := by
  have k := pullTorus_left_comp_iso h i
  have : Mono ((bcIso f X).hom.left ≫ ((Over.pullback f).map i).left) := inferInstance
  rw [← k] at this
  have : Mono (pullTorus h i).left := mono_of_mono _ h.1.isoPullback.hom
  exact (Over.forget _).mono_of_mono_map this

theorem closedImm_of_pullTorus (h : IsGrpPullback G' G f φ) (i : splitTorus S X ⟶ G)
    (hc : IsClosedImmersion (pullTorus h i).left) : IsClosedImmersion ((Over.pullback f).map i).left := by
  have k := pullTorus_left_comp_iso h i
  have e : ((Over.pullback f).map i).left = (bcIso f X).inv.left ≫ (pullTorus h i).left ≫ h.1.isoPullback.hom := by
    rw [k, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
  haveI : IsIso (bcIso f X).inv.left := inferInstanceAs (IsIso ((Over.forget _).map (bcIso f X).inv))
  rw [e]
  infer_instance

theorem isClosedImmersion_of_isTorPart {tι : splitTorus S X ⟶ G} (h : IsTorPart tι) : IsClosedImmersion tι.left := by
  obtain ⟨-, B, _, q, hB, -, hk⟩ := h
  have h₁ : IsClosedImmersion (η[B].left ≫ B.hom) := by
    rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 S))
  have h₂ : IsClosedImmersion η[B].left := IsClosedImmersion.of_comp _ B.hom
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hk.map (Over.forget S)).flip h₂

theorem isIso_torusMap (T : Scheme.{0}) {Y : Type} [AddCommGroup Y] (e : X ≃+ Y) :
    IsIso (torusMap T e.toAddMonoidHom) :=
  ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩

end General

theorem spMap_fractionRing_closedPoint (V : Type) [CommRing V] [IsDomain V] :
    (spMap (algebraMap V (FractionRing V))) (closedPoint (FractionRing V)) = genericPoint (Sp V) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V (FractionRing V)) (maximalIdeal (FractionRing V)) = ⊥
  rw [maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V _)

theorem bijective_of_mono_torusMap {κ : Type} [Field κ] {X₀ X₁ : Type} [AddCommGroup X₀] [AddCommGroup X₁]
    [Module.Free ℤ X₀] [Module.Finite ℤ X₀] [Module.Free ℤ X₁] [Module.Finite ℤ X₁]
    (hr : Module.finrank ℤ X₀ = Module.finrank ℤ X₁) (ρ : X₀ →+ X₁) [Mono (torusMap (Sp κ) ρ)] :
    Function.Bijective ρ := by
  have hs : Function.Surjective ρ := by
    let l : X₁ →+ X₁ ⧸ ρ.range := QuotientAddGroup.mk' ρ.range
    have e : torusMap (Sp κ) l ≫ torusMap (Sp κ) ρ =
        torusMap (Sp κ) (0 : X₁ →+ X₁ ⧸ ρ.range) ≫ torusMap (Sp κ) ρ := by
      rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
      congr 1
      ext x
      simp [l]
    have e2 := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
    intro y
    have hy : QuotientAddGroup.mk' ρ.range y = 0 := DFunLike.congr_fun e2 y
    obtain ⟨x, hx⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨x, hx⟩
  let e₀ : X₁ ≃ₗ[ℤ] X₀ := LinearEquiv.ofFinrankEq X₁ X₀ hr.symm
  have hinj := OrzechProperty.injective_of_surjective_endomorphism (e₀.toLinearMap ∘ₗ ρ.toIntLinearMap)
    (e₀.surjective.comp hs)
  exact ⟨fun a b hab => hinj (by simp [hab]), hs⟩

end GlobalTheory.Poinc.FibClosed

namespace GlobalTheory.Poinc.FibClosed

open GlobalTheory.SplitTorus (torusMap bcMap bcIso)

theorem isTorPart_pullTorus_closed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  intro V _ _ _ G₁ _ _ hG X₁ _ _ _ j hj GK _ ψ hψ hgen κ _ b hb G₀ _ ψ₀ hψ₀ X₀ _ _ _ t₀ ht₀ hr
  haveI := hj
  let e : X₁ ≃+ (Fin (Module.finrank ℤ X₁) → ℤ) := (Module.finBasis ℤ X₁).equivFun.toAddEquiv
  let u : splitTorus (Sp V) (Fin (Module.finrank ℤ X₁) → ℤ) ⟶ G₁ := torusMap (Sp V) e.toAddMonoidHom ≫ j
  have hu : IsMonHom u := inferInstance
  have hgenU : ∀ (k : Type) [Field k] (g : Sp k ⟶ Sp V), g (closedPoint k) = genericPoint (Sp V) →
      IsClosedImmersion ((Over.pullback g).map u).left := by
    intro k _ g hg
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue u k g, hg, ← spMap_fractionRing_closedPoint V,
      ← GlobalTheory.TorusFibreImm.closedImm_iff_residue u (FractionRing V) _]
    refine closedImm_of_pullTorus hψ u ?_
    rw [pullTorus_torusMap_comp, Over.comp_left]
    haveI := isClosedImmersion_of_isTorPart hgen
    haveI := isIso_torusMap (Sp (FractionRing V)) e
    haveI : IsIso (torusMap (Sp (FractionRing V)) e.toAddMonoidHom).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (torusMap (Sp (FractionRing V)) e.toAddMonoidHom)))
    infer_instance
  have hsp := GlobalTheory.TorusFibre.isClosedImmersion_special_of_local V (FractionRing V) G₁ hG _ u hu
    (by
      haveI := hgenU (FractionRing V) _ (spMap_fractionRing_closedPoint V)
      exact (Over.forget _).mono_of_mono_map
        (inferInstanceAs (Mono ((Over.pullback (spMap (algebraMap V (FractionRing V)))).map u).left)))
  have hfib : IsClosedImmersion ((Over.pullback (spMap b)).map u).left := by
    have h2 := (GlobalTheory.TorusFibreImm.closedImm_iff_residue u (ResidueField V) _).1 hsp
    have h3 : (Spec.map (CommRingCat.ofHom (algebraMap V (ResidueField V)))) (closedPoint (ResidueField V)) =
        (spMap b) (closedPoint κ) :=
      (IsLocalRing.comap_closedPoint (residue V)).trans (IsLocalRing.comap_closedPoint b).symm
    rw [GlobalTheory.TorusFibreImm.closedImm_iff_residue, ← h3]
    exact h2
  have hmono : Mono (pullTorus hψ₀ u) := mono_pullTorus hψ₀ u hfib
  have hmono' : Mono (pullTorus hψ₀ j) := by
    have k : pullTorus hψ₀ j = torusMap _ e.symm.toAddMonoidHom ≫ pullTorus hψ₀ u := by
      rw [pullTorus_torusMap_comp, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X₁ from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
    haveI := isIso_torusMap (Sp κ) e.symm
    rw [k]
    infer_instance
  obtain ⟨ρ, hρ⟩ := ht₀.factor (pullTorus hψ₀ j) inferInstance
  haveI : Mono (torusMap (Sp κ) ρ) := by
    rw [hρ] at hmono'
    exact mono_of_mono _ t₀
  have hbij := bijective_of_mono_torusMap (κ := κ) hr ρ
  have h := ht₀.equiv (AddEquiv.ofBijective ρ hbij)
  rw [hρ]
  exact h

end GlobalTheory.Poinc.FibClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusPartGenericFibreClosedFibreDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (X₁ : Type) [AddCommGroup X₁] [Module.Free ℤ X₁] [Module.Finite ℤ X₁] (j : splitTorus (Sp V) X₁ ⟶ G₁), IsMonHom j → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (t₀ : splitTorus (Sp κ) X₀ ⟶ G₀), IsTorPart t₀ → Module.finrank ℤ X₀ = Module.finrank ℤ X₁ → IsTorPart (pullTorus hψ₀ j) := by
  first | exact @GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | exact GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed | (intros; apply GlobalTheory.Poinc.FibClosed.isTorPart_pullTorus_closed <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem ringHom_eq_of_spMap {A B : Type} [CommRing A] [CommRing B] {a b : A →+* B} (h : spMap a = spMap b) : a = b := by
  have h1 := Spec.map_injective h
  have h2 := congrArg CommRingCat.Hom.hom h1
  simpa using h2

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (s : Sp B ⟶ Sp A) : ∃ a : A →+* B, s = spMap a := ⟨(Spec.preimage s).hom, by simp [spMap]⟩

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (z : T ⟶ (Over.pullback f).obj G) (z₀ : (Over.map f).obj T ⟶ G),
      z₀.left = z.left ≫ pullback.fst G.hom f → z = (Over.mapPullbackAdj f).unit.app T ≫ (Over.pullback f).map z₀ := by
    intro z z₀ hz
    ext
    apply pullback.hom_ext
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, hz, Over.homMk_left]
      erw [pullback.lift_fst_assoc, Category.id_comp]
    · simp only [Over.pullback_obj_left, Over.mapPullbackAdj_unit_app, Over.comp_left, Over.pullback_map_left,
        Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Over.homMk_left]
      erw [pullback.lift_snd]
      exact Over.w z
  rw [key x x₀ hx, key y y₀ hy, ← MonObj.comp_mul, ← Functor.map_mul]
  simp

theorem exists_common_pullback {Y : Scheme.{0}} {G : Over Y} [GrpObj G] {κ κ' : Type} [Field κ] [Field κ'] {s : Sp κ ⟶ Y}
    {s' : Sp κ' ⟶ Y} (hs : s (closedPoint κ) = s' (closedPoint κ')) {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {G₀' : Over (Sp κ')} [GrpObj G₀'] {φ' : G₀'.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ)
    (hφ' : IsGrpPullback G₀' G s' φ') :
    ∃ (K : Type) (_ : Field K) (b : κ →+* K) (b' : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀.left)
      (ψ' : GK.left ⟶ G₀'.left), spMap b ≫ s = spMap b' ≫ s' ∧ IsGrpPullback GK G₀ (spMap b) ψ ∧
      IsGrpPullback GK G₀' (spMap b') ψ' ∧ ψ ≫ φ = ψ' ≫ φ' := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s) (g := s') _ _ hs
  obtain ⟨K, _, ⟨p⟩⟩ : ∃ (K : Type) (_ : Field K), Nonempty (Sp K ⟶ pullback s s') :=
    ⟨_, inferInstance, ⟨(pullback s s').fromSpecResidueField z⟩⟩
  obtain ⟨b, hb⟩ := exists_spMap (p ≫ pullback.fst s s')
  obtain ⟨b', hb'⟩ := exists_spMap (p ≫ pullback.snd s s')
  have e : spMap b ≫ s = spMap b' ≫ s' := by
    rw [← hb, ← hb', Category.assoc, Category.assoc, pullback.condition]
  have hψ := isGrpPullback_pullback_fst (spMap b) G₀
  set ψ := pullback.fst G₀.hom (spMap b)
  set GK := (Over.pullback (spMap b)).obj G₀
  have w0 : (ψ ≫ φ) ≫ G.hom = (GK.hom ≫ spMap b') ≫ s' := by
    simp only [Category.assoc]
    rw [hφ.1.w, ← Category.assoc ψ, hψ.1.w, Category.assoc, e]
  refine ⟨K, inferInstance, b, b', GK, inferInstance, ψ, hφ'.1.lift (ψ ≫ φ) (GK.hom ≫ spMap b') w0, e, hψ, ?_,
    (hφ'.1.lift_fst _ _ _).symm⟩
  have n := hψ.comp hφ
  rw [e, ← hφ'.1.lift_fst (ψ ≫ φ) (GK.hom ≫ spMap b') w0] at n
  exact IsGrpPullback.cancel hφ' n (hφ'.1.lift_snd _ _ _)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z} [GrpObj G]
  {I T : Type} {f : I → (G ⟶ G)} {gγ : T → (Over.mk M.pt ⟶ G)} {ζ : oˣ} {L : ℕ}

theorem RkAt.unique {w : M.Z} {r r' : ℕ} (h : RkAt G w r) (h' : RkAt G w r') : r = r' := by
  obtain ⟨X, _, _, _, κ, _, s, G₀, _, φ, tι, hs, hφ, ht, rfl⟩ := h
  obtain ⟨X', _, _, _, κ', _, s', G₀', _, φ', tι', hs', hφ', ht', rfl⟩ := h'
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', -, hψ, hψ', -⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, -⟩ := IsTorPart.exists_equiv (ht.pull hψ) (ht'.pull hψ')
  exact e.toIntLinearEquiv.finrank_eq

theorem LatAt.transfer {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : I → X →+ X}
    {c : T → X →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w) {κ' : Type} [Field κ'] {s' : Sp κ' ⟶ M.Z}
    (hs' : s' (closedPoint κ') = w) {a' : o →+* κ'} (ha' : s' ≫ M.s = spMap a') {G₀' : Over (Sp κ')} [GrpObj G₀']
    {φ' : G₀'.left ⟶ G.left} (hφ' : IsGrpPullback G₀' G s' φ') {X' : Type} [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {t' : splitTorus (Sp κ') X' ⟶ G₀'} (ht' : IsTorPart t') :
    ∃ (e : X' ≃+ X) (K : Type) (_ : Field K) (b : κ' →+* K) (GK : Over (Sp K)) (_ : GrpObj GK) (ψ : GK.left ⟶ G₀'.left)
      (hψ : IsGrpPullback GK G₀' (spMap b) ψ),
      Compat f gγ ζ L m c (spMap b ≫ s') (b.comp a') (ψ ≫ φ') (torusMap _ e.toAddMonoidHom ≫ pullTorus hψ t') := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hc⟩ := h
  obtain ⟨K, _, b, b', GK, _, ψ, ψ', e1, hψ, hψ', e2⟩ := exists_common_pullback (hs.trans hs'.symm) hφ hφ'
  obtain ⟨e, he⟩ := IsTorPart.exists_equiv (ht'.pull hψ') (ht.pull hψ)
  have hab : b.comp a = b'.comp a' := by
    apply ringHom_eq_of_spMap
    rw [← spMap_comp', ← spMap_comp', ← ha, ← ha', reassoc_of% e1]
  refine ⟨e, K, inferInstance, b', GK, inferInstance, ψ', hψ', ?_⟩
  have hc2 := hc.pull b hψ
  rw [he, e1, hab, e2] at hc2
  exact hc2

theorem Compat.unique [IsSeparated G.hom] (hL : 0 < L) {X : Type} [AddCommGroup X] {m m' : I → X →+ X}
    {c c' : T → X →+ ZMod L} {K : Type} [Field K] {s : Sp K ⟶ M.Z} {a : o →+* K} (hζ : IsPrimitiveRoot (a ζ) L)
    {G₀ : Over (Sp K)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (hφ : IsGrpPullback G₀ G s φ) {t : splitTorus (Sp K) X ⟶ G₀}
    (ht : IsTorPart t) (h : Compat f gγ ζ L m c s a φ t) (h' : Compat f gγ ζ L m' c' s a φ t) : m = m' ∧ c = c' := by
  obtain ⟨hm, hc⟩ := h
  obtain ⟨hm', hc'⟩ := h'
  constructor
  · funext e
    apply ht.cancel
    apply hom_ext_of_pullback hφ
    rw [← hm e, ← hm' e]
  · funext tt
    obtain ⟨z, hz, hv⟩ := hc tt
    obtain ⟨z', hz', hv'⟩ := hc' tt
    have hzz : z = z' := by
      have := ht.mono
      apply (cancel_mono t).1
      apply hom_ext_of_pullback hφ
      exact ValAt.unique hv hv'
    subst hzz
    ext χ
    have h3 := congrArg Units.val (GlobalTheory.ZH.TorusPerp.unitOn_injective ((hz χ).symm.trans (hz' χ)))
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3
    haveI : NeZero L := ⟨hL.ne'⟩
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

theorem LatAt.unique [IsSeparated G.hom] (hL : 0 < L) (hζ : ∀ (κ : Type) [Field κ] (a : o →+* κ), IsPrimitiveRoot (a ζ) L)
    {X X' : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X']
    [Module.Finite ℤ X'] {m : I → X →+ X} {c : T → X →+ ZMod L} {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z}
    (h : LatAt f gγ ζ L m c w) (h' : LatAt f gγ ζ L m' c' w) :
    ∃ θ : X ≃+ X', (∀ e x, θ (m e x) = m' e (θ x)) ∧ ∀ t x, c' t (θ x) = c t x := by
  obtain ⟨κ', _, s', a', G₀', _, φ', tι', hs', ha', hφ', ht', hc'⟩ := h'
  obtain ⟨e, K, _, b, GK, _, ψ, hψ, hc⟩ := h.transfer hs' ha' hφ' ht'
  have hc2 := (hc'.pull b hψ).equiv e (m' := fun i => (e : X' →+ X).comp ((m' i).comp (e.symm : X →+ X')))
    (c' := fun t => (c' t).comp (e.symm : X →+ X')) (fun i x => by simp) (fun t x => by simp)
  obtain ⟨h1, h2⟩ := Compat.unique hL (hζ K (b.comp a')) (hψ.comp hφ') ((ht'.pull hψ).equiv e) hc hc2
  subst h1 h2
  refine ⟨e.symm, fun i x => ?_, fun t x => ?_⟩ <;> simp

theorem LatAt.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {w : M.Z} (h : LatAt f gγ ζ L m c w)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) : LatAt f gγ ζ L m' c' w := by
  obtain ⟨κ, _, s, a, G₀, _, φ, tι, hs, ha, hφ, ht, hcc⟩ := h
  exact ⟨κ, _, s, a, G₀, _, φ, _, hs, ha, hφ, ht.equiv e, hcc.equiv e hm hc⟩

private theorem ratModel_isLocallyNoetherian {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o]
    (M : RatModel o Ω) : IsLocallyNoetherian M.Z := by
  have := M.lft
  constructor
  intro U
  have h1 := HasRingHomProperty.appLE @LocallyOfFiniteType M.s this ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have : IsNoetherianRing Γ(Sp o, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  letI := (M.s.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  have : Algebra.FiniteType Γ(Sp o, ⊤) Γ(M.Z, U.1) := h1
  exact Algebra.FiniteType.isNoetherianRing Γ(Sp o, ⊤) Γ(M.Z, U.1)

theorem latAt_iff_of_specializes [IsNoetherianRing o] [IsCommMonObj G] (hG : IsSemiAbelian G) (hL : 0 < L) (hζ : ζ ^ L = 1)
    (hu : IsUnit (L : o)) (hf : ∀ e, IsMonHom (f e)) (hγ : ∀ t, gγ t ^ L = 1) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) {w w' : M.Z} (hw : w ⤳ w') {r : ℕ}
    (hr : RkAt G w r) (hr' : RkAt G w' r) (hext : ∀ t, ExtNear (gγ t) w') :
    LatAt f gγ ζ L m c w ↔ LatAt f gγ ζ L m c w' := by
  by_cases hww : w = w'
  · subst hww
    exact Iff.rfl
  have := ratModel_isLocallyNoetherian M
  obtain ⟨V, _, _, _, ξ, G₁, _, _, φ₁, X₁, _, _, _, j, GK, _, ψ, hψ, hξ', hξ, hφ₁, hj, hjt⟩ :=
    GlobalTheory.T.exists_trait_spreading_torusPart_of_specialisation M.Z G hG w w' hw hww
  have := hj
  obtain ⟨a, ha⟩ := exists_spMap (ξ ≫ M.s)
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ ξ G G₁ φ₁ hφ₁ hG
  have hgen : IsGrpPullback GK G (spMap (algebraMap V (FractionRing V)) ≫ ξ) (ψ ≫ φ₁) := hψ.comp hφ₁
  have hrX : r = Module.finrank ℤ X₁ :=
    RkAt.unique hr ⟨X₁, _, inferInstance, inferInstance, FractionRing V, inferInstance, _, GK, inferInstance, _, _, hξ,
      hgen, hjt, rfl⟩
  obtain ⟨X₀, _, _, _, κ₀, _, s₀, G₀, _, φ₀, t₀, hs₀, hφ₀, ht₀, hrk₀⟩ := hr'
  have hGc := isGrpPullback_pullback_fst (spMap (IsLocalRing.residue V)) G₁
  have hcl : (spMap (IsLocalRing.residue V) ≫ ξ) (closedPoint (IsLocalRing.ResidueField V)) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (IsLocalRing.residue V))).trans hξ'
  obtain ⟨K, _, b₀, b₁, GK', _, ψ₀, ψ₁, -, hψ₀, hψ₁, -⟩ := exists_common_pullback (hs₀.trans hcl.symm) hφ₀ (hGc.comp hφ₁)
  have hψc : IsGrpPullback GK' G₁ (spMap (b₁.comp (IsLocalRing.residue V)))
      (ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
    rw [← spMap_comp']
    exact hψ₁.comp hGc
  have ht0 : IsTorPart (pullTorus hψc j) :=
    GlobalTheory.T.splitTorusPart_generic_fibre_closed_fibre_dvr V G₁ hG₁ X₁ j hj GK ψ hψ hjt K (b₁.comp (IsLocalRing.residue V)) inferInstance GK' _ hψc X₀ _
      (ht₀.pull hψ₀) (hrk₀.trans hrX)
  have hsc : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) (closedPoint K) = w' :=
    (congrArg (fun x => ξ x) (GtDescent.spMap_cpt (b₁.comp (IsLocalRing.residue V)))).trans hξ'
  have ha_gen : (spMap (algebraMap V (FractionRing V)) ≫ ξ) ≫ M.s = spMap ((algebraMap V (FractionRing V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have ha_cl : (spMap (b₁.comp (IsLocalRing.residue V)) ≫ ξ) ≫ M.s = spMap ((b₁.comp (IsLocalRing.residue V)).comp a) := by
    rw [Category.assoc, ha, spMap_comp']
  have hextV : ∀ t, ExtNear (gγ t) (ξ (closedPoint V)) := by
    rw [hξ']
    exact hext
  constructor
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hξ ha_gen hgen hjt
    have hψ₂' : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (algebraMap V (FractionRing V)))) (ψ₂ ≫ ψ) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψ
    have hinj : Function.Injective (b₂.comp (algebraMap V (FractionRing V))) :=
      b₂.injective.comp (IsFractionRing.injective V (FractionRing V))
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_over_field o Ω M G hG I T f gγ ζ L hL hζ X m c V ξ a G₁ φ₁ hφ₁ _ hextV K₂ _ hinj GK₂ _ hψ₂' ?_
      rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψ hψ₂' (spMap_comp' _ _).symm rfl, ← spMap_comp']
      simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc2 := hcV.pull (b₁.comp (IsLocalRing.residue V)) hψc
    rw [pullTorus_torusMap_comp] at hc2
    exact ⟨K, _, _, _, GK', _, _, _, hsc, ha_cl, hψc.comp hφ₁, ht0.equiv e, hc2⟩
  · intro h
    obtain ⟨e, K₂, _, b₂, GK₂, _, ψ₂, hψ₂, hc⟩ := h.transfer hsc ha_cl (hψc.comp hφ₁) ht0
    have hψ₃ : IsGrpPullback GK₂ G₁ (spMap (b₂.comp (b₁.comp (IsLocalRing.residue V))))
        (ψ₂ ≫ ψ₁ ≫ pullback.fst G₁.hom (spMap (IsLocalRing.residue V))) := by
      rw [← spMap_comp']
      exact hψ₂.comp hψc
    have hcV : Compat f gγ ζ L m c ξ a φ₁ (torusMap _ e.toAddMonoidHom ≫ j) := by
      refine GlobalTheory.T.torusCompat_of_compat_closedPoint o Ω M G hG I T f gγ ζ L hL hζ hu hf hγ X m c V ξ a G₁ φ₁ hφ₁ _ inferInstance hextV GK ψ hψ
        ?_ K₂ _ inferInstance GK₂ _ hψ₃ ?_ ?_
      · rw [pullTorus_torusMap_comp]
        exact hjt.equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl]
        exact (ht0.pull hψ₂).equiv e
      · rw [pullTorus_torusMap_comp, ← pullTorus_pullTorus hψ₂ hψc hψ₃ (spMap_comp' _ _).symm rfl, ← spMap_comp']
        simpa only [Category.assoc, RingHom.comp_assoc] using hc
    have hc3 := hcV.pull (algebraMap V (FractionRing V)) hψ
    rw [pullTorus_torusMap_comp] at hc3
    exact ⟨FractionRing V, _, _, _, GK, _, _, _, hξ, ha_gen, hgen, hjt.equiv e, hc3⟩

end GlobalTheory.Poinc.FibLat
