module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivMapOfTorMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem equivMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ, TorMatch U U' g β ρ → EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ h
  intro f f' hf hf' hc m m' hm hm' y
  have hkV : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V) := fun k hk => by
    simpa using hk.map g
  have hkR : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ hk => hk
  have t := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G hG D A U f hf m hm
  have t' := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V hV G' hG' D' A' U' f' hf' m' hm'
  have c₁ := torMatch_comp R hR G hG D A U R hR G hG D A U (RingHom.id R) f.left V hV G' hG' D' A' U' g β hg hkR m ρ t h
  have c₂ := torMatch_comp R hR G hG D A U V hV G' hG' D' A' U' g β V hV G' hG' D' A' U' (RingHom.id V) f'.left
    Function.injective_id hkV ρ m' h t'
  rw [RingHom.comp_id] at c₁
  rw [RingHom.id_comp, hc] at c₂
  have e := torMatch_unique R hR G hG D A U V hV G' hG' D' A' U' g (β ≫ f.left) hg _ _ c₁ c₂
  exact DFunLike.congr_fun e y

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompOfIsMonHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SpreadTorMatch

theorem spMap_comp_ringHom' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem section_over_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ)
    (s : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G)),
    (∀ (B : Type) [CommRing B] (a : R →+* B) τ h, s B a τ h ^ k = 1) →
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (a' : R →+* B') (f : B →+* B') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : B') = f (τ χ : B)) → (s B' a' τ' h').left = spMap f ≫ (s B a τ h).left) →
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (a' : R →+* B') (f : B →+* B')
      (G₀ : Over (Sp B)) [GrpObj G₀] (m₀ : G₀.left ⟶ G.left) (hm₀ : IsGrpPullback G₀ G (spMap a) m₀) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha hm₀).left ≫ m₀) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (GV : Over (Sp V)) [GrpObj GV] [IsCommMonObj GV]
      (mV : GV.left ⟶ G.left) (hmV : IsGrpPullback GV G (spMap ψ) mV)
      (j : splitTorus (Sp V) X' ⟶ GV) [IsMonHom j]
      (G₀ : Over (Sp (ResidueField V))) [GrpObj G₀] (m₀ : G₀.left ⟶ GV.left)
      (hm₀ : IsGrpPullback G₀ GV (spMap (residue V)) m₀)
      (h₀ : ∀ x ∈ maximalIdeal R ^ (0 + 1), (residue V).comp ψ x = 0) (m₀' : G₀.left ⟶ G.left)
      (hm₀' : IsGrpPullback G₀ G (spMap ((residue V).comp ψ)) m₀'),
      m₀' = m₀ ≫ mV →
      GlobalTheory.TorusPart.pullTorus hm₀ j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀' →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (u : V →+* W), IsLocalHom u → IsUnit (k : W) →
    ∀ (τW : Multiplicative X' →* Wˣ) (τ : Multiplicative D.toPre.X →* Wˣ) (h : τ ^ k = 1),
      τW ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τW (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τW (Multiplicative.ofAdd χ))) →
      (s W (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV := by
  intro R _ _ _ G _ _ hG D A U k s hpow hnat htor X' _ ρ V _ _ ψ GV _ _ mV hmV j _ G₀ _ m₀ hm₀ h₀ m₀' hm₀'
    hmm hpt W _ _ u hu hk τW τ h hτWk hτ z hz
  obtain ⟨_, hsm, _, _, _, _⟩ := hG
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hmV (Over.mk (spMap u)) (spMap (u.comp ψ))
    (spMap_comp_ringHom' ψ u)

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun χ => ?_
    have h1 := hz (Multiplicative.toAdd χ)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at h1
    have h2 : τW χ ^ k = 1 := by simpa using DFunLike.congr_fun hτWk χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, h1]
    simp only [unitOn, ← map_pow, h2, map_one]
  have hy : (e (z ≫ j)) ^ k = 1 := by
    rw [← map_pow, ← MonObj.pow_comp, hzk, MonObj.one_comp, map_one]
  suffices hxy : s W (u.comp ψ) τ h = e (z ≫ j) by
    rw [hxy, he]
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hsm W (spMap (u.comp ψ)) k hk _ _
    (by rw [hpow W (u.comp ψ) τ h, hy]) (ResidueField W) (residue W) inferInstance ?_

  let τκ : Multiplicative D.toPre.X →* (ResidueField W)ˣ := (Units.map (residue W).toMonoidHom).comp τ
  have h3 : ∀ χ, τ χ ^ k = 1 := fun χ => by simpa using DFunLike.congr_fun h χ
  have hκ : τκ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (Units.map (residue W).toMonoidHom (τ χ)) ^ k = 1
    rw [← map_pow, h3, map_one]
  have hres : (ResidueField.map u).comp (residue V) = (residue W).comp u := ResidueField.map_comp_residue u
  have hb := GlobalTheory.SplitTorus.isGrpPullback_bcMap (spMap (residue V)) X'
  have hw : (spMap (residue W) ≫ z.left) ≫ (splitTorus (Sp V) X').hom =
      spMap (ResidueField.map u) ≫ spMap (residue V) := by
    rw [Category.assoc, Over.w z]
    show spMap (residue W) ≫ spMap u = _
    rw [← spMap_comp_ringHom', ← spMap_comp_ringHom', hres]
  let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
    Over.homMk (hb.1.lift _ _ hw) (hb.1.lift_snd _ _ _)
  have key : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap (residue W) ≫ z.left :=
    hb.1.lift_fst _ _ _
  let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) ρ
  have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := by
    intro χ
    apply Units.ext
    have hτκ : ((τκ (Multiplicative.ofAdd χ) : (ResidueField W)ˣ) : ResidueField W) =
        residue W (τW (Multiplicative.ofAdd (ρ χ)) : W) := by
      show residue W (τ (Multiplicative.ofAdd χ) : W) = _
      rw [hτ]
    rw [GlobalTheory.UU.chV_val, GlobalTheory.ToricOverField.unitOn_val_map (residue W) _ _ hτκ, ← hz (ρ χ), GlobalTheory.UU.chV_val]
    have hk2 := congrArg (fun φ => φ.appTop.hom (charUnit (Sp V) X' (ρ χ)).val) key
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hk2
    rw [← hk2, GlobalTheory.UU.bcMap_charUnit]
    simp only [z₀, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.torusMap_appTop_chi]
  have hfa : (residue W).comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, hres]
  have hT := htor (ResidueField V) (ResidueField W) ((residue V).comp ψ) h₀ ((residue W).comp (u.comp ψ))
    (ResidueField.map u) G₀ m₀' hm₀' τκ hκ z₀ hfa hz₀
  have hN := hnat W (ResidueField W) (u.comp ψ) ((residue W).comp (u.comp ψ)) (residue W) τ h τκ hκ rfl
    (fun χ => rfl)
  rw [← hN, hT, he]
  have hz0gt : z₀ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus hm₀ j := by
    show (z₁ ≫ _) ≫ _ = _
    rw [Category.assoc, ← hpt]
  rw [hz0gt, hmm]
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc (GlobalTheory.TorusPart.pullTorus hm₀ j).left, GlobalTheory.TorusPart.pullTorus_left, ← Category.assoc,
    ← Category.assoc, key]
  simp only [Category.assoc]

theorem section_over_field : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G']
    (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (k : ℕ)
    (s' : ∀ (B : Type) [CommRing B] (a : W →+* B) (τ : Multiplicative D'.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G')),
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : W →+* B) (ha : ∀ x ∈ maximalIdeal W ^ (0 + 1), a x = 0) (a' : W →+* B') (f : B →+* B')
      (G₀ : Over (Sp B)) [GrpObj G₀] (m₀ : G₀.left ⟶ G'.left) (hm₀ : IsGrpPullback G₀ G' (spMap a) m₀) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D'.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U'.gt 0) ha hm₀).left ≫ m₀) →
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (β : G'.left ⟶ G.left)
      (V : Type) [CommRing V] (G₁ : Over (Sp V)) [GrpObj G₁] (m₁ : G₁.left ⟶ G.left)
      (Ω : Type) [Field Ω] (α : V →+* Ω) (b : W →+* Ω) (hb : ∀ x ∈ maximalIdeal W ^ (0 + 1), b x = 0)
      (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ G₁.left) (hn : IsGrpPullback GΩ G₁ (spMap α) n)
      (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
      (j : splitTorus (Sp V) D'.toPre.X ⟶ G₁),
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn' →
      n ≫ m₁ = n' ≫ β →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp b →
    ∀ (Y : Type) [CommRing Y] (u : V →+* Y) (w : Y →+* Ω'), w.comp u = σ.comp α →
    ∀ (τY : Multiplicative D'.toPre.X →* Yˣ) (τ'' : Multiplicative D'.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τY χ : Y)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) D'.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τY (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ β = spMap w ≫ (z ≫ j).left ≫ m₁ := by
  intro W _ _ _ G' _ _ D' A' U' k s' htor R _ G β V _ G₁ _ m₁ Ω _ α b hb GΩ _ n hn n' hn' j hpull hcomm
    Ω' _ σ a' ha' Y _ u w hwu τY τ'' h hτ z hz
  have hb2 := GlobalTheory.SplitTorus.isGrpPullback_bcMap (spMap α) D'.toPre.X
  have hw : (spMap w ≫ z.left) ≫ (splitTorus (Sp V) D'.toPre.X).hom = spMap σ ≫ spMap α := by
    rw [Category.assoc, Over.w z]
    show spMap w ≫ spMap u = _
    rw [← spMap_comp_ringHom', ← spMap_comp_ringHom', hwu]
  let z₀ : Over.mk (spMap σ) ⟶ splitTorus (Sp Ω) D'.toPre.X :=
    Over.homMk (hb2.1.lift _ _ hw) (hb2.1.lift_snd _ _ _)
  have key : z₀.left ≫ GlobalTheory.SplitTorus.bcMap (spMap α) D'.toPre.X = spMap w ≫ z.left :=
    hb2.1.lift_fst _ _ _
  have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ'' (Multiplicative.ofAdd χ)) := by
    intro χ
    apply Units.ext
    rw [GlobalTheory.UU.chV_val, GlobalTheory.ToricOverField.unitOn_val_map w _ _ (hτ _), ← hz χ, GlobalTheory.UU.chV_val]
    have hk2 := congrArg (fun φ => φ.appTop.hom (charUnit (Sp V) D'.toPre.X χ).val) key
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hk2
    rw [← hk2, GlobalTheory.UU.bcMap_charUnit]
  have hT := htor Ω Ω' b hb a' σ GΩ n' hn' τ'' h z₀ ha' hz₀
  rw [hT, ← hpull]
  simp only [Over.comp_left, Category.assoc]
  rw [← hcomm, ← Category.assoc (GlobalTheory.TorusPart.pullTorus hn j).left, GlobalTheory.TorusPart.pullTorus_left,
    ← Category.assoc, ← Category.assoc, key]
  simp only [Category.assoc]

private theorem powComp_lemma {L M N : Type} [Monoid L] [Monoid M] [CommMonoid N] (τ : M →* N) (ρ : L →* M)
    (k : ℕ) (h : τ ^ k = 1) : (τ.comp ρ) ^ k = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply]

private theorem powMap_lemma_2 {M N P : Type} [Monoid M] [CommMonoid N] [CommMonoid P] (f : N →* P) (τ : M →* N)
    (k : ℕ) (h : τ ^ k = 1) : (f.comp τ) ^ k = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply, map_one]

private theorem unitsLift_lemma_3 (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ)
    (hk : 1 ≤ k) (τ : Multiplicative X →* Kˣ) (h : τ ^ k = 1) :
    ∃ τO : Multiplicative X →* Oˣ, τO ^ k = 1 ∧ (Units.map O.subtype.toMonoidHom).comp τO = τ := by
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one K O X k hk τ h
  have e : (Units.map O.subtype.toMonoidHom).comp τO = τ := MonoidHom.ext fun x => Units.ext (hτO x)
  refine ⟨τO, MonoidHom.ext fun x => ?_, e⟩
  apply Units.map_injective (f := O.subtype.toMonoidHom) (fun a b hab => Subtype.ext hab)
  rw [MonoidHom.pow_apply, map_pow, ← MonoidHom.comp_apply, e, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply, map_one]

private theorem exists_dom_lemma_4 (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] (f : A →+* K) :
    ∃ (O : ValuationSubring K) (φ : A →+* O), IsLocalHom φ ∧ ∀ x, (φ x : K) = f x := by
  obtain ⟨O, hle, hloc⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨O, f.codRestrict O (fun x => hle (f.mem_range_self x)), ⟨fun x hx => ?_⟩, fun x => rfl⟩
  have h1 : IsUnit (Subring.inclusion hle (f.rangeRestrict x)) := hx
  have h2 : IsUnit (f.rangeRestrict x) := hloc.map_nonunit _ h1
  have : IsLocalHom f.rangeRestrict := IsLocalHom.of_surjective _ f.rangeRestrict_surjective
  exact this.map_nonunit _ h2

private theorem exists_comp_lemma_5 (A : Type) [CommRing A] [IsLocalRing A] (K L : Type) [Field K] [Field L]
    (f : A →+* K) (hf : ∀ x ∈ maximalIdeal A, f x = 0) (g : A →+* L) (hg : ∀ x ∈ maximalIdeal A, g x = 0) :
    ∃ (M : Type) (_ : Field M) (p : K →+* M) (q : L →+* M), p.comp f = q.comp g := by
  let f' : ResidueField A →+* K := Ideal.Quotient.lift (maximalIdeal A) f hf
  let g' : ResidueField A →+* L := Ideal.Quotient.lift (maximalIdeal A) g hg
  letI := f'.toAlgebra
  letI := g'.toAlgebra
  haveI : Nontrivial (K ⊗[ResidueField A] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ K L f'.injective g'.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ResidueField A] L)
  have key : ∀ x, f x ⊗ₜ[ResidueField A] (1 : L) = (1 : K) ⊗ₜ[ResidueField A] g x := by
    intro x
    have e1 : f x = algebraMap (ResidueField A) K (residue A x) := rfl
    have e2 : g x = algebraMap (ResidueField A) L (residue A x) := rfl
    rw [e1, e2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact ⟨_ ⧸ m, Ideal.Quotient.field m, (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom,
    RingHom.ext fun x => congrArg (Ideal.Quotient.mk m) (key x)⟩

theorem torMatch_of_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → TorMatch U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, φ₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψ, hφ₁, hj, hα, hαψ, hcomm, hpull, hpt⟩ := hsp
  intro F _ _ _ _ hF k hk τ τ' q q' a a' hτ'k hτρ hqy hqt hq'y hq't hQ hQ'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk
    · exact hpos
  obtain ⟨_, hsm, _, _, _, _⟩ := id hG
  obtain ⟨s, hpow, hnat, htor, hgen⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', hpow', hnat', htor', hgen'⟩ := GlobalTheory.ToricTorsionUnif.main V hV G' hG' D' A' U' k hk1
  let ρm : Multiplicative D.toPre.X →* Multiplicative D'.toPre.X := AddMonoidHom.toMultiplicative ρ
  have hτeq : τ = τ'.comp ρm := MonoidHom.ext fun χ => hτρ (Multiplicative.toAdd χ)
  subst hτeq
  have hτk := powComp_lemma τ' ρm k hτ'k
  rw [hgen F _ _ hτk q a rfl hqy hqt hQ, ← Category.assoc, hgen' F _ τ' hτ'k q' a' rfl hq'y hq't hQ']

  obtain ⟨O, φ, hφ, hφv⟩ := exists_dom_lemma_4 V F ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
  obtain ⟨τ'O, hτ'O, eO⟩ := unitsLift_lemma_3 F O D'.toPre.X k hk1 τ' hτ'k
  have hτO := powComp_lemma τ'O ρm k hτ'O

  obtain ⟨Ω', _, σ, c₀, hσ⟩ := exists_comp_lemma_5 V Ω (ResidueField O) b (fun x hx => hb x (by simpa using hx))
    ((residue O).comp φ) (fun x hx => (IsLocalRing.residue_eq_zero_iff _).mpr (map_nonunit φ x hx))
  let c : O →+* Ω' := c₀.comp (residue O)
  have hc : IsLocalHom c := ⟨fun x hx => by
    by_contra hne
    have h0 : residue O x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hne
    have h1 : c x = 0 := by simp only [c, RingHom.comp_apply, h0, map_zero]
    rw [h1] at hx
    exact not_isUnit_zero hx⟩
  have hcφ : c.comp φ = σ.comp b := hσ.symm

  obtain ⟨O₁, u, hu, hu'⟩ := exists_dom_lemma_4 V₁ Ω' (σ.comp α)
  have hwu : O₁.subtype.comp u = σ.comp α := RingHom.ext hu'
  let τ'Ω : Multiplicative D'.toPre.X →* Ω'ˣ := (Units.map c.toMonoidHom).comp τ'O
  have hτ'Ω : τ'Ω ^ k = 1 := powMap_lemma_2 _ τ'O k hτ'O
  have hτΩ := powComp_lemma τ'Ω ρm k hτ'Ω
  obtain ⟨τW, hτW, eW⟩ := unitsLift_lemma_3 Ω' O₁ D'.toPre.X k hk1 τ'Ω hτ'Ω
  have hτWR := powComp_lemma τW ρm k hτW
  obtain ⟨z, hz⟩ := GlobalTheory.ToricOverField.exists_point (A := V₁) u τW
  haveI := hj
  have hkW : IsUnit (k : O₁) := by simpa using hk.map (u.comp ψ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hloc := section_over_local R G hG D A U k s hpow hnat htor D'.toPre.X ρ V₁ ψ G₁ φ₁ hφ₁ j G₀ m₀ hm₀ h₀
    (m₀ ≫ φ₁) hm₀' rfl hpt O₁ u hu hkW τW (τW.comp ρm) hτWR hτW (fun χ => rfl) z hz
  have hfld := section_over_field V G' D' A' U' k s' htor' R G β V₁ G₁ φ₁ Ω α b hb GΩ n hn n' hn' j hpull hcomm
    Ω' σ (c.comp φ) hcφ O₁ u O₁.subtype hwu τW τ'Ω hτ'Ω (fun χ => by rw [← eW]; try rfl) z hz
  have hcomp : c.comp (φ.comp g) = O₁.subtype.comp (u.comp ψ) := by
    refine RingHom.ext fun r => ?_
    have h1 := congrArg (fun f => f (g r)) hcφ
    have h2 := congrArg (fun f => f r) hαψ
    have h3 := congrArg (fun f => f (ψ r)) hwu
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, ← h2, h3]
  have hx1 := hnat O₁ Ω' (u.comp ψ) (c.comp (φ.comp g)) O₁.subtype (τW.comp ρm) hτWR (τ'Ω.comp ρm) hτΩ hcomp
    (fun χ => by rw [← eW]; try rfl)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hβ (Over.mk (spMap φ)) (spMap (φ.comp g))
    (spMap_comp_ringHom' g φ)
  have hxy : s O (φ.comp g) (τ'O.comp ρm) hτO = e (s' O φ τ'O hτ'O) := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hsm O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' c hc ?_
    · rw [hpow O (φ.comp g) _ hτO, ← map_pow e, hpow' O φ τ'O hτ'O, map_one]
    · rw [he, ← hnat O Ω' (φ.comp g) (c.comp (φ.comp g)) c _ hτO _ hτΩ rfl (fun χ => rfl), ← Category.assoc,
        ← hnat' O Ω' φ (c.comp φ) c τ'O hτ'O τ'Ω hτ'Ω rfl (fun χ => rfl), hfld, hx1, hloc]
  have haR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [hF r]
    exact (hφv (g r)).symm
  have haV : (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) = O.subtype.comp φ :=
    RingHom.ext fun x => (hφv x).symm
  rw [hnat O F (φ.comp g) _ O.subtype _ hτO _ hτk haR (fun χ => by rw [← eO]; try rfl),
    hnat' O F φ _ O.subtype τ'O hτ'O τ' hτ'k haV (fun χ => by rw [← eO]; try rfl), hxy, he, Category.assoc]

end GlobalTheory.SpreadTorMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfTorMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem unifPre_generic {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) :
    IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧
      LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) := by
  have := U.gen_hom
  refine ⟨?_, ?_⟩
  · have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))) := U.ext
    have h1 : LBIso (A.L.pull (U.gen.inv.left ≫ U.gen.hom.left))
        (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (chartPullSame A.L _ (fun _ => U.gen.hom.left) _ U.gen.inv.left fun _ => rfl)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (chartPullUnpull A.L _ hgi)
      (chartPullSame U.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : B →+* C) (b : A →+* B) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem weilIs_congr_base {S X : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (k : ℤ) {a b : X ⟶ S}
    (hab : a = b) (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) : WeilIs G L k x y c ↔ WeilIs G L k x' y' c := by
  subst hab
  obtain rfl : x = x' := Over.OverMorphism.ext hx
  obtain rfl : y = y' := Over.OverMorphism.ext hy
  exact Iff.rfl

end GlobalTheory.GenRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.GenRestrict

theorem exists_genericPoints_equiv_any : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hDVR g hinj G' _ _ β h hG' D' A' U' hL F _ _ _ _ hc
  obtain ⟨gR, lR⟩ := unifPre_generic U.toUnifPre
  obtain ⟨gV, lV⟩ := unifPre_generic U'.toUnifPre
  have gVG : IsGrpPullback A'.A G (jK V ≫ spMap g) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β) :=
    gV.comp h
  have hcomp : jFK (R := V) F ≫ jK V ≫ spMap g = jFK (R := R) F ≫ jK R := by
    have e1 : (algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g) =
        (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) := RingHom.ext fun r => (hc r).symm
    calc jFK (R := V) F ≫ jK V ≫ spMap g
        = spMap ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g)) := by
          rw [spMap_comp_eq (algebraMap (FractionRing V) F), spMap_comp_eq (algebraMap V (FractionRing V)) g]
      _ = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) := by rw [e1]
      _ = jFK (R := R) F ≫ jK R := spMap_comp_eq _ _
  obtain ⟨eV, heV⟩ := GlobalTheory.LiePull.exists_pushEquiv gVG (TFK (R := V) F) (jFK (R := V) F ≫ jK V ≫ spMap g) rfl
  obtain ⟨eR, heR⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := V) F ≫ jK V ≫ spMap g) hcomp
  obtain ⟨eR₀, heR₀⟩ := GlobalTheory.LiePull.exists_pushEquiv gR (TFK (R := R) F) (jFK (R := R) F ≫ jK R) rfl
  have hlast : ∀ x, (eR.symm (eV x)).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := fun x => by
    rw [← heR, MulEquiv.apply_symm_apply, heV]
    simp only [Category.assoc]
  have lVG : LBIso A'.L (U.LG.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) lV
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull U'.LG.L _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => β) _ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) fun _ => rfl) hL)
  refine ⟨eV.trans eR.symm, fun k x y c hw => ?_, fun σ x x' hx => ?_, fun x => ?_⟩
  · have h1 := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A'.A _ _ U.LG.L A'.L U.LG.isLB A'.isLB gVG lVG
      (TFK (R := V) F) k x y (eV x) (eV y) (unitOn c) (heV x) (heV y)).1 hw
    have h2 := (weilIs_congr_base G U.LG.L k hcomp (eV x) (eV y) (eR₀ (eR.symm (eV x))) (eR₀ (eR.symm (eV y)))
      (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) (by rw [heR₀, ← heR, MulEquiv.apply_symm_apply]) _).1 h1
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ G A.A _ _ U.LG.L A.L U.LG.isLB A.isLB gR lR
      (TFK (R := R) F) k _ _ _ _ (unitOn c) (heR₀ _) (heR₀ _)).2 h2
  · have hσ : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, AlgHom.coe_toRingHom]
      rw [hc r]
      exact σ.commutes _
    refine gR.1.hom_ext ?_ ?_
    · simp only [MulEquiv.trans_apply, Category.assoc, hlast, hx]
    · rw [Over.w, Category.assoc, Over.w]
      show jFK (R := R) F = spMap σ.toRingHom ≫ jFK (R := R) F
      rw [← spMap_comp_eq, hσ]
  · exact hlast x

end GlobalTheory.GenRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericPointsUniformisationsWeilPairingGalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F],
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) →
      ∃ e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A),
        (∀ (k : ℕ) (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) ∧
        (∀ (σ : F →ₐ[FractionRing V] F) (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) ∧
        ∀ x : TFK (R := V) F ⟶ A'.A, (e x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) ≫ β := by
  first | exact @GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | exact GlobalTheory.GenRestrict.exists_genericPoints_equiv_any | (intros; apply GlobalTheory.GenRestrict.exists_genericPoints_equiv_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOrdSub
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

namespace GlobalTheory.TauFormGen

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues GlobalTheory.TauForm

theorem dvd_ord_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G')
  (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing V) F (gK x)) →
  ∀ (k : ℕ), IsUnit (k : R) → ∀ (ϖ : V), Irreducible ϖ → ∀ (O : ValuationSubring F) (φ : V →+* O) (σ : F →ₐ[FractionRing V] F) (π : F), IsLocalHom φ →
    (∀ w, (φ w : F) = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) → (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    π ^ k = algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ) → IsPrimitiveRoot (σ π / π) k →
  ∀ (ρ : D.toPre.X →+ D'.toPre.X) (e : (TFK (R := V) F ⟶ A'.A) ≃* (TFK (R := R) F ⟶ A.A)),
    (∀ (x y : TFK (R := V) F ⟶ A'.A) (c : Fˣ), WeilIs A'.A A'.L (k : ℤ) x y (unitOn c) → WeilIs A.A A.L (k : ℤ) (e x) (e y) (unitOn c)) →
    (∀ (x x' : TFK (R := V) F ⟶ A'.A), x'.left = spMap σ.toRingHom ≫ x.left → (e x').left = spMap σ.toRingHom ≫ (e x).left) →
    (∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ) (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a') →
  ∀ (a b : D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D'.toPre (ρ a) (ρ b) x' →
    (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' := by
  intro R _ _ _ hRb G _ _ hG D A U V _ _ _ _ hVb G' _ _ hG' D' A' U' g gK hgK F _ _ _ _ hF k hk ϖ hϖ O φ σ π hφ eφ hσ
    hπ hζ ρ e hW hGal hT a b x x' hx hx'
  obtain ⟨hR, _⟩ := hRb
  obtain ⟨hV, _⟩ := hVb
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  obtain ⟨f, ⟨i₁, s₁, -, a₁, w₁⟩, p₁⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, s₂, -, a₂, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV D' A' G' hG' U' F k hk1
  have wt₁ : ∀ (p p' : QkPt D.toPre F k) (τ : Multiplicative D.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A.A A.L (k : ℤ) (f p) (f p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₁ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have wt₂ : ∀ (p p' : QkPt D'.toPre F k) (τ : Multiplicative D'.toPre.X →* Fˣ), p.y = 0 → GlobalTheory.UT.IsTor τ p.g →
      WeilIs A'.A A'.L (k : ℤ) (f' p) (f' p') (unitOn (τ (Multiplicative.ofAdd p'.y))) := fun p p' τ hy hτ =>
    (w₂ p p' _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns p p' hy hτ)
  have c₁ : ∀ (σ : F →ₐ[FractionRing R] F) p p', QkExt σ.toRingHom p p' →
      (f p').left = spMap σ.toRingHom ≫ (f p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hR D A G hG U F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f p)
    have : y = f p' := (i₁ p' y).1 ((hiff p' (f p) y hpp' hy).1 ((i₁ p (f p)).2 rfl))
    rw [← this, hy]
  have c₂ : ∀ (σ : F →ₐ[FractionRing V] F) p p', QkExt σ.toRingHom p p' →
      (f' p').left = spMap σ.toRingHom ≫ (f' p).left := by
    intro σ p p' hpp'
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds V (maximalIdeal V) hV D' A' G' hG' U' F F σ k hk1 p
    obtain ⟨y, hy⟩ := hx (f' p)
    have : y = f' p' := (i₂ p' y).1 ((hiff p' (f' p) y hpp' hy).1 ((i₂ p (f' p)).2 rfl))
    rw [← this, hy]
  have uniq : ∀ (u v : TFK (R := R) F ⟶ A.A) (c c' : Fˣ), WeilIs A.A A.L (k : ℤ) u v (unitOn c) →
      WeilIs A.A A.L (k : ℤ) u v (unitOn c') → c = c' := fun u v c c' h h' =>
    GlobalTheory.weilIs_unique_fieldPoint _ A.A A.L A.isLB F _ k u v c c' h h'
  have tor : ∀ (τ' : Multiplicative D'.toPre.X →* Fˣ) (q' : QkPt D'.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt D.toPre F k,
      WeilIs A.A A.L (k : ℤ) (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') :=
      hT _ τ' q q' (f q) (f' q') h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)
    have hw := wt₁ q p (τ'.comp (AddMonoidHom.toMultiplicative ρ)) h₄ h₅
    rw [this] at hw
    exact hw
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    have h := hW _ _ _ (wt₂ q' p' τ' h₂ h₃)
    rw [← hp] at h
    exact uniq _ _ _ _ (tor τ' q' h₁ h₂ h₃ p) h

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.KummerConj.conj_eq_add_tor R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.KummerConj.conj_eq_add_tor V _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.InertiaFix.sigma_fixes_abelianPart V _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, hGal (f' p') (f' r') (c₂ σ p' r' hr'), ← hp])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) := by
    have h := tor τ₂ q₂ k₂ y₂ t₂ pb
    rw [← hq] at h
    exact uniq _ _ _ _ (wt₁ q₁ pb τ₁ y₁ t₁) h
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D'.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord V F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.TauShift.main V _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw V).map_mul, (ord_vw V).map_unit, (ord_vw V).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

end GlobalTheory.TauFormGen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorCoord

theorem coordMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∀ ρ, TorMatch U U' g β ρ → CoordMap D.toPre D'.toPre g ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hVb hV G' _ _ hG' D' A' U' g β hg hβ hL ρ hT
  haveI := hV
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap V (FractionRing V)).comp g) ((IsFractionRing.injective V (FractionRing V)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r) := IsFractionRing.lift_algebraMap _
  refine GlobalTheory.PsiFromTauEven.main R V hV g gK hgK D.toPre D'.toPre D.tau_bimult D.psi_even D'.tau_bimult D'.psi_even ρ ?_
  intro a b x x' hx hx'
  obtain ⟨⟨-, -, -, hVc⟩, hV0⟩ := id hVb
  haveI := hVc
  haveI := hV0
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let F := AlgebraicClosure (FractionRing V)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing V) F).comp gK).toAlgebra
  have hF : ∀ y, algebraMap (FractionRing R) F y = algebraMap (FractionRing V) F (gK y) := fun _ => rfl
  have hFr : ∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r)) :=
    fun r => (hF _).trans (congrArg _ (hgK r))
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_genericPoints_uniformisations_weilPairing_galois R hR G hG D A U V hVb hV g hg G' β hβ hG' D' A' U' hL F hFr
  have hm : ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative D.toPre.X →* Fˣ) (τ' : Multiplicative D'.toPre.X →* Fˣ)
      (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := V) F ⟶ A'.A),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
      q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g → QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a = e a' := by
    intro k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8
    have h := (hT F hFr k hk τ τ' q q' a a' h1 h2 h3 h4 h5 h6 h7 h8).trans (he3 a').symm
    simp only [genMap] at h
    have hs : ∀ z : TFK (R := R) F ⟶ A.A, z.left ≫ U.gen.inv.left ≫ pullback.snd G.hom (jK R) = (TFK (R := R) F).hom := by
      intro z
      have := Over.w U.gen.inv
      rw [← Over.w z, ← this]
      rfl
    have h' : a.left ≫ U.gen.inv.left = (e a').left ≫ U.gen.inv.left :=
      pullback.hom_ext (by simpa only [Category.assoc] using h) (by simpa only [Category.assoc] using (hs a).trans (hs (e a')).symm)
    ext1
    have hi : Mono U.gen.inv.left := inferInstance
    exact (cancel_mono _).1 h'
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x' :=
    fun k hk => by
      obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root V F ϖ hϖ k (by simpa using hk.map g)
      exact GlobalTheory.TauFormGen.dvd_ord_sub R hR G hG D A U V hVb G' hG' D' A' U' g gK hgK F hF k hk ϖ hϖ O φ σ π h₁ h₂ h₃ h₄ h₅ ρ e
        (he1 k) (he2 σ) (hm k hk) a b x x' hx hx'
  obtain ⟨u, hu⟩ := GlobalTheory.TauForm.exists_unit_of_ord_eq (W := V) (x := Units.map gK.toMonoidHom x) (y := x') (by
    rw [← sub_eq_zero]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
      ((GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun (Units.map gK.toMonoidHom x) - (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw V).toFun x'))
      (by simpa using hl.pow _)) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega))
  exact ⟨u, hu⟩

end GlobalTheory.Poinc.TorCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjectiveAlt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOntoSpread

theorem restrict_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → Function.Surjective ρ := by
  intro R _ _ _ _ G _ _ hG D A U V _ _ _ _ G' _ _ _ D' A' U' g β _ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, m₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψl, hm₁, hj, _, _, _, hΩ, h₀j⟩ := hsp
  haveI := hψl; haveI := hj
  have hG₁ : IsSemiAbelian G₁ := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ G G₁ m₁ hm₁ hG
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V₁) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V₁) 0 ≫ j := by
    haveI : IsSeparated G₁.hom := hG₁.separated
    have hjac : maximalIdeal V₁ ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V₁ (maximalIdeal V₁) hjac (splitTorus (Sp V₁) F) G₁ _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V₁ := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V₁ ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V₁).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V₁ →+* V₁ ⧸ maximalIdeal V₁ ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback G₁ (thick V₁ (maximalIdeal V₁) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V₁ ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V₁ (maximalIdeal V₁) e G₁) G (spMap (q.comp ψ))
        (pullback.fst G₁.hom (thick V₁ (maximalIdeal V₁) e) ≫ m₁) :=
      (he.comp hm₁).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha hR
    obtain ⟨ρe, hρe⟩ := hfac D'.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance
    have hres : ∀ x ∈ maximalIdeal V₁ ^ (e + 1), residue V₁ x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres hm₀
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V₁).comp ψ) x = 0 := fun x hx =>
      h₀ x (by rw [zero_add, pow_one]; exact Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus hm₀ j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he hm₀ (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres hm₀).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (U.gt e) ha' hm₀' :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V₁) hres) (U.gt e) ha ha' hR hm₀' ke
        (RingHom.ext fun x => rfl)
        (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst])
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha' hm₀'
    obtain ⟨u, hu⟩ := hfac' D.toPre.X (GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _ =
      pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :=
    (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U'.gt 0) hb hn').1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOntoSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvr
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.GenRestrict

theorem exists_surjective_coordMap_equivMap : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (p : ℕ), p.Prime → (p : R) ∈ maximalIdeal R → ∀ (Wo : Set (Sp R)), IsOpen Wo → (∀ y, PsiUnitOn D.toPre y Wo) → (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) ∈ Wo → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∃ ρ : D.toPre.X →+ D'.toPre.X, Function.Surjective ρ ∧ CoordMap D.toPre D'.toPre g ρ ∧ EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV hVd G' _ _ hG' D' A' U' g β p _ _ Wo hWo hψ hker gp hL
  obtain ⟨⟨hRN, -, -, hRA⟩, -⟩ := id hR
  obtain ⟨⟨-, -, hVI, -⟩, hV0⟩ := id hV
  obtain ⟨N, _, _, _, φ, g', hN, hφ, hg', hfac⟩ := GlobalTheory.FarTrait.exists_factor g
  obtain ⟨hNN, hNI, hNA, hN0⟩ := hN
  have hNb : GlobalTheory.Mum.Base N := ⟨⟨hNN, inferInstance, hNI, hNA⟩, hN0⟩
  have hsp : spMap g' ≫ spMap φ = spMap g := by
    rw [← Spec.map_comp]
    exact congrArg spMap (RingHom.ext hfac)
  have hgen : spMap φ (genericPoint (Sp N)) ∈ (⟨Wo, hWo⟩ : (Sp R).Opens) := by
    have e : spMap φ (genericPoint (Sp N)) = (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) := by
      rw [genericPoint_eq_bot_of_affine]
      refine PrimeSpectrum.ext (Ideal.ext fun r => ?_)
      change φ r ∈ (⊥ : Ideal N) ↔ r ∈ RingHom.ker g
      rw [Ideal.mem_bot, RingHom.mem_ker, ← hfac, map_eq_zero_iff g' hg']
    rw [e]
    exact hker
  have hG₂ : IsSemiAbelian ((Over.pullback (specOf φ)).obj G) := Geo.Tor.IsSemiAbelian.pullback _ G hG
  haveI : IsCommMonObj ((Over.pullback (specOf φ)).obj G) := hG₂.comm
  have hbc : IsMonHom (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom :=
    inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (specOf φ)).obj G)))
  obtain ⟨D₂, A₂, hD, U₂, hU⟩ := GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hR D A G hG U N hNb.1 φ hφ ⟨Wo, hWo⟩ hψ hgen
    ((Over.pullback (specOf φ)).obj G) (Iso.refl _) hbc
  obtain ⟨hL₁, hC₁, hE₁⟩ := PullUnif.main R hR G hG D A U N hNb _ hG₂ D₂ A₂ U₂ φ (pullback.fst G.hom (specOf φ)) hφ
    (Iso.refl _) hbc (Category.id_comp _).symm hD hU
  have sq : β ≫ G.hom = (G'.hom ≫ spMap g') ≫ specOf φ := by
    rw [Category.assoc, gp.1.w, ← hsp]
  let β₂ : G'.left ⟶ ((Over.pullback (specOf φ)).obj G).left := pullback.lift β (G'.hom ≫ spMap g') sq
  have hβ : β₂ ≫ pullback.fst G.hom (specOf φ) = β := pullback.lift_fst _ _ _
  have hβ' : β₂ ≫ pullback.snd G.hom (specOf φ) = G'.hom ≫ spMap g' := pullback.lift_snd _ _ _
  have gp₂ : IsGrpPullback G' ((Over.pullback (specOf φ)).obj G) (spMap g') β₂ :=
    (isGrpPullback_pullback G (specOf φ)).cancel (gp.congr hsp.symm hβ.symm) hβ'
  have hL₂ : LBIso U'.LG.L (U₂.LG.L.pull β₂) :=
    LBIso.trans U'.LG.isLB (LB.isLB_pull U.LG.isLB _) (LB.isLB_pull U₂.LG.isLB _) hL
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hL₁ β₂ hβ.symm).symm
  obtain ⟨ρ, hρ⟩ := GlobalTheory.SpreadTrait.exists_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂
  have hs := GlobalTheory.TorusOntoSpread.restrict_surjective N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hT := GlobalTheory.SpreadTorMatch.torMatch_of_spread N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ gp₂ ρ hρ
  have hC₂ := TorCoord.coordMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV hVd G' hG' D' A' U' g' β₂ hg' gp₂ hL₂ ρ hT
  have hE₂ := equivMap_of_torMatch N hNb _ hG₂ D₂ A₂ U₂ V hV G' hG' D' A' U' g' β₂ hg' ρ hT
  refine ⟨ρ.comp hD.xe.symm.toAddMonoidHom, hs.comp hD.xe.symm.surjective, fun y r r' hr hr' => ?_,
    fun f f' hf hf' hff m m' hm hm' y => ?_⟩
  · obtain ⟨r₂, hr₂⟩ := GlobalTheory.BetaAdd.exists_coord D₂ (hD.xe.symm.toAddMonoidHom y)
    rw [← hfac]
    exact ((hC₁ y r r₂ hr hr₂).map g').trans (hC₂ _ r₂ r' hr₂ hr')
  · have hf₂ : IsMonHom ((Over.pullback (specOf φ)).map f) := inferInstance
    have e₁ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst G.hom (specOf φ) =
        pullback.fst G.hom (specOf φ) ≫ f.left := pullback.lift_fst _ _ _
    have e₂ : ((Over.pullback (specOf φ)).map f).left ≫ pullback.snd G.hom (specOf φ) =
        pullback.snd G.hom (specOf φ) := Over.w ((Over.pullback (specOf φ)).map f)
    have e₃ : f'.left ≫ β₂ = β₂ ≫ ((Over.pullback (specOf φ)).map f).left := by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₁, hβ, ← Category.assoc, hβ, hff]
      · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        erw [e₂, hβ', ← Category.assoc, Over.w f']
    obtain ⟨m₂, hm₂⟩ := endChar_exists_of_isMonHom N hNb _ hG₂ D₂ A₂ U₂ _ hf₂
    have h₁ := hE₁ f _ hf hf₂ e₁ m m₂ hm hm₂ y
    exact (congrArg ρ h₁).trans (hE₂ _ f' hf₂ hf' e₃ m₂ m' hm₂ hm' _)

end GlobalTheory.Poinc.Eq8.GenRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left) (p : ℕ), p.Prime → (p : R) ∈ maximalIdeal R → ∀ (Wo : Set (Sp R)), IsOpen Wo → (∀ y, PsiUnitOn D.toPre y Wo) → (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum R) ∈ Wo → IsGrpPullback G' G (spMap g) β → LBIso U'.LG.L (U.LG.L.pull β) → ∃ ρ : D.toPre.X →+ D'.toPre.X, Function.Surjective ρ ∧ CoordMap D.toPre D'.toPre g ρ ∧ EquivMap U U' β ρ := by
  first | exact @GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap | exact GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap | (intros; apply GlobalTheory.Poinc.Eq8.GenRestrict.exists_surjective_coordMap_equivMap <;> assumption)
end
