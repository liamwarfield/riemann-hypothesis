module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAmpleKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrinThicken

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem evc_comm {S : Scheme.{0}} {X Y : Over S} {M : LB (X ⊗ X).left} (hM : M.IsLB)
    (hc : cls M hM = CechPic.pull (lift (snd X X) (fst X X)).left (cls M hM)) (a b : Y ⟶ X) :
    evc hM a b = evc hM b a := by
  rw [evc, evc]
  conv_lhs => rw [hc]
  rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]

end GlobalTheory.PrinThicken
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulUnramified

lemma eq_one_of_pow_eq_one_thick_affine (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (G : Over (Sp C)) [GrpObj G] (n : ℕ)
    (hn : IsUnit (n : C)) (R : CommRingCat.{0}) (g : Spec R ⟶ Sp C) (z : Over.mk g ⟶ G)
    (hz : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g), j ≫ z = 1)
    (hzn : z ^ n = 1) : z = 1 := by
  let φ : CommRingCat.of C ⟶ R := Spec.preimage g
  let K : Ideal C := RingHom.ker π
  let J : Ideal R := Ideal.map φ.hom K
  let q : R →+* R ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* R ⧸ J :=
    (Ideal.quotientMap J φ.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ∀ c, ψ (π c) = q (φ c) := by
    intro c
    have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk K c := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  have hJ : RingHom.ker q = J := Ideal.mk_ker
  have hJsq : J ^ 2 = ⊥ := by
    simp only [J, ← Ideal.map_pow]
    change Ideal.map φ.hom (RingHom.ker π ^ 2) = ⊥
    rw [hsq, Ideal.zero_eq_bot, Ideal.map_bot]
  let T₀ : Over (Sp C₀) := Over.mk (spMap ψ)
  have hw : Spec.map (CommRingCat.ofHom q) ≫ g = T₀.hom ≫ spMap π := by
    rw [← Spec.map_preimage g]
    simp only [T₀, spMap, Over.mk_hom, ← Spec.map_comp]
    congr 1
    ext c
    exact (hψ c).symm
  let j : Over.mk (T₀.hom ≫ spMap π) ⟶ Over.mk g := Over.homMk (Spec.map (CommRingCat.ofHom q)) hw
  have hsurj : Function.Surjective j.left := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker q ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hJ, hJsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have hker : RingHom.ker (CommRingCat.ofHom q).hom ^ 2 = ⊥ := by
    change RingHom.ker q ^ 2 = ⊥
    rw [hJ, hJsq]
  have hn' : IsUnit (n : Γ(Sp C, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  exact eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq (CommRingCat.ofHom q) hker) n hn' z
    (hz T₀ j) hzn

end GlobalTheory.MulUnramified

namespace GlobalTheory.MulUnramified

theorem eq_one_of_pow_eq_one_thick : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  intro C C₀ _ _ π hπ hsq G _ n hn T z hz hzn
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i ↦ ?_
  let k : T.left.affineOpenCover.I₀ := i
  let f : Over.mk (T.left.affineOpenCover.f k ≫ T.hom) ⟶ T := Over.homMk (T.left.affineOpenCover.f k) rfl
  have hfz : (f ≫ z) ^ n = 1 := by
    rw [← MonObj.comp_pow, hzn, comp_one]
  have h := eq_one_of_pow_eq_one_thick_affine C C₀ π hπ hsq G n hn _ _ (f ≫ z)
    (fun T₀ j ↦ by rw [← Category.assoc]; exact hz T₀ _) hfz
  have h' := congrArg (·.left) (h.trans (comp_one f).symm)
  simp only [Over.comp_left] at h'
  exact h'

end GlobalTheory.MulUnramified
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  first | (exact @GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (exact GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (intros; apply GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAgree

open GlobalTheory.MulUnramified

variable {C C₀ : Type} [CommRing C] [CommRing C₀] (π : C →+* C₀)

lemma spMap_surjective (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) :
    Function.Surjective (spMap π) := by
  intro (p : PrimeSpectrum C)
  change p ∈ Set.range (PrimeSpectrum.comap π)
  rw [range_comap_of_surjective _ _ hπ, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  refine p.isPrime.mem_of_pow_mem 2 ?_
  have : a ^ 2 ∈ RingHom.ker π ^ 2 := Ideal.pow_mem_pow ha 2
  rw [hsq, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  rw [this]
  exact zero_mem _

lemma preimage_eq_of_agree (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    (V : Y.left.Opens) : f.left ⁻¹ᵁ V = f'.left ⁻¹ᵁ V := by
  have hs : Surjective (spMap π) := ⟨spMap_surjective π hπ hsq⟩
  have hf : Surjective (pullback.fst X.hom (spMap π)) := inferInstance
  have e := congrArg (·.left) (h (Over.mk (pullback.snd X.hom (spMap π)))
    (Over.homMk (pullback.fst X.hom (spMap π)) pullback.condition))
  simp only [Over.comp_left, Over.homMk_left] at e
  exact preimage_eq _ hf.surj e V

noncomputable def alg (X : Over (Sp C)) (V : X.left.Opens) : C →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of C)).inv ≫ X.hom.appLE ⊤ V le_top).hom

lemma fromSpec_over (X : Over (Sp C)) {V : X.left.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ X.hom = spMap (alg X V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom (isAffineOpen_top (Spec (CommRingCat.of C))) hV
    (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, alg, spMap, CommRingCat.ofHom_hom, Spec.map_comp]

lemma appLE_alg {X Y : Over (Sp C)} (f : X ⟶ Y) (V : Y.left.Opens) (V' : X.left.Opens)
    (hf : V' ≤ f.left ⁻¹ᵁ V) (c : C) : f.left.appLE V V' hf (alg Y V c) = alg X V' c := by
  simp only [alg, CommRingCat.hom_comp, RingHom.comp_apply]
  exact comp_appLE_apply f.left Y.hom (Over.w f) _ _ _ _ _ _ _

lemma sub_mem (hπ : Function.Surjective π) {X Y : Over (Sp C)} {f f' : X ⟶ Y}
    (h : ∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ X), y ≫ f = y ≫ f')
    {V : Y.left.Opens} (hV : IsAffineOpen V) {V' : X.left.Opens} (hV' : IsAffineOpen V')
    (hf : V' ≤ f.left ⁻¹ᵁ V) (hf' : V' ≤ f'.left ⁻¹ᵁ V) (s : Γ(Y.left, V)) :
    f.left.appLE V V' hf s - f'.left.appLE V V' hf' s ∈ (RingHom.ker π).map (alg X V') := by
  set J := (RingHom.ker π).map (alg X V')
  let q : Γ(X.left, V') →+* Γ(X.left, V') ⧸ J := Ideal.Quotient.mk J
  let ψ : C₀ →+* Γ(X.left, V') ⧸ J :=
    (Ideal.quotientMap J (alg X V') Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hψ : ψ.comp π = q.comp (alg X V') := by
    ext c
    have e : (RingHom.quotientKerEquivOfSurjective hπ).symm (π c) = Ideal.Quotient.mk _ c :=
      (RingEquiv.symm_apply_eq _).mpr rfl
    simp only [ψ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      Ideal.quotientMap_mk]
  let y : Over.mk ((Over.mk (spMap ψ)).hom ≫ spMap π) ⟶ X :=
    Over.homMk (spMap q ≫ hV'.fromSpec) (by
      rw [Category.assoc, fromSpec_over]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])
  have e := congrArg (·.left) (h (Over.mk (spMap ψ)) y)
  simp only [y, Over.comp_left, Over.homMk_left, Category.assoc] at e
  rw [← hV.SpecMap_appLE_fromSpec f.left hV' hf, ← hV.SpecMap_appLE_fromSpec f'.left hV' hf',
    ← Category.assoc, ← Category.assoc, cancel_mono, spMap, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at e
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact congr($e s)

lemma eq_on_map {B R : Type} [CommRing B] [CommRing R] (I : Ideal C) (hI : I ^ 2 = 0)
    (φB : C →+* B) (φR : C →+* R) (β β' : B →+* R) (hβ : β.comp φB = φR) (hβ' : β'.comp φB = φR)
    (hd : ∀ b, β b - β' b ∈ I.map φR) {x : B} (hx : x ∈ I.map φB) : β x = β' x := by
  have hJ : I.map φR * I.map φR = ⊥ := by
    rw [← Ideal.map_mul, ← pow_two, hI, Submodule.zero_eq_bot, Ideal.map_bot]
  suffices β x = β' x ∧ β x ∈ I.map φR from this.1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    rw [← RingHom.comp_apply β, hβ, ← RingHom.comp_apply β', hβ']
    exact ⟨rfl, Ideal.mem_map_of_mem _ hc⟩
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by simp only [map_add, hx.1, hy.1], by simpa only [map_add] using add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [smul_eq_mul, map_mul, map_mul, ← hx.1, ← sub_eq_zero, ← sub_mul, ← Ideal.mem_bot, ← hJ]
      exact Ideal.mul_mem_mul (hd a) hx.2
    · rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hx.2

end GlobalTheory.SqZeroAgree

namespace GlobalTheory


open MulUnramified SqZeroAgree in
theorem comp_eq_of_sqZero_agree : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G),
    (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') →
    ∀ (T : Over (Sp C)) (w w' : T ⟶ K),
    (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') →
    w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  intro C C₀ _ _ π hπ hsq K G g g' hg T w w' hw h'
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.left (w.left t))) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ g.left ⁻¹ᵁ V⟩ :=
    K.left.isBasis_affineOpens.exists_subset_of_mem_open (a := w.left t) (u := g.left ⁻¹ᵁ V) htV
      (TopologicalSpace.Opens.isOpen _)
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hWV' : W ≤ w.left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t) (u := w.left ⁻¹ᵁ V') htV'
      (TopologicalSpace.Opens.isOpen _)
  have hV'V₂ : V' ≤ g'.left ⁻¹ᵁ V := preimage_eq_of_agree π hπ hsq hg V ▸ hV'V
  have hWV'₂ : W ≤ w'.left ⁻¹ᵁ V' := preimage_eq_of_agree π hπ hsq hw V' ▸ hWV'
  refine ⟨W, htW, ?_⟩
  have key : ∀ s, w.left.appLE V' W hWV' (g.left.appLE V V' hV'V s) =
      w.left.appLE V' W hWV' (g'.left.appLE V V' hV'V₂ s) := by
    intro s
    have hx := sub_mem π hπ hg hV hV' hV'V hV'V₂ s
    have e := eq_on_map (RingHom.ker π) hsq (alg K V') (alg T W) (w.left.appLE V' W hWV').hom
      (w'.left.appLE V' W hWV'₂).hom (RingHom.ext (appLE_alg w V' W hWV'))
      (RingHom.ext (appLE_alg w' V' W hWV'₂)) (sub_mem π hπ hw hV' hW hWV' hWV'₂) hx
    have e' : w'.left.appLE V' W hWV'₂ (g.left.appLE V V' hV'V s) =
        w'.left.appLE V' W hWV'₂ (g'.left.appLE V V' hV'V₂ s) := by
      rw [comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V hWV'₂),
        comp_appLE_apply _ _ rfl _ _ _ _ _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
      have hh : w'.left ≫ g.left = w'.left ≫ g'.left := by rw [← Over.comp_left, h', Over.comp_left]
      rw [appLE_congr hh V W _ (le_preimage_of_comp _ _ hV'V₂ hWV'₂)]
    simp only [map_sub] at e
    rw [← sub_eq_zero, ← sub_eq_zero.mpr e, e', sub_self, sub_zero]
  have fin : (w.left ≫ g.left).appLE V W (le_preimage_of_comp _ _ hV'V hWV') =
      (w.left ≫ g'.left).appLE V W (le_preimage_of_comp _ _ hV'V₂ hWV') := by
    ext s
    rw [← comp_appLE_apply _ _ rfl _ _ _ hV'V hWV', ← comp_appLE_apply _ _ rfl _ _ _ hV'V₂ hWV']
    exact key s
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec _ hW (le_preimage_of_comp _ _ hV'V hWV'), fin,
    hV.SpecMap_appLE_fromSpec _ hW]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_eq_of_sqZero_agree_pairs : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (K G : Over (Sp C)) (g g' : K ⟶ G), (∀ (T₀ : Over (Sp C₀)) (y : Over.mk (T₀.hom ≫ spMap π) ⟶ K), y ≫ g = y ≫ g') → ∀ (T : Over (Sp C)) (w w' : T ⟶ K), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ w = j ≫ w') → w' ≫ g = w' ≫ g' → w ≫ g = w ≫ g' := by
  first | (exact @GlobalTheory.comp_eq_of_sqZero_agree) | (exact GlobalTheory.comp_eq_of_sqZero_agree) | (intros; apply GlobalTheory.comp_eq_of_sqZero_agree  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerLiftUnit


open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.PrinThicken in
theorem ker_pow_eq_one_of_lift : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ A _ _ i hi hA l hl P₀ P hP₀ hP r₁ r₂ hsymm amp hred e he ker₀
  have csymm : cls P hP = GlobalTheory.CechPic.pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsymm
  have wS : (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l = l ≫ (lift (snd A A) (fst A A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hl.1, GlobalTheory.AbDual.lift_left_fst_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_fst, hl.2]
    · rw [Category.assoc, hl.2, GlobalTheory.AbDual.lift_left_snd_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_snd, hl.1]
  have c₀symm : cls P₀ hP₀ = GlobalTheory.CechPic.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left (cls P₀ hP₀) := by
    have e := (cls_eq_iff (pull_isLB hP l) hP₀).2 hred
    rw [cls_pull hP] at e
    rw [← e, ← pull_comp, wS, pull_comp, ← csymm]
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := GlobalTheory.abelianDualCrystal.1 _ A hA
  obtain ⟨lam, hlam, hiff⟩ := GlobalTheory.PoincarePull.exists_hom_triv_iff C A hA D Q q q' _ (pull_isLB hP _) amp P hP r₁ r₂
  haveI := hlam
  have hiff' : ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ≫ lam = 1 := fun T x hx ↦
    (hiff T x).1 ((triv_ev_iff hP _ _).2 ((evc_comm hP csymm _ _).trans ((triv_ev_iff hP _ _).1 hx)))
  have tors₀ : ∀ (T₀ : Over (Sp C₀)) (z : Over.mk (T₀.hom ≫ spMap π) ⟶ A), z ≫ lam = 1 → z ^ e = 1 := by
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ A₀ := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have k₁ : z₀ ^ e = 1 := ker₀ _ z₀ (by
      have e1 := evc_trR hi hi hl.1 hl.2 hP hP₀ hred (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff _ z).2 hz)
      rw [show pushP hi (s := T₀.hom) rfl z₀ = z from Over.OverMorphism.ext hz₀] at e1
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (GlobalTheory.CechPic.pull s) (e1.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP₀ _ _).2 ((evc_comm hP₀ c₀symm _ _).symm.trans e2))
    have hp : ∀ m : ℕ, (z₀ ^ m).left ≫ i = (z ^ m).left := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact one_left_comp hi (s := T₀.hom) rfl
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact mul_left_comp hi (s := T₀.hom) rfl ih hz₀
    apply Over.OverMorphism.ext
    rw [← hp e, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  intro T x hx
  have hx0 : x ≫ lam = 1 := hiff' T x hx
  have hw0 : (x ^ e) ≫ lam = 1 := by rw [pow_comp, hx0, one_pow]
  have hwC : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ (x ^ e) = 1 := fun T₀ j ↦ by
    rw [comp_pow]
    exact tors₀ T₀ (j ≫ x) (by rw [Category.assoc, hx0, MonObj.comp_one])
  let k := equalizer.ι lam (1 : A ⟶ D)
  have hk : k ≫ lam = 1 := by rw [equalizer.condition, MonObj.comp_one]
  let u : 𝟙_ (Over (Sp C)) ⟶ equalizer lam (1 : A ⟶ D) :=
    equalizer.lift 1 (by rw [MonObj.one_comp, MonObj.comp_one])
  have hww : (x ^ e) ^ e = 1 := by
    have h1 := GlobalTheory.T.comp_eq_of_sqZero_agree_pairs C C₀ π hπ hsq (equalizer lam (1 : A ⟶ D)) A (k ^ e) 1
      (fun T₀ y ↦ by
        rw [comp_pow, MonObj.comp_one]
        exact tors₀ T₀ (y ≫ k) (by rw [Category.assoc, hk, MonObj.comp_one]))
      T (equalizer.lift (x ^ e) (by rw [hw0, MonObj.comp_one])) (toUnit T ≫ u)
      (fun T₀ j ↦ by
        rw [← cancel_mono k, Category.assoc, Category.assoc, Category.assoc,
          show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _,
          show u ≫ k = 1 from equalizer.lift_ι _ _, hwC, MonObj.comp_one, MonObj.comp_one])
      (by rw [comp_pow, MonObj.comp_one, Category.assoc, show u ≫ k = 1 from equalizer.lift_ι _ _,
        MonObj.comp_one, one_pow])
    rw [comp_pow, show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _, MonObj.comp_one] at h1
    exact h1
  exact GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial C C₀ π hπ hsq A e he T (x ^ e) hwC hww

end GlobalTheory.KerLiftUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedPolarisationKernelKilledOfUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifted_polarisation_kernel_killed_of_unit : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift | exact GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift | (intros; apply GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift <;> assumption)
end
