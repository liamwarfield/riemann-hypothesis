module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFormallyUnramifiedGrpEnd
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace UnramifiedEndFlat

open IsLocalRing

theorem flat_of_map_maximalIdeal_self {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : A →+* A) (hm : (maximalIdeal A).map φ = maximalIdeal A)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal A) : φ.Flat := by
  have hle : maximalIdeal A ≤ (maximalIdeal A).comap φ := Ideal.le_comap_of_map_le hm.le
  refine flat_of_surjective_quotient_sq (maximalIdeal_le_jacobson _) hle h₀ fun y hy => ?_
  rw [← hm, Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a + b, add_mem ha hb, ?_⟩
    rw [show φ (a + b) - (y + z) = (φ a - y) + (φ b - z) by rw [map_add (f := _)]; ring]
    exact add_mem hay hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨d, hd⟩ := h₀ c
    refine ⟨d * a, Ideal.mul_mem_left _ _ ha, ?_⟩
    rw [show φ (d * a) - c • y = (φ d - c) * φ a + c * (φ a - y) by
      rw [map_mul, smul_eq_mul]; ring]
    refine add_mem ?_ (Ideal.mul_mem_left _ _ hay)
    rw [pow_two]
    exact Ideal.mul_mem_mul hd (hle ha)

theorem flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] (e : B ≃+* A)
    (φ : A →+* B) (hm : (maximalIdeal A).map φ = maximalIdeal B)
    (h₀ : ∀ b, ∃ a, φ a - b ∈ maximalIdeal B) : φ.Flat := by
  have he : (maximalIdeal B).map (e : B →+* A) = maximalIdeal A :=
    map_maximalIdeal_of_surjective _ e.surjective
  have h : ((e : B →+* A).comp φ).Flat := by
    refine flat_of_map_maximalIdeal_self _ (by rw [← Ideal.map_map, hm, he]) fun b => ?_
    obtain ⟨a, ha⟩ := h₀ (e.symm b)
    refine ⟨a, ?_⟩
    have := Ideal.mem_map_of_mem (e : B →+* A) ha
    rw [he] at this
    simpa using this
  have := h.comp (RingHom.Flat.of_bijective (f := (e.symm : A →+* B)) e.symm.bijective)
  convert this
  ext x
  simp

theorem flat_iff_comp_germ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) {C : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ C) :
    g.hom.Flat ↔ (X.presheaf.germ U x hx ≫ g).hom.Flat := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  letI := g.hom.toAlgebra
  letI := (X.presheaf.germ U x hx ≫ g).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) C := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.flat_iff_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl C

theorem flat_stalkSpecializes {X : Scheme.{0}} {x x' : X} (h : x ⤳ x') :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  rw [flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _

theorem flat_stalkMap_of_specializes {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have h' : f x ⤳ f x' := h.map f.continuous
  rw [flat_iff_comp_germ hU (h'.mem_open U.2 hx'),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']
  exact hf.comp (flat_stalkSpecializes h)

theorem flat_of_closedPoints {X Y : Scheme.{0}} [JacobsonSpace X] (f : X ⟶ Y)
    (hf : ∀ x : X, IsClosed {x} → (f.stalkMap x).hom.Flat) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  exact flat_stalkMap_of_specializes f (specializes_iff_mem_closure.mpr hy) (hf y hyc)

theorem residueFieldMap_surjective {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ g)] (x : X)
    (hx : IsClosed {x}) : Function.Surjective (f.residueFieldMap x) := by
  have h : (residueFieldIsoBase (f ≫ g) x hx).inv =
      Spec.preimage (Y.fromSpecResidueField (f x) ≫ g) ≫ f.residueFieldMap x := by
    apply Spec.map_injective
    simp
  have h2 : Function.Surjective (residueFieldIsoBase (f ≫ g) x hx).inv :=
    (ConcreteCategory.bijective_of_isIso _).2
  rw [h] at h2
  exact Function.Surjective.of_comp (g := Spec.preimage (Y.fromSpecResidueField (f x) ≫ g)) h2

theorem flat_stalkMap_of_fixed {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (f : X ⟶ X) (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (hfg : f ≫ g = g)
    [FormallyUnramified f] (x : X) (hx : IsClosed {x}) (hfx : f x = x) :
    (f.stalkMap x).hom.Flat := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (f ≫ g) := by rw [hfg]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have h1 := FormallyUnramified.stalkMap f x
  have h2 := LocallyOfFiniteType.stalkMap f x
  refine flat_of_map_maximalIdeal
    (X.presheaf.stalkCongr (Inseparable.of_eq hfx.symm)).commRingCatIsoToRingEquiv _ ?_ fun b => ?_
  · algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact Algebra.FormallyUnramified.map_maximalIdeal
  · obtain ⟨a, ha⟩ := residueFieldMap_surjective f g x hx (X.residue x b)
    obtain ⟨a, rfl⟩ := X.residue_surjective (f x) a
    refine ⟨a, Ideal.Quotient.eq.mp ?_⟩
    exact ha

end UnramifiedEndFlat


open UnramifiedEndFlat in
theorem flat_of_formallyUnramified_grpEnd (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k))
    [GrpObj G] (φ : G ⟶ G) (hG : LocallyOfFiniteType G.hom) (hφ : IsMonHom φ)
    (hu : FormallyUnramified φ.left) : Flat φ.left := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  refine UnramifiedEndFlat.flat_of_closedPoints _ fun x hx => ?_
  let x' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨x, hx⟩).2
  let o : G.left := η[G].left (IsLocalRing.closedPoint k)
  have ho : IsClosed {o} := (pointEquivClosedPoint G.hom ⟨η[G].left, η[G].w⟩).2
  have hfo : φ.left o = o := by
    have : η[G] ≫ φ = η[G] := IsMonHom.one_hom φ
    exact congr(($this).left (IsLocalRing.closedPoint k))
  have h0 := UnramifiedEndFlat.flat_stalkMap_of_fixed φ.left G.hom φ.w o ho hfo
  let α := GrpObj.mulRight (A := G) x'
  let β := GrpObj.mulRight (A := G) (x' ≫ φ)
  have hαβ : α.hom ≫ φ = φ ≫ β.hom := by
    simp [α, β, comp_lift_assoc]
  have hα : η[G] ≫ α.hom = x' := by
    simpa [α, comp_lift_assoc] using lift_comp_one_left (𝟙 (𝟙_ (Over (Sp k)))) x'
  have hα' : α.hom.left o = x :=
    (congr(($hα).left (IsLocalRing.closedPoint k))).trans (pointOfClosedPoint_apply G.hom x hx _)
  have : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map β.hom))
  have h1 : ((φ.left ≫ β.hom.left).stalkMap o).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (Flat.stalkMap β.hom.left _).comp h0
  rw [← Over.comp_left, ← hαβ, Over.comp_left, Scheme.Hom.stalkMap_comp] at h1
  rw [← hα']
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (φ.left.stalkMap (α.hom.left o)) (α.hom.left.stalkMap o)).mp h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FormallyUnramifiedMulN
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MulUnramified

def affineComb {A R : Type} [CommRing A] [CommRing R] (a b c : A →+* R)
    (h : ∀ s t, (a s - c s) * (b t - c t) = 0) : A →+* R where
  toFun s := a s + b s - c s
  map_one' := by simp
  map_zero' := by simp
  map_add' s t := by simp only [map_add (f := _)]; ring
  map_mul' s t := by
    simp only [map_mul]
    linear_combination - h s t - h t s

lemma appLE_congr {T X : Scheme.{0}} {f g : T ⟶ X} (h : f = g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) : f.appLE V W hf = g.appLE V W hg := by
  subst h; rfl

lemma preimage_eq {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) (hi : Function.Surjective i) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by
  ext x
  obtain ⟨x, rfl⟩ := hi x
  have : f (i x) = g (i x) := congr($h x)
  simp [this]

lemma app_sub_eq_zero {T₀ T X : Scheme.{0}} (i : T₀ ⟶ T) {f g : T ⟶ X}
    (h : i ≫ f = i ≫ g) (V : X.Opens) (W : T.Opens)
    (hf : W ≤ f ⁻¹ᵁ V) (hg : W ≤ g ⁻¹ᵁ V) (s : Γ(X, V)) :
    i.app W (f.appLE V W hf s - g.appLE V W hg s) = 0 := by
  rw [map_sub, sub_eq_zero, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr h]

lemma comp_appLE_apply {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X) {x : T ⟶ X} (h : a ≫ p = x)
    (V : X.Opens) (V' : P.Opens) (W : T.Opens) (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V')
    (h₃ : W ≤ x ⁻¹ᵁ V) (s : Γ(X, V)) :
    a.appLE V' W h₂ (p.appLE V V' h₁ s) = x.appLE V W h₃ s := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_congr h]

lemma le_preimage_of_comp {T P X : Scheme.{0}} (a : T ⟶ P) (p : P ⟶ X)
    {V : X.Opens} {V' : P.Opens} {W : T.Opens} (h₁ : V' ≤ p ⁻¹ᵁ V) (h₂ : W ≤ a ⁻¹ᵁ V') :
    W ≤ (a ≫ p) ⁻¹ᵁ V := fun _ hx ↦ h₁ (h₂ hx)

lemma parallelogram {T P X : Scheme.{0}} (p q : P ⟶ X)
    (hpq : ∀ (Z : Scheme.{0}) (u v : Z ⟶ P), u ≫ p = v ≫ p → u ≫ q = v ≫ q → u = v)
    (a b c d : T ⟶ P) (hap : a ≫ p = d ≫ p) (hbp : b ≫ p = c ≫ p)
    (haq : a ≫ q = c ≫ q) (hbq : b ≫ q = d ≫ q)
    {V : X.Opens} (hV : IsAffineOpen V) {V' : P.Opens} (hV' : IsAffineOpen V')
    {W : T.Opens} (hW : IsAffineOpen W) (hp : V' ≤ p ⁻¹ᵁ V) (hq : V' ≤ q ⁻¹ᵁ V)
    (ha : W ≤ a ⁻¹ᵁ V') (hb : W ≤ b ⁻¹ᵁ V') (hc : W ≤ c ⁻¹ᵁ V') (hd : W ≤ d ⁻¹ᵁ V')
    (h : ∀ s t, (a.appLE V' W ha s - c.appLE V' W hc s) *
      (b.appLE V' W hb t - c.appLE V' W hc t) = 0) (s : Γ(P, V')) :
    d.appLE V' W hd s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := by
  let φ : Γ(P, V') ⟶ Γ(T, W) :=
    CommRingCat.ofHom (affineComb (a.appLE V' W ha).hom (b.appLE V' W hb).hom (c.appLE V' W hc).hom h)
  have hφ : ∀ s, φ s = a.appLE V' W ha s + b.appLE V' W hb s - c.appLE V' W hc s := fun _ ↦ rfl
  have key : Spec.map (d.appLE V' W hd) ≫ hV'.fromSpec = Spec.map φ ≫ hV'.fromSpec := by
    apply hpq
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec p hV' hp,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a p hap _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply d p rfl _ _ _ _ _ (le_preimage_of_comp d p hp hd),
        comp_appLE_apply b p hbp _ _ _ _ _ (le_preimage_of_comp c p hp hc),
        comp_appLE_apply c p rfl _ _ _ _ _ (le_preimage_of_comp c p hp hc)]
      ring
    · rw [Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec q hV' hq,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext s
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      rw [hφ, comp_appLE_apply a q haq _ _ _ _ _ (le_preimage_of_comp c q hq hc),
        comp_appLE_apply d q rfl _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply b q hbq _ _ _ _ _ (le_preimage_of_comp d q hq hd),
        comp_appLE_apply c q rfl _ _ _ _ _ (le_preimage_of_comp c q hq hc)]
      ring
  rw [cancel_mono, Spec.map_inj] at key
  rw [key, hφ]

variable {S : Scheme.{0}}

lemma comp_mulN (G : Over S) [GrpObj G] {T : Over S} (x : T ⟶ G) (n : ℕ) :
    x ≫ mulN G n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [mulN, pow_succ, Hom.mul_def, ← ih, comp_lift_assoc, Category.comp_id]

lemma eq_one_of_pow_eq_one (G : Over S) [GrpObj G] {T₀ T : Over S} (j : T₀ ⟶ T)
    (hj : Function.Surjective j.left)
    (hsq : ∀ (W : T.left.Opens), IsAffineOpen W → ∀ s t : Γ(T.left, W),
      j.left.app W s = 0 → j.left.app W t = 0 → s * t = 0)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (z : T ⟶ G) (hz : j ≫ z = 1) (hzn : z ^ n = 1) :
    z = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  let e : T ⟶ G := 1
  have he : j ≫ e = 1 := by simp [e]
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e.left t)) isOpen_univ
  have hcp : (lift e e).left ≫ (fst G G).left = e.left := by rw [← Over.comp_left, lift_fst]
  have hcq : (lift e e).left ≫ (snd G G).left = e.left := by rw [← Over.comp_left, lift_snd]
  have hcm : (lift e e).left ≫ (μ[G]).left = e.left := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one]
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ _⟩ :=
    (G ⊗ G).left.isBasis_affineOpens.exists_subset_of_mem_open (a := (lift e e).left t)
      (u := ((fst G G).left ⁻¹ᵁ V ⊓ (snd G G).left ⁻¹ᵁ V ⊓ (μ[G]).left ⁻¹ᵁ V : (G ⊗ G).left.Opens))
      ⟨⟨show ((lift e e).left ≫ (fst G G).left) t ∈ V by rwa [hcp],
        show ((lift e e).left ≫ (snd G G).left) t ∈ V by rwa [hcq]⟩,
        show ((lift e e).left ≫ (μ[G]).left) t ∈ V by rwa [hcm]⟩ (TopologicalSpace.Opens.isOpen _)
  have hp : V' ≤ (fst G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_left)
  have hq : V' ≤ (snd G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_right)
  have hm : V' ≤ (μ[G]).left ⁻¹ᵁ V := hV'V.trans inf_le_right
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hc : W ≤ (lift e e).left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t)
      (u := (lift e e).left ⁻¹ᵁ V') htV' (TopologicalSpace.Opens.isOpen _)
  refine ⟨W, htW, ?_⟩
  have heW : W ≤ e.left ⁻¹ᵁ V := hcp ▸ le_preimage_of_comp _ _ hp hc
  have near : ∀ x : T ⟶ G, j ≫ x = 1 → j.left ≫ x.left = j.left ≫ e.left := fun x hx ↦ by
    rw [← Over.comp_left, ← Over.comp_left, hx, he]
  have near₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 →
      j.left ≫ (lift x y).left = j.left ≫ (lift e e).left := fun x y hx hy ↦ by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, hx, hy, he]
  have hW₁ : ∀ x : T ⟶ G, j ≫ x = 1 → W ≤ x.left ⁻¹ᵁ V := fun x hx ↦ by
    rw [preimage_eq j.left hj (near x hx)]; exact heW
  have hW₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 → W ≤ (lift x y).left ⁻¹ᵁ V' :=
    fun x y hx hy ↦ by rw [preimage_eq j.left hj (near₂ x y hx hy)]; exact hc
  have add : ∀ (x y : T ⟶ G) (hx : j ≫ x = 1) (hy : j ≫ y = 1) (hxy : j ≫ (x * y) = 1)
      (s : Γ(G.left, V)), (x * y).left.appLE V W (hW₁ _ hxy) s =
        x.left.appLE V W (hW₁ _ hx) s + y.left.appLE V W (hW₁ _ hy) s - e.left.appLE V W heW s := by
    intro x y hx hy hxy s
    have := parallelogram (fst G G).left (snd G G).left
      (fun Z u v h₁ h₂ ↦ pullback.hom_ext h₁ h₂)
      (lift x e).left (lift e y).left (lift e e).left (lift x y).left
      (by simp only [← Over.comp_left, lift_fst]) (by simp only [← Over.comp_left, lift_fst])
      (by simp only [← Over.comp_left, lift_snd]) (by simp only [← Over.comp_left, lift_snd])
      hV hV' hW hp hq (hW₂ _ _ hx he) (hW₂ _ _ he hy) hc (hW₂ _ _ hx hy)
      (fun s t ↦ hsq W hW _ _ (app_sub_eq_zero _ (near₂ _ _ hx he) _ _ _ _ _)
        (app_sub_eq_zero _ (near₂ _ _ he hy) _ _ _ _ _)) ((μ[G]).left.appLE V V' hm s)
    rwa [comp_appLE_apply _ _ (x := (x * y).left) (by rw [← Over.comp_left, ← Hom.mul_def])
        _ _ _ _ _ (hW₁ _ hxy),
      comp_appLE_apply _ _ (x := x.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one])
        _ _ _ _ _ (hW₁ _ hx),
      comp_appLE_apply _ _ (x := y.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul])
        _ _ _ _ _ (hW₁ _ hy),
      comp_appLE_apply _ _ hcm _ _ _ _ _ heW] at this
  have hpow : ∀ k : ℕ, j ≫ (z ^ k) = 1 := fun k ↦ by rw [comp_pow, hz, one_pow]
  have ind : ∀ (k : ℕ) (s : Γ(G.left, V)), (z ^ k).left.appLE V W (hW₁ _ (hpow k)) s -
      e.left.appLE V W heW s = k * (z.left.appLE V W (hW₁ _ hz) s - e.left.appLE V W heW s) := by
    intro k s
    induction k with
    | zero =>
      rw [appLE_congr (g := e.left) (by rw [pow_zero]) _ _ _ heW]
      simp
    | succ k ih =>
      rw [appLE_congr (g := (z ^ k * z).left) (by rw [pow_succ]) _ _ _
        (hW₁ _ (by rw [← pow_succ]; exact hpow _)), add _ _ (hpow k) hz (by rw [← pow_succ]; exact hpow _)]
      push_cast
      linear_combination ih
  have hn' : IsUnit (n : Γ(T.left, W)) := by
    simpa using hn.map (T.hom.appLE ⊤ W le_top).hom
  have fin : z.left.appLE V W (hW₁ _ hz) = e.left.appLE V W heW := by
    ext s
    have := ind n s
    rw [appLE_congr (g := e.left) (by rw [hzn]) _ _ _ heW, sub_self] at this
    exact sub_eq_zero.mp (hn'.mul_right_eq_zero.mp this.symm)
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec z.left hW (hW₁ _ hz), fin, hV.SpecMap_appLE_fromSpec e.left hW heW]

lemma mul_eq_zero_of_ker_sq {R R₀ : CommRingCat.{0}} (φ : R ⟶ R₀) (hφ : RingHom.ker φ.hom ^ 2 = ⊥)
    (W : (Spec R).Opens) (hW : IsAffineOpen W) (s t : Γ(Spec R, W))
    (hs : (Spec.map φ).app W s = 0) (ht : (Spec.map φ).app W t = 0) : s * t = 0 := by
  have h : (Spec.map φ).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    suffices RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ by
      simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
        Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact this
    have key : ∀ s ∈ RingHom.ker (Spec.map φ).appTop.hom,
        (Scheme.ΓSpecIso R).hom s ∈ RingHom.ker φ.hom := fun s hs ↦ by
      rw [RingHom.mem_ker] at hs ⊢
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, hs,
        map_zero]
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_bot]
    apply (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
    rw [map_mul, map_zero, ← Ideal.mem_bot, ← hφ, pow_two]
    exact Ideal.mul_mem_mul (key s hs) (key t ht)
  have h' : RingHom.ker ((Spec.map φ).app W).hom ^ 2 = ⊥ := by
    simpa using congr(($h).ideal ⟨W, hW⟩)
  rw [← Ideal.mem_bot, ← h', pow_two]
  exact Ideal.mul_mem_mul hs ht

end GlobalTheory.MulUnramified

namespace GlobalTheory


open MulUnramified in
theorem formallyUnramified_mulN (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulN G n).left := by
  refine FormallyUnramified.of_hom_ext _ fun R R₀ φ hφ hsq g₁ g₂ hi hg ↦ ?_
  have hS : g₂ ≫ G.hom = g₁ ≫ G.hom := by
    rw [← Over.w (mulN G n), reassoc_of% hg]
  let T : Over S := Over.mk (g₁ ≫ G.hom)
  let T₀ : Over S := Over.mk (Spec.map φ ≫ g₁ ≫ G.hom)
  let j : T₀ ⟶ T := Over.homMk (Spec.map φ) rfl
  let x : T ⟶ G := Over.homMk g₁ rfl
  let y : T ⟶ G := Over.homMk g₂ hS
  have hj : j ≫ x = j ≫ y := Over.OverMorphism.ext hi
  have hxy : x ^ n = y ^ n := by
    rw [← comp_mulN, ← comp_mulN]
    exact Over.OverMorphism.ext hg
  have hsurj : Function.Surjective (Spec.map φ) := by
    intro (p : PrimeSpectrum R)
    change p ∈ Set.range (PrimeSpectrum.comap φ.hom)
    rw [range_comap_of_surjective _ _ hφ, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow ha 2
    rw [hsq, Ideal.mem_bot] at this
    rw [this]
    exact zero_mem _
  have := eq_one_of_pow_eq_one G j hsurj (mul_eq_zero_of_ker_sq φ hsq) n hn (x / y)
    (by rw [GrpObj.comp_div, hj, div_self']) (by rw [div_pow, hxy, div_self'])
  exact congrArg (·.left) (div_eq_one.mp this)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace OpenSubgroupScheme

variable {K : Type} [Field K] {Ga G : Over (Spec (CommRingCat.of K))}

lemma mem_range_iff_factors (p : Ga ⟶ G) [IsOpenImmersion p.left] (x : 𝟙_ _ ⟶ G) :
    x.left (IsLocalRing.closedPoint K) ∈ Set.range p.left ↔ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = x := by
  constructor
  · intro h
    have hr : Set.range x.left ⊆ Set.range p.left := by
      rintro _ ⟨z, rfl⟩
      have : z = IsLocalRing.closedPoint K :=
        Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
      rw [this]; exact h
    refine ⟨Over.homMk (IsOpenImmersion.lift p.left x.left hr) ?_, ?_⟩
    · rw [← Over.w p, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w x
    · ext1
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨a.left (IsLocalRing.closedPoint K), rfl⟩

lemma exists_point [IsAlgClosed K] [LocallyOfFiniteType G.hom] (y : G.left) (hy : IsClosed {y}) :
    ∃ x : 𝟙_ _ ⟶ G, x.left (IsLocalRing.closedPoint K) = y :=
  ⟨Over.homMk (pointOfClosedPoint G.hom y hy) (pointOfClosedPoint_comp G.hom y hy),
    pointOfClosedPoint_apply G.hom y hy _⟩

lemma comp_mulRight [GrpObj G] (x g : 𝟙_ _ ⟶ G) : x ≫ (GrpObj.mulRight g).hom = x * g := by
  rw [GrpObj.mulRight_hom, Hom.mul_def, comp_lift_assoc, Category.comp_id, ← Category.assoc,
    Subsingleton.elim (x ≫ toUnit G) (𝟙 _), Category.id_comp]

lemma mulRight_apply [GrpObj G] (x g : 𝟙_ _ ⟶ G) :
    (GrpObj.mulRight g).hom.left (x.left (IsLocalRing.closedPoint K)) =
      (x * g).left (IsLocalRing.closedPoint K) := by
  rw [← comp_mulRight]; rfl

lemma range_eq_univ [IsAlgClosed K] [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G) [IsMonHom p]
    [IsOpenImmersion p.left] [LocallyOfFiniteType G.hom] [ConnectedSpace G.left] :
    Set.range p.left = Set.univ := by
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  set U : Set G.left := Set.range p.left with hU
  have hUo : IsOpen U := p.left.isOpenEmbedding.isOpen_range
  let V : Set G.left := ⋃ g : {g : 𝟙_ _ ⟶ G // ¬ ∃ a : 𝟙_ _ ⟶ Ga, a ≫ p = g},
    (GrpObj.mulRight g.1).hom.left ⁻¹' U
  have hVo : IsOpen V := isOpen_iUnion fun g => hUo.preimage (Scheme.Hom.continuous _)
  have hdisj : U ∩ V = ∅ := by
    by_contra hne
    obtain ⟨y, ⟨hyU, hyV⟩, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.mpr hne)
      (hUo.inter hVo).isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hyV
    rw [Set.mem_preimage, mulRight_apply] at hg
    obtain ⟨a, ha⟩ := (mem_range_iff_factors p x).mp hyU
    obtain ⟨b, hb⟩ := (mem_range_iff_factors p _).mp hg
    refine g.2 ⟨a⁻¹ * b, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha, hb, inv_mul_cancel_left]
  have hone : (1 : 𝟙_ _ ⟶ G).left (IsLocalRing.closedPoint K) ∈ U :=
    (mem_range_iff_factors p _).mpr ⟨1, MonObj.one_comp p⟩
  have hcov : U ∪ V = Set.univ := by
    by_contra hne
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      (hUo.union hVo).isClosed_compl.isLocallyClosed
    obtain ⟨x, rfl⟩ := exists_point y hyc
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hy
    refine hy.2 (Set.mem_iUnion.mpr ⟨⟨x⁻¹, ?_⟩, ?_⟩)
    · rintro ⟨a, ha⟩
      refine hy.1 ((mem_range_iff_factors p x).mpr ⟨a⁻¹, ?_⟩)
      rw [GrpObj.inv_comp, ha, inv_inv]
    · rw [Set.mem_preimage, mulRight_apply, mul_inv_cancel]
      exact hone
  have hc : Uᶜ = V := by
    ext y
    constructor
    · intro hy
      exact ((hcov ▸ Set.mem_univ y : y ∈ U ∪ V)).resolve_left hy
    · intro hy hyU
      exact (hdisj ▸ ⟨hyU, hy⟩ : y ∈ (∅ : Set G.left))
  have hcl : IsClopen U := ⟨isOpen_compl_iff.mp (hc ▸ hVo), hUo⟩
  exact hcl.eq_univ ⟨_, hone⟩

end OpenSubgroupScheme

theorem isIso_of_isOpenImmersion_of_geometricallyConnected :
    ∀ (S : Scheme.{0}) (Ga G : Over S) [GrpObj Ga] [GrpObj G] (p : Ga ⟶ G), IsMonHom p →
      IsOpenImmersion p.left → LocallyOfFiniteType G.hom → GeometricallyConnected G.hom → IsIso p := by
  intro S Ga G _ _ p _ _ _ _
  have hsurj : Set.range p.left = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    let s : S := G.hom y
    let Ω : Type := AlgebraicClosure (S.residueField s)
    let t : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ω)) ≫ S.fromSpecResidueField s
    have ht : G.hom y = t (IsLocalRing.closedPoint Ω) :=
      (Scheme.fromSpecResidueField_apply s _).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ ht
    have : IsOpenImmersion ((Over.pullback t).map p).left :=
      MorphismProperty.overPullbackMap _ _ ‹_›
    have : LocallyOfFiniteType ((Over.pullback t).obj G).hom := by
      show LocallyOfFiniteType (pullback.snd G.hom t); infer_instance
    have : ConnectedSpace ((Over.pullback t).obj G).left :=
      GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback G.hom t)
    have h := OpenSubgroupScheme.range_eq_univ ((Over.pullback t).map p)
    obtain ⟨w, hw⟩ : z ∈ Set.range ((Over.pullback t).map p).left := h ▸ Set.mem_univ _
    refine ⟨pullback.fst Ga.hom t w, ?_⟩
    have e : ((Over.pullback t).map p).left ≫ pullback.fst G.hom t = pullback.fst Ga.hom t ≫ p.left :=
      pullback.lift_fst _ _ _
    rw [← hz, ← hw, ← Scheme.Hom.comp_apply, ← e]
    rfl
  have : IsIso p.left := isIso_of_isOpenImmersion_of_opensRange_eq_top p.left (by
    ext1
    exact hsurj)
  have : IsIso ((Over.forget S).map p) := this
  exact isIso_of_reflects_iso p (Over.forget S)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteOfIsClosedSplitTorusOfPowEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory

theorem adjunction_homEquiv_symm_mul {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) [R.Monoidal] {Y : C} {M : D} [MonObj M] (a b : Y ⟶ R.obj M) :
    (adj.homEquiv Y M).symm (a * b) = (adj.homEquiv Y M).symm a * (adj.homEquiv Y M).symm b := by
  rw [Hom.mul_def, Hom.mul_def, Functor.obj.μ_def, ← Category.assoc,
    adj.homEquiv_naturality_right_symm]
  congr 1
  ext
  · rw [← adj.homEquiv_naturality_right_symm]; simp
  · rw [← adj.homEquiv_naturality_right_symm]; simp

variable {k : Type} [Field k] {X : Type} [AddCommGroup X]

attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

noncomputable def splitTorusPoint (t : Multiplicative X →* kˣ) :
    𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X :=
  Over.homMk (Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom) (by
    erw [Category.assoc, torusIso_hom_hom, ← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have : (torusEval t).toRingHom.comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k :=
      (torusEval t).comp_algebraMap
    rw [this]
    exact Spec.map_id _)

theorem splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    (splitTorusPoint t).left =
      Spec.map (CommRingCat.ofHom (torusEval t).toRingHom) ≫ (torusIso k X).hom := rfl

theorem splitTorusPoint_bijective :
    Function.Bijective (splitTorusPoint : (Multiplicative X →* kˣ) → _) := by
  constructor
  · intro s t h
    have h1 := congrArg (·.left) h
    simp only [splitTorusPoint_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).1 h1)
    exact torusEval_bijective.1 (AlgHom.coe_ringHom_injective (congrArg (·.hom) h2))
  · intro x
    let g : Spec (.of k) ⟶ Spec (.of (AddMonoidAlgebra k X)) := x.left ≫ (torusIso k X).inv
    have hg : CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k X)) ≫ Spec.preimage g = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, ← torusIso_hom_hom, Spec.map_id]
      simp only [g]
      erw [Category.assoc, Iso.inv_hom_id_assoc]
      exact Over.w x
    obtain ⟨t, ht⟩ := torusEval_bijective.2 ⟨(Spec.preimage g).hom, fun r => congr($hg r)⟩
    refine ⟨t, Over.OverMorphism.ext ?_⟩
    rw [splitTorusPoint_left, ht]
    change Spec.map (Spec.preimage g) ≫ _ = _
    rw [Spec.map_preimage]
    simp only [g]
    erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

noncomputable def splitTorusDown (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ splitTorusAff ZU X :=
  (Over.homMk (𝟙 (Sp k)) (specULiftZIsTerminal.hom_ext _ _) :
    (Spec (.of k)).asOver (Spec ZU) ⟶ (Over.map (toZ (Sp k))).obj (𝟙_ (Over (Sp k)))) ≫
    ((Over.mapPullbackAdj (toZ (Sp k))).homEquiv _ _).symm x

theorem splitTorusDown_left (x : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    (splitTorusDown x).left = x.left ≫ torusFst (Sp k) X := by
  simp [splitTorusDown, Adjunction.homEquiv_symm_apply, torusFst]
  rfl

theorem splitTorusDown_mul (x y : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :
    splitTorusDown (x * y) = splitTorusDown x * splitTorusDown y := by
  unfold splitTorusDown
  rw [← comp_mul]
  exact congrArg _ (adjunction_homEquiv_symm_mul (Over.mapPullbackAdj _) x y)

theorem splitTorusDown_injective :
    Function.Injective (splitTorusDown : (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) → _) := by
  intro x y h
  have h1 := congrArg (·.left) h
  simp only [splitTorusDown_left] at h1
  exact Over.OverMorphism.ext (pullback.hom_ext h1 ((Over.w x).trans (Over.w y).symm))

noncomputable def torusEvalInt (t : Multiplicative X →* kˣ) :
    AddMonoidAlgebra ZU.{0} X →ₐ[ZU.{0}] k :=
  AddMonoidAlgebra.lift _ k X ((Units.coeHom k).comp t)

theorem splitTorusDown_point (t : Multiplicative X →* kˣ) :
    splitTorusDown (splitTorusPoint t) = Spec.mapMulEquiv (WithConv.toConv (torusEvalInt t)) := by
  refine Over.OverMorphism.ext ?_
  rw [splitTorusDown_left, splitTorusPoint_left]
  erw [Category.assoc, torusIso_hom_fst, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom (torusEvalInt t).toRingHom)
  rw [← CommRingCat.ofHom_comp]
  congr 2
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt]

theorem torusEvalInt_mul (s t : Multiplicative X →* kˣ) :
    WithConv.toConv (torusEvalInt (s * t)) =
      WithConv.toConv (torusEvalInt s) * WithConv.toConv (torusEvalInt t) := by
  apply WithConv.ofConv_injective
  apply AlgHom.coe_ringHom_injective
  refine ringHom_ext_ZU fun y => ?_
  simp [torusEvalInt, AlgHom.convMul_def]

theorem splitTorusPoint_mul (s t : Multiplicative X →* kˣ) :
    splitTorusPoint (s * t) = splitTorusPoint s * splitTorusPoint t := by
  apply splitTorusDown_injective
  rw [splitTorusDown_mul, splitTorusDown_point, splitTorusDown_point, splitTorusDown_point,
    torusEvalInt_mul, map_mul]


variable (k X) in
noncomputable def splitTorusPointEquiv :
    (Multiplicative X →* kˣ) ≃* (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) :=
  { Equiv.ofBijective _ splitTorusPoint_bijective with map_mul' := splitTorusPoint_mul }

theorem range_splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by
  have h : ∀ p, (splitTorusPoint t).left p = (torusIso k X).hom (torusPrime t) := fun p => by
    have hp : p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hp]
    rfl
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    exact h p
  · rintro rfl
    exact ⟨_, h (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

theorem finite_of_isClosed_splitTorus_of_pow_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] (n : ℕ), n.Prime → (n : k) ≠ 0 →
      ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X))
        (Z : Set (splitTorus (Sp k) X).left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) →
        (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C := by
  intro k _ _ X _ _ _ n hp hn C Z hZ hC htors
  haveI : NeZero (n : k) := ⟨hn⟩
  let e := splitTorusPointEquiv (k := k) (X := X)
  have hcl : @IsClosed _ (torusZariski k X)
      (C.comap e.toMonoidHom : Set (Multiplicative X →* kˣ)) := by
    refine isClosed_induced_iff.2 ⟨(torusIso k X).hom ⁻¹' Z,
      hZ.preimage (torusIso k X).hom.continuous, ?_⟩
    ext t
    change _ ↔ splitTorusPoint t ∈ C
    rw [hC, range_splitTorusPoint_left, Set.singleton_subset_iff]
    rfl
  have h := finite_of_isClosed_torusZariski_of_pow_eq_one hp.two_le hcl fun s hs h1 =>
    e.injective (by rw [map_one]; exact htors _ hs (by rw [← map_pow, h1, map_one]))
  have e' : C.comap e.toMonoidHom ≃ C := e.toEquiv.subtypeEquiv fun _ => Iff.rfl
  exact e'.finite_iff.1 h.1

end GlobalTheory
end
