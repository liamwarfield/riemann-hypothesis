module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseSchOfHomScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypePreimageFromSpecStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothStalk

theorem essFiniteType_preimage_fromSpecStalk (F : Type) [CommRing F] (X : Scheme.{0})
    (g : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType g] (z : X) :
    (Spec.preimage (X.fromSpecStalk z ≫ g)).hom.EssFiniteType := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have he : Spec.preimage (X.fromSpecStalk z ≫ g) = φ ≫ X.presheaf.germ U z hx := by
    rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, hφ, ← hU.fromSpecStalk_eq_fromSpecStalk hx,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  rw [he, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp hft.essFiniteType ?_
  let _ := X.presheaf.algebra_section_stalk ⟨z, hx⟩
  have := hU.isLocalization_stalk ⟨z, hx⟩
  exact Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hx⟩).asIdeal.primeCompl

theorem stalk_regular_essFiniteType_dim : ∀ (F : Type) [Field F] (Cs : Scheme.{0}) (g : Cs ⟶ Sp F) (n : ℕ), SmoothOfRelativeDimension n g → ∀ z : Cs, IsRegularLocalRing (Cs.presheaf.stalk z) ∧ ∃ b : F →+* Cs.presheaf.stalk z, Cs.fromSpecStalk z ≫ g = spMap b ∧ b.EssFiniteType ∧ (letI := ((residue (Cs.presheaf.stalk z)).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim (Cs.presheaf.stalk z) = a ∧ Algebra.trdeg F (ResidueField (Cs.presheaf.stalk z)) = t ∧ a + t = n) := by
  intro F _ Cs g n hsm z
  haveI := hsm
  haveI : Smooth g := SmoothOfRelativeDimension.smooth n g
  haveI : IsRegularRing (CommRingCat.of F) := inferInstanceAs (IsRegularRing F)
  have hreg : ∀ x : Cs, IsRegularLocalRing (Cs.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth g x
  refine ⟨hreg z, (Spec.preimage (Cs.fromSpecStalk z ≫ g)).hom, ?_, essFiniteType_preimage_fromSpecStalk F Cs g z, ?_⟩
  · exact (Spec.map_preimage _).symm
  · have h := GlobalTheory.StalkDim.stalk_dim_add_trdeg F g (𝟙 Cs) n (by simp) (by simpa using hsm)
      (fun x => haveI := hreg x; ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing) z
    have he : Spec.preimage (Cs.fromSpecResidueField z ≫ g) =
        Spec.preimage (Cs.fromSpecStalk z ≫ g) ≫ Cs.residue z := by
      rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Scheme.fromSpecResidueField,
        Category.assoc]
    rw [he] at h
    exact h

end GlobalTheory.SmoothStalk
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.BaseSch

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lowMap_eq {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :
    lowMap c b = spMap b ≫ lowMap c (RingHom.id c.F) := by
  simp only [lowMap, RingHom.id_comp]
  rw [← spMap_comp']

theorem objMap_congr {D : Datum H} {l : Geo.Tor.Level H} {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    {s' : S' ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {f f' : S' ⟶ S} (h : f = f')
    (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ : 𝟙_ (Over S) ⟶ G) :
    ∃ σ' : 𝟙_ (Over S') ⟶ G', σ'.left ≫ φ = q ≫ σ.left := by
  have hw : (q ≫ σ.left) ≫ G.hom = 𝟙 S' ≫ q := by
    rw [Category.assoc, Over.w σ]
    simp
  refine ⟨Over.homMk (h.1.lift (q ≫ σ.left) (𝟙 S') hw) (by simpa using h.1.lift_snd _ _ hw), ?_⟩
  simp

theorem hom_ext_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) {T : Over S'} (σ₁ σ₂ : T ⟶ G')
    (e : σ₁.left ≫ φ = σ₂.left ≫ φ) : σ₁ = σ₂ := by
  ext1
  exact h.1.hom_ext e (by rw [Over.w σ₁, Over.w σ₂])

theorem pull_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ₁ σ₂ : 𝟙_ (Over S') ⟶ G') (τ₁ τ₂ : 𝟙_ (Over S) ⟶ G)
    (h₁ : σ₁.left ≫ φ = q ≫ τ₁.left) (h₂ : σ₂.left ≫ φ = q ≫ τ₂.left) :
    (σ₁ * σ₂).left ≫ φ = q ≫ (τ₁ * τ₂).left := by
  let Q : Over.mk ((𝟙_ (Over S')).hom ≫ q) ⟶ 𝟙_ (Over S) := Over.homMk q (by simp)
  have e := h.2 (𝟙_ (Over S')) σ₁ σ₂ (Q ≫ τ₁) (Q ≫ τ₂) (by simp [Q, h₁]) (by simp [Q, h₂])
  rw [← e, ← MonObj.comp_mul]
  simp [Q]

theorem sec_comp_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (hw : φ ≫ G.hom = G'.hom ≫ f) (σ : 𝟙_ (Over S') ⟶ G') (τ : 𝟙_ (Over S) ⟶ G) :
    (σ.left ≫ φ) ≫ G.hom = (f ≫ τ.left) ≫ G.hom := by
  rw [Category.assoc, hw, Category.assoc, Over.w τ, ← Category.assoc, Over.w σ]
  simp

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


set_option maxHeartbeats 800000 in
theorem of_homScheme (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F)
    (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F)))
    (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)) (N : ℕ) (hsm : SmoothOfRelativeDimension N g)
    (hex : ∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV)
      (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) →
      (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v),
        v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left)
    (huniq : ∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g →
      ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
        (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)),
        s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) →
        (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂)
    (heps : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l)))
      (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v)
      (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
      s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) →
      (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)
    (hadd : ∀ y z, u (y + z) = u y * u z) (hlin : ∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV)
    (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)) (hx : ∀ y z, x (y + z) = x y * x z)
    (hxl : ∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b)
      (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)),
      b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧
      IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧
      ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
        ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂))
          (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧
        (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f))
          (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
          (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) →
          (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧
      (letI := ((residue W).comp b).toAlgebra
        ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = N) := by
  obtain ⟨v, m0, hvg, hvx⟩ := hex V bV o' x hx hxl
  obtain ⟨hreg, b, hqb, hft, hdim⟩ :=
    GlobalTheory.SmoothStalk.stalk_regular_essFiniteType_dim c.F Cs g N hsm (v (closedPoint V))
  haveI : IsDomain (Cs.presheaf.stalk (v (closedPoint V))) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨q, hq⟩ : ∃ q, q = Cs.fromSpecStalk (v (closedPoint V)) := ⟨_, rfl⟩
  rw [← hq] at hqb
  have hs : lowMap c b = q ≫ g ≫ lowMap c (RingHom.id c.F) := by
    rw [lowMap_eq c b, ← hqb, Category.assoc]
  obtain ⟨o, ⟨mq⟩⟩ := (obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (g ≫ lowMap c (RingHom.id c.F)) oC q (lowMap c b) hs
  have hsec := fun y => exists_section_pull mq.toSABMap.cart (u y)
  choose x₀ hx₀ using hsec
  set θ₀ : Cs.presheaf.stalk (v (closedPoint V)) →+* V := (Scheme.stalkClosedPointTo v).hom with hθ₀
  have hθq : spMap θ₀ ≫ q = v := by
    rw [hq]
    simpa [hθ₀, spMap] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk v
  have hθb : θ₀.comp b = bV := by
    apply spMap_injective
    rw [spMap_comp', ← hqb, ← Category.assoc, hθq, hvg]
  obtain ⟨m0', hm0'⟩ := objMap_congr hθq.symm m0
  obtain ⟨n, hn⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o' q (spMap θ₀) mq).2 m0'
  have hmono : ∀ {T : Scheme.{0}} (a₁ a₂ : T ⟶ Sp (Cs.presheaf.stalk (v (closedPoint V)))), a₁ ≫ q = a₂ ≫ q → a₁ = a₂ :=
    fun a₁ a₂ h => by rw [hq] at h; exact (cancel_mono _).1 h
  refine ⟨Cs.presheaf.stalk (v (closedPoint V)), inferInstance, inferInstance, hreg, b, o, x₀, θ₀, n, hft, ?_, ?_, ?_, hθb, ?_, ⟨?_, ?_⟩, hdim⟩
  · intro y z
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hadd, pull_mul mq.toSABMap.cart _ _ _ _ (hx₀ y) (hx₀ z)]
  · intro a y
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hlin, Over.comp_left, Over.comp_left, Category.assoc, mq.toSABMap.act a, reassoc_of% (hx₀ y)]
  · exact inferInstance
  · intro y
    refine mq.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn, hm0', hvx, Category.assoc, hx₀, ← Category.assoc, hθq]
    · exact sec_comp_eq _ _ n.toSABMap.cart.1.w (x y) (x₀ y)
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₁) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₂) mq).1 m₂
    have hg : ∀ f : Cs.presheaf.stalk (v (closedPoint V)) →+* A, (spMap f ≫ q) ≫ g = spMap (f.comp b) := fun f => by
      rw [Category.assoc, hqb, spMap_comp']
    have e := huniq A (spMap f₁ ≫ q) (spMap f₂ ≫ q) (by rw [hg, hg, hf]) _ o'' k₁ k₂ z
      (by rw [lowMap_eq c (f₁.comp b), ← hg, Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, Category.assoc])
    exact spMap_injective (hmono _ _ e)
  · intro k _ f o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q
      (spMap (GlobalTheory.RigChart.constHom f)) mq).1 m₂
    have hc : spMap (GlobalTheory.RigChart.constHom f) ≫ q = constPt (spMap f ≫ q) := by
      simp only [constPt, GlobalTheory.RigChart.constHom, spMap_comp', Category.assoc]
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hc k₂
    have e := heps k (spMap f ≫ q) _ o'' k₁ k₂' z
      (by rw [lowMap_eq c (f.comp b), spMap_comp', ← hqb]; simp only [Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, ← Category.assoc, hc])
    rw [← hc] at e
    exact spMap_injective (hmono _ _ e)

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

theorem exists_baseSch_of_homScheme (hcs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)) : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hx hxl
  obtain ⟨Cs, g, oC, u, hsm, hadd, hlin, hex, huniq, heps⟩ := hcs D' c X
  exact of_homScheme D' c X Cs g oC u _ hsm hex huniq heps hadd hlin V bV o' x hx hxl

end GlobalTheory.UCanon.BaseSch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSchemeLow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.RankZero

theorem nonempty_moduli : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H), D.p + D.q = 0 → Nonempty (Moduli D l) :=
  fun H D l hD => (GlobalTheory.Models.RankZero.main _ H D hD).1.map fun X => X l

end GlobalTheory.UCanon.RankZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliOfRankZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_moduli_of_rank_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H), D.p + D.q = 0 → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.UCanon.RankZero.nonempty_moduli | exact GlobalTheory.UCanon.RankZero.nonempty_moduli | (intros; apply GlobalTheory.UCanon.RankZero.nonempty_moduli <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UObjDim

theorem smoothOfRelativeDimension_obj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom :=
  fun _ _ _ _ o => GlobalTheory.ObjDim.smoothOfRelativeDimension o

end GlobalTheory.UObjDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionShimuraObjectAbelianSchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) (o : Obj D l (baseKA l) s), SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  first | exact @GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | exact GlobalTheory.UObjDim.smoothOfRelativeDimension_obj | (intros; apply GlobalTheory.UObjDim.smoothOfRelativeDimension_obj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorObjDualRepresents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDual
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDualDim

theorem finrank_dual_eq (O X : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    Module.finrank O (Module.Dual O X) = Module.finrank O X := by
  haveI : Module.FinitePresentation O X := Module.finitePresentation_of_projective O X
  let F := FractionRing O
  let f : X →ₗ[O] F ⊗[O] X := TensorProduct.mk O F X 1
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) f le_rfl
  let g := IsLocalizedModule.map (nonZeroDivisors O) f (Algebra.linearMap O F)
  have h2 := IsLocalizedModule.finrank_eq (nonZeroDivisors O) g le_rfl
  rw [← h1, ← h2, ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    ← IsLocalization.finrank_eq F (nonZeroDivisors O) le_rfl,
    (LinearMap.extendScalarsOfIsLocalizationEquiv (nonZeroDivisors O) F).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem smoothOfRelativeDimension_tensorObj_dual : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  intro S B _ _ O _ _ _ a X _ _ _ _ g hg
  have h := GlobalTheory.SerreDim.smoothOfRelativeDimension_tensor S O (Module.Dual O X) B
    (tensorObj (Module.Dual O X) a) a (tensorAct (Module.Dual O X) a) g
    ⟨GlobalTheory.Serre.isTensor (Module.Dual O X) a⟩ hg
  rwa [finrank_dual_eq] at h

end GlobalTheory.TensorDualDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDualStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (GlobalTheory.Serre.tensorObj (Module.Dual O X) a).hom := by
  first | exact @GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | exact GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | (intros; apply GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HomScheme

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem dualTensorHom_lTensor {N N' : Type} [AddCommGroup N] [Module O N] [AddCommGroup N']
    [Module O N'] (g : N →ₗ[O] N') (z : Module.Dual O X ⊗[O] N) (x : X) :
    dualTensorHom O X N' (g.lTensor _ z) x = g (dualTensorHom O X N z x) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f n => simp [dualTensorHom_apply]
  | add z w hz hw => simp [map_add (f := _), hz, hw]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]
  {a : OAct O G} {b : OAct O H}

def homEquiv [Module.Finite O X] [Module.Projective O X] (h : IsTensor H b G a (Module.Dual O X))
    (T : Over S) : Pts b T ≃ₗ[O] (X →ₗ[O] Pts a T) :=
  (h.equiv T).symm.trans (dualTensorHomEquiv O X (Pts a T))

theorem homEquiv_pre [Module.Finite O X] [Module.Projective O X]
    (h : IsTensor H b G a (Module.Dual O X)) {T T' : Over S} (u : T' ⟶ T) (y : Pts b T) (x : X) :
    homEquiv h T' (Pts.pre b u y) x = Pts.pre a u (homEquiv h T y x) := by
  simp only [homEquiv, LinearEquiv.trans_apply]
  rw [h.natural_symm]
  exact dualTensorHom_lTensor _ _ x

theorem tensorObj_dual_represents {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]
    {O : Type} [CommRing O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] :
    ∃ u : X → (tensorObj (Module.Dual O X) a ⟶ B),
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) →
          ∃! c : T ⟶ tensorObj (Module.Dual O X) a, ∀ x, c ≫ u x = f x := by
  let M := Module.Dual O X
  let C := tensorObj M a
  let b := tensorAct M a
  let h : IsTensor C b B a M := isTensor M a
  let Φ := homEquiv h
  let u : X → (C ⟶ B) := fun x => (Φ C (Pts.mk b (𝟙 C)) x).hom
  have hnat : ∀ (T : Over S) (c : T ⟶ C) (x : X), (Φ T (Pts.mk b c) x).hom = c ≫ u x := by
    intro T c x
    have := congrArg Pts.hom (homEquiv_pre h c (Pts.mk b (𝟙 C)) x)
    rw [Pts.hom_pre] at this
    rw [← this]
    congr 3
  refine ⟨u, fun x => ?_, fun x y => ?_, fun o x => ?_, fun T f hadd hsmul => ?_⟩
  · refine isMonHom_of_mul_comp _ fun T p q => ?_
    rw [← hnat, ← hnat, ← hnat, Pts.mk_mul, map_add (f := _), LinearMap.add_apply, Pts.hom_add]
  · change (Φ C _ (x + y)).hom = _
    rw [map_add (f := _), Pts.hom_add]
  · change (Φ C _ (o • x)).hom = _
    rw [map_smul, Pts.hom_smul]
  · let F : X →ₗ[O] Pts a T :=
      { toFun := fun x => Pts.mk a (f x)
        map_add' := fun x y => by rw [hadd]; rfl
        map_smul' := fun o x => by rw [hsmul]; rfl }
    refine ⟨((Φ T).symm F).hom, fun x => ?_, fun c hc => ?_⟩
    · rw [← hnat, Pts.mk_hom, LinearEquiv.apply_symm_apply]
      rfl
    · have : Φ T (Pts.mk b c) = F := by
        ext1 x
        apply Pts.ext
        rw [hnat, hc]
        rfl
      rw [← this, LinearEquiv.symm_apply_apply]
      rfl

theorem exists_homObj_relDim (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (g : ℕ) (hg : SmoothOfRelativeDimension g B.hom)
    {O : Type} [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] :
    ∃ (C : Over S) (_ : GrpObj C) (u : X → (C ⟶ B)), IsAbelianScheme C ∧
      SmoothOfRelativeDimension (Module.finrank O X * g) C.hom ∧
      (∀ x, IsMonHom (u x)) ∧ (∀ x y, u (x + y) = u x * u y) ∧
      (∀ (o : O) x, u (o • x) = u x ≫ a.act o) ∧
      ∀ (T : Over S) (f : X → (T ⟶ B)), (∀ x y, f (x + y) = f x * f y) →
        (∀ (o : O) x, f (o • x) = f x ≫ a.act o) → ∃! c : T ⟶ C, ∀ x, c ≫ u x = f x := by
  haveI := hB.comm
  obtain ⟨u, h1, h2, h3, h4⟩ := tensorObj_dual_represents B a X
  exact ⟨_, inferInstance, u, (isTensor (Module.Dual O X) a).isAbelianScheme hB,
    GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul S B O a X g hg, h1, h2, h3, h4⟩

end GlobalTheory.HomScheme
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanonHom

theorem pullSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G)),
    (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r) →
    ∃ x : X → (T ⟶ G'), (∀ y, (x y).left ≫ φ = (x₀ y).left) ∧ (∀ y z, x (y + z) = x y * x z) ∧
      ∀ (r : O) y, x (r • y) = x y ≫ a'.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x₀ hadd hlin
  have hw : ∀ y, (x₀ y).left ≫ G.hom = T.hom ≫ f := fun y => Over.w (x₀ y)
  let x : X → (T ⟶ G') := fun y => Over.homMk (hφ.1.lift (x₀ y).left T.hom (hw y)) (hφ.1.lift_snd _ _ _)
  have hx : ∀ y, (x y).left ≫ φ = (x₀ y).left := fun y => hφ.1.lift_fst _ _ _
  have uniq : ∀ (p q : T ⟶ G'), p.left ≫ φ = q.left ≫ φ → p = q := fun p q h => by
    ext; apply hφ.1.hom_ext h; rw [Over.w p, Over.w q]
  refine ⟨x, hx, fun y z => uniq _ _ ?_, fun r y => uniq _ _ ?_⟩
  · rw [hx, hadd, hφ.2 T (x y) (x z) (x₀ y) (x₀ z) (hx y).symm (hx z).symm]
  · rw [hx, hlin, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hx]

theorem pushSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x : X → (T ⟶ G')),
    (∀ y z, x (y + z) = x y * x z) → (∀ (r : O) y, x (r • y) = x y ≫ a'.act r) →
    ∃ x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G), (∀ y, (x₀ y).left = (x y).left ≫ φ) ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧
      ∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x hadd hlin
  have hw : ∀ y, ((x y).left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := fun y => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (x y)]; rfl
  refine ⟨fun y => Over.homMk ((x y).left ≫ φ) (hw y), fun y => rfl, fun y z => ?_, fun r y => ?_⟩
  · ext
    change (x (y + z)).left ≫ φ = _
    rw [hadd]
    exact (hφ.2 T (x y) (x z) (Over.homMk _ (hw y)) (Over.homMk _ (hw z)) rfl rfl).symm
  · ext
    simp only [Over.homMk_left, Over.comp_left, hlin, Category.assoc, ha]

theorem objMap_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} {o' : Obj D l b' s'} {o : Obj D l b s} {f f' : S' ⟶ S}
    (h : f = f') (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h; exact ⟨m, rfl⟩

theorem obj_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp B}
    (h : s₁ = s₂) (o : Obj D l b s₁) : ∃ o₂ : Obj D l b s₂, ∀ {S₀ : Scheme.{0}} {B₀ : Type} [CommRing B₀] {b₀ : Base l B₀}
      {s₀ : S₀ ⟶ Sp B₀} (o₀ : Obj D l b₀ s₀) (f : S ⟶ S₀), Nonempty (ObjMap o o₀ f) → Nonempty (ObjMap o₂ o₀ f) := by
  subst h; exact ⟨o, fun _ _ h => h⟩

theorem homScheme_low : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v) := by
  intro E _ _ _ H D' l c X _ _ _ _
  have hXo : Nonempty (Moduli D' (LowDat.lowLevel l)) := by
    by_cases hpq : 1 ≤ D'.p + D'.q
    · exact GlobalTheory.Moduli.moduli_scheme_exists E H D' _ hpq
    · exact GlobalTheory.T.nonempty_moduli_of_rank_zero H D' _ (by omega)
  obtain ⟨Xo⟩ := hXo
  set sF : Sp c.F ⟶ Sp (KA (LowDat.lowLevel l)) := lowMap c (RingHom.id c.F) with hsF
  have P := GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := LowDat.lowLevel l)
  obtain ⟨oY, ⟨mY⟩⟩ := P.1 Xo.s Xo.univ (pullback.fst Xo.s sF) (pullback.snd Xo.s sF ≫ sF) pullback.condition.symm
  have hB : IsAbelianScheme oY.t.G := ⟨inferInstance, oY.t.semi.smooth, oY.proper, oY.t.semi.geomConnected⟩
  have hg := GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme D' (LowDat.lowLevel l) (pullback.snd Xo.s sF ≫ sF) oY
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int _ _
  obtain ⟨C, _, u, -, hCsm, -, hadd, hlin, huniv⟩ :=
    GlobalTheory.HomScheme.exists_homObj_relDim _ oY.t.G hB _ hg oY.t.act X
  obtain ⟨oC, ⟨mC⟩⟩ := P.1 (pullback.snd Xo.s sF ≫ sF) oY C.hom ((C.hom ≫ pullback.snd Xo.s sF) ≫ sF)
    (Category.assoc _ _ _)
  obtain ⟨u', hu'φ, hu'add, hu'lin⟩ := pullSec oC.t.G oY.t.G C.hom mC.toSABMap.φ mC.cart (𝓞 E) oC.t.act oY.t.act mC.act X
    (𝟙_ (Over C.left)) (fun y => Over.homMk (𝟙 C.left) (by simp) ≫ u y) (fun y z => by rw [hadd, comp_mul])
    (fun r y => by rw [hlin, Category.assoc])
  have key : ∀ {T : Scheme.{0}} (v₁ v₂ : T ⟶ C.left), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, v₁ ≫ (u y).left = v₂ ≫ (u y).left) → v₁ = v₂ := by
    intro T v₁ v₂ hw hu
    obtain ⟨c0, -, huq⟩ := huniv (Over.mk (v₁ ≫ C.hom)) (fun y => Over.homMk v₁ rfl ≫ u y)
      (fun y z => by rw [hadd, comp_mul]) (fun r y => by rw [hlin, Category.assoc])
    have e1 := huq (Over.homMk v₁ rfl) (fun y => rfl)
    have e2 := huq (Over.homMk v₂ hw.symm) (fun y => by ext; simpa using (hu y).symm)
    simpa using congrArg CommaMorphism.left (e1.trans e2.symm)
  have hu'l : ∀ y, (u' y).left ≫ mC.toSABMap.φ = (u y).left := fun y => by rw [hu'φ]; simp
  have key2 : ∀ (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ (v₁ v₂ : Sp A ⟶ C.left)
      (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
      (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u' y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u' y).left) → v₁ = v₂ := by
    intro A _ hA v₁ v₂ s' o'' m₁ m₂ z hw hz₁ hz₂
    obtain ⟨k₁, hk₁⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨k₂, hk₂⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hw.symm k₂
    have hφ := GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' A hA s' _ o'' oY (v₁ ≫ C.hom) k₁ k₂'
    refine key v₁ v₂ hw fun y => ?_
    calc v₁ ≫ (u y).left = z y ≫ k₁.toSABMap.φ := by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hu'l]
      _ = z y ≫ k₂'.toSABMap.φ := by rw [hφ]
      _ = v₂ ≫ (u y).left := by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hu'l]
  refine ⟨C.left, C.hom ≫ pullback.snd Xo.s sF, oC, u', ?_, hu'add, hu'lin, ?_, ?_, ?_⟩
  · haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D'.dim)
    haveI h1 : SmoothOfRelativeDimension D'.dim (pullback.snd Xo.s sF) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension D'.dim)
        (IsPullback.of_hasPullback Xo.s sF) Xo.smooth
    haveI := hCsm
    rw [add_comm]
    infer_instance
  · intro V _ _ bV o' x hxadd hxlin
    obtain ⟨f, ⟨hf, ⟨k⟩⟩, -⟩ := Xo.rep (Sp V) (lowMap c bV) inferInstance o'
    have hlow : lowMap c bV = spMap bV ≫ sF := by simp only [hsF, lowMap, spMap, ← Spec.map_comp]; rfl
    let fY : Sp V ⟶ pullback Xo.s sF := pullback.lift f (spMap bV) (hf.trans hlow)
    obtain ⟨k', -⟩ := objMap_congr (pullback.lift_fst f (spMap bV) (hf.trans hlow)).symm k
    obtain ⟨n, -⟩ := (P.2 Xo.s (pullback.snd Xo.s sF ≫ sF) (lowMap c bV) Xo.univ oY o' (pullback.fst _ _) fY mY).2 k'
    obtain ⟨x₀, hx₀, hx₀add, hx₀lin⟩ := pushSec o'.t.G oY.t.G fY n.toSABMap.φ n.cart (𝓞 E) o'.t.act oY.t.act n.act X
      (𝟙_ (Over (Sp V))) x hxadd hxlin
    obtain ⟨cc, hcc, -⟩ := huniv (Over.mk ((𝟙_ (Over (Sp V))).hom ≫ fY)) x₀ hx₀add hx₀lin
    have hccw : cc.left ≫ C.hom = fY := by simpa using Over.w cc
    obtain ⟨n', hn'⟩ := objMap_congr hccw.symm n
    obtain ⟨m, hm⟩ := (P.2 _ _ (lowMap c bV) oY oC o' C.hom cc.left mC).2 n'
    refine ⟨cc.left, m, ?_, fun y => ?_⟩
    · rw [← Category.assoc, hccw, pullback.lift_snd]
    · apply mC.cart.1.hom_ext
      · rw [Category.assoc, ← hm, hn', Category.assoc, hu'l, ← hx₀, ← hcc y]
        rfl
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (x y), Category.assoc, Over.w (u' y)]
        simp
  · intro A _ _ v₁ v₂ hv s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 A (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) v₁ v₂ s' o'' m₁ m₂ z ?_ hz₁ hz₂
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₁ ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₂ ≫ C.hom) mY).1 k₂
    have hv' := hv =≫ sF
    simp only [Category.assoc] at hv'
    have hs₁ : ((v₁ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    have hs₂ : ((v₂ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]; exact hv'.symm
    have hfst := (Xo.rep (Sp A) s' inferInstance o'').unique ⟨hs₁, ⟨K₁⟩⟩ ⟨hs₂, ⟨K₂⟩⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hv
  · intro k _ v s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 (DualNumber k) (IsNoetherianRing.isNilpotent_nilradical _) v (constPt v) s' o'' m₁ m₂ z ?_ hz₁ hz₂
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsAlgebraic ℚ c.F := Algebra.IsAlgebraic.of_finite ℚ c.F
    have hcp : ∀ {W : Scheme.{0}} (w : C.left ⟶ W), constPt v ≫ w = constPt (v ≫ w) := fun w => by simp [constPt]
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom (constPt v) mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (constPt v ≫ C.hom) mY).1 k₂
    obtain ⟨K₁', -⟩ := objMap_congr (Category.assoc v C.hom (pullback.fst Xo.s sF)) K₁
    obtain ⟨K₂', -⟩ := objMap_congr (show (constPt v ≫ C.hom) ≫ pullback.fst Xo.s sF =
      constPt (v ≫ C.hom ≫ pullback.fst Xo.s sF) by simp [constPt]) K₂
    have hs₁ : s' = (v ≫ C.hom ≫ pullback.fst Xo.s sF) ≫ Xo.s := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    obtain ⟨o₂, ho₂⟩ := obj_congr hs₁ o''
    have hfst := Xo.unram k _ o₂ (ho₂ Xo.univ _ ⟨K₁'⟩) (ho₂ Xo.univ _ ⟨K₂'⟩)
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hcp]; exact hfst
    · simp only [Category.assoc]; rw [hcp]; exact GlobalTheory.Models.RankZero.eq_constPt_field _

end GlobalTheory.UCanonHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRingLinearHomSchemeLowerObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_baseSch : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) :=
  BaseSch.exists_baseSch_of_homScheme GlobalTheory.UCanonHom.homScheme_low

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRingLinearHomSchemeLowerObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localRing_linearHomScheme_lowerObject : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  first | exact @GlobalTheory.UCanon.exists_baseSch | exact GlobalTheory.UCanon.exists_baseSch | (intros; apply GlobalTheory.UCanon.exists_baseSch <;> assumption)
end
