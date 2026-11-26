module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstruction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbelia

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensor
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isFrame_tens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  intro X C _ V hV L L' u u' ⟨τ, hτg, hτf⟩ ⟨τ', hτ'g, hτ'f⟩
  dsimp only [IsFrame, IsGenOn, tens]
  refine ⟨fun T p ↦ res (inf_le_inf_left (V T) (inf_le_left : L.U p.1 ⊓ L'.U p.2 ≤ L.U p.1)) (τ T p.1) *
      res (inf_le_inf_left (V T) (inf_le_right : L.U p.1 ⊓ L'.U p.2 ≤ L'.U p.2)) (τ' T p.2), ?_, ?_⟩
  · intro T p q
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτg T p.1 q.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'g T p.2 q.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L.U p.1 ⊓ L.U q.1 := ⟨⟨hy.1.1, hy.1.2.1⟩, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ L'.U p.2 ⊓ L'.U q.2 := ⟨⟨hy.1.1, hy.1.2.2⟩, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ L.U p.1 ⊓ L'.U p.2 ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.2, hy.2⟩
    have m4 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := hy.1
    have m5 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U q.1 ⊓ L'.U q.2) := ⟨hy.1.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m3, gm_res (𝟙 X) y _ m4, gm_res (𝟙 X) y _ m5]
    rw [h1, h2]
    ac_rfl
  · intro T T' a p
    refine unit_ext fun y hy ↦ ?_
    have h1 := congrArg (gm (𝟙 X) y _) (hτf T T' a p.1)
    have h2 := congrArg (gm (𝟙 X) y _) (hτ'f T T' a p.2)
    have m1 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L.U p.1 := ⟨hy.1, hy.2.1⟩
    have m2 : (𝟙 X : X ⟶ X) y ∈ V T' ⊓ L'.U p.2 := ⟨hy.1, hy.2.2⟩
    have m3 : (𝟙 X : X ⟶ X) y ∈ V T ⊓ (L.U p.1 ⊓ L'.U p.2) := ⟨hV a hy.1, hy.2⟩
    simp only [map_mul, gm_res (𝟙 X) y _ m1] at h1
    simp only [map_mul, gm_res (𝟙 X) y _ m2] at h2
    simp only [map_mul, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ m1, gm_res (𝟙 X) y _ m2, gm_res (𝟙 X) y _ m3]
    rw [h1, h2]
    ac_rfl

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisLineBundleCechTensorStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsFrame L V hV u → IsFrame L' V hV u' → IsFrame (tens L L') V hV fun T T' a ↦ u T T' a * u' T T' a := by
  first | exact @GlobalTheory.LBObs.isFrame_tens | exact GlobalTheory.LBObs.isFrame_tens | (intros; apply GlobalTheory.LBObs.isFrame_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

structure CommonRef {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C']
    (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X) : Type where

  t : C

  t' : C'

  W : X.affineOpens
  le : W.1 ≤ opOf G t
  le' : W.1 ≤ opOf G' t'

namespace CommonRef

variable {X : Scheme.{0}} {C C' : Type} [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C']
  {G : C ⥤ AffOp X} {G' : C' ⥤ AffOp X}

instance : Category.{0} (CommonRef G G') where
  Hom a b := (a.t ⟶ b.t) × (a.t' ⟶ b.t') × PLift (b.W.1 ≤ a.W.1)
  id a := (𝟙 _, 𝟙 _, ⟨le_rfl⟩)
  comp f g := (f.1 ≫ g.1, f.2.1 ≫ g.2.1, ⟨g.2.2.down.trans f.2.2.down⟩)
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

instance : Quiver.IsThin (CommonRef G G') := fun a b =>
  ⟨fun f g => Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))⟩

variable (G G')

def fst : CommonRef G G' ⥤ C where
  obj d := d.t
  map f := f.1

def snd : CommonRef G G' ⥤ C' where
  obj d := d.t'
  map f := f.2.1

def opn : CommonRef G G' ⥤ AffOp X where
  obj d := Opposite.op d.W
  map f := (homOfLE f.2.2.down).op

def toFst : fst G G' ⋙ G ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G.obj d.t).unop from d.le)).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

def toSnd : snd G G' ⋙ G' ⟶ opn G G' where
  app d := (homOfLE (show d.W ≤ (G'.obj d.t').unop from d.le')).op
  naturality _ _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem isBas (hG : IsBas (opOf G)) (hG' : IsBas (opOf G')) : IsBas (opOf (opn G G')) := by
  refine ⟨fun x U hx => ?_, fun d₁ d₂ x U hx h₁ h₂ => ?_⟩
  · obtain ⟨t, hxt, htU⟩ := hG.1 x U hx
    obtain ⟨t', hxt', ht'⟩ := hG'.1 x (opOf G t ⊓ U) ⟨hxt, hx⟩
    exact ⟨⟨t, t', (G'.obj t').unop, ht'.trans inf_le_left, le_rfl⟩, hxt', ht'.trans inf_le_right⟩
  · have hx₃ : x ∈ U ⊓ d₁.W.1 ⊓ d₂.W.1 := ⟨⟨hx, h₁⟩, h₂⟩
    obtain ⟨t, a₁, a₂, hxt, htU⟩ := hG.2 d₁.t d₂.t x _ hx₃ (d₁.le h₁) (d₂.le h₂)
    obtain ⟨t', b₁, b₂, hxt', ht'⟩ := hG'.2 d₁.t' d₂.t' x (opOf G t) hxt (d₁.le' h₁) (d₂.le' h₂)
    refine ⟨⟨t, t', (G'.obj t').unop, ht', le_rfl⟩, ⟨(a₁.some, b₁.some, ⟨?_⟩)⟩, ⟨(a₂.some, b₂.some, ⟨?_⟩)⟩, hxt', ?_⟩
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_right))
    · exact ht'.trans (htU.trans inf_le_right)
    · exact ht'.trans (htU.trans (inf_le_left.trans inf_le_left))

end CommonRef

theorem common_refinement : ∀ (X : Scheme.{0}) (C C' : Type) [Category.{0} C] [Category.{0} C'] [Quiver.IsThin C] [Quiver.IsThin C'] (G : C ⥤ AffOp X) (G' : C' ⥤ AffOp X), IsBas (opOf G) → IsBas (opOf G') → ∃ (D : Type) (_ : Category.{0} D) (_ : Quiver.IsThin D) (K : D ⥤ AffOp X) (H : D ⥤ C) (H' : D ⥤ C'), Nonempty (H ⋙ G ⟶ K) ∧ Nonempty (H' ⋙ G' ⟶ K) ∧ IsBas (opOf K) :=
  fun X C C' _ _ _ _ G G' hG hG' =>
    ⟨CommonRef G G', inferInstance, inferInstance, CommonRef.opn G G', CommonRef.fst G G', CommonRef.snd G G',
      ⟨CommonRef.toFst G G'⟩, ⟨CommonRef.toSnd G G'⟩, CommonRef.isBas G G' hG hG'⟩

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigOneAddMul
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

section Additive

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
  [Algebra R₀ R₁]

theorem sig_mem_map (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (y : R₁ ⊗[R₀] B₀) :
    σ y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem sig_one_add_mul (hI : I ^ 2 = 0) (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (z z' : R₁ ⊗[R₀] B₀) : (1 + σ z) * (1 + σ z') = 1 + σ (z + z') := by
  have h0 : σ z * σ z' = 0 := by
    have hm := Ideal.mul_mem_mul (sig_mem_map α p hp σ hσ z) (sig_mem_map α p hp σ hσ z')
    rw [← Ideal.map_mul, ← sq, hI, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (Submodule.mem_bot _).1 hm
  rw [map_add (f := _)]
  linear_combination h0

end Additive

theorem isObU_mul : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u' c' → IsObU L α (fun T T' a ↦ u T T' a * u' T T' a) (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  refine ⟨fun T T' a ↦ v T T' a * v' T T' a, σ, z + z', fun T T' a ↦ ?_, hσ, (map_add _ _ _).symm,
    fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · simp only [Units.val_mul, map_mul, hv, hv']
  · have h1 := (hz T T' T'' a b).1
    have h2 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at h1 h2 ⊢
    change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (z.1 T T' T'' a b + z'.1 T T' T'' a b) = 0
    rw [map_add (f := _), h1, h2, add_zero]
  · have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    have hs : σ' T'' (z'.1 T T' T'' a b) = σ T'' (z'.1 T T' T'' a b) :=
      sig_unique α (L.p T'') (L.surj T'') _ _ (hσ' T'') (hσ T'') _
    rw [hs] at e'
    change _ = (1 + σ T'' (z.1 T T' T'' a b + z'.1 T T' T'' a b)) * _
    rw [← sig_one_add_mul hI α (L.p T'') (L.surj T'') (σ T'') (hσ T'')]
    simp only [Units.val_mul, map_mul]
    calc L.ρ b (v T T' a : L.B T') * L.ρ b (v' T T' a : L.B T') * ((v T' T'' b : L.B T'') * (v' T' T'' b : L.B T''))
        = (L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'')) *
            (L.ρ b (v' T T' a : L.B T') * (v' T' T'' b : L.B T'')) := by ring
      _ = _ := by rw [e, e']; ring

end GlobalTheory.LBObs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditive
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObL_tens : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L L' c c' hL hL'
  obtain ⟨C, _, _, G, hG, hLG⟩ := hL
  obtain ⟨C', _, _, G', hG', hLG'⟩ := hL'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hK⟩ := GlobalTheory.LBObs.common_refinement X₀ C C' G G' hG hG'
  have h₁ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G K H θ hLG
  have h₂ := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L' c' C' D G' K H' θ' hLG'
  obtain ⟨u, hu, hU⟩ := h₁
  obtain ⟨u', hu', hU'⟩ := h₂
  refine ⟨D, inferInstance, inferInstance, K, hK, fun T T' a ↦ u T T' a * u' T T' a,
    GlobalTheory.T.isLineBundleFrameOnBasis_lineBundleCechTensor X₀ D (opOf K) (opOf_le K) L L' u u' hu hu', ?_⟩
  rw [map_add (f := _)]
  exact GlobalTheory.LBObs.isObU_mul R R₀ I hI π hπ hk R₁ α D (K ⋙ OAff s₀) ((ofSys S).restrict K) u u' _ _ hU hU'

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionTensorAdditiveStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_tensor_additive : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L L' : LB X₀) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), IsObL S α L c → IsObL S α L' c' → IsObL S α (tens L L') (c + c') := by
  first | exact @GlobalTheory.LBObs.isObL_tens | exact GlobalTheory.LBObs.isObL_tens | (intros; apply GlobalTheory.LBObs.isObL_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

def unitOneSub {B : Type} [CommRing B] (w : B) (h : w * w = 0) : Bˣ where
  val := 1 - w
  inv := 1 + w
  val_inv := by linear_combination (-1 : B) * h
  inv_val := by linear_combination (-1 : B) * h

theorem unitOneSub_val {B : Type} [CommRing B] (w : B) (h : w * w = 0) : (unitOneSub w h : B) = 1 - w := rfl

theorem mul_eq_zero_of_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem lift_of_isObU_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u h
  obtain ⟨v, σ, z, hv, hσ, hz, hzv⟩ := h
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  have hw : ∀ (T T' : C) (a : T ⟶ T'), σ T' (f T T' a) ∈ I.map (algebraMap R (L.B T')) := fun T T' a ↦
    (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  refine ⟨fun T T' a ↦ v T T' a * unitOneSub (σ T' (f T T' a)) (mul_eq_zero_of_mem hI (hw T T' a) (hw T T' a)),
    fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · have h0 : L.p T' (σ T' (f T T' a)) = 0 := (L.ker T' _).2 (hw T T' a)
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one, h0, sub_zero, mul_one, hv]
    exact mul_one _
  · have hnat := (GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    have hs : σ T'' (z.1 T T' T'' a b) = L.ρ b (σ T' (f T T' a)) - σ T'' (f T T'' (a ≫ b)) + σ T'' (f T' T'' b) := by
      rw [← e, d1_apply, map_add (f := _), map_sub, hnat]
      rfl
    have hx := hw T T' a
    have hρx : L.ρ b (σ T' (f T T' a)) ∈ I.map (algebraMap R (L.B T'')) := by
      rw [hnat]
      exact (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
        (L.ker T'') (σ T'') (hσ T'')).1 _
    have hW := hw T T'' (a ≫ b)
    have hy := hw T' T'' b
    set x := L.ρ b (σ T' (f T T' a)) with hxdef
    set W := σ T'' (f T T'' (a ≫ b))
    set y := σ T'' (f T' T'' b)
    have hxx := mul_eq_zero_of_mem hI hρx hρx
    have hxy := mul_eq_zero_of_mem hI hρx hy
    have hyy := mul_eq_zero_of_mem hI hy hy
    have hWx := mul_eq_zero_of_mem hI hW hρx
    have hWy := mul_eq_zero_of_mem hI hW hy
    have key : (1 + (x - W + y)) * ((1 - x) * (1 - y)) = 1 - W := by
      linear_combination -hxx - hxy - hyy + hWx + hWy + y * hxx - y * hWx + y * hxy
    have hz' := (hzv T T' T'' a b).2
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one]
    rw [← hxdef]
    linear_combination (-(1 - x) * (1 - y)) * hz' + (-(v T T'' (a ≫ b) : L.B T'') * (1 - x) * (1 - y)) * hs
      - (v T T'' (a ≫ b) : L.B T'') * key

end GlobalTheory.LBLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftOfObstructionEqZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  first | exact @GlobalTheory.LBLift.lift_of_isObU_zero | exact GlobalTheory.LBLift.lift_of_isObU_zero | (intros; apply GlobalTheory.LBLift.lift_of_isObU_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasis
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBTrans

variable {X : Scheme.{0}}

theorem res_comp {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {U : X.Opens} (a b : Γ(X, U)ˣ)
    (h : ∀ x ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), x ∈ W ∧ res hW a = res hW b) : a = b := by
  let J := {W : X.Opens // ∃ hW : W ≤ U, res hW a = res hW b}
  have hc : U ≤ ⨆ j : J, j.1 := fun x hx => by
    obtain ⟨W, hW, hx', e⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, e⟩, hx'⟩
  apply Units.ext
  refine X.sheaf.eq_of_locally_eq' (fun j : J => j.1) U (fun j => homOfLE j.2.1) hc _ _ (fun j => ?_)
  exact congrArg Units.val j.2.2

theorem glue_units {J : Type} (V : X.Opens) (W : J → X.Opens) (hW : ∀ i, W i ≤ V) (hc : V ≤ iSup W)
    (u : ∀ i, Γ(X, W i)ˣ)
    (hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, res (hW i) s = u i := by
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => (u i).val) (fun i j => congrArg Units.val (hh i j))
  obtain ⟨s', hs', -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc
    (fun i => ((u i)⁻¹).val) (fun i j => congrArg Units.val
      (show res (inf_le_left : W i ⊓ W j ≤ W i) (u i)⁻¹ = res inf_le_right (u j)⁻¹ by
        rw [map_inv, map_inv, hh]))
  have e : (show Γ(X, V) from s) * (show Γ(X, V) from s') = 1 := by
    apply X.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
    intro i
    show (X.presheaf.map (homOfLE (hW i)).op).hom _ = (X.presheaf.map (homOfLE (hW i)).op).hom _
    rw [map_mul, map_one]
    exact (congrArg₂ (· * ·) (hs i) (hs' i)).trans (u i).mul_inv
  exact ⟨⟨s, s', e, (mul_comm _ _).trans e⟩, fun i => Units.ext (hs i)⟩

variable {C : Type} [Category.{0} C] {V : C → X.Opens} {hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T}
  {u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ}

theorem res_quot (hu : IsCoc V hV u) {T₁ T₂ T T'' : C} (a : T₁ ⟶ T) (b : T₂ ⟶ T) (c : T ⟶ T'') :
    res (hV c) (u T₂ T b * (u T₁ T a)⁻¹) = u T₂ T'' (b ≫ c) * (u T₁ T'' (a ≫ c))⁻¹ := by
  rw [hu b c, hu a c, map_mul, map_inv, mul_inv_rev, _root_.mul_assoc, mul_inv_cancel_left]

theorem transition_units (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [thin : Quiver.IsThin C]
    (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) :
    IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ,
      ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  intro hB hu T₁ T₂
  have sub : ∀ {T T' : C} (f f' : T ⟶ T'), f = f' := fun f f' => @Subsingleton.elim _ (thin _ _) f f'
  let J := {T : C // Nonempty (T₁ ⟶ T) ∧ Nonempty (T₂ ⟶ T)}
  let W : J → X.Opens := fun j => V j.1
  have hW : ∀ j : J, W j ≤ V T₁ ⊓ V T₂ := fun j => le_inf (hV j.2.1.some) (hV j.2.2.some)
  let w : ∀ j : J, Γ(X, W j)ˣ := fun j => u T₂ j.1 j.2.2.some * (u T₁ j.1 j.2.1.some)⁻¹
  have hw : ∀ (j : J) (a : T₁ ⟶ j.1) (b : T₂ ⟶ j.1), w j = u T₂ j.1 b * (u T₁ j.1 a)⁻¹ :=
    fun j a b => by simp only [w]; rw [sub j.2.2.some b, sub j.2.1.some a]
  have hc : V T₁ ⊓ V T₂ ≤ iSup W := fun x hx => by
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨T, ⟨a⟩, ⟨b⟩⟩, hxT⟩
  have hh : ∀ i j, res (inf_le_left : W i ⊓ W j ≤ W i) (w i) = res inf_le_right (w j) := by
    intro i j
    apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨c⟩, ⟨d⟩, hxT, hle⟩ := hB.2 i.1 j.1 x (W i ⊓ W j) hx hx.1 hx.2
    refine ⟨V T, hle, hxT, ?_⟩
    rw [res_comp, res_comp]
    have e1 := res_quot hu i.2.1.some i.2.2.some c
    have e2 := res_quot hu j.2.1.some j.2.2.some d
    change res (hV c) (w i) = res (hV d) (w j)
    simp only [w]
    rw [e1, e2, sub (i.2.1.some ≫ c) (j.2.1.some ≫ d), sub (i.2.2.some ≫ c) (j.2.2.some ≫ d)]
  obtain ⟨s, hs⟩ := glue_units (V T₁ ⊓ V T₂) W hW hc w hh
  have key : ∀ (g : Γ(X, V T₁ ⊓ V T₂)ˣ) (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T),
      res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b ↔
        res (le_inf (hV a) (hV b)) g = u T₂ T b * (u T₁ T a)⁻¹ :=
    fun g T a b => (eq_mul_inv_iff_mul_eq).symm
  refine ⟨s, fun T a b => (key s T a b).2 ?_, fun g hg => ?_⟩
  · have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this
  · apply units_eq_of_local
    intro x hx
    obtain ⟨T, ⟨a⟩, ⟨b⟩, hxT, -⟩ := hB.2 T₁ T₂ x (V T₁ ⊓ V T₂) hx hx.1 hx.2
    refine ⟨V T, le_inf (hV a) (hV b), hxT, ?_⟩
    rw [(key g T a b).1 (hg T a b)]
    have := hs ⟨T, ⟨a⟩, ⟨b⟩⟩
    rw [hw ⟨T, ⟨a⟩, ⟨b⟩⟩ a b] at this
    exact this.symm

end GlobalTheory.LBTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTransitionUnitsCocycleThinBasisStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∀ T₁ T₂ : C, ∃! g : Γ(X, V T₁ ⊓ V T₂)ˣ, ∀ (T : C) (a : T₁ ⟶ T) (b : T₂ ⟶ T), res (le_inf (hV a) (hV b)) g * u T₁ T a = u T₂ T b := by
  first | exact @GlobalTheory.LBTrans.transition_units | exact GlobalTheory.LBTrans.transition_units | (intros; apply GlobalTheory.LBTrans.transition_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycle
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThinGlue

variable {X : Scheme.{0}}

theorem res_res {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem units_eq_of_local {W : X.Opens} (x y : Γ(X, W)ˣ)
    (h : ∀ p ∈ W, ∃ (W' : X.Opens) (hW : W' ≤ W), p ∈ W' ∧ res hW x = res hW y) : x = y := by
  choose W' hW hp hxy using h
  ext
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun p : W => W' p.1 p.2) W (fun p => homOfLE (hW p.1 p.2)) ?_ _ _ ?_
  · intro p hpW
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hpW⟩, hp _ hpW⟩
  · intro p
    have := congrArg Units.val (hxy p.1 p.2)
    exact this

end GlobalTheory.ThinGlue

namespace GlobalTheory.ThinGlue

theorem exists_lb_frame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ),
    IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  intro X C _ V hV _ u hB hC
  have hE := fun T₁ T₂ => GlobalTheory.T.existsUnique_transition_units_cocycle_thin_basis X C V hV u hB hC T₁ T₂
  choose g hg using fun T₁ T₂ => (hE T₁ T₂).exists
  have key : ∀ (T₁ T₂ S : C) (a : T₁ ⟶ S) (b : T₂ ⟶ S) (h : V S ≤ V T₁ ⊓ V T₂),
      res h (g T₁ T₂) * u T₁ S a = u T₂ S b := fun T₁ T₂ S a b _ => hg T₁ T₂ S a b
  have bas2 : ∀ (i j : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S, ⟨a⟩, ⟨b⟩, hpS, hSW⟩ := hB.2 i j p W hp (hW hp).1 (hW hp).2
    exact ⟨V S, hSW, hpS, h S a b hSW⟩
  have bas3 : ∀ (i j k : C) (W : X.Opens) (hW : W ≤ V i ⊓ V j ⊓ V k) (x y : Γ(X, W)ˣ),
      (∀ (S : C) (_ : i ⟶ S) (_ : j ⟶ S) (_ : k ⟶ S) (hS : V S ≤ W), res hS x = res hS y) → x = y := by
    intro i j k W hW x y h
    refine units_eq_of_local x y fun p hp => ?_
    obtain ⟨S₀, ⟨a⟩, ⟨b⟩, hpS₀, hS₀W⟩ := hB.2 i j p W hp (hW hp).1.1 (hW hp).1.2
    obtain ⟨S, ⟨c⟩, ⟨d⟩, hpS, hSW⟩ := hB.2 S₀ k p W hp hpS₀ (hW hp).2
    exact ⟨V S, hSW, hpS, h S (a ≫ c) (b ≫ c) d hSW⟩
  have gself : ∀ T, g T T = 1 := fun T =>
    (hE T T).unique (hg T T) (fun S a b => by rw [Subsingleton.elim a b, map_one, _root_.one_mul])
  let L : LB X := ⟨C, V, g⟩
  refine ⟨L, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine eq_top_iff.2 fun p _ => ?_
    obtain ⟨t, hp, _⟩ := hB.1 p ⊤ trivial
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hp⟩
  · intro T
    show res _ (g T T) = 1
    rw [gself, map_one]
  · intro i j k
    refine bas3 i j k _ le_rfl _ _ fun S a b c hS => ?_
    show res hS (res _ (g i j) * res _ (g j k)) = res hS (res _ (g i k))
    simp only [map_mul, res_res]
    have e1 := key i j S a b (hS.trans inf_le_left)
    have e2 := key j k S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    have e3 := key i k S a c (hS.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    apply mul_right_cancel (b := u i S a)
    rw [e3, mul_comm (res _ (g i j)), _root_.mul_assoc, e1, e2]
  · refine ⟨fun T m => res (le_of_eq (inf_comm _ _)) (g m T), fun T => ?_, ?_⟩
    · intro m m'
      refine bas3 T m m' _ le_rfl _ _ fun S a b c hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (g m m') * res _ (res _ (g m' T)))
      simp only [map_mul, res_res]
      have e1 := key m T S b a (hS.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
      have e2 := key m m' S b c (hS.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      have e3 := key m' T S c a (hS.trans (le_inf inf_le_right (inf_le_left.trans inf_le_left)))
      apply mul_right_cancel (b := u m S b)
      rw [e1, mul_comm (res _ (g m m')), _root_.mul_assoc, e2, e3]
    · intro T T' a m
      refine bas2 T' m _ le_rfl _ _ fun S c d hS => ?_
      show res hS (res _ (res _ (g m T))) = res hS (res _ (u T T' a) * res _ (g m T'))
      simp only [map_mul, res_res]
      have e1 := key m T S d (a ≫ c) (hS.trans (le_inf inf_le_right ((inf_le_left.trans (hV a)))))
      have e2 := key m T' S d c (hS.trans (le_inf inf_le_right inf_le_left))
      have e3 := hC a c
      apply mul_right_cancel (b := u m S d)
      rw [e1, _root_.mul_assoc, e2, e3]

end GlobalTheory.ThinGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfThinBasisCocycleStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → IsCoc V hV u → ∃ L : LB X, L.IsLB ∧ IsFrame L V hV u := by
  first | exact @GlobalTheory.ThinGlue.exists_lb_frame | exact GlobalTheory.ThinGlue.exists_lb_frame | (intros; apply GlobalTheory.ThinGlue.exists_lb_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBasOfPreimageEq
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isBas_of_preimage_eq (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (C : Type)
    [Category.{0} C] (V : C → X.Opens) (V₀ : C → X₀.Opens) (hV : ∀ T, i ⁻¹ᵁ V T = V₀ T) (h : IsBas V₀) :
    IsBas V := by
  have hle : ∀ (t : C) (U : X.Opens), V₀ t ≤ i ⁻¹ᵁ U → V t ≤ U := by
    intro t U htU z hz
    obtain ⟨w, rfl⟩ := i.surjective z
    have hw : w ∈ V₀ t := by rw [← hV t]; exact hz
    exact htU hw
  have hmem : ∀ (t : C) (y : X₀), y ∈ V₀ t → i y ∈ V t := by
    intro t y hy
    rw [← hV t] at hy
    exact hy
  have hmem' : ∀ (t : C) (y : X₀), i y ∈ V t → y ∈ V₀ t := by
    intro t y hy
    rw [← hV t]
    exact hy
  refine ⟨fun x U hx ↦ ?_, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t, hyt, htU⟩ := h.1 y (i ⁻¹ᵁ U) hx
    exact ⟨t, hmem t y hyt, hle t U htU⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t₃, a₁, a₂, hy₃, h₃U⟩ := h.2 t₁ t₂ y (i ⁻¹ᵁ U) hx (hmem' t₁ y h₁) (hmem' t₂ y h₂)
    exact ⟨t₃, a₁, a₂, hmem t₃ y hy₃, hle t₃ U h₃U⟩

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfIsFrame
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBObs

theorem gm_id_res' {X : Scheme.{0}} {U V : X.Opens} (hle : V ≤ U) {x : X} (hx : x ∈ V) (a : Γ(X, U)ˣ) :
    gm (𝟙 X) x V (ReciprocityTheory.ChartRestriction.G.Semi.res hle a) = gm (𝟙 X) x U a :=
  gm_res (𝟙 X) x hle hx a

theorem lbIso_of_isFrame : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) [Quiver.IsThin C] (L L' : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), IsBas V → L.IsLB → L'.IsLB → IsFrame L V hV u → IsFrame L' V hV u → LBIso L L' := by
  intro X C _ V hV _ L L' u hB _ _ hF hF'
  obtain ⟨τ, hτg, hτ⟩ := hF
  obtain ⟨τ', hτ'g, hτ'⟩ := hF'

  have e : ∀ (T T' : C) (a : T ⟶ T') (m : L.ι) (x : X) (hx : x ∈ V T' ⊓ L.U m),
      gm (𝟙 X) x _ (τ T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L.U m)) (hτ T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h
  have e' : ∀ (T T' : C) (a : T ⟶ T') (m : L'.ι) (x : X) (hx : x ∈ V T' ⊓ L'.U m),
      gm (𝟙 X) x _ (τ' T m) = gm (𝟙 X) x _ (u T T' a) * gm (𝟙 X) x _ (τ' T' m) := by
    intro T T' a m x hx
    have h := congrArg (gm (𝟙 X) x (V T' ⊓ L'.U m)) (hτ' T T' a m)
    rwa [map_mul, gm_id_res' _ hx, gm_id_res' _ hx] at h

  have key : ∀ (T₁ T₂ : C) (m : L.ι) (m' : L'.ι) (x : X), x ∈ V T₁ → x ∈ V T₂ → x ∈ L.U m → x ∈ L'.U m' →
      gm (𝟙 X) x (V T₁ ⊓ L'.U m') (τ' T₁ m') / gm (𝟙 X) x (V T₁ ⊓ L.U m) (τ T₁ m) =
        gm (𝟙 X) x (V T₂ ⊓ L'.U m') (τ' T₂ m') / gm (𝟙 X) x (V T₂ ⊓ L.U m) (τ T₂ m) := by
    intro T₁ T₂ m m' x h1 h2 hm hm'
    obtain ⟨T₃, ⟨a⟩, ⟨b⟩, h3, -⟩ := hB.2 T₁ T₂ x ⊤ trivial h1 h2
    rw [e T₁ T₃ a m x ⟨h3, hm⟩, e' T₁ T₃ a m' x ⟨h3, hm'⟩, e T₂ T₃ b m x ⟨h3, hm⟩, e' T₂ T₃ b m' x ⟨h3, hm'⟩,
      mul_div_mul_left_eq_div, mul_div_mul_left_eq_div]

  have hglue : ∀ p : L'.ι × L.ι, ∃ s : Γ(X, L'.U p.1 ⊓ L.U p.2)ˣ, ∀ (T : C) (x : X),
      x ∈ V T → x ∈ L'.U p.1 ⊓ L.U p.2 →
        gm (𝟙 X) x _ s = gm (𝟙 X) x (V T ⊓ L'.U p.1) (τ' T p.1) / gm (𝟙 X) x (V T ⊓ L.U p.2) (τ T p.2) := by
    intro p
    obtain ⟨s, hs⟩ := glue_unit (L'.U p.1 ⊓ L.U p.2) (fun T => V T ⊓ (L'.U p.1 ⊓ L.U p.2)) (fun T => inf_le_right)
      (fun x hx => by
        obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨T, hT, hx⟩)
      (fun T => ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_left) (τ' T p.1) /
        ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_inf_left (V T) inf_le_right) (τ T p.2))
      (fun T₁ T₂ x hx => by
        simp only [map_div]
        rw [gm_id_res' _ hx.1, gm_id_res' _ hx.1, gm_id_res' _ hx.2, gm_id_res' _ hx.2]
        exact key T₁ T₂ p.2 p.1 x hx.1.1 hx.2.1 hx.1.2.2 hx.1.2.1)
    refine ⟨s, fun T x hT hx => ?_⟩
    have h := congrArg (gm (𝟙 X) x (V T ⊓ (L'.U p.1 ⊓ L.U p.2))) (hs T)
    simp only [map_div] at h
    have hTx : x ∈ V T ⊓ (L'.U p.1 ⊓ L.U p.2) := ⟨hT, hx⟩
    rwa [gm_id_res' _ hTx, gm_id_res' _ hTx, gm_id_res' _ hTx] at h
  choose w hw using hglue
  refine ⟨⟨w⟩, fun p q => ?_⟩
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.unit_ext
  intro x hx
  obtain ⟨T, hT, -⟩ := hB.1 x ⊤ trivial
  have hp : x ∈ L'.U p.1 ⊓ L.U p.2 := hx.1
  have hq : x ∈ L'.U q.1 ⊓ L.U q.2 := hx.2

  have g1 := congrArg (gm (𝟙 X) x _) (hτ'g T p.1 q.1)
  have g2 := congrArg (gm (𝟙 X) x _) (hτg T p.2 q.2)
  have hx1 : x ∈ V T ⊓ L'.U p.1 ⊓ L'.U q.1 := ⟨⟨hT, hp.1⟩, hq.1⟩
  have hx2 : x ∈ V T ⊓ L.U p.2 ⊓ L.U q.2 := ⟨⟨hT, hp.2⟩, hq.2⟩
  rw [map_mul, gm_id_res' _ hx1, gm_id_res' _ hx1, gm_id_res' _ hx1] at g1
  rw [map_mul, gm_id_res' _ hx2, gm_id_res' _ hx2, gm_id_res' _ hx2] at g2
  have hwp : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U p) (w p)) =
      gm (𝟙 X) x ((L'.div L).U p) (w p) := gm_id_res' _ hx _
  have hwq : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q)
      (ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : (L'.div L).U p ⊓ (L'.div L).U q ≤ (L'.div L).U q) (w q)) =
      gm (𝟙 X) x ((L'.div L).U q) (w q) := gm_id_res' _ hx _
  have hx' : x ∈ L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2) := hx
  have hg : gm (𝟙 X) x ((L'.div L).U p ⊓ (L'.div L).U q) ((L'.div L).g p q) =
      gm (𝟙 X) x (L'.U p.1 ⊓ L'.U q.1) (L'.g p.1 q.1) * (gm (𝟙 X) x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := by
    show gm (𝟙 X) x (L'.U p.1 ⊓ L.U p.2 ⊓ (L'.U q.1 ⊓ L.U q.2))
      (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L'.g p.1 q.1) * (ReciprocityTheory.ChartRestriction.G.Semi.res _ (L.g p.2 q.2))⁻¹) = _
    rw [map_mul, map_inv, gm_id_res' _ hx', gm_id_res' _ hx']
  rw [map_mul, hwp, hwq, hg]
  erw [hw p T x hT hp, hw q T x hT hq]
  rw [g1, g2]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end GlobalTheory.LBObs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := GlobalTheory.T.unitCocycle_lift_of_obstruction_eq_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := GlobalTheory.T.exists_charts_squareZero_presented_scheme R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := GlobalTheory.T.exists_lineBundle_of_thinBasis_cocycle X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  first | exact @GlobalTheory.LBObs.exists_lift_of_isObL_zero | exact GlobalTheory.LBObs.exists_lift_of_isObL_zero | (intros; apply GlobalTheory.LBObs.exists_lift_of_isObL_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullback
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqPull

theorem tensor_isPullback {S : Scheme.{0}} (X Y : Over S) :
    IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom := by
  rw [Over.fst_left, Over.snd_left]
  exact IsPullback.of_hasPullback _ _

theorem sq_of_grpPullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  intro S S₀ f B _ B₀ _ i h
  obtain ⟨hP, hM⟩ := h
  let T : Over S₀ := B₀ ⊗ B₀
  have hw : ∀ x : T ⟶ B₀, (x.left ≫ i) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
    intro x
    rw [Category.assoc, hP.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((fst B₀ B₀).left ≫ i) (hw _)
  let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk ((snd B₀ B₀).left ≫ i) (hw _)
  have h1 : (lift x₀ y₀).left ≫ (fst B B).left = (fst B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_fst]; rfl
  have h2 : (lift x₀ y₀).left ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
    rw [← Over.comp_left, lift_snd]; rfl
  refine ⟨(lift x₀ y₀).left, ?_, ?_, h1, h2⟩
  · have outer : IsPullback ((snd B₀ B₀).left ≫ i) (fst B₀ B₀).left B.hom (B₀.hom ≫ f) :=
      IsPullback.paste_horiz (tensor_isPullback B₀ B₀).flip hP
    have sq : IsPullback (lift x₀ y₀).left (fst B₀ B₀).left (fst B B).left i := by
      refine IsPullback.of_right (h₁₂ := (snd B B).left) (v₁₃ := B.hom) (h₂₂ := B.hom) ?_ h1
        (tensor_isPullback B B).flip
      rw [h2, hP.w]
      exact outer
    exact IsPullback.paste_vert sq hP
  · have := hM T (fst B₀ B₀) (snd B₀ B₀) x₀ y₀ rfl rfl
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left] at this
    exact this

end GlobalTheory.SqPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareGroupSchemePullbackStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_group_scheme_pullback : ∀ (S S₀ : Scheme.{0}) (f : S₀ ⟶ S) (B : Over S) [GrpObj B] (B₀ : Over S₀) [GrpObj B₀] (i : B₀.left ⟶ B.left), IsGrpPullback B₀ B f i → ∃ k : (B₀ ⊗ B₀).left ⟶ (B ⊗ B).left, IsPullback k (B₀ ⊗ B₀).hom (B ⊗ B).hom f ∧ k ≫ (μ[B]).left = (μ[B₀]).left ≫ i ∧ k ≫ (fst B B).left = (fst B₀ B₀).left ≫ i ∧ k ≫ (snd B B).left = (snd B₀ B₀).left ≫ i := by
  first | exact @GlobalTheory.SqPull.sq_of_grpPullback | exact GlobalTheory.SqPull.sq_of_grpPullback | (intros; apply GlobalTheory.SqPull.sq_of_grpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LBObs.exists_lift_of_lam_iso_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ _ π hπ hI B _ B₀ _ _ i i₂ hB hgp hsq P L₀ hP hL₀ hΛ
  have hab : IsAbelianScheme B₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hgp
  obtain ⟨g, hdim⟩ := GlobalTheory.AbelianDim.exists_relDim R₀ B₀ hab
  have hsm : Smooth B.hom := hB.smooth
  obtain ⟨R₁, _, _, ⟨α⟩⟩ := GlobalTheory.Obs.exists_aug R R₀ (RingHom.ker π) hI π hπ rfl
  have hpb : IsPullback i B₀.hom B.hom (spMap π) := hgp.1
  obtain ⟨S, ⟨Pr⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl B₀.left B₀.hom B.left B.hom i hpb hsm
  obtain ⟨k, hkp, hkμ, hkf, hks⟩ := GlobalTheory.T.exists_square_group_scheme_pullback (Sp R) (Sp R₀) (spMap π) B B₀ i hgp
  have hki : i₂ = k := (GlobalTheory.SqPull.tensor_isPullback B B).hom_ext (hsq.1.trans hkf.symm) (hsq.2.trans hks.symm)
  subst hki
  have hsm2 : Smooth (B ⊗ B).hom := inferInstanceAs (Smooth (Limits.pullback.fst B.hom B.hom ≫ B.hom))
  obtain ⟨S₂, ⟨P₂⟩⟩ := GlobalTheory.LiftSys.exists_sys_presents R R₀ (RingHom.ker π) hI π hπ rfl (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom (B ⊗ B).left
    (B ⊗ B).hom i₂ hkp hsm2
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S L₀ hL₀
  have h1 : (L₀.pull (fst B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h2 : (L₀.pull (snd B₀ B₀).left).IsLB := pull_isLB hL₀ _
  have h3 : (P.pull i₂).IsLB := pull_isLB hP _
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h1
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_lineBundleLiftObstruction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ h2
  have hc₃ : IsObL S₂ α (P.pull i₂) 0 :=
    GlobalTheory.T.lineBundle_obstruction_zero_of_restriction R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ (B ⊗ B).left (B ⊗ B).hom i₂ P₂ P hkp hP
  have hc₁₂ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ c₁ c₂ hc₁ hc₂
  have hc₁₂₃ := GlobalTheory.T.lineBundleLiftObstruction_tensor_additive R R₀ _ hI π hπ rfl R₁ α (B₀ ⊗ B₀).left (B₀ ⊗ B₀).hom S₂ _ _ _ _ hc₁₂ hc₃
  rw [add_zero] at hc₁₂₃

  have hz : GlobalTheory.CechPic.pull (1 : B₀ ⊗ B₀ ⟶ B₀).left (cls L₀ hL₀) = 0 := by
    rw [Hom.one_def, Over.comp_left, GlobalTheory.CechPic.pull_comp]
    have h0 : cls (L₀.pull (η[B₀]).left) (pull_isLB hL₀ _) = 0 :=
      (cls_eq_zero_iff _).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R₀) (pull_isLB hL₀ _))
    rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), h0, map_zero]
  have hmul : (fst B₀ B₀ * snd B₀ B₀ : B₀ ⊗ B₀ ⟶ B₀) = μ[B₀] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hLam : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hcube : cls (abelian₂ B₀ L₀) hLam = lam (cls L₀ hL₀) (fst B₀ B₀) (snd B₀ B₀) :=
    GlobalTheory.CechPic.cls_cube_two hL₀ (fst B₀ B₀) (snd B₀ B₀) hLam
  have hΛc : cls _ hLam = cls _ h3 := (cls_eq_iff hLam h3).2 hΛ
  have hiso : LBIso (tens (tens (L₀.pull (fst B₀ B₀).left) (L₀.pull (snd B₀ B₀).left)) (P.pull i₂))
      (L₀.pull (μ[B₀]).left) := by
    refine (cls_eq_iff (isLB_tens (isLB_tens h1 h2) h3) (pull_isLB hL₀ _)).1 ?_
    rw [cls_tens (isLB_tens h1 h2) h3, cls_tens h1 h2, ← hΛc, hcube, lam, hmul, hz, cls_pull hL₀, cls_pull hL₀,
      cls_pull hL₀]
    abel
  have hpb2 : IsPullback i₂ (B₀ ⊗ B₀).hom (B ⊗ B).hom (spMap π) := hkp
  have nat : ∀ (f₀ : (B₀ ⊗ B₀) ⟶ B₀) (f : (B ⊗ B) ⟶ B), i₂ ≫ f.left = f₀.left ≫ i →
      ∀ (L' : LB (B₀ ⊗ B₀).left) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff (B₀ ⊗ B₀).hom))), L'.IsLB →
        LBIso L' (L₀.pull f₀.left) → IsObL S₂ α L' c' → IsExtendedPullbackDegTwo R₁ (overW f₀) c c' := by
    intro f₀ f hf L' c' hL' hiso hob
    obtain ⟨l, hl, hn⟩ := GlobalTheory.Obs.exists_chart_lifts R R₀ _ hI π hπ rfl B₀.left (B₀ ⊗ B₀).left B.left (B ⊗ B).left
      B₀.hom (B₀ ⊗ B₀).hom B.hom (B ⊗ B).hom i i₂ hpb hkp S S₂ Pr P₂ f₀.left (overW f₀) f.left (Over.w f) hf
    exact GlobalTheory.T.lineBundleLiftObstruction_natural R R₀ _ hI π hπ rfl R₁ α B₀.left (B₀ ⊗ B₀).left B₀.hom (B₀ ⊗ B₀).hom S S₂ f₀.left (overW f₀)
      l hl hn L₀ L' c c' hL₀ hL' hiso hc hob
  have eμ := nat μ[B₀] μ[B] hkμ _ (c₁ + c₂) (isLB_tens (isLB_tens h1 h2) h3) hiso hc₁₂₃
  have e1 := nat (fst B₀ B₀) (fst B B) hkf _ c₁ h1 (GlobalTheory.PolBaseChange.lbIso_refl h1) hc₁
  have e2 := nat (snd B₀ B₀) (snd B B) hks _ c₂ h2 (GlobalTheory.PolBaseChange.lbIso_refl h2) hc₂
  have h0 : c = 0 := GlobalTheory.T.primitive_degree_two_any_ring R₀ R₁ α.q α.sq B₀ g hab hdim c c₁ c₂ eμ e1 e2
  subst h0
  exact GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero R R₀ _ hI π hπ rfl R₁ α B₀.left B₀.hom S B.left B.hom i Pr L₀ hpb hL₀ hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (B : Over (Sp R)) [GrpObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left) (L₀ : LB B₀.left), P.IsLB → L₀.IsLB → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → ∃ L : LB B.left, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  first | exact @GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | exact GlobalTheory.LBObs.exists_lift_of_lam_iso_pull | (intros; apply GlobalTheory.LBObs.exists_lift_of_lam_iso_pull <;> assumption)
end
