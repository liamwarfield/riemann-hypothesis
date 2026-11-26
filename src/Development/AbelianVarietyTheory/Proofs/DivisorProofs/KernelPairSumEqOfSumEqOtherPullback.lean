module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev sqR (N : Near π G) : Over (Sp R) :=
  Over.mk ((Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π)

def fstU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))))))

def sndU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (snd (Desc.UT N) (Desc.UT N)))))))

def pairU (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  (lift (fstU N) (sndU N)).left

abbrev VT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) : (Desc.UT N ⊗ Desc.UT N).left.Opens :=
  pairU N ⁻¹ᵁ V

theorem pairU_over (N : Near π G) :
    pairU N ≫ (N.U ⊗ N.U).hom = (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π :=
  Over.w (lift (fstU N) (sndU N))

def mT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : (VT N V).toScheme ⟶ (Desc.UT N).left :=
  pullback.lift ((pairU N ∣_ V) ≫ m) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (by
    have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
    refine (Category.assoc _ _ _).trans ?_
    rw [hm, ← Category.assoc, e, Category.assoc, pairU_over, Category.assoc])

variable [GrpObj G]

def trip (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N ⟶ (Over.pullback p).obj G :=
  (snd _ _ ≫ Desc.emb N p hp)⁻¹ * (fst _ _ ≫ Desc.sum N p hp)

def Pk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Over (pullback π π) :=
  Over.mk (pullback.snd (Desc.emb N p hp).left (trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom)

def dP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.fst _ _) (by
    show pullback.fst _ _ ≫ (Desc.UT N).hom = pullback.snd _ _ ≫ _
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, pullback.condition, Category.assoc, Over.w (trip N p hp)])

def abP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cdP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  lift (cP N p hp) (dP N p hp)

def Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (V : (N.U ⊗ N.U).left.Opens) :
    (Pk N p hp).left.Opens :=
  (abP N p hp).left ⁻¹ᵁ VT N V ⊓ (cdP N p hp).left ⁻¹ᵁ VT N V

def q3 (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _) rfl

theorem abP_eq (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp = q3 N p hp ≫ fst _ _ := Over.OverMorphism.ext rfl

theorem indicatorIdempotent_eq_add_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    cP N p hp = q3 N p hp ≫ snd _ _ := Over.OverMorphism.ext rfl

theorem dP_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    dP N p hp ≫ Desc.emb N p hp = q3 N p hp ≫ trip N p hp := Over.OverMorphism.ext pullback.condition

theorem abP_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp ≫ Desc.sum N p hp = cdP N p hp ≫ Desc.sum N p hp := by
  have e4 : cdP N p hp ≫ Desc.sum N p hp = (cP N p hp ≫ Desc.emb N p hp) * (dP N p hp ≫ Desc.emb N p hp) := by
    rw [cdP, Desc.sum, comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  rw [e4, dP_emb, trip, comp_mul, GrpObj.comp_inv, indicatorIdempotent_eq_add_sum, abP_eq]
  simp only [Category.assoc]
  exact (mul_inv_cancel_left _ _).symm

theorem exists_lift (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (Z : Scheme.{0})
    (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left) (h : g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left) :
    ∃ z : Z ⟶ (Pk N p hp).left, z ≫ (abP N p hp).left = g ∧ z ≫ (cdP N p hp).left = g' := by
  let FinalForm : Over (pullback π π) := Over.mk (g ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  have hw : g' ≫ (Desc.UT N ⊗ Desc.UT N).hom = g ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Over.w (Desc.sum N p hp), ← Category.assoc, ← h, Category.assoc]
  let a : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g rfl
  let b : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g' hw
  have hab : a ≫ Desc.sum N p hp = b ≫ Desc.sum N p hp := Over.OverMorphism.ext h
  let t : FinalForm ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N := lift a (b ≫ fst _ _)
  have ht : (b ≫ snd _ _) ≫ Desc.emb N p hp = t ≫ trip N p hp := by
    rw [trip, comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_snd, ← Category.assoc t, lift_fst, hab, Desc.sum,
      comp_mul]
    simp only [Category.assoc]
    exact (inv_mul_cancel_left _ _).symm
  let zo : FinalForm ⟶ Pk N p hp := Over.homMk (pullback.lift (b ≫ snd _ _).left t.left (congrArg Over.Hom.left ht))
    (by show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [← Category.assoc, pullback.lift_snd]; exact Over.w t)
  have h1 : zo ≫ abP N p hp = a := by rw [abP_eq, ← Category.assoc]; exact (congrArg (· ≫ fst _ _)
    (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_fst _ _)
  have h2 : zo ≫ cdP N p hp = b := by
    have hc : zo ≫ cP N p hp = b ≫ fst _ _ := by
      rw [indicatorIdempotent_eq_add_sum, ← Category.assoc]; exact (congrArg (· ≫ snd _ _)
        (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_snd _ _)
    have hd : zo ≫ dP N p hp = b ≫ snd _ _ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    rw [cdP, comp_lift, hc, hd]
    exact (lift_comp_fst_snd b)
  exact ⟨zo.left, congrArg Over.Hom.left h1, congrArg Over.Hom.left h2⟩

end GlobalTheory.Mum.DescKP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev prU (N : Near π G) : (Desc.UT N).left ⟶ N.U.left := pullback.fst _ _

def liftU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : Y ⟶ (Desc.UT N).left :=
  pullback.lift x t h

theorem liftU_prU (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ prU N = x :=
  pullback.lift_fst _ _ _

theorem liftU_hom (N : Near π G) {Y : Scheme.{0}} (x : Y ⟶ N.U.left) (t : Y ⟶ pullback π π)
    (h : x ≫ N.U.hom = t ≫ pullback.fst π π ≫ π) : liftU N x t h ≫ (Desc.UT N).hom = t :=
  pullback.lift_snd _ _ _

theorem UT_ext (N : Near π G) {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N).left) (h1 : f ≫ prU N = g ≫ prU N)
    (h2 : f ≫ (Desc.UT N).hom = g ≫ (Desc.UT N).hom) : f = g :=
  pullback.hom_ext h1 h2

theorem pairU_fst (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_fst (fstU N) (sndU N))

theorem pairU_snd (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ prU N :=
  congrArg Over.Hom.left (lift_snd (fstU N) (sndU N))

theorem pairU_isPullback (N : Near π G) :
    IsPullback (pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  have hUU : (N.U ⊗ N.U).hom = (fst N.U N.U).left ≫ N.U.hom := rfl
  have cUU : (fst N.U N.U).left ≫ N.U.hom = (snd N.U N.U).left ≫ N.U.hom := pullback.condition
  have hTT : (Desc.UT N ⊗ Desc.UT N).hom = (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := rfl
  have cTT : (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.UT N).hom := pullback.condition
  have extUU : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (N.U ⊗ N.U).left), f ≫ (fst N.U N.U).left = g ≫ (fst N.U N.U).left →
      f ≫ (snd N.U N.U).left = g ≫ (snd N.U N.U).left → f = g := fun f g h1 h2 => pullback.hom_ext h1 h2
  have extTT : ∀ {Y : Scheme.{0}} (f g : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left),
      f ≫ (fst (Desc.UT N) (Desc.UT N)).left = g ≫ (fst (Desc.UT N) (Desc.UT N)).left →
      f ≫ (snd (Desc.UT N) (Desc.UT N)).left = g ≫ (snd (Desc.UT N) (Desc.UT N)).left → f = g :=
    fun f g h1 h2 => pullback.hom_ext h1 h2
  have liftTT : ∀ {Y : Scheme.{0}} (a b : Y ⟶ (Desc.UT N).left), a ≫ (Desc.UT N).hom = b ≫ (Desc.UT N).hom →
      ∃ f : Y ⟶ (Desc.UT N ⊗ Desc.UT N).left,
        f ≫ (fst (Desc.UT N) (Desc.UT N)).left = a ∧ f ≫ (snd (Desc.UT N) (Desc.UT N)).left = b :=
    fun a b h => ⟨pullback.lift a b h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have ha : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (fst N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← hUU]; exact s.condition
  have hb : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      (s.fst ≫ (snd N.U N.U).left) ≫ N.U.hom = s.snd ≫ pullback.fst π π ≫ π := fun s => by
    rw [Category.assoc, ← cUU, ← hUU]; exact s.condition
  have hab : ∀ s : PullbackCone (N.U ⊗ N.U).hom (pullback.fst π π ≫ π),
      liftU N _ _ (ha s) ≫ (Desc.UT N).hom = liftU N _ _ (hb s) ≫ (Desc.UT N).hom := fun s => by
    rw [liftU_hom, liftU_hom]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (pairU_over N)) ?_
  refine PullbackCone.IsLimit.mk (pairU_over N) (fun s => (liftTT _ _ (hab s)).choose) ?_ ?_ ?_
  · intro s
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    apply extUU
    · rw [Category.assoc, pairU_fst, ← Category.assoc, h1, liftU_prU]
    · rw [Category.assoc, pairU_snd, ← Category.assoc, h2, liftU_prU]
  · intro s
    obtain ⟨h1, _⟩ := (liftTT _ _ (hab s)).choose_spec
    show _ ≫ (Desc.UT N ⊗ Desc.UT N).hom = _
    rw [hTT, ← Category.assoc, h1, liftU_hom]
  · intro s m m1 m2
    obtain ⟨h1, h2⟩ := (liftTT _ _ (hab s)).choose_spec
    have m2' : m ≫ (Desc.UT N ⊗ Desc.UT N).hom = s.snd := m2
    rw [hTT] at m2'
    apply extTT
    · rw [h1]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_fst, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, m2']
    · rw [h2]
      apply UT_ext
      · rw [liftU_prU, Category.assoc, ← pairU_snd, ← Category.assoc, m1]
      · rw [liftU_hom, Category.assoc, ← cTT, m2']

end GlobalTheory.Mum.DescKP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackDescentSquarePairToOpenSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_descentSquarePairToOpenSquare : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} (N : Near π G), IsPullback (DescKP.pairU N) (Desc.UT N ⊗ Desc.UT N).hom (N.U ⊗ N.U).hom (pullback.fst π π ≫ π) := by
  first | exact @GlobalTheory.Mum.DescKP.pairU_isPullback | exact GlobalTheory.Mum.DescKP.pairU_isPullback | (intros; apply GlobalTheory.Mum.DescKP.pairU_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

namespace GlobalTheory.OpenGeomIrr

theorem geometricallyIrreducible_comp_of_isOpenImmersion : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j →
    ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  intro T W X j hj f hf hs
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h₁ : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hne : Nonempty ↥(Limits.pullback (j ≫ f) x) := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (.of K)) := inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (j ≫ f) x).surjective p
    exact ⟨z⟩
  let e := pullbackRightPullbackFstIso f x j
  have hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x)) := ⟨e.inv hne.some⟩
  have h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x)) :=
    (Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace
  exact e.hom.homeomorph.irreducibleSpace_iff.1 h₂

end GlobalTheory.OpenGeomIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleCompOfIsOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j → ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  first | exact @GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | exact GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion | (intros; apply GlobalTheory.OpenGeomIrr.geometricallyIrreducible_comp_of_isOpenImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplication
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplication
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem embL_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.fst G.hom p = Desc.toS N p hp ≫ N.u := pullback.lift_fst _ _ _

theorem embL_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.snd G.hom p = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem pairU_fst' (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ fst _ _).left = _
  rw [lift_fst]; rfl

theorem pairU_snd' (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ snd _ _).left = _
  rw [lift_snd]; rfl

theorem fst_hom' (N : Near π G) :
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (fst (Desc.UT N) (Desc.UT N))

theorem snd_hom' (N : Near π G) :
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (snd (Desc.UT N) (Desc.UT N))

theorem mT_fst' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : mT N V m hm ≫ pullback.fst _ _ = (pairU N ∣_ V) ≫ m :=
  pullback.lift_fst _ _ _

theorem mT_snd' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) :
    mT N V m hm ≫ pullback.snd _ _ = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem fst_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem snd_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem fst_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (fst_hom' N))))

theorem snd_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (snd_hom' N))))

theorem fst_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

theorem snd_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

theorem sum_eq_mT_emb : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  intro R _ _ S π G _ N V m hm law p hp
  let T0 : Over (pullback π π) := Over.mk ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  let ι0 : T0 ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk (VT N V).ι rfl
  let a : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ fst _ _ ≫ Desc.emb N p hp
  let b : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ snd _ _ ≫ Desc.emb N p hp
  have hab : ι0 ≫ Desc.sum N p hp = a * b := by rw [Desc.sum, comp_mul]
  have wpt : ∀ c : T0 ⟶ (Over.pullback p).obj G, (c.left ≫ pullback.fst G.hom p) ≫ G.hom = T0.hom ≫ p := by
    intro c
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ p) (Over.w c)
  let x : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (a.left ≫ pullback.fst G.hom p) (wpt a)
  let y : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (b.left ≫ pullback.fst G.hom p) (wpt b)
  have hxy : (x * y).left = (a * b).left ≫ pullback.fst G.hom p :=
    (isGrpPullback_pullback G p).2 T0 a b x y rfl rfl
  have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
  have e' : ∀ {Z : Scheme.{0}} (h : (N.U ⊗ N.U).left ⟶ Z), (pairU N ∣_ V) ≫ V.ι ≫ h = (VT N V).ι ≫ pairU N ≫ h :=
    fun h => by rw [← Category.assoc, e, Category.assoc]
  have ptx : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (fst N.U N.U).left) x.left := by
    refine ⟨(VT N V).ι ≫ (fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((fst_toS_fst' N p hp).trans (pairU_fst' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  have pty : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (snd N.U N.U).left) y.left := by
    refine ⟨(VT N V).ι ≫ (snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((snd_toS_fst' N p hp).trans (pairU_snd' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  obtain ⟨x₀, h₁, h₂, h₃⟩ := law (VT N V).toScheme (pairU N ∣_ V) (T0.hom ≫ p) x y ptx pty
  have hx₀ : x₀ = mT N V m hm ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · exact h₁.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_fst' N p hp)).trans (mT_fst' N V m hm))).symm)
    · exact h₂.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_snd' N p hp)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (mT_snd' N V m hm))))).symm)
  apply pullback.hom_ext
  · rw [Category.assoc (mT N V m hm), embL_fst']
    refine (?_ : _ = (mT N V m hm ≫ Desc.toS N p hp) ≫ N.u).trans (Category.assoc _ _ _)
    rw [← hx₀, h₃, hxy, ← hab]
    rfl
  · have w : (Desc.sum N p hp).left ≫ pullback.snd G.hom p = (Desc.UT N ⊗ Desc.UT N).hom := Over.w _
    rw [Category.assoc, w, Category.assoc, embL_snd', mT_snd']

end GlobalTheory.Mum.DescKP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplicationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  first | exact @GlobalTheory.Mum.DescKP.sum_eq_mT_emb | exact GlobalTheory.Mum.DescKP.sum_eq_mT_emb | (intros; apply GlobalTheory.Mum.DescKP.sum_eq_mT_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  first | exact @GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | exact GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | (intros; apply GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPairSumEqOfSumEqOtherPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]

theorem ι_mem {X : Scheme.{0}} (U : X.Opens) (x : U.toScheme) : U.ι x ∈ U := x.2

theorem surjective_Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (V : (N.U ⊗ N.U).left.Opens) (h : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)) :
    Surjective ((Wk N p hp V).ι ≫ (Pk N p hp).hom) := by
  obtain ⟨z, h1, h2⟩ := exists_lift N p hp (VT N V).toScheme (VT N V).ι (VT N V).ι rfl
  have hr : Set.range z ⊆ Set.range (Wk N p hp V).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · show (abP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h1]; exact ι_mem _ x
    · show (cdP N p hp).left (z x) ∈ VT N V
      rw [← Scheme.Hom.comp_apply, h2]; exact ι_mem _ x
  let z' := IsOpenImmersion.lift (Wk N p hp V).ι z hr
  have e : z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ← h1, Category.assoc, Over.w (abP N p hp)]
  have : Surjective (z' ≫ (Wk N p hp V).ι ≫ (Pk N p hp).hom) := by rw [e]; exact h
  exact Surjective.of_comp z' _

theorem agree_Wk (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π)
    (hp' : p' ≫ π = pullback.fst π π ≫ π)
    (h : (VT N V).ι ≫ (Desc.sum N p hp).left = mT N V m hm ≫ (Desc.emb N p hp).left)
    (h' : (VT N V).ι ≫ (Desc.sum N p' hp').left = mT N V m hm ≫ (Desc.emb N p' hp').left) :
    (Wk N p hp V).ι ≫ (abP N p hp ≫ Desc.sum N p' hp').left =
      (Wk N p hp V).ι ≫ (cdP N p hp ≫ Desc.sum N p' hp').left := by
  let a' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (abP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).1)
  let c' := IsOpenImmersion.lift (VT N V).ι ((Wk N p hp V).ι ≫ (cdP N p hp).left) (by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact (ι_mem _ x).2)
  have ea : a' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (abP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have ec : c' ≫ (VT N V).ι = (Wk N p hp V).ι ≫ (cdP N p hp).left := IsOpenImmersion.lift_fac _ _ _
  have e0 := congrArg (fun f => (Wk N p hp V).ι ≫ Over.Hom.left f) (abP_sum N p hp)
  simp only [Over.comp_left] at e0
  have hemb := GlobalTheory.Mum.DescHom.isOpenImmersion_emb N p hp
  have e2 : a' ≫ mT N V m hm = c' ≫ mT N V m hm := by
    refine (cancel_mono (Desc.emb N p hp).left).1 ?_
    simp only [Category.assoc]
    rw [← h, ← Category.assoc, ea, ← Category.assoc, ec, Category.assoc, Category.assoc]
    exact e0
  simp only [Over.comp_left]
  rw [← Category.assoc, ← ea, Category.assoc, h', ← Category.assoc, e2, Category.assoc, ← h', ← Category.assoc, ec,
    Category.assoc]

end GlobalTheory.Mum.DescKP


open GlobalTheory.Mum.DescKP in
theorem GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  intro R _ _ _ _ S π _ _ _ G _ _ hG N hLaw p p' hp hp' Z g g' hgg
  obtain ⟨V, m, hV, hm, hL⟩ := hLaw
  have hlaw := fun (q : pullback π π ⟶ S) (hq : q ≫ π = pullback.fst π π ≫ π) => GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication N V m hm hL q hq
  have : Smooth N.U.hom := N.smooth
  have : Surjective N.U.hom := DescHom.surjective_near N
  have : Smooth G.hom := hG.smooth
  have : IsSeparated G.hom := hG.separated
  have := DescHom.geometricallyIrreducible_of_semiAbelian G hG

  have sV := GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square N.U N.smooth inferInstance V hV
  have sq : IsPullback (DescKP.pairU N ∣_ V) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
      (V.ι ≫ (N.U ⊗ N.U).hom) (pullback.fst π π ≫ π) :=
    (isPullback_morphismRestrict (DescKP.pairU N) V).paste_vert (GlobalTheory.T.isPullback_descentSquarePairToOpenSquare N)
  have sVT : Surjective ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq sV
  have sW := DescKP.surjective_Wk N p hp V sVT

  have : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have : Surjective (Desc.UT N).hom := inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))
  have hGp : GeometricallyIrreducible ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd G.hom p))
  have := DescHom.isOpenImmersion_emb N p hp
  have : GeometricallyIrreducible (Desc.UT N).hom := by
    have e : (Desc.emb N p hp).left ≫ ((Over.pullback p).obj G).hom = (Desc.UT N).hom := Over.w _
    have h := GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (Desc.emb N p hp).left inferInstance _ hGp (by rw [e]; infer_instance)
    rwa [e] at h
  have : Smooth (Desc.UT N ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N).hom))
  have : GeometricallyIrreducible (Desc.UT N ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N).hom
  have : Smooth ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    inferInstanceAs (Smooth (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom ≫ (Desc.UT N ⊗ Desc.UT N).hom))
  have h3 : GeometricallyIrreducible ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom :=
    GeometricallyIrreducible.comp (pullback.fst (Desc.UT N ⊗ Desc.UT N).hom (Desc.UT N).hom) (Desc.UT N ⊗ Desc.UT N).hom
  have : Surjective (DescKP.Pk N p hp).hom := Surjective.of_comp (DescKP.Wk N p hp V).ι _
  have : Smooth (DescKP.Pk N p hp).hom :=
    inferInstanceAs (Smooth (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left ≫
      ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom))
  have : GeometricallyIrreducible (DescKP.Pk N p hp).hom :=
    GlobalTheory.T.geometricallyIrreducible_comp_of_isOpenImmersion_surjective _ _ _ (pullback.snd (Desc.emb N p hp).left (DescKP.trip N p hp).left) inferInstance _ h3
      (inferInstanceAs (Surjective (DescKP.Pk N p hp).hom))
  have : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))

  let j : Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom) ⟶ DescKP.Pk N p hp :=
    Over.homMk (DescKP.Wk N p hp V).ι rfl
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (DescKP.Wk N p hp V).ι)
  have : Surjective (Over.mk ((DescKP.Wk N p hp V).ι ≫ (DescKP.Pk N p hp).hom)).hom := sW
  have hF : DescKP.abP N p hp ≫ Desc.sum N p' hp' = DescKP.cdP N p hp ≫ Desc.sum N p' hp' := by
    refine DescHom.ext_of_open j ?_
    ext1
    exact DescKP.agree_Wk N V m hm p p' hp hp' (hlaw p hp) (hlaw p' hp')
  obtain ⟨z, hz, hz'⟩ := DescKP.exists_lift N p hp Z g g' hgg
  rw [← hz, ← hz', Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, hF]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPairSumEqOfSumEqOtherPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPair_sum_eq_of_sum_eq_other_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ (Z : Scheme.{0}) (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left), g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left → g ≫ (Desc.sum N p' hp').left = g' ≫ (Desc.sum N p' hp').left := by
  first | exact @GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq | exact GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq | (intros; apply GlobalTheory.Mum.DescKP.sum_eq_of_sum_eq <;> assumption)
end
