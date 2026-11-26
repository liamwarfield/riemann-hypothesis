module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCoboundaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

abbrev sq : A ⟶ A := (𝟙 A) ^ 2

theorem comp_sq {T : Over S} (x : T ⟶ A) : x ≫ sq A = x ^ 2 := by
  rw [sq, MonObj.comp_pow, Category.comp_id]

abbrev Two : Over S := pullback (sq A) η[A]

abbrev incl : Two A ⟶ A := pullback.fst _ _

variable {A}

theorem incl_sq {T : Over S} (u : T ⟶ Two A) : (u ≫ incl A) ^ 2 = 1 := by
  rw [← comp_sq, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
  congr 1
  exact toUnit_unique _ _

def kpt {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : T ⟶ Two A :=
  pullback.lift x (toUnit _) (by rw [comp_sq, hx, Hom.one_def])

@[simp, reassoc] theorem kpt_incl {T : Over S} (x : T ⟶ A) (hx : x ^ 2 = 1) : kpt x hx ≫ incl A = x :=
  pullback.lift_fst _ _ _

theorem two_ext {T : Over S} {u v : T ⟶ Two A} (h : u ≫ incl A = v ≫ incl A) : u = v :=
  pullback.hom_ext h (toUnit_unique _ _)

variable (A)

def twoFun : (Over S)ᵒᵖ ⥤ CommGrpCat.{0} where
  obj T := CommGrpCat.of (MonoidHom.ker (powMonoidHom 2 : (Opposite.unop T ⟶ A) →* (Opposite.unop T ⟶ A)))
  map φ := CommGrpCat.ofHom
    { toFun := fun x => ⟨φ.unop ≫ x.1, by
        show (φ.unop ≫ x.1) ^ 2 = 1
        rw [← MonObj.comp_pow, show x.1 ^ 2 = 1 from x.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp φ ψ := by ext x; exact Category.assoc _ _ _

def twoRep : (twoFun A ⋙ forget _).RepresentableBy (Two A) where
  homEquiv {T} :=
    { toFun := fun u => (⟨u ≫ incl A, incl_sq u⟩ : MonoidHom.ker (powMonoidHom 2 : (T ⟶ A) →* (T ⟶ A)))
      invFun := fun x => kpt x.1 x.2
      left_inv := fun u => two_ext (kpt_incl _ _)
      right_inv := fun x => Subtype.ext (kpt_incl _ _) }
  homEquiv_comp {T T'} f u := Subtype.ext (Category.assoc _ _ _)

instance : CommGrpObj (Two A) := CommGrpObj.ofRepresentableBy _ (twoFun A) (twoRep A)

variable {A}

theorem mul_incl {T : Over S} (x y : T ⟶ Two A) : (x * y) ≫ incl A = (x ≫ incl A) * (y ≫ incl A) := by
  have h := ((yonedaGrpObjIsoOfRepresentableBy (Two A) (twoFun A ⋙ forget₂ CommGrpCat GrpCat)
    (twoRep A)).hom.app (Opposite.op T)).hom.map_mul x y
  exact congrArg Subtype.val h

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem sq_w : (sq A).left ≫ A.hom = A.hom := Over.w _

abbrev pairO : Over S := Over.mk (pullback.fst (sq A).left (sq A).left ≫ A.hom)

abbrev tripO : Over S :=
  Over.mk (pullback.fst _ _ ≫ pullback.fst (sq A).left (sq A).left ≫ A.hom :
    GlobalTheory.LBDescent.Triple (sq A).left ⟶ S)

theorem snd_w : pullback.snd (sq A).left (sq A).left ≫ A.hom = pullback.fst (sq A).left (sq A).left ≫ A.hom := by
  rw [← sq_w A, pullback.condition_assoc]

def s₁ : pairO A ⟶ A := Over.homMk (pullback.fst _ _) rfl

def s₂ : pairO A ⟶ A := Over.homMk (pullback.snd _ _) (snd_w A)

theorem s_sq : s₁ A ≫ sq A = s₂ A ≫ sq A := Over.OverMorphism.ext pullback.condition

def t₁ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.fst _ _) rfl

def t₂ : tripO A ⟶ A := Over.homMk (pullback.fst _ _ ≫ pullback.snd _ _) (by
  show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w]; rfl)

def t₃ : tripO A ⟶ A := Over.homMk (pullback.snd _ _ ≫ pullback.snd _ _) (by
  show (pullback.snd _ _ ≫ pullback.snd _ _) ≫ A.hom = _
  rw [Category.assoc, snd_w, ← pullback.condition_assoc, snd_w]; rfl)

theorem t₁₂_sq : t₁ A ≫ sq A = t₂ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (sq A).left = (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    rw [Category.assoc, Category.assoc, pullback.condition])
theorem t₂₃_sq : t₂ A ≫ sq A = t₃ A ≫ sq A :=
  Over.OverMorphism.ext (by
    show (pullback.fst _ _ ≫ pullback.snd _ _) ≫ (sq A).left = (pullback.snd _ _ ≫ pullback.snd _ _) ≫ (sq A).left
    simp only [Category.assoc]
    have e := pullback.condition (f := pullback.snd (sq A).left (sq A).left) (g := pullback.fst (sq A).left (sq A).left)
    rw [reassoc_of% e, pullback.condition])

variable {A}

def dif {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) : T ⟶ Two A :=
  kpt (a⁻¹ * b) (by rw [mul_pow, inv_pow, ← comp_sq, ← comp_sq, h, inv_mul_cancel])

@[simp, reassoc] theorem dif_incl {T : Over S} (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    dif a b h ≫ incl A = a⁻¹ * b := kpt_incl _ _

variable (A)

def ψ : tripO A ⟶ Two A ⊗ Two A := lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))

def δ : pairO A ⟶ Two A := dif (s₁ A) (s₂ A) (s_sq A)

end GlobalTheory.TwoTors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem exists_pullTop_of_isPullback : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  intro S X A Z _ hA p q h D
  obtain ⟨c, hc⟩ := exists_pullTop_snd A Z hA (pullTop h.isoPullback.inv D)
  refine ⟨c, ?_⟩
  have h₁ : h.isoPullback.hom ≫ (snd A Z).left = q := h.isoPullback_hom_snd
  have h₂ := congrArg (pullTop h.isoPullback.hom) hc
  rw [← h₁]
  refine (pullTop_pullTop_comp _ _ c).symm.trans (h₂.trans ?_)
  rw [pullTop_pullTop_comp, Iso.hom_inv_id]
  rfl

end GlobalTheory.CharKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange : ∀ {S X : Scheme.{0}} (A Z : Over S) [GrpObj A], IsAbelianScheme A → ∀ (p : X ⟶ A.left) (q : X ⟶ Z.left), IsPullback p q A.hom Z.hom → ∀ D : Γ(X, ⊤)ˣ, ∃ c : Γ(Z.left, ⊤)ˣ, GlobalTheory.CharKer.pullTop q c = D := by
  first | exact @GlobalTheory.CharKer.exists_pullTop_of_isPullback | exact GlobalTheory.CharKer.exists_pullTop_of_isPullback | (intros; apply GlobalTheory.CharKer.exists_pullTop_of_isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullback
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoTors.TripleProd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def pt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = _
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc, Over.w])

theorem pt_t₁ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₁ A = a :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])

theorem pt_t₂ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₂ A = b :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])

theorem pt_t₃ {T : Over S} (a b c : T ⟶ A) (h₁ h₂) : pt a b c h₁ h₂ ≫ t₃ A = c :=
  Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = _
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])

theorem ext₃ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h₂ : m ≫ t₂ A = n ≫ t₂ A)
    (h₃ : m ≫ t₃ A = n ≫ t₃ A) : m = n := by
  have e₁ : m.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.fst _ _ :=
    congrArg CommaMorphism.left h₁
  have e₂ : m.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.fst _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₂
  have e₃ : m.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ = n.left ≫ pullback.snd _ _ ≫ pullback.snd _ _ :=
    congrArg CommaMorphism.left h₃
  have e₄ := e₂
  rw [pullback.condition] at e₄
  refine Over.OverMorphism.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_))
  · exact (Category.assoc _ _ _).trans (e₁.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₂.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₄.trans (Category.assoc _ _ _).symm)
  · exact (Category.assoc _ _ _).trans (e₃.trans (Category.assoc _ _ _).symm)

theorem comp_ψ_fst {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ fst _ _) ≫ incl A = (m ≫ t₁ A)⁻¹ * (m ≫ t₂ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_fst_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem comp_ψ_snd {T : Over S} (m : T ⟶ tripO A) :
    ((m ≫ ψ A) ≫ snd _ _) ≫ incl A = (m ≫ t₂ A)⁻¹ * (m ≫ t₃ A) := by
  rw [Category.assoc, Category.assoc, ψ, lift_snd_assoc, dif_incl, MonObj.comp_mul, GrpObj.comp_inv]

theorem ext₂ {T : Over S} {m n : T ⟶ tripO A} (h₁ : m ≫ t₁ A = n ≫ t₁ A) (h : m ≫ ψ A = n ≫ ψ A) : m = n := by
  have e₂ := comp_ψ_fst m
  have e₃ := comp_ψ_snd m
  rw [h, comp_ψ_fst, h₁] at e₂
  have h₂ : m ≫ t₂ A = n ≫ t₂ A := (mul_left_cancel e₂).symm
  rw [h, comp_ψ_snd, h₂] at e₃
  exact ext₃ h₁ h₂ (mul_left_cancel e₃).symm

theorem mul_sq {T : Over S} (a : T ⟶ A) (x : T ⟶ Two A) : a ≫ sq A = (a * (x ≫ incl A)) ≫ sq A := by
  rw [comp_sq, comp_sq, mul_pow, incl_sq, _root_.mul_one]

theorem exists_pt {T : Over S} (a : T ⟶ A) (q : T ⟶ Two A ⊗ Two A) :
    ∃ m : T ⟶ tripO A, m ≫ t₁ A = a ∧ m ≫ ψ A = q := by
  refine ⟨pt a (a * ((q ≫ fst _ _) ≫ incl A)) ((a * ((q ≫ fst _ _) ≫ incl A)) * ((q ≫ snd _ _) ≫ incl A))
    (mul_sq _ _) (mul_sq _ _), pt_t₁ _ _ _ _ _, ?_⟩
  refine CartesianMonoidalCategory.hom_ext _ _ (two_ext ?_) (two_ext ?_)
  · rw [comp_ψ_fst, pt_t₁, pt_t₂, inv_mul_cancel_left]
  · rw [comp_ψ_snd, pt_t₂, pt_t₃, inv_mul_cancel_left]

theorem isPullback {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] :
    IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  have w : (t₁ A).left ≫ A.hom = (ψ A).left ≫ (Two A ⊗ Two A).hom := (Over.w _).trans (Over.w _).symm
  have key : ∀ s : PullbackCone A.hom (Two A ⊗ Two A).hom, ∃ l : s.pt ⟶ (tripO A).left,
      l ≫ (t₁ A).left = s.fst ∧ l ≫ (ψ A).left = s.snd := fun s => by
    obtain ⟨m, h₁, h₂⟩ := exists_pt (T := Over.mk (s.fst ≫ A.hom)) (Over.homMk s.fst rfl)
      (Over.homMk s.snd s.condition.symm)
    exact ⟨m.left, congrArg CommaMorphism.left h₁, congrArg CommaMorphism.left h₂⟩
  choose l hl₁ hl₂ using key
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w l hl₁ hl₂ fun s m h₁ h₂ => ?_⟩⟩
  have hw : ∀ k : s.pt ⟶ (tripO A).left, k ≫ (t₁ A).left = s.fst → k ≫ (tripO A).hom = s.fst ≫ A.hom :=
    fun k hk => by rw [← hk, Category.assoc, Over.w]
  have e : (Over.homMk m (hw m h₁) : Over.mk (s.fst ≫ A.hom) ⟶ tripO A) = Over.homMk (l s) (hw _ (hl₁ s)) :=
    ext₂ (Over.OverMorphism.ext (h₁.trans (hl₁ s).symm)) (Over.OverMorphism.ext (h₂.trans (hl₂ s).symm))
  exact congrArg CommaMorphism.left e

end GlobalTheory.TwoTors.TripleProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TwoTors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsPullback (t₁ A).left (ψ A).left A.hom (Two A ⊗ Two A).hom := by
  first | exact @GlobalTheory.TwoTors.TripleProd.isPullback | exact GlobalTheory.TwoTors.TripleProd.isPullback | (intros; apply GlobalTheory.TwoTors.TripleProd.isPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwo
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.TwoTors

theorem sq_symm_of_cocycle {G M : Type} [CommGroup G] [CommGroup M] (c : G → G → M)
    (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) (h2 : ∀ x : G, x ^ 2 = 1) (x y : G) :
    c x y ^ 2 = c y x ^ 2 := by
  let a : G → G → Additive M := fun x y => Additive.ofMul (c x y)
  have hca : ∀ x y z, a x y + a (x * y) z = a y z + a x (y * z) := fun x y z => by
    simp only [a, ← ofMul_mul, hc]
  let e : G → G → Additive M := fun x y => a x y - a y x
  have emul : ∀ x y z, e (x * y) z = e x z + e y z := by
    intro x y z
    have h₁ := hca x y z
    have h₂ := hca z x y
    have h₃ := hca x z y
    rw [mul_comm z x] at h₂
    rw [mul_comm z y] at h₃
    have e₁ : a (x * y) z = a y z + a x (y * z) - a x y := by rw [← h₁]; abel
    have e₂ : a z (x * y) = a z x + a (x * z) y - a x y := by rw [h₂]; abel
    have e₃ : a x z = a z y + a x (y * z) - a (x * z) y := by rw [← h₃]; abel
    simp only [e]
    rw [e₁, e₂, e₃]
    abel
  have hone : ∀ y, e 1 y = 0 := by
    intro y
    have h₁ := hca 1 1 y
    have h₂ := hca y 1 1
    simp only [_root_.one_mul, _root_.mul_one] at h₁ h₂
    have : a 1 1 = a 1 y := by
      have := congrArg (· - a 1 y) h₁; simpa using this
    have : a y 1 = a 1 1 := by
      have := congrArg (· - a y 1) h₂; simpa using this
    simp only [e]
    rw [sub_eq_zero]
    rw [← ‹a 1 1 = a 1 y›, ‹a y 1 = a 1 1›]
  have key : e x y + e x y = 0 := by
    rw [← emul, ← pow_two, h2, hone]
  apply Additive.ofMul.injective
  rw [ofMul_pow, ofMul_pow]
  change 2 • a x y = 2 • a y x
  rw [← sub_eq_zero, ← smul_sub, two_nsmul]
  exact key

theorem isFinite_two {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hf : IsFinite (sq A).left) :
    IsFinite (Two A).hom := by
  have h := (IsPullback.of_hasPullback (sq A) η[A]).map (Over.forget S)
  have h₂ : IsFinite (pullback.snd (sq A) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h hf
  rw [← Over.w (pullback.snd (sq A) η[A])]
  exact MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S)))

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

theorem pullTop_pullTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    GlobalTheory.CharKer.pullTop f (GlobalTheory.CharKer.pullTop g u) = GlobalTheory.CharKer.pullTop (f ≫ g) u := by
  ext; simp [GlobalTheory.CharKer.pullTop]; rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def inclHom (T : Over S) : (T ⟶ Two A) →* (T ⟶ A) := MonoidHom.mk' (· ≫ incl A) mul_incl

theorem comp_dif {T T' : Over S} (g : T' ⟶ T) (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    g ≫ dif a b h = dif (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) :=
  two_ext (by rw [Category.assoc, dif_incl, dif_incl, MonObj.comp_mul, GrpObj.comp_inv])

theorem dif_incl_incl {T : Over S} (u v : T ⟶ Two A) (h : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A) :
    dif (u ≫ incl A) (v ≫ incl A) h = u⁻¹ * v :=
  two_ext (by
    rw [dif_incl]
    change (inclHom T u)⁻¹ * inclHom T v = inclHom T (u⁻¹ * v)
    rw [map_mul, map_inv])

theorem incl_sq_eq {T : Over S} (u v : T ⟶ Two A) : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A := by
  rw [comp_sq, comp_sq, incl_sq, incl_sq]

theorem sq_eq_one {T : Over S} (x : T ⟶ Two A) : x ^ 2 = 1 := by
  have h : inclHom T (x ^ 2) = inclHom T 1 := by rw [map_pow, map_one]; exact incl_sq x
  exact two_ext h

def tpt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (by rw [← Over.comp_left, h₁, Over.comp_left])
    (by rw [← Over.comp_left, h₂, Over.comp_left])) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = T.hom
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
      exact Over.w a)

theorem tpt_ψ {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) :
    tpt a b c h₁ h₂ ≫ ψ A = lift (dif a b h₁) (dif b c h₂) := by
  have e₁ : tpt a b c h₁ h₂ ≫ t₁ A = a := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = a.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])
  have e₂ : tpt a b c h₁ h₂ ≫ t₂ A = b := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = b.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])
  have e₃ : tpt a b c h₁ h₂ ≫ t₃ A = c := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = c.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, ψ, lift_fst, lift_fst, comp_dif]; congr 1 <;> assumption
  · rw [Category.assoc, ψ, lift_snd, lift_snd, comp_dif]; congr 1 <;> assumption

variable (A)

theorem fst_δ : (pullback.fst _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₁ A) (t₂ A) (t₁₂_sq A)).left := by
  have : (Over.homMk (pullback.fst _ _) rfl : tripO A ⟶ pairO A) ≫ δ A = dif (t₁ A) (t₂ A) (t₁₂_sq A) := by
    rw [δ, comp_dif]; congr 1 <;> exact Over.OverMorphism.ext rfl
  exact congrArg CommaMorphism.left this

theorem snd_δ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₂ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (pairO A).hom = (tripO A).hom := by
    show pullback.snd _ _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [← pullback.condition_assoc, snd_w]
  have : (Over.homMk (pullback.snd _ _) w₂ : tripO A ⟶ pairO A) ≫ δ A = dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]; congr 1
    all_goals first
      | exact Over.OverMorphism.ext rfl
      | exact Over.OverMorphism.ext (pullback.condition (f := pullback.snd (sq A).left (sq A).left)).symm
  exact congrArg CommaMorphism.left this

theorem tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion : pr13 (sq A).left ≫ (δ A).left =
    (dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₃ : pr13 (sq A).left ≫ (pairO A).hom = (tripO A).hom := by
    show pr13 _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [pr13, pullback.lift_fst_assoc, Category.assoc]
  have a₁ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₁ A = t₁ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.fst _ _ = _; rw [pr13, pullback.lift_fst]; rfl)
  have a₃ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₂ A = t₃ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.snd _ _ = _; rw [pr13, pullback.lift_snd]; rfl)
  have : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ δ A =
      dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]
    apply two_ext
    rw [dif_incl, mul_incl, dif_incl, dif_incl, a₁, a₃]
    group
  exact congrArg CommaMorphism.left this

theorem killsSq_of (c : Γ((Two A ⊗ Two A).left, ⊤)ˣ) (w : Γ((Two A).left, ⊤)ˣ) (D : Γ(Triple (sq A).left, ⊤)ˣ)
    (hc : GlobalTheory.CharKer.pullTop (ψ A).left c = D)
    (hw : ∀ (T : Over S) (x y : T ⟶ Two A), GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) *
      GlobalTheory.CharKer.pullTop (x * y).left w = GlobalTheory.CharKer.pullTop x.left w * GlobalTheory.CharKer.pullTop y.left w) :
    KillsSq (sq A).left D (GlobalTheory.CharKer.pullTop (δ A).left w⁻¹) := by
  unfold KillsSq
  rw [pullTop_pullTop, pullTop_pullTop, pullTop_pullTop, fst_δ, snd_δ, tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion, ← hc, map_inv, map_inv, map_inv]
  have H := hw (tripO A) (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))
  rw [map_pow] at H
  have hψ : (ψ A).left = (lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))).left := rfl
  rw [hψ, _root_.mul_assoc, ← _root_.mul_inv, ← H, _root_.mul_inv, mul_inv_cancel_left]

end GlobalTheory.TwoTors


open GlobalTheory.TwoTors in
theorem GlobalTheory.TwoTors.killsSq_of_triCocycle : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ,
    TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  intro K _ _ A _ _ hA hf D hD
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange A (Two A ⊗ Two A) hA (t₁ A).left (ψ A).left (GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback A) D
  have key : ∀ {T : Over (Sp K)} (a b d : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = d ≫ sq A) p₁ p₂,
      GlobalTheory.CharKer.pullTop (tri (sq A).left a.left b.left d.left p₁ p₂) D =
        GlobalTheory.CharKer.pullTop (lift (dif a b h₁) (dif b d h₂)).left c := by
    intro T a b d h₁ h₂ p₁ p₂
    rw [← hc, pullTop_pullTop, ← tpt_ψ a b d h₁ h₂]
    rfl
  have hcoc : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c =
        GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c := by
    intro T x y z
    have H := hD T.left ((1 : T ⟶ Two A) ≫ incl A).left (x ≫ incl A).left ((x * y) ≫ incl A).left
      ((x * y * z) ≫ incl A).left (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
      (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left]) (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
    rw [key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _),
      key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _)] at H
    simp only [dif_incl_incl] at H
    have e₁ : (1 : T ⟶ Two A)⁻¹ * x = x := by group
    have e₂ : x⁻¹ * (x * y) = y := by group
    have e₃ : (1 : T ⟶ Two A)⁻¹ * (x * y) = x * y := by group
    have e₄ : (x * y)⁻¹ * (x * y * z) = z := by group
    have e₅ : x⁻¹ * (x * y * z) = y * z := by group
    rw [e₁, e₂, e₃, e₄, e₅] at H
    exact H
  have hsym : ∀ (T : Over (Sp K)) (x y : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) = GlobalTheory.CharKer.pullTop (lift y x).left (c ^ 2) := by
    intro T x y
    rw [map_pow, map_pow]
    exact sq_symm_of_cocycle (fun x y : T ⟶ Two A => GlobalTheory.CharKer.pullTop (lift x y).left c) (hcoc T) sq_eq_one x y
  have hcoc2 : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift (x * y) z).left (c ^ 2) =
        GlobalTheory.CharKer.pullTop (lift y z).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift x (y * z)).left (c ^ 2) := by
    intro T x y z
    simp only [map_pow]
    rw [← mul_pow, ← mul_pow, hcoc]
  obtain ⟨w, hw⟩ := GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary K (Two A) (isFinite_two A hf) (c ^ 2) hcoc2 hsym
  refine ⟨GlobalTheory.CharKer.pullTop (δ A).left w⁻¹, ?_⟩
  exact killsSq_of A c w D hc hw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKillingSquareTripleFibreCocycleMulTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ, TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  first | exact @GlobalTheory.TwoTors.killsSq_of_triCocycle | exact GlobalTheory.TwoTors.killsSq_of_triCocycle | (intros; apply GlobalTheory.TwoTors.killsSq_of_triCocycle <;> assumption)
end
