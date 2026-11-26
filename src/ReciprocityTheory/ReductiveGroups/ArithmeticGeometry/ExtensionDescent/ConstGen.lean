module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableReductionPlusSplit

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def translPt {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ A := lift (fst T A ≫ x) (snd T A) ≫ μ[A]

def translT {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (translPt A x)

def thetaLB (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]

structure ThetaGrp (L : LB A.left) (k : ℤ) (T : Over S) where

  pt : T ⟶ A

  φ : LB.Gen (thetaLB A L k pt)

  isGen : φ.IsGen

def constGen (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := (T ⊗ A).left) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top (Units.map (fst T A).left.appTop.hom.toMonoidHom c)

def CommIsOf (L : LB A.left) (k : ℤ) {T : Over S} (θx θy : ThetaGrp A L k T)
    (c : Γ(T.left, ⊤)ˣ) : Prop :=
  LB.Gen.Corr L _ _ _ _
    (LB.mulGen L _ _ _ _ θx.φ (LB.pullGen L _ _ θy.φ (translT A θx.pt).left))
    (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ θy.φ (LB.pullGen L _ _ θx.φ (translT A θy.pt).left))
      (constGen A L c))

abbrev overRes {T : Over S} (V : T.left.Opens) : Over S := Over.mk (V.ι ≫ T.hom)

def overResι {T : Over S} (V : T.left.Opens) : overRes V ⟶ T := Over.homMk V.ι rfl

def unitRes {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) : Γ((overRes V).left, ⊤)ˣ :=
  Units.map V.ι.appTop.hom.toMonoidHom c

def WeilIs (L : LB A.left) (k : ℤ) {T : Over S} (x y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
    ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def CLND (R : Type) [CommRing R] : Prop :=
  ∃ _ : IsLocalRing R, IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧
    IsAdicComplete (IsLocalRing.maximalIdeal R) R

def AdmBase (R : Type) [CommRing R] (I : Ideal R) : Prop :=
  IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete I R

instance PolAV.isCommMonObj {S : Scheme.{0}} (P : PolAV S) : IsCommMonObj P.A := P.isAb.comm

section Points

variable (R : Type) [CommRing R] [IsDomain R]

abbrev jK : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

abbrev TK : Over (Spec (CommRingCat.of R)) := Over.mk (jK R)

variable {R}

abbrev ptK {B : Over (Spec (CommRingCat.of R))} (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) :
    (TK R).left ⟶ B.left :=
  (toUnit (TK R) ≫ x).left

end Points

structure DegPre (R : Type) [CommRing R] [IsDomain R] where
  P : PolAV (Spec (CommRingCat.of R))
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  cub : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩
  sym : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym (eSec P.A)) (LB.oneGen P.L)
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  c : X → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)
  c_add : ∀ a b, c (a + b) = padd P.A (c a) (c b)
  psi : ∀ χ : X, LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (c χ)) (fun _ => -1))
  psi_gen : ∀ χ : X, (psi χ).IsGen

namespace DegPre

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

instance : AddCommGroup D.X := D.addX
instance : Module.Free ℤ D.X := D.freeX
instance : Module.Finite ℤ D.X := D.finX

abbrev rank : ℕ := Module.finrank ℤ D.X

abbrev xK (χ : D.X) : (TK R).left ⟶ D.P.A.left := ptK (D.c χ)

def rigK := LB.pullGen D.P.L _ _ D.rig (toUnit (TK R)).left

def tau (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi (a + b)) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

def io (y χ : D.X) := D.tau y χ

def pt3 (a a' b : D.X) : (TK R).left ⟶ (G3 D.P.A).left :=
  (lift (toUnit (TK R) ≫ D.c a) (lift (toUnit (TK R) ≫ D.c a') (toUnit (TK R) ≫ D.c b))).left

def PsiEven : Prop :=
  ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.psi (-χ)) (LB.pullGen D.P.L _ _ D.sym (D.xK χ)))
    (D.psi χ)

def TauBimult : Prop :=
  ∀ a a' b : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (D.tau (a + a') b)
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
    (LB.mulGen D.P.L _ _ _ _ (D.tau a b) (D.tau a' b))

abbrev toOpen (V : (Spec (CommRingCat.of R)).Opens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def PsiIn (χ : D.X) (J : Ideal R) : Prop :=
  ∀ (j : PUnit → D.P.L.ι) (V : (Spec (CommRingCat.of R)).Opens), IsAffineOpen V →
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ∀ h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j,
      ∃ r ∈ J.map (toOpen V),
        ((jK R).app V).hom r = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val

end DegPre

structure DegData (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) where
  toPre : DegPre R
  psi_even : toPre.PsiEven
  tau_bimult : toPre.TauBimult
  psi_pos : ∀ χ : toPre.X, χ ≠ 0 → toPre.PsiIn χ I
  psi_tendsto : ∀ n : ℕ, {χ : toPre.X | ¬ toPre.PsiIn χ (I ^ n)}.Finite

namespace GeneratorPullback

variable {X Y Y' : Scheme.{0}} (L : LB X) {K K₁ K₂ K₃ : Type} [Fintype K] [Fintype K₁] [Fintype K₂]
  [Fintype K₃]

def powGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) :
    LB.Gen (LB.LinComb L φ (fun k => (n : ℤ) * ε k)) where
  s := fun j => t.s j ^ n

def SecRel (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι) (j₃ : K₃ → L.ι),
    LB.Coh L (Sum.elim φ₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃)) (Sum.elim j₁ (Sum.elim j₂ j₃)) →
    (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          LB.wchart L φ₁ j₁)).op).hom (s₁.f j₁) =
      (Y'.presheaf.map (homOfLE ((inf_le_left.trans inf_le_right).trans
        (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom (s₂.f j₂)) *
      (Y'.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤
          LB.wchart L φ₃ j₃)).op).hom (u.s j₃).val

end GeneratorPullback

section Fam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev jFK : Spec (CommRingCat.of F) ⟶ (TK R).left :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))

abbrev TF : Over (Spec (CommRingCat.of R)) := Over.mk (jFK (R := R) F ≫ jK R)

namespace DegPre

abbrev BF : Over (Spec (CommRingCat.of R)) := TF (R := R) F ⊗ D.P.A

abbrev prB : BF D F ⟶ D.P.A := snd _ _

def trF (mu : D.X) : BF D F ⟶ BF D F :=
  lift (fst _ _) (padd D.P.A (prB D F) (toUnit _ ≫ D.c mu))

def zF : TF (R := R) F ⟶ BF D F := lift (𝟙 _) (toUnit _ ≫ η[D.P.A])

def famφ (α : D.X) : Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  ![(prB D F).left, (padd D.P.A (prB D F) (toUnit _ ≫ D.c α)).left, (toUnit _ ≫ D.c α).left,
    (toUnit _ ≫ η[D.P.A]).left]

def famε (k : ℕ) : Fin 4 → ℤ := ![(k : ℤ) - 1, 1, -1, 1]

def deltaφ (k : ℕ) (α mu : D.X) : Fin 4 ⊕ Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  Sum.elim (famφ D F (α + k • mu)) (fun i => (trF D F mu).left ≫ famφ D F α i)

def deltaε (k : ℕ) : Fin 4 ⊕ Fin 4 → ℤ := Sum.elim (famε k) (fun i => - famε k i)

def famMult (k : ℕ) (mu α : D.X) :=
  LB.pullGen D.P.L _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (D.tau mu α))
      (GeneratorPullback.powGen D.P.L _ _ D.rigK k))
    (jFK (R := R) F)

def FamFE (k : ℕ) (s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (famφ D F α) (famε k))) : Prop :=
  ∀ (mu α : D.X) (u : LB.Gen (LB.LinComb D.P.L (deltaφ D F k α mu) (deltaε k))), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zF D F).left) (famMult D F k mu α) →
    GeneratorPullback.SecRel D.P.L (famφ D F (α + k • mu)) (famε k) (s (α + k • mu))
      (famφ D F α) (famε k) (s α) (trF D F mu).left (deltaφ D F k α mu) (deltaε k) u

end DegPre

structure Fam (k : ℕ) where
  s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))
  fe : DegPre.FamFE D F k s

end Fam

section Thick

variable (R : Type) [CommRing R] (I : Ideal R)

abbrev thick (e : ℕ) : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))

abbrev thickTrans (e : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1 + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))))

abbrev thickObj (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
  (Over.pullback (thick R I e)).obj G


lemma thickTrans_comp (e : ℕ) : thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by
  simp only [thick, thickTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

abbrev thickMap (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    (thickObj R I e G).left ⟶ (thickObj R I (e + 1) G).left :=
  pullback.map G.hom (thick R I e) G.hom (thick R I (e + 1)) (𝟙 _) (thickTrans R I e) (𝟙 _)
    (by simp) (by simp [thickTrans_comp])

end Thick

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.Inh

open Semi

instance geomConn_id (S : Scheme.{0}) : GeometricallyConnected (𝟙 S) := by
  rw [geometricallyConnected_iff]
  intro K _ y Z fst snd h
  have h' : IsPullback y (𝟙 _) (𝟙 S) y := IsPullback.of_vert_isIso ⟨by simp⟩
  let e : Z ≅ Spec (CommRingCat.of K) := h.isoIsPullback _ _ h'
  exact (Scheme.homeoOfIso e.symm).surjective.connectedSpace (Scheme.homeoOfIso e.symm).continuous

def trivLB (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB := by
  refine ⟨?_, ?_, ?_⟩
  · simp [trivLB]
  · intro i
    exact (res _).map_one
  · intro i j k
    refine (congrArg₂ (· * ·) (res _).map_one (res _).map_one).trans ?_
    exact (_root_.one_mul _).trans (res _).map_one.symm

theorem linComb_triv_g {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j j' : (LB.LinComb (trivLB X) φ ε).ι) : (LB.LinComb (trivLB X) φ ε).g j j' = 1 := by
  have hg : ∀ a b, (trivLB X).g a b = 1 := fun _ _ => rfl
  apply Finset.prod_eq_one
  intro k _
  rw [hg, map_one]
  first
    | exact (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)
    | (erw [map_one, one_zpow])

theorem powOver_triv_g {S : Scheme.{0}} (A : Over S) (U : S.Opens) (N : ℕ)
    (j j' : (powOver A (trivLB A.left) U N).ι) : (powOver A (trivLB A.left) U N).g j j' = 1 :=
  linComb_triv_g _ _ j j'

theorem surj_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (D : X.Opens) (hD : D = ⊤)
    (e : D ≤ f ⁻¹ᵁ ⊤) : Function.Surjective (f.appLE ⊤ D e).hom := by
  subst hD
  have h1 : IsIso (homOfLE e) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
  have h2 : IsIso (f.appLE ⊤ ⊤ e) := by
    first
      | (rw [Scheme.Hom.appLE]; infer_instance)
      | (show IsIso (f.app ⊤ ≫ X.presheaf.map (homOfLE e).op); infer_instance)
  first
    | exact (ConcreteCategory.bijective_of_isIso (f.appLE ⊤ ⊤ e)).2
    | exact (asIso (f.appLE ⊤ ⊤ e)).commRingCatIsoToRingEquiv.surjective

variable (S : Scheme.{0})

def zeroPolAV : PolAV S where
  A := 𝟙_ (Over S)
  isAb :=
    { comm := inferInstance
      smooth := by show Smooth (𝟙 S); infer_instance
      proper := by show IsProper (𝟙 S); infer_instance
      geomConnected := by show GeometricallyConnected (𝟙 S); infer_instance }
  g := 0
  smoothDim := by show SmoothOfRelativeDimension 0 (𝟙 S); infer_instance
  L := trivLB _
  isLB := trivLB_isLB _
  rigid := ⟨⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  sym := fun _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; rw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]
    all_goals rfl⟩
  ample := by
    intro U hU
    haveI : IsIso (𝟙_ (Over S)).hom := by show IsIso (𝟙 S); infer_instance
    let Y := ((𝟙_ (Over S)).hom ⁻¹ᵁ U).toScheme
    let s0 : LB.Sec (powOver (𝟙_ (Over S)) (trivLB _) U 1) :=
      ⟨fun _ => 1, by
        intro i j; rw [powOver_triv_g, Units.val_one, _root_.one_mul]; repeat erw [map_one]
        all_goals rfl⟩
    have hD : nonzeroLocus s0 = ⊤ := by
      apply top_unique
      intro x _
      simp only [nonzeroLocus, s0, Scheme.basicOpen_one]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, by
        simp only [powOver, LB.LinComb, LB.wchart, trivLB]
        exact Set.mem_iInter.2 fun _ => trivial⟩
    refine ⟨1, le_rfl, 0, fun _ => s0, by simp only [iSup_const]; exact hD,
      fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
    · rw [hD]
      have : IsAffine Y := hU
      exact isAffineOpen_top Y
    · intro j k
      erw [map_one]; (try erw [map_one]); (try erw [map_one]); exact (_root_.mul_one _).symm
    · intro p
      obtain ⟨a, rfl⟩ := surj_appLE ((𝟙_ (Over S)).hom ∣_ U) _ hD le_top p
      exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
  ktriv := fun _ _ _ x _ => toUnit_unique x _

end ReciprocityTheory.ChartRestriction.G.Out.Inh
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

namespace GeneratorPullback

variable {X X' Y Y' : Scheme.{0}} (L : LB X)

lemma pullAlong_le {K : Type} [Fintype K] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X))
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (jj : K → (L.pull F).ι) :
    LB.wchart (L.pull F) ψ jj ≤ h ⁻¹ᵁ LB.wchart L φ (fun k => jj k ⟨⟩) := by
  intro y hy
  show h.base y ∈ (⋂ k, (φ k).base ⁻¹' (L.U (jj k ⟨⟩) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (ψ k).base y ∈ LB.wchart L (fun _ : PUnit => F) (jj k) := Set.mem_iInter.1 hy k
  have h2 : F.base ((ψ k).base y) ∈ L.U (jj k ⟨⟩) := Set.mem_iInter.1 h1 ⟨⟩
  change (h ≫ φ k).base y ∈ (L.U (jj k ⟨⟩) : Set X)
  rw [← hψ k]
  exact h2

def pullAlong {K : Type} [Fintype K] (F : X' ⟶ X) (h : Y' ⟶ Y) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen (LB.LinComb (L.pull F) ψ ε) where
  s := fun jj => res (pullAlong_le L F h φ ψ hψ jj) (pullU h _ (t.s (fun k => jj k ⟨⟩)))

lemma box_le {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X'))
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => jj k i) := by
  intro y hy
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (φ k).base y ∈ LB.wchart L F (jj k) := Set.mem_iInter.1 hy k
  have h2 : (F i).base ((φ k).base y) ∈ L.U (jj k i) := Set.mem_iInter.1 h1 i
  show (φ k).base y ∈ (⋂ _u : PUnit, (F i).base ⁻¹' (L.U (jj k i) : Set X))
  exact Set.mem_iInter.2 fun _ => h2

def boxGen {J K : Type} [Fintype J] [Fintype K] (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) :
    LB.Gen (LB.LinComb (LB.LinComb L F (fun _ => 1)) φ ε) where
  s := fun jj => ∏ i, res (box_le L F φ jj i) ((t i).s (fun k _ => jj k i))

end GeneratorPullback

section Pow

variable {S : Scheme.{0}}

def powObj (G : Over S) : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | n + 1 => G ⊗ powObj G n

instance powObj.grp (G : Over S) [GrpObj G] : ∀ n, GrpObj (powObj G n)
  | 0 => inferInstanceAs (GrpObj (𝟙_ (Over S)))
  | n + 1 => by
    haveI := powObj.grp G n
    exact inferInstanceAs (GrpObj (G ⊗ powObj G n))

instance powObj.comm (G : Over S) [GrpObj G] [IsCommMonObj G] : ∀ n, IsCommMonObj (powObj G n)
  | 0 => inferInstanceAs (IsCommMonObj (𝟙_ (Over S)))
  | n + 1 => by
    haveI := powObj.comm G n
    exact inferInstanceAs (IsCommMonObj (G ⊗ powObj G n))

def powPr (G : Over S) : ∀ {n : ℕ}, Fin n → (powObj G n ⟶ G)
  | _ + 1, ⟨0, _⟩ => fst _ _
  | n + 1, ⟨i + 1, h⟩ => snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩

instance powPr.isMonHom (G : Over S) [GrpObj G] : ∀ {n : ℕ} (i : Fin n), IsMonHom (powPr G i)
  | _ + 1, ⟨0, _⟩ => inferInstanceAs (IsMonHom (fst _ _))
  | n + 1, ⟨i + 1, h⟩ => by
    haveI := powPr.isMonHom G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩
    exact inferInstanceAs (IsMonHom (snd _ _ ≫ powPr G (n := n) ⟨i, Nat.lt_of_succ_lt_succ h⟩))

def powIsLimit (G : Over S) : ∀ n : ℕ, IsLimit (Fan.mk (powObj G n) (powPr G (n := n)))
  | 0 => mkFanLimit _ (fun s => toUnit s.pt) (fun _ i => i.elim0) (fun _ _ _ => toUnit_unique _ _)
  | n + 1 =>
    mkFanLimit _
      (fun s => lift (s.proj 0) ((powIsLimit G n).lift (Fan.mk s.pt (fun i => s.proj i.succ))))
      (fun s i => by
        refine Fin.cases ?_ (fun i => ?_) i
        · exact lift_fst _ _
        · exact (lift_snd_assoc _ _ _).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩))
      (fun s m hm => by
        apply CartesianMonoidalCategory.hom_ext
        · have h0 : m ≫ powPr G 0 = s.proj 0 := hm 0
          exact h0.trans (lift_fst _ _).symm
        · refine Eq.trans ?_ (lift_snd _ _).symm
          apply (powIsLimit G n).hom_ext
          rintro ⟨i⟩
          have hi : m ≫ snd _ _ ≫ powPr G i = s.proj i.succ := hm i.succ
          exact ((Category.assoc _ _ _).trans hi).trans
            ((powIsLimit G n).fac (Fan.mk s.pt fun i => s.proj i.succ) ⟨i⟩).symm)

structure IsPowGrp (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) where
  pr : Fin j → (G' ⟶ G)
  hom : ∀ i, IsMonHom (pr i)
  lim : IsLimit (Fan.mk G' pr)

def powIsPowGrp (G : Over S) [GrpObj G] (n : ℕ) : IsPowGrp (powObj G n) G n :=
  ⟨powPr G, fun i => inferInstance, powIsLimit G n⟩

abbrev boxLB {G' G : Over S} {j : ℕ} (L : LB G.left) (pr : Fin j → (G' ⟶ G)) : LB G'.left :=
  LB.LinComb L (K := Fin j) (fun i => (pr i).left) (fun _ => 1)

variable {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}

def boxRig (p : IsPowGrp G' G j) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    LB.Gen ((boxLB L p.pr).pull (eSec G')) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) (fun _ => eSec G') (fun _ => 1)
    (fun i => letI := p.hom i; (CubeMap.ofHom (p.pr i)).rigPull L r)

def boxCub (p : IsPowGrp G' G j) (L : LB G.left) (t : LB.Gen (Theta G L)) :
    LB.Gen (Theta G' (boxLB L p.pr)) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) (thφ G' (x3 G')) thε
    (fun i => letI := p.hom i; (CubeMap.ofHom (p.pr i)).thetaPull L t)

theorem inv_pr (p : IsPowGrp G' G j) (i : Fin j) (k : Fin 2) :
    (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → (G'.left ⟶ G'.left)) k ≫ (p.pr i).left =
      (p.pr i).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → (G.left ⟶ G.left)) k := by
  have := p.hom i
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · simp

def boxSym (p : IsPowGrp G' G j) (L : LB G.left)
    (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) :
    LB.Gen (LB.LinComb (boxLB L p.pr) (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]) :=
  GeneratorPullback.boxGen L (fun i => (p.pr i).left) _ _
    (fun i => GeneratorPullback.pullAlong L (p.pr i).left (p.pr i).left _ _ _ (inv_pr p i) sy)

def BoxIsLBSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left),
    L.IsLB → (boxLB L p.pr).IsLB

def BoxRigIsGenSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))),
    L.IsLB → r.IsGen → (boxRig p L r).IsGen

def BoxCubicalSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : RigLB G) (c : CubicalStr G L) (hL : (boxLB L.L p.pr).IsLB)
    (hr : (boxRig p L.L L.rig).IsGen),
    ∃ c' : CubicalStr G' ⟨boxLB L.L p.pr, boxRig p L.L L.rig, hL, hr⟩, c'.t = boxCub p L.L c.t

def BoxSymSt : Prop :=
  ∀ (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ)
    (p : IsPowGrp G' G j) (L : LB G.left)
    (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])),
    L.IsLB → sy.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ sy (eSec G)) (LB.oneGen L) →
    (boxSym p L sy).IsGen ∧
      LB.Gen.Corr (boxLB L p.pr) _ _ _ _ (LB.pullGen (boxLB L p.pr) _ _ (boxSym p L sy) (eSec G'))
        (LB.oneGen (boxLB L p.pr))

end Pow

end ReciprocityTheory.ChartRestriction.G.Out
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.HomExtDvrSt
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def HomExtDvrSt : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    (G G' : Over (Spec (CommRingCat.of T))) [GrpObj G] [GrpObj G'],
    IsSemiAbelian G → IsSemiAbelian G' →
    ∀ φ : genFibre T G ⟶ genFibre T G', IsMonHom φ →
      ∃! ψ : G ⟶ G', IsMonHom ψ ∧ (Over.pullback (specMap T (FractionRing T))).map ψ = φ

structure Laws7 : Prop where
  homExtDvr : HomExtDvrSt

end ReciprocityTheory.ChartRestriction.G.Out
end
end
