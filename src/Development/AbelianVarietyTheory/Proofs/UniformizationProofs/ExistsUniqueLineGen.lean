module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.TorusPointForms
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] SplitExt.free SplitExt.finite

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev cPt (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ

def oφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A b (cPt D T χ)).left, (cPt D T χ).left, b.left, (pzero D.P.A T).left]

def oε : Fin 4 → ℤ := ![1, -1, -1, 1]

def oεInv : Fin 4 → ℤ := ![-1, 1, 1, -1]

abbrev oLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oε

abbrev oInvLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oεInv

def cubAt {T : Over (Spec (CommRingCat.of R))} (x x' x'' : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' x'')).left

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

structure GtPt where

  base : TF (R := R) F ⟶ D.P.A

  form : ∀ χ : D.X, LB.Gen (oInvLB D base χ)
  form_gen : ∀ χ : D.X, (form χ).IsGen
  form_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (form (χ + χ')) (cubAt D (cPt D _ χ) (cPt D _ χ') base))
    (LB.mulGen D.P.L _ _ _ _ (form χ) (form χ'))

namespace GtPt

variable {D F}

def IsAdd (g g' h : GtPt D F) : Prop :=
  h.base = padd D.P.A g.base g'.base ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (h.form χ) (cubAt D (cPt D _ χ) g.base g'.base))
      (LB.mulGen D.P.L _ _ _ _ (g.form χ) (g'.form χ))

def IsZero (g : GtPt D F) : Prop :=
  g.base = pzero D.P.A _ ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ) (LB.oneGen D.P.L)

inductive IsNsmul (g : GtPt D F) : ℕ → GtPt D F → Prop
  | zero (h : GtPt D F) : IsZero h → IsNsmul g 0 h
  | succ (k : ℕ) (h h' : GtPt D F) : IsNsmul g k h → IsAdd h g h' → IsNsmul g (k + 1) h'

def IsIo (y : D.X) (g : GtPt D F) : Prop :=
  g.base = cPt D _ y ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ)
      (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))

end GtPt

def QPair (k : ℕ) : Type :=
  {p : D.X × GtPt D F // ∃ h : GtPt D F, p.2.IsNsmul k h ∧ GtPt.IsIo p.1 h}

def QRel (k : ℕ) (p p' : QPair D F k) : Prop :=
  ∃ (z : D.X) (w : GtPt D F), GtPt.IsIo z w ∧ p'.1.1 = p.1.1 + k • z ∧ GtPt.IsAdd p.1.2 w p'.1.2

def Qk (k : ℕ) : Type := Quot (QRel D F k)

namespace Qk

variable {D F} {k : ℕ}

def mk (p : QPair D F k) : Qk D F k := Quot.mk _ p

def IsAdd (a b c : Qk D F k) : Prop :=
  ∃ p p' p'' : QPair D F k, mk p = a ∧ mk p' = b ∧ mk p'' = c ∧
    p''.1.1 = p.1.1 + p'.1.1 ∧ GtPt.IsAdd p.1.2 p'.1.2 p''.1.2

def IsZero (a : Qk D F k) : Prop :=
  ∃ p : QPair D F k, mk p = a ∧ p.1.1 = 0 ∧ p.1.2.IsZero

end Qk

abbrev baseF : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (jFK (R := R) F ≫ jK R)).obj D.P.A

def toB {B' : Over (Spec (CommRingCat.of F))} (β : B' ≅ baseF D F) :
    Over.mk (B'.hom ≫ jFK (R := R) F ≫ jK R) ⟶ D.P.A :=
  Over.homMk (β.hom.left ≫ pullback.fst D.P.A.hom (jFK (R := R) F ≫ jK R)) (by
    have h : β.hom.left ≫ pullback.snd D.P.A.hom (jFK (R := R) F ≫ jK R) = B'.hom := Over.w β.hom
    simp only [Over.mk_hom, Category.assoc]
    erw [pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jFK (R := R) F ≫ jK R) h))

def IsDatumIso (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F)
    (ξ : E.X ≃+ D.X) : Prop :=
  IsMonHom β.hom ∧
    ∀ χ : E.X, ∃ t : LB.Iso (E.O χ).L (oLB D (toB D F β) (ξ χ)), t.IsGen

def IsPointCorr {E : SplitExt (Spec (CommRingCat.of F))} (β : E.B ≅ baseF D F)
    {G : Over (Spec (CommRingCat.of F))} [GrpObj G] (q : G ⟶ E.B)
    (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F) : Prop :=
  (∀ x x', (e x).IsAdd (e x') (e (padd G x x'))) ∧
    (e η[G]).IsZero ∧
    ∀ x, (e x).base.left = (x ≫ q).left ≫ (toB D F β).left

def PointsOfGtSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F, IsPointCorr D F β d.q e

def PointsOfGtCoordSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F)
        (t : ∀ k, LB.Iso (E.O (E.basis k)).L (oLB D (toB D F β) (ξ (E.basis k)))),
        IsPointCorr D F β d.q e ∧ (∀ k, (t k).IsGen) ∧
        ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) (j : E.ChartIdx) (j' : Fin 4 → D.P.L.ι)
          (k : Module.Free.ChooseBasisIndex ℤ E.X) (W : (Spec (CommRingCat.of F)).Opens)
          (h₁ : W ≤ (oInvLB D (e x).base (ξ (E.basis k))).U j')
          (h₂ : W ≤ (x ≫ d.q).left ⁻¹ᵁ
            (LB.div (oLB D (toB D F β) (ξ (E.basis k))) (E.O (E.basis k)).L).U (j', j k))
          (h₃ : W ≤ x.left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j)),
          res (X := Spec (CommRingCat.of F)) h₁ (((e x).form (ξ (E.basis k))).s j') *
              res (X := Spec (CommRingCat.of F)) h₂ (pullU (x ≫ d.q).left _ ((t k).s (j', j k))) =
            res (X := Spec (CommRingCat.of F)) h₃ (pullU x.left _ (d.u j k))

end GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.PairingRatioBijection
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

def scal : F →+* Γ(Spec (CommRingCat.of F), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

def trPt (b : TF (R := R) F ⟶ D.P.A) : D.BF F ⟶ D.BF F :=
  lift (fst _ _) (padd D.P.A (D.prB F) (fst _ _ ≫ b))

abbrev lineAt (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : LB (TF (R := R) F).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => b.left) (fun _ => (k : ℤ))

def LineGen (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : Type :=
  {t : LB.Gen (lineAt D F k b) // t.IsGen}

def phφ (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) : Fin 4 ⊕ Fin 4 → ((D.BF F).left ⟶ D.P.A.left) :=
  Sum.elim (D.famφ F (α + y)) (fun i => (trPt D F b).left ≫ D.famφ F α i)

def phMult (k : ℕ) (g : GtPt D F) (t : LineGen D F k g.base) (α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.form α) (LB.invGen D.P.L _ _ t.1))
    (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k)

variable {D F}

def IsPh {k : ℕ} (p : QPair D F k) (t : LineGen D F k p.1.2.base) (s s' : Fam D F k) : Prop :=
  ∀ α : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k)),
    u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (D.zF F).left) (phMult D F k p.1.2 t α) ∧
    GeneratorPullback.SecRel D.P.L (D.famφ F (α + p.1.1)) (DegPre.famε k) (s'.s (α + p.1.1))
      (D.famφ F α) (DegPre.famε k) (s.s α) (trPt D F p.1.2.base).left
      (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k) u

def FamSmul {k : ℕ} (c : F) (s s' : Fam D F k) : Prop :=
  ∀ α j, (s'.s α).f j = liftFun D.P.A (T := TF (R := R) F) _ (scal F c) * (s.s α).f j

def FamAdd {k : ℕ} (s s' s'' : Fam D F k) : Prop :=
  ∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j

variable (R F) in
abbrev TKF (R : Type) [CommRing R] [IsDomain R]
    (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Over (Spec (CommRingCat.of (FractionRing R))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))

variable (F) in
abbrev SecA (F : Type) [Field F] [Algebra (FractionRing R) F]
    (P : PolAV (Spec (CommRingCat.of (FractionRing R)))) (k : ℕ) : Type :=
  LB.Sec (LPow P.A P.L (k : ℤ) (TKF R F))

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))}

structure IsLinBij {k : ℕ} (E : SecA F P k → Fam D F k → Prop) : Prop where
  existsUnique_right : ∀ σ, ∃! s, E σ s
  existsUnique_left : ∀ s, ∃! σ, E σ s
  add : ∀ σ σ' σ'' s s' s'', E σ s → E σ' s' → E σ'' s'' →
    (∀ j, σ''.f j = σ.f j + σ'.f j) → FamAdd s s' s''
  smul : ∀ (c : F) σ σ' s s', E σ s → E σ' s' →
    (∀ j, σ'.f j = liftFun P.A (T := TKF R F) _ (scal F c) * σ.f j) → FamSmul c s s'

def Intertwines {k : ℕ} (E : SecA F P k → Fam D F k → Prop)
    (θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F)) (p : QPair D F k) (t : LineGen D F k p.1.2.base) :
    Prop :=
  ∀ σ σ' s s', E σ s → E σ' s' → (IsActOf P.A P.L (k : ℤ) θ σ σ' ↔ IsPh p t s s')

def IsImage {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (p : QPair D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  1 ≤ k ∧ D.TauBimult ∧ IsLinBij E ∧ x ^ k = 1 ∧
    (∀ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x → ∃ t, Intertwines E θ p t) ∧
    (∀ t, ∃ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x ∧ Intertwines E θ p t)

def IsImageQ {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (a : Qk D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  ∀ p : QPair D F k, Qk.mk p = a → IsImage E p x

variable (D F)

variable (P)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfIsAddSelf
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtPointsCompare

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

section Cast

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}

def castGen (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) := h ▸ t

theorem castGen_isGen (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (castGen h t).IsGen := by
  subst h; exact ht

theorem castGen_castGen (h : φ = φ') (h' : φ' = φ) (t : LB.Gen (LB.LinComb L φ ε)) :
    castGen h' (castGen h t) = t := by
  subst h; rfl

theorem corr_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) (u : LB.Gen (LB.LinComb L ψ δ)) :
    LB.Gen.Corr L _ _ _ _ (castGen h t) u ↔ LB.Gen.Corr L _ _ _ _ t u := by
  subst h; rfl

theorem corr_mul_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ}
    {φ₁ φ₁' φ₂ φ₂' : K → (Y ⟶ X)} (h : φ = φ') (h₁ : φ₁ = φ₁') (h₂ : φ₂ = φ₂')
    (t : LB.Gen (LB.LinComb L φ ε)) (c : LB.Gen (LB.LinComb L ψ δ))
    (t₁ : LB.Gen (LB.LinComb L φ₁ ε)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (castGen h t) c)
        (LB.mulGen L _ _ _ _ (castGen h₁ t₁) (castGen h₂ t₂)) ↔
      LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t c) (LB.mulGen L _ _ _ _ t₁ t₂) := by
  subst h h₁ h₂; rfl

end Cast

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem oφ_eq (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : oφ D b χ = DegPre.gtφ D F b χ := by
  have : padd D.P.A b (cPt D _ χ) = padd D.P.A (DegPre.cF D F χ) b := mul_comm b (cPt D _ χ)
  unfold oφ DegPre.gtφ
  rw [this]; rfl

theorem corr_one_of_mult (b : TF (R := R) F ⟶ D.P.A)
    (s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b 0) DegPre.gtε))
    (s' : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b (0 + 0)) DegPre.gtε)) (hs : HEq s' s)
    (m : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ s' (DegPre.cubAt D F (DegPre.cF D F 0) (DegPre.cF D F 0) b))
      (LB.mulGen D.P.L _ _ _ _ s s)) :
    LB.Gen.Corr D.P.L _ _ _ _ s (LB.oneGen D.P.L) := by
  revert s'
  rw [add_zero (0 : D.X)]
  intro s' hs m
  obtain rfl := eq_of_heq hs
  refine corr_of_val D.P.isLB fun y J hJ => Eq.trans ?_ (val_one _).symm
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
      ((val_corr hJ m _).trans (val_mul hJ _ _ _))
  have z : DegPre.cF D F 0 = 1 := cPoint_zero _
  rw [z, C.face] at e
  exact (mul_left_cancel e).symm

def ptEquiv : GtPt D F ≃ GtPtF D F where
  toFun g :=
    { b := g.base
      s := fun χ => castGen (oφ_eq D F g.base χ) (g.form χ)
      isGen := fun χ => castGen_isGen _ (g.form_gen χ)
      s_zero := corr_one_of_mult D F g.base _ (castGen (oφ_eq D F g.base (0 + 0)) (g.form (0 + 0)))
        (by rw [add_zero (0 : D.X)])
        ((corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul 0 0))
      mult := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul χ χ') }
  invFun g :=
    { base := g.b
      form := fun χ => castGen (oφ_eq D F g.b χ).symm (g.s χ)
      form_gen := fun χ => castGen_isGen _ (g.isGen χ)
      form_mul := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.mult χ χ') }
  left_inv g := by
    obtain ⟨b, s, h₁, h₂⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _
  right_inv g := by
    obtain ⟨b, s, h₁, h₂, h₃⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _

variable {D F}

theorem isZero_iff (g : GtPt D F) : (ptEquiv D F g).IsZero ↔ g.IsZero :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)

theorem isAdd_iff (g g' h : GtPt D F) :
    (ptEquiv D F g).IsAdd (ptEquiv D F g') (ptEquiv D F h) ↔ g.IsAdd g' h :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_mul_castGen _ _ _ _ _ _ _)

theorem isIota_iff (y : D.X) (g : GtPt D F) :
    GtPtF.IsIota y (ptEquiv D F g) ↔ GtPt.IsIo y g :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)

theorem isNsmul_iff (k : ℕ) (g h : GtPt D F) :
    GtPtF.IsNsmul k (ptEquiv D F g) (ptEquiv D F h) ↔ g.IsNsmul k h := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    have key : ∀ (i : ℕ) (hi : i < k + 1), g.IsNsmul i ((ptEquiv D F).symm (gs ⟨i, hi⟩)) := by
      intro i
      induction i with
      | zero =>
        intro hi
        exact .zero _ ((isZero_iff _).1 (by rw [Equiv.apply_symm_apply]; exact h0))
      | succ i ih =>
        intro hi
        refine .succ i _ _ (ih (by omega)) ((isAdd_iff _ _ _).1 ?_)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hs ⟨i, by omega⟩
    have := key k (Nat.lt_succ_self k)
    rwa [show gs ⟨k, Nat.lt_succ_self k⟩ = ptEquiv D F h from hl, Equiv.symm_apply_apply] at this
  · intro H
    induction H with
    | zero h hz => exact ⟨fun _ => ptEquiv D F h, (isZero_iff h).2 hz, fun i => i.elim0, rfl⟩
    | succ k h h' _ ha ih =>
      obtain ⟨gs, h0, hs, hl⟩ := ih
      refine ⟨Fin.snoc (α := fun _ => GtPtF D F) gs (ptEquiv D F h'), ?_, fun i => ?_, ?_⟩
      · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0
      · rw [Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.succ_last, Fin.snoc_last, hl]; exact (isAdd_iff _ _ _).2 ha
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc]; exact hs j
      · rw [Fin.snoc_last]

variable (D F)

theorem exists_nsmul_iff (k : ℕ) (y : D.X) (g : GtPt D F) :
    (∃ h : GtPtF D F, GtPtF.IsNsmul k (ptEquiv D F g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h := by
  constructor
  · rintro ⟨h, h₁, h₂⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨w, (isNsmul_iff _ _ _).1 h₁, (isIota_iff _ _).1 h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨ptEquiv D F h, (isNsmul_iff _ _ _).2 h₁, (isIota_iff _ _).2 h₂⟩

theorem qkPt_ext {k : ℕ} {q q' : QkPt D F k} (h₁ : q.y = q'.y) (h₂ : q.g = q'.g) : q = q' := by
  obtain ⟨y, g, h⟩ := q
  obtain ⟨y', g', h'⟩ := q'
  obtain rfl : y = y' := h₁
  obtain rfl : g = g' := h₂
  rfl

def pairEquivOf (k : ℕ) (e : GtPt D F ≃ GtPtF D F)
    (H : ∀ y g, (∃ h : GtPtF D F, GtPtF.IsNsmul k (e g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h) : QPair D F k ≃ QkPt D F k where
  toFun p := ⟨p.1.1, e p.1.2, (H _ _).2 p.2⟩
  invFun q := ⟨(q.y, e.symm q.g), (H _ _).1 (by rw [Equiv.apply_symm_apply]; exact q.eq)⟩
  left_inv p := Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply e p.1.2))
  right_inv q := qkPt_ext D F rfl (Equiv.apply_symm_apply e q.g)

def pairEquiv (k : ℕ) : QPair D F k ≃ QkPt D F k :=
  pairEquivOf D F k (ptEquiv D F) (exists_nsmul_iff D F k)

variable {D F}

theorem rel_iff {k : ℕ} (p p' : QPair D F k) :
    QkPt.Equiv D F (pairEquiv D F k p) (pairEquiv D F k p') ↔ QRel D F k p p' := by
  constructor
  · rintro ⟨z, hz, h, hi, ha⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨z, w, (isIota_iff _ _).1 hi, hz, (isAdd_iff _ _ _).1 ha⟩
  · rintro ⟨z, w, hi, hz, ha⟩
    exact ⟨z, hz, ptEquiv D F w, (isIota_iff _ _).2 hi, (isAdd_iff _ _ _).2 ha⟩

variable (D F)

variable {D F}

variable (D F)

end GlobalTheory.GtPointsCompare
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PhiOperatorCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
open GlobalTheory.GtPointsCompare (castGen pairEquiv ptEquiv rel_iff)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns


theorem phiRel_total (hB : D.TauBimult) (q : QkPt D F k)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) (s : Fam D F k) :
    ∃ s', PhiRel D F k q w s s' :=
  (exists_phi hG q w hw hB s).imp fun _ h => (phiRel_iff hG q w hw _ _).2 h

theorem phiRel_transfer (hB : D.TauBimult) {q q' : QkPt D F k} (he : QkPt.Equiv D F q q')
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q.g.b) (DegPre.lineε k))} (hw : w.IsGen) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F q'.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s s', PhiRel D F k q w s s' ↔ PhiRel D F k q' w' s s' := by
  obtain ⟨w', hw', h⟩ := UT.PhiProj.phiRel_of_equiv hG he hw
  refine ⟨w', hw', fun s s' => ⟨h s s', fun H => ?_⟩⟩
  obtain ⟨r, hr⟩ := phiRel_total hB q hw s
  exact ThetaTranslate.phiRel_unique hG q' hw' (h s r hr) H ▸ hr

theorem weilQkIs_of_equiv (hB : D.TauBimult) {p p' q q' : QkPt D F k} (h : QkPt.Equiv D F p q)
    (h' : QkPt.Equiv D F p' q') {ζ : F} (H : WeilQkIs D F k p p' ζ) : WeilQkIs D F k q q' ζ := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  obtain ⟨v, hv, e⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h) hw
  obtain ⟨v', hv', e'⟩ := phiRel_transfer hB (TorusExt.equiv_symm hB h') hw'
  exact H v v' hv hv' s s₁ s₂ s₃ s₄ ((e' _ _).1 h₁) ((e _ _).1 h₂) ((e _ _).1 h₃) ((e' _ _).1 h₄)

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {E : SecA F P k → Fam D F k → Prop}

section Unif

variable {I : Ideal R} {Dd : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif I Dd P G)

end Unif

end GlobalTheory.PhiOperatorCompare
