module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem value_of_normalAt {κ : Rule} (hH : Homog (fun _ => 1) κ) (hT : ThetaOne κ) (x : KeyIn ℂ)
    {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ} (hab : KeyPow.charHalf x.P.g a b)
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) : (κ ℂ x : ℂ) = M.det ^ 4 / c ^ 8 := by
  have key := KeyPow.value_at_normalForm (fun _ => 1) 0 (κ ℂ) x.P.g a b (Nat.zero_le _)
    (fun P hg rig hr th hth v hv th' hth' v' hv' a M _ h₁ h₂ =>
      hH ℂ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂)
    (fun z hz σ hN => by
      obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (KeyPow.normalAt_one_iff z σ _ _).1 hN
      exact hT z u σ _ _ h₁ h₂ (fun i => hab.1 _) (fun i => hab.2 _) h₃ h₄ h₅ h₆)
    x rfl τ M c hc hM h
  simpa only [_root_.pow_one] using key

theorem value_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ →
    ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  intro κ hH hT x y j hp
  obtain ⟨⟨τ, M, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  have hre : ∀ f : Fin x.P.g → ℂ, (∀ i, f i = 0 ∨ f i = 1 / 2) → (fun k => ((f k).re : ℂ)) = f := by
    intro f hf
    funext k
    rcases hf k with h | h <;> rw [h] <;> norm_num
  have ha := hre a hab.1
  have hb := hre b hab.2
  obtain ⟨e, τ', M', hdet, hN'⟩ := KeyPow.normalAt_pow x y j τ M (fun k => (a k).re) (fun k => (b k).re) c hp
    (by rw [ha, hb]; exact hN)
  have hx := value_of_normalAt hH hT x hab hc hM hN
  have hy := value_of_normalAt hH hT y
    ⟨fun p => by rw [congrFun ha (e.symm p).2]; exact hab.1 _,
      fun p => by rw [congrFun hb (e.symm p).2]; exact hab.2 _⟩
    (pow_ne_zero j hc) (by rw [hdet]; exact pow_ne_zero j hM) hN'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hy, hx, hdet, div_pow, ← _root_.pow_mul, ← _root_.pow_mul, ← _root_.pow_mul,
    ← _root_.pow_mul, mul_comm j 4, mul_comm j 8]

end GlobalTheory.KeyCl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  first | exact @GlobalTheory.KeyCl.value_pow_complex | exact GlobalTheory.KeyCl.value_pow_complex | (intros; apply GlobalTheory.KeyCl.value_pow_complex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SymRoot

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

def rigCls (c : Pic A.left) : Pic A.left := c - pull (1 : A ⟶ A).left c

theorem pull_rigCls (c : Pic A.left) (x : T ⟶ A) :
    pull x.left (rigCls c) = pull x.left c - pull (1 : T ⟶ A).left c := by
  rw [rigCls, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_one]

theorem lam_rigCls (c : Pic A.left) (x y : T ⟶ A) : lam (rigCls c) x y = lam c x y := by
  simp only [lam, pull_rigCls]
  abel

theorem lam_diag [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hs : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL) :
    lam (cls L hL) (𝟙 A) (𝟙 A) = 2 • rigCls (cls L hL) := by
  have h := lam_mul_left hL hΘ (𝟙 A) (𝟙 A)⁻¹ (𝟙 A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls L hL) (𝟙 A)⁻¹ (𝟙 A) = -(2 • rigCls (cls L hL)) := by
    rw [lam, inv_mul_cancel, Hom.inv_def, Category.id_comp, hs, Over.id_left, pull_id, rigCls]
    abel
  rw [e] at h
  exact add_neg_eq_zero.1 h.symm

theorem exists_polAV_sqOf : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  intro laws h k o _ ζ R _ _ β c L ⟨ha, hk⟩ hdim hL hΛ hs
  have hA := c.ab
  have hd : c.diag.IsLB := pull_isLB c.isLB _
  have hp : IsProjBy c.A.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ c.A c.diag hA hd ha R (𝟙 _) _ (𝟙 _) c.A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  have hΘ : ∃ t : LB.Gen (Theta c.A L), t.IsGen := CubeAffine.triv_theta_of_isProjBy laws R c.A hA hp L hL
  have s₁ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls L hL) = cls L hL :=
    ((cls_eq_iff hL (pull_isLB hL _)).2 hs).symm
  have e₀ : cls c.P c.isLB = lam (cls L hL) (fst c.A c.A) (snd c.A c.A) :=
    ((cls_eq_iff (LB.isLB_linComb hL _ _) c.isLB).2 hΛ).symm.trans (cls_cube_two hL _ _ (LB.isLB_linComb hL _ _))
  obtain ⟨M, hM, e⟩ := cls_surj (rigCls (cls L hL))
  have e₁ : cls c.P c.isLB = lam (cls M hM) (fst c.A c.A) (snd c.A c.A) := by rw [e, lam_rigCls, e₀]
  have e₂ : pull (GrpObj.inv : c.A ⟶ c.A).left (cls M hM) = cls M hM := by
    rw [e, pull_rigCls, s₁, rigCls]
  have e₃ : cls c.diag hd = 2 • cls M hM := by
    refine (cls_pull c.isLB _ _).trans ?_
    rw [e₀, pull_lam, lift_fst, lift_snd, lam_diag hL hΘ s₁, e]
  have hr : Out.Rigidified c.A M := by
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ((cls_pull hM _ _).trans ?_)
    have e₄ : (η[c.A] : 𝟙_ _ ⟶ c.A) = 1 := by rw [Hom.one_def]; simp
    have := pull_rigCls (cls L hL) η[c.A]
    rw [← e₄, sub_self, ← e] at this
    exact this
  have hsym : Out.Sym c.A M := fun s => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (LB.isLB_linComb hM _ _)).1 ?_
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, e₂, one_smul, neg_smul, add_neg_cancel]⟩
  have hamp : Out.RelAmple c.A M := by
    have f : IsFinite (𝟙 c.A : c.A ⟶ c.A).left := by rw [Over.id_left]; infer_instance
    refine (relAmple_finite_pow_iso _ c.A c.A (𝟙 _) M 2 two_pos hA hA hM f).2.1.1
      ((relAmple_finite_pow_iso _ c.A c.A (𝟙 _) _ 2 two_pos hA hA hd f).2.2.2 _ (isLB_lbPow hM 2) ?_ ha)
    exact (cls_eq_iff hd (isLB_lbPow hM 2)).1 (e₃.trans (cls_lbPow hM 2 _).symm)
  have hid : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  refine ⟨{ A := c.A, isAb := hA, g := h, smoothDim := hdim, L := M, isLB := hM, rigid := hr, sym := hsym,
            ample := hamp, ktriv := ThetaExtend.kTriv_of_lam hM c.isLB e₁ hk }, 𝟙 _,
    (isGrpPullback_of_iso (Iso.refl c.A)).congr rfl rfl, rfl, 𝟙 _, ⟨by simp, by simp⟩, ?_⟩
  refine (cls_eq_iff (LB.isLB_linComb hM _ _) (pull_isLB c.isLB _)).1 ?_
  exact (cls_cube_two hM _ _ (LB.isLB_linComb hM _ _)).trans (e₁.symm.trans (pull_id _).symm)

end GlobalTheory.SymRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  first | exact @GlobalTheory.SymRoot.exists_polAV_sqOf | exact GlobalTheory.SymRoot.exists_polAV_sqOf | (intros; apply GlobalTheory.SymRoot.exists_polAV_sqOf <;> assumption)
end
end
