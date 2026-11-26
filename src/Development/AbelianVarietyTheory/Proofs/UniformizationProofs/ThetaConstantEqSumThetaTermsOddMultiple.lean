module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAutomorphismInducingFrobeniusAllDegrees
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFiniteOrderOfFixThreeTorsion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ThetaSum

theorem exists_gen_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hσ : σ.IsGen) (m : ℕ) (a : G ⟶ G)
    (ha : a = 𝟙 G ^ m) :
    ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 _, a.left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen := by
  subst ha
  have hL := L.isLB
  have hcube : MulPull.HasGen L.L (thφ G (x3 G)) thε := ⟨c.t, c.isGen⟩
  have hrig : MulPull.HasGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) := ⟨L.rig, L.rigGen⟩
  have hsym : MulPull.HasGen L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨σ, hσ⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull G.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) m
  refine h.of_formEq hL fun U _ h => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Nat.cast_pow]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem coef_congr {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen)
    (h : ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g w' χ = coef s g w χ := by
  refine CoefBasic.coef_eq fun z J hJ => ?_
  rw [h z J hJ]
  exact CoefBasic.isCoef_coef g hw χ s z J hJ

theorem zero_isAdd {o : GtPtF D F} (ho : o.IsZero) (g : GtPtF D F) : o.IsAdd g g := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  refine (isAdd_iff _ _ _).2 ⟨by rw [hb, _root_.one_mul], fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [hv χ y J hJ, hb, C.face₂, _root_.mul_one, _root_.one_mul]

theorem theta_const_sum : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∀ w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → SumF I F (coef ϑ g' w') c ∧ ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ ρ hN th ϑ hϑ m hm p x t c hx hc w hw g' hg' κ hκ w' hw' hv
  obtain ⟨α, s₁, θ, hα, hαn, htw, hθ, hact, hval⟩ := hc
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hm0)
  have hbij := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (m ^ 2) hm2 w₀ hN.1
  obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R I hI D A G hG U).1 m
  have hsm : Function.Injective fun χ : D.toPre.X => m • χ := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  have hpull := (GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hI D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2
    (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
    (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hϑ hσ₁ htw
  rw [hEB] at hpull
  obtain ⟨q₁, q₂⟩ := hpull κ hκ p.g g' ((hEact F p.g g').2 hg') w w' hw.1 hw' hv
  have main : ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero →
      FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧
        ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
    intro s hs o w₁ ho hw₁
    have hΦ := GlobalTheory.T.symmetricLift_oddOrder_acts_as_expansionOperator hL R I hI D A G hG U F (m ^ 2) hm.pow p x hx θ hθ w₀ hN.1 w hw s₁ t σ₁ s hσ₁ hs hact
    obtain ⟨ω₁, hω₁, hωv, hco⟩ := CoefPhi.coef_phi hL R I hI D F (m ^ 2) hm2 p w hw.1 o p.g (zero_isAdd ho p.g) w₁ hw₁.1
    have key : ∀ a, coef s o w₁ (a + p.y) = coef σ₁ p.g w a := fun a =>
      (hco 1 (m ^ 2) le_rfl (Nat.mul_one _).symm p (one_nsmul _).symm rfl w w₁ ω₁
        ⟨hw.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩
        ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩ σ₁ s hΦ a).trans (coef_congr p.g hw.1 (hωv ho hw₁) σ₁ a)
    refine ⟨fun χ => by rw [key, ← hEh, q₁], fun β hβ => ?_⟩
    rw [← sub_add_cancel β p.y, key]
    refine q₂ _ ?_
    rintro ⟨χ, e⟩
    exact hβ χ (by rw [← hEh, e, sub_add_cancel])
  refine ⟨?_, main⟩
  obtain ⟨s, hs, -⟩ := hbij.1 t
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := F)
  obtain ⟨w₁, hw₁⟩ := (CoefBasic.coef_basic R D.toPre F (m ^ 2) o).2.1 ((isZero_iff o).1 ho).1
  obtain ⟨r₁, r₂⟩ := main s hs o w₁ ho hw₁
  have hsum := (EvalZero.value_at_origin hL R I hI D A G hG U F).2.2 w₀ ρ hN (m ^ 2) t s hs o w₁ ho hw₁ c hval
  have := ((AdicSum.sumF_calculus R I hI F D.toPre.X (coef s o w₁) (coef s o w₁) c c).2.2 D.toPre.X
    (fun χ => m • χ + p.y) (fun a b h => hsm (add_right_cancel h))
    (fun β hβ => r₂ β fun χ e => hβ ⟨χ, e.symm⟩)).2 hsum
  rwa [show (coef s o w₁ ∘ fun χ => m • χ + p.y) = coef ϑ g' w' from funext r₁] at this

end GlobalTheory.UT.ThetaSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultipleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_eq_sum_thetaTerms_odd_multiple : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → ThC A ρ m th x t c → ∀ w, TXFrame (m ^ 2) p w → ∀ (g' : GtPtF D.toPre F), GtPtF.IsNsmul m p.g g' → ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), Normd κ → ∀ w' : Frm D.toPre F 1 g'.b, w'.IsGen → (∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J) → SumF I F (coef ϑ g' w') c ∧ ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ → (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0 := by
  first | exact @GlobalTheory.UT.ThetaSum.theta_const_sum | exact GlobalTheory.UT.ThetaSum.theta_const_sum | (intros; apply GlobalTheory.UT.ThetaSum.theta_const_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSections
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSections
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.InducedTranslation

section Transl

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem lift_translT {Z : Over S} (t : Z ⟶ T) (u : Z ⟶ A) (x : T ⟶ A) :
    lift t u ≫ translT A x = lift t ((t ≫ x) * u) := by
  have e : translPt A x = (fst T A ≫ x) * snd T A := rfl
  rw [translT, comp_lift, lift_fst, e, MonObj.comp_mul, lift_fst_assoc, lift_snd]

theorem eq_lift {h : T ⊗ A ⟶ T ⊗ A} (hh : h ≫ fst T A = fst T A) {Z : Over S} (t : Z ⟶ T) (u : Z ⟶ A) :
    lift t u ≫ h = lift t (lift t u ≫ h ≫ snd T A) :=
  hom_ext _ _ (by rw [Category.assoc, hh, lift_fst, lift_fst]) (by rw [Category.assoc, lift_snd])

theorem end_ext {h h' : T ⊗ A ⟶ T ⊗ A} (e : lift (fst T A) (snd T A) ≫ h = lift (fst T A) (snd T A) ≫ h') :
    h = h' := by
  rwa [lift_fst_snd, Category.id_comp, Category.id_comp] at e

theorem translT_comp (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) :=
  end_ext (by rw [← Category.assoc, lift_translT, lift_translT, lift_translT, MonObj.comp_mul, _root_.mul_assoc])

theorem translT_one : translT A (1 : T ⟶ A) = 𝟙 _ :=
  end_ext (by rw [lift_translT, MonObj.comp_one, _root_.one_mul, Category.comp_id])

theorem translT_fst (x : T ⟶ A) : translT A x ≫ fst T A = fst T A := lift_fst _ _

theorem pow_fst (h : CategoryTheory.End (T ⊗ A)) (hh : h.asHom ≫ fst T A = fst T A) (n : ℕ) :
    (h ^ n).asHom ≫ fst T A = fst T A := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih => rw [pow_succ', End.mul_asHom, Category.assoc, hh, ih]

end Transl

theorem map_mul_of_fix_origin (laws : Laws) {S : Scheme.{0}} (P : PolAV S) {T : Over S}
    (h : T ⊗ P.A ⟶ T ⊗ P.A) (hfst : h ≫ fst _ _ = fst _ _) (h0 : ptSecT P.A 1 ≫ h = ptSecT P.A 1)
    {Z : Over S} (t : Z ⟶ T) (u v : Z ⟶ P.A) :
    lift t (u * v) ≫ h ≫ snd _ _ = (lift t u ≫ h ≫ snd _ _) * (lift t v ≫ h ≫ snd _ _) := by
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ T.hom P
  have hg' : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom T.hom :=
    (IsPullback.of_hasPullback T.hom P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd T P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst T P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.left ≫ (fst T P.A).left = (fst T P.A).left := congrArg (·.left) hfst
  let σ : P'.A ⟶ P'.A := Over.homMk (e.hom ≫ h.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])
  have hσ : σ.left ≫ e.hom = e.hom ≫ h.left := by
    change (e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _
    simp
  have ex : ∀ {Z : Over S} (t : Z ⟶ T), ∃ ρ : (Over.mk t.left ⟶ P'.A) →* (Z ⟶ P.A),
      ∀ x, (lift t (ρ x)).left = x.left ≫ e.hom := fun {Z} t => by
    let c : Z ⟶ Over.mk ((Over.mk t.left).hom ≫ T.hom) := Over.homMk (𝟙 _) (by simp)
    refine ⟨MonoidHom.mk' (fun x => c ≫ toBase hg.w x) fun x y => by rw [pm, MonObj.comp_mul], fun x => ?_⟩
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have : IsMonHom σ := laws.rigidity _ _ _ P'.isAb P'.isAb σ (by
    obtain ⟨ρ, hρ⟩ := ex (𝟙 T)
    have hη : (1 : Over.mk (𝟙 T : T ⟶ T).left ⟶ P'.A) = η[P'.A] :=
      (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
    have h1 := hρ 1
    rw [map_one, hη] at h1
    have h2 : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ h.left = (lift (𝟙 T) (1 : T ⟶ P.A)).left :=
      congrArg (·.left) h0
    rw [h1] at h2
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc]
    exact h2)
  obtain ⟨ρ, hρ⟩ := ex t
  have inj : ∀ a b : Z ⟶ P.A, lift t a = lift t b → a = b := fun a b hab => by
    rw [← lift_snd t a, hab, lift_snd]
  have sur : ∀ a : Z ⟶ P.A, ∃ x, ρ x = a := fun a =>
    ⟨Over.homMk ((lift t a).left ≫ e.inv) (by
      rw [← e₂, Category.assoc, e.inv_hom_id_assoc, ← Over.comp_left, lift_fst]; rfl),
      inj _ _ (Over.OverMorphism.ext ((hρ _).trans (by simp)))⟩
  have key : ∀ x, lift t (ρ x) ≫ h ≫ snd _ _ = ρ (x ≫ σ) := fun x => inj _ _ (by
    rw [← eq_lift hfst]
    refine Over.OverMorphism.ext ?_
    rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, Category.assoc, hσ])
  obtain ⟨x, rfl⟩ := sur u
  obtain ⟨y, rfl⟩ := sur v
  rw [← map_mul, key, key, key, MonObj.mul_comp, map_mul]

theorem exists_pow_eq_translT (hL : LL) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] [CharZero F] (p : Spec (CommRingCat.of F) ⟶ S)
    [Finite {x : Over.mk p ⟶ P.A // x ^ 3 = 1}] (ψ : CategoryTheory.End (Over.mk p ⊗ P.A))
    (hψ : ψ.asHom ≫ fst _ _ = fst _ _) {N : ℕ} (hN : 1 ≤ N) (hord : ψ ^ N = 1) {m : ℕ}
    (hm : Nat.card (Equiv.Perm {x : Over.mk p ⟶ P.A // x ^ 3 = 1}) ∣ m) :
    ∃ x : Over.mk p ⟶ P.A, (ψ ^ m).asHom = translT P.A x := by
  obtain ⟨a, ha⟩ : ∃ a, a = ptSecT P.A 1 ≫ ψ.asHom ≫ snd _ _ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : CategoryTheory.End (Over.mk p ⊗ P.A),
      h.asHom = ψ.asHom ≫ translT P.A a⁻¹ := ⟨End.of _, rfl⟩
  have hfst : h.asHom ≫ fst _ _ = fst _ _ := by rw [hh, Category.assoc, translT_fst, hψ]
  have h0 : ptSecT P.A 1 ≫ h.asHom = ptSecT P.A 1 := by
    rw [hh, ← Category.assoc, ptSecT, eq_lift hψ, lift_translT, Category.id_comp, ← ptSecT, ← ptSecT, ← ha,
      inv_mul_cancel]
  have hψh : ψ.asHom = h.asHom ≫ translT P.A a := by
    rw [hh, Category.assoc, translT_comp, mul_inv_cancel, translT_one, Category.comp_id]
  have hmul := fun {Z} (t : Z ⟶ Over.mk p) => map_mul_of_fix_origin hL.1 P h.asHom hfst h0 t
  have hcomm : ∀ x, translT P.A x ≫ h.asHom = h.asHom ≫ translT P.A (ptSecT P.A x ≫ h.asHom ≫ snd _ _) := fun x => end_ext (by
    rw [← Category.assoc, lift_translT, eq_lift hfst, hmul, ← Category.assoc (lift _ _) h.asHom (translT _ _), eq_lift hfst,
      lift_translT, ptSecT, ← Category.assoc (fst _ _), comp_lift, Category.comp_id])
  have hpow : ∀ n : ℕ, ∃ x, (ψ ^ n).asHom = (h ^ n).asHom ≫ translT P.A x :=
    fun n => by
    induction n with
    | zero => exact ⟨1, by rw [translT_one, Category.comp_id, pow_zero, pow_zero]⟩
    | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨a * (ptSecT P.A x ≫ h.asHom ≫ snd _ _), ?_⟩
      rw [pow_succ', pow_succ', End.mul_asHom, End.mul_asHom, hx, ← translT_comp, Category.assoc, Category.assoc,
        ← Category.assoc h.asHom, ← hcomm, Category.assoc, ← hψh]
  have h0' : ∀ n : ℕ, ptSecT P.A 1 ≫ (h ^ n).asHom = ptSecT P.A 1 := fun n => by
    induction n with
    | zero => exact Category.comp_id _
    | succ n ih => rw [pow_succ', End.mul_asHom, ← Category.assoc, ih, h0]
  have hhN : h ^ N = 1 := by
    obtain ⟨x, hx⟩ := hpow N
    have e := congrArg (ptSecT P.A 1 ≫ · ≫ snd _ _) hx
    simp only [hord] at e
    rw [End.one_asHom, Category.id_comp, ← Category.assoc, ← Category.assoc, h0', ptSecT, lift_translT, lift_snd,
      lift_snd, Category.id_comp, _root_.mul_one] at e
    rw [← e, translT_one, Category.comp_id, hord] at hx
    exact End.ext hx.symm
  let φ : (Over.mk p ⟶ P.A) →* (Over.mk p ⟶ P.A) :=
    MonoidHom.mk' (fun x => ptSecT P.A x ≫ h.asHom ≫ snd _ _) (hmul (𝟙 _))
  let f : {x : Over.mk p ⟶ P.A // x ^ 3 = 1} → {x : Over.mk p ⟶ P.A // x ^ 3 = 1} :=
    fun x => ⟨φ x.1, by rw [← map_pow, x.2, map_one]⟩
  have hf : ∀ (n : ℕ) x, ptSecT P.A (f^[n] x).1 = ptSecT P.A x.1 ≫ (h ^ n).asHom := fun n x => by
    induction n with
    | zero => exact (Category.comp_id _).symm
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ', End.mul_asHom, ← Category.assoc, ← ih]
      exact (eq_lift hfst _ _).symm
  have hinj : Function.Injective f := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    refine Function.LeftInverse.injective (g := f^[n]) fun x => Subtype.ext ?_
    have e := congrArg (· ≫ snd _ _) (hf (n + 1) x)
    simp only [hhN] at e
    rwa [End.one_asHom, Category.comp_id, ptSecT, ptSecT, lift_snd, lift_snd] at e
  let π : Equiv.Perm _ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : π ^ m = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h1 : h ^ m = 1 := FiniteOrderFix.eq_one_of_finite_order_of_fix_three_torsion hL S P F p (h ^ m)
    (pow_fst h hfst m) (h0' m) ⟨N, hN, by rw [← pow_mul, mul_comm, pow_mul, hhN, one_pow]⟩ fun x hx => by
      have e : f^[m] ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have := congrArg (fun s : Equiv.Perm _ => s ⟨x, hx⟩) hπ
        simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at this
        exact this
      rw [← hf m ⟨x, hx⟩, e]
  obtain ⟨x, hx⟩ := hpow m
  exact ⟨x, by rw [hx, h1, End.one_asHom, Category.id_comp]⟩

attribute [local instance] TorusExt.gtGroup


open TorusExt in
theorem eq_pow_of_rel {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k m : ℕ} (p : QkPt D F k) (g' : GtPtF D F) (hg' : GtPtF.IsNsmul m g' p.g)
    {E : Type} [Monoid E] (Ind : QkPt D F (k * m) → E → Prop)
    (comp : ∀ p p' p'' ψ ψ', Ind p ψ → (Ind p' ψ' → QkAdd p p' p'' → Ind p'' (ψ' * ψ)) ∧
      (QkPt.Equiv D F p p' → Ind p' ψ) ∧ (Ind p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → Ind p' 1))
    (ex : ∀ q, ∃ τ, Ind q τ) (ψ : E) (hψ : ∀ q : QkPt D F (k * m), q.y = m • p.y → q.g = p.g → Ind q ψ) :
    ∃ τ q, Ind q τ ∧ τ ^ (k * m) = 1 ∧ ψ = τ ^ m := by
  have hg : p.g = m • g' := (isNsmul_iff_eq _ _ _).1 hg'
  have hι : (k * m) • g' = iota hB F p.y := by rw [mul_nsmul', ← hg, qk_nsmul hB]
  let r : ℕ → QkPt D F (k * m) := fun j => qkMk hB (j • p.y) (j • g') (by
    rw [smul_comm, hι, map_nsmul])
  obtain ⟨τ, h1⟩ := ex (r 1)
  have h0 : Ind (r 0) 1 :=
    (comp (r 1) (r 0) (r 0) _ 1 h1).2.2.2 (zero_nsmul _) ((isZero_iff_eq _).2 (zero_nsmul _))
  have hj : ∀ j : ℕ, Ind (r j) (τ ^ j) := fun j => by
    induction j with
    | zero => rwa [pow_zero]
    | succ j ih =>
      rw [pow_succ']
      refine (comp (r j) (r 1) (r (j + 1)) _ _ ih).1 h1 ?_
      have e : r (j + 1) = qkAdd hB (r j) (r 1) := qk_ext (add_nsmul _ _ _) (add_nsmul _ _ _)
      rw [e]
      exact qkAdd_qkAdd hB _ _
  refine ⟨τ, _, h1, (comp (r (k * m)) (r 0) (r 0) _ _ (hj _)).2.2.1
    ((comp (r 0) (r (k * m)) (r 0) _ 1 h0).2.1 ((equiv_iff hB _ _).2 ⟨p.y, ?_, ?_⟩)),
    (comp (r m) (r 0) (r 0) _ _ (hψ (r m) rfl hg.symm)).2.2.1 (hj m)⟩
  · change (k * m) • p.y = 0 • p.y + (k * m) • p.y
    rw [zero_nsmul, zero_add]
  · change (k * m) • g' = 0 • g' + _
    rw [zero_nsmul, zero_add, hι]

theorem exists_translT_indAt :
    LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  intro hL R _ _ _ I hR D A G _ _ hG U F _ _ _ k hk p
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hcard := (hL.1.mulN _ A 3 (by omega)).2.2.2.2 F (jFK (R := R) F) (by norm_num)
  have : Finite {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ 3 = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨m, hm4, hm⟩ : ∃ m, 4 ≤ m ∧
      Nat.card (Equiv.Perm {x : Over.mk (jFK (R := R) F) ⟶ A.A // x ^ 3 = 1}) ∣ m :=
    ⟨4 * _, Nat.le_mul_of_pos_right _ Nat.card_pos, Dvd.intro_left _ rfl⟩
  have hN : 4 ≤ k * m := hm4.trans (Nat.le_mul_of_pos_left _ hk)
  obtain ⟨g', hg'⟩ := (gt_onto_divisible_kernel hL R I hR D F).2.1 m (by omega) p.g
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F k hk p
  obtain ⟨τ, q, h1, hord, e⟩ := eq_pow_of_rel D.tau_bimult p g' hg'
    (E := CategoryTheory.End (TFK (R := R) F ⊗ A.A)) (fun q s => IndAt U.toUnifPre F (k * m) q s.asHom)
    (fun a b c s t hs => by
      obtain ⟨c₁, c₂, c₃, c₄⟩ := GlobalTheory.T.indAt_comp_equiv_unique_id hL R I hR D A G hG U F (k * m) (by omega) a b c s.asHom t.asHom hs
      exact ⟨c₁, c₂, fun ht => End.ext (c₃ hN ht), c₄⟩)
    (fun q => by
      obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_automorphism_inducing_frobenius_all_degrees hL R I hR D A G hG U F (k * m) (by omega) q
      exact ⟨End.of χ.hom, hχ 1 (k * m) le_rfl (_root_.mul_one _).symm q (one_nsmul _).symm rfl⟩)
    (End.of ψ.hom) (hψ m _ (by omega) rfl)
  obtain ⟨x, hx⟩ := exists_pow_eq_translT hL A (jFK (R := R) F) τ h1.1 (by omega : 1 ≤ k * m) hord hm
  have e' : ψ.hom = translT A.A x := (congrArg End.asHom e).trans hx
  refine ⟨x, ?_⟩
  rw [← e']
  exact hψ

end GlobalTheory.InducedTranslation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSectionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, ∃ x : TFK (R := R) F ⟶ A.A, ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ q : QkPt D.toPre F N, q.y = n • p.y → q.g = p.g → IndAt U.toUnifPre F N q (translT A.A x) := by
  first | exact @GlobalTheory.InducedTranslation.exists_translT_indAt | exact GlobalTheory.InducedTranslation.exists_translT_indAt | (intros; apply GlobalTheory.InducedTranslation.exists_translT_indAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelOfAmpleBundleFiniteFlatOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentable
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKLIffMemKLPush
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem memKL_push (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    {T' : Over S'} (x : T' ⟶ A') (hx : MemKL A' L' x) : MemKL A L (pushPt h.1.w x) := by
  obtain ⟨w, hw⟩ := hw
  replace hw := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk (T'.hom ≫ f)
  let T₂ : Over S' := Over.mk ((fst T A).left ≫ T'.hom)
  have sq : (snd T A).left ≫ A.hom = ((fst T A).left ≫ T'.hom) ≫ f :=
    pullback.condition.symm.trans (Category.assoc _ _ _).symm
  let a : T₂ ⟶ T' := Over.homMk (fst T A).left rfl
  let b : T₂ ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have hb : b.left ≫ φ = (snd T A).left := h.1.lift_fst _ _ _
  have k₁ : (lift a b).left ≫ (fst T' A').left = (fst T A).left := congrArg (fun q => q.left) (lift_fst a b)
  have k₂ : (lift a b).left ≫ (snd T' A').left ≫ φ = (snd T A).left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ φ) (lift_snd a b)).trans hb)
  have k₃ : (lift a b).left ≫ ((fst T' A' ≫ x) * snd T' A').left ≫ φ =
      ((fst T A ≫ pushPt h.1.w x) * snd T A).left := by
    have e : lift a b ≫ ((fst T' A' ≫ x) * snd T' A') = (a ≫ x) * b := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    let j : Over.mk (T₂.hom ≫ f) ⟶ T ⊗ A := Over.homMk (𝟙 _) ((Category.id_comp _).trans
      ((Over.w (snd T A)).symm.trans sq))
    have e₁ := h.2 T₂ (a ≫ x) b (j ≫ fst T A ≫ pushPt h.1.w x) (j ≫ snd T A)
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) ((Category.id_comp _).trans hb.symm)
    rw [← MonObj.comp_mul, ← e] at e₁
    exact (Category.assoc _ _ _).symm.trans (e₁.symm.trans (Category.id_comp _))
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T' A').left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T' A').left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ (lift a b).left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L' _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ φ = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]

end

theorem memKL_iff_memKL_push : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) (A' : Over S') [GrpObj A] [GrpObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left) (L' : LB A'.left) (h : IsGrpPullback A' A f φ), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → ∀ (T' : Over S') (x : T' ⟶ A'), GlobalTheory.MemKL A' L' x ↔ GlobalTheory.MemKL A L (pushPt h.1.w x) :=
  fun _ _ _ _ _ _ _ _ _ _ h hL hL' hw _ x => ⟨memKL_push h hL hL' hw x, memKL_of_push h hL hL' hw x⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentable
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem memKL_baseChange_rep : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  intro S S' f B _ L hL H j hrep T' x
  have h := isGrpPullback_pullback B f
  have hL' : (L.pull (pullback.fst B.hom f)).IsLB := LB.isLB_pull hL _
  rw [GlobalTheory.memKL_iff_memKL_push S S' f B _ _ L _ h hL hL' (GlobalTheory.lbIso_self hL') T' x, hrep]
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z.left ≫ j.left = x.left ≫ pullback.fst B.hom f := congrArg (·.left) hz
    refine ⟨Over.homMk (pullback.lift z.left T'.hom (Over.w z)) (pullback.lift_snd _ _ _), ?_⟩
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w x).symm))
    rw [← hz']
    simp [pullback.lift_fst, pullback.lift_fst_assoc]
  · rintro ⟨z, rfl⟩
    refine ⟨Over.homMk (z.left ≫ pullback.fst H.hom f) ?_, ?_⟩
    · have := Over.w z
      simp only [Over.pullback_obj_hom] at this
      simp [pullback.condition, ← this]
    · refine Over.OverMorphism.ext ?_
      change (z.left ≫ pullback.fst H.hom f) ≫ j.left = (z.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst B.hom f
      simp [pullback.lift_fst]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentableStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memKernelOfLineBundle_baseChange_representable : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  first | exact @GlobalTheory.memKL_baseChange_rep | exact GlobalTheory.memKL_baseChange_rep | (intros; apply GlobalTheory.memKL_baseChange_rep <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelFlat

theorem kernelFiniteFlat : Laws → GlobalTheory.Published.KernelFiniteFlatSt := by
  intro hLaw V _ _ A _ hA L hL ha
  obtain ⟨H, j, hj, hfin, hH⟩ := GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample hLaw.globalFns V A hA L hL ha
  refine ⟨H, j, hj, hfin, GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal V H hfin fun m _ => ?_, hH⟩
  let f := spMap (algebraMap V (Localization.AtPrime m))
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have : IsCommMonObj ((Over.pullback f).obj A) := hA'.comm
  have hP : IsProjBy ((Over.pullback f).obj A).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha (Localization.AtPrime m) f
      _ (pullback.fst A.hom f) (pullback.snd A.hom f) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom f)).IsLB := LB.isLB_pull hL _
  have hj' : IsClosedImmersion ((Over.pullback f).map j).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback H.hom f) hfin
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hLaw.globalFns (Localization.AtPrime m) ((Over.pullback f).obj A) hA' hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hLaw _ _ hA' hP _ hL') ((Over.pullback f).obj H)
    ((Over.pullback f).map j) hj' (GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f A L hL H j hH) hfin'

end GlobalTheory.KernelFlat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclic
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ProductAcyclic

theorem acyclic_of_homology_equiv {R : Type} [CommRing R] {C C' : CochainComplex (ModuleCat.{0} R) ℕ}
    (e : ∀ n, Nonempty (C.homology n ≃ₗ[R] C'.homology n)) (h : C.Acyclic) : C'.Acyclic := by
  intro n
  obtain ⟨e⟩ := e n
  have h₁ := h n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton] at h₁ ⊢
  exact e.symm.injective.subsingleton

theorem exists_cover (X : Scheme.{0}) [CompactSpace X] {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    (O : X.Opens) (h : ∀ x, x ∉ V₀ → x ∈ O) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      V 0 = V₀ ∧ ∀ j, j ≠ 0 → V j ≤ O := by
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ W ≤ O} => (W.1 : Set X)) (fun W => W.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (h x hx) O.isOpen
      exact Set.mem_iUnion.2 ⟨⟨W, hW, hWo⟩, hxW⟩)
  refine ⟨s.card, Fin.cons V₀ fun j => (s.equivFin.symm j).1.1, fun j => ?_, ?_, rfl, fun j hj => ?_⟩
  · refine Fin.cases hV₀ (fun j => ?_) j
    exact (s.equivFin.symm j).1.2.1
  · refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hx : x ∈ V₀
    · exact ⟨0, hx⟩
    · obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.1 (hs hx)
      refine ⟨(s.equivFin ⟨W, hW⟩).succ, ?_⟩
      simpa using hxW
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
    exact (s.equivFin.symm j).1.2.2

variable {K : Type} [Field K] {Z T X : Scheme.{0}} {p : Z ⟶ T} {g : T ⟶ Spec (CommRingCat.of K)}
  {q : Z ⟶ X} {h : X ⟶ Spec (CommRingCat.of K)} {F : LB Z}

theorem over_affineOpen (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB)
    {R : Type} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ T} [IsOpenImmersion t] {Y : Scheme.{0}}
    {π : Y ⟶ Z} {f : Y ⟶ Spec (CommRingCat.of R)} (H : IsPullback π f p t)
    {V : T.Opens} (hV : t.opensRange = V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) :
    (∀ i, IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) ∧
    ((∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic) ↔
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V).Acyclic) := by
  have H' : IsPullback (π ≫ q) f h (t ≫ g) := H.paste_horiz sq.flip
  have : IsOpenImmersion π := MorphismProperty.of_isPullback (P := @IsOpenImmersion) H.flip ‹_›
  have hq : IsAffineHom (π ≫ q) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H'.flip inferInstance
  have hsep : IsSeparated f := MorphismProperty.of_isPullback (P := @IsSeparated) H' ‹_›
  have hr : π.opensRange = p ⁻¹ᵁ V := by
    subst hV
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact ⟨f y, by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]⟩
    · rintro x ⟨y, hy⟩
      obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback H x y hy.symm
      exact ⟨w, hw⟩
  have hE (i : ν) : π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = (π ≫ q) ⁻¹ᵁ B i := by
    rw [← hr, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq,
      Scheme.Hom.comp_preimage]
  have hA (i : ν) : IsAffineOpen ((π ≫ q) ⁻¹ᵁ B i) := (hB i).preimage _
  have hA' (i : ν) : IsAffineOpen (π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V)) :=
    (congrArg IsAffineOpen (hE i)).mpr (hA i)
  have hc' : ⨆ i, π ⁻¹ᵁ (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) = ⊤ := by
    simp only [hE]
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion K _ (p ≫ g) F _ π ν
    (fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) hF fun i => hr ▸ inf_le_right
  refine ⟨fun i => ?_, fun h₁ n => ?_, fun h₁ κ _ _ D hD hDc => ?_⟩
  · have h₁ := (hA i).image_of_isOpenImmersion π
    rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_comm] at h₁
  · exact (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ (h₁ ν _ hA' hc') n).of_iso e
  · exact acyclic_of_homology_equiv (cechLB_homology_equiv_of_affine_covers R Y f _ ν _ κ D
      (LB.isLB_pull hF π) hsep hA' hc' hD hDc)
      (MumfordCohom.acyclic_cechLB_of_acyclic _ _ _ _ fun n => (h₁ n).of_iso e.symm)

theorem isAffineOpen_prod (sq : IsPullback p q g h) [IsSeparated h] (hF : F.IsLB) {V : T.Opens}
    (hV : IsAffineOpen V) {ν : Type} [LinearOrder ν] [Fintype ν]
    (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i)) (hc : ⨆ i, B i = ⊤) (i : ν) :
    IsAffineOpen (q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V) :=
  (over_affineOpen (R := Γ(T, V)) sq hF (IsPullback.of_hasPullback p hV.fromSpec)
    hV.opensRange_fromSpec B hB hc).1 i

theorem homology_equiv_over (sq : IsPullback p q g h) [IsSeparated g] [IsSeparated h] (hF : F.IsLB)
    {σ : Type} [LinearOrder σ] [Fintype σ] (V : σ → T.Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVc : ⨆ j, V j = ⊤) (k : σ)
    (H : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z)
      (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t →
      ∀ j, j ≠ k → (∀ y, t y ∈ V j) →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → (cechLB f (F.pull π) D).Acyclic)
    {ν : Type} [LinearOrder ν] [Fintype ν] (B : ν → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hBc : ⨆ i, B i = ⊤) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Z.Opens)
    (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (n : ℕ) :
    Nonempty ((cechLB (p ≫ g) F D).homology n ≃ₗ[K]
      (cechLB (p ≫ g) F fun i => q ⁻¹ᵁ B i ⊓ p ⁻¹ᵁ V k).homology n) := by
  have : T.IsSeparated := ⟨by
    rw [← terminal.comp_from g]
    infer_instance⟩
  have : X.IsSeparated := ⟨by
    rw [← terminal.comp_from h]
    infer_instance⟩
  have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) sq.flip ‹_›
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ K _ (p ≫ g) F κ D _
    (fun i => q ⁻¹ᵁ B i) _ (fun j => p ⁻¹ᵁ V j) hF inferInstance hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hB i) hW)
    (fun j _ hW => MumfordCohom.isAffineOpen_preimage_inf _ (hV j) hW)
    (fun i j => isAffineOpen_prod sq hF (hV j) B hB hBc i) n
  have e₂ := trunc₂HomologyIsoFstSingleton k (secCube (p ≫ g) F fun u : ν ⊕ₗ σ =>
      Sum.elim (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) (ofLex u))
    (fun s hs hs' => by
      have hVs : IsAffineOpen (⨅ j ∈ s, V j) :=
        IsAffineOpen.biInf _ s.finite_toSet hs fun j _ => hV j
      obtain ⟨j, hj, hjk⟩ : ∃ j ∈ s, j ≠ k := by
        by_contra! h₀
        exact hs' (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨hs, h₀⟩)
      have H₀ := IsPullback.of_hasPullback p hVs.fromSpec
      have h₁ := (over_affineOpen (R := Γ(T, ⨅ j ∈ s, V j)) sq hF H₀ hVs.opensRange_fromSpec
        B hB hBc).2.1 (H Γ(T, ⨅ j ∈ s, V j) _ _ _ _ H₀ inferInstance j hjk
          fun y => biInf_le V hj (hVs.range_fromSpec.le ⟨y, rfl⟩))
      obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
        (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) s _ (preimage_biInf V p s)
      exact fun m => (h₁ m).of_iso i₂) n
  obtain ⟨i₂⟩ := MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ g) F
    (fun i => q ⁻¹ᵁ B i) (fun j => p ⁻¹ᵁ V j) {k} (p ⁻¹ᵁ V k) (by simp)
  exact ⟨e₁ ≪≫ₗ (e₂ ≪≫ (HomologicalComplex.homologyMapIso i₂ n).symm).toLinearEquiv⟩

theorem acyclic_of_over_affine_and_converse : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ((∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic)) ∧ ∀ t₀ : T, IsClosed ({t₀} : Set T) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ≠ t₀) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  intro K _ Z T p g X q h sq _ _ _ _ F hF
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  obtain ⟨m, B, hB, hBc, -, -⟩ := exists_cover X (isAffineOpen_bot X) ⊤ fun _ _ => trivial
  refine ⟨fun H κ _ _ D hD hc => ?_, fun t₀ ht₀ H hac R _ t Y π f H₀ ht => ?_⟩
  · obtain ⟨r, V, hV, hVc, -, -⟩ := exists_cover T (isAffineOpen_bot T) ⊤ fun _ _ => trivial
    have H₀ := IsPullback.of_hasPullback p (hV 0).fromSpec
    refine acyclic_of_homology_equiv (fun n => ?_) ((over_affineOpen (R := Γ(T, V 0)) sq hF H₀
      (hV 0).opensRange_fromSpec B hB hBc).2.1 (H Γ(T, V 0) _ _ _ _ H₀ inferInstance))
    exact (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht _ _ _ => H R t Y π f H₁ ht) B hB hBc D hD hc n).map fun e => e.symm
  · by_cases h₀ : t₀ ∈ t.opensRange
    swap
    · exact H R t Y π f H₀ ht fun y hy => h₀ ⟨y, hy⟩
    obtain ⟨r, V, hV, hVc, hV₀, hV₁⟩ := exists_cover T (isAffineOpen_opensRange t)
      ⟨{t₀}ᶜ, ht₀.isOpen_compl⟩ fun x hx hx' => hx ((show x = t₀ from hx') ▸ h₀)
    let P : Fin (m + 1) ×ₗ Fin (r + 1) → Z.Opens := fun u =>
      q ⁻¹ᵁ B (ofLex u).1 ⊓ p ⁻¹ᵁ V (ofLex u).2
    have hP (u) : IsAffineOpen (P u) := isAffineOpen_prod sq hF (hV _) B hB hBc _
    have hPc : ⨆ u, P u = ⊤ := by
      refine top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hBc.ge (Set.mem_univ (q x)))
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hVc.ge (Set.mem_univ (p x)))
      exact ⟨toLex (i, j), hi, hj⟩
    refine (over_affineOpen sq hF H₀ hV₀.symm B hB hBc).2.2 ?_
    exact acyclic_of_homology_equiv (homology_equiv_over sq hF V hV hVc 0
      (fun R _ t Y π f H₁ ht j hj hy => H R t Y π f H₁ ht fun y e => hV₁ j hj (hy y) e)
      B hB hBc P hP hPc) (hac _ P hP hPc)

end GlobalTheory.ProductAcyclic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleProductAcyclicOfAffineBaseAcyclicStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_product_acyclic_of_affine_base_acyclic : ∀ (K : Type) [Field K] (Z T : Scheme.{0}) (p : Z ⟶ T) (g : T ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0}) (q : Z ⟶ X) (h : X ⟶ Spec (CommRingCat.of K)), IsPullback p q g h → IsSeparated g → QuasiCompact g → IsSeparated h → QuasiCompact h → ∀ F : LB Z, F.IsLB → ((∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic)) ∧ ∀ t₀ : T, IsClosed ({t₀} : Set T) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ y, t y ≠ t₀) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Z).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (p ≫ g) (F) D).Acyclic) → (∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f p t → IsOpenImmersion t → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (Y).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (f) (F.pull π) D).Acyclic)) := by
  first | exact @GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse | exact GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse | (intros; apply GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse <;> assumption)
end
end
