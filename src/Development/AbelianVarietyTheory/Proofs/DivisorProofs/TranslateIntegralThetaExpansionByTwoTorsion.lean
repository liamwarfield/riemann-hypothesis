module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAdd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Transl

theorem pG_comp_lift_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ g a β hβm e hβ hab h h₁ h₂
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift (thick R I e ≫ a.left) (𝟙 _) (by
      rw [Category.assoc, Over.w a]; exact (Category.comp_id _).trans (Category.id_comp _).symm))
      (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG I e G).left = thick R I e ≫ a.left := pullback.lift_fst _ _ _
  have hh : h = (tr ae).left := by
    apply pullback.hom_ext
    · exact h₂.trans (tr_fst hae).symm
    · exact h₁.trans (Over.w (tr ae)).symm
  subst hh
  have k₁ := TorusCoord.im_mul (U.gt e) (toUnit _ ≫ ae) (𝟙 (thickObj R I e G))
  have k₂ : TorusCoord.im (U.gt e) (toUnit (thickObj R I e G) ≫ ae) = toUnit _ ≫ g.b := by
    apply Over.OverMorphism.ext
    show ((thickObj R I e G).hom ≫ ae.left) ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ g.b.left
    rw [Category.assoc, Category.assoc]
    exact congrArg ((thickObj R I e G).hom ≫ ·) (hab _ (Over.w ae) hae)
  have k₃ : TorusCoord.im (U.gt e) (𝟙 (thickObj R I e G)) = (U₂.gt e).pG ≫ β.hom :=
    Over.OverMorphism.ext ((Category.id_comp _).trans hβ.symm)
  have k₄ : (U₂.gt e).pG ≫ (β.hom * (toUnit _ ≫ g.b)) = ((U₂.gt e).pG ≫ β.hom) * (toUnit _ ≫ g.b) := by
    rw [MonObj.comp_mul, ← Category.assoc _ (toUnit _), comp_toUnit]
  rw [k₂, k₃, _root_.mul_comm (toUnit _ ≫ g.b), ← k₄] at k₁
  exact congrArg (fun q => q.left) k₁

end GlobalTheory.MumCmp.Transl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAddStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (a : 𝟙_ (Over (Sp R)) ⟶ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R I e ≫ g.b.left) → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
  first | exact @GlobalTheory.MumCmp.Transl.pG_comp_lift_translate | exact GlobalTheory.MumCmp.Transl.pG_comp_lift_translate | (intros; apply GlobalTheory.MumCmp.Transl.pG_comp_lift_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorCorrectedTorusCoordinateRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorCorrectedTorusCoordinateRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslRatio

theorem prod_gtφT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) :
    ∏ k, h (ρ.left ≫ DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h ((toUnit T' ≫ D.c χ) * (ρ ≫ b)).left)⁻¹ * h (toUnit T' ≫ D.c χ).left * h (ρ ≫ b).left *
        (h (1 : T' ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four, ← comp_toUnit ρ, Category.assoc, ← MonObj.comp_mul, ← MonObj.comp_one ρ]
  show h (ρ ≫ ((toUnit T ≫ D.c χ) * b)).left ^ (-1 : ℤ) * h (ρ ≫ toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
    h (ρ ≫ b).left ^ (1 : ℤ) * h (ρ ≫ (1 : T ⟶ D.P.A)).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem formEq_translate {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R)
    {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (hT : T ⟶ T) (p : T ⟶ D.P.A)
    (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (hp : hT ≫ p = (p₂ ≫ β) * (toUnit T ≫ b)) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => hT.left ≫ D.Oφ p χ k)
        (Sum.elim (fun k : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2)
          (fun k => (toUnit T).left ≫ DegPre.gtφT D _ b χ k)))
      (Sum.elim Oinvε (fun k => - Sum.elim (fun k : Fin 4 × Fin 3 => Oinvε k.1 * twε k.2) DegPre.gtε k))
      (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D.c χ) (D.c χ) k) ![1, -1, 1, -1] := by
  intro U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ twφ D₂ D β b i) ^ twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k =
      ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ k : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ k.1 ≫ twφ D₂ D β b k.2) ^ (Oinvε k.1 * twε k.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] :
        Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β * (toUnit T ≫ b) =
      (p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.assoc, hc, mul_right_comm]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (hT.left ≫ D.Oφ p χ k) ^ (Oinvε k) =
      (h ((p₂ ≫ β) * (toUnit T ≫ b) * (toUnit T ≫ D.c χ)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h ((p₂ ≫ β) * (toUnit T ≫ b)).left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
    simp only [WeightPf.Oφ_comp]
    rw [Fin.prod_univ_four, ← hp]
    show h ((hT ≫ p) * (toUnit T ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (1 : ℤ) *
      h (hT ≫ p).left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
    simp only [zpow_neg, zpow_one]
  have hS : ∏ k, h ((toUnit T).left ≫ DegPre.gtφT D _ b χ k) ^ (DegPre.gtε k) =
      (h ((toUnit T ≫ D.c χ) * (toUnit T ≫ b)).left)⁻¹ *
      h (toUnit T ≫ D.c χ).left * h (toUnit T ≫ b).left * (h (1 : T ⟶ D.P.A).left)⁻¹ :=
    prod_gtφT (toUnit T) b χ h
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, hC, hS, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, h0, h3, _root_.one_mul, Category.assoc, hc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio_gen : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ gp w hw χ₂ χ hc h hh hp
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let hT : T ⟶ T := Over.homMk h ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) hh))
  obtain ⟨t₁, ht₁, hv₁⟩ := GlobalTheory.Mum.GenTransport.exists_transport D.P.isLB D₂.P.isLB _ _ w hw _ _
    (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_translate D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) hT g.pG g₂.pG β gp.b
    (Over.OverMorphism.ext hp |>.trans (by
      show g₂.pG ≫ (β * (toUnit D₂.P.A ≫ gp.b)) = _
      rw [MonObj.comp_mul, comp_toUnit_assoc])) χ₂ χ hc
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) h) (LB.invGen D.P.L _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L _ _ (gp.s χ) ((thickObj R I e G).hom ≫ thick R I e)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.t_gen χ) _) (DVR.invGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁ (DVR.pullGen_isGen _ _ _ _ (gp.isGen χ) _))))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r)
    ((val_inv _ r).trans (congrArg (·⁻¹) ((val_mul hJ _ _ r).trans
      (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r)))))))

end GlobalTheory.MumCmp.TranslRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorCorrectedTorusCoordinateRatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_corrected_torusCoordinate_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)), w.IsGen → ∀ (χ₂ : D₂.X) (χ : D.X), D₂.c χ₂ ≫ β = D.c χ → ∀ h : (thickObj R I e G).left ⟶ (thickObj R I e G).left, h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ g.pG.left = g₂.pG.left ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b 0 → ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ GlobalTheory.CoordCompare.diffφ (D.prBe I e) (D.c χ) (D.c χ) k) ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val u r z J = val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  first | exact @GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen | exact GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen | (intros; apply GlobalTheory.MumCmp.TranslRatio.exists_ratio_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.twistRatio_eq_one_at_unit : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  intro R _ _ I D D₂ e G _ _ g g₂ β gp w χ₂ χ a h hh hf hcorr z J J' hJ hJ'
  set o := (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G) with ho
  have hom1 : o.left ≫ (thickObj R I e G).hom = 𝟙 _ := Over.w o
  have e1 : o.left ≫ h ≫ (thickObj R I e G).hom = 𝟙 _ := by rw [hh, hom1]
  have f1 : (Over.map (thick R I e)).map o ≫ fstG I e G = 1 := by
    have := GlobalTheory.FormalPoint.map_mul_fstG (R := R) (I := I) (e := e) (G := G) o o
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  let T := (Over.map (thick R I e)).obj (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))))
  have tu : (toUnit T).left = thick R I e := by
    have := Over.w (toUnit T)
    simpa [T] using this
  have e2 : o.left ≫ h ≫ (fstG I e G).left = thick R I e ≫ a.left := by
    rw [hf]
    show ((Over.map (thick R I e)).map o ≫ fstG I e G ≫ ((toUnit G ≫ a) * 𝟙 G)).left = _
    rw [← Category.assoc, f1, MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, _root_.mul_one,
      Over.comp_left, tu]
  have hc := hcorr (o.left ≫ h) (by simpa [Category.assoc] using e1) (by simpa [Category.assoc] using e2)
  have va := val_corr hJ hc (𝟙 _)
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at va
  have vb : val (g₂.t χ₂) o.left z J' = 1 := GlobalTheory.TorusCoord.val_unit g₂ χ₂ hJ'
  let f : (_ ⟶ D₂.P.A.left) → _ := fun ψ => gv w ψ z (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ψ)
  have e0 : ∀ k, o.left ≫ D₂.Oφ g₂.pG χ₂ k = D₂.Oφ (1 : T ⟶ D₂.P.A) χ₂ k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map o) g₂.pG χ₂ k).trans
      (congrArg (D₂.Oφ · χ₂ k) (GlobalTheory.TorusCoord.im_one g₂))
  have vc : (∏ k, f (o.left ≫ D₂.Oφ g₂.pG χ₂ k) ^ Oinvε k) = 1 := by
    refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
    rw [Fin.prod_univ_four]
    show f ((1 : T ⟶ D₂.P.A) * (toUnit T ≫ D₂.c χ₂)).left ^ (-1 : ℤ) * f (toUnit T ≫ D₂.c χ₂).left ^ (1 : ℤ) *
      f (1 : T ⟶ D₂.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D₂.P.A).left ^ (-1 : ℤ) = 1
    rw [_root_.one_mul]
    simp
  have vc' : (∏ k, gv w (o.left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((o.left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (o.left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) = 1 := vc
  rw [vc', vb, ← Category.assoc, hom1, Category.id_comp, va, _root_.one_mul, _root_.one_mul, mul_inv_cancel]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCoordinateRatio_eq_one_unitSection : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X) (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → (∀ ae : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left, ae ≫ (thickObj R I e G).hom = 𝟙 _ → ae ≫ (fstG I e G).left = thick R I e ≫ a.left → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.t χ) ae) (LB.pullGen D.P.L _ _ (gp.s χ) (thick R I e))) → ∀ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (J : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D.P.A.left) → D.P.L.ι) (J' : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → val (g.t χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ h) z J * ((∏ k, gv w ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J (((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J' * val (gp.s χ) ((1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = 1 := by
  first | exact @GlobalTheory.Mum.twistRatio_eq_one_at_unit | exact GlobalTheory.Mum.twistRatio_eq_one_at_unit | (intros; apply GlobalTheory.Mum.twistRatio_eq_one_at_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwCoordInv

open GlobalTheory.CoordCompare TorusCoord

theorem ratio_translate_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  intro R _ _ I D D₂ e G _ _ g g₂ β _ _ hβ gp w χ₂ χ hker a₀ h hh hf Z r r' z J J' hJ hJ' hq
  obtain ⟨h₁, h₂⟩ := ratio_invariant g g₂ β hβ χ χ₂ hker r r' z J J' hJ hJ' hq
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% hq]
  have hprod : ∀ k, r ≫ D₂.Oφ g₂.pG χ₂ k = r' ≫ D₂.Oφ g₂.pG χ₂ k := fun k =>
    Oφ_congr χ₂ g₂.pG r r' h₁ k
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hq)
  let hO : thickObj R I e G ⟶ thickObj R I e G := Over.homMk h hh
  have hfO : (Over.map (thick R I e)).map hO ≫ fstG I e G =
      fstG I e G ≫ ((toUnit G ≫ a₀) * 𝟙 G) := Over.OverMorphism.ext hf
  have hsh : ∀ x : Z' ⟶ thickObj R I e G, (Over.map (thick R I e)).map (x ≫ hO) ≫ fstG I e G =
      (toUnit _ ≫ a₀) * ((Over.map (thick R I e)).map x ≫ fstG I e G) := fun x => by
    rw [Functor.map_comp, Category.assoc, hfO, ← Category.assoc, MonObj.comp_mul, comp_toUnit_assoc,
      Category.comp_id]
  have hkey : b ≫ hO = (τ ≫ g.i) * (b' ≫ hO) := by
    apply FormalPoint.eq_of_map_fstG
    rw [hsh, FormalPoint.map_mul_fstG, hsh, hτ, FormalPoint.map_mul_fstG, mul_left_comm]
  have v₁ := val_torus_mul g χ (Z := Z') hJ τ _ (b ≫ hO) (b' ≫ hO) rfl hkey
  have v₂ := val_torus_mul g χ (Z := Z') hJ τ _ b b' rfl hτ
  let k : Z ⟶ (thickObj R I e G).left := (τ ≫ g.i).left
  have v₁' : val (g.t χ) (r ≫ h) z J = val (g.t χ) k z J * val (g.t χ) (r' ≫ h) z J := v₁
  have v₂' : val (g.t χ) r z J = val (g.t χ) k z J * val (g.t χ) r' z J := v₂
  have hB : val (g₂.t χ₂) r z J' = val (g.t χ) k z J * val (g₂.t χ₂) r' z J' := by
    rw [v₂'] at h₂
    rw [mul_inv_eq_iff_eq_mul.1 h₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have hP : (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) =
      ∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z
        (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i))
        (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k :=
    Finset.prod_congr rfl fun k _ => by rw [hprod k]
  have hS : val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J =
      val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J := by
    rw [reassoc_of% hw]
  rw [hP, hS, v₁', hB]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwCoordInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCoordinateRatio_fibre_invariant : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β] [Mono β.left], g₂.pG ≫ β = g.pG → ∀ (gp : GtPt D (𝟙_ (Over (Sp R)))) (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β gp.b) GlobalTheory.MumCmp.twε)) (χ₂ : D₂.X) (χ : D.X), (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A → r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A → val (g.t χ) r z J = val (g₂.t χ₂) r z J') → ∀ (a : 𝟙_ (Over (Sp R)) ⟶ G) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (thickObj R I e G).hom = (thickObj R I e G).hom → h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' → r ≫ g.q.left = r' ≫ g.q.left → val (g.t χ) (r ≫ h) z J * ((∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' * val (gp.s χ) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ = val (g.t χ) (r' ≫ h) z J * ((∏ k, gv w (r' ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r' ≫ D₂.Oφ g₂.pG χ₂ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β gp.b i)) (J' (r' ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r' z J' * val (gp.s χ) (r' ≫ (thickObj R I e G).hom ≫ thick R I e) z J)⁻¹ := by
  first | exact @GlobalTheory.TwCoordInv.ratio_translate_invariant | exact GlobalTheory.TwCoordInv.ratio_translate_invariant | (intros; apply GlobalTheory.TwCoordInv.ratio_translate_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslCoord

theorem coord_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlev A₂ D₂ U₂ wL hwL β hβ hp w hw xe hker hc e h hh hfst χ Z r z J J' hJ hJ'
  have hpg := GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβ e (hp e)
    (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh hfst
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_generator_corrected_torusCoordinate_ratio (U.gt e) (U₂.gt e) β.hom g w hw χ (xe χ) (hc χ) h hh hpg
  have hp' : (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := Over.OverMorphism.ext (hp e)
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.CoordCompare.exists_gen_of_val_eq D.toPre.P.isLB _ _ (U.gt e).q.left u hu
    (fun Z r r' z J hJ hrr => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB z
      rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_fibre_invariant (U.gt e) (U₂.gt e) β.hom hp' g w χ (xe χ)
        (fun Z r z J J' hJ hJ' h1 h2 => hker e Z r z J J' hJ hJ' h1 h2 χ) a h hh hfst r r' z J J' hJ hJ' hrr)
  have h1 := GlobalTheory.CoordCompare.val_eq_one GlobalTheory.globalFns_holds (D.toPre.c (xe χ)) _ rfl v hv (fun y J hJ => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB y
      have := (U.gt e).q_hom
      have k := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, MonObj.one_comp] at k
      rw [k, hu' _ _ y J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_eq_one_unitSection (U.gt e) (U₂.gt e) β.hom g w χ (xe χ) a h hh hfst (fun ae h1 h2 => (hlev e ae h1 h2).2 (xe χ)) y J J' hJ hJ')
    Z (r ≫ (U.gt e).q.left) z J hJ
  rw [hv' Z r z J hJ, hu' Z r z J J' hJ hJ', mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.MumCmp.TranslCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinate_uniformisation_translate_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  first | exact @GlobalTheory.MumCmp.TranslCoord.coord_translate | exact GlobalTheory.MumCmp.TranslCoord.coord_translate | (intros; apply GlobalTheory.MumCmp.TranslCoord.coord_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TwistedExpTransport


set_option maxHeartbeats 1600000 in
theorem expandsAt_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  intro R _ _ I D D₂ A A₂ G _ _ U U₂ a g β xe w wL ν e h hG hp h1 h2 σ σ₂ f f₂ hσ hf hE
  classical
  have hu : (U₂.gt e).pG.left ≫ (toUnit D₂.toPre.P.A).left = (thickObj R I e G).hom ≫ thick R I e := by
    have e1 := Over.w (toUnit D₂.toPre.P.A)
    have e2 := Over.w (U₂.gt e).pG
    have e3 : (𝟙_ (Over (Spec (CommRingCat.of R)))).hom = 𝟙 _ := rfl
    rw [e3, Category.comp_id] at e1
    rw [e1, e2]
    rfl
  obtain ⟨S, hS⟩ := expandsAt_val U e 1 σ f hE
  refine expandsAt_of_val U₂ e 1 σ₂ f₂ (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  choose N hN using fun ψ : (thickObj R I e G).left ⟶ G.left => exists_chart U.LG.isLB (ψ y)
  have hN : Good U.LG.L y N := hN

  let ω : ((thickObj R I e G).left ⟶ D₂.toPre.P.A.left) → ((thickObj R I e G).left.presheaf.stalk y)ˣ :=
    fun ψ => gv w ψ y (fun i => J (ψ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' ψ)
  have hω := fun χ => GlobalTheory.ExpTrans.prod_fam U₂ e 1 ω χ
  have hF : ∀ χ, sval (f (xe χ)) (h ≫ pGl U e) y J *
      (val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J * val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val =
      (∏ κ, ω (pGl U₂ e ≫ D₂.toPre.famφB χ κ) ^ DegPre.famε 1 κ).val * sval (f₂ χ) (pGl U₂ e) y J' := by
    intro χ
    have := hf χ _ (pGl U₂ e) y J J' hJ hJ'
    rw [hu] at this
    rw [hp]
    exact this
  have hT : ∀ χ, val ((U.gt e).t (xe χ)) h y J =
      (∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k) * val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J' *
        val (g.s (xe χ)) ((thickObj R I e G).hom ≫ thick R I e) y J := by
    intro χ
    have := h2 χ _ (𝟙 _) y J J' hJ hJ'
    simp only [Category.id_comp] at this
    exact this
  refine ⟨fun χ hχ => ?_, fun jL' hL' => ?_⟩
  · have hi : xe χ ∉ S := fun hc => hχ (Finset.mem_map.2 ⟨xe χ, hc, xe.symm_apply_apply χ⟩)
    have z0 := (hS _ h y J hJ).1 _ hi
    have := hF χ
    rw [z0, zero_mul] at this
    exact (Units.mul_right_eq_zero _).1 this.symm
  · obtain ⟨N', hN', eN'⟩ := exists_good U₂.LG.L U₂.LG.isLB y (K := PUnit) (fun _ => fGl I G e) (fun _ => jL')
      (fun _ _ _ => rfl) (fun _ => hL')
    have eN : N' (fGl I G e) = jL' := eN' PUnit.unit
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
      have m := hN (h ≫ fGl I G e)
      have e' : N (h ≫ fGl I G e) = N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left) := congrArg N hG
      rw [e'] at m
      exact m
    have W' : ω (pGl U₂ e) * wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' =
        wv U e h y (J (h ≫ pGl U e)) (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) *
          gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL' *
          val ν ((thickObj R I e G).hom ≫ thick R I e) y J := by
      have := h1 _ (𝟙 _) y J J' N N' hJ hJ' hN hN'
      simp only [Category.id_comp] at this
      rw [hG, eN] at this
      exact this
    have Sg : sv U 1 σ (h ≫ fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) =
        (gw wL (fGl I G e) y (N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) jL').val * sv U₂ 1 σ₂ (fGl I G e) y jL' := by
      have := hσ _ (fGl I G e) y N N' hN hN'
      rw [sval_of σ _ y N (fun _ => N (fGl I G e ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun _ => by rw [Category.comp_id]),
        sval_of σ₂ _ y N' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact eN), eN] at this
      rw [hG]
      exact this
    have E := (hS _ h y J hJ).2 _ hL₁
    refine (ω (pGl U₂ e)).mul_right_inj.1 ?_
    have key : ∀ χ, (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
        (sval (f (xe χ)) (h ≫ pGl U e) y J * (val ((U.gt e).t (xe χ)) h y J).val) =
        (ω (pGl U₂ e)).val * (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) := by
      intro χ
      have hF' := hF χ
      have hω' := congrArg Units.val (hω χ)
      simp only [Units.val_mul, pow_one] at hF' hω'
      rw [hT χ]
      simp only [Units.val_mul]
      linear_combination ((∏ k, ω (Oφl U₂ e χ k) ^ Oinvε k).val * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hF' +
        (sval (f₂ χ) (pGl U₂ e) y J' * (val (tG U₂ e χ) (𝟙 (thickObj R I e G).left) y J').val) * hω'
    have L1 : (ω (pGl U₂ e)).val * ((wv U₂ e (𝟙 _) y (J' (pGl U₂ e)) jL' ^ 1).val * sv U₂ 1 σ₂ (fGl I G e) y jL') =
        (val ν ((thickObj R I e G).hom ≫ thick R I e) y J).val *
          ∑ α ∈ S, sval (f α) (h ≫ pGl U e) y J * (val ((U.gt e).t α) h y J).val := by
      rw [← E, pow_one, pow_one, Sg, ← _root_.mul_assoc, ← Units.val_mul, W']
      simp only [Units.val_mul]
      ring
    rw [L1, Finset.sum_map, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨χ, rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe χ) = χ := xe.symm_apply_apply χ
    rw [e₀]
    exact key χ

end GlobalTheory.TwistedExpTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_transport_translation_twist : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₂ : DegData R I) (A A₂ : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (U₂ : UnifPre I D₂ A₂ G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ⟶ D.toPre.P.A) (xe : D₂.toPre.X ≃+ D.toPre.X) (w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b) GlobalTheory.MumCmp.twε)) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])) (e : ℕ) (h : (thickObj R I e G).left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0 → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG I e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG I e G).left)) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z (N (r ≫ (fstG I e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG I e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R I e G).hom ≫ thick R I e) z J) → ∀ (σ : H0 U.LG.L 1) (σ₂ : H0 U₂.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → U.ExpandsAt e 1 σ f → U₂.ExpandsAt e 1 σ₂ f₂ := by
  first | exact @GlobalTheory.TwistedExpTransport.expandsAt_twist | exact GlobalTheory.TwistedExpTransport.expandsAt_twist | (intros; apply GlobalTheory.TwistedExpTransport.expandsAt_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficients
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TrCoef

theorem exists_nestSec {X X' Y : Scheme.{0}} {L : LB X} {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (ε : J → ℤ) (ψ : K → (Y ⟶ X')) (δ : K → ℤ)
    (s : LB.Sec (LB.LinComb L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2))) :
    ∃ T : LB.Sec (LB.LinComb (LB.LinComb L F ε) ψ δ), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (I : (Z ⟶ X) → L.ι), Good L z I → sval T r z (fun χ j => I (χ ≫ F j)) = sval s r z I := by
  have le : ∀ q : K → J → L.ι, LB.wchart (LB.LinComb L F ε) ψ q ≤
      LB.wchart L (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => q p.1 p.2) := fun q y hy =>
    Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2
  have v : ∀ (q : K → J → L.ι) (y : Y) (hy : y ∈ LB.wchart (LB.LinComb L F ε) ψ q),
      gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2)) =
        gs (𝟙 Y) y _ (s.f fun p => q p.1 p.2) := fun q y hy => gs_res _ y (le q) hy _
  refine ⟨⟨fun q => (Y.presheaf.map (homOfLE (le q)).op).hom (s.f fun p => q p.1 p.2),
    fun q q' => fn_ext fun y hy => ?_⟩, fun Z r z I hI => ?_⟩
  · have htr : trF (L := LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' =
        trF (L := L) (K := K × J) (fun p => ψ p.1 ≫ F p.2) (fun p => δ p.1 * ε p.2) (𝟙 Y) y
          (fun p => q p.1 p.2) (fun p => q' p.1 p.2) := by
      refine (Finset.prod_congr rfl fun k _ => congrArg (· ^ δ k)
        (gm_linComb L F ε (𝟙 Y ≫ ψ k) y (q k) (q' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k))).trans ?_
      simp only [trF, Fintype.prod_prod_type, ← Finset.prod_zpow, ← zpow_mul, Category.assoc, mul_comm]
    refine ((gs_res (𝟙 Y) y _ hy _).trans (v q y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb (LB.LinComb L F ε) ψ δ (𝟙 Y) y q q' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (v q' y hy.2)))).symm)
    refine (sec_trans s (𝟙 Y) y (le q hy.1) (le q' hy.2)).trans ?_
    rw [← htr]
    rfl
  · have hI' : Good (LB.LinComb L F ε) z (fun χ j => I (χ ≫ F j)) := fun χ => hI.mem F χ
    have hm := hI'.mem ψ r
    rw [sval_of s r z I (fun p => I ((r ≫ ψ p.1) ≫ F p.2)) (fun p => by rw [Category.assoc])]
    exact gs_res r z (le _) hm _

end GlobalTheory.MumCmp.TrCoef

namespace GlobalTheory.MumCmp.TrCoef

theorem formEq_coef {R : Type} [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (g : GtPt D (𝟙_ (Over (Sp R)))) (χ₂ : D₂.X) (χ : D.X) (hc : D₂.c χ₂ ≫ β = D.c χ) :
    FormEq (Sum.elim (fun k => GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k)
        (Sum.elim (fun k => (toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k)
          (fun k => (toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k)))
      (Sum.elim (DegPre.famε 1) (Sum.elim DegPre.gtε ![-1, 1]))
      (fun p : Fin 4 × Fin 3 => D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2)
      (fun p => DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) := by
  intro U _ h
  have hu : ∀ x : D₂.P.A ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit D₂.P.A := fun x => toUnit_unique _ _
  have ht : ∀ x : D₂.P.A ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit D₂.P.A ≫ g.b)).left * (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ g.b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.famφB χ₂ k = ((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
      Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.famφB χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b p.2) ^
      (DegPre.famε 1 p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![𝟙 D₂.P.A, 𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂), toUnit D₂.P.A ≫ D₂.c χ₂, 1] :
        Fin 4 → (D₂.P.A ⟶ D₂.P.A)) k ≫ β) * (toUnit D₂.P.A ≫ g.b)).left *
        (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left) ^ DegPre.famε 1 k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (DegPre.famε 1 k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have hL1 : ∏ k, h (GlobalTheory.MumCmp.twφ D₂ D β g.b 0 ≫ D.famφB χ k) ^ DegPre.famε 1 k =
      h ((β * (toUnit D₂.P.A ≫ g.b)) * (toUnit D₂.P.A ≫ D.c χ)).left * (h (toUnit D₂.P.A ≫ D.c χ).left)⁻¹ *
        h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ 𝟙 D.P.A).left ^ (((1 : ℕ) : ℤ) - 1) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c χ))).left ^ (1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ D.c χ).left ^ (-1 : ℤ) *
      h ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      ← Category.assoc (β * (toUnit D₂.P.A ≫ g.b)),
      toUnit_unique ((β * (toUnit D₂.P.A ≫ g.b)) ≫ toUnit D.P.A) (toUnit D₂.P.A)]
    simp only [Nat.cast_one, sub_self, zpow_zero, _root_.one_mul, zpow_one, zpow_neg_one]
    rfl
  have hL2 : ∏ k, h ((toUnit D₂.P.A).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b χ k) ^ DegPre.gtε k =
      (h ((toUnit D₂.P.A ≫ D.c χ) * (toUnit D₂.P.A ≫ g.b)).left)⁻¹ * h (toUnit D₂.P.A ≫ D.c χ).left *
        h (toUnit D₂.P.A ≫ g.b).left * (h (1 : D₂.P.A ⟶ D.P.A).left)⁻¹ := by
    rw [Fin.prod_univ_four]
    show h (toUnit D₂.P.A ≫ ((toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ) * g.b)).left ^ (-1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ D.c χ).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ g.b).left ^ (1 : ℤ) *
      h (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R))) ≫ η[D.P.A]).left ^ (-1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc (toUnit D₂.P.A), ← Category.assoc (toUnit D₂.P.A),
      toUnit_unique (toUnit D₂.P.A ≫ toUnit (𝟙_ (Over (Sp R)))) (toUnit D₂.P.A)]
    simp only [zpow_one, zpow_neg_one]
    rfl
  have hL3 : ∏ k, h ((toUnit D₂.P.A).left ≫ (![g.b.left, η[D.P.A].left] : Fin 2 → _) k) ^ (![-1, 1] : Fin 2 → ℤ) k =
      (h (toUnit D₂.P.A ≫ g.b).left)⁻¹ * h (1 : D₂.P.A ⟶ D.P.A).left := by
    rw [Fin.prod_univ_two]
    show h (toUnit D₂.P.A ≫ g.b).left ^ (-1 : ℤ) * h (toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [zpow_one, zpow_neg_one]
    rfl
  have h0 : (𝟙 D₂.P.A * (toUnit D₂.P.A ≫ D₂.c χ₂)) ≫ β = β * (toUnit D₂.P.A ≫ D.c χ) := by
    rw [MonObj.mul_comp, Category.id_comp, Category.assoc, hc]
  have h2 : (toUnit D₂.P.A ≫ D₂.c χ₂) ≫ β = toUnit D₂.P.A ≫ D.c χ := by rw [Category.assoc, hc]
  have h3 : (1 : D₂.P.A ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hL1, hL2, hL3, hA, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Category.id_comp, h0, h2, h3, _root_.one_mul]
  rw [mul_right_comm β (toUnit D₂.P.A ≫ D.c χ)]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem exists_translated_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ D D₂ β hβ g xe hc w hw ν hν f
  have key : ∀ χ : D₂.X, ∃ f₂ : D₂.SecB 1 χ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z)
      (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι),
      Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' →
      Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval f₂ r z J' := by
    intro χ
    haveI := hβ
    let u := LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit D₂.P.A).left)
      (LB.pullGen D.P.L _ _ ν (toUnit D₂.P.A).left)
    have hu : u.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (g.isGen _) _)
      (DVR.pullGen_isGen _ _ _ _ hν _)
    let S := pullMulSec (f (xe χ)) (GlobalTheory.MumCmp.twφ D₂ D β g.b 0) u hu
    obtain ⟨S', hS'⟩ := exists_sec D.P.isLB (formEq_coef D D₂ β g χ (xe χ) (hc χ)) S
    obtain ⟨T, hT⟩ := exists_nestSec (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε (D₂.famφB χ) (DegPre.famε 1) S'
    have hA := LB.isLB_linComb D₂.P.isLB (D₂.famφB χ) (DegPre.famε 1)
    have hB := LB.isLB_linComb (LB.isLB_linComb D.P.isLB (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε)
      (D₂.famφB χ) (DegPre.famε 1)
    have hU := DVR.linCombIso_isGen w hw (D₂.famφB χ) (DegPre.famε 1)
    refine ⟨DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB,
      fun Z r z J J' hJ hJ' => ?_⟩
    have hJ'' : Good (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε) z
        (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := fun χ' => hJ.mem _ χ'
    have m₁ := hJ'.mem (D₂.famφB χ) r
    have m₂ := hJ''.mem (D₂.famφB χ) r
    have e1 : Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J *
        (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
        Geo.Tor.sval T r z (fun χ' j => J (χ' ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) := by
      rw [hT Z r z J hJ, hS' Z r z J hJ, sval_pullMulSec _ _ _ hu r z hJ, val_mul hJ, val_pull hJ, val_pull hJ]
    rw [e1]
    have e2 := DVR.ps_gs_secOfIso (LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB
      (fun k => J' (r ≫ D₂.famφB χ k)) (fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)) r z ⟨m₁, m₂⟩
    have e3 := DVR.ps_gm_linCombIso w (D₂.famφB χ) (DegPre.famε 1)
      ((fun k j => J ((r ≫ D₂.famφB χ k) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b j)), (fun k => J' (r ≫ D₂.famφB χ k))) r z ⟨m₂, m₁⟩
    rw [show Geo.Tor.sval (DVR.secOfIso (u := LB.linCombIso w (D₂.famφB χ) (DegPre.famε 1)) T hU hA hB) r z J' = _ from e2,
      e3]
    exact (Units.mul_inv_cancel_left _ _).symm
  choose f₂ hf₂ using key
  exact ⟨f₂, hf₂⟩

end GlobalTheory.MumCmp.TrCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficientsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translated_expansion_coefficients : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₂ : DegPre R) (β : D₂.P.A ⟶ D.P.A), IsMonHom β → ∀ (g : GtPt D (𝟙_ (Over (Sp R)))) (xe : D₂.X ≃+ D.X), (∀ χ : D₂.X, D₂.c χ ≫ β = D.c (xe χ)) → ∀ w : LB.Iso D₂.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₂ D β g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen → ∀ f : ∀ α : D.X, D.SecB 1 α, ∃ f₂ : ∀ α : D₂.X, D₂.SecB 1 α, ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D₂.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂ D β g.b i)) (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.TrCoef.exists_translated_coef | exact GlobalTheory.MumCmp.TrCoef.exists_translated_coef | (intros; apply GlobalTheory.MumCmp.TrCoef.exists_translated_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwoTorsTr

theorem tr_tr {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G)
    (ha : a ^ 2 = 1) : ((toUnit G ≫ a) * 𝟙 G) ≫ ((toUnit G ≫ a) * 𝟙 G) = 𝟙 G := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (((toUnit G ≫ a) * 𝟙 G) ≫ toUnit G) (toUnit G),
    Category.comp_id, ← _root_.mul_assoc, ← MonObj.comp_mul, ← pow_two, ha, MonObj.comp_one, _root_.one_mul]

end GlobalTheory.TwoTorsTr

namespace GlobalTheory.TwoTorsTr

theorem secPull_invol {X : Scheme.{0}} (L L₂ : LB X) (hL : L.IsLB) (hL₂ : L₂.IsLB) (τ : X ⟶ X) (ττ : τ ≫ τ = 𝟙 X)
    (wL : LB.Iso L₂ (L.pull τ)) (hw : wL.IsGen) (σ : H0 L 1) : ∃ σ₂ : H0 L₂ 1,
    (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧
    ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  have hc : ∀ κ : Fin 1, (fun _ : Fin 1 => 𝟙 X) κ ≫ τ = τ ≫ (fun _ : Fin 1 => 𝟙 X) κ := fun _ => by
    simp only [Category.id_comp, Category.comp_id]
  obtain ⟨σ₂, hσ₂, -⟩ := SecPull.existsUnique_secPull _ _ _ _ L L₂ τ hL hL₂ wL hw (Fin 1)
    (fun _ => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (N : (Z ⟶ X) → L.ι) (N' : (Z ⟶ X) → L₂.ι),
      Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' →
      Geo.Tor.sval σ (r ≫ τ) z N = (Geo.Tor.gw wL r z (N (r ≫ τ)) (N' r)).val * Geo.Tor.sval σ₂ r z N' := by
    intro Z r z N N' hN hN'
    have := ExpTrans.sec_val wL (fun _ : Fin 1 => 𝟙 X) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) τ hc σ σ₂
      r z (hσ₂ Z r z) hN hN'
    rw [this, Fin.prod_univ_one, zpow_natCast, pow_one, ExpTrans.om, Category.comp_id]
  refine ⟨σ₂, key, fun h0 j => ?_⟩
  refine ThetaScalar.eq_zero_of_sval hL σ (fun y J hJ => ?_) j
  choose J' hJ' using fun ψ : X ⟶ X => exists_chart hL₂ (ψ y)
  have e := key X τ y J J' hJ hJ'
  rw [ττ, ThetaScalar.sval_eq_zero σ₂ h0 τ y hJ', MulZeroClass.mul_zero] at e
  exact e

end GlobalTheory.TwoTorsTr

namespace GlobalTheory

theorem twoTors_secPull : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  intro R _ G _ _ L L₂ hL hL₂ a ha wL hw σ
  exact TwoTorsTr.secPull_invol L L₂ hL hL₂ _
    (by rw [← Over.comp_left, TwoTorsTr.tr_tr G a ha, Over.id_left]) wL hw σ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullback_twoTorsion_translation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L L₂ : LB G.left), L.IsLB → L₂.IsLB → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ wL : LB.Iso L₂ (L.pull ((toUnit G ≫ a) * 𝟙 G).left), wL.IsGen → ∀ σ : H0 L 1, ∃ σ₂ : H0 L₂ 1, (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → L.ι) (N' : (Z ⟶ G.left) → L₂.ι), Geo.Tor.Good L z N → Geo.Tor.Good L₂ z N' → Geo.Tor.sval σ (r ≫ ((toUnit G ≫ a) * 𝟙 G).left) z N = (Geo.Tor.gw wL r z (N (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' r)).val * Geo.Tor.sval σ₂ r z N') ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) := by
  first | exact @GlobalTheory.twoTors_secPull | exact GlobalTheory.twoTors_secPull | (intros; apply GlobalTheory.twoTors_secPull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.MumCmp.translate_expansion_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  obtain ⟨wL, hwL⟩ := hL
  obtain ⟨ν, hν, hW⟩ := GlobalTheory.T.exists_levelComparison_generator_of_uniformisation R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw
  obtain ⟨σ₂, hσ₂, h0⟩ := GlobalTheory.T.exists_section_pullback_twoTorsion_translation R G U.LG.L U₂.LG.L U.LG.isLB U₂.LG.isLB a ha wL hwL σ
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_translated_expansion_coefficients R D.toPre D₂.toPre β.hom hβm g xe hc w hw ν hν f
  refine ⟨σ₂, f₂, ν, hν, fun e => ?_, h0, hf₂⟩
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom ∧
      h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    ⟨pullback.lift ((fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) (thickObj R (maximalIdeal R) e G).hom
      (by rw [Category.assoc, Over.w ((toUnit G ≫ a) * 𝟙 G)]; exact pullback.condition),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  exact GlobalTheory.T.expansion_transport_translation_twist R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre a g β.hom xe w wL ν e h hh₂
    (GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβm e (hβq e)
      (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh₁ hh₂)
    (hW e h hh₁ hh₂) (GlobalTheory.T.torusCoordinate_uniformisation_translate_eq R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw xe hxe hc e h hh₁ hh₂)
    σ σ₂ f f₂ hσ₂ hf₂ (hE e)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  first | exact @GlobalTheory.MumCmp.translate_expansion_twist | exact GlobalTheory.MumCmp.translate_expansion_twist | (intros; apply GlobalTheory.MumCmp.translate_expansion_twist <;> assumption)
end
