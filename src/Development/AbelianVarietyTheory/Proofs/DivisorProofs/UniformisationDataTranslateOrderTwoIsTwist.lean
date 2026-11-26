module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateIntegralThetaExpansionByTwoTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwPsi

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point

variable {R : Type} [CommRing R] [IsDomain R]

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem cancel {A : Type} [CommRing A] [IsDomain A] {S S₂ : A} {ψ rig G N W Wc W1 ψ₂ rig₂ : Aˣ} (hs : S₂ ≠ 0)
    (e : S * (ψ * rig).val * (G * N).val = (W * Wc⁻¹ * W1).val * (S₂ * (ψ₂ * rig₂).val))
    (e4 : S * N.val = W.val * S₂) : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂) := by
  refine Units.ext (mul_left_cancel₀ (mul_ne_zero W.ne_zero hs) ?_)
  simp only [Units.val_mul] at e ⊢
  linear_combination e - ((ψ : A) * G * rig) * e4

theorem core {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ))
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β g.b) twε))
    (f : ∀ α : D.X, D.SecB 1 α) (f₂ : ∀ α : D₂.X, D₂.SecB 1 α)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![g.b.left, η[D.P.A].left] ![-1, 1]))
    (h : LevelOneEq D f) (h₂ : LevelOneEq D₂ f₂)
    (hf : ∀ (χ : D₂.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
      (J' : (Z ⟶ D₂.P.A.left) → D₂.P.L.ι), Good D.P.L z J → Good D₂.P.L z J' →
      sval (f (xe χ)) (r ≫ twφ D₂ D β g.b 0) z J *
        (val (g.s (xe χ)) (r ≫ (toUnit D₂.P.A).left) z J * val ν (r ≫ (toUnit D₂.P.A).left) z J).val =
      (∏ κ, gv w (r ≫ D₂.famφB χ κ) z (fun i => J ((r ≫ D₂.famφB χ κ) ≫ twφ D₂ D β g.b i))
        (J' (r ≫ D₂.famφB χ κ)) ^ DegPre.famε 1 κ).val * sval (f₂ χ) r z J')
    [IsIntegral (DegPre.BF D₂ (FractionRing R)).left]
    (χ : D₂.X) (z : (DegPre.BF D₂ (FractionRing R)).left) (J : _ → D.P.L.ι) (J' : _ → D₂.P.L.ι)
    (hJ : Good D.P.L z J) (hJ' : Good D₂.P.L z J')
    (ne : sval (f₂ 0) (DegPre.prB D₂ (FractionRing R)).left z J' ≠ 0) :
    val (D.psi (xe χ)) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J *
        val (g.s (xe χ)) (toUnit (DegPre.BF D₂ (FractionRing R))).left z J *
        val D.rig (DegPre.BF D₂ (FractionRing R)).hom z J =
      (wv w (cP D₂ (DegPre.BF D₂ (FractionRing R)) χ).left z J J')⁻¹ *
        wv w (1 : DegPre.BF D₂ (FractionRing R) ⟶ D₂.P.A).left z J J' *
        (val (D₂.psi χ) ((fst (TF (R := R) (FractionRing R)) D₂.P.A).left ≫ jFK (R := R) (FractionRing R)) z J' *
          val D₂.rig (DegPre.BF D₂ (FractionRing R)).hom z J') := by
  let T := DegPre.BF D₂ (FractionRing R)
  let κ : T ⟶ TF (R := R) (FractionRing R) := fst _ _
  let Φ : D₂.P.A ⟶ D.P.A := padd D.P.A β (toUnit D₂.P.A ≫ g.b)
  have hΦ : ∀ u : T ⟶ D₂.P.A, u ≫ Φ = (u ≫ β) * (toUnit T ≫ g.b) := fun u => by
    show u ≫ (β * (toUnit D₂.P.A ≫ g.b)) = _
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  have hU : ∀ u : T ⟶ D₂.P.A, u.left ≫ (toUnit D₂.P.A).left = (toUnit T).left := fun u => by
    rw [← Over.comp_left, toUnit_unique (u ≫ toUnit D₂.P.A) (toUnit T)]
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ D₂.P.A, y * cP D₂ T χ = DegPre.prB D₂ (FractionRing R) :=
    ⟨_, inv_mul_cancel_right _ _⟩
  have hyΦ : (y ≫ Φ) * cP D T (xe χ) = DegPre.prB D₂ (FractionRing R) ≫ Φ := by
    rw [hΦ, hΦ, ← hy, MonObj.mul_comp, cP_comp β (hc χ), mul_right_comm]
  have e₁ := h (xe χ) 0 rfl T κ (y ≫ Φ) z J hJ
  have e₂ := h₂ χ 0 rfl T κ y z J' hJ'
  have e₃ := hf χ _ y.left z J J' hJ hJ'
  have e₄ := hf 0 _ (DegPre.prB D₂ (FractionRing R)).left z J J' hJ hJ'
  have p₃ := prod_famB D₂ y χ (fun q => wv w q z J J')
  have p₄ := prod_famB D₂ (DegPre.prB D₂ (FractionRing R)) 0 (fun q => wv w q z J J')
  rw [hy] at p₃ e₂
  rw [cPoint_zero, _root_.mul_one, inv_mul_cancel_right] at p₄
  rw [hyΦ] at e₁
  change _ = (∏ κ, wv w (y.left ≫ D₂.famφB χ κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₃
  change _ = (∏ κ, wv w ((DegPre.prB D₂ (FractionRing R)).left ≫ D₂.famφB 0 κ) z J J' ^ DegPre.famε 1 κ).val * _ at e₄
  rw [p₃, hU, show y.left ≫ twφ D₂ D β g.b 0 = (y ≫ Φ).left from rfl, e₁, e₂] at e₃
  rw [p₄, hU, map_zero xe, val_corr hJ g.s_zero, val_one, _root_.one_mul,
    show (DegPre.prB D₂ (FractionRing R)).left ≫ twφ D₂ D β g.b 0 = (DegPre.prB D₂ (FractionRing R) ≫ Φ).left from rfl] at e₄
  exact cancel ne e₃ e₄

theorem grp {U : Type} [CommGroup U] {ψ0 ψ₂0 rig rig₂ W1 ψ G Wc ψ₂ : U} (h0 : ψ0 = W1⁻¹ * ψ₂0)
    (c0 : ψ0 * rig = ψ₂0 * rig₂) (c : ψ * G * rig = Wc⁻¹ * W1 * (ψ₂ * rig₂)) : ψ * G = Wc⁻¹ * ψ₂ := by
  subst h0
  apply Additive.ofMul.injective
  have e0 := congrArg Additive.ofMul c0
  have e := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at e0 e ⊢
  linear_combination (norm := abel) e - e0

theorem formEq {D D₂ : DegPre R} (g : GtPt D (𝟙_ (Over (Sp R)))) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (xe : D₂.X ≃+ D.X) (hc : ∀ χ, D₂.c χ ≫ β = D.c (xe χ)) (χ : D₂.X) :
    FormEq (Sum.elim (fun _ : PUnit => ptK (D.c (xe χ)))
        (fun k => (toUnit (TK R)).left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) k))
      (Sum.elim (fun _ => -1) DegPre.gtε) (fun i => D₂.xK χ ≫ twφ D₂ D β g.b i) (fun i => -1 * twε i) := by
  let u := toUnit (TK R)
  have k : ∀ a : TK R ⟶ 𝟙_ (Over (Sp R)), a = u := fun a => toUnit_unique _ _
  have m0 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 0 = D₂.xK χ ≫ twφ D₂ D β g.b 0 := by
    show u.left ≫ ((toUnit _ ≫ D.c (xe χ)) * g.b).left = (u ≫ D₂.c χ).left ≫ (β * (toUnit _ ≫ g.b)).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [MonObj.comp_mul, ← Category.assoc]
    rw [k (u ≫ toUnit _), k ((u ≫ D₂.c χ) ≫ toUnit _), Category.assoc, hc]
  have m1 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 1 = ptK (D.c (xe χ)) := by
    show u.left ≫ (toUnit _ ≫ D.c (xe χ)).left = (u ≫ D.c (xe χ)).left
    rw [← Over.comp_left, ← Category.assoc, k (u ≫ toUnit _)]
  have m2 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 2 = D₂.xK χ ≫ twφ D₂ D β g.b 1 := by
    show u.left ≫ g.b.left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ g.b).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, k ((u ≫ D₂.c χ) ≫ toUnit _)]
  have m3 : u.left ≫ DegPre.gtφT D (𝟙_ (Over (Sp R))) g.b (xe χ) 3 = D₂.xK χ ≫ twφ D₂ D β g.b 2 := by
    show u.left ≫ (toUnit _ ≫ η[D.P.A]).left = (u ≫ D₂.c χ).left ≫ (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, ← Category.assoc, k (u ≫ toUnit _),
      k ((u ≫ D₂.c χ) ≫ toUnit _)]
  intro U _ h
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_three, Fintype.prod_unique, Sum.elim_inl,
    Sum.elim_inr]
  rw [m0, m1, m2, m3]
  simp only [DegPre.gtε, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_succ]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

end GlobalTheory.MumCmp.TwPsi

namespace GlobalTheory.MumCmp


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.PsiCompare GlobalTheory.MumCmp.Point GlobalTheory.MumCmp.TwPsi in
theorem psi_maps_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ _ D D₂ g β hβ xe hc w hw ⟨t₀, m₀, c₀⟩ f f₂ ν _ h h₂ hne hf χ
  have hL := D.toPre.P.isLB
  have hL' := D₂.toPre.P.isLB
  have := D₂.toPre.P.isAb.smooth
  have := D₂.toPre.P.isAb.geomConnected
  have : IsIntegral (DegPre.BF D₂.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D₂.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D₂.toPre.P.A.hom).flip
  let T := DegPre.BF D₂.toPre (FractionRing R)
  let π : T.left ⟶ (TK R).left :=
    (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)
  have hπ : π ≫ jK R = T.hom := by
    rw [Category.assoc]; exact Over.w (fst (TF (R := R) (FractionRing R)) D₂.toPre.P.A)
  have hT0 : π ≫ D₂.toPre.xK 0 = (1 : T ⟶ D₂.toPre.P.A).left := by
    rw [Uniq.xK_zero, ← Category.assoc, hπ]; rfl
  have hTχ : π ≫ D₂.toPre.xK χ = (cP D₂.toPre T χ).left := by
    let k : T ⟶ TK R := Over.homMk π hπ
    exact congrArg (fun q => q.left) (comp_cP D₂.toPre k χ)
  have hTU : π ≫ (toUnit (TK R)).left = (toUnit T).left := by
    rw [toUnit_left_eq, toUnit_left_eq]; exact hπ
  have key : ∀ (z : T.left) J J', Good D.toPre.P.L z J → Good D₂.toPre.P.L z J' →
      val (D.toPre.psi (xe χ)) π z J * val (g.s (xe χ)) (π ≫ (toUnit (TK R)).left) z J =
        (wv w (π ≫ D₂.toPre.xK χ) z J J')⁻¹ * val (D₂.toPre.psi χ) π z J' := by
    intro z J J' hJ hJ'
    have ne : sval (f₂ 0) (DegPre.prB D₂.toPre (FractionRing R)).left z J' ≠ 0 := fun e => hne (h₂.eq_zero z hJ' e)
    have cχ := core g β.hom xe hc w f f₂ ν h h₂ hf χ z J J' hJ hJ' ne
    have c0 := core g β.hom xe hc w f f₂ ν h h₂ hf 0 z J J' hJ hJ' ne
    rw [map_zero xe, val_corr hJ g.s_zero, val_one, _root_.mul_one, cPoint_zero, inv_mul_cancel, _root_.one_mul] at c0
    have h0 : val (D.toPre.psi 0) π z J = (wv w (π ≫ D₂.toPre.xK 0) z J J')⁻¹ * val (D₂.toPre.psi 0) π z J' := by
      have e := Uniq.gm_mapsAtExp m₀ π z (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
        (J' (π ≫ D₂.toPre.xK 0)) (Set.mem_iInter.2 fun k => hJ _) (hJ' _)
      rw [← val_of t₀ π z J (fun k => J ((π ≫ D₂.toPre.xK 0) ≫ twφ D₂.toPre D.toPre β.hom g.b k))
          (fun k => congrArg J (Category.assoc π _ _).symm), val_corr hJ c₀, val_mul hJ, val_pull hJ,
        val_corr hJ g.s_zero, val_one, _root_.mul_one] at e
      rw [e, zpow_neg_one]; rfl
    rw [hT0] at h0
    rw [hTχ, hTU]
    exact grp h0 c0 cχ
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_gen hL (formEq g β.hom xe hc χ)
    (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))
    (mulGen_isGen _ _ _ _ _ _ _ (D.toPre.psi_gen _) (pullGen_isGen _ _ _ _ (g.isGen _) _))
  have R₁ := reg_val (L' := D₂.toPre.P.L) ht₁ π
  have R₂ := reg_wv (L := D.toPre.P.L) (L' := D₂.toPre.P.L) hw (π ≫ D₂.toPre.xK χ)
  have R₃ := (reg_val' (L := D.toPre.P.L) (D₂.toPre.psi_gen χ) π).inv
  obtain ⟨a, ha⟩ := ((R₁.mul R₂).mul R₃).glue hL hL' (fun U _ h h' => by
    simp only [Category.assoc, Fintype.prod_unique, zpow_neg_one, inv_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_prod, ofMul_one]
    simp only [neg_mul, _root_.one_mul, neg_zsmul, Finset.sum_neg_distrib]
    abel)
  have ha1 : a = 1 := unit_ext fun x _ => by
    obtain ⟨J, hJ⟩ := good_exists hL x
    obtain ⟨J', hJ'⟩ := good_exists hL' x
    rw [← ha _ (𝟙 _) x J J' hJ hJ', map_one]
    show val t₁ (𝟙 _ ≫ π) x J * wv w (𝟙 _ ≫ π ≫ D₂.toPre.xK χ) x J J' * (val (D₂.toPre.psi χ) (𝟙 _ ≫ π) x J')⁻¹ = 1
    rw [Category.id_comp, Category.id_comp, hv₁ _ _ x J hJ, val_mul hJ, val_pull hJ, key x J J' hJ hJ']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  have H : ∀ (y : (TK R).left) J J', Good D.toPre.P.L y J → Good D₂.toPre.P.L y J' →
      val t₁ (𝟙 _) y J = wv w (D₂.toPre.xK χ) y J J' ^ (-1 : ℤ) * val (D₂.toPre.psi χ) (𝟙 _) y J' := by
    intro y J J' hJ hJ'
    have e := ha _ (DegPre.zF D₂.toPre (FractionRing R)).left y J J' hJ hJ'
    rw [ha1, map_one] at e
    have hz : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π = 𝟙 _ := PsiCompare.zF_fst D₂.toPre
    change val t₁ ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J *
      wv w ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ) y J J' *
      (val (D₂.toPre.psi χ) ((DegPre.zF D₂.toPre (FractionRing R)).left ≫ π) y J')⁻¹ = 1 at e
    have hz' : (DegPre.zF D₂.toPre (FractionRing R)).left ≫ π ≫ D₂.toPre.xK χ = D₂.toPre.xK χ := by
      rw [← Category.assoc (DegPre.zF D₂.toPre (FractionRing R)).left π, hz, Category.id_comp]
    rw [hz', hz] at e
    rw [zpow_neg_one, ← mul_inv_eq_one, mul_inv, inv_inv, ← _root_.mul_assoc]
    exact e
  exact ⟨t₁, mapsAtExp_of_val hL hL' hw (D₂.toPre.psi_gen χ) ht₁ H, corr_of_val hL fun y J hJ => hv₁ _ _ y J hJ⟩

end GlobalTheory.MumCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiTwistedEqPsiMulCharacterOfPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₂ : DegData R (maximalIdeal R)) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))) (β : D₂.toPre.P.A ≅ D.toPre.P.A), IsMonHom β.hom → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen → GlobalTheory.PsiCompare.LevelOneEq D.toPre f → GlobalTheory.PsiCompare.LevelOneEq D₂.toPre f₂ → (¬ ∀ mu j, (f₂ mu).f j = 0) → (∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J') → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.psi_maps_twist | exact GlobalTheory.MumCmp.psi_maps_twist | (intros; apply GlobalTheory.MumCmp.psi_maps_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

theorem GlobalTheory.MumCmp.psi_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0
  have hR : AdmBase R (maximalIdeal R) := hB.1
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hS : SecBaseChangeSt := GlobalTheory.allSixLaws.1.secBaseChange
  obtain ⟨σ, f, hσ0, hE⟩ : ∃ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α),
      (¬ ∀ j, σ.f j = 0) ∧ ∀ e : ℕ, U.ExpandsAt e 1 σ f := by
    obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R _ D A G U.toUnifPre 1 le_rfl
    let i₀ : Fin (1 ^ A.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
    have hs : ¬ ∀ j, (b i₀).f j = 0 := fun h0 => by
      obtain ⟨c, -, hc⟩ := hb SecOps.secZero
      have e₁ := hc 0 (fun j => by simp [scal]; rfl)
      have e₂ := hc 1 (fun j => by
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        obtain rfl : i = i₀ := Fin.ext (by have := i.2; simp only [one_pow] at this; show i.1 = 0; omega)
        rw [h0 j, MulZeroClass.mul_zero])
      exact one_ne_zero (congrFun (e₂.trans e₁.symm) i₀)
    obtain ⟨E, ⟨r, hr, σ, f, hσ, -, hE⟩, -⟩ := (U.expand 1 le_rfl).1 (b i₀)
    refine ⟨σ, f, fun hz0 => hs ?_, hE⟩
    refine GlobalTheory.ThetaScalar.eq_zero_of_sval U.LG.isLB _ fun y J hJ => ?_
    have e₁ := GlobalTheory.PullIntegral.sval_of_secScal hσ (𝟙 _) y hJ
    rw [GlobalTheory.ThetaScalar.sval_eq_zero σ hz0 _ y hJ] at e₁
    have e₃ : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK R) ≫ jK R) r) =
        cst (pullback.snd G.hom (jK R) ≫ jK R) y r :=
      (gs_pull (𝟙 _) (pullback.snd G.hom (jK R) ≫ jK R) y ⊤ trivial _).trans (by rw [Category.id_comp]; rfl)
    rw [e₃] at e₁
    exact (GlobalTheory.IntegralExpansionLocal.isUnit_cst_of_ne_zero _ y hr).mul_right_eq_zero.1 e₁.symm
  obtain ⟨σ₂, f₂, ν, hν, hE₂, h0σ, hrel⟩ :=
    GlobalTheory.T.translate_integral_thetaExpansion_by_twoTorsion R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  have hne : ¬ ∀ mu j, (f₂ mu).f j = 0 := fun h0' => hσ0 (h0σ (by
    have H := (GlobalTheory.comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D₂ A₂ G U₂.toUnifPre 1 1 ![1] ![σ₂] ![f₂]
      (fun i => by fin_cases i; exact hE₂)).2 hsa.geomConnected (fun α j => by
        simpa [scal] using h0' α j)
    exact fun j => by simpa [scal] using H j))
  exact GlobalTheory.T.psi_twisted_eq_psi_mul_character_of_point R hB D D₂ g β hβm xe hc w hw h0 f f₂ ν hν
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U.toUnifPre (U.expand 1 le_rfl) σ f hE)
    (GlobalTheory.PsiCompare.levelOneEq_of_expandsAt hG hR U₂.toUnifPre (U₂.expand 1 le_rfl) σ₂ f₂ hE₂) hne hrel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_periods_translatedBundle_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.psi_twist | exact GlobalTheory.MumCmp.psi_twist | (intros; apply GlobalTheory.MumCmp.psi_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem formEq_twist_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  intro R _ _ D₂ D T Y₀ q y p₂ β _ hp b χ₂ χ U _ h
  have hu : ∀ x : T ⟶ D₂.P.A, x ≫ toUnit D₂.P.A = toUnit T := fun x => toUnit_unique _ _
  have ht : ∀ x : T ⟶ D₂.P.A, ∏ i, h (x.left ≫ GlobalTheory.MumCmp.twφ D₂ D β b i) ^ GlobalTheory.MumCmp.twε i =
      h ((x ≫ β) * (toUnit T ≫ b)).left * (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    intro x
    rw [Fin.prod_univ_three]
    show h (x ≫ (β * (toUnit D₂.P.A ≫ b))).left ^ (1 : ℤ) * h (x ≫ toUnit D₂.P.A ≫ b).left ^ (-1 : ℤ) *
      h (x ≫ toUnit D₂.P.A ≫ η[D.P.A]).left ^ (1 : ℤ) = _
    rw [MonObj.comp_mul, ← Category.assoc x, ← Category.assoc x, hu, zpow_one, zpow_one, zpow_neg_one]
    rfl
  have hx : ∀ k, D₂.Oφ p₂ χ₂ k = ((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k).left := by
    intro k; fin_cases k <;> rfl
  have hA : ∏ p : Fin 4 × Fin 3, h (D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) ^ (Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) =
      ∏ k : Fin 4, (h (((![p₂ * (toUnit T ≫ D₂.c χ₂), toUnit T ≫ D₂.c χ₂, p₂, 1] : Fin 4 → (T ⟶ D₂.P.A)) k ≫ β) * (toUnit T ≫ b)).left *
        (h (toUnit T ≫ b).left)⁻¹ * h (1 : T ⟶ D.P.A).left) ^ Oinvε k := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← ht, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_comm (Oinvε k) (GlobalTheory.MumCmp.twε i), zpow_mul, hx]
  have h0 : (p₂ * (toUnit T ≫ D₂.c χ₂)) ≫ β = (q ≫ y) * (toUnit T ≫ D₂.c χ₂ ≫ β) := by
    rw [MonObj.mul_comp, hp, Category.assoc]
  have h3 : (1 : T ⟶ D₂.P.A) ≫ β = 1 := MonObj.one_comp β
  have hC : ∏ k, h (D.Oφ (q ≫ y) χ k) ^ (-Oinvε k) = h ((q ≫ y) * (toUnit T ≫ D.c χ)).left *
      (h (toUnit T ≫ D.c χ).left)⁻¹ * (h (q ≫ y).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
    rw [Fin.prod_univ_four]
    show h ((q ≫ y) * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
      h (q ≫ y).left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ) = _
    simp only [zpow_neg, zpow_one, inv_inv]
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [hA, prod_cub, hC, GlobalTheory.CoordCompare.prod_diff, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    h0, h3, hp, _root_.one_mul, Category.assoc]
  simp only [Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zpow_neg, zpow_one, inv_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSumTwistCubeIdentityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSum_twist_cube_identity : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := by
  first | exact @GlobalTheory.MumCmp.formEq_twist_cube | exact GlobalTheory.MumCmp.formEq_twist_cube | (intros; apply GlobalTheory.MumCmp.formEq_twist_cube <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespond
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslC

theorem exists_flat_transport : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {J K : Type} [Fintype J] [Fintype K], L.IsLB → L'.IsLB → ∀ (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)), w.IsGen → ∀ (φ' : K → (Y ⟶ X')) (δ : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' δ)), a.IsGen → ∃ t : LB.Gen (LB.LinComb L (fun p : K × J => φ' p.1 ≫ pr p.2) (fun p => δ p.1 * ε p.2)), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Z ⟶ X) → L.ι) (I' : (Z ⟶ X') → L'.ι), Good L z I → Good L' z I' → val t r z I = (∏ k, gv w (r ≫ φ' k) z (fun j => I ((r ≫ φ' k) ≫ pr j)) (I' (r ≫ φ' k)) ^ δ k) * val a r z I' := GlobalTheory.T.exists_generator_transport_linCombIso

theorem formEq_twist : ∀ {R : Type} [CommRing R] [IsDomain R] (D₂ D : DegPre R) {T Y₀ : Over (Spec (CommRingCat.of R))} (q : T ⟶ Y₀) (y : Y₀ ⟶ D.P.A) (p₂ : T ⟶ D₂.P.A) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β], p₂ ≫ β = q ≫ y → ∀ (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (χ₂ : D₂.X) (χ : D.X), FormEq (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => D₂.Oφ p₂ χ₂ p.1 ≫ GlobalTheory.MumCmp.twφ D₂ D β b p.2) (fun k : thK => (lift (q ≫ y) (lift (toUnit T ≫ D₂.c χ₂ ≫ β) (toUnit T ≫ b))).left ≫ thφ D.P.A (x3 D.P.A) k)) (D.Oφ (q ≫ y) χ)) (Sum.elim (Sum.elim (fun p : Fin 4 × Fin 3 => Oinvε p.1 * GlobalTheory.MumCmp.twε p.2) thε) (fun k => - Oinvε k)) (fun k => q.left ≫ GlobalTheory.CoordCompare.diffφ y (D₂.c χ₂ ≫ β) (D.c χ) k) ![1, -1, 1, -1] := GlobalTheory.T.formalSum_twist_cube_identity

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D₂ : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def θpt (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) :
    (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ G3 D.P.A :=
  lift g.pG (lift (toUnit _ ≫ C) (toUnit _ ≫ b))

theorem θpt_congr (g : GtCoord I D e G) (C b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) {Z : Scheme.{0}}
    (r r' : Z ⟶ (thickObj R I e G).left) (h : r ≫ g.pG.left = r' ≫ g.pG.left) :
    r ≫ (θpt g C b).left = r' ≫ (θpt g C b).left := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hw : r ≫ T.hom = r' ≫ T.hom := by rw [← Over.w g.pG, reassoc_of% h]
  let a : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r hw
  let a' : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r' rfl
  have ha : a ≫ g.pG = a' ≫ g.pG := Over.OverMorphism.ext h
  have hu : a ≫ toUnit T = a' ≫ toUnit T := toUnit_unique _ _
  have : a ≫ θpt g C b = a' ≫ θpt g C b := by
    simp only [θpt, comp_lift, ha, ← Category.assoc]
    rw [toUnit_unique (a ≫ toUnit _) (a' ≫ toUnit _)]
  exact congrArg (fun q => q.left) this

theorem exists_ratio_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ) k)
      ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
        Good D.P.L z J → Good D₂.P.L z J' →
        val u r z J = (∏ k, gv w (r ≫ D₂.Oφ g₂.pG χ₂ k) z (fun i => J ((r ≫ D₂.Oφ g₂.pG χ₂ k) ≫ twφ D₂ D β b i))
          (J' (r ≫ D₂.Oφ g₂.pG χ₂ k)) ^ Oinvε k) * val (g₂.t χ₂) r z J' *
          val D.cub.t (r ≫ (θpt g (D₂.c χ₂ ≫ β) b).left) z J * (val (g.t χ) r z J)⁻¹ := by
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_flat_transport D.P.isLB D₂.P.isLB _ _ w hw _ _ (g₂.t χ₂) (g₂.t_gen χ₂)
  have hF := formEq_twist D₂ D ((Over.map (thick R I e)).map g.q) (D.prBe I e) g₂.pG β hp b χ₂ χ
  obtain ⟨u, hu, hv⟩ := exists_gen D.P.isLB hF
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t₁
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (θpt g (D₂.c χ₂ ≫ β) b).left))
      (LB.invGen D.P.L _ _ (g.t χ)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht₁
      (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)) (DVR.invGen_isGen _ _ _ _ (g.t_gen χ)))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  exact (hv Z r z J hJ).trans ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ r).trans
    (congrArg₂ (· * ·) (hv₁ Z r z J J' hJ hJ') (val_pull hJ _ _ r))) (val_inv _ r)))

theorem rearr {U : Type} [CommGroup U] (W a θ c : U) : W * a * θ * c⁻¹ = W * θ * (a * c⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_desc_gen (g : GtCoord I D e G) (g₂ : GtCoord I D₂ e G) (β : D₂.P.A ⟶ D.P.A) [IsMonHom β]
    [Mono β.left] (hp : g₂.pG ≫ β = g.pG) (b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (w : LB.Iso D₂.P.L (LB.LinComb D.P.L (twφ D₂ D β b) twε)) (hw : w.IsGen) (χ₂ : D₂.X) (χ : D.X)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D₂.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g₂.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D₂.P.A →
      val (g.t χ) r z J = val (g₂.t χ₂) r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (CoordCompare.diffφ (D.prBe I e) (D₂.c χ₂ ≫ β) (D.c χ)) ![1, -1, 1, -1]),
      v.IsGen := by
  obtain ⟨u, hu, hu'⟩ := exists_ratio_gen g g₂ β hp b w hw χ₂ χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, -⟩ := CoordCompare.exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.P.L D₂.P.isLB z
    obtain ⟨h₁, h₂⟩ := CoordCompare.ratio_invariant g g₂ β hp χ χ₂ hker r r' z J J' hJ hJ' h
    have h₀ : r ≫ g.pG.left = r' ≫ g.pG.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.prBe I e).left) h).trans (Category.assoc _ _ _))
    rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ', θpt_congr g _ b r r' h₀, rearr, rearr, h₂]
    congr 2
    exact Finset.prod_congr rfl fun k _ => by rw [CoordCompare.Oφ_congr χ₂ g₂.pG r r' h₁ k])
  exact ⟨v, hv⟩

end Level

theorem c_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ) := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlift A₂ D₂ U₂ hL β hβ hp xe hker w hw χ
  obtain ⟨⟨_, -, -, _⟩, -⟩ := hR
  have : Mono β.hom.left := inferInstance
  have hp' : ∀ e, (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  have := D.toPre.P.isAb.proper
  have h := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) (IsAdicComplete.le_jacobson_bot _)
    D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ D₂.toPre.c χ ≫ β.hom) (toUnit _ ≫ D.toPre.c (xe χ)) fun n => by
      obtain ⟨v, hv⟩ := exists_desc_gen (U.gt n) (U₂.gt n) β.hom (hp' n) g.b w hw χ (xe χ)
        (fun Z r z J J' hJ hJ' h h' => hker n Z r z J J' hJ hJ' h h' χ)
      have h₁ := CoordCompare.thick_eq _ _ v hv
      have h₂ : (fstG (maximalIdeal R) n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
          pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) n) ≫ thick R (maximalIdeal R) n := pullback.condition
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
  simpa using congrArg (η[D.toPre.P.A] ≫ ·) h

end GlobalTheory.MumCmp.TranslC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationsTranslationPeriodMapsCorrespondStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisations_translation_period_maps_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ) := by
  first | exact @GlobalTheory.MumCmp.TranslC.c_correspond | exact GlobalTheory.MumCmp.TranslC.c_correspond | (intros; apply GlobalTheory.MumCmp.TranslC.c_correspond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

theorem abelianPart_iso_of_twoUnif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  intro R _ _ _ hBase D A G _ _ hG U g _ a _ _ A₂ D₂ U₂ _
  have hR : AdmBase R (maximalIdeal R) := hBase.1
  have hN : IsNoetherianRing R := hR.1
  have hC : IsAdicComplete (maximalIdeal R) R := hR.2.2.2
  have hJ : maximalIdeal R ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  obtain ⟨b₁, hb₁, h₁⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D₂ D A₂ A G G
    U₂.toUnifPre U.toUnifPre (𝟙 G) inferInstance
  obtain ⟨b₂, hb₂, h₂⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R (maximalIdeal R) hR D D₂ A A₂ G G
    U.toUnifPre U₂.toUnifPre (𝟙 G) inferInstance

  have q₁ : ∀ e, (U.gt e).q = (U₂.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₁ := by
    intro e
    have := h₁ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have q₂ : ∀ e, (U₂.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R (maximalIdeal R) e)).map b₂ := by
    intro e
    have := h₂ e
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at this
    exact this
  have epi : ∀ {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
      (V : UnifPre (maximalIdeal R) D' A' G) (e : ℕ), Epi (V.gt e).q := by
    intro D' A' V e
    have := (V.gt e).q_flat
    have := (V.gt e).q_surj
    have : Epi (V.gt e).q.left := Flat.epi_of_flat_of_surjective _
    exact Over.epi_of_epi_left _
  have k₁ : b₂ ≫ b₁ = 𝟙 _ := by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U.toUnifPre n
    rw [← cancel_epi (U.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₂, ← q₁]
  have k₂ : b₁ ≫ b₂ = 𝟙 _ := by
    have := D₂.toPre.P.isAb.smooth
    have := D₂.toPre.P.isAb.geomConnected
    have := D₂.toPre.P.isAb.proper
    refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq hJ _ _ _ fun n => ?_
    have := epi U₂.toUnifPre n
    rw [← cancel_epi (U₂.gt n).q, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      Category.comp_id, ← Category.assoc, ← q₁, ← q₂]
  refine ⟨⟨b₁, b₂, k₂, k₁⟩, hb₁, fun e => ?_⟩
  show (U₂.gt e).q.left ≫ (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left =
    (U.gt e).q.left ≫ (fstG (maximalIdeal R) e D.toPre.P.A).left
  have m : ((Over.pullback (thick R (maximalIdeal R) e)).map b₁).left ≫
      (fstG (maximalIdeal R) e D.toPre.P.A).left = (fstG (maximalIdeal R) e D₂.toPre.P.A).left ≫ b₁.left :=
    pullback.lift_fst _ _ _
  rw [← m, q₁ e, Over.comp_left, Category.assoc]

end GlobalTheory.MumCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIsoOfTwoUniformisationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_iso_of_two_uniformisations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom ∧ ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left := by
  first | exact @GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif | exact GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif | (intros; apply GlobalTheory.MumCmp.abelianPart_iso_of_twoUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem isTwist_of_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  intro R _ _ _ hB D A G _ _ hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨β, hβm, hβq⟩ := GlobalTheory.T.abelianPart_iso_of_two_uniformisations R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨xe, hxe⟩ := GlobalTheory.unifPre_characterGroup_iso R (maximalIdeal R) hB.1 D D₂ A A₂ G hG U.toUnifPre U₂.toUnifPre
  obtain ⟨w, hw, h0⟩ := GlobalTheory.T.exists_iso_uniformisation_translate_orderTwo R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq
  have hc := GlobalTheory.T.uniformisations_translation_period_maps_correspond R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe w hw
  exact ⟨β, xe, hβm, hc, w, hw,
    GlobalTheory.T.uniformisation_periods_translatedBundle_twist R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw h0⟩

end GlobalTheory.MumCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → GlobalTheory.MumCmp.IsTwist D₂.toPre D.toPre g := by
  first | exact @GlobalTheory.MumCmp.isTwist_of_translate | exact GlobalTheory.MumCmp.isTwist_of_translate | (intros; apply GlobalTheory.MumCmp.isTwist_of_translate <;> assumption)
end
