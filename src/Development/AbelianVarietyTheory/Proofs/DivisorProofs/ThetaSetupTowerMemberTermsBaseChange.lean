module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.TermsMove

theorem tors_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {g : GtPtF D F} {n : ℕ} (d : ℕ) (h : ∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) :
    ∃ o, GtPtF.IsNsmul (n * d) g o ∧ o.IsZero := by
  letI := @TorusExt.gtGroup
  obtain ⟨o, o₁, o₂⟩ := h
  rw [TorusExt.isNsmul_iff_eq] at o₁
  rw [TorusExt.isZero_iff_eq] at o₂
  refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
  rw [mul_nsmul, ← o₁, o₂, nsmul_zero]

theorem frExt_isGen {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {E : Type} (F : Type) [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} (he : e.IsGen) : (frExt F e).IsGen :=
  pullGen_isGen A.L _ _ e he (TorsionExt.fieldMap (R := R) E F).left


open GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.ArcPull in
set_option maxHeartbeats 800000 in
theorem exists_witnesses : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C lab x fr th w₀ s g' w h1 h2 h3 h4 h5 h6
    V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen x₂ fr₂ h1' h2' ρ hρ
  have hG := GlobalTheory.globalFns_holds
  letI : Algebra (FractionRing V) (FractionRing V') := f.toAlgebra
  haveI : IsScalarTower (FractionRing V) (FractionRing V) (FractionRing V') := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hF : Compat io (FractionRing V') := hf
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hinj
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := map_maximalIdeal_le io
  have hg₂ : jFK (R := V') (FractionRing V') ≫ spMap f = jFK (R := V) (FractionRing V') := (Spec.map_comp _ _).symm
  obtain ⟨κ, κ', hκ⟩ := exists_isFibreIso hD hF
  obtain ⟨w₀₂, hw₀₂, Ω, hΩ₁, hΩ₂, hE⟩ := exists_expand hG hmon hU hF hg₂ hcart.1 hwψ hgen h4 hκ
  obtain ⟨t', s', E', ht', hs'⟩ := (hE 1 le_rfl).1 _ _ (expandsF_pull (F := FractionRing V') 𝔪.U.toUnifPre hG h5)
  have hx : ∀ b, (x₂ (𝔗.lam b)).left ≫ ψ = (fieldMap (R := V) (FractionRing V) (FractionRing V') ≫ x b).left := fun b => by
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · show _ = (spMap f ≫ (x b).left) ≫ 𝔪.φ
      rw [Category.assoc, ← hφ, ← Category.assoc, h1', Category.assoc, 𝔗.lam_pt, Category.assoc, h1, ← Category.assoc,
        ← Category.assoc, ← spMap_comp, ← spMap_comp, hyK]
    · rw [Category.assoc, hcart.1.w, ← Category.assoc, Over.w, Over.w]
      exact hg₂
  have hfr : ∀ b, FrUp wψ (fr₂ (𝔗.lam b)) (frExt (FractionRing V') (fr b)) (ρ b : FractionRing V') := fun b z J J' hJ hJ' => by
    have e : vS (frExt (FractionRing V') (fr b)) z J = val (fr b) (spMap f) z J :=
      (val_frExt (fr b) (𝟙 _) hJ).trans (congrArg (fun q => val (fr b) q z J) (Category.id_comp _))
    rw [e]
    exact hρ b z J J' hJ hJ'
  have hv : ∀ b, ValAt t' (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b))
      (f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) * ((ρ b)⁻¹ ^ 1).val) := fun b =>
    valAt_pull hΩ₁ hΩ₂ ht' (hx b) (hfr b) (valAt_ext (h3 b))
  have t0 : (show AbSec 𝔪₂.A (FractionRing V') 1 from t') ≠ 0 := fun e => by
    have h₀ := hv x₀
    rw [show t' = (0 : AbSec 𝔪₂.A (FractionRing V') 1) from e] at h₀
    exact mul_ne_zero ((map_ne_zero f).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv))
      (Units.ne_zero _) (valAt_unique h₀ (valAt_zero _ _))
  obtain ⟨x', fr', Θ, -, k1, k2, k3, -⟩ := IntTerm.exists_points_frames_theta _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m _ δ 𝔪₂
  obtain rfl : x' = x₂ := funext fun a => Over.OverMorphism.ext (𝔪₂.cart.1.hom_ext ((k1 a).trans (h1' a).symm)
    ((Over.w _).trans (Over.w _).symm))
  have hΘ : ∀ a, ValAt Θ (x' a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩) := fun a z J' hJ' => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' 𝔗.X₂.ρ.P.isLB z
    have e := mul_left_cancel (((k2 a).2 z J J' hJ hJ').trans ((h2' a).2 z J J' hJ hJ').symm)
    have b := k3 a z J' hJ'
    rw [FrameMove.val_powFrame] at b ⊢
    rwa [← e]
  obtain ⟨K, hK⟩ := exists_eq_smul t0 Θ
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG 𝔪₂.U (FractionRing V') le_rfl w₀₂ hw₀₂
  choose g₁ w₁ a₁ a₂ a₃ a₄ using fun c => exists_ext (F := FractionRing V') hG 𝔪.U h4 (g' c) (h6 c).2.1
  choose g₂ w₂ b₁ b₂ b₃ b₄ using fun c => exists_point hG hI hF hκ hΩ₁ hΩ₂ (fun k hk => (hE k hk).2) (g₁ c) (a₁ c) (ρ (lab c))
  refine ⟨Θ, w₀₂, K • s', g₂, w₂, K, hΘ, hw₀₂, (he' _ _).2 ?_, fun c => ⟨?_, b₁ c, ?_⟩, fun mu c => ?_, fun b => ?_⟩
  · exact (congrArg e' hK).trans ((map_smul e' K _).trans (congrArg (K • ·) ((he' _ _).1 E')))
  · rw [𝔗.lev]
    exact tors_mul _ (b₂ c _ (a₂ c _ (h6 c).1))
  · exact b₄ c (x' (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c))) _ (frExt (FractionRing V') (fr (lab c)))
      (frExt_isGen _ (h2 (lab c)).1) (hx (lab c)) (hfr (lab c)) (a₄ c (x (lab c)) (fr (lab c)) (h2 (lab c)).1 (h6 c).2.2)
  · rw [coef_smul (b₁ c), _root_.mul_assoc, b₃ c _ _ hs', a₃, he₈]
    rfl
  · have h₀ := valAt_lin (hv b) (valAt_zero _ _) K
    rw [add_zero, add_zero, ← hK] at h₀
    rw [valAt_unique (hΘ _) h₀, pow_one, _root_.mul_assoc, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

end GlobalTheory.TermsMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_witnesses_baseChange_member : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  first | exact @GlobalTheory.TermsMove.exists_witnesses | exact GlobalTheory.TermsMove.exists_witnesses | (intros; apply GlobalTheory.TermsMove.exists_witnesses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section
namespace GlobalTheory.Poinc.Sep.BaseTerms

theorem torsFrame_dvd {S : Scheme.{0}} (P : PolAV S) {T : Over S} {m d : ℕ}
    {rig rig' : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ τ'} (H : IsTorsFrame P rig (m * d) x τ)
    (H' : IsTorsFrame P rig' m x τ') {y : T.left} {J} (hJ : Good P.L y J) :
    (val τ (𝟙 _) y J / val τ' (𝟙 _) y J) ^ ((m * d) ^ 2) =
      (val rig T.hom y J / val rig' T.hom y J) ^ ((m * d) ^ 2) := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P (m * d) T
  obtain ⟨β, hβ⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P m T
  obtain ⟨δ₀, hδ₀⟩ := GlobalTheory.EmbLocal.exists_mulPull hG P d T
  have a := GlobalTheory.ThetaCompare.torsFrame_pow hG P hα H hJ
  have b := GlobalTheory.ThetaCompare.torsFrame_pow hG P hβ H' hJ
  have rα := GlobalTheory.ThetaCompare.Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ (m * d)) rfl rfl
  have rβ := GlobalTheory.ThetaCompare.Reg.two (y := y) (J := J) β hβ (snd T P.A) (snd T P.A ^ m) rfl rfl
  have rδ := GlobalTheory.ThetaCompare.Reg.two (y := y) (J := J) δ₀ hδ₀ (snd T P.A) (snd T P.A ^ d) rfl rfl
  have c := (rα.mul hJ (((rβ.pow hJ (d ^ 2)).mul hJ (rδ.pull hJ (snd T P.A ^ m))).inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', lift_snd, ← pow_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      push_cast
      module) x 1
  simp only [SymLiftOdd.comp_pow', GlobalTheory.ThetaCompare.pt_snd, H'.1, one_pow] at c
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div] at a b c ⊢
  push_cast at a b c ⊢
  linear_combination (norm := module) a - (d ^ 2) • b + c


set_option maxHeartbeats 1000000 in
theorem tower_frames {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act)
    (w₀ : LB.Iso 𝔗.X₂.ρ.P.L (X₁.ρ.P.L.pull 𝔗.φ)) (hw₀ : w₀.IsGen) :
    ∃ (u₀ : 𝔗.X₂.S.R) (k : X₁.S.Gam → ℕ), IsUnit u₀ ∧ ∀ (b : X₁.S.Gam) (Y : Scheme.{0})
      (r : Y ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left) (y : Y) (J₁ : (Y ⟶ X₁.ρ.P.A.left) → X₁.ρ.P.L.ι)
      (J₂ : (Y ⟶ 𝔗.X₂.ρ.P.A.left) → 𝔗.X₂.ρ.P.L.ι), Good X₁.ρ.P.L y J₁ → Good 𝔗.X₂.ρ.P.L y J₂ →
      ((gw w₀ (r ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left) y (J₁ (r ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left ≫ 𝔗.φ))
          (J₂ (r ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left)) * val (𝔗.X₂.ρ.fr (𝔗.lam b)) r y J₂ : _) :
          Y.presheaf.stalk y) =
        gs r y ⊤ (fn (u₀ * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b)) *
          (val (X₁.ρ.fr b) (r ≫ (show (baseOver (Sp 𝔗.X₂.S.R)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔗.om))
            y J₁ : Y.presheaf.stalk y) := by
  have hG : GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔗.X₂.ρ.P.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔗.om) hw₀ X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔗.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Y : Scheme.{0}) (r : Y ⟶ (𝟙_ (Over _)).left) (z : Y) J J', Good X₁.ρ.P.L z J →
      Good 𝔗.X₂.ρ.P.L z J' → GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔗.om) z J =
        GlobalTheory.ConstFam.wVal w₀ z J J' (r ≫ eSec 𝔗.X₂.ρ.P.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Y r z J J' hJ hJ' => (Hr Y r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  choose τ' hτ' Hτ using fun b => GlobalTheory.ConstFam.exists_gen_through (φ' := fun _ : Fin 1 => (𝔗.X₂.ρ.pt (𝔗.lam b)).left)
    (h := spMap 𝔗.om) hw₀ X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB (fun _ => 𝔗.lam_pt b) (X₁.ρ.fr b) (X₁.ρ.fr_tors b).2.1
  have hT' : ∀ b, IsTorsFrame 𝔗.X₂.ρ.P rig' (X₁.S.r * X₁.S.N) (𝔗.X₂.ρ.pt (𝔗.lam b)) (τ' b) := fun b =>
    GlobalTheory.FrameMove.isTorsFrame_move 𝔗.cart hw₀ hr (𝔗.lam_pt b) (X₁.ρ.fr_tors b) (hτ' b) (fun z J J' hJ hJ' => by
      have := Hτ b _ (𝟙 _) z J J' hJ hJ'
      rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  have H₂ : ∀ b, IsTorsFrame 𝔗.X₂.ρ.P 𝔗.X₂.ρ.rig (X₁.S.r * X₁.S.N * 𝔗.d) (𝔗.X₂.ρ.pt (𝔗.lam b))
      (𝔗.X₂.ρ.fr (𝔗.lam b)) := fun b => 𝔗.lev ▸ 𝔗.X₂.ρ.fr_tors (𝔗.lam b)
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ : Γ((baseOver (Sp 𝔗.X₂.S.R)).left, ⊤)ˣ, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left) (z : Z) J, Good 𝔗.X₂.ρ.P.L z J →
      val 𝔗.X₂.ρ.rig r z J = gm r z ⊤ ρ * val rig' r z J := exists_ratio (K := PUnit) (φ := fun _ => eSec 𝔗.X₂.ρ.P.A) (ε := fun _ => 1) 𝔗.X₂.ρ.P.isLB rfl
    𝔗.X₂.ρ.rig rig' 𝔗.X₂.ρ.rig_gen hrig'
  choose v hv using fun b => exists_ratio 𝔗.X₂.ρ.P.isLB rfl (𝔗.X₂.ρ.fr (𝔗.lam b)) (τ' b) (𝔗.X₂.ρ.fr_tors _).2.1 (hτ' b)
  have hroot : ∀ b, v b ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) = ρ₀ ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := fun b => by
    apply unit_ext
    intro x _
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' 𝔗.X₂.ρ.P.isLB x
    have q := GlobalTheory.Poinc.Sep.BaseTerms.torsFrame_dvd 𝔗.X₂.ρ.P (H₂ b) (hT' b) hJ
    rw [hv b _ (𝟙 _) x J hJ, hρ₀ _ _ x J hJ, mul_div_cancel_right, mul_div_cancel_right] at q
    have q' : gm (𝟙 _) x ⊤ (v b) ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) =
        gm (𝟙 _) x ⊤ ρ₀ ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := q
    rw [map_pow, map_pow]
    exact q'
  have hinj : Function.Injective (algebraMap 𝔗.X₂.o₁ 𝔗.X₂.S.R) := fun a a' h =>
    (ArithBase.inj (o := 𝔗.X₂.o₁) (Ω := 𝔗.X₂.Ω₁)) (congrArg Subtype.val h)
  have hprim : IsPrimitiveRoot (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R)
      ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := by
    rw [← 𝔗.lev]
    exact 𝔗.X₂.S.prim.map_of_injective hinj
  have hP : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom ρ₀.val) := (ρ₀.map (Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom.toMonoidHom).isUnit
  have hV : ∀ b, ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom (v b).val) ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) = ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom ρ₀.val) ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := fun b => by
    have h' := congrArg (fun u => (Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom (Units.val u)) (hroot b)
    simpa only [Units.val_pow_eq_pow_val, map_pow] using h'
  have hμ : ∀ b, ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom (v b).val * ↑hP.unit⁻¹) ^ ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) = 1 := fun b => by
    rw [_root_.mul_pow, hV b, ← _root_.mul_pow, hP.mul_val_inv, one_pow]
  have hpos : 0 < X₁.S.r * X₁.S.N * 𝔗.d := by
    rw [← 𝔗.lev]
    exact Nat.mul_pos 𝔗.X₂.S.r_pos (by have := 𝔗.X₂.S.N_ge; omega)
  haveI : NeZero ((X₁.S.r * X₁.S.N * 𝔗.d) ^ 2) := ⟨pow_ne_zero 2 hpos.ne'⟩
  choose k hk using fun b => hprim.eq_pow_of_pow_eq_one (hμ b)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom ρ₀.val, k, (ρ₀.map (Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom.toMonoidHom).isUnit, fun b Y r y J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have h1 := Hτ b Y r y J₁ J₂ hJ₁ hJ₂
  rw [Fin.prod_univ_one, zpow_one] at h1
  have h2 := hv b Y r y J₂ hJ₂
  have h3 : fn ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom.hom ρ₀.val * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) =
      (v b).val := by
    rw [(hk b).2, mul_left_comm, hP.mul_val_inv, _root_.mul_one]
    show ((Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of 𝔗.X₂.S.R)).inv).hom (v b).val = (v b).val
    rw [Iso.hom_inv_id]
    rfl
  change _ = _ * (val (X₁.ρ.fr b) (r ≫ spMap 𝔗.om) y J₁).val
  rw [h3, h1, h2, gs_unit r y ⊤ trivial (v b)]
  simp only [GlobalTheory.ConstFam.wVal, Category.assoc, Units.val_mul]
  ring

theorem iso_square_const {S : Scheme.{0}} (A₂ : PolAV S) {Y X₁ X₂ : Scheme.{0}} {M : LB Y} {L₁ : LB X₁} {L₂ : LB X₂}
    (hM : M.IsLB) (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {ψ : A₂.A.left ⟶ Y} {a : Y ⟶ X₁} {b : A₂.A.left ⟶ X₂}
    {c : X₂ ⟶ X₁} (hc : b ≫ c = ψ ≫ a) (w : LB.Iso A₂.L (M.pull ψ)) (wl : LB.Iso M (L₁.pull a))
    (wl₂ : LB.Iso A₂.L (L₂.pull b)) (w₀ : LB.Iso L₂ (L₁.pull c)) (hw : w.IsGen) (hwl : wl.IsGen) (hwl₂ : wl₂.IsGen)
    (hw₀ : w₀.IsGen) :
    ∃ c₁ : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ A₂.A.left) (z : Z) (j₁ : L₁.ι) (j : M.ι) (j₂ : L₂.ι) (k : A₂.L.ι),
      a (ψ (r z)) ∈ L₁.U j₁ → ψ (r z) ∈ M.U j → b (r z) ∈ L₂.U j₂ → r z ∈ A₂.L.U k →
      gw wl (r ≫ ψ) z j₁ j * gw w r z j k = gm (r ≫ A₂.A.hom) z ⊤ c₁ * (gw w₀ (r ≫ b) z j₁ j₂ * gw wl₂ r z j₂ k) := by
  have pw := (isGen_iff w).1 hw
  have pwl := (isGen_iff wl).1 hwl
  have pwl₂ := (isGen_iff wl₂).1 hwl₂
  have pw₀ := (isGen_iff w₀).1 hw₀
  obtain ⟨wa, Ta⟩ := exists_comp hM wl w pwl pw hL₁ A₂.isLB
  obtain ⟨wb, Tb⟩ := exists_comp hL₂ w₀ wl₂ pw₀ pwl₂ hL₁ A₂.isLB
  have pa := Ta.pgen_comp hM pwl pw
  have pb := Tb.pgen_comp hL₂ pw₀ pwl₂
  have conv : ∀ (F₁ F₂ : A₂.A.left ⟶ X₁) (_ : F₁ = F₂) (u : LB.Iso A₂.L (L₁.pull F₁)), PGen u →
      ∃ u' : LB.Iso A₂.L (L₁.pull F₂), PGen u' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ A₂.A.left) (z : Z) j k,
        gw u' r z j k = gw u r z j k := by
    rintro F₁ _ rfl u hu
    exact ⟨u, hu, fun _ _ _ _ _ => rfl⟩
  obtain ⟨wb', pb', hb'⟩ := conv _ _ hc wb pb
  obtain ⟨u, hu⟩ := GlobalTheory.PreUnif.exists_ratio hL₁ A₂.isLB wa wb' pa pb'
  have hA := A₂.isAb
  obtain ⟨s, hs⟩ := (GlobalTheory.globalFns_holds S A₂.A hA).2 u.val
  obtain ⟨s', hs'⟩ := (GlobalTheory.globalFns_holds S A₂.A hA).2 (u⁻¹).val
  have hss : s * s' = 1 := (GlobalTheory.globalFns_holds S A₂.A hA).1 (by rw [map_mul, hs, hs', Units.mul_inv, map_one])
  let c₁ : Γ(S, ⊤)ˣ := ⟨s, s', hss, (mul_comm _ _).trans hss⟩
  refine ⟨c₁, fun Z r z j₁ j j₂ k h₁ hj h₂ hk => ?_⟩
  have hm₁ : c (b (r z)) ∈ L₁.U j₁ := by
    have e : (b ≫ c) (r z) = (ψ ≫ a) (r z) := by rw [hc]
    exact e ▸ h₁
  have e : gm (r ≫ A₂.A.hom) z ⊤ c₁ = gm r z ⊤ u := by
    rw [← gm_pull r A₂.A.hom z ⊤ trivial c₁]
    show gm r z ⊤ (pullU A₂.A.hom ⊤ c₁) = _
    congr 1
    exact Units.ext hs
  rw [← Ta Z r z j₁ j k h₁ hj hk, hu Z r z j₁ k h₁ hk, hb' Z r z j₁ k, Tb Z r z j₁ j₂ k hm₁ h₂ hk, e]

theorem pts_match {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    {A : PolAV (Sp (FractionRing V))} {A₂ : PolAV (Sp (FractionRing V'))} {B : Scheme.{0}} {G : Over B} [GrpObj G]
    {y₀ : Sp (FractionRing V) ⟶ B} {φ : A.A.left ⟶ G.left} (cart : IsGrpPullback A.A G y₀ φ)
    {f : FractionRing V →+* FractionRing V'} {ψ : A₂.A.left ⟶ A.A.left} (gp : IsGrpPullback A₂.A A.A (spMap f) ψ)
    (x₂ : TFK (R := V') (FractionRing V') ⟶ A₂.A) (x : TFK (R := V) (FractionRing V) ⟶ A.A)
    (h : x₂.left ≫ ψ ≫ φ = spMap f ≫ x.left ≫ φ) : x₂.left ≫ ψ = spMap f ≫ x.left := by
  refine cart.1.hom_ext ?_ ?_
  · simpa only [Category.assoc] using h
  · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w x₂, Category.assoc, Over.w x]
    show Spec.map _ ≫ spMap f = spMap f ≫ Spec.map _
    rw [show (CommRingCat.ofHom (algebraMap (FractionRing V') (FractionRing V'))) = 𝟙 _ from rfl,
      show (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = 𝟙 _ from rfl, Spec.map_id, Spec.map_id,
      Category.id_comp, Category.comp_id]

theorem frames_along_tower : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (m' : ℕ) (t' : Fin m' → V')
      (δ' : Fin m' → LinearMap.BilinForm ℤ X') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  intro g n F W Z i X₁ act 𝔗
  obtain ⟨w₀, hw₀⟩ := 𝔗.lb
  obtain ⟨u₀, k, hu₀, hT⟩ := tower_frames 𝔗 w₀ hw₀
  refine ⟨k, ?_⟩
  intro z₁ z₂ _ V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ io f _ ev₂ X' _ m' t' δ' 𝔪₂ ψ w hw _ hyK gp hφ x fr hx hfr x₂ fr₂ hx₂ hfr₂
  obtain ⟨c₁, hc₁⟩ := iso_square_const 𝔪₂.A 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB hφ w 𝔪.wl 𝔪₂.wl w₀ hw 𝔪.wl_gen
    𝔪₂.wl_gen hw₀
  let c₁' : (FractionRing V')ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V'))).hom.hom.toMonoidHom c₁
  have hsp : (spMap 𝔪₂.yK ≫ spMap 𝔗.om : Sp (FractionRing V') ⟶ Sp X₁.S.R) = spMap f ≫ spMap 𝔪.yK := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hyK
  refine ⟨c₁' * Units.map (𝔪₂.yK : 𝔗.X₂.S.R →* FractionRing V') hu₀.unit, fun b zz J J' hJ hJ' => ?_⟩
  set y := (x₂ (𝔗.lam b)).left with hy
  have e₁ : y ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left := hx₂ (𝔗.lam b)
  have e₂ : y ≫ ψ ≫ 𝔪.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt (𝔗.lam b)).left ≫ 𝔗.φ := by
    rw [← hφ, ← Category.assoc, e₁, Category.assoc]
  have e₃ : y ≫ ψ ≫ 𝔪.φ = spMap f ≫ (x b).left ≫ 𝔪.φ := by
    rw [e₂, 𝔗.lam_pt b, ← Category.assoc, hsp, Category.assoc, hx b]
  have hpts : y ≫ ψ = spMap f ≫ (x b).left := pts_match 𝔪.cart gp (x₂ (𝔗.lam b)) (x b) e₃
  have e₄ : spMap f ≫ (x b).left ≫ 𝔪.φ = y ≫ ψ ≫ 𝔪.φ := e₃.symm
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.ConstFam.exists_good' X₁.ρ.P.isLB zz
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.ConstFam.exists_good' 𝔗.X₂.ρ.P.isLB zz
  have ha := (hfr₂ (𝔗.lam b)).2 zz J₂ J' hJ₂ hJ'
  have hb := hT b (TFK (R := V') (FractionRing V')).left (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) zz J₁ J₂ hJ₁ hJ₂
  rw [← e₂, ← e₁] at hb
  have hd := hc₁ _ y zz (J₁ (y ≫ ψ ≫ 𝔪.φ)) (J (y ≫ ψ)) (J₂ (y ≫ 𝔪₂.φ)) (J' y) (hJ₁ _) (hJ _) (hJ₂ _) (hJ' _)
  have hc0 := (hfr b).2 (spMap f zz) (fun χ => J₁ (spMap f ≫ χ)) (fun χ => J (spMap f ≫ χ)) (fun χ => hJ₁ _)
    (fun χ => hJ _)
  have p₁ : (gw 𝔪.wl (spMap f ≫ (x b).left) zz (J₁ (spMap f ≫ (x b).left ≫ 𝔪.φ)) (J (spMap f ≫ (x b).left))).val =
      ((spMap f).stalkMap zz).hom (gw 𝔪.wl (x b).left (spMap f zz) (J₁ (spMap f ≫ (x b).left ≫ 𝔪.φ))
        (J (spMap f ≫ (x b).left))).val :=
    GlobalTheory.UT.EvalZero.gm_comp_map (spMap f) (x b).left zz ((X₁.ρ.P.L.pull 𝔪.φ).U (fun _ => J₁ (spMap f ≫ (x b).left ≫ 𝔪.φ)) ⊓
      𝔪.A.L.U (J (spMap f ≫ (x b).left))) ⟨mem_pull.2 (hJ₁ _), hJ _⟩ _
  have p₂ : (val (fr b) (spMap f) zz J).val =
      ((spMap f).stalkMap zz).hom (val (fr b) (𝟙 _) (spMap f zz) (fun χ => J (spMap f ≫ χ))).val :=
    GlobalTheory.UT.EvalZero.val_comp_map (fr b) (spMap f) (𝟙 _) (spMap f) (Category.comp_id _) zz hJ
  have p₃ : (val (X₁.ρ.fr b) ((show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) ≫ (show (baseOver (Sp 𝔗.X₂.S.R)).left ⟶ (baseOver (Sp X₁.S.R)).left from
      spMap 𝔗.om)) zz J₁).val = ((spMap f).stalkMap zz).hom
        (val (X₁.ρ.fr b) (spMap 𝔪.yK) (spMap f zz) (fun χ => J₁ (spMap f ≫ χ))).val :=
    GlobalTheory.UT.EvalZero.val_comp_map (X₁.ρ.fr b) (spMap f) (spMap 𝔪.yK) _ hsp.symm zz hJ₁
  have hc : (gw 𝔪.wl (y ≫ ψ) zz (J₁ (y ≫ ψ ≫ 𝔪.φ)) (J (y ≫ ψ))).val *
      @id ((TFK (R := V') (FractionRing V')).left.presheaf.stalk zz) (val (fr b) (spMap f) zz J).val =
      (val (X₁.ρ.fr b) ((show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) ≫ (show (baseOver (Sp 𝔗.X₂.S.R)).left ⟶ (baseOver (Sp X₁.S.R)).left from
        spMap 𝔗.om)) zz J₁).val := by
    rw [e₃, hpts, p₁, p₂, p₃]
    simp only [id]
    rw [← map_mul, ← Units.val_mul]
    exact congrArg (fun u => ((spMap f).stalkMap zz).hom u.val) hc0
  have ha' : gw 𝔪₂.wl y zz (J₂ (y ≫ 𝔪₂.φ)) (J' y) * val (fr₂ (𝔗.lam b)) (𝟙 _) zz J' =
      val (𝔗.X₂.ρ.fr (𝔗.lam b)) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) zz J₂ := ha
  have hG : gw w y zz (J (y ≫ ψ)) (J' y) * val (fr₂ (𝔗.lam b)) (𝟙 _) zz J' =
      (gw 𝔪.wl (y ≫ ψ) zz (J₁ (y ≫ ψ ≫ 𝔪.φ)) (J (y ≫ ψ)))⁻¹ * gm (y ≫ 𝔪₂.A.A.hom) zz ⊤ c₁ *
        (gw w₀ (y ≫ 𝔪₂.φ) zz (J₁ (y ≫ ψ ≫ 𝔪.φ)) (J₂ (y ≫ 𝔪₂.φ)) *
          val (𝔗.X₂.ρ.fr (𝔗.lam b)) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) zz J₂) := by
    rw [eq_inv_mul_of_mul_eq hd, ← ha']
    first | rfl | simp only [mul_assoc] | group
  have hU : gs (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) zz ⊤ (fn (u₀ * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b)) =
      GlobalTheory.Poinc.TorsRatio.cstK zz (𝔪₂.yK (u₀ * ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b)) :=
    (GlobalTheory.FrameMove.gs_spMap 𝔪₂.yK zz _).trans (GlobalTheory.Poinc.TorsRatio.cst_eq_cstK zz _)
  have hC : (gm (y ≫ 𝔪₂.A.A.hom) zz ⊤ c₁).val = GlobalTheory.Poinc.TorsRatio.cstK zz (c₁' : FractionRing V') := by
    rw [← gs_unit _ zz ⊤ trivial, show y ≫ 𝔪₂.A.A.hom = (TFK (R := V') (FractionRing V')).hom from Over.w (x₂ (𝔗.lam b))]
    have e : (c₁ : Γ(Sp (FractionRing V'), ⊤)) =
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V'))).inv.hom (c₁' : FractionRing V') := by
      simp [c₁']
    rw [e]
    exact (GlobalTheory.FrameMove.gs_spMap (RingHom.id _) zz _).trans (GlobalTheory.Poinc.TorsRatio.cst_eq_cstK zz _)
  have hval := congrArg Units.val hG
  have hb' := hb
  rw [Units.val_mul] at hb'
  simp only [Units.val_mul] at hval
  rw [hb', ← hc, hU, hC] at hval
  show (gw w y zz (J (y ≫ ψ)) (J' y)).val * (val (fr₂ (𝔗.lam b)) (𝟙 _) zz J').val = _
  rw [hval]
  have hB := Units.inv_mul (gw 𝔪.wl (y ≫ ψ) zz (J₁ (y ≫ ψ ≫ 𝔪.φ)) (J (y ≫ ψ)))
  simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
    IsUnit.unit_spec] at hB ⊢
  have key : ∀ a b c d e : (TFK (R := V') (FractionRing V')).left.presheaf.stalk zz,
      a * b * (c * (d * e)) = b * c * e * (a * d) := fun _ _ _ _ _ => by ring
  rw [key, hB, _root_.mul_one]
  ring

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesAlongThetaTowerRootOfUnityPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_along_theta_tower_root_of_unity_power : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act), ∃ k : X₁.S.Gam → ℕ,
    ∀ (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ)
      (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (X' : Type) [AddCommGroup X'] (m' : ℕ) (t' : Fin m' → V')
      (δ' : Fin m' → LinearMap.BilinForm ℤ X') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X' t' δ') (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left)
      (w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), w.IsGen → 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ →
    ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∃ c : (FractionRing V')ˣ, ∀ b, FrPull w f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b)
      ((c : FractionRing V') * 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ ^ k b) := by
  first | exact @GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | exact GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower | (intros; apply GlobalTheory.Poinc.Sep.BaseTerms.frames_along_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemberZeta

open GlobalTheory.Points

theorem valR_through_stalk {X : Scheme.{0}} {x : X} {C : Type} [CommRing C] (ψ : X.presheaf.stalk x →+* C)
    {U : X.Opens} (hU : x ∈ U) (a : Γ(X, U)) :
    valR (spMap ψ ≫ X.fromSpecStalk x) U a = ψ (X.presheaf.germ U x hU a) := by
  have h : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : X.fromSpecStalk x w ∈ Set.range (X.fromSpecStalk x) := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := X.fromSpecStalk x w) this U.isOpen hU
  have e : (X.fromSpecStalk x).appLE U ⊤ h = X.presheaf.germ U x hU ≫ (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU, Category.assoc, Category.assoc, ← Functor.map_comp]
    exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) ((Spec (X.presheaf.stalk x)).presheaf.map_id _)).trans (Category.comp_id _))
  refine (valR_appLE (spMap ψ) (X.fromSpecStalk x) h (le_preimage_top _) a).symm.trans ?_
  rw [e]
  exact valR_specMap (CommRingCat.ofHom ψ) _

theorem val_germ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {V : Type} [CommRing V] [IsDomain V]
    {z : M.Z} (ev : M.Z.presheaf.stalk z →+* V) (x : M.Z.presheaf.stalk z) :
    M.val (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) (M.stalkHom z x) = algebraMap V (FractionRing V) (ev x) := by
  obtain ⟨U, hz, f, rfl⟩ := M.Z.presheaf.germ_exist x
  have hr : Set.range (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    have : (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact Specializes.mem_open (x := (jK V ≫ spMap ev ≫ M.Z.fromSpecStalk z) w) this U.isOpen hz
  have e : jK V ≫ spMap ev = spMap ((algebraMap V (FractionRing V)).comp ev) := by
    rw [← Spec.map_comp]; rfl
  rw [RatModel.val_eq hr (RatModel.stalkHom_germ hz f).symm]
  show valR _ U f = _
  rw [← Category.assoc, e, valR_through_stalk _ hz]
  rfl

theorem algebraMap_ev_eq_yK : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) (z : X.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X.M.Z.presheaf.stalk z →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X z act V ev Y t δ) (zt : X.M.Z.presheaf.stalk z),
    X.M.stalkHom z zt = algebraMap X.o₁ X.Ω₁ X.S.ζ →
    algebraMap V (FractionRing V) (ev zt) = 𝔪.yK ⟨algebraMap X.o₁ X.Ω₁ X.S.ζ, X.S.R.algebraMap_mem _⟩ := by
  intro g n F W Z i X z act V _ _ _ ev Y _ m t δ 𝔪 zt h
  rw [𝔪.yK_eq]
  exact (val_germ ev zt).symm.trans (congrArg (X.M.val _) h)

end GlobalTheory.Poinc.Sep.MemberZeta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkEvaluationRootOfUnityValueMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_evaluation_root_of_unity_value_member : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) (z : X.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X.M.Z.presheaf.stalk z →+* V) (Y : Type) [AddCommGroup Y] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ Y) (𝔪 : UMem X z act V ev Y t δ) (zt : X.M.Z.presheaf.stalk z),
    X.M.stalkHom z zt = algebraMap X.o₁ X.Ω₁ X.S.ζ →
    algebraMap V (FractionRing V) (ev zt) = 𝔪.yK ⟨algebraMap X.o₁ X.Ω₁ X.S.ζ, X.S.R.algebraMap_mem _⟩ := by
  first | exact @GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK | exact GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK | (intros; apply GlobalTheory.Poinc.Sep.MemberZeta.algebraMap_ev_eq_yK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerMemberTermsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

noncomputable section

namespace GlobalTheory.Poinc.Sep.BaseTerms

theorem terms_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  intro g n F W Z i X₁ act 𝔗 z₁ z₂ hp x₀ hdiv
  obtain ⟨k, hk⟩ := GlobalTheory.T.frames_along_theta_tower_root_of_unity_power X₁ act 𝔗
  set M := (𝔗.X₂.S.r * 𝔗.X₂.S.N) ^ 2 with hM
  refine ⟨fun b => k x₀ + (M - 1) * k b, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab T hT V' _ _ _ io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart hw hφ hmon hU he₈ hgen zt hzt
  obtain ⟨x, fr, th, w₀, s, g', w, h1, h2, h3, h4, h5, h6, h7⟩ := hT
  obtain ⟨wψ, hwψ⟩ := hw
  obtain ⟨j₂, hj₂⟩ := 𝔗.X₂.div z₂
  obtain ⟨u, ⟨x₂, fr₂, -, -, -, -, -, h1', h2', -⟩, -, -⟩ := GlobalTheory.T.exists_member_terms_integral_unit_shift _ _ F W Z i 𝔗.X₂ z₂ 𝔗.act₂ j₂ hj₂ V' ev₂ X m
    (fun k => io (t k)) δ 𝔪₂ (𝔗.X₂.S.HH 𝔗.X₂.M z₂) Subtype.val Subtype.range_coe
  obtain ⟨c₀, hc₀⟩ := hk z₁ z₂ hp V ev X m t δ 𝔪 V' io f hf ev₂ X m (fun k => io (t k)) δ 𝔪₂ ψ wψ hwψ hExt hyK hcart hφ
    x fr h1 h2 x₂ fr₂ h1' h2'
  set ζ' : FractionRing V' := 𝔪₂.yK ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ with hζ'
  have hζM : ζ' ^ M = 1 := by
    rw [hζ', ← map_pow]
    have : (⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, 𝔗.X₂.S.R.algebraMap_mem _⟩ : 𝔗.X₂.S.R) ^ M = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hM, 𝔗.X₂.S.prim.pow_eq_one, map_one]
    rw [this, map_one]
  have hζ0 : ζ' ≠ 0 := by
    intro h0
    have hMpos : M ≠ 0 := by
      rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega))
    rw [h0, zero_pow hMpos] at hζM
    exact zero_ne_one hζM
  let ρ : X₁.S.Gam → (FractionRing V')ˣ := fun b => c₀ * (Units.mk0 ζ' hζ0) ^ k b
  have hρ : ∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b) := by
    intro b
    simpa [ρ] using hc₀ b
  obtain ⟨th₂, w₀₂, s₂, g'₂, w₂, K, h3', h4', h5', h6', hcoef, hval⟩ := GlobalTheory.T.exists_theta_witnesses_baseChange_member X₁ act 𝔗 z₁ z₂ hp x₀ hdiv V ev X m t δ 𝔪 C lab
    x fr th w₀ s g' w h1 h2 h3 h4 h5 h6 V' io f hf hinj hfin ev₂ 𝔪₂ ψ hD bc hExt hyK hcart wψ hwψ hφ hmon hU he₈ hgen
    x₂ fr₂ h1' h2' ρ hρ
  refine ⟨x₂, fr₂, th₂, w₀₂, s₂, g'₂, w₂, h1', h2', h3', h4', h5', h6', ?_⟩
  intro mu c
  have hz := GlobalTheory.T.stalk_evaluation_root_of_unity_value_member 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X m (fun k => io (t k)) δ 𝔪₂ zt hzt
  have hF0 : f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) ≠ 0 :=
    (map_ne_zero_iff f f.injective).2 (UMem.yK_th_ne_zero _ _ F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv)
  have hρc : (ρ (lab c) : FractionRing V') ≠ 0 := (ρ (lab c)).ne_zero
  have e1 := hcoef mu c
  have e2 := hval x₀
  have e3 := h7 mu c
  have eρ : (ρ x₀ : FractionRing V') = ρ (lab c) * ζ' ^ (k x₀ + (M - 1) * k (lab c)) := by
    simp only [ρ, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [_root_.mul_assoc, ← pow_add]
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
      rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := 𝔗.X₂.S.r_pos; omega) (by have := 𝔗.X₂.S.N_ge; omega)))
    have hsum : (M - 1) * k (lab c) + k (lab c) = M * k (lab c) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
    rw [show k (lab c) + (k x₀ + (M - 1) * k (lab c)) = k x₀ + ((M - 1) * k (lab c) + k (lab c)) by ring, hsum,
      pow_add, pow_mul, hζM, one_pow, _root_.mul_one]
  have e3' : f (coef s (g' c) (w c) (𝔪.e₈ mu)) =
      algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) := by
    rw [← e3, map_mul, hf]
  show algebraMap V' (FractionRing V') (ev₂ zt ^ (k x₀ + (M - 1) * k (lab c)) * io (T mu c)) *
    𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩ = coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu)
  rw [map_mul, map_pow, hz]
  apply mul_right_cancel₀ (mul_ne_zero hρc hF0)
  linear_combination (-(algebraMap V' (FractionRing V') (io (T mu c))) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) *
      𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam x₀), 𝔗.X₂.S.th_mem _⟩) * eρ +
    (algebraMap V' (FractionRing V') (io (T mu c)) * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) * e2 -
    f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e1 - K * f (𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) * e3'

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTowerMemberTermsBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetupTower_member_terms_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite → ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ) (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre) (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK → IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → (∃ w : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ), w.IsGen) → 𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U → (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) → 𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) → ∀ zt : 𝔗.X₂.M.Z.presheaf.stalk z₂, 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → 𝔪₂.Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c)) := by
  first | exact @GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange | exact GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange | (intros; apply GlobalTheory.Poinc.Sep.BaseTerms.terms_baseChange <;> assumption)
end
