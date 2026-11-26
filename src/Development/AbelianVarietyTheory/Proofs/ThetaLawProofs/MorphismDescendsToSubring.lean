module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem morphism_descends_to_subring :
    ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ Y₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (q : Y₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation q] (φ : X ⟶ Y₀), IsPullback π f f₀ (spMap R₀.subtype) → φ ≫ q = π ≫ f₀ → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Y₀, j ≫ ψ = φ ∧ ψ ≫ q = π₁ ≫ f₀ := by
  intro R _ R₀ X X₀ Y₀ f f₀ q π _ _ _ φ hP hφ
  let _ : Algebra R₀ R := R₀.subtype.toAlgebra
  have hP' : IsPullback π f f₀ (spMap (algebraMap R₀ R)) := hP

  let e := hP'.isoPullback
  obtain ⟨R', ψ', hfg, hψ'q, hψ'φ⟩ := Spread.exists_fg_comp_eq (pB := f₀) (pZ := q) (A := R)
    (e.inv ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, hP'.isoPullback_inv_fst])
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun R₁ h hS X₁ f₁ π₁ j hP₁ hjπ hjf => ?_⟩

  have hle : ∀ x ∈ R', x ∈ R₁ := by
    let T : Subalgebra R₀ R := { R₁.toSubsemiring with algebraMap_mem' := fun r => h r.2 }
    have hT : R' ≤ T := ht ▸ Algebra.adjoin_le hS
    exact fun x hx => hT hx
  let a : R' →+* R₁ := RingHom.codRestrict R'.val.toRingHom R₁ (fun x => hle x x.2)
  have ha : spMap a ≫ spMap (algebraMap R₀ R') = spMap (Subring.inclusion h) := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  have hb : spMap R₁.subtype ≫ spMap a = spMap R'.val.toRingHom := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  let L : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ R')) :=
    pullback.lift π₁ (f₁ ≫ spMap a) (by rw [Category.assoc, ha]; exact hP₁.w)
  refine ⟨L ≫ ψ', ?_, ?_⟩
  · have hjL : j ≫ L = e.hom ≫ Spread.bcMap f₀ R'.val := by
      apply pullback.hom_ext
      · simp only [L, e, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
        rw [pullback.lift_fst, hjπ]
      · simp only [L, e, Category.assoc, pullback.lift_snd, Spread.bcMap_snd,
          IsPullback.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, hjf, Category.assoc, hb]
    rw [← Category.assoc, hjL, Category.assoc, hψ'φ, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
  · rw [Category.assoc, hψ'q, ← Category.assoc, pullback.lift_fst]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyPBScale

theorem appLE_constFn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {X Y : Scheme.{0}} {φ : Y ⟶ X}
    (p : X ⟶ Sp R) (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (a : R) : (φ.appLE U V h).hom (constFn p U a) = constFn p' V (f a) :=
  KeyVia.appLE_cst f p p' hφ h a

theorem resG_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  KeyVia.res_appLE (φ := p) (U := ⊤) (fun _ _ => trivial) h _

theorem lie_baseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (hu : ∀ i : Fin m, IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left) (i : Fin m) :
    (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).2 (hu i)

theorem keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R) (M : Matrix (Fin P.g) (Fin P.g) R) (Q : Out.PolAV (Sp R')) (e : Q.g = P.g) (hgQ rigQ hrQ s hs u hu s' hs' u' hu'), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → (∀ i, LB.Sec.f s' i = constFn Q.A.hom _ (f a) * LB.Sec.f s i) → (∀ i : Fin Q.g, IsLieComb (fun j : Fin Q.g => f (M (i.cast e) (j.cast e))) u (u' i)) → KeyPB (⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ : KeyIn R') (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f → KeyPB (⟨Q, hgQ, rigQ, hrQ, s', hs', u', hu'⟩ : KeyIn R') (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f := by
  intro R R' _ _ f P hg rig hr th hth v hv th' hth' v' hv' a M Q e hgQ rigQ hrQ s hs u hu s' hs' u' hu' h₁ h₂ h₃ h₄
  rintro ⟨φ, he, w, hg', F, hp, hw, hrig, hsec, hF, hε, hlie⟩
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  refine ⟨φ, he, w, hg', F, hp, hw, hrig, fun j i h => ?_, hF, hε, ?_⟩
  · have k := hsec j i h
    dsimp only at k ⊢
    rw [h₁, h₃, map_mul, map_mul, k, appLE_constFn f P.A.hom Q.A.hom hp.1.w, resG_constFn]
    exact mul_left_comm (G := Γ(Q.A.left, (P.L.pull φ).U j ⊓ Q.L.U i)) _ _ _
  · subst hF'
    exact lie_baseChange f hp e M v v' u u' h₂ h₄ hlie

end GlobalTheory.KeyPBScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

theorem GlobalTheory.exists_entire_generator_div_frames : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), L.IsLB → ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ A.left)) (ep : K → ℤ) (t : LB.Gen (LB.LinComb L φ ep)), t.IsGen → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (pt : E → (Sp ℂ ⟶ Y)) (z : K → E → Fin g → ℂ), GlobalTheory.PowUnif.IsHolFamily pt → (∀ k, Differentiable ℂ (z k)) → (∀ e k, pt e ≫ φ k = (u.ex (z k e)).left) → ∃ T : E → ℂ, Differentiable ℂ T ∧ (∀ e, T e ≠ 0) ∧ ∀ e (j : K → L.ι), (∀ k, ⊤ ≤ (u.ex (z k e)).left ⁻¹ᵁ L.U (j k)) → valAt' (pt e) (LB.wchart L φ j) (t.s j).val = T e * ∏ k, u.fr (j k) (z k e) ^ ep k := by
  intro A _ L g u hL Y K _ φ ep t ht E _ _ pt z hpt hz hφ
  have hv : GlobalTheory.CubeValues.ValueRules := GlobalTheory.valAt'_rules
  let d : (Fin g → ℂ) → (Sp ℂ ⟶ A.left) := fun w => (u.ex w).left
  have hφ' : ∀ e k, pt e ≫ φ k = d (z k e) := hφ
  have hw : ∀ e (j : K → L.ι), ⊤ ≤ pt e ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k) := fun e j => by
    rw [GlobalTheory.PowUnif.le_wchart_iff]
    simp only [hφ']
  choose j₀ hj₀ using fun e k => GlobalTheory.PowUnif.exists_chart hL (d (z k e))
  let ω : (K → L.ι) → E → ℂ := fun j e => valAt' (pt e) (LB.wchart L φ j) (t.s j).val
  let P : (K → L.ι) → E → ℂ := fun j e => ∏ k, u.fr (j k) (z k e) ^ ep k
  have hω : ∀ j e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → ω j e ≠ 0 := fun j e h =>
    GlobalTheory.valAt'_unit_ne_zero (pt e) ((hw e j).2 h) (t.s j)
  have hP : ∀ j e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → P j e ≠ 0 := fun j e h =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ (h k))
  have hG : ∀ j j' e, (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j k)) → (∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ L.U (j' k)) →
      ω j e / P j e = ω j' e / P j' e := by
    intro j j' e h h'
    have hk : ∀ k, ⊤ ≤ d (z k e) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun k =>
      (GlobalTheory.top_le_preimage_inf _ _ _).2 ⟨h k, h' k⟩
    let c : ℂ := ∏ k, valAt' (d (z k e)) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ep k
    have hc : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (GlobalTheory.valAt'_unit_ne_zero _ (hk k) _)
    have e₁ : ω j e = c * ω j' e := by
      refine (GlobalTheory.CubeValues.val_gen (pt e) hv t ht j j' ((hw e j).2 h) ((hw e j').2 h')).trans ?_
      refine congrArg (· * ω j' e) ?_
      refine (GlobalTheory.CubeValues.val_linComb (pt e) hv L φ ep j j' ((hw e j).2 h) ((hw e j').2 h')).trans ?_
      simp only [hφ', c]
    have e₂ : P j e = c * P j' e := by
      simp only [P, c]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← mul_zpow]
      exact congrArg (· ^ ep k) (u.fr_compat _ _ _ (hk k))
    rw [e₁, e₂, mul_div_mul_left _ _ hc]
  refine ⟨fun e => ω (j₀ e) e / P (j₀ e) e, fun e₀ => ?_,
    fun e => div_ne_zero (hω _ _ (hj₀ e)) (hP _ _ (hj₀ e)), fun e j h => ?_⟩
  · have hS := hpt (LB.wchart L φ (j₀ e₀)) (t.s (j₀ e₀)).val
    have hS₀ := hS.1.mem_nhds ((hw e₀ _).2 (hj₀ e₀))
    have hd : DifferentiableAt ℂ (fun e => ω (j₀ e₀) e * (P (j₀ e₀) e)⁻¹) e₀ := by
      classical
      refine DifferentiableAt.mul (hS.2.differentiableAt hS₀) (DifferentiableAt.inv ?_ (hP _ _ (hj₀ e₀)))
      refine (HasFDerivAt.finsetProd fun k _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine DifferentiableAt.zpow (f := fun e => u.fr (j₀ e₀ k) (z k e)) ?_ (Or.inl (u.fr_ne _ _ (hj₀ e₀ k)))
      exact ((u.fr_hol _).differentiableAt ((u.hol _ 0).1.mem_nhds (hj₀ e₀ k))).comp e₀ (hz k e₀)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hS₀] with e he
    rw [hG _ _ e (hj₀ e) ((hw e _).1 he), div_eq_mul_inv]
  · beta_reduce
    rw [hG _ _ e (hj₀ e) h]
    exact (div_mul_cancel₀ _ (hP j e h)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEntireGeneratorDivFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), L.IsLB → ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ A.left)) (ep : K → ℤ) (t : LB.Gen (LB.LinComb L φ ep)), t.IsGen → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (pt : E → (Sp ℂ ⟶ Y)) (z : K → E → Fin g → ℂ), GlobalTheory.PowUnif.IsHolFamily pt → (∀ k, Differentiable ℂ (z k)) → (∀ e k, pt e ≫ φ k = (u.ex (z k e)).left) → ∃ T : E → ℂ, Differentiable ℂ T ∧ (∀ e, T e ≠ 0) ∧ ∀ e (j : K → L.ι), (∀ k, ⊤ ≤ (u.ex (z k e)).left ⁻¹ᵁ L.U (j k)) → valAt' (pt e) (LB.wchart L φ j) (t.s j).val = T e * ∏ k, u.fr (j k) (z k e) ^ ep k := by
  first | exact @GlobalTheory.exists_entire_generator_div_frames | exact GlobalTheory.exists_entire_generator_div_frames | (intros; apply GlobalTheory.exists_entire_generator_div_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMul
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta.Frame
open Matrix

private lemma add_lat_eq_add_mulVec_add {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ)
    (z : Fin g → ℂ) :
    z + lat τ k n = z + τ *ᵥ ReciprocityTheory.PTheta.ofIntVec n + ReciprocityTheory.PTheta.ofIntVec k := by
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  rw [hk, hn, lat]
  abel

private lemma autFactor_re_eq_aut_of_half_characteristics {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
    (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    ReciprocityTheory.PTheta.autFactor (fun i => (a i).re) (fun i => (b i).re) τ n k z =
      aut τ a b k n z := by
  rw [ReciprocityTheory.PTheta.autFactor, TorusAlg.ofRealVec_re ha, TorusAlg.ofRealVec_re hb]
  have hk : ReciprocityTheory.PTheta.ofIntVec k = fun i => (k i : ℂ) := rfl
  have hn : ReciprocityTheory.PTheta.ofIntVec n = fun i => (n i : ℂ) := rfl
  simp only [aut, ReciprocityTheory.PTheta.eC, hk, hn, ← Complex.exp_add]
  congr 1
  ring

theorem thetaChar_law {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    Differentiable ℂ (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 ∧
      ∀ k n z, thetaChar τ a b (z + lat τ k n) = aut τ a b k n z * thetaChar τ a b z := by
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨hne, hspan, -⟩ := TorusAlg.thetaChar_level hs hp ha hb
  have hmem : thetaChar τ a b ∈
      thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar_iff_autFactor] at hmem
  refine ⟨hmem.1, hne, fun k n z => ?_⟩
  have hper := hmem.2 n k z
  rw [pow_one] at hper
  rw [add_lat_eq_add_mulVec_add, hper, autFactor_re_eq_aut_of_half_characteristics ha hb]

theorem eq_zero_of_mul_eq_zero {g : ℕ} {θ D : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    {S : Set (Fin g → ℂ)} (hS : IsOpen S) (hD : ContinuousOn D S) (h : ∀ w ∈ S, θ w * D w = 0)
    {z : Fin g → ℂ} (hz : z ∈ S) : D z = 0 := by
  by_contra hDz
  have hθa : AnalyticOnNhd ℂ θ Set.univ :=
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ hθ.differentiableOn
  have hin : ∀ᶠ w in nhds z, w ∈ S := hS.mem_nhds hz
  have hnear : ∀ᶠ w in nhds z, w ∈ S ∧ D w ≠ 0 :=
    hin.and ((hD.continuousAt (hS.mem_nhds hz)).eventually_ne hDz)
  have hθz : θ =ᶠ[nhds z] 0 := by
    filter_upwards [hnear] with w hw
    rcases mul_eq_zero.1 (h w hw.1) with h' | h'
    · exact h'
    · exact absurd h' hw.2
  have hall := hθa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) hθz
  exact h0 (funext fun w => hall (Set.mem_univ w))

theorem frame_eq_aut_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  intro g x h u τ a b hab hw k n i z hz
  obtain ⟨hs, hp, hΛ, -, hth, -⟩ := hw
  have hlaw := thetaChar_law hs hp hab
  obtain ⟨ha, hb⟩ := hab
  have hlatΛ : lat τ k n ∈ u.Λ := (hΛ _).2 ⟨k, n, rfl⟩
  have hex : ∀ w, u.ex (w + lat τ k n) = u.ex w := fun w =>
    CubeValues.ex_add_period u w _ hlatΛ
  let S : Set (Fin g → ℂ) := {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ x.P.L.U i}
  have hSo : IsOpen S := (u.hol (x.P.L.U i) 0).1
  have hfr : ContinuousOn (u.fr i) S := (u.fr_hol i).continuousOn
  have hfr' : ContinuousOn (fun w => u.fr i (w + lat τ k n)) S := by
    refine hfr.comp (continuous_id.add continuous_const).continuousOn fun w hw => ?_
    show ⊤ ≤ (u.ex (w + lat τ k n)).left ⁻¹ᵁ x.P.L.U i
    rw [hex]
    exact hw
  have haut : Continuous fun w => aut τ a b k n w := by
    unfold aut
    simp only [dotProduct]
    fun_prop
  have hD : ContinuousOn (fun w => u.fr i w - aut τ a b k n w * u.fr i (w + lat τ k n)) S :=
    hfr.sub (haut.continuousOn.mul hfr')
  refine sub_eq_zero.1 (eq_zero_of_mul_eq_zero hlaw.1 hlaw.2.1 hSo hD (fun w hwS => ?_) hz)
  by_cases hθ : thetaChar τ a b w = 0
  · rw [hθ, zero_mul]
  · have hf := TorusAlg.frame_eq_autFactor_mul u x.th hs ha hb hΛ hth n k i w hwS hθ
    rw [autFactor_re_eq_aut_of_half_characteristics ha hb, ← add_lat_eq_add_mulVec_add] at hf
    rw [← hf, sub_self, mul_zero]

end GlobalTheory.SimilTheta.Frame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaUniformisationFrameEqAutomorphyMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), charHalf g a b → Wit x h u τ a b → ∀ (k n : Fin g → ℤ) (i : x.P.L.ι) (z : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i → u.fr i z = aut τ a b k n z * u.fr i (z + lat τ k n) := by
  first | exact @GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | exact GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul | (intros; apply GlobalTheory.SimilTheta.Frame.frame_eq_aut_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AutSimilitudeAndMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_column_sum_eq_add_two_mul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c : Fin 4) :
    ∃ s : ℤ, ∑ r, al r c = m + 2 * s := by
  have h1 : ∑ r, al r c * al r c = m := by
    have := congrFun (congrFun hal c) c
    simpa [Matrix.mul_apply] using this
  have h2 : Even (∑ r, al r c * (al r c - 1)) := Finset.even_sum _ fun r _ => Int.even_mul_pred_self _
  obtain ⟨s, hs⟩ := h2
  refine ⟨-s, ?_⟩
  have : ∑ r, al r c * (al r c - 1) = ∑ r, al r c * al r c - ∑ r, al r c := by
    simp [mul_sub, Finset.sum_sub_distrib]
  linarith

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_int_two_mul_dotProduct_of_half_integral {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (k : Fin g → ℤ) :
    ∃ t : ℤ, 2 * (a ⬝ᵥ fun i => (k i : ℂ)) = t := by
  refine ⟨∑ i, if a i = 0 then 0 else k i, ?_⟩
  simp only [dotProduct, Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h <;> simp [h]

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma sum_intCast_mul_column_eq_of_transpose_mul_eq_smul (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (c c' : Fin 4) :
    ∑ r, (al r c : ℂ) * al r c' = if c = c' then (m : ℂ) else 0 := by
  have := congrFun (congrFun hal c) c'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
  split_ifs at this ⊢ with h <;> [skip; skip] <;> exact_mod_cast (by simpa using this)

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma sum_column_smul_add_tors_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (m : ℕ) (hm : 1 ≤ m) (al : Matrix (Fin 4) (Fin 4) ℤ) (hal : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) :
    ∑ r, (al r c : ℂ) • (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r) = (m : ℂ) • y c + _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold _root_.GlobalTheory.SimilTheta.tors
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun r c' => ((al r c : ℂ) * al r c') • y c')]
  simp only [← Finset.sum_smul, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
  have h2 : ∀ x x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) = (↑m)⁻¹ * (↑(al x c) * ↑(al x x_1)) := fun _ _ => by ring
  have h3 : ∑ x, ∑ x_1, (↑(al x c) * ((↑m)⁻¹ * ↑(al x x_1)) : ℂ) • _root_.GlobalTheory.SimilTheta.lat τ (k x_1) (n x_1) = _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
    rw [Finset.sum_comm]
    simp only [h2, ← Finset.sum_smul, ← Finset.mul_sum, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal]
    simp [mul_ite, inv_mul_cancel₀ hm0]
  rw [h3]
  simp

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma intCast_zsmul_vector {g : ℕ} (α : ℤ) (v : Fin g → ℤ) :
    (fun i => (((α • v) i : ℤ) : ℂ)) = (α : ℂ) • fun i => (v i : ℂ) := by
  ext i; simp

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SimilTheta.aut_similitude_and_mul : ∀ (g m : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), _root_.GlobalTheory.KeyPow.charHalf g a b → τ.IsSymm → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → (∀ (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) (c : Fin 4) (k₀ n₀ : Fin g → ℤ), (∏ r, _root_.GlobalTheory.SimilTheta.aut τ a b (al r c • k₀) (al r c • n₀) (∑ c', al r c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n r)) * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ _root_.GlobalTheory.SimilTheta.lat τ k₀ n₀)) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ (y c) ^ m) ∧ ∀ (k₀ n₀ : Fin g → ℤ) (z : Fin g → ℂ), _root_.GlobalTheory.SimilTheta.aut τ a b ((m : ℤ) • k₀) ((m : ℤ) • n₀) ((m : ℤ) • z) = _root_.GlobalTheory.SimilTheta.aut τ a b k₀ n₀ z ^ (m ^ 2) := by
  intro g m τ a b al hab hτ hm hal
  refine ⟨fun k n y c k₀ n₀ => ?_, fun k₀ n₀ z => ?_⟩
  · obtain ⟨s, hs⟩ := exists_column_sum_eq_add_two_mul m al hal c
    obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    have hV := sum_column_smul_add_tors_eq τ m hm al hal k n y c
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    set K₀ : Fin g → ℂ := fun i => (k₀ i : ℂ)
    set N₀ : Fin g → ℂ := fun i => (n₀ i : ℂ)
    set Kc : Fin g → ℂ := fun i => (k c i : ℂ)
    set Nc : Fin g → ℂ := fun i => (n c i : ℂ)
    have hterm : ∀ x, (2 * ↑Real.pi * Complex.I *
            (((↑(al x c) * a ⬝ᵥ K₀) - ↑(al x c) * b ⬝ᵥ N₀) -
                ↑(al x c) * (↑(al x c) * N₀ ⬝ᵥ τ *ᵥ N₀) / 2 -
              ↑(al x c) * N₀ ⬝ᵥ (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x)) : ℂ) =
        2 * ↑Real.pi * Complex.I * ((al x c : ℂ) * (a ⬝ᵥ K₀ - b ⬝ᵥ N₀) - (al x c : ℂ) * al x c * (N₀ ⬝ᵥ τ *ᵥ N₀ / 2)
          - N₀ ⬝ᵥ ((al x c : ℂ) • (∑ c', al x c' • y c' + _root_.GlobalTheory.SimilTheta.tors τ al m k n x))) := by
      intro x
      rw [dotProduct_smul, smul_eq_mul]
      ring
    simp only [hterm]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← dotProduct_sum, hV, sum_intCast_mul_column_eq_of_transpose_mul_eq_smul m al hal c c, if_pos rfl]
    have hs' : ∑ x, (al x c : ℂ) = m + 2 * s := by exact_mod_cast hs
    rw [hs']
    have hsym : Nc ⬝ᵥ τ *ᵥ N₀ = N₀ ⬝ᵥ τ *ᵥ Nc := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.eq, dotProduct_comm]
    have hNK : Nc ⬝ᵥ K₀ = ((n c ⬝ᵥ k₀ : ℤ) : ℂ) := by simp [Nc, K₀, dotProduct]
    have hNK' : N₀ ⬝ᵥ Kc = ((n₀ ⬝ᵥ k c : ℤ) : ℂ) := by simp [N₀, Kc, dotProduct]
    unfold _root_.GlobalTheory.SimilTheta.lat
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    refine ⟨s * (ta - tb) + (n c ⬝ᵥ k₀ - n₀ ⬝ᵥ k c), ?_⟩
    push_cast
    rw [← hNK, ← hNK', ← hta, ← htb]
    linear_combination (2 * ↑Real.pi * Complex.I) * hsym
  · obtain ⟨ta, hta⟩ := exists_int_two_mul_dotProduct_of_half_integral a hab.1 k₀
    obtain ⟨tb, htb⟩ := exists_int_two_mul_dotProduct_of_half_integral b hab.2 n₀
    unfold _root_.GlobalTheory.SimilTheta.aut
    simp only [intCast_zsmul_vector, smul_dotProduct, dotProduct_smul, mulVec_smul, smul_eq_mul]
    rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨u, hu⟩ := Int.even_mul_pred_self (m : ℤ)
    have hmu : (m : ℂ) * (m - 1) = u + u := by exact_mod_cast hu
    refine ⟨-u * (ta - tb), ?_⟩
    simp only [zsmul_eq_mul, Int.cast_natCast]
    push_cast
    rw [← hta, ← htb]
    linear_combination (-(2 * ↑Real.pi * Complex.I) * ((a ⬝ᵥ fun i ↦ (k₀ i : ℂ)) - b ⬝ᵥ fun i ↦ (n₀ i : ℂ))) * hmu

end GlobalTheory.SimilTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.ClosedLimit

universe u

theorem surjective_of_isPushout {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {a : A ⟶ A'} {b : B ⟶ B'}
    {f' : A' ⟶ B'} (po : IsPushout f a b f') (s : Set B)
    (hs : Subring.closure (Set.range f.hom ∪ s) = ⊤) (h : ∀ x ∈ s, b.hom x ∈ f'.hom.range) :
    Function.Surjective f'.hom := by
  have h₁ : (⊤ : Subring B) ≤ f'.hom.range.comap b.hom := by
    rw [← hs, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | hx)
    · exact ⟨a.hom y, congr($(po.w.symm).hom y)⟩
    · exact h _ hx
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨y, rfl⟩ | hx)
  · exact h₁ (Subring.mem_top y)
  · exact hx

theorem exists_isClosedImmersion_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (α : D ⟶ E) (c : Cone D) (d : Cone E) (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, IsAffine (E.obj i)]
    [∀ i, LocallyOfFiniteType (α.app i)]
    (hα : ∀ {i j} (f : i ⟶ j), IsPullback (D.map f) (α.app i) (α.app j) (E.map f))
    (g : c.pt ⟶ d.pt) [IsClosedImmersion g] (hg : ∀ i, g ≫ d.π.app i = c.π.app i ≫ α.app i) :
    ∃ i, IsClosedImmersion (α.app i) := by
  classical
  have : IsAffine d.pt := Scheme.isAffine_of_isLimit _ hd
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  have one (x : Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i),
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hsurj ((c.π.app i).appTop x)
    obtain ⟨j, y, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E d hd y
    let m := IsCofiltered.min i j
    let a : m ⟶ i := IsCofiltered.minToLeft i j
    let b : m ⟶ j := IsCofiltered.minToRight i j
    have e₁ : c.π.app m ≫ D.map a = c.π.app i := c.w a
    have e₂ : c.π.app m ≫ α.app m ≫ E.map b = g ≫ d.π.app j := by
      rw [← reassoc_of% hg, d.w b]
    obtain ⟨l, f, hl⟩ := exists_app_map_eq_map_of_isLimit D c hc (U := ⊤) isCompact_univ
      ((D.map a).appTop x) ((α.app m ≫ E.map b).appTop y) (by
        have h₁ : (c.π.app m).appTop ((D.map a).appTop x) = (c.π.app i).appTop x :=
          congr(($e₁).appTop x)
        have h₂ : (c.π.app m).appTop ((α.app m ≫ E.map b).appTop y) =
          g.appTop ((d.π.app j).appTop y) := congr(($e₂).appTop y)
        exact h₁.trans (hy.symm.trans h₂.symm))
    refine ⟨l, f ≫ a, (E.map f ≫ E.map b).appTop y, ?_⟩
    have e₃ : α.app l ≫ E.map f ≫ E.map b = D.map f ≫ α.app m ≫ E.map b := by
      rw [α.naturality_assoc]
    have h₃ : (α.app l).appTop ((E.map f ≫ E.map b).appTop y) =
      (D.map f).appTop ((α.app m ≫ E.map b).appTop y) := congr(($e₃).appTop y)
    have h₄ : (D.map (f ≫ a)).appTop x = (D.map f).appTop ((D.map a).appTop x) :=
      congr(($(D.map_comp f a)).appTop x)
    exact h₃.trans (hl.symm.trans h₄.symm)
  have mono {j l : I} (f : j ⟶ i) (h : l ⟶ j) (x : Γ(D.obj i, ⊤))
      (hx : (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range) :
      (D.map (h ≫ f)).appTop.hom x ∈ (α.app l).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨(E.map h).appTop y, ?_⟩
    have h₃ : (α.app l).appTop ((E.map h).appTop y) =
      (D.map h).appTop ((α.app j).appTop y) := congr(($((α.naturality h).symm)).appTop y)
    have h₄ : (D.map (h ≫ f)).appTop x = (D.map h).appTop ((D.map f).appTop x) :=
      congr(($(D.map_comp h f)).appTop x)
    exact h₃.trans ((congrArg _ hy).trans h₄.symm)
  have many (s : Finset Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), ∀ x ∈ s,
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert x s _ ih =>
      obtain ⟨j₁, f₁, h₁⟩ := ih
      obtain ⟨j₂, f₂, h₂⟩ := one x
      obtain ⟨l, g₁, g₂, eg⟩ := IsCofiltered.cospan f₁ f₂
      refine ⟨l, g₁ ≫ f₁, fun y hy ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [eg]; exact mono _ _ _ h₂
      · exact mono _ _ _ (h₁ y hy)
  have hft : (α.app i).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  let _ := (α.app i).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  obtain ⟨j, f, hj⟩ := many s
  have : IsAffine (D.obj j) := isAffine_of_isAffineHom (D.map f)
  refine ⟨j, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  refine surjective_of_isPushout (isPushout_appTop_of_isPullback (hα f)) s ?_ hj
  exact (Algebra.adjoin_eq_ring_closure (s : Set Γ(D.obj i, ⊤))).symm.trans (congrArg Subalgebra.toSubring hs)

open GlobalTheory.Spread

section
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)

noncomputable def bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) : pullback (g₀ ≫ q) t ⟶ pullback q t :=
  pullback.lift (pullback.fst _ _ ≫ g₀) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

theorem bcHom_fst {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g₀ := pullback.lift_fst _ _ _

@[reassoc]
theorem bcHom_snd {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem isPullback_bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) :
    IsPullback (pullback.fst (g₀ ≫ q) t) (bcHom g₀ q t) g₀ (pullback.fst q t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q t) (v₂₂ := q) (h₃₁ := t) ?_
    (bcHom_fst g₀ q t).symm (.of_hasPullback _ _)
  rw [bcHom_snd]
  exact .of_hasPullback _ _

theorem isPullback_bcMap_bcHom {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) :
    IsPullback (bcMap (g₀ ≫ q) f) (bcHom g₀ q _) (bcHom g₀ q _) (bcMap q f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := g₀) (h₂₂ := pullback.fst _ _) ?_ ?_
    (isPullback_bcHom g₀ q _)
  · rw [bcMap_fst, bcMap_fst]
    exact isPullback_bcHom g₀ q _
  · apply pullback.hom_ext
    · rw [Category.assoc, bcHom_fst, bcMap_fst_assoc, Category.assoc, bcMap_fst, bcHom_fst]
    · rw [Category.assoc, bcHom_snd, bcMap_snd, Category.assoc, bcMap_snd, bcHom_snd_assoc]

theorem isClosedImmersion_of_isPullback {X Y X' Y' : Scheme.{0}} {g : X ⟶ Y} {πX : X ⟶ X₀}
    {πY : Y ⟶ Y₀} {g' : X' ⟶ Y'} {πX' : X' ⟶ X₀} {πY' : Y' ⟶ Y₀}
    (h : IsPullback πX g g₀ πY) (h' : IsPullback πX' g' g₀ πY') (m : Y' ⟶ Y) (hm : m ≫ πY = πY')
    [IsClosedImmersion g] : IsClosedImmersion g' := by
  subst hm
  have : IsPullback (h.lift πX' (g' ≫ m) (by rw [Category.assoc, h'.w])) g' g m :=
    IsPullback.of_right (by rw [h.lift_fst]; exact h') (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback this inferInstance

theorem exists_finset_bcHom (A : Type) [CommRing A] [Algebra k A] [IsAffine Y₀]
    [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀]
    [IsClosedImmersion (bcHom g₀ q (spMap (algebraMap k A)))] :
    ∃ s : Finset A, IsClosedImmersion
      (bcHom g₀ q (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))) := by
  classical
  let α : bcDiagram (g₀ ≫ q) A ⟶ bcDiagram q A :=
    { app s := bcHom g₀ q _
      naturality s t f := (isPullback_bcMap_bcHom g₀ q _).w }
  have (s : (Finset A)ᵒᵖ) : IsAffine ((bcDiagram q A).obj s) :=
    inferInstanceAs (IsAffine (pullback q
      (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))))
  have (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (α.app s) :=
    MorphismProperty.of_isPullback (isPullback_bcHom g₀ q _) inferInstance
  have : @IsClosedImmersion (bcCone (g₀ ≫ q) A).pt (bcCone q A).pt
    (bcHom g₀ q (spMap (algebraMap k A))) := ‹_›
  obtain ⟨s, hs⟩ := exists_isClosedImmersion_of_isLimit _ _ α (bcCone (g₀ ≫ q) A) (bcCone q A)
    (isLimitBcCone _ _) (isLimitBcCone _ _) (fun f ↦ isPullback_bcMap_bcHom g₀ q _)
    (bcHom g₀ q (spMap (algebraMap k A))) (fun s ↦ (isPullback_bcMap_bcHom g₀ q _).w.symm)
  exact ⟨s.unop, hs⟩

end

theorem descends_of_isAffine (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0})
    (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [IsAffine Y₀] [QuasiCompact g₀] [QuasiSeparated g₀]
    [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S)
    (hY : IsPullback πY p q (spMap R₀.subtype)) (hX : IsPullback πX g g₀ πY)
    (hg : IsClosedImmersion g) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁),
        πY₁ ≫ q = p₁ ≫ spMap (Subring.inclusion h) → IsPullback πX₁ g₁ g₀ πY₁ →
          IsClosedImmersion g₁ := by
  have hY' : IsPullback πY p q (spMap (algebraMap R₀ S)) := hY
  have := isClosedImmersion_of_isPullback g₀ hX (isPullback_bcHom g₀ q (spMap (algebraMap R₀ S)))
    hY'.isoPullback.inv hY'.isoPullback_inv_fst
  obtain ⟨s, hs'⟩ := exists_finset_bcHom g₀ q S
  refine ⟨s, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let i : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hi : spMap i ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact isClosedImmersion_of_isPullback g₀
    (isPullback_bcHom g₀ q (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))))) hX₁
    (pullback.lift πY₁ (p₁ ≫ spMap i) (by rw [Category.assoc, hi, hY₁])) (pullback.lift_fst _ _ _)

theorem exists_isPullback_restrict {X₀ Y₀ X Y V : Scheme.{0}} {g₀ : X₀ ⟶ Y₀} {g : X ⟶ Y}
    {πX : X ⟶ X₀} {πY : Y ⟶ Y₀} (hX : IsPullback πX g g₀ πY) (j : V ⟶ Y₀) :
    ∃ m : pullback g (pullback.fst πY j) ⟶ pullback g₀ j,
      IsPullback m (pullback.snd _ _) (pullback.snd _ _) (pullback.snd πY j) := by
  have h := (IsPullback.of_hasPullback g (pullback.fst πY j)).paste_horiz hX
  rw [pullback.condition (f := πY)] at h
  refine ⟨pullback.lift (pullback.fst _ _ ≫ πX) (pullback.snd _ _ ≫ pullback.snd πY j)
    (by rw [h.w, Category.assoc]), ?_⟩
  exact IsPullback.of_right (by rw [pullback.lift_fst]; exact h) (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)

end GlobalTheory.ClosedLimit

namespace GlobalTheory

open ClosedLimit in
theorem isClosedImmersion_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0}) (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [QuasiCompact q] [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S), IsPullback πY p q (spMap R₀.subtype) → IsPullback πX g g₀ πY → IsClosedImmersion g → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁), IsPullback πY₁ p₁ q (spMap (Subring.inclusion h)) → IsPullback πX₁ g₁ g₀ πY₁ → IsClosedImmersion g₁ := by
  classical
  intro S _ R₀ X₀ Y₀ X Y g₀ q _ _ _ _ g πX πY p hY hX hg
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace q
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstance
  have key (i : 𝒰.I₀) := descends_of_isAffine S R₀ _ _ _ _ (pullback.snd g₀ (𝒰.f i)) (𝒰.f i ≫ q) _ _ _ _
    ((IsPullback.of_hasPullback πY (𝒰.f i)).flip.paste_vert hY)
    (exists_isPullback_restrict hX (𝒰.f i)).choose_spec inferInstance
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (𝒰.pullback₁ πY₁)).mpr fun i ↦ ?_
  exact hF i R₁ h
    ((Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem F (Finset.mem_univ (α := 𝒰.I₀) i))).trans hs) _ _ _ _ _ _
    ((IsPullback.of_hasPullback πY₁ (𝒰.f i)).flip.paste_vert hY₁).w
    (exists_isPullback_restrict hX₁ (𝒰.f i)).choose_spec

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_descends_to_subring' : ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0}) (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [QuasiCompact q] [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S), IsPullback πY p q (spMap R₀.subtype) → IsPullback πX g g₀ πY → IsClosedImmersion g → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁), IsPullback πY₁ p₁ q (spMap (Subring.inclusion h)) → IsPullback πX₁ g₁ g₀ πY₁ → IsClosedImmersion g₁ := by
  first | exact @GlobalTheory.isClosedImmersion_descends_to_subring | exact GlobalTheory.isClosedImmersion_descends_to_subring | (intros; apply GlobalTheory.isClosedImmersion_descends_to_subring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta
open ReciprocityTheory.PTheta Matrix

private theorem levelTheta_one_zero {g : ℕ} (a b : Fin g → ℝ) (τ : Matrix (Fin g) (Fin g) ℂ)
    (z : Fin g → ℂ) : GlobalTheory.levelTheta a b 1 τ 0 z = theta a b z τ := by
  unfold GlobalTheory.levelTheta
  have e1 : ((fun i => ((0 : Fin g → ℤ) i : ℝ) / ((1 : ℕ) : ℝ)) + a) = a := by
    funext i; simp
  rw [e1]
  simp

theorem differentiableOn_thetaChar_comp {g : ℕ} {a b : Fin g → ℂ} (h : charHalf g a b)
    {w : (Fin g → Fin g → ℂ) → Fin g → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun p => thetaChar (per p) a b (w p)) (Key.phDom g) := by
  obtain ⟨ha, hb⟩ := h
  have hF := GlobalTheory.KeyKa.LevelBasis.holFam_levelTheta (fun i => (a i).re) (fun i => (b i).re) Nat.one_pos 0
  unfold GlobalTheory.KeyKa.HolFam at hF
  simp only [levelTheta_one_zero] at hF
  have hm : Differentiable ℂ (fun p : Fin g → Fin g → ℂ => (p, w p)) := by fun_prop
  refine (hF.comp hm.differentiableOn (fun p hp => ⟨hp, Set.mem_univ _⟩)).congr (fun p _ => ?_)
  rw [GlobalTheory.TorusAlg.thetaChar_eq_theta _ ha hb]
  rfl

theorem differentiable_per_apply {g : ℕ} (i j : Fin g) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => per p i j) := by
  simp only [GlobalTheory.KeyKa.per, ReciprocityTheory.ChartRestriction.G.Key.phSym, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.of_apply, smul_eq_mul]
  fun_prop

theorem differentiable_lat {g : ℕ} (k n : Fin g → ℤ) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) k n) := by
  rw [differentiable_pi]
  intro i
  have hp := differentiable_per_apply (g := g)
  simp only [lat, Pi.add_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem differentiable_tors {g : ℕ} (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Differentiable ℂ (fun p : Fin g → Fin g → ℂ => tors (per p) al m k n r) := by
  have hl : ∀ c, Differentiable ℂ (fun p : Fin g → Fin g → ℂ => lat (per p) (k c) (n c)) :=
    fun c => differentiable_lat (k c) (n c)
  unfold tors
  exact (Differentiable.fun_sum fun c _ => (hl c).const_smul (al r c)).const_smul ((m : ℂ)⁻¹)

theorem level_one_and_holomorphic : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  intro g a b h
  refine ⟨fun p hp => ?_, fun al m k n y => ?_, fun k n z => ?_⟩
  · have hτ : per p ∈ SiegelH (Fin g) := hp
    obtain ⟨ha, hb⟩ := h
    have e := GlobalTheory.KeyKa.LevelBasis.isLevel_iff (per p) (fun i => (a i).re) (fun i => (b i).re) 1
      (thetaChar (per p) a b)
    rw [GlobalTheory.TorusAlg.ofRealVec_re ha, GlobalTheory.TorusAlg.ofRealVec_re hb] at e
    rw [e, (GlobalTheory.TorusAlg.thetaChar_level hτ.1 hτ.2 ha hb).2.1]
    exact Submodule.mem_span_singleton_self _
  · unfold simTheta
    have hθ : ∀ r, DifferentiableOn ℂ
        (fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r)) (Key.phDom g) :=
      fun r => differentiableOn_thetaChar_comp h
        ((differentiable_const _).add (differentiable_tors al m k n r))
    have hprod : DifferentiableOn ℂ
        (∏ r, fun p => thetaChar (per p) a b (∑ c, al r c • y c + tors (per p) al m k n r))
        (Key.phDom g) :=
      Finset.prod_induction _ (fun F => DifferentiableOn ℂ F (Key.phDom g))
        (fun _ _ h1 h2 => h1.mul h2) (differentiableOn_const 1) (fun r _ => hθ r)
    rw [Finset.prod_fn] at hprod
    exact hprod.mul (differentiableOn_const _)
  · have hp := differentiable_per_apply (g := g)
    simp only [aut, Matrix.mulVec, dotProduct]
    fun_prop

end GlobalTheory.SimilTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_level_one_and_holomorphic_parameter : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  first | exact @GlobalTheory.SimilTheta.level_one_and_holomorphic | exact GlobalTheory.SimilTheta.level_one_and_holomorphic | (intros; apply GlobalTheory.SimilTheta.level_one_and_holomorphic <;> assumption)
end
end
