module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRange
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem localization_away_descent_range :
 ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  classical
  intro k _ P T
  have hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ),
      IsLocalization.mk' (Localization.Away P) f
        (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t := by
    intro t
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P) t
    obtain ⟨n, hn⟩ := s.2
    exact ⟨f, n, by congr 1; exact Subtype.ext hn⟩
  choose f n hfn using hs
  refine ⟨T.biUnion (fun t => (f t).coeffs), ?_⟩
  intro R hF P₁ h hP t ht
  have hlift : f t ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (f t).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · have : (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k) := by
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩
      exact ⟨⟨_, hF this⟩, rfl⟩
  obtain ⟨f₁, hf₁⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨IsLocalization.mk' (Localization.Away P₁) f₁
    (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁,
    Polynomial.map_pow, hP]
  have key := IsLocalization.mk'_spec' (Localization.Away P) (f t)
    (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)
  rw [hfn t] at key
  exact key.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRangeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_away_lift_descent : ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  first | exact @GlobalTheory.localization_away_descent_range | exact GlobalTheory.localization_away_descent_range | (intros; apply GlobalTheory.localization_away_descent_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.descentLocInj : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  intro k _ P hP R P₁ h _
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P₁) z
  simp only at hz ⊢
  unfold IsLocalization.Away.lift at hz
  rw [IsLocalization.lift_mk'_spec, mul_zero] at hz
  have h2 := hz
  have hinj : Function.Injective (algebraMap (Polynomial k) (Localization.Away P)) :=
    IsLocalization.injective (Localization.Away P) (powers_le_nonZeroDivisors_of_noZeroDivisors hP)
  have h3 : f.map R.subtype = 0 := by
    apply hinj
    simpa using h2
  have h4 : f = 0 := by
    have := Polynomial.map_injective R.subtype Subtype.val_injective
    exact this (by simpa using h3)
  subst h4
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizationAway_polynomial_subring_lift_injective : ∀ (k : Type) [Field k] (P : Polynomial k), P ≠ 0 → ∀ (R : Subring k) (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → Function.Injective (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h) := by
  first | exact @GlobalTheory.descentLocInj | exact GlobalTheory.descentLocInj | (intros; apply GlobalTheory.descentLocInj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurve
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadCurve

open Polynomial

theorem group_sections_curve_descend : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  intro k _ G _ hG g hg m hm hmk s hs P hP u a b hu hab
  classical
  obtain ⟨hc, h1, h2, h3, h5⟩ := hG
  obtain ⟨R₀, G₀, i₀, ic₀, φ, -, hR₀, s₁, s₂, s₃, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring k G ∅ h1 h2 h3

  haveI := s₁; haveI := s₂; haveI := s₃
  set L := Localization.Away P with hL

  have hu₀ : (u ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ L) := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hu]
    exact ModelDescent.spMap_comp_eq (RingHom.ext fun r => (IsScalarTower.algebraMap_apply R₀ k L r).symm)
  obtain ⟨S, yS, hSfg, -, hyS⟩ := Spread.exists_fg_points G₀.hom (fun _ : Unit => u ≫ φ) (fun _ => hu₀) ⊥
    Subalgebra.fg_bot
  obtain ⟨T, hT⟩ := hSfg
  obtain ⟨Fc, hFc⟩ := GlobalTheory.T.exists_finset_away_lift_descent k P T

  set X' : L := algebraMap (Polynomial k) L X with hX'
  have haev : ∀ (c : L →ₐ[k] k) (q : Polynomial k), c (algebraMap (Polynomial k) L q) = q.eval (c X') := by
    intro c q
    have : (c : L →+* k).comp (algebraMap (Polynomial k) L) = Polynomial.evalRingHom (c X') := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        have e : algebraMap (Polynomial k) L (C r) = algebraMap k L r := by
          rw [IsScalarTower.algebraMap_apply k (Polynomial k) L, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [e]
        exact c.commutes r
      · simp [hX']
    exact congrArg (fun f : Polynomial k →+* k => f q) this
  have hne : ∀ c : L →ₐ[k] k, P.eval (c X') ≠ 0 := by
    intro c
    rw [← haev]
    exact ((IsLocalization.Away.algebraMap_isUnit P).map c).ne_zero

  let F : Finset k := Fc ∪ P.coeffs ∪ {(m : k)⁻¹, a X', b X', (P.eval (a X'))⁻¹, (P.eval (b X'))⁻¹}

  have hx₀ : ∀ i : s, (i.1.left ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ k) := by
    intro i
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w i.1]
    exact Category.id_comp _
  obtain ⟨R, y, hRfg, hR₁R, hy⟩ := Spread.exists_fg_points G₀.hom (fun i : s => i.1.left ≫ φ) hx₀
    (Algebra.adjoin R₀ (F : Set k)) (Subalgebra.fg_adjoin_finset F)
  let R' : Subring k := R.toSubring
  have hFR : (F : Set k) ⊆ R' := fun x hx => hR₁R (Algebra.subset_adjoin hx)
  have hR₀R : R₀ ≤ R' := fun r hr => R.algebraMap_mem ⟨r, hr⟩
  let jn : R₀ →+* R' := Subring.inclusion hR₀R
  have hjn : R'.subtype.comp jn = R₀.subtype := rfl
  have hjnsp : spMap R'.subtype ≫ spMap jn = spMap R₀.subtype := ModelDescent.spMap_comp_eq hjn
  let G₁ : Over (Sp R') := (Over.pullback (spMap jn)).obj G₀
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁c : IsCommMonObj G₁ := Functor.isCommMonObj_obj
  have hψ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap jn) (spMap R'.subtype)
    (hφ.congr hjnsp.symm rfl)
  set ψ := pullback.lift φ (G.hom ≫ spMap R'.subtype) (by rw [hφ.1.w, Category.assoc, hjnsp]) with hψdef
  have hψ₁ : ψ ≫ pullback.fst G₀.hom (spMap jn) = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G₀.hom (spMap jn) = G.hom ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hyR : ∀ i : s, (y i : Sp R' ⟶ G₀.left) ≫ G₀.hom = spMap jn := fun i => (hy i).1
  have hyk : ∀ i : s, spMap R'.subtype ≫ (y i : Sp R' ⟶ G₀.left) = i.1.left ≫ φ := fun i => (hy i).2

  have hsq : IsPullback hψ.1.isoPullback.inv (pullback.snd G₁.hom (spMap R'.subtype)) G.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hgc : GeometricallyConnected (pullback.snd G₁.hom (spMap R'.subtype)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h5
  have hgd : SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R'.subtype)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hsq hg
  have hunit : IsUnit (m : R') := by
    refine IsUnit.of_mul_eq_one (a := (m : R')) ⟨(m : k)⁻¹, hFR (by simp [F])⟩ (Subtype.ext ?_)
    simp [mul_inv_cancel₀ hmk]

  let sec : s → (𝟙_ (Over (Sp R')) ⟶ G₁) := fun i =>
    Over.homMk (pullback.lift (y i : Sp R' ⟶ G₀.left) (𝟙 _) (by rw [hyR i, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  have hsec₁ : ∀ i : s, (sec i).left ≫ pullback.fst G₀.hom (spMap jn) = y i := fun i => pullback.lift_fst _ _ _
  have hkey : ∀ i : s, i.1.left ≫ ψ = spMap R'.subtype ≫ (sec i).left := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hsec₁, hyk]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w i.1, Category.assoc]
      erw [pullback.lift_snd]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hdist : ∀ i j : s, spMap R'.subtype ≫ (sec i).left = spMap R'.subtype ≫ (sec j).left → i = j := by
    intro i j e
    have e' : i.1.left ≫ φ = j.1.left ≫ φ := by
      rw [← hψ₁, ← Category.assoc, ← Category.assoc, hkey, hkey, e]
    refine Subtype.ext (Over.OverMorphism.ext (hφ.1.hom_ext e' ?_))
    rw [Over.w i.1, Over.w j.1]
  have hsec_inj : Function.Injective sec := fun i j e => hdist i j (by rw [e])
  haveI hsep₁ : IsSeparated G₁.hom := show IsSeparated (pullback.snd _ _) from inferInstance
  have hpow : ∀ i : s, sec i ^ m = 1 := by
    intro i
    have A := GlobalTheory.FrameMove.pow_comm hψ (hkey i) m
    have B := GlobalTheory.FrameMove.pow_comm hψ (hkey i) 0
    rw [hs i.1 i.2] at A
    rw [pow_zero, pow_zero] at B
    refine Over.OverMorphism.ext (Spread.point_ext R'.subtype Subtype.val_injective G₁.hom ?_ (A.symm.trans B))
    rw [Over.w, Over.w]

  have hPl : P ∈ Polynomial.lifts R'.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts P).2 fun n => ?_
    by_cases hn : P.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨P.coeff n, hFR (by simp [F, Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨P₁, hP₁⟩ := Polynomial.mem_lifts P |>.1 hPl
  have hP₁0 : P₁ ≠ 0 := by
    rintro rfl
    exact hP (by rw [← hP₁, Polynomial.map_zero])
  have hPu : IsUnit (((algebraMap (Polynomial k) L).comp (Polynomial.mapRingHom R'.subtype)) P₁) := by
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, hP₁]
    exact IsLocalization.Away.algebraMap_isUnit P
  set Lm := IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hPu with hLm
  have hinj : Function.Injective Lm := GlobalTheory.T.localizationAway_polynomial_subring_lift_injective k P hP R' P₁ hPu hP₁
  have hrange : ∀ t ∈ T, t ∈ Lm.range := hFc R' (fun x hx => hFR (by simp [F, hx])) P₁ hPu hP₁
  have hLmC : ∀ r : R', Lm (algebraMap R' (Localization.Away P₁) r) = algebraMap k L r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R' (Polynomial R') (Localization.Away P₁), hLm,
      IsLocalization.Away.lift_eq]
    simp [Polynomial.algebraMap_apply, IsScalarTower.algebraMap_apply k (Polynomial k) L]

  have hcl : Subring.closure (Set.range (algebraMap R₀ L) ∪ (T : Set L)) ≤ Lm.range := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · refine ⟨algebraMap R' (Localization.Away P₁) (jn r), ?_⟩
      rw [hLmC]
      exact (IsScalarTower.algebraMap_apply R₀ k L r).symm
    · exact hrange z hz
  have hSr : ∀ z : S, S.val.toRingHom z ∈ Lm.range := by
    intro z
    apply hcl
    rw [← Algebra.adjoin_eq_ring_closure, hT]
    exact z.2
  obtain ⟨gS, hgS⟩ := ModelDescent.exists_factor S.val.toRingHom Lm hinj hSr
  have hcomp : gS.comp (algebraMap R₀ S) = (algebraMap R' (Localization.Away P₁)).comp jn := by
    refine RingHom.ext fun r => hinj ?_
    change Lm (gS (algebraMap R₀ S r)) = Lm (algebraMap R' _ (jn r))
    rw [← RingHom.comp_apply Lm gS, hgS, hLmC]
    change (algebraMap R₀ L r) = _
    exact IsScalarTower.algebraMap_apply R₀ k L r
  let u₁' : Sp (Localization.Away P₁) ⟶ G₀.left := spMap gS ≫ yS ()
  have hu₁' : u₁' ≫ G₀.hom = spMap (algebraMap R' (Localization.Away P₁)) ≫ spMap jn := by
    rw [Category.assoc, (hyS ()).1, ModelDescent.spMap_comp_eq hcomp]
    exact (ModelDescent.spMap_comp_eq rfl).symm
  let u₁ : Sp (Localization.Away P₁) ⟶ G₁.left :=
    pullback.lift u₁' (spMap (algebraMap R' (Localization.Away P₁))) hu₁'
  have hu₁f : u₁ ≫ pullback.fst G₀.hom (spMap jn) = u₁' := pullback.lift_fst _ _ _
  have hu₁s : u₁ ≫ G₁.hom = spMap (algebraMap R' (Localization.Away P₁)) := pullback.lift_snd _ _ _

  have hpt : ∀ c : L →ₐ[k] k, c X' ∈ R' → (P.eval (c X'))⁻¹ ∈ R' → ∃ (w0 : R')
      (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm := by
    intro c hc hci
    have hev : ((Polynomial.eval (⟨c X', hc⟩ : R') P₁ : R') : k) = P.eval (c X') := by
      refine Eq.trans ?_ (congrArg (Polynomial.eval (c X')) hP₁)
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply R'.subtype _).symm
    have hw0 : IsUnit (Polynomial.evalRingHom (⟨c X', hc⟩ : R') P₁) := by
      refine IsUnit.of_mul_eq_one (b := ⟨(P.eval (c X'))⁻¹, hci⟩) (Subtype.ext ?_)
      rw [Subring.coe_mul, Polynomial.coe_evalRingHom, hev]
      exact mul_inv_cancel₀ (hne c)
    refine ⟨⟨c X', hc⟩, hw0, IsLocalization.ringHom_ext (Submonoid.powers P₁) ?_⟩
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        haev]
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl

  obtain ⟨α, hα, hαe⟩ := hpt a (hFR (by simp [F])) (hFR (by simp [F]))
  obtain ⟨β, hβ, hβe⟩ := hpt b (hFR (by simp [F])) (hFR (by simp [F]))
  have key : ∀ (c : L →ₐ[k] k) (w0 : R') (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm →
      (spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) ≫ u₁) ≫
        pullback.fst G₀.hom (spMap jn) = spMap c.toRingHom ≫ u ≫ φ := by
    intro c w0 hw0 hce
    rw [Category.assoc, Category.assoc, hu₁f, ← Category.assoc, ModelDescent.spMap_comp_eq hce,
      ← ModelDescent.spMap_comp_eq (f := Lm) (g := c.toRingHom) rfl, Category.assoc, ← Category.assoc (spMap Lm),
      ModelDescent.spMap_comp_eq hgS, (hyS ()).2]
  have hcG : ∀ c : L →ₐ[k] k, spMap c.toRingHom ≫ u ≫ G.hom = 𝟙 _ := by
    intro c
    rw [hu, ModelDescent.spMap_comp_eq (h := RingHom.id k) (RingHom.ext c.commutes)]
    simp [spMap]
  have hdistc : spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠
      spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
    intro e
    apply hab
    have ea := key a α hα hαe
    have eb := key b β hβ hβe
    rw [e] at ea
    have e2 : spMap a.toRingHom ≫ u ≫ φ = spMap b.toRingHom ≫ u ≫ φ := ea.symm.trans eb
    refine hφ.1.hom_ext (by simpa only [Category.assoc] using e2) ?_
    rw [Category.assoc, hcG, Category.assoc, hcG]
  refine ⟨R', G₁, inferInstance, SpreadGroup.finiteType_of_fg hR₀ hRfg, hunit, hG₁c,
    show Smooth (pullback.snd _ _) from inferInstance, hsep₁, show QuasiCompact (pullback.snd _ _) from inferInstance,
    hgc, hgd, ⟨s.attach.image sec, ?_, ?_, ?_⟩, P₁, hP₁0, u₁, α, β, hα, hβ, hu₁s, hdistc⟩
  · rw [Finset.card_image_of_injective _ hsec_inj, Finset.card_attach]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hpow i
  · intro x hx z hz hxz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
    exact fun e => hxz (by rw [hdist i j e])

end GlobalTheory.SpreadCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subring_descent_group_sections_curve : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  first | exact @GlobalTheory.SpreadCurve.group_sections_curve_descend | exact GlobalTheory.SpreadCurve.group_sections_curve_descend | (intros; apply GlobalTheory.SpreadCurve.group_sections_curve_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CurveBaseChange

variable {R F : Type} [CommRing R] [Field F] (ψ : R →+* F) (P₁ : Polynomial R)

def locMap : Localization.Away P₁ →+* Localization.Away (P₁.map ψ) :=
  IsLocalization.Away.map (Localization.Away P₁) (Localization.Away (Polynomial.mapRingHom ψ P₁)) (Polynomial.mapRingHom ψ) P₁

theorem locMap_algebraMap (p : Polynomial R) :
    locMap ψ P₁ (algebraMap (Polynomial R) _ p) = algebraMap (Polynomial F) _ (p.map ψ) := by
  unfold locMap IsLocalization.Away.map
  erw [IsLocalization.map_eq]
  rfl

theorem eval_map_apply' (a : R) (p : Polynomial R) : (p.map ψ).eval (ψ a) = ψ (p.eval a) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem isUnit_eval (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    IsUnit (Polynomial.evalRingHom (ψ a) (P₁.map ψ)) := by
  simpa [eval_map_apply'] using ha.map ψ

def evalAt (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    Localization.Away (P₁.map ψ) →ₐ[F] F where
  toRingHom := IsLocalization.Away.lift (S := Localization.Away (P₁.map ψ)) (P₁.map ψ) (isUnit_eval ψ P₁ a ha)
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) (Localization.Away (P₁.map ψ))]
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq]

theorem evalAt_comp (a : R) (ha : IsUnit (Polynomial.evalRingHom a P₁)) :
    (evalAt ψ P₁ a ha).toRingHom.comp (locMap ψ P₁) =
      ψ.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ ha) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers P₁)
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, locMap_algebraMap]
  simp [evalAt, IsLocalization.Away.lift, IsLocalization.lift_eq, eval_map_apply']

theorem locMap_comp_algebraMap :
    (locMap ψ P₁).comp (algebraMap R (Localization.Away P₁)) =
      (algebraMap F (Localization.Away (P₁.map ψ))).comp ψ := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁), locMap_algebraMap,
    RingHom.comp_apply, IsScalarTower.algebraMap_apply F (Polynomial F) (Localization.Away (P₁.map ψ))]
  simp [Polynomial.algebraMap_apply]

end GlobalTheory.CurveBaseChange

namespace GlobalTheory


open GlobalTheory.CurveBaseChange in
theorem curve_baseChange_two_points : ∀ (R F : Type) [CommRing R] [Field F] (ψ : R →+* F) (X : Over (Sp R)) (P₁ : Polynomial R) (u₁ : Sp (Localization.Away P₁) ⟶ X.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ X.hom = spMap (algebraMap R (Localization.Away P₁)) → IsUnit (ψ P₁.leadingCoeff) → spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ → ∃ (P' : Polynomial F) (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ ((Over.pullback (spMap ψ)).obj X).left) (a' b' : Localization.Away P' →ₐ[F] F), u' ≫ ((Over.pullback (spMap ψ)).obj X).hom = spMap (algebraMap F (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro R F _ _ ψ X P₁ u₁ α β hα hβ hu hlc hne
  have hP : P₁.map ψ ≠ 0 := by
    intro h
    have h' := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero ψ hlc.ne_zero
    rw [h, Polynomial.leadingCoeff_zero] at h'
    exact hlc.ne_zero h'.symm
  have hcomm : (spMap (locMap ψ P₁) ≫ u₁) ≫ X.hom =
      spMap (algebraMap F (Localization.Away (P₁.map ψ))) ≫ spMap ψ := by
    rw [Category.assoc, hu, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, locMap_comp_algebraMap]
  refine ⟨P₁.map ψ, hP, pullback.lift _ _ hcomm, evalAt ψ P₁ α hα, evalAt ψ P₁ β hβ, ?_, ?_⟩
  · exact pullback.lift_snd _ _ _
  · intro h
    apply hne
    have h2 := congrArg (· ≫ pullback.fst X.hom (spMap ψ)) h
    simp only [Category.assoc, pullback.lift_fst] at h2
    rw [← Category.assoc, ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, ← evalAt_comp,
      ← evalAt_comp, Geo.Tor.spMap_comp, Geo.Tor.spMap_comp, Category.assoc, Category.assoc]
    exact h2

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveBaseChangeTwoDistinctPointsOfFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_baseChange_two_distinct_points_of_field : ∀ (R F : Type) [CommRing R] [Field F] (ψ : R →+* F) (X : Over (Sp R)) (P₁ : Polynomial R) (u₁ : Sp (Localization.Away P₁) ⟶ X.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ X.hom = spMap (algebraMap R (Localization.Away P₁)) → IsUnit (ψ P₁.leadingCoeff) → spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap ψ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ → ∃ (P' : Polynomial F) (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ ((Over.pullback (spMap ψ)).obj X).left) (a' b' : Localization.Away P' →ₐ[F] F), u' ≫ ((Over.pullback (spMap ψ)).obj X).hom = spMap (algebraMap F (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.curve_baseChange_two_points | exact GlobalTheory.curve_baseChange_two_points | (intros; apply GlobalTheory.curve_baseChange_two_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadConn

variable {S : Scheme.{0}}

theorem unit_comp (G : Over S) [GrpObj G] : (η[G]).left ≫ G.hom = 𝟙 S := by
  have h := Over.w (η[G])
  have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
  rwa [h2] at h

theorem hom_unit (G : Over S) [GrpObj G] (s : S) : G.hom ((η[G]).left s) = s := by
  rw [← Scheme.Hom.comp_apply, unit_comp]
  rfl

theorem isConnected_fibre (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : G.hom ⁻¹' {s} ⊆ U) : _root_.IsConnected (G.hom ⁻¹' {s}) := by
  have hu : (η[G]).left s ∈ G.hom ⁻¹' {s} := hom_unit G s
  have he : connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) = G.hom ⁻¹' {s} := by
    refine (connectedComponentIn_subset _ _).antisymm fun x hx => ?_
    have h1 := (hU x).1 (h hx)
    have hx' : G.hom x = s := hx
    rwa [hx'] at h1
  rw [← he]
  exact isConnected_connectedComponentIn_iff.2 hu

theorem subset_of_isPreconnected (G : Over S) [GrpObj G] (U : Set G.left)
    (hU : ∀ x : G.left, x ∈ U ↔ x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x)))
    (s : S) (h : _root_.IsPreconnected (G.hom ⁻¹' {s})) : G.hom ⁻¹' {s} ⊆ U := by
  intro x hx
  have hx' : G.hom x = s := hx
  refine (hU x).2 ?_
  rw [hx']
  exact h.subset_connectedComponentIn (hom_unit G s) subset_rfl hx

theorem geometricallyConnected_fibre (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    [QuasiCompact G.hom] (s : S) (h : _root_.IsConnected (G.hom ⁻¹' {s})) :
    GeometricallyConnected (G.hom.fiberToSpecResidueField s) := by
  have hc : ConnectedSpace (G.hom.fiber s) :=
    (G.hom.fiberHomeo s).connectedSpace_iff.2 (isConnected_iff_connectedSpace.1 h)
  exact GlobalTheory.RatPointConn.geometricallyConnected_of_ratPoint (S.residueField s)
    (Over.mk (G.hom.fiberToSpecResidueField s))
    (inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (S.fromSpecResidueField s))))
    (inferInstanceAs (QuasiCompact (pullback.snd G.hom (S.fromSpecResidueField s)))) hc
    ⟨Over.homMk (pullback.lift (S.fromSpecResidueField s ≫ (η[G]).left) (𝟙 _)
      (by rw [Category.assoc, unit_comp, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _)⟩

theorem isConnected_of_geometricallyConnected_fibre {X : Scheme.{0}} (f : X ⟶ S) (s : S)
    (h : GeometricallyConnected (f.fiberToSpecResidueField s)) : _root_.IsConnected (f ⁻¹' {s}) := by
  have hc : ConnectedSpace (f.fiber s) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s)
  exact isConnected_iff_connectedSpace.2 ((f.fiberHomeo s).connectedSpace_iff.1 hc)

end GlobalTheory.SpreadConn

namespace GlobalTheory.SpreadConn

theorem geometricallyConnected_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  intro R _ _ _ G _ hs hq K _ e he hgc
  obtain ⟨G₀, _, j, -, hjo, hj⟩ := GlobalTheory.identityComponentOpen (Sp R) G hs
  let U : Set G.left := Set.range j.left
  let η₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hη : η₀ ∈ Set.range (spMap e) := ⟨(default : PrimeSpectrum K), by
    apply PrimeSpectrum.ext
    change Ideal.comap e (default : PrimeSpectrum K).asIdeal = ⊥
    have h0 : (default : PrimeSpectrum K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [h0]
    exact Ideal.comap_bot_of_injective _ he⟩
  have hgen : GeometricallyConnected (G.hom.fiberToSpecResidueField η₀) :=
    GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom (spMap e)
      ((Sp R).fromSpecResidueField η₀)
      (by rw [Scheme.range_fromSpecResidueField]; exact Set.singleton_subset_iff.2 hη) hgc
  have hsub0 : G.hom ⁻¹' {η₀} ⊆ U := subset_of_isPreconnected G U hj η₀
    (isConnected_of_geometricallyConnected_fibre G.hom η₀ hgen).isPreconnected
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have hUo : IsOpen U := j.left.isOpenEmbedding.isOpen_range
  have hZ : Topology.IsConstructible Uᶜ :=
    (IsRetrocompact.isConstructible hUo fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _).compl
  have hC : Topology.IsConstructible (G.hom '' Uᶜ) := G.hom.isConstructible_image hZ
  obtain ⟨V, hV, h1, h2⟩ := GlobalTheory.exists_isOpen_inter_closure_subset_of_isConstructible continuous_id hC.compl
  rw [Set.preimage_id] at h1 h2
  have hηC : η₀ ∈ (G.hom '' Uᶜ)ᶜ := by
    rintro ⟨x, hx, hxη⟩
    exact hx (hsub0 hxη)
  have hgenz : ∀ p : Sp R, η₀ ⤳ p := fun p =>
    (PrimeSpectrum.le_iff_specializes (η₀ : PrimeSpectrum R) (p : PrimeSpectrum R)).1
      (show (⊥ : Ideal R) ≤ (p : PrimeSpectrum R).asIdeal from bot_le)
  have hcl : closure (G.hom '' Uᶜ)ᶜ = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    exact closure_mono (Set.singleton_subset_iff.2 hηC) (specializes_iff_mem_closure.1 (hgenz p))
  rw [hcl, Set.inter_univ] at h1 h2
  have hVne : V.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h2
    exact Set.empty_ne_univ h2
  obtain ⟨p₀, hp₀⟩ := hVne
  have hηV : η₀ ∈ V := (hgenz p₀).mem_open hV hp₀
  obtain ⟨_, ⟨f, rfl⟩, hf, hfV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηV hV
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).1 hf ?_, fun F _ ψ hψ => ?_⟩
  · rw [he (h0.trans (map_zero e).symm)]
    exact zero_mem _
  · let p : Sp R := spMap ψ (default : PrimeSpectrum F)
    have hpf : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      refine (PrimeSpectrum.mem_basicOpen f (p : PrimeSpectrum R)).2 fun hfp => ?_
      change ψ f ∈ (default : PrimeSpectrum F).asIdeal at hfp
      exact (default : PrimeSpectrum F).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hfp hψ)
    have hpC : p ∉ G.hom '' Uᶜ := h1 (hfV hpf)
    have hsub : G.hom ⁻¹' {p} ⊆ U := fun x hx => by
      by_contra hxU
      exact hpC ⟨x, hxU, hx⟩
    have hfib := geometricallyConnected_fibre G p (isConnected_fibre G U hj p hsub)
    refine GlobalTheory.GenericSplit.geometricallyConnected_snd_of_range_subset G.hom
      ((Sp R).fromSpecResidueField p) (spMap ψ) ?_ hfib
    rw [Scheme.range_fromSpecResidueField]
    rintro _ ⟨y, rfl⟩
    show spMap ψ y = p
    rw [Subsingleton.elim (α := PrimeSpectrum F) y default]

end GlobalTheory.SpreadConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeometricallyConnectedFibresOfGenStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_geometricallyConnected_fibres_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → QuasiCompact G.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → GeometricallyConnected (pullback.snd G.hom (spMap e)) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → GeometricallyConnected (pullback.snd G.hom (spMap ψ)) := by
  first | exact @GlobalTheory.SpreadConn.geometricallyConnected_of_generic | exact GlobalTheory.SpreadConn.geometricallyConnected_of_generic | (intros; apply GlobalTheory.SpreadConn.geometricallyConnected_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeInt
namespace GlobalTheory

theorem isJacobsonRing_integers : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem closedPt_of_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  intro R _ _ _ f hf
  haveI := isJacobsonRing_integers
  let S := Localization.Away f
  have hinj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  haveI : Nontrivial S := hinj.nontrivial
  haveI : Algebra.FiniteType R S := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S
  haveI : Algebra.FiniteType ℤ S := Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  obtain ⟨n, hn⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ n) := Ideal.Quotient.field n
  haveI : Algebra.FiniteType ℤ (S ⧸ n) := inferInstance
  haveI hfin := finite_of_finite_type_of_isJacobsonRing ℤ (S ⧸ n)
  have hZ : (algebraMap ℤ (S ⧸ n)).IsIntegral := fun x => IsIntegral.of_finite ℤ x
  let ψ : R →+* S ⧸ n := (Ideal.Quotient.mk n).comp (algebraMap R S)
  have hcomp : ψ.comp (Int.castRingHom R) = algebraMap ℤ (S ⧸ n) := RingHom.ext_int _ _
  have hψ : ψ.IsIntegral := RingHom.IsIntegral.tower_top (Int.castRingHom R) ψ (hcomp ▸ hZ)
  haveI hbot : (⊥ : Ideal (S ⧸ n)).IsMaximal := Ideal.bot_isMaximal
  let M : Ideal R := (⊥ : Ideal (S ⧸ n)).comap ψ
  have hM : M.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ψ hψ ⊥
  refine ⟨M, hM, ?_, ?_⟩
  · intro hfM
    have h0 : ψ f = 0 := by simpa [M] using hfM
    have hu : IsUnit (algebraMap R S f) := IsLocalization.Away.algebraMap_isUnit f
    have hu' : IsUnit (ψ f) := hu.map (Ideal.Quotient.mk n)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · have hMZ : (M.comap (Int.castRingHom R)).IsMaximal := by
      have : M.comap (Int.castRingHom R) = (⊥ : Ideal (S ⧸ n)).comap (algebraMap ℤ (S ⧸ n)) := by
        rw [← hcomp, ← Ideal.comap_comap]
      rw [this]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ hZ ⊥
    obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (M.comap (Int.castRingHom R))
    change _ = Ideal.span {a} at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact Ring.ne_bot_of_isMaximal_of_not_isField hMZ Int.not_isField ha
    have hpr : Prime a := by
      rw [← Ideal.span_singleton_prime ha0, ← ha]
      exact hMZ.isPrime
    refine ⟨a.natAbs, Int.prime_iff_natAbs_prime.1 hpr, ?_⟩
    have hmem : (a.natAbs : ℤ) ∈ M.comap (Int.castRingHom R) := by
      rw [ha, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    have h2 := Ideal.mem_comap.1 hmem
    simpa only [eq_intCast, Int.cast_natCast] using h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  first | exact @GlobalTheory.closedPt_of_finiteType_int | exact GlobalTheory.closedPt_of_finiteType_int | (intros; apply GlobalTheory.closedPt_of_finiteType_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurve
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CharPSpec

theorem spMap_comp_eq' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C}
    {h : A →+* C} (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem exists_charP_specialization : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  intro k _ _ _ G _ hG g hg m hm s hs P hP u a b hu hab
  classical
  have hm0 : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨R, G₁, _, hfg, hmR, hcomm, hsm, hsep, hqc, hgc, hrd, ⟨s₁, hcard, hs₁, hdist⟩, P₁, hP₁, u₁, α, β, hα, hβ,
    hu₁, hαβ⟩ := GlobalTheory.T.exists_fg_subring_descent_group_sections_curve k G hG g hg m hm hm0 s hs P hP u a b hu hab
  haveI : Algebra.FiniteType ℤ R := hfg
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  obtain ⟨f₁, hf₁, H₁⟩ := GlobalTheory.T.exists_basicOpen_smoothOfRelativeDimension_of_generic R G₁ hsm hqc k R.subtype hinj g hrd
  obtain ⟨f₂, hf₂, H₂⟩ := GlobalTheory.T.exists_basicOpen_geometricallyConnected_fibres_of_generic R G₁ hsm hqc k R.subtype hinj hgc
  obtain ⟨f₃, hf₃, H₃⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj (s₁.image fun x => x.left)
    (by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact Over.w y)
    (by
      intro x hx y hy hxy
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
      exact hdist x' hx' y' hy' fun h => hxy (by rw [h]))
  have hsec : ∀ (c₀ : R) (hc₀ : IsUnit (Polynomial.evalRingHom c₀ P₁)),
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hc₀) ≫ u₁ ≫ G₁.hom = 𝟙 _ := by
    intro c₀ hc₀
    rw [hu₁, spMap_comp_eq' (h := RingHom.id R)]
    · show Spec.map (CommRingCat.ofHom (RingHom.id R)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    · ext r
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (Polynomial R) (Localization.Away P₁),
        IsLocalization.Away.lift_eq]
      simp
  obtain ⟨f₄, hf₄, H₄⟩ := GlobalTheory.T.exists_basicOpen_sections_distinct_in_fibres R G₁ hsep k R.subtype hinj
    {spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁,
      spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁}
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [Category.assoc]; exact hsec α hα
      · rw [Finset.mem_singleton.mp hx, Category.assoc]; exact hsec β hβ)
    (by
      intro x hx y hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Finset.mem_singleton.mp hy]; exact hαβ
      · rw [Finset.mem_singleton.mp hx]; exact Ne.symm hαβ
      · rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy] at hxy; exact absurd rfl hxy)
  have hlc : R.subtype P₁.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP₁
  set f := f₁ * f₂ * f₃ * f₄ * P₁.leadingCoeff with hfdef
  have hf : f ≠ 0 := by
    intro h
    have := congrArg R.subtype h
    rw [map_zero, hfdef] at this
    simp only [map_mul] at this
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃) hf₄) hlc) this
  obtain ⟨M, hM, hfM, p, hp, hpM⟩ := GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int R f hf
  letI := Ideal.Quotient.field M
  let ψ : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) _).comp (Ideal.Quotient.mk M)
  have hψ : ∀ r, r ∉ M → IsUnit (ψ r) := by
    intro r hr
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, map_ne_zero_iff _ (algebraMap (R ⧸ M) _).injective]
    exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hu := hψ f hfM
  simp only [hfdef, map_mul, IsUnit.mul_iff] at hu
  obtain ⟨⟨⟨⟨u1, u2⟩, u3⟩, u4⟩, u5⟩ := hu
  haveI : Fact p.Prime := ⟨hp⟩
  have hpF : CharP (AlgebraicClosure (R ⧸ M)) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast ψ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero]
  refine ⟨AlgebraicClosure (R ⧸ M), inferInstance, inferInstance, p, inferInstance, hpF,
    (Over.pullback (spMap ψ)).obj G₁, inferInstance, ?_, H₁ _ ψ u1, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, ?_, ?_, ?_, H₂ _ ψ u2⟩
    · show Smooth (pullback.snd _ _); infer_instance
    · show IsSeparated (pullback.snd _ _); infer_instance
    · show QuasiCompact (pullback.snd _ _); infer_instance
  · rw [← map_natCast ψ]
    exact (hmR.map ψ).ne_zero
  · refine ⟨s₁.image (GlobalTheory.IsogRed.sec (spMap ψ)), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [← GlobalTheory.IsogRed.sec_pow, hs₁ y hy]
      simpa using (GlobalTheory.IsogRed.sec_pow (spMap ψ) y 0).trans (pow_zero _)
    · rw [← hcard]
      refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
      by_contra hne
      have e := congrArg (fun z => z.left ≫ pullback.fst G₁.hom (spMap ψ)) hxy
      simp only [GlobalTheory.IsogRed.sec_left] at e
      exact H₃ _ ψ u3 x.left (Finset.mem_image_of_mem _ hx) y.left (Finset.mem_image_of_mem _ hy)
        (fun h => hne (Over.OverMorphism.ext h)) e
  · exact GlobalTheory.T.curve_baseChange_two_distinct_points_of_field R _ ψ G₁ P₁ u₁ α β hα hβ hu₁ u5
      (H₄ _ ψ u4 _ (Finset.mem_insert_self _ _) _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (fun h => hαβ (by rw [h])))

end GlobalTheory.CharPSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharPSpecialisationSmoothCommGroupCurveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (k' : Type) (_ : Field k') (_ : IsAlgClosed k') (p : ℕ) (_ : Fact p.Prime) (_ : CharP k' p) (G' : Over (Sp k')) (_ : GrpObj G'), GlobalTheory.SS.SmConn G' ∧ SmoothOfRelativeDimension g G'.hom ∧ (m : k') ≠ 0 ∧ (∃ s' : Finset (𝟙_ (Over (Sp k')) ⟶ G'), (∀ x ∈ s', x ^ m = 1) ∧ s'.card = s.card) ∧ ∃ (P' : Polynomial k') (_ : P' ≠ 0) (u' : Sp (Localization.Away P') ⟶ G'.left) (a' b' : Localization.Away P' →ₐ[k'] k'), u' ≫ G'.hom = spMap (algebraMap k' (Localization.Away P')) ∧ spMap a'.toRingHom ≫ u' ≠ spMap b'.toRingHom ≫ u' := by
  first | exact @GlobalTheory.CharPSpec.exists_charP_specialization | exact GlobalTheory.CharPSpec.exists_charP_specialization | (intros; apply GlobalTheory.CharPSpec.exists_charP_specialization <;> assumption)
end
