module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumThetaGeneratorChartRatio
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaConstantUniformisedChartFibreEqFamilyConsta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieBasisExpCoordsDetBoundedAlongArc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibre
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreKeyTheta

variable {X : Scheme.{0}}

theorem toStk_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (z : Sp ℂ) (h : x z ∈ U) (a : Γ(X, U)) :
    toStk z (valAt' x U a) = gs x z U a := by
  rw [valAt', dite_eq_left ((top_le_iff_mem x U z).2 h), valAt, gs_eq x z U h]
  show ((Sp ℂ).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem cst_id (z : Sp ℂ) (a : ℂ) : cst (𝟙 (Sp ℂ)) z a = toStk z a := by
  rw [cst, gs_eq (𝟙 (Sp ℂ)) z ⊤ trivial]
  rfl

def isoSymm {A B : LB X} (w : LB.Iso A B) : LB.Iso B A :=
  ⟨fun p => (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem isoSymm_isGen {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : (isoSymm w).IsGen := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  intro p q
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

end GlobalTheory.FibreKeyTheta


open GlobalTheory.FibreKeyTheta in
theorem GlobalTheory.FibreKeyTheta.th_isFn_const_mul : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  intro x S G _ L y Φ g u w θ fr s hL hΦ hw hθ hfr hu hs
  classical
  let km : x.P.A.left ⟶ pullback G.hom y := pullback.lift Φ x.P.A.hom hΦ.w
  have km1 : km ≫ pullback.fst G.hom y = Φ := pullback.lift_fst _ _ _
  have km2 : km ≫ pullback.snd G.hom y = x.P.A.hom := pullback.lift_snd _ _ _
  have le : ∀ j : L.ι, Φ ⁻¹ᵁ L.U j ≤ km ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U (fun _ => j) := fun j p hp =>
    mem_pull.2 ((congrArg (fun e => e p ∈ L.U j) km1).mpr hp)
  let σ : ∀ j : L.ι, Γ(x.P.A.left, Φ ⁻¹ᵁ L.U j) := fun j => (km.appLE _ _ (le j)).hom (s.f (fun _ => j))
  have hσv : ∀ {Z : Scheme.{0}} (r : Z ⟶ x.P.A.left) (z : Z) (j : L.ι), Φ (r z) ∈ L.U j →
      gs r z _ (σ j) = gs (r ≫ km) z _ (s.f (fun _ => j)) := fun r z j h =>
    gs_appLE km _ _ (le j) r z h _
  have hσ : ∀ (p : x.P.A.left) j j', Φ p ∈ L.U j → Φ p ∈ L.U j' →
      gs (𝟙 _) p _ (σ j) = (gm Φ p (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 _) p _ (σ j') := by
    intro p j j' h h'
    rw [hσv _ p j h, hσv _ p j' h', Category.id_comp]
    refine (sec_trans s km p (le j h) (le j' h')).trans ?_
    congr 2
    simp [trF, km1]
  have hwD : PGen (isoSymm w) := (isGen_iff _).1 (isoSymm_isGen w hw)
  obtain ⟨s', hs'⟩ := sec_down hwD hL x.P.isLB σ hσ
  have refl : LBIso x.P.L (x.P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull x.P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 x.P.A.left) x.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  obtain ⟨a, ha, -⟩ := GlobalTheory.SectionBaseChange.generates GlobalTheory.allSixLaws.1.secBaseChange x.P (t := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) x.P.isLB refl x.th x.th_ne s'
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := ⟨(⊥ : PrimeSpectrum ℂ)⟩
  have key : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i →
      a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i) = θ z * u.fr i z := by
    intro i z hi
    have hri : (u.ex z).left pt ∈ x.P.L.U i := (top_le_iff_mem _ _ pt).1 hi
    obtain ⟨j, hj⟩ := exists_chart hL (Φ ((u.ex z).left pt))
    have hj' : ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j := (top_le_iff_mem _ _ pt).2 hj
    have hr0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := by simpa using Over.w (u.ex z)
    have hr1 : ((u.ex z).left ≫ km) ≫ pullback.snd G.hom y = 𝟙 _ := by rw [Category.assoc, km2, hr0]
    have e1 := hs j z ((u.ex z).left ≫ km) (by rw [Category.assoc, km1]) hr1 hj'
    have hm : (u.ex z).left pt ∈ x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j) := ⟨hri, mem_pull.2 hj⟩
    have e2 := hu i (fun _ => j) z ((top_le_iff_mem _ _ pt).2 hm)
    have e3 := hs' (Sp ℂ) (u.ex z).left pt j i hj hri
    rw [hσv _ pt j hj, ← toStk_valAt' ((u.ex z).left ≫ km) _ pt (le j hj), e1, ha i, gs_mul _ pt _ hri, gs_constFn _ _ _ pt hri,
      hr0] at e3
    erw [cst_id] at e3
    rw [← toStk_valAt' _ _ pt hri] at e3
    have hm' : (u.ex z).left pt ∈ (L.pull Φ).U (fun _ => j) ⊓ x.P.L.U i := ⟨mem_pull.2 hj, hri⟩
    have gwv : gw (isoSymm w) (u.ex z).left pt j i =
        (gm (u.ex z).left pt (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)))⁻¹ :=
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ pt _ hm' _))
    rw [gwv, Units.eq_inv_mul_iff_mul_eq] at e3
    have e3' : toStk pt (valAt' (u.ex z).left (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)).val *
        (θ z * fr j z)) = toStk pt (a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i)) := by
      rw [map_mul, map_mul (toStk pt) a]
      erw [toStk_valAt' _ _ pt hm, gs_unit _ pt _ hm]
      exact e3
    have e4 := (toStk pt).injective e3'
    rw [e2, ← e4]
    ring
  obtain ⟨z0, hz0⟩ := hθ
  obtain ⟨i0, hi0⟩ := exists_chart x.P.isLB ((u.ex z0).left pt)
  have hi0' : ⊤ ≤ (u.ex z0).left ⁻¹ᵁ x.P.L.U i0 := (top_le_iff_mem _ _ pt).2 hi0
  have ha0 : a ≠ 0 := by
    intro h0
    have e := key i0 z0 hi0'
    rw [h0, zero_mul] at e
    exact mul_ne_zero hz0 (u.fr_ne i0 z0 hi0') e.symm
  refine ⟨a⁻¹, fun i z hi => ?_⟩
  have e := key i z hi
  show _ = a⁻¹ * θ z * u.fr i z
  rw [mul_assoc, ← e, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  first | exact @GlobalTheory.FibreKeyTheta.th_isFn_const_mul | exact GlobalTheory.FibreKeyTheta.th_isFn_const_mul | (intros; apply GlobalTheory.FibreKeyTheta.th_isFn_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenericFibrePoint

theorem fibre_map_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y yF x φ hgp hL
  have hsq : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hgp.1.w, Category.assoc]; rfl
  let φ' : x.P.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift φ (x.P.A.hom ≫ yF) hsq
  have h1 : φ' ≫ Y.m.φ = φ := Y.m.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF := Y.m.cart.1.lift_snd _ _ _
  have hn : IsGrpPullback x.P.A Y.t.G (yF ≫ (Y.jQ ≫ pullback.fst _ _)) (φ' ≫ Y.m.φ) := by
    rw [h1]; exact hgp
  have hc : IsGrpPullback x.P.A Y.oF.t.G yF φ' := IsGrpPullback.cancel Y.m.cart hn h2
  refine ⟨φ', h1, h2, hc.comp Y.m0.toSABMap.cart, ?_⟩
  obtain ⟨w, hw, -⟩ := Y.m.lin
  obtain ⟨w0, hw0, -⟩ := Y.m0.toSABMap.lin
  have k : LBIso (Y.t.PP.L.pull Y.m.φ) (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) :=
    LBIso.trans (pull_isLB Y.t.PP.isLB _) Y.oF.t.PP.isLB (pull_isLB Xo.univ.t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩) ⟨w0, hw0⟩
  have k' : LBIso (Y.t.PP.L.pull φ) (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) :=
    GlobalTheory.Spread.lbIso_pull_comp φ' h1.symm rfl k
  exact LBIso.trans x.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL k'

end GlobalTheory.GenericFibrePoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesianStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_group_factors_universal_cartesian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  first | exact @GlobalTheory.GenericFibrePoint.fibre_map_univ | exact GlobalTheory.GenericFibrePoint.fibre_map_univ | (intros; apply GlobalTheory.GenericFibrePoint.fibre_map_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigRescale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem exists_rescale_rig : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  intro A _ L g u rig hL hr
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp [eSec]
  obtain ⟨j₀, hj₀⟩ := exists_chart_at hL (u.ex 0).left
  have hj₀' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U (fun _ => j₀) := by
    exact (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) (fun _ => j₀)).2 (by rw [Category.id_comp, ← h0]; exact hj₀)
  have hr₀ := valAt'_unit_ne_zero _ hj₀' (rig.s (fun _ => j₀))
  have hf₀ : u.fr j₀ 0 ≠ 0 := u.fr_ne j₀ 0 hj₀
  set r₀ := valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U (fun _ => j₀)) (rig.s (fun _ => j₀)).val with hr₀def
  let u' : HolUnif A L g :=
    { u with
      fr := fun i z => r₀ / u.fr j₀ 0 * u.fr i z
      fr_hol := fun i => (u.fr_hol i).const_mul _
      fr_ne := fun i z h => mul_ne_zero (div_ne_zero hr₀ hf₀) (u.fr_ne i z h)
      fr_compat := fun i j z h => by
        show r₀ / u.fr j₀ 0 * u.fr i z = _ * (r₀ / u.fr j₀ 0 * u.fr j z)
        rw [u.fr_compat i j z h]; ring }
  refine ⟨u', r₀ / u.fr j₀ 0, div_ne_zero hr₀ hf₀, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro j hj
  have hj1 : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U j := fun p _ => hj trivial
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U j ⊓ (L.pull (eSec A)).U (fun _ => j₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hj1, hj₀'⟩
  have hz : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U j₀) := by
    rw [top_le_preimage_inf, h0]
    exact ⟨by simpa only [Category.id_comp] using (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) j).1 hj1, by rw [← h0]; exact hj₀⟩
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr j (fun _ => j₀))
  simp only [Units.val_mul] at e
  rw [valAt'_mul] at e
  have e1 := (valAt'_res _ inf_le_left _ hm).symm.trans (e.trans (congrArg _ (valAt'_res _ inf_le_right _ hm)))
  have hg := val_pull_g L (eSec A) (𝟙 (Sp ℂ)) j (fun _ => j₀) hm
  rw [Category.id_comp] at hg
  have hc := u.fr_compat (j PUnit.unit) j₀ 0 hz
  rw [h0] at hc
  show r₀ / u.fr j₀ 0 * u.fr (j PUnit.unit) 0 = _
  rw [e1, hg, hc, ← hr₀def]
  field_simp

end GlobalTheory.RigRescale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_uniformisation_rigidification : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  first | exact @GlobalTheory.RigRescale.exists_rescale_rig | exact GlobalTheory.RigRescale.exists_rescale_rig | (intros; apply GlobalTheory.RigRescale.exists_rescale_rig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultiple
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

open GlobalTheory GlobalTheory.OrthoMetric GlobalTheory.ArchMetricCompare

theorem exists_thetaChar_mulVec_ne {g : ℕ} (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hh : IsUnit h.det) : ∃ z, thetaChar τ c₁ c₂ (h.mulVec z) ≠ 0 := by
  have re : ∀ c : Fin g → ℂ, (∀ k, c k = 0 ∨ c k = 1 / 2) → (fun i => (((c i).re : ℝ) : ℂ)) = c := by
    intro c hc
    funext i
    rcases hc i with e | e <;> rw [e] <;> norm_num
  have hne := GlobalTheory.CanTh.thetaChar_ne_zero hs hp (fun i => (c₁ i).re) (fun i => (c₂ i).re)
  rw [re c₁ h₁, re c₂ h₂] at hne
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 hne
  refine ⟨h⁻¹.mulVec z₀, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hh, Matrix.one_mulVec]
  exact hz₀

theorem exists_unif_of_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hσ hty hP hover hgen hM
  have hh : IsUnit Θ.h.det := by
    refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
    ext i k
    have e := congrFun (Θ.per 0 k).1 i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
  refine ⟨Ha.T, fun w hw yF hy₁ hy₂ hz x φ hx => ?_⟩
  have hPer := Ha.period w hw
  obtain ⟨fr, hf₁, hf₂, hf₃, -, s, hs⟩ := Θ.frame w hw
  obtain ⟨-, wx, -, hgp, hwx, -, -, -⟩ := hx
  obtain ⟨φ', hφ₁, hφ₂, hgp', hiso⟩ := GlobalTheory.T.genericFibre_group_factors_universal_cartesian E H Dw l Xo c _ _ Y yF x φ hgp ⟨wx, hwx⟩
  rw [hy₁] at hgp'
  have hL := Xo.univ.t.PP.isLB
  have hM' := LB.isLB_pull hL (φ' ≫ Y.m0.toSABMap.φ)
  let u₁ := fibreUnif hgp' (Fu.ex Ha.i (Ha.Pw w)) (Ha.Pw w).range fr (Fu.ex_add _ _ hPer) (Fu.ex_onto _ _ hPer)
    (Fu.ex_ker _ _ hPer) hPer.2.2.1 hPer.2.2.2.1 (isHolTo_exp Fu Ha.i hPer) hf₁ hf₂ hf₃
  obtain ⟨wI, hwI⟩ := LBIso.symm hiso
  let u₂ := carry u₁ hM' x.P.isLB hwI
  have hex₁ : ∀ z, (u₂.ex z).left ≫ φ' ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left := fun z =>
    liftPt_comp hgp' _
  obtain hθ : ∃ z, thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) ≠ 0 :=
    exists_thetaChar_mulVec_ne _ _ _ _ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ hh

  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.keySection_eq_const_mul_thetaFunction_fibre x _ Xo.univ.t.G Xo.univ.t.PP.L (Fu.u Ha.i (Ha.Pw w)) (φ' ≫ Y.m0.toSABMap.φ) g u₂ wI
    (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr s hL hgp'.1 hwI hθ
    (fun j z hj => hf₂ j z (by rwa [hex₁] at hj))
    (fun k j z hkj => by
      obtain ⟨hk, hj⟩ := (top_le_preimage_inf _ _ _).1 hkj
      exact carry_fr u₁ hM' x.P.isLB hwI k j z hk hj)
    (fun j z p hp₁ hp₂ hj => hs j z p (hp₁.trans (hex₁ z)) hp₂ (by rwa [hex₁] at hj))
  obtain ⟨u₃, lam, hlam, hex, hΛ, hR, hfr⟩ := GlobalTheory.T.exists_rescale_uniformisation_rigidification x.P.A x.P.L g u₂ x.rig x.P.isLB x.rig_gen
  have hFn : u₃.IsFn x.th fun z => c₁ / lam * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) := by
    intro i z hi
    rw [hex] at hi ⊢
    rw [hc₁ i z hi, hfr]
    field_simp
  have hdim : g = x.P.g := by
    obtain ⟨u₀, -, -, -, -, -, hv, hw', -⟩ := thetaUnifAV_all x.P x.rig x.rig_gen
    obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g g u₀ hv hw' u₃.ex u₃.ex_add
      (fun U f => by simpa only [Set.mem_univ, true_and] using u₃.hol U f)
    exact AHWeil.dim_eq u₃ u₀ F hF
  refine ⟨hdim.symm, u₃, c₁ / lam, hR, fun z => ⟨(u₃.ex z).left ≫ φ', ?_, ?_, ?_⟩, hΛ, hFn⟩
  · rw [Category.assoc, hex]
    exact hex₁ z
  · rw [Category.assoc, ← Category.assoc φ', hφ₂, Category.assoc, ← Category.assoc (u₃.ex z).left, Over.w (u₃.ex z),
      hy₂]
    exact Category.id_comp _
  · rw [Category.assoc, hφ₁]

end GlobalTheory.ArcNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArcFibreUniformisationThetaMultipleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_ : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) := by
  first | exact @GlobalTheory.ArcNormal.exists_unif_of_arc | exact GlobalTheory.ArcNormal.exists_unif_of_arc | (intros; apply GlobalTheory.ArcNormal.exists_unif_of_arc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArc
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArc
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ArcNormal

theorem exists_chart_theta_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ (κ : ℂ) (r : PowerSeries ℂ) (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ)), κ ≠ 0 ∧ PowerSeries.constantCoeff r ≠ 0 ∧ IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ ∧ IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ ∧ ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧ ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u Ha.i (Ha.Pw w)) (fun z => (Fu.ex Ha.i (Ha.Pw w) z).left) (fun z => thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) fr → ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι), x ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) → ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) → valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (M.θ j) = valAt' x _ (w₁.s (fun _ => j, k)).val * ((κ * rw) * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * fr j₀ z) := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hL2 := GlobalTheory.abelianSchemeLaws_all.2
  obtain ⟨hA, hB⟩ := GlobalTheory.theta_generates_along_arc hL.globalFns hL.secBaseChange Y a χ W
  have hw0 : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I : ℂ).im := by simp
  have hne : ∃ j, th.f j ≠ 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hs, hp⟩ := Θ.pos _ hw0
    have h7 := (GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic g Θ.S (Θ.τ ((Ha.T + 1 : ℝ) * Complex.I)) Θ.c₁ Θ.c₂ hs hp Θ.half₁ Θ.half₂ Θ.c₁_S).1
    apply h7
    funext v
    set w := ((Ha.T + 1 : ℝ) * Complex.I : ℂ) with hwdef
    have hz : Θ.h.mulVec (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = v := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, (Θ.per w _).1]
      exact (pi_eq_sum_univ' v).symm
    rw [← hz]
    generalize (∑ k, v k • Ha.Pw w (Θ.bas (Pi.single (.inl k) 1))) = z
    obtain ⟨fr, -, n, -, -, hv⟩ := Θ.onB w hw0
    obtain ⟨j, hj⟩ := exists_chart a.D₀.P.isLB ((show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (IsLocalRing.closedPoint ℂ))
    have hU : ⊤ ≤ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) ⁻¹ᵁ a.D₀.P.L.U j := fun q _ =>
      (Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) q) ▸ hj
    have e := hv j z hU
    have e0 : valAt' (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) (a.D₀.P.L.U j) (th.f j) = 0 := by
      rw [hc j]
      exact (dif_pos hU).trans ((congrArg _ (map_zero _)).trans (map_zero _))
    rw [e0] at e
    have := (mul_eq_zero.1 e.symm).resolve_right (n j z hU)
    exact (mul_eq_zero.1 this).resolve_left Θ.κ_ne
  have hth : GlobalTheory.ArcQ.ThNZ th := ((GlobalTheory.ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ th).1).1 hne
  obtain ⟨⟨t, ht, -⟩, hnz⟩ := hB th
  obtain ⟨σ0, fam, hfam0, hexp, -, -, -, -, ⟨w₂, hw₂⟩, hrest⟩ := hA t (hnz t ht hth _)
  have hpull : GlobalTheory.ThetaUnit.IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) := hfam0 ▸ ht
  obtain ⟨-, hr⟩ := (hrest w₂ hw₂.1).2 hPI
  obtain ⟨r, hr⟩ := hr M.U M.θ hM ⟨M.θ_mem, M.gen⟩
  obtain ⟨w₀, h₀⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m0.toSABMap
  obtain ⟨w₁, h₁⟩ := GlobalTheory.Reg.ChartInhab.exists_rigIso Y.m
  obtain ⟨fr₀, hfr₀⟩ := Θ.frame _ hw0
  obtain ⟨κ, hκ, -, -, hmain⟩ := Ha.theta th σ0 fam Θ.bas Θ.S Θ.h Θ.τ Θ.c₁ Θ.c₂ w₂ w₁ w₀ hne hexp hpull Θ.sympl Θ.ker Θ.per Θ.half₁ Θ.half₂ hw₂ h₁ h₀ ⟨_, fr₀, hw0, hfr₀⟩
  obtain ⟨T', hT'⟩ := hmain M.U M.θ r.val hM M.θ_mem hr
  refine ⟨κ, r.val, w₀, w₁, hκ, ?_, h₀, h₁, T', hT'⟩
  exact ((PowerSeries.isUnit_iff_constantCoeff).1 r.isUnit).ne_zero

theorem exists_bounds_of_sumsAt : ∀ (κ : ℂ), κ ≠ 0 → ∀ r : PowerSeries ℂ, PowerSeries.constantCoeff r ≠ 0 → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ rw : ℂ, SumsAt r w rw → C⁻¹ ≤ ‖κ * rw‖ ∧ ‖κ * rw‖ ≤ C := by
  intro κ hκ r hr0
  by_cases hex : ∃ w₀ rw₀, SumsAt r w₀ rw₀
  swap
  · exact ⟨0, 1, one_pos, fun w _ rw h => (hex ⟨w, rw, h⟩).elim⟩
  obtain ⟨w₀, rw₀, h₀⟩ := hex
  have hq₀ : 0 < ‖eTwoPi w₀‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖PowerSeries.coeff n r * eTwoPi w₀ ^ n‖ ≤ B := by
    obtain ⟨B, hB⟩ := h₀.summable.tendsto_atTop_zero.norm.bddAbove_range
    exact ⟨B, fun n => hB ⟨n, rfl⟩⟩
  have ha₀ : 0 < ‖PowerSeries.constantCoeff r‖ := norm_pos_iff.2 hr0
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set A := ‖PowerSeries.constantCoeff r‖ with hA
  set B' := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  set t : ℝ := min (1 / 2) (A / (4 * B')) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos ha₀ (by linarith))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have htB : t ≤ A / (4 * B') := min_le_right _ _
  have htB' : 4 * B' * t ≤ A := by
    have := mul_le_mul_of_nonneg_left htB (by linarith : (0:ℝ) ≤ 4 * B')
    rwa [mul_div_cancel₀ _ (by linarith : (4 * B' : ℝ) ≠ 0)] at this
  refine ⟨-Real.log (t * ‖eTwoPi w₀‖) / (2 * Real.pi), max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)),
    lt_max_of_lt_left (by positivity), fun w hw rw hrw => ?_⟩
  have hqn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    simp [eTwoPi, Complex.norm_exp]
  have hq : ‖eTwoPi w‖ ≤ t * ‖eTwoPi w₀‖ := by
    rw [hqn]
    have hpos : 0 < t * ‖eTwoPi w₀‖ := mul_pos ht0 hq₀
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).1 hw
    linarith
  have hf := (hasSum_nat_add_iff' 1).2 hrw
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
  have hg : HasSum (fun n : ℕ => B' * t * t ^ n) (B' * t * (1 - t)⁻¹) :=
    (hasSum_geometric_of_lt_one ht0.le (by linarith)).mul_left (B' * t)
  have hle : ‖rw - PowerSeries.constantCoeff r‖ ≤ B' * t * (1 - t)⁻¹ := by
    refine hf.norm_le_of_bounded hg fun n => ?_
    have h1 : ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1) ≤ B' := by
      have := hB (n + 1)
      rw [norm_mul, norm_pow] at this
      exact this.trans (le_max_left _ _)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w‖ ^ (n + 1)
        ≤ ‖PowerSeries.coeff (n + 1) r‖ * (t * ‖eTwoPi w₀‖) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (norm_nonneg _)
      _ = (‖PowerSeries.coeff (n + 1) r‖ * ‖eTwoPi w₀‖ ^ (n + 1)) * t ^ (n + 1) := by ring
      _ ≤ B' * t ^ (n + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = B' * t * t ^ n := by ring
  have h2 : B' * t * (1 - t)⁻¹ ≤ A / 2 := by
    have h1t : 0 < 1 - t := by linarith
    rw [← div_eq_mul_inv, div_le_iff₀ h1t]
    nlinarith
  have hlo : A / 2 ≤ ‖rw‖ := by
    have := norm_sub_norm_le (PowerSeries.constantCoeff r) rw
    rw [norm_sub_rev] at this
    linarith
  have hhi : ‖rw‖ ≤ 3 / 2 * A := by
    have := norm_sub_norm_le rw (PowerSeries.constantCoeff r)
    linarith
  rw [norm_mul]
  constructor
  · have hx : 0 < ‖κ‖ * A := mul_pos hκ' ha₀
    calc (max (3 / 2 * (‖κ‖ * A)) (2 / (‖κ‖ * A)))⁻¹ ≤ (2 / (‖κ‖ * A))⁻¹ :=
          inv_anti₀ (by positivity) (le_max_right _ _)
      _ = ‖κ‖ * (A / 2) := by field_simp
      _ ≤ ‖κ‖ * ‖rw‖ := mul_le_mul_of_nonneg_left hlo hκ'.le
  · calc ‖κ‖ * ‖rw‖ ≤ ‖κ‖ * (3 / 2 * A) := mul_le_mul_of_nonneg_left hhi hκ'.le
      _ = 3 / 2 * (‖κ‖ * A) := by ring
      _ ≤ _ := le_max_left _ _

theorem theta_const_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨κ, r, w₀, w₁, hκ, hr0, h₀, h₁, T', hT'⟩ := exists_chart_theta_unit E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM
  obtain ⟨T₃, C, hC, hb⟩ := exists_bounds_of_sumsAt κ hκ r hr0
  refine ⟨max T' (max Ha.T T₃), C, hC, fun w hw yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨rw, hrw, hval⟩ := hT' w hw.1
  obtain rfl := GlobalTheory.T.thetaConstant_uniformisedChartFibre_eq_familyConstant E H Dw l Xo c σ V Y a χ W g ty Fu Ha th Θ M hgood hty hPI hχ hrng hM w hw.2.1 w₀ w₁ h₀ h₁ (κ * rw) hval yF e₁ e₂ hz x φ hx u c₀ hrig hfib hfn
  exact hb w hw.2.2 rw hrw

end GlobalTheory.ArcNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArcStatement
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoefficient_bounded_along_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.theta_const_bounded | exact GlobalTheory.ArcNormal.theta_const_bounded | (intros; apply GlobalTheory.ArcNormal.theta_const_bounded <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

theorem sp_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem mem_of_pow_mem' {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem exists_values' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  let inc := (IntermediateField.inclusion c.le).toRingHom
  refine ⟨⟨inc (baseKA l).ρ, mem_of_pow_mem' V two_ne_zero ?_⟩,
    ⟨inc (baseKA l).ζ, mem_of_pow_mem' V l.A_pos.ne' ?_⟩, rfl, rfl⟩
  · rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    exact neg_mem (natCast_mem V _)
  · rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
    exact one_mem V

theorem ratio_bounds {K D n C₂ C₃ : ℝ} (hK : 0 < K) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃) (hD₁ : C₃⁻¹ ≤ D) (hD₂ : D ≤ C₃)
    (hn₁ : C₂⁻¹ ≤ n) (hn₂ : n ≤ C₂) :
    ((K + K⁻¹) * C₃ * C₂ ^ 2)⁻¹ ≤ K * D / n ^ 2 ∧ K * D / n ^ 2 ≤ (K + K⁻¹) * C₃ * C₂ ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (inv_pos.2 hC₂) hn₁
  have hD : 0 < D := lt_of_lt_of_le (inv_pos.2 hC₃) hD₁
  have hKi : 0 < K⁻¹ := inv_pos.2 hK
  have h1 : 1 ≤ C₂ * n := by
    have := mul_le_mul_of_nonneg_left hn₁ hC₂.le
    rwa [mul_inv_cancel₀ hC₂.ne'] at this
  have h2 : 1 ≤ C₃ * D := by
    have := mul_le_mul_of_nonneg_left hD₁ hC₃.le
    rwa [mul_inv_cancel₀ hC₃.ne'] at this
  have hKK : 1 ≤ K * (K + K⁻¹) := by
    rw [mul_add, mul_inv_cancel₀ hK.ne']; nlinarith
  constructor
  · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by positivity)]
    have : n ^ 2 ≤ C₂ ^ 2 := pow_le_pow_left₀ hn.le hn₂ 2
    calc n ^ 2 ≤ C₂ ^ 2 * 1 := by simpa using this
      _ ≤ C₂ ^ 2 * ((K * (K + K⁻¹)) * (C₃ * D)) := by
          gcongr; nlinarith
      _ = (K + K⁻¹) * C₃ * C₂ ^ 2 * (K * D) := by ring
  · rw [div_le_iff₀ (by positivity)]
    have : 1 ≤ (C₂ * n) ^ 2 := one_le_pow₀ h1
    calc K * D ≤ K * C₃ * 1 := by nlinarith
      _ ≤ (K + K⁻¹) * C₃ * (C₂ * n) ^ 2 := by
          gcongr
          · linarith
      _ = (K + K⁻¹) * C₃ * C₂ ^ 2 * n ^ 2 := by ring

end GlobalTheory.ArcNormal

open scoped Matrix
namespace GlobalTheory.ArcNormal

theorem exists_normalAt_of_unif {g : ℕ} (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) {La : Type}
    [AddCommGroup La] (P : La →+ (Fin g → ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La)
    (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (c₀ : ℂ) (hu : IsUnit h.det)
    (hsymm : τ.IsSymm) (hpos : (τ.map Complex.im).PosDef) (hc : KeyPow.charHalf g c₁ c₂)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1)
    (hΛ : u.Λ = P.range.toIntSubmodule) (hR : u.IsRig x.rig)
    (hF : u.IsFn x.th fun z => c₀ * thetaChar τ c₁ c₂ (h *ᵥ z)) :
    ∃ (Wv : Fin x.P.g → Fin g → ℂ), (∀ i, u.IsDiff (Wv i) (x.v i)) ∧
      ∃ (τ' Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b' : Fin x.P.g → ℂ), KeyPow.charHalf _ a' b' ∧
        KeyPow.NormalAt x τ' Mx a' b' c₀ ∧
        ‖Mx.det‖ = (2 * Real.pi) ^ g * ‖h.det‖ * ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ := by
  subst hg
  choose Wv hW using fun i => ((GlobalTheory.LamT.existsUnique_isDiff_and_linear x u).1 _ (x.basis.1 i)).exists
  refine ⟨Wv, hW, ?_⟩
  let φ : (Fin x.P.g → ℂ) ≃L[ℂ] (Fin x.P.g → ℂ) :=
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm.toContinuousLinearEquiv
  have hφ : ∀ z, h *ᵥ φ z = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).apply_symm_apply z
  have hφ' : ∀ z, φ (h *ᵥ z) = z := fun z =>
    (Matrix.toLinearEquiv' h (Matrix.invertibleOfIsUnitDet _ hu)).symm_apply_apply z
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  clear_value φ
  let Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := (2 * Real.pi * Complex.I : ℂ) • Matrix.of fun i => h *ᵥ Wv i
  refine ⟨τ, Mx, c₁, c₂, hc, ⟨KeyNormalForm.change u φ (fun _ => 0) (differentiable_const _), hsymm, hpos, fun z => ?_,
    KeyNormalForm.isRig_change u φ _ _ rfl hR,
    KeyNormalForm.isFn_change u φ _ _ hF fun z => by simp only [hφ, Complex.exp_zero, mul_one],
    fun i => KeyNormalForm.isDiff_change u φ _ _ ?_⟩, ?_⟩
  · rw [KeyNormalForm.mem_change, hΛ]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨m, rfl⟩ := bas.surjective v
      refine ⟨fun i => m (Sum.inl i), fun i => m (Sum.inr i), ?_⟩
      rw [← hφ z, ← hv]
      exact GlobalTheory.KeyFourth.mulVec_period _ bas _ _ hn m
    · rintro ⟨m, n, rfl⟩
      refine ⟨bas (Sum.elim m n), ?_⟩
      rw [← hφ' (P _), GlobalTheory.KeyFourth.mulVec_period _ bas _ _ hn]
      rfl
  · have e₁ : (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i = h *ᵥ Wv i := by
      funext j
      simp only [Mx, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
      rw [inv_mul_cancel_left₀ hπ]
    rw [e₁, hφ']
    exact hW i
  · have e₂ : Mx = (2 * Real.pi * Complex.I : ℂ) • ((Matrix.of fun i j => Wv i j) * hᵀ) := by
      ext i j
      simp [Mx, Matrix.mulVec, Matrix.mul_apply, dotProduct, mul_comm]
    rw [e₂, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin, norm_mul, norm_mul, norm_pow]
    have : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [this]
    simp only [Fin.cast_eq_self]
    ring

end GlobalTheory.ArcNormal

namespace GlobalTheory.ArcNormal

open scoped Matrix

theorem main_of_lemmas (hFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∃ (_
    : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (c₀
    : ℂ), u.IsRig x.rig ∧ GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u ∧ u.Λ = (Ha.Pw
    w).range.toIntSubmodule ∧ u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec
    z))) (hTheta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u
    : HolUnif x.P.A x.P.L g) (c₀
    : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw
    w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec
    z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C) (hLie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ
    (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a
    : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W
    : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp
    (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th
    : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M
    : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C
    (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw
    w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ
    : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg
    : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv
    : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw
    w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → C⁻¹ ≤ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast
    hg.symm i) j).det‖ ∧ ‖(Matrix.of fun i j : Fin g => Wv (Fin.cast hg.symm i) j).det‖ ≤ C) : ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo
    : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y
    : Model Xo c V.subtype), 1 ≤ Dw.p + Dw.q → PushInvertible Y.t.G Y.t.PP.L → ∀ (a
    : ArcIn Dw l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries
    ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R :=
    ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp
    V.subtype) → (∀ x : Sp (PowerSeries
    ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ∀ M : GChart Y, ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ y : ℂ → (Sp
    ℂ ⟶ Y.X), (∀ (U : Y.X.Opens) (f : Γ(Y.X,
    U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y
    w) U f)) ∧ ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ (hz : ⊤ ≤ y w ⁻¹ᵁ M.U) (x
    : KeyIn ℂ), KeyAt M (y w) hz x → ∃ (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b'
    : Fin x.P.g → ℂ) (c₀
    : ℂ), GlobalTheory.KeyPow.charHalf _ a' b' ∧ c₀ ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ Mx a' b' c₀ ∧ C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2 ∧ ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C := by
  intro E _ _ _ H Dw l Xo c V Y hpq hP a χ hχ hover hgen M hM
  let _ : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  have : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hχ
  obtain ⟨U, hU, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H Dw l Xo c hpq
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := (Formalism.L2.PjFree.goodEmb_iff c.F.val.toRingHom).mpr rfl
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c _ _ (U _) (hU _ hσ).1
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := GlobalTheory.arcClause_closed E H Dw l Xo c _ _ Y _ a χ W Uw.g _ Uw.F hσ hty (exists_values' c V) hover hgen
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ a.D₀
    (⟨fun _ => 0, fun _ _ => by simp⟩ : a.D₀.P.L.Sec)
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c _ _ _ Y a χ W _ _ Uw.F Ha hty th hth
  have hlift : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c,
      yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧ yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom := by
    intro w hw
    refine ⟨pullback.lift (Uw.F.u Ha.i (Ha.Pw w)) (spMap c.F.val.toRingHom) ?_, pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
    rw [Uw.F.over_σ _ _ (Ha.period w hw)]
    exact (sp_comp' _ _).symm
  classical
  let y : ℂ → (Sp ℂ ⟶ Y.X) := fun w =>
    if h : ∃ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧
      yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom then h.choose ≫ Y.j
    else spMap (PowerSeries.constantCoeff (R := ℂ)) ≫ χ
  have hy : ∀ w : ℂ, Ha.T < w.im → ∃ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Uw.F.u Ha.i (Ha.Pw w) ∧
      yF ≫ pullback.snd _ _ = spMap c.F.val.toRingHom ∧ y w = yF ≫ Y.j := by
    intro w hw
    have h := hlift w hw
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  refine ⟨y, fun U f hUf => ?_, ?_⟩
  · obtain ⟨T', hT'⟩ := Ha.point U f hUf
    refine ⟨max T' Ha.T, fun w hw => ?_⟩
    obtain ⟨yF, k₁, k₂, e⟩ := hy w ((le_max_right _ _).trans_lt hw)
    rw [e]
    exact hT' w ((le_max_left _ _).trans_lt hw) yF k₁ k₂
  · obtain ⟨T₁, hF⟩ := hFib E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    obtain ⟨T₂, C₂, hC₂, hT⟩ := hTheta E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    obtain ⟨T₃, C₃, hC₃, hL⟩ := hLie E H Dw l Xo c _ V Y a χ W _ _ Uw.F Ha th Θ M hσ hty hP hover hgen hM
    have hh : IsUnit Θ.h.det := by
      refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun i k => Ha.Pw 0 (Θ.bas (Pi.single (.inl k) 1)) i) ?_
      ext i k
      have e := congrFun (Θ.per 0 k).1 i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using e
    set K : ℝ := (2 * Real.pi) ^ Uw.g * ‖Θ.h.det‖ with hKdef
    have hK : 0 < K := mul_pos (pow_pos Real.two_pi_pos _) (norm_pos_iff.2 hh.ne_zero)
    refine ⟨max Ha.T (max T₁ (max T₂ T₃)), (K + K⁻¹) * C₃ * C₂ ^ 2, by positivity, fun w hw hz x hx => ?_⟩
    have hw₀ : Ha.T < w.im := (le_max_left _ _).trans_lt hw
    have hw₁ : T₁ < w.im := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hw
    have hw₂ : T₂ < w.im := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans_lt hw
    have hw₃ : T₃ < w.im := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans_lt hw
    obtain ⟨yF, k₁, k₂, e⟩ := hy w hw₀
    have hx' : ∃ hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U, KeyAt M (yF ≫ Y.j) hz' x := by
      rw [← e]; exact ⟨hz, hx⟩
    obtain ⟨hz', φ, hφ⟩ := hx'
    obtain ⟨hg, u, c₀, hR, hA, hΛ, hFn⟩ := hF w hw₁ yF k₁ k₂ hz' x φ hφ
    obtain ⟨hc₁, hc₂⟩ := hT w hw₂ yF k₁ k₂ hz' x φ hφ u c₀ hR hA hFn
    obtain ⟨Wv, hW, τ', Mx, a', b', hab, hN, hdet⟩ := exists_normalAt_of_unif x hg u (Ha.Pw w) Θ.bas Θ.h (Θ.τ w)
      Θ.c₁ Θ.c₂ c₀ hh (Θ.pos w hw₀).1 (Θ.pos w hw₀).2 ⟨Θ.half₁, Θ.half₂⟩ (Θ.per w) hΛ hR hFn
    obtain ⟨hd₁, hd₂⟩ := hL w hw₃ yF k₁ k₂ hz' x φ hφ hg u Wv hA hW
    have hc₀ : c₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc₁
      exact absurd hc₁ (not_le.2 (inv_pos.2 hC₂))
    refine ⟨τ', Mx, a', b', c₀, hab, hc₀, hN, ?_⟩
    rw [hdet, ← hKdef]
    exact ratio_bounds hK hC₂ hC₃ hd₁ hd₂ hc₁ hc₂

end GlobalTheory.ArcNormal

namespace GlobalTheory.ArcNormal

theorem arc_normal_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), 1 ≤ Dw.p + Dw.q → PushInvertible Y.t.G Y.t.PP.L → ∀ (a : ArcIn Dw l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ∀ M : GChart Y, ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ y : ℂ → (Sp ℂ ⟶ Y.X), (∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) ∧ ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ (hz : ⊤ ≤ y w ⁻¹ᵁ M.U) (x : KeyIn ℂ), KeyAt M (y w) hz x → ∃ (τ Mx : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a' b' : Fin x.P.g → ℂ) (c₀ : ℂ), GlobalTheory.KeyPow.charHalf _ a' b' ∧ c₀ ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ Mx a' b' c₀ ∧ C⁻¹ ≤ ‖Mx.det‖ / ‖c₀‖ ^ 2 ∧ ‖Mx.det‖ / ‖c₀‖ ^ 2 ≤ C :=
  main_of_lemmas GlobalTheory.T.exists_arc_fibre_uniformisation_theta_multiple GlobalTheory.T.thetaCoefficient_bounded_along_holomorphicArc GlobalTheory.T.lieBasis_expCoords_det_bounded_along_arc

end GlobalTheory.ArcNormal
