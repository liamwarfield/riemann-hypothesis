module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsThetaShiftTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.HeatDefect

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem val_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    (val t (r ≫ h) z J).val = (r.stalkMap z).hom (val t h (r z) (fun ψ => J (r ≫ ψ))).val := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc]),
    val_of t h (r z) (fun ψ => J (r ≫ ψ)) (fun k => J (r ≫ h ≫ φ k)) (fun k => rfl)]
  have hm : (r ≫ h) z ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gs_unit _ z _ hm _).symm.trans ((gs_comp_stalk r h z _ hm _).trans (congrArg _ (gs_unit h (r z) _ hm _)))

theorem good_comp {X Z : Scheme.{0}} {L : LB X} (r : Z ⟶ Z) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => by
  have := hJ (r ≫ ψ)
  rwa [Scheme.Hom.comp_apply] at this

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem gs_scal (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (c : R) : (m.left.stalkMap z).hom (gs (𝟙 _) (m.left z) ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c)) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom c) := by
  rw [← gs_comp_stalk m.left (𝟙 _) z ⊤ trivial, Category.comp_id]
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  have e₁ := gs_pull m.left (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  have e₂ := gs_pull (𝟙 _) (DegPre.BF Q (FractionRing R)).hom z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
  rw [Over.w m] at e₁
  rw [Category.id_comp] at e₂
  exact e₁.trans e₂.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R}

theorem shiftEq_at {k : ℕ} {mu α : Q.X} {σ : Q.SecB k α} {σ₁ σ₂ : Q.SecB k (α + k • mu)} {c : R}
    (H : ShiftEq Q k mu α σ σ₁ c σ₂)
    (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left)
      (DegPre.famMult Q (FractionRing R) k mu α))
    (m : DegPre.BF Q (FractionRing R) ⟶ DegPre.BF Q (FractionRing R)) (z : (DegPre.BF Q (FractionRing R)).left)
    (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι) (hJ : Good Q.P.L z J) :
    sval σ₁ (m ≫ DegPre.prB Q (FractionRing R)).left z J =
      (val u m.left z J).val *
          sval σ (m ≫ DegPre.trF Q (FractionRing R) mu ≫ DegPre.prB Q (FractionRing R)).left z J +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom c) *
          sval σ₂ (m ≫ DegPre.prB Q (FractionRing R)).left z J := by
  have e := congrArg (m.left.stalkMap z).hom (H u hu hc (m.left z) _ (good_comp m.left z hJ))
  rw [Over.comp_left, Over.comp_left, Over.comp_left, sval_comp_stalk _ _ _ _ hJ, sval_comp_stalk _ _ _ _ hJ,
    sval_comp_stalk _ _ _ _ hJ, e, map_add, map_mul, map_mul, gs_scal]
  congr 2
  have := val_comp_stalk u (𝟙 _) m.left z hJ
  rw [Category.comp_id] at this
  exact this.symm

end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem scal_injective (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    Function.Injective (fun r : R => gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom r)) := by
  let F := FractionRing R
  let χ : F →+* (DegPre.BF Q F).left.presheaf.stalk z :=
    ((DegPre.BF Q F).left.presheaf.germ ⊤ z trivial).hom.comp
      ((fst (TF (R := R) F) Q.P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
  have hT : (DegPre.BF Q F).hom = (fst (TF (R := R) F) Q.P.A).left ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [← Over.w (fst (TF (R := R) F) Q.P.A)]
    show _ ≫ (jFK (R := R) F ≫ jK R) = _
    rw [jFK, jK, ← Spec.map_comp]
    rfl
  have key : ∀ r : R, gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q F).hom r) = χ (algebraMap R F r) := by
    intro r
    unfold ReciprocityTheory.ChartRestriction.G.Out.scal
    rw [hT, gs_eq _ z ⊤ trivial]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R F))
    have n' := congrArg (fun f => f.hom r) n
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n'
    simp only [χ, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, n']
    rfl
  intro a b hab
  have : χ (algebraMap R F a) = χ (algebraMap R F b) := (key a).symm.trans (hab.trans (key b))
  exact IsFractionRing.injective R F (χ.injective this)
end GlobalTheory.HeatDefect

namespace GlobalTheory.HeatDefect

theorem sval_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {k : ℕ} {x y : Q.X} (e : x = y)
    (he : Q.SecB k x = Q.SecB k y) (σ : Q.SecB k x) {Z : Scheme.{0}} (r : Z ⟶ Q.P.A.left) (z : Z)
    (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) : sval (cast he σ) r z J = sval σ r z J := by
  subst e; rfl

theorem tActs_cast {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R}
    {h : Heat Y.H Y.q.left Q.P.L dd D} {k : ℕ} {x y : Q.X} (e : x = y) (he : Q.SecB k x = Q.SecB k y)
    {σ σ' : Q.SecB k x} (H : TActs Y h k x σ σ') : TActs Y h k y (cast he σ) (cast he σ') := by
  subst e; exact H

theorem scal_add {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) (a b : R) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom (a + b)) =
      gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom a) +
        gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom b) := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.scal
  rw [map_add (f := _), map_add (f := _)]
  exact gs_add (𝟙 _) z ⊤ trivial _ _

theorem scal_zero {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (z : (DegPre.BF Q (FractionRing R)).left) :
    gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Q (FractionRing R)).hom 0) = 0 := by
  have := scal_add Q z 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem defect_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h c hB hD k hk mu mu' α
  obtain ⟨σ, σ₁, σ₂, he, h1, h2, h3, z, J, hJ, hs⟩ := GlobalTheory.T.exists_integral_sections_thetaShift_triple R Dd k hk mu mu' α
  have e : α + k • mu + k • mu' = α + k • (mu + mu') := by rw [smul_add, add_assoc]
  obtain ⟨σ', a1⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k α σ
  obtain ⟨σ₁', a2⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₁
  obtain ⟨σ₂', a3⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h hB k _ σ₂
  have d1 := hD k mu α σ σ' σ₁ σ₁' hk h1 a1 a2
  have d2 := hD k mu' (α + k • mu) σ₁ σ₁' σ₂ σ₂' hk h2 a2 a3
  have d3 := hD k (mu + mu') α σ σ' _ _ hk h3 a1 (tActs_cast e he a3)
  obtain ⟨⟨u1, hu1, hc1⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α
  obtain ⟨⟨u2, hu2, hc2⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu' (α + k • mu)
  obtain ⟨⟨u3, hu3, hc3⟩, -⟩ := gen_fe (D := Dd.toPre) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k (mu + mu') α
  have E1 := shiftEq_at d1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E10 := shiftEq_at h1 u1 hu1 hc1 (DegPre.trF Dd.toPre (FractionRing R) mu') z J hJ
  have E2 := shiftEq_at d2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E20 := shiftEq_at h2 u2 hu2 hc2 (𝟙 _) z J hJ
  have E3 := shiftEq_at d3 u3 hu3 hc3 (𝟙 _) z J hJ
  have E30 := shiftEq_at h3 u3 hu3 hc3 (𝟙 _) z J hJ
  simp only [Category.id_comp, scal_zero, zero_mul, add_zero] at E1 E10 E2 E20 E3 E30
  rw [sval_cast e he, sval_cast e he] at E3
  rw [sval_cast e he] at E30
  rw [← Category.assoc, UUA.trF_add, add_comm mu' mu] at E1 E10
  set s := sval σ (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set s' := sval σ' (DegPre.trF Dd.toPre (FractionRing R) (mu + mu') ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set v1 := (val u1 (DegPre.trF Dd.toPre (FractionRing R) mu').left z J).val
  set v2 := (val u2 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set v3 := (val u3 (Over.Hom.left (𝟙 (DegPre.BF Dd.toPre (FractionRing R)))) z J).val
  set p1 := sval σ₁ (DegPre.trF Dd.toPre (FractionRing R) mu' ≫ DegPre.prB Dd.toPre (FractionRing R)).left z J
  set q := sval σ₂ (DegPre.prB Dd.toPre (FractionRing R)).left z J
  set C1 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu α))
  set C2 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k mu' (α + k • mu)))
  set C3 := gs (𝟙 _) z ⊤ (ReciprocityTheory.ChartRestriction.G.Out.scal (DegPre.BF Dd.toPre (FractionRing R)).hom (c k (mu + mu') α))
  have k1 : (v2 * v1 - v3) * s = 0 := by linear_combination (-v2) * E10 - E20 + E30
  have hv' : v2 * v1 - v3 = 0 := hs.mul_left_eq_zero.mp k1
  have k2 : (C3 - (C1 + C2)) * q = 0 := by linear_combination E2 - E3 + v2 * E1 + s' * hv' - C1 * E20
  have hq : IsUnit q := by
    rw [E30]; exact (Units.isUnit _).mul hs
  have hC : C3 = C1 + C2 := sub_eq_zero.mp (hq.mul_left_eq_zero.mp k2)
  rw [← scal_add] at hC
  exact scal_injective R Dd.toPre z hC

end GlobalTheory.HeatDefect
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_period_defect_isCocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (c : ℕ → Dd.toPre.X → Dd.toPre.X → R), IsBasic Y h → HasDefect Y h c → ∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α, c k (mu + mu') α = c k mu α + c k mu' (α + k • mu) := by
  first | exact @GlobalTheory.HeatDefect.defect_cocycle | exact GlobalTheory.HeatDefect.defect_cocycle | (intros; apply GlobalTheory.HeatDefect.defect_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilOneOfTrivPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RaynaudAxis

theorem cubN_mul_pow {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (n : ℕ) :
    cubN θ n 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ n = t (a ^ n * b) * t 1 * (t (a ^ n))⁻¹ * (t b)⁻¹ := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e := h (a ^ n) a b
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ, pow_succ]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    linear_combination (norm := abel) e' + ih'

theorem cubN_of_torsion {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (N : ℕ) (ha : a ^ N = 1) :
    cubN θ N 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ N = 1 := by
  rw [cubN_mul_pow t θ h, ha, _root_.one_mul, mul_inv_cancel_right, mul_inv_cancel]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

def tV {L : RigLB G} (i : H ⟶ G) (τ : LB.Gen (L.L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => i.left) (ε := fun _ => 1) τ x.left z J

theorem prod_tt (i : H ⟶ G) {Y : Over S} (p : Y ⟶ H) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k : PUnit, h ((fun _ : PUnit => p.left ≫ i.left) k) ^ ((fun _ : PUnit => (1 : ℤ)) k) = h (p ≫ i).left := by
  rw [Fintype.prod_unique, zpow_one]; rfl

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

theorem cub_tV (hG : GlobalFnsSt) (hA : IsAbelianScheme H) (i : H ⟶ G) [IsMonHom i] {L : RigLB G}
    (c : CubicalStr G L) (τ : LB.Gen (L.L.pull i.left)) (hτ : τ.IsGen) (T : Over S) (x y u : T ⟶ H) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * tV i τ z J (x * y) * tV i τ z J (x * u) * tV i τ z J (y * u) *
        tV i τ z J 1 = tV i τ z J (x * y * u) * tV i τ z J x * tV i τ z J y * tV i τ z J u := by
  haveI := hA.comm
  have h3 := surjective_cube hG hA
  let a := x3 H 0
  let b := x3 H 1
  let d := x3 H 2
  let tt := fun p : G3 H ⟶ H => LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gt : ∀ p, (tt p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hτ _
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vt : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (tt p) σ.left z J = tV i τ z J (σ ≫ p) := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu
    (tt (a * b))) (tt (a * d))) (tt (b * d))) (tt 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (tt (a * b * d)) (tt a)) (tt b))
    (tt d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a ≫ i) (σ ≫ b ≫ i) (σ ≫ d ≫ i) * tV i τ z J (σ ≫ (a * b)) *
        tV i τ z J (σ ≫ (a * d)) * tV i τ z J (σ ≫ (b * d)) * tV i τ z J (σ ≫ 1) ∧
      val t₂ σ.left z J = tV i τ z J (σ ≫ (a * b * d)) * tV i τ z J (σ ≫ a) * tV i τ z J (σ ≫ b) *
        tV i τ z J (σ ≫ d) := fun σ z J hJ => by
    constructor
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt σ hJ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
  let e : 𝟙_ (Over S) ⟶ G3 H := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 H := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' L.isLB (fun V _ k => ?_) (G3 H).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gt _)) (gt _)) (gt _)) (gt _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gt _)
        (gt _)) (gt _)) (gt _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
        (prod_tt i (a * b * d) k) (prod_tt i a k)) (prod_tt i b k)) (prod_tt i d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
          (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k) (prod_tt i (a * b) k)) (prod_tt i (a * d) k))
          (prod_tt i (b * d) k)) (prod_tt i 1 k)).symm)
      simp only [MonObj.mul_comp, MonObj.one_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      have C := isCub_cubV c (T := 𝟙_ (Over S)) hI
      simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, e₀, e₁, e₂, MonObj.one_comp, _root_.mul_one]
      rw [C.face, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂] at this
  exact this

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis

theorem cubWeil_one_of_triv_pull : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H]
    (i : H ⟶ G), IsAbelianScheme H → IsMonHom i → ∀ (L : RigLB G) (c : CubicalStr G L), Triv (L.L.pull i.left) →
    ∀ (N : ℕ) (T : Over S) (a b : T ⟶ H), a ^ N = 1 → b ^ N = 1 → CubWeil c N (a ≫ i) (b ≫ i) 1 := by
  intro S G H _ _ _ i hA hi L c ⟨τ, hτ⟩ N T a b ha hb
  haveI := hA.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine ⟨by rw [← MonObj.pow_comp, ha, MonObj.one_comp], by rw [← MonObj.pow_comp, hb, MonObj.one_comp],
    fun z J hJ => ?_⟩
  let θ : (T ⟶ H) → (T ⟶ H) → (T ⟶ H) → (T.left.presheaf.stalk z)ˣ :=
    fun p q w => cubV c z J (p ≫ i) (q ≫ i) (w ≫ i)
  have h := cub_tV hG hA i c τ hτ T (z := z) (J := J) (hJ := hJ)
  have tr : ∀ p q : T ⟶ H, cubN (cubV c z J) N 1 (p ≫ i) (q ≫ i) = cubN θ N 1 p q := fun p q =>
    Finset.prod_congr rfl fun k _ => by
      simp only [θ, _root_.one_mul, MonObj.pow_comp]
  have e₁ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) a b N ha
  have e₂ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) b a N hb
  rw [mul_comm b a, mul_right_comm _ (tV i τ z J b)⁻¹] at e₂
  rw [map_one, _root_.one_mul, tr, tr]
  exact mul_right_cancel (e₁.trans e₂.symm)

end GlobalTheory.RaynaudAxis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilKernel

theorem triv_slice_of_forall_weilIs_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  intro S A _ _ P hA hL h1 h2 k _ _ p n hn a ha hpair
  have hB : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have ht2 : Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ A)) := h2
  obtain ⟨r, hr⟩ : Triv (P.pull (eSec (A ⊗ A))) := by
    have e := (AbDual.triv_ev_iff hL _ _).2 (AbDual.evc_one_right hL ht2 (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = η[A ⊗ A] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := WeilIntegral.triv_theta CubeTop.cubeTheorem hB hL
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hL t ht
  let M : RigLB (A ⊗ A) := ⟨P, r, hL, hr⟩
  have c : CubicalStr (A ⊗ A) M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hB M t' ht' hn'
  have ha' : (lift a (1 : Over.mk p ⟶ A)) ^ n = 1 := WeilIntegral.lift_pow ha (one_pow n)

  have s1 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift a 1) (lift 1 b) 1 := fun b hb =>
    (cubWeil_iff_weilIs (c := c) globalFns_holds hB ha' (WeilIntegral.lift_pow (one_pow n) hb) 1).2 (hpair b hb)

  have s2 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift b 1) (lift a 1) 1 := by
    intro b hb
    have h := RaynaudAxis.cubWeil_one_of_triv_pull S (A ⊗ A) A (lift (𝟙 A) 1) hA inferInstance M c h2 n
      (Over.mk p) b a hb ha
    simpa using h

  have s3 : ∀ z : Over.mk p ⟶ A ⊗ A, z ^ n = 1 → CubWeil c n (lift a 1) z 1 := by
    intro z hz
    have e : lift (z ≫ fst A A) 1 * lift 1 (z ≫ snd A A) = z := by
      ext <;> simp [MonObj.mul_comp]
    have hz1 : (z ≫ fst A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have hz2 : (z ≫ snd A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have h := ((s2 _ hz1).mul_left (s1 _ hz2).symm).symm
    rw [e] at h
    simpa using h

  have ht := OrthKer.mem_kernel_of_cubWeil_orthogonal k S p (A ⊗ A) hB M c n hn (lift a 1) ha' s3
  have hD : (translDiff (A ⊗ A) P (lift a 1)).IsLB := LB.isLB_linComb hL _ _
  have h0 : CechPic.cls _ hD = 0 := (CechPic.cls_eq_zero_iff hD).2 ht

  have e := AbDual.pull_translDiff hL (lift a 1) hD (snd A (Over.mk p)) (lift 1 (fst A (Over.mk p)))
  rw [h0, map_zero] at e
  have k1 : (snd A (Over.mk p) ≫ lift a 1) * lift 1 (fst A (Over.mk p)) =
      lift (snd A (Over.mk p) ≫ a) (fst A (Over.mk p)) := by
    ext <;> simp [MonObj.mul_comp]
  have k2 : CechPic.pull (lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p))).left (CechPic.cls P hL) = 0 := by
    have e1 : AbDual.evc hL (1 : A ⟶ A) (𝟙 A) = 0 := (AbDual.triv_ev_iff hL _ _).1 h1
    have e2 : lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p)) =
        fst A (Over.mk p) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      ext <;> simp
    have e3 : CechPic.pull (lift (1 : A ⟶ A) (𝟙 A)).left (CechPic.cls P hL) = 0 := e1
    rw [e2, Over.comp_left, CechPic.pull_comp, e3, map_zero]
  rw [k1, k2, sub_zero] at e
  exact (AbDual.triv_ev_iff hL _ _).2 e.symm

end GlobalTheory.WeilKernel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one) | (exact GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one) | (intros; apply GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ZarhinFam

section Maps

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

def zpr (mu : B ⟶ A) (k : Fin 8) : Zob A B ⟶ A :=
  Sum.elim (pa A B) (fun j => pb A B j ≫ mu) (sig k)

def zphi (mu : B ⟶ A) : Zob A B ⟶ Out.powObj A 8 :=
  (Out.powIsLimit A 8).lift (Fan.mk _ (zpr A B mu))

theorem zphi_powPr (mu : B ⟶ A) (k : Fin 8) : zphi A B mu ≫ Out.powPr A k = zpr A B mu k :=
  (Out.powIsLimit A 8).fac _ ⟨k⟩

end Maps

def zW (d : ℕ) : Matrix (Fin 8) (Fin 8) ℤ := fun k l =>
  Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 (sig k) (sig l)

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundle
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowPos

open GlobalTheory.FlatTw GlobalTheory.FlatLine

theorem rk_pos {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {G : WTZ D.host.E} (h : Y.GoodAt G)
    {f : Rul Y.d.Xo₂ Y.d.c₂} (hf : f ∈ Y.V G) (hf0 : f ≠ 0) : 0 < Y.rk G := by
  haveI : Module.Finite Y.d.c₂.F (Y.V G) := Module.Finite.of_basis h.1.some.2.1.1
  show 0 < Module.finrank Y.d.c₂.F (Submodule.span Y.d.c₂.F (latW Y.U G : Set (Y.V G)))
  rw [h.2.2, finrank_top]
  exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f, hf⟩, fun e => hf0 (congrArg Subtype.val e)⟩

theorem mem_cuspW_of_exZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') {f : Rul Xo c}
    (hf : f ∈ cuspW Xo c U G) : f ∈ cuspW Xo c U G' := by
  rw [AllWt.mem_cuspW] at hf ⊢
  refine ⟨h ▸ hf.1, fun σ hσ => ?_⟩
  rw [← AllWt.modelWt_congr (U σ) hσ (hU σ hσ) h]
  exact hf.2 σ hσ

theorem exZ_lowered {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 : ℤ) (hn : Even n) :
    exZ Dw (wtOf Dw (uMinus Dw a n kc c0 + parWt Dw (anchor Dw a n kc)) ((n / 2 : ℕ) : ℤ)) = exZ Dw (shiftG Dw a n (-c0)) := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : m + m = 2 * m := by ring
  rw [h2, Nat.mul_div_cancel_left m two_pos, GlobalTheory.CovTop.Model.exZ_shiftG]
  show exZ Dw (wtOf Dw _ _) = exZ Dw (wtOf Dw _ _)
  congr 2
  rw [uMinus, ← uWt_add_anchor Dw a (2 * m) kc, neg_smul]
  abel

end GlobalTheory.CovTop.LowPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

namespace GlobalTheory.CechFin

private theorem resG_resG_ext {Z : Scheme.{0}} {U V T : Z.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCob_of_isCob_subcover (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J)
    (hS : ∀ i, W i ≤ ⨆ a ∈ S, W a) (d : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hd : IsCoc W d)
    (h₀ : ∀ i, Γ(Z, W i))
    (hh₀ : ∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) :
    ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have cov : ∀ (V : Z.Opens) (i : J), V ≤ W i → V ≤ ⨆ a : S, V ⊓ W a.1 := by
    intro V i hV x hx
    have hx' := hS i (hV hx)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨ha', hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 ha
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha'⟩, hx, hxa⟩
  have glue : ∀ i, ∃ g : Γ(Z, W i), ∀ a : S,
      resG Z (inf_le_left : W i ⊓ W a.1 ≤ W i) g = d i a.1 + resG Z inf_le_right (h₀ a.1) := by
    intro i
    obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' (fun a : S => W i ⊓ W a.1) (W i)
      (fun _ => homOfLE inf_le_left) (cov (W i) i le_rfl)
      (fun a => d i a.1 + resG Z inf_le_right (h₀ a.1)) (by
        intro a b
        show resG Z inf_le_left (d i a.1 + resG Z inf_le_right (h₀ a.1)) =
          resG Z inf_le_right (d i b.1 + resG Z inf_le_right (h₀ b.1))
        have hT : W i ⊓ W a.1 ⊓ (W i ⊓ W b.1) ≤ W i ⊓ W a.1 ⊓ W b.1 :=
          le_inf inf_le_left (inf_le_right.trans inf_le_right)
        have c := congrArg (resG Z hT) (hd i a.1 b.1)
        have e := congrArg (resG Z (hT.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
          (hh₀ a.1 a.2 b.1 b.2)
        simp only [map_add (f := _), map_sub, resG_resG_ext] at c e ⊢
        linear_combination c - e)
    exact ⟨g, fun a => hg a⟩
  choose g hg using glue
  refine ⟨g, fun i i' => ?_⟩
  refine Z.sheaf.eq_of_locally_eq' (fun a : S => W i ⊓ W i' ⊓ W a.1) (W i ⊓ W i')
    (fun _ => homOfLE inf_le_left) (cov (W i ⊓ W i') i inf_le_left) _ _ (fun a => ?_)
  show resG Z inf_le_left (d i i') = resG Z inf_le_left (resG Z inf_le_left (g i) - resG Z inf_le_right (g i'))
  have k₁ := congrArg (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W a.1 ≤ W i ⊓ W a.1)) (hg i a)
  have k₂ := congrArg (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W a.1 ≤ W i' ⊓ W a.1)) (hg i' a)
  have c := hd i i' a.1
  simp only [map_add (f := _), map_sub, resG_resG_ext] at k₁ k₂ c ⊢
  linear_combination c - k₁ + k₂

end GlobalTheory.CechFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcoverStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover : ∀ (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J), (∀ i, W i ≤ ⨆ a ∈ S, W a) → ∀ d : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W d → ∀ h₀ : ∀ i, Γ(Z, W i), (∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) → ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechFin.isCob_of_isCob_subcover | exact GlobalTheory.CechFin.isCob_of_isCob_subcover | (intros; apply GlobalTheory.CechFin.isCob_of_isCob_subcover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.PicBilin

variable {S : Scheme.{0}}

theorem evc_pow_left {A B Y : Over S} [GrpObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (hadd : ∀ (a a' : Y ⟶ A) (t : Y ⟶ B), evc hP (a * a') t = evc hP a t + evc hP a' t)
    (a : Y ⟶ A) (t : Y ⟶ B) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  induction n with
  | zero =>
    have e := hadd 1 1 t
    rw [_root_.mul_one] at e
    rw [pow_zero, zero_smul]
    exact left_eq_add.1 e
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem comp_pow_pt {A T Y : Over S} [GrpObj A] (f : Y ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ)
    (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) : cls _ h = m • cls L hL := by
  refine (cls_linComb hL (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1) h).trans ?_
  simp [pull_id]

end GlobalTheory.PicBilin

namespace GlobalTheory.PicBilin

theorem triv_pow_of_translDiff : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  intro S A _ _ hA P hP rig₁ rig₂ hsym T hT h₀ h' m hsq htd
  have hs : (swap P).IsLB := pull_isLB hP _
  obtain ⟨hadd₁, hadd₂⟩ := additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP rig₁ rig₂
  have eL : ∀ {Y : Over S} (a a' t : Y ⟶ A), evc hP (a * a') t = evc hP a t + evc hP a' t :=
    fun a a' t => (isAdditive_iff hP).1 hadd₁ _ a a' t
  have eR : ∀ {Y : Over S} (a t t' : Y ⟶ A), evc hP a (t * t') = evc hP a t + evc hP a t' := by
    intro Y a t t'
    have e := (isAdditive_iff hs).1 hadd₂ _ t t' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at e
  have hsymc : cls P hP = cls _ hs := (cls_eq_iff hP hs).2 hsym
  have eS : ∀ {Y : Over S} (a b : Y ⟶ A), evc hP a b = evc hP b a := by
    intro Y a b
    rw [← evc_swap hP hs a b]
    simp only [evc, hsymc]
  have hL₁ : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).IsLB := LB.isLB_linComb hL₁ _ _
  have e0 := pull_translDiff hL₁ (h' ^ m) hD (snd A T) (fst A T)
  rw [(cls_eq_zero_iff hD).2 htd, map_zero] at e0
  have hu : ∀ u : A ⊗ T ⟶ A, CechPic.pull u.left (cls _ hL₁) = evc hP u u := fun u => by
    rw [cls_ev hP, pull_evc, Category.comp_id]
  rw [hu, hu] at e0
  have hXX : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) = 0 := by
    rw [← pull_evc, hT (evc hP (h' ^ m) (h' ^ m)), map_zero]
  have key : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) + evc hP (snd A T ≫ h' ^ m) (fst A T) +
      (evc hP (fst A T) (snd A T ≫ h' ^ m) + evc hP (fst A T) (fst A T)) - evc hP (fst A T) (fst A T) = 0 := by
    rw [← eR, ← eR, ← eL]
    exact e0.symm
  rw [hXX, eS (fst A T) (snd A T ≫ h' ^ m)] at key
  have h2 : 2 • evc hP (snd A T ≫ h' ^ m) (fst A T) = 0 := by
    rw [two_nsmul, ← key]
    abel
  rw [comp_pow_pt, evc_pow_left hP (fun a a' t => eL a a' t)] at h2
  have hsq' : toUnit (A ⊗ T) ≫ h₀ = (snd A T ≫ h') ^ 2 := by
    rw [← comp_pow_pt, hsq, ← Category.assoc, toUnit_unique (snd A T ≫ toUnit T) (toUnit _)]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have eQ : ∀ {Y : Over S} (a b : Y ⟶ A), evc hQ a b = m • evc hP a b := by
    intro Y a b
    rw [evc, cls_heckePow hP m hQ, map_nsmul]
    rfl
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hQ _) _)).1 ?_
  rw [cls_pull (pull_isLB hQ _)]
  change CechPic.pull (fst A T).left (evc hQ (toUnit A ≫ h₀) (𝟙 A)) = 0
  rw [pull_evc, eQ, Category.comp_id, ← Category.assoc, toUnit_unique (fst A T ≫ toUnit A) (toUnit _), hsq',
    evc_pow_left hP (fun a a' t => eL a a' t), smul_comm]
  exact h2

end GlobalTheory.PicBilin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_trivial_of_translate_difference_trivial : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.PicBilin.triv_pow_of_translDiff) | (exact GlobalTheory.PicBilin.triv_pow_of_translDiff) | (intros; apply GlobalTheory.PicBilin.triv_pow_of_translDiff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClass
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K]

theorem pull_lam_av {A : AbVar K} (c : Pic A.X.left) {Y Z : Over (Sp K)} (u : Z ⟶ Y) (x y : Y ⟶ A.X) :
    CechPic.pull u.left (AbVar.lam c x y) = AbVar.lam c (u ≫ x) (u ≫ y) := by
  simp only [AbVar.lam, map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul]

theorem pull_one_eq_zero {A : AbVar K} (c : Pic A.X.left) (Y : Over (Sp K)) :
    CechPic.pull (1 : Y ⟶ A.X).left c = 0 := by
  rw [CategoryTheory.Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨V, hV, hc⟩ := AbDual.exists_pull_eq_zero (CechPic.pull (η[A.X]).left c) (IsLocalRing.closedPoint K)
  exact AbDual.pull_eq_zero_of_mem V _ (fun z => by
    have : (toUnit Y).left z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc

theorem exists_phi : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A',
    AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧
      (IsAmpleCls c → IsIsogeny φ) := by
  intro K _ A A' P hP hdim c
  set β : Pic (A.X ⊗ A.X).left := AbVar.lam c (fst A.X A.X) (snd A.X A.X) with hβ
  have hpull : ∀ {Y : Over (Sp K)} (x y : Y ⟶ A.X),
      CechPic.pull (lift x y).left β = AbVar.lam c x y := fun x y => by
    rw [hβ, pull_lam_av, lift_fst, lift_snd]
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ A.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β := by
    intro Y a a' t
    rw [hpull, hpull, hpull]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K A c Y a a' t
  have hnorm : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ A.X)).left β = 0 := by
    rw [hpull, AbVar.lam, _root_.mul_one, pull_one_eq_zero, sub_self, sub_zero]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' A P hP β hadd hnorm
  refine ⟨ψ, hψ, fun hc => ?_⟩
  have hfin : IsFinite ψ.hom.left := by
    refine (GlobalTheory.T.isFinite_iff_finite_ker' K A A' ψ).2 ?_
    have hF := GlobalTheory.T.finite_mumfordClass_eq_zero_ample K A c hc
    refine Finite.of_injective (β := {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K)))
      (snd A.X _ ≫ x) = 0}) (fun x => ⟨x.1, ?_⟩) ?_
    · have hx : x.1 ≫ ψ.hom = 1 := by
        have := x.2
        rw [MonoidHom.mem_ker, ptMap_apply] at this
        exact this
      rw [← hpull, hψ, AbDual.pull_evc, lift_fst, lift_snd_assoc, Category.assoc, hx, MonObj.comp_one]
      exact AbDual.evc_one_right hP.isLB hP.zero _
    · intro x y h
      exact Subtype.ext (Subtype.mk.inj h)
  exact ⟨hfin, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A A' ψ hdim.symm hfin⟩

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClassStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_dual_of_mumfordClass : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A', AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧ (IsAmpleCls c → IsIsogeny φ) := by
  first | (exact @GlobalTheory.AV.AbVar.exists_phi) | (exact GlobalTheory.AV.AbVar.exists_phi) | (intros; apply GlobalTheory.AV.AbVar.exists_phi  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToInteger
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_isAdj : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left),
    IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  intro K _ A B c d hc f
  obtain ⟨A', P, ⟨hP, -⟩, hdim⟩ := GlobalTheory.T.abelianVariety_exists_dual_pair K A
  obtain ⟨φ, hφ, hiso⟩ := GlobalTheory.T.exists_hom_to_dual_of_mumfordClass K A A' P hP hdim c
  obtain ⟨n, v, hn, -, -, hvφ⟩ := exists_quasiInverse_isogeny K A A' φ (hiso hc)
  have hadd : ∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ B.X),
      CechPic.pull (lift (a * a') t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) =
      CechPic.pull (lift a t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) +
      CechPic.pull (lift a' t).left (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) := by
    intro Y a a' t
    simp only [lam_eq, CechPic.pull_lam, lift_fst_assoc, lift_snd, MonObj.mul_comp]
    simp only [← lam_eq]
    exact GlobalTheory.T.abelianVarietyMumfordClass_mul_left K B d Y _ _ t
  have hzero : CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ B.X)).left
      (AbVar.lam d (fst A.X B.X ≫ f.hom) (snd A.X B.X)) = 0 := by
    rw [lam_eq, CechPic.pull_lam, lift_snd, CechPic.lam_one_right]
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom K A A' B P hP _ hadd hzero
  have hpow : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (b : Y ⟶ A'.X) (m : ℕ),
      AbDual.evc hP.isLB a (b ^ m) = m • AbDual.evc hP.isLB a b := by
    intro Y a b m
    induction m with
    | zero => rw [pow_zero, zero_smul, AbDual.evc_one_right hP.isLB hP.zero a]
    | succ m ih => rw [pow_succ, GlobalTheory.T.poincareClass_additive_in_dual_variable K A A' P hP Y a, ih, succ_nsmul]
  refine ⟨n, ψ ≫ v, hn, ?_⟩
  have e1 := congrArg (CechPic.pull (lift (fst A.X B.X) (snd A.X B.X ≫ (ψ ≫ v).hom)).left) hφ
  rw [lam_eq, CechPic.pull_lam, AbDual.pull_evc, lift_fst, lift_snd_assoc, lift_snd, ← lam_eq] at e1
  unfold IsAdj
  rw [e1]
  simp only [comp_hom, Category.assoc]
  rw [← comp_hom v φ, hvφ, nsmul_hom, id_hom, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, hpow, ← hψ,
    natCast_zsmul]

end GlobalTheory.AV.AbVar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointUpToIntegerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_up_to_integer : ∀ (K : Type) [Field K] (A B : AbVar K) (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → ∀ f : A ⟶ B, ∃ (n : ℕ) (h : B ⟶ A), 0 < n ∧ IsAdj c d f n h := by
  first | (exact @GlobalTheory.AV.AbVar.exists_isAdj) | (exact GlobalTheory.AV.AbVar.exists_isAdj) | (intros; apply GlobalTheory.AV.AbVar.exists_isAdj  <;> assumption)
end
end
