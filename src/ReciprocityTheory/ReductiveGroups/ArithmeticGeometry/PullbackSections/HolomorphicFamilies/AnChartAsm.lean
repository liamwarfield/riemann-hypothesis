module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartX

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ComposeLinearAction
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField

section Ev

variable {g m n : ℕ}

theorem ev_addF (a : Fin 2 → Pt ℂ n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addF ℂ g i) = a 0 i + a 1 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  simp only [ev, addF]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]

theorem ev_CX (a : Fin 1 → Pt ℂ n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : ℂ)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS ℂ 1 g) = C c * a 0 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]
  simp only [ev]
  rw [MvPowerSeries.subst_smul hs, MvPowerSeries.subst_X hs]

theorem addOf_addF (a b : Pt ℂ n g) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    addOf (addF ℂ g) a b = a + b := by
  funext i
  simp only [addOf]
  rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [ha, hb])]
  simp

theorem expS_zero_an (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have ha : PowerSeries.HasSubst (0 : PS k n d) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold FB.expS
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (PowerSeries.exp k)]
  rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, zero_mul, zero_add,
    PowerSeries.constantCoeff_exp, map_one, ← PowerSeries.coe_substAlgHom ha, map_one]

theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt ℂ g j i) = 0 := by
  simp [pt]

end Ev

def addFGLaw (g : ℕ) : FGLaw ℂ g where
  F := addF ℂ g
  const i := by simp [addF]
  unit i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addF, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt ℂ g 0, pt ℂ g 1] (addF ℂ g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt ℂ g 1, pt ℂ g 2] (addF ℂ g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt]),
      ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}

def linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Pt ℂ 1 g :=
  fun k => C (ty k (a : E)) * X ((0 : Fin 1), k)

theorem cc_linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (i : Fin g) : constantCoeff (linAct ty a i) = 0 := by
  simp [linAct]

theorem compose_linear_action (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (b : Pt ℂ n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (linAct ty a) b = fun i => C (ty i (a : E)) * b i := by
  funext i
  simp only [comp1, linAct]
  rw [ev_CX _ (fun ⟨j, k⟩ => by fin_cases j; simp [hb])]
  simp

def linOAct (ty : Fin g → (E →+* ℂ)) : OAct (𝓞 E) (addFGLaw g) where
  act := linAct ty
  const := cc_linAct ty
  hom a := by
    show comp1 (linAct ty a) (addOf (addF ℂ g) (pt ℂ g 0) (pt ℂ g 1)) =
      addOf (addF ℂ g) (comp1 (linAct ty a) (pt ℂ g 0)) (comp1 (linAct ty a) (pt ℂ g 1))
    rw [addOf_addF _ _ (cc_pt 0) (cc_pt 1), compose_linear_action _ _ _ (fun i => by simp [pt]),
      compose_linear_action _ _ _ (cc_pt 0), compose_linear_action _ _ _ (cc_pt 1), addOf_addF _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show linAct ty (a + b) = addOf (addF ℂ g) (linAct ty a) (linAct ty b)
    rw [addOf_addF _ _ (cc_linAct ty a) (cc_linAct ty b)]
    funext i
    simp [linAct, add_mul]
  mul_act a b := by
    show linAct ty (a * b) = comp1 (linAct ty a) (linAct ty b)
    rw [compose_linear_action _ _ _ (cc_linAct ty b)]
    funext i
    simp [linAct, mul_assoc]
  one_act := by
    funext i
    simp [linAct, pt]

def anFB [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : FB ℂ g (𝓞 E) := FB.triv (addFGLaw g) (linOAct ty)

theorem anFB_canon [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : (anFB ty).IsCanonGauge ℂ 0 := by
  constructor <;> simp [anFB, FB.triv, ev_zero', expS_zero_an]

end Act

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} [Algebra c.F ℂ]

def anUvec (e' : Fin g ≃ Lt1 Dw) : Lt1 Dw → Fin g → ℂ := fun ℓ j => if j = e'.symm ℓ then 1 else 0

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows

open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj

section Der

variable {g : ℕ} {Y : Scheme.{0}}

instance isLocalHom_fst : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩

instance isLocalHom_epsMul (cc : ℂ) : IsLocalHom (epsMul cc) :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    have := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp ha
    simpa [epsMul] using this)⟩

instance isLocalHom_fst' : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :=
  isLocalHom_fst

theorem dual_top_le (W : (Spec (CommRingCat.of (DualNumber ℂ))).Opens)
    (hW : IsLocalRing.closedPoint (DualNumber ℂ) ∈ W) : ⊤ ≤ W := by
  intro x _
  have hs : (x : PrimeSpectrum (DualNumber ℂ)) ⤳ IsLocalRing.closedPoint (DualNumber ℂ) := by
    first
    | exact IsLocalRing.specializes_closedPoint _
    | exact (PrimeSpectrum.le_iff_specializes _ _).1
        (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum (DualNumber ℂ)).2.ne_top)
  exact hs.mem_open W.isOpen hW

theorem fst_appLE {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (hU : ⊤ ≤ (e 0) ⁻¹ᵁ U) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(Y, U)) :
    TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h f)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ hU f) := by
  have he : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := hv.1
  have hh : ∀ {a b : Sp ℂ ⟶ Y} (_ : a = b) (h1 : ⊤ ≤ a ⁻¹ᵁ U) (h2 : ⊤ ≤ b ⁻¹ᵁ U),
      a.appLE U ⊤ h1 = b.appLE U ⊤ h2 := by
    intro a b hab h1 h2
    subst hab
    rfl
  have h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
    rw [he]
    exact hU
  have key := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h
  rw [← hh he h0 hU]
  have key2 := congrArg (fun φ => φ.hom f) key
  first
  | exact key2.symm
  | simpa using key2.symm

theorem tangent_open_preimage_zero {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) : ⊤ ≤ (e 0) ⁻¹ᵁ U := by
  intro x _
  rw [← hv.1]
  have hx := h (show (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base x ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  first
  | exact hx
  | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; exact hx)

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (hv' : IsDerivAt0 e w v') : v = v' := by
  apply hom_ext_of_local
  · have hc : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base (IsLocalRing.closedPoint ℂ) =
        IsLocalRing.closedPoint (DualNumber ℂ) :=
      IsLocalRing.comap_closedPoint _
    have e1 := congrArg (fun φ => φ.base (IsLocalRing.closedPoint ℂ)) (hv.1.trans hv'.1.symm)
    have e2 : v ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) =
        v' ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) := e1
    rw [hc] at e2
    exact e2
  · intro U h₁ h₂
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
    ext f
    have hU := tangent_open_preimage_zero hv U h₁
    · exact (fst_appLE hv U hU h₁ f).trans (fst_appLE hv' U hU h₂ f).symm
    · exact (hv.2 U h₁ f).trans (hv'.2 U h₂ f).symm

theorem isDerivAt0_comp_hom {Y' : Scheme.{0}} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e w v) (φ : Y ⟶ Y') :
    IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  refine ⟨by rw [← Category.assoc, hv.1], fun U h f => ?_⟩
  have h' : ⊤ ≤ v ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
  have key := hv.2 (φ ⁻¹ᵁ U) h' (φ.app U f)
  simp only [← valAt'_comp]
  rw [← key]
  have hc : (v ≫ φ).appLE U ⊤ h = φ.app U ≫ v.appLE (φ ⁻¹ᵁ U) ⊤ h' := by
    first
    | exact Scheme.comp_appLE v φ U ⊤ h
    | exact Scheme.Hom.comp_appLE v φ U ⊤ h
    | simp [Scheme.Hom.appLE]
  rw [hc]
  rfl

theorem isDerivAt0_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (cc : ℂ) : IsDerivAt0 e (cc • w) (spMap (epsMul cc) ≫ v) := by
  have hcomp : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsMul cc) =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  refine ⟨?_, fun U h f => ?_⟩
  · rw [← Category.assoc, ← hv.1]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  · have hp : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ U := by
      have hx := h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
      have hc : (spMap (epsMul cc)).base (IsLocalRing.closedPoint (DualNumber ℂ)) =
          IsLocalRing.closedPoint (DualNumber ℂ) :=
        IsLocalRing.comap_closedPoint (epsMul cc)
      first
      | (rw [← hc]; exact hx)
      | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; rwa [hc] at hx)
    have hq : ⊤ ≤ v ⁻¹ᵁ U := dual_top_le _ hp
    have key := congrArg (fun φ => φ.hom f) (specMap_comp_appLE (CommRingCat.ofHom (epsMul cc)) v U h hq)
    have hd := hv.2 U hq f
    simp only at key
    rw [map_smul, ← hd]
    show TrivSqZeroExt.snd (((spMap (epsMul cc) ≫ v).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom f) = _
    rw [key]
    first
    | simp [epsMul]
    | rfl

theorem isDerivAt0_comp_lin {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolFam e) (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y} (hv : IsDerivAt0 e (D w) v) :
    IsDerivAt0 (fun z => e (D z)) w v := by
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact hv.1, fun U h f => ?_⟩
  rw [hv.2 U h f]
  have h0 : (0 : Fin g → ℂ) ∈ {z | ⊤ ≤ e z ⁻¹ᵁ U} := tangent_open_preimage_zero hv U h
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact ((hol U f).2 0 h0).differentiableAt ((hol U f).1.mem_nhds h0)
  have hc := fderiv_comp (0 : Fin g → ℂ) hd D.differentiableAt
  show _ = fderiv ℂ ((fun z => valAt' (e z) U f) ∘ D) 0 w
  rw [hc, ContinuousLinearMap.fderiv, map_zero]
  rfl

end Der

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

def tyD (ty : Fin g → (E →+* ℂ)) (a : NumberField.RingOfIntegers E) : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z k => ty k (a : E) * z k
      map_add' := fun z z' => by funext k; simp [mul_add]
      map_smul' := fun t z => by funext k; simp; ring }

theorem tyD_apply (a : NumberField.RingOfIntegers E) (z : Fin g → ℂ) : tyD ty a z = fun k => ty k (a : E) * z k := rfl

theorem derivAt_over (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left}
    (hv : IsDerivAt0 (fun z => (F.ex i P z).left) w v) :
    v ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ F.u i P := by
  obtain ⟨v0, hv0, -⟩ := (F.ex_diff i P hP).1 w
  rw [isDerivAt0_unique hv hv0, Over.w v0]
  first
  | rfl
  | simp [epsPt]

end Tan

end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
end
end
