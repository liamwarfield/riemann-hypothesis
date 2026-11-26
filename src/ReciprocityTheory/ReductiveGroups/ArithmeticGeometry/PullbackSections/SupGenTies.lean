module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def SupAtUnitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w,
      0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) →
      ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
        (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧
        supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤
          2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧
        0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 44 * large₂.sc.L

def CuspTieSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    LastPos (T.Q.Dw j) (wtA w) →
    ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → f ∈ T.C j w

structure XExt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : X.Ψ, ‖τ.1 X.ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, ∃ k : ℤ, EFf X.ξ0 X.Gm x y = k
  EF_perf : ∀ φ : X.Λ →+ ℤ, ∃ x ∈ X.Λ, ∀ y : X.Λ, (φ y : ℚ) = EFf X.ξ0 X.Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm X.Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ X.Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ X.Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ →
    (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ X.Γ

def XExt.toX {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} (e : XExt X) :
    DataX E r :=
  ⟨X, e.k0, e.minWeight_pos, e.k0_le, e.ξ0_abs, e.EF_int, e.EF_perf, e.L', e.L'_fg, e.L'_int, e.L'_dual, e.NA, e.NC,
    e.NA_pos, e.NC_pos, e.NA_sub, e.NC_sub, e.g, e.g_pos, e.cong⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def NZDOfCompSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ →
    (∀ k, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) (F.1 : T.R j) k x ≠ 0) →
    (recPJ h j hj).NonZeroComp w F

def NoBaseSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → DF w + 2 ≤ qq D →
    (∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α}) →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k,
      ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (f : T.R j),
        P ∈ harmA T.Q.c (wtA w) w.n ∧
        (∀ σ' : T.Q.c.F →+* ℂ, Real.log (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) ≤ 140 * D.R.r * large₂.sc.L * absA w) ∧
        IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f ∧ ∃ x' ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) f k x' ≠ 0

def ThetaWeightBounds : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (j : ℕ) (hj : InR D j)
    (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    Formalism.MainNotions.Gaps.FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 →
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 →
      D.R.r ≤ w2.n ∧ LastPos (T.Q.Dw j) (wtA w2) ∧ DF w2 + 2 ≤ qq D) ∧
    (j < D.R.m → ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW →
      D.R.r ≤ w1.n ∧ LastPos (T.Q.Dw j) (wtA w1) ∧ DF w1 + 2 ≤ qq D)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThValDescIn
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def FrBCFieldSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
    (ψ : S →ₐ[c.F] K), ∃ z : FrPt Xo c K, FrMap ψ y z

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExistsFieldOfFf
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U)
    (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section LC

variable {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X))
  (ε : K → ℤ) (H : Y' ⟶ Y)

theorem wchart_pull_le' (e : ∀ k, H ≫ φ k = φ' k) (j : K → L.ι) :
    (LB.LinComb L φ' ε).U j ≤ H ⁻¹ᵁ (LB.LinComb L φ ε).U j := by
  intro p hp
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : p ∈ (φ' k).base ⁻¹' (L.U (j k) : Set X) := Set.mem_iInter.1 hp k
  rw [← e k] at h1
  simpa using h1

theorem map_prod_pullU (e : ∀ k, H ≫ φ k = φ' k) (U : K → X.Opens) (u : ∀ k, Γ(X, U k)ˣ) (V : Y.Opens)
    (V' : Y'.Opens) (hV : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (hV' : ∀ k, V' ≤ φ' k ⁻¹ᵁ U k) (hH : V' ≤ H ⁻¹ᵁ V) :
    Units.map (H.appLE V V' hH).hom.toMonoidHom (∏ k, (res (hV k) (pullU (φ k) (U k) (u k))) ^ ε k) =
      ∏ k, (res (hV' k) (pullU (φ' k) (U k) (u k))) ^ ε k := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  congr 1
  ext
  show (H.appLE V V' hH).hom (((φ k).appLE (U k) V (hV k)).hom (u k : Γ(X, U k))) =
    ((φ' k).appLE (U k) V' (hV' k)).hom (u k : Γ(X, U k))
  show ((φ k).appLE (U k) V (hV k) ≫ H.appLE V V' hH).hom (u k : Γ(X, U k)) = _
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr (e k) (U k) V' _ (hV' k)]

def pullSecF (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) :
    Γ(Y', (LB.LinComb L φ' ε).U j) :=
  (H.appLE ((LB.LinComb L φ ε).U j) ((LB.LinComb L φ' ε).U j) (wchart_pull_le' L φ φ' ε H e j)).hom (s.f j)

set_option maxHeartbeats 1000000 in
theorem pullSecF_compat (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) (i j : K → L.ι) :
    (Y'.presheaf.map (homOfLE (inf_le_left : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
        (LB.LinComb L φ' ε).U i)).op).hom (pullSecF L φ φ' ε H e s i) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) *
        (Y'.presheaf.map (homOfLE (inf_le_right : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
          (LB.LinComb L φ' ε).U j)).op).hom (pullSecF L φ φ' ε H e s j) := by
  have hW : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤
      H ⁻¹ᵁ ((LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j) :=
    fun p hp => ⟨wchart_pull_le' L φ φ' ε H e i hp.1, wchart_pull_le' L φ φ' ε H e j hp.2⟩
  have hres : ∀ (k : K → L.ι) (hk : (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U k)
      (hk' : (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j ≤ (LB.LinComb L φ' ε).U k),
      (Y'.presheaf.map (homOfLE hk').op).hom (pullSecF L φ φ' ε H e s k) =
        (H.appLE _ _ hW).hom ((Y.presheaf.map (homOfLE hk).op).hom (s.f k)) := by
    intro k hk hk'
    show (H.appLE _ _ (wchart_pull_le' L φ φ' ε H e k) ≫ Y'.presheaf.map (homOfLE hk').op).hom (s.f k) =
      (Y.presheaf.map (homOfLE hk).op ≫ H.appLE _ _ hW).hom (s.f k)
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have hu : Units.map (H.appLE _ _ hW).hom.toMonoidHom ((LB.LinComb L φ ε).g i j) = (LB.LinComb L φ' ε).g i j :=
    map_prod_pullU φ φ' ε H e (fun k => L.U (i k) ⊓ L.U (j k)) (fun k => L.g (i k) (j k)) _ _
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))
      (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ' i k)) (inf_le_right.trans (LB.wchart_le L φ' j k))) hW
  have hg : (H.appLE _ _ hW).hom ((LB.LinComb L φ ε).g i j : Γ(Y, (LB.LinComb L φ ε).U i ⊓ (LB.LinComb L φ ε).U j)) =
      ((LB.LinComb L φ' ε).g i j : Γ(Y', (LB.LinComb L φ' ε).U i ⊓ (LB.LinComb L φ' ε).U j)) :=
    congrArg Units.val hu
  rw [hres i inf_le_left inf_le_left, hres j inf_le_right inf_le_right, ← hg, ← map_mul]
  exact congrArg (H.appLE _ _ hW).hom (s.compat i j)

def pullSecLC (e : ∀ k, H ≫ φ k = φ' k) (s : LB.Sec (LB.LinComb L φ ε)) : LB.Sec (LB.LinComb L φ' ε) where
  f := pullSecF L φ φ' ε H e s
  compat := pullSecF_compat L φ φ' ε H e s

end LC

theorem exists_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S}
    (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A) (s : LB.Sec (LPow A L a T)) :
    ∃ s' : LB.Sec (LPow A L a T'), IsPullSec A L a h hh s s' := by
  have e : ∀ _k : Fin 1, h.left ≫ (snd T A).left = (snd T' A).left := fun _ => by rw [← Over.comp_left, hh]
  exact ⟨pullSecLC L _ _ _ h.left e s, fun j => rfl⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeE
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeD
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X}

theorem tv_sum {κ : Type} (s : Finset κ) (f : κ → TanM x Xo.univ.t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => first | rfl | simp [tv]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, tv_add, ih]

variable {c}

def tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT hv)

theorem tv_tvOf {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : tv (tvOf hv) = ovT (t := Xo.univ.t) hv := rfl

variable (c) in
theorem eigAt_iff {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (τ : E →+* ℂ) :
    IsEigAt (c := c) τ v ↔ IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (tvOf hv) := by
  refine (isEigAt_iff (c := c) τ (ovT (t := Xo.univ.t) hv)).trans ?_
  constructor
  · intro h a
    apply tanM_ext
    show tv (tvOf hv) ≫ Xo.univ.t.act.act a = _
    rw [tv_smul, tv_tvOf]
    exact h a
  · intro h a
    have h2 := congrArg tv (h a)
    change tv (tvOf hv) ≫ Xo.univ.t.act.act a = _ at h2
    rw [tv_smul, tv_tvOf] at h2
    exact h2

theorem combAt_iff {m : ℕ} (u : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ i, IsTanAt x (u i))
    (cf : Fin m → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x w) :
    IsCombAt x u cf w ↔ tvOf hw = ∑ i, cf i • tvOf (hu i) := by
  have e1 : tv (∑ i, cf i • tvOf (hu i)) = combT x (fun j => ovT (t := Xo.univ.t) (hu j)) cf := by
    rw [tv_sum]
    simp only [tv_smul, tv_tvOf]
    rfl
  have key := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hu j)) cf w
  constructor
  · intro h
    apply tanM_ext
    rw [e1, tv_tvOf]
    exact Over.OverMorphism.ext (key.1 h).symm
  · intro h
    have h2 := congrArg tv h
    rw [e1, tv_tvOf] at h2
    exact key.2 (by rw [← h2]; rfl)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tvOf_tv {x : Sp S ⟶ Xo.X} (n : TanM x Xo.univ.t.G) :
    tvOf (isTanAtG_of (t := Xo.univ.t) (x0 := x) (tv n) (tv_mem n)) = n := by
  apply tanM_ext
  first
    | rfl
    | exact Over.OverMorphism.ext rfl
    | (ext; rfl)
    | (ext1; simp [tvOf, tv, mkT])
    | simp [tvOf, tv, mkT]

theorem eig_coords (y : FrPt Xo c S) (τ : E →+* ℂ) (n : TanM y.x Xo.univ.t.G)
    (hn : IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) n) :
    ∃! a : Fin (Dw.mult τ) → S, n = ∑ i, a i • tvOf (y.tan τ i) := by
  have hw := isTanAtG_of (t := Xo.univ.t) (x0 := y.x) (tv n) (tv_mem n)
  have hE := (eigAt_iff c hw τ).2 (by rw [tvOf_tv]; exact hn)
  obtain ⟨a, ha, huniq⟩ := y.basis τ _ hw hE
  refine ⟨a, ?_, fun a' h' => huniq a' ((combAt_iff (y.u τ) (y.tan τ) a' hw).2 ?_)⟩
  · have h1 := (combAt_iff (y.u τ) (y.tan τ) a hw).1 ha
    rw [tvOf_tv] at h1
    exact h1
  · rw [tvOf_tv]
    exact h'

theorem eig_comb {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x Xo.univ.t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) Xo.univ.t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.smul_sum.symm
  rw [map_smul, hv i b]
  exact smul_comm _ _ _

def fullB (y : FrPt Xo c S) : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → TanM y.x Xo.univ.t.G :=
  fun k => tvOf (y.tan k.1 k.2)

theorem fullB_eig (y : FrPt Xo c S) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    IsEigV (actR (x0 := y.x) (S := S) Xo.univ.t.act) (embK c τ) (fullB y ⟨τ, i⟩) :=
  (eigAt_iff c (y.tan τ i) τ).1 (y.eig τ i)

theorem fullB_basis (y : FrPt Xo c S) (m : TanM y.x Xo.univ.t.G) :
    ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, m = ∑ k, a k • fullB y k := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := y.x) (S := S) Xo.univ.t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM y.x Xo.univ.t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => eig_coords y τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), a k.1 k.2 • fullB y k
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b k • fullB y k := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • fullB y ⟨τ, i⟩)
      (fun τ => eig_comb τ _ (fun i => fullB_eig y τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeC
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X)

theorem key_fwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i) :
    ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i := by
  rw [sec_eq_iff] at h
  rw [scal_eq_iff]
  intro J yy hy
  have hp : bcV ψ x yy ∈ (tB ψ x).PP.L.U (fun _ _ => J 0) := (cpV' ψ x).le J hy
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcV ψ x) yy hp (h _ _ hp)
  have A1 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0))
        ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f (fun _ _ => J 0)) =
      gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U (fun _ => J 0)) (s''.f (fun _ => J 0)) :=
    (gs_secCP (cpU' ψ x) s'' (bcV ψ x) yy _ hp).trans (by rw [bcV_bcU]; rfl)
  have hp2 : (bcV ψ x ≫ pullback.fst _ _) yy ∈
      (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom x)).U (fun _ => J 0) := (cpσ ψ x).le _ hp
  have A2 : gs (bcV ψ x) yy ((tB ψ x).PP.L.U (fun _ _ => J 0)) ((σB ψ x s0).f (fun _ _ => J 0)) =
      gs (bcPm ψ x) yy ((PPx x).U (fun _ => J 0)) (s0.f (fun _ => J 0)) :=
    (gs_secCP (cpσ ψ x) (θA x s0) (bcV ψ x) yy _ hp).trans
      ((gs_secCP (cpθ x) s0 _ yy _ hp2).trans (by rw [Category.assoc, bcV_gxU]; rfl))
  have A3 : bcV ψ x ≫ (tB ψ x).G.hom = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := bcV_snd ψ x
  rw [A1, A2, A3] at h1
  have hJ : (fun _ : Fin 1 => J 0) = J := funext fun k => by rw [Subsingleton.elim k 0]
  rw [hJ] at h1
  have e4 : gs (𝟙 _) yy ((PPx (spMap ψ ≫ x)).U J) ((secCP (cpS ψ x) s0).f J) =
      gs (bcPm ψ x) yy ((PPx x).U J) (s0.f J) :=
    (gs_secCP (cpS ψ x) s0 (𝟙 _) yy J hy).trans (by rw [Category.id_comp]; rfl)
  exact h1.trans (congrArg _ e4.symm)

theorem key_bwd (s0 : LB.Sec (PPx x)) (s'' : LB.Sec (PPx (spMap ψ ≫ x))) (a : T)
    (h : ∀ i, s''.f i = scal (spMap ψ ≫ x) a i * (secCP (cpS ψ x) s0).f i) :
    ∀ i, (secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i = constFn (tB ψ x).G.hom _ a * (σB ψ x s0).f i := by
  rw [scal_eq_iff] at h
  rw [sec_eq_iff]
  intro i q hq
  have hq' : bcU ψ x q ∈ (PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit) := (cpU' ψ x).le i hq
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_of_id (bcU ψ x) q hq' (h _ _ hq')
  rw [bcU_fst] at h1
  have B0 : gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((secCP (cpU' ψ x) s'' : LB.Sec (tB ψ x).PP.L).f i) =
      gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        (s''.f (fun _ => i PUnit.unit PUnit.unit)) :=
    (gs_secCP (cpU' ψ x) s'' (𝟙 _) q i hq).trans (by rw [Category.id_comp]; rfl)
  have B1 : gs (bcU ψ x) q ((PPx (spMap ψ ≫ x)).U (fun _ => i PUnit.unit PUnit.unit))
        ((secCP (cpS ψ x) s0).f (fun _ => i PUnit.unit PUnit.unit)) =
      gs (𝟙 _) q ((tB ψ x).PP.L.U i) ((σB ψ x s0).f i) := by
    refine (gs_secCP (cpS ψ x) s0 (bcU ψ x) q _ hq').trans ?_
    rw [bcU_bcPm]
    exact ((gs_secCP (cpσ ψ x) (θA x s0) (𝟙 _) q i hq).trans
      ((gs_secCP (cpθ x) s0 _ q _ ((cpσ ψ x).le i hq)).trans (by rfl))).symm
  exact B0.trans (h1.trans (congrArg _ B1))

theorem genBC_frame (hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt) (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt)
    {K : Type} [Field K] (ρ : S →+* K) (s0 : LB.Sec (PPx x))
    (hgen : ∀ s' : LB.Sec (PPx x), ∃! a : S, ∀ i, s'.f i = scal x a i * s0.f i) (s'' : LB.Sec (PPx (spMap ρ ≫ x))) :
    ∃! a : K, ∀ i, s''.f i = scal (spMap ρ ≫ x) a i * (secCP (cpS ρ x) s0).f i := by
  obtain ⟨a, ha, hu⟩ := gen_baseChange hS hT Xo.univ (mA x) (θA x s0) (hθ_of x s0 hgen) ρ (mB ρ x)
    (w := idIso ((tA x).PP.L.pull (mB ρ x).φ)) (σB ρ x s0) (hσ_of ρ x s0) (secCP (cpU' ρ x) s'')
  exact ⟨a, key_fwd ρ x s0 s'' a ha, fun a' ha' => hu a' (key_bwd ρ x s0 s'' a' ha')⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V]

def iotaK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V)) :
    tK.G.left ⟶ pullback t.G.hom (Out.jK V) :=
  pullback.lift m.φ tK.G.hom m.cart.1.w

def secU {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t) {k : ℕ} (s : P.U.SecK k) :
    LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => pullback.fst t.G.hom (Out.jK V)) (fun _ => (k : ℤ))) :=
  P.bundle ▸ s

def SecTieGK {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (P : PELUnif (IsLocalRing.maximalIdeal V) t) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) (s : P.U.SecK k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (zp : Z ⟶ (𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G).left),
    zp ≫ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left = r →
    ∀ (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) (J' : (Z ⟶ tK.G.left) → tK.PP.L.ι),
      Good t.PP.L z J → Good tK.PP.L z J' →
      sval (secU P s) (r ≫ iotaK m) z J = ((gv w r z (fun _ => J (r ≫ m.φ)) (J' (r ≫ 𝟙 _))).val) ^ k * sval F zp z J'

def NuK {t : SAB H (Sp V)} (P : PELUnif (IsLocalRing.maximalIdeal V) t)
    (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)) {tK : SAB H (Sp (FractionRing V))}
    (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (k : ℕ)
    (F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))) : Prop :=
  ∃ (s : P.U.SecK k) (Ex : Fam P.D.toPre (FractionRing V) k),
    SecTieGK m w P k F s ∧ P.U.Expands k s Ex ∧ NuGe P.D Q (FractionRing V) vK k Ex 0

end Defs

def NuDataSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t),
    ∃ (ϖ : V) (Q : P.D.toPre.X → ℤ) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
      Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ ValOver ϖ (FractionRing V) vK

def ThetaNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (θ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => ((1 : ℕ) : ℤ))))
      (θK : LB.Sec (LPow tK.G tK.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))), SecTieK m w 1 θK θ → NuK P Q vK m w 1 θK

def MulNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (N : ℕ), 1 ≤ N → ∀ (s : LB.Sec (LPow tK.G tK.PP.L 1 (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (mulA tK.G N).left] ![(N : ℤ) ^ 2, -1]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N).left] ![(N : ℤ) ^ 2, -1]))
      (s₁ : LB.Sec (LPow tK.G tK.PP.L ((N : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm s) → α₀.IsGen → IsNormMul tK.G tK.PP.L tK.PP.rig N α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (mulT tK.G (𝟙_ (Over (Sp (FractionRing V)))) N) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ →
      NuK P Q vK m w (N ^ 2) (zCast tK.G (natCast_sq N) s₁)

def EndNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (π : 𝓞 E) (n k : ℕ), 0 < k → ∀ (F₁ : LB.Sec (LPow tK.G tK.PP.L ((n : ℤ) ^ 2) (𝟙_ (Over (Sp (FractionRing V))))))
      (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2)
        ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
      (h₁ : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V)))))),
      NuK P Q vK m w (n ^ 2) (zCast tK.G (natCast_sq n) F₁) → α₀.IsGen →
      IsNormEnd tK.G tK.PP (tK.act.act π) (k : ℤ) ((n : ℤ) ^ 2) α₀ →
      LB.Gen.Corr tK.PP.L _ _ _ _ α (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) →
      IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)) (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π)
        (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ →
      NuK P Q vK m w k h₁

def FinNuSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (a : ℤ) (k : ℕ) (ha : a = k), 0 < k → ∀ (h hh : LB.Sec (LPow tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))))
      (b : (𝟙_ (Over (Sp (FractionRing V)))) ⟶ tK.G) (U : ThetaGrp tK.G tK.PP.L a (𝟙_ (Over (Sp (FractionRing V))))),
      NuK P Q vK m w k (zCast tK.G ha h) → b ^ k = 1 → SymLift tK.G tK.PP.L a k b U → IsActOf tK.G tK.PP.L a U h hh →
      NuK P Q vK m w k (zCast tK.G ha hh)

def NuRegSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (t : SAB H (Sp V)) (P : PELUnif (IsLocalRing.maximalIdeal V) t), P.TorsionIso →
    ∀ (ϖ : V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (tK : SAB H (Sp (FractionRing V))) (m : SABMap tK t (Out.jK V)) (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)),
      RigIso m w →
    ∀ (k : ℕ), 0 < k → ∀ F : LB.Sec (LPow tK.G tK.PP.L (k : ℤ) (𝟙_ (Over (Sp (FractionRing V))))), NuK P Q vK m w k F →
      ∃ σ : LB.Sec (LB.LinComb t.PP.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))), SecTieK m w k F σ

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory


theorem act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (n : ℕ) : t.act.act (n : 𝓞 E) = 𝟙 _ ^ n := by
  have act0 : t.act.act 0 = 1 := by
    have h0 := t.act.add 0 0
    rw [add_zero] at h0
    exact mul_eq_left.1 h0.symm
  induction n with
  | zero => rw [Nat.cast_zero, act0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one, pow_succ]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Calc

variable {X Y Z : Scheme.{0}}

theorem sval_zCast {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L k₁ T)) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    sval (zCast A h F) r z J = sval F r z J := by
  subst h
  rfl

def pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => 1)) :=
  thfPull1 L (F := 𝟙 X) h (Category.comp_id h) (thfPull L (𝟙 X) s)

theorem gs_pull1 (L : LB X) (h : Y ⟶ X) (s : LB.Sec L) (r : Z ⟶ Y) (z : Z) (j : Fin 1 → L.ι)
    (hz : r z ∈ LB.wchart L (fun _ : Fin 1 => h) j) :
    gs r z _ ((pull1 L h s).f j) = gs (r ≫ h) z (L.U (j 0)) (s.f (j 0)) := by
  simp only [pull1, thfPull1, thfPull]
  refine Eq.trans (gs_appLE h _ _ _ r z ?_ _) ?_
  · exact hz
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (r ≫ h) z ?_ _) ?_
  · exact chart_le_pullback_open L h (Category.comp_id h) j hz
  rw [Category.comp_id]

def secOne (L : LB X) (s : LB.Sec L) : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) :=
  pull1 L (𝟙 X) s

theorem plain_le (L : LB X) (i : L.ι) : L.U i ≤ (𝟙 X) ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := by
  intro y hy
  exact Set.mem_iInter.mpr fun _ => hy

def plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) : LB.Sec L where
  f i := (Scheme.Hom.appLE (𝟙 X) _ _ (plain_le L i)).hom (σ.f (fun _ => i))
  compat i j := fn_ext fun y hy => by
    have m₁ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := plain_le L i hy.1
    have m₂ : (𝟙 X ≫ 𝟙 X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := plain_le L j hy.2
    have g : gm (𝟙 X ≫ 𝟙 X) y _ ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).g (fun _ => i) (fun _ => j)) =
        gm (𝟙 X) y (L.U i ⊓ L.U j) (L.g i j) :=
      (gm_linComb L _ _ (𝟙 X ≫ 𝟙 X) y _ _ m₁ m₂).trans (by simp only [Fin.prod_univ_one, zpow_one, Category.comp_id])
    refine (gs_res _ y _ hy _).trans ((gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat σ (𝟙 X ≫ 𝟙 X) y m₁ m₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val g.symm))
        ((gs_res _ y _ hy _).trans (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy.2 _)))))))

theorem gs_plainOf (L : LB X) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1))) (y : X) (i : L.ι)
    (hy : y ∈ L.U i) :
    gs (𝟙 X) y (L.U i) ((plainOf L σ).f i) =
      gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i)) := by
  simp only [plainOf]
  refine Eq.trans (gs_appLE (𝟙 X) _ _ _ (𝟙 X) y ?_ _) ?_
  · exact hy
  rw [Category.comp_id]

theorem gs_resTop (r : Z ⟶ X) (z : Z) {U : X.Opens} (hz : r z ∈ U) (a : Γ(X, ⊤)) :
    gs r z U (resG X (le_top : U ≤ ⊤) a) = gs r z ⊤ a := by
  exact gs_res r z le_top hz a

theorem secOne_gen {S : Type} [CommRing S] (G : Over (Sp S)) (L : LB G.left) (θ : LB.Sec L)
    (hθ : ∀ σ : LB.Sec L, ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * θ.f i) :
    ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))),
      ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i := by
  show ∀ σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)),
    ∃! a : S, ∀ i, σ.f i = resG G.left le_top ((G.hom).appTop.hom (toΓ S a)) * (secOne L θ).f i
  have e3 : ∀ (i : L.ι) (y : G.left)
      (hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i)),
      gs (𝟙 G.left) y _ ((secOne L θ).f (fun _ => i)) = gs (𝟙 G.left) y (L.U i) (θ.f i) := by
    intro i y hy
    refine (gs_pull1 L (𝟙 _) θ (𝟙 _) y (fun _ => i) hy).trans ?_
    rw [Category.comp_id]
  intro σ
  obtain ⟨a, ha, huniq⟩ := hθ (plainOf L σ)
  refine ⟨a, ?_, fun b hb => huniq b ?_⟩
  · rintro (j : Fin 1 → L.ι)
    obtain ⟨i, rfl⟩ : ∃ i : L.ι, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    refine fn_ext fun y hy => ?_
    have hyi : y ∈ L.U i := LB.wchart_le L _ (fun _ : Fin 1 => i) 0 hy
    rw [gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]
    refine (gs_plainOf L σ y i hyi).symm.trans ?_
    rw [ha i, gs_mul _ y _ hyi, gs_resTop _ y hyi]
  · intro i
    refine fn_ext fun y hyi => ?_
    have hy : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i) := plain_le L i hyi
    rw [gs_mul _ y _ hyi, gs_resTop _ y hyi]
    refine (gs_plainOf L σ y i hyi).trans ?_
    show gs (𝟙 G.left) y ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 1)).U (fun _ => i))
      (σ.f (fun _ => i)) = _
    rw [hb (fun _ => i), gs_mul _ y _ hy, gs_resTop _ y hy, e3 i y hy]

theorem gs_isoMaps {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s') (r : Z ⟶ X)
    (z : Z) (i : M.ι) (k : L.ι) (hi : r z ∈ M.U i) (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gv w r z i k).val * gs r z (L.U k) (s.f k) := by
  unfold Formalism.L2.Pj.IsoMaps at h
  have hV : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have h' := congrArg (gs r z (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res r z _ hV, gs_mul _ z _ hV, gs_res r z _ hV] at h'
  rw [h']
  congr 1
  exact gs_unit _ z _ hV _

end Calc

theorem thetaTie : ThetaTieSt := by
  intro E _ _ _ H Dw l Xo c Tc io y I
  let _ := io.toAlgebra
  let A := Xo.univ.t.G
  let θK : LB.Sec (LPow I.t'.G I.t'.PP.L ((1 : ℕ) : ℤ) (𝟙_ (Over (Sp Tc.Fr)))) :=
    pull1 I.t'.PP.L (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left I.σ
  have gθK : ∀ (Z : Scheme.{0}) (zp : Z ⟶ (𝟙_ (Over (Sp Tc.Fr)) ⊗ I.t'.G).left) (z : Z)
      (J' : (Z ⟶ I.t'.G.left) → I.t'.PP.L.ι), Good I.t'.PP.L z J' →
      sval θK zp z J' = gs (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left) z
        (I.t'.PP.L.U (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left)))
        (I.σ.f (J' (zp ≫ (snd (𝟙_ (Over (Sp Tc.Fr))) I.t'.G).left))) :=
    fun Z zp z J' hJ' => gs_pull1 I.t'.PP.L _ I.σ zp z _ (hJ'.mem _ zp)
  refine ⟨secOne I.G.PP.L I.θ, secOne_gen I.G.G I.G.PP.L I.θ I.θgen, θK, ?_, ?_⟩
  · intro Z r zp zp' h1 h2 h3 z J J' hJ hJ'
    let a0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ Over.mk y.x := Over.homMk I.t'.G.hom rfl
    let b0 : Over.mk (I.t'.G.hom ≫ y.x) ⟶ A := Over.homMk I.m1.φ I.m1.cart.1.w
    let g0 : I.t'.G.left ⟶ Gx y.x := (lift a0 b0).left
    have g0f : g0 ≫ (fst (Over.mk y.x) A).left = I.t'.G.hom := congrArg (fun q => q.left) (lift_fst a0 b0)
    have g0s : g0 ≫ (snd (Over.mk y.x) A).left = I.m1.φ := congrArg (fun q => q.left) (lift_snd a0 b0)
    have hzp : zp = r ≫ g0 := by
      apply pullback.hom_ext
      · show zp ≫ (fst (Over.mk y.x) A).left = (r ≫ g0) ≫ (fst (Over.mk y.x) A).left
        rw [Category.assoc, g0f, h2]
      · show zp ≫ (snd (Over.mk y.x) A).left = (r ≫ g0) ≫ (snd (Over.mk y.x) A).left
        rw [Category.assoc, g0s, h1]
    subst hzp
    have hj : ∀ j : PUnit → Xo.univ.t.PP.L.ι,
        (Xo.univ.t.PP.L.pull I.m1.φ).U j ≤ g0 ⁻¹ᵁ (PPx y.x).U (fun _ => j PUnit.unit) := fun j y' hy' =>
      Set.mem_iInter.2 fun _ => (congrArg (fun q => q y' ∈ Xo.univ.t.PP.L.U (j PUnit.unit)) g0s).mpr (mem_pull.1 hy')
    have mJ : r z ∈ (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => J (r ≫ I.m1.φ)) := mem_pull.2 (hJ (r ≫ I.m1.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have e1 : sval (zCast A Nat.cast_one.symm y.s) (r ≫ g0) z J =
        gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [sval_zCast]
      exact sval_of (L := Xo.univ.t.PP.L) (φ := fun _ : Fin 1 => (snd (Over.mk y.x) A).left) (ε := fun _ => 1) y.s
        (r ≫ g0) z J (fun _ => J (r ≫ I.m1.φ)) (fun _ => by rw [Category.assoc, g0s])
    have e2 : gs (r ≫ g0) z _ (y.s.f (fun _ => J (r ≫ I.m1.φ))) =
        gs r z _ (I.s1.f (fun _ => J (r ≫ I.m1.φ))) := by
      rw [I.gen1 g0 g0s g0f _ (hj _)]
      erw [gs_appLE g0 _ _ (hj _) r z mJ]
    erw [e1, e2, gs_isoMaps I.maps1 r z _ _ mJ mK, gθK Z zp' z J' hJ', h3, pow_one, Category.comp_id]
  · intro Z r zp h3 z J J' hJ hJ'
    have mJ : r z ∈ (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) := mem_pull.2 (hJ (r ≫ I.m2.φ))
    have mK : r z ∈ I.t'.PP.L.U (J' (r ≫ 𝟙 _)) := by simpa using hJ' (r ≫ 𝟙 _)
    have hpl : (I.G.PP.L.pull I.m2.φ).U (fun _ => J (r ≫ I.m2.φ)) ≤ I.m2.φ ⁻¹ᵁ I.G.PP.L.U (J (r ≫ I.m2.φ)) :=
      fun _ hy' => mem_pull.1 hy'
    have e1 : sval (secOne I.G.PP.L I.θ) (r ≫ I.m2.φ) z J =
        gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) := by
      erw [sval_of _ _ z J (fun _ => J (r ≫ I.m2.φ)) (fun _ => by rw [Category.comp_id])]
      rw [secOne]
      erw [gs_pull1 _ _ _ _ z _ (plain_le _ _ (hJ (r ≫ I.m2.φ)))]
      rw [Category.comp_id]
    have e2 : gs (r ≫ I.m2.φ) z (I.G.PP.L.U (J (r ≫ I.m2.φ))) (I.θ.f (J (r ≫ I.m2.φ))) =
        gs r z _ (I.θ2.f (fun _ => J (r ≫ I.m2.φ))) := by
      rw [I.pull _ hpl]
      erw [gs_appLE I.m2.φ _ _ hpl r z mJ]
    erw [e1, e2, gs_isoMaps I.maps2 r z _ _ mJ mK, gθK Z zp z J' hJ', h3, pow_one, Category.comp_id]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
