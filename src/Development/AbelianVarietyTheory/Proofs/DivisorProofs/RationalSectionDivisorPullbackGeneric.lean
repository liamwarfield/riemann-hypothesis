module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.MultPull

open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull

theorem isRatSec_pull_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) :
    IsRatSec (L.pull j) fun c => Units.map (fnMap j hη).toMonoidHom (r (c PUnit.unit)) := by
  intro c c' h
  have l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) := l h
  have h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    (genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁
  have e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  change fnMap j hη (r (c PUnit.unit) : X.functionField) =
    fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) *
      fnMap j hη (r (c' PUnit.unit) : X.functionField)
  rw [hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]
  first
    | exact congrArg (· * _) (fnOf_resG l h _)
    | exact congrArg (· * _) (fnOf_resG l h _).symm

theorem ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) (y : Y)
    [IsIso (j.stalkMap y)] (f : X.functionField) :
    Scheme.ord (fnMap j hη f) y = Scheme.ord f (j y) := by
  let e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a := rfl
  have hc : Order.coheight y = Order.coheight (j y) := by
    have := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this.symm
  by_cases hz : Order.coheight (j y) = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have hz' : Order.coheight y = 1 := hc.trans hz
  have key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) :
      Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y =
        Scheme.ord (algebraMap _ X.functionField a) (j y) := by
    have ha' : j.stalkMap y a ≠ 0 := by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha
    rw [fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb']
  have h₁ := Scheme.ord_mul (x := j y) hf hb'
  have hfm : fnMap j hη f ≠ 0 := (map_ne_zero_iff _ (fnMap j hη).injective).2 hf
  have hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0 :=
    (map_ne_zero_iff _ (fnMap j hη).injective).2 hb'
  have h₂ := Scheme.ord_mul (x := y) hfm hbm
  rw [← map_mul, hfb] at h₂
  rw [hfb] at h₁
  rw [key a ha0, key b hb0] at h₂
  omega

end GlobalTheory.MultPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def TwistSum (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) {C : Type} (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V)
    (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (e : ℕ) : Prop :=
  ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) →
    X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ →
    ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) →
      SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)

def TwistAtEach (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam)
    (sg : ℤˣ) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
    (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
    (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T →
    ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e

theorem exists_stalk_zeta (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.o₁) :
    ∃ s : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ a := by
  obtain ⟨s, hs⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨algebraMap X₁.o₁ X₁.Ω₁ a, Subalgebra.algebraMap_mem _ a⟩
  exact ⟨s, by rw [← RatModel.coe_stalkEquiv, hs]⟩

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ChernNull

open Set CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem exists_poly_dvd {k R : Type} [CommRing k] [IsDomain k] [CommRing R] [IsDomain R] {D : ℕ}
    (f : MvPolynomial (Fin D) k →+* R) (hf : f.Etale) (g : R) (hg : g ≠ 0) :
    ∃ Q : MvPolynomial (Fin D) k, Q ≠ 0 ∧ ∃ r : R, f Q = g * r := by
  letI := f.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) k) R := hf
  obtain ⟨Q, hQ, r, hr⟩ := (WeilIntegral.isAlgebraic_of_etale (MvPolynomial (Fin D) k) R g).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hg)
  exact ⟨Q, hQ, r, hr⟩

theorem analyticAt_eval {D : ℕ} (P : MvPolynomial (Fin D) ℂ) (z : Fin D → ℂ) :
    AnalyticAt ℂ (fun w : Fin D → ℂ => MvPolynomial.eval w P) z := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z)

theorem volume_poly_zero (D : ℕ) (P : MvPolynomial (Fin D) ℂ) (hP : P ≠ 0) :
    volume {v : ReciprocityTheory.L2DbarEstimates.V D | MvPolynomial.eval (fun a => v a) P = 0} = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ
    (fun z _ => analyticAt_eval P z) ⟨w, mem_univ _, hw⟩
  have hs : {z : Fin D → ℂ | z ∈ univ ∧ MvPolynomial.eval z P = 0} =
      {z : Fin D → ℂ | MvPolynomial.eval z P = 0} := by
    ext z
    simp
  have hT : MeasurableSet {z : Fin D → ℂ | MvPolynomial.eval z P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  rw [hs] at h0
  rw [← (volume_preserving_ofLp_complex (Fin D)).measure_preimage hT.nullMeasurableSet] at h0
  refine measure_mono_null (fun v hv => ?_) h0
  exact hv

theorem injective_of_arithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) (σ : k →+* ℂ) : Function.Injective σ := by
  have := h.isDomain
  have := h.finite
  have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker])
  refine (injective_iff_map_eq_zero σ).2 fun a ha => ?_
  have : a ∈ RingHom.ker σ := ha
  rwa [hk, Ideal.mem_bot] at this

theorem exists_sec_vanish {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z) :
    ∃ g : Γ(X, U), g ≠ 0 ∧ ∀ z ∈ U, z ∈ Z → z ∉ X.basicOpen g := by
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
  let W : X.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨g, hgW, hgm⟩ := hU.exists_basicOpen_le (V := W) ⟨genericPoint X, ⟨hgU, hgen⟩⟩ hgU
  refine ⟨g, fun e => ?_, fun z _ hz hzg => (hgW hzg).2 hz⟩
  rw [e, X.basicOpen_zero] at hgm
  exact hgm

theorem chart_null {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (h : IsArithVar p D) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z)
    (σ : k →+* ℂ) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  have := h.isDomain
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (injective_of_arithVar h σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

theorem chernPart_over_closed : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X _ p D h Z hZ hgen σ B φ ε
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => chart_null h hZ hgen σ c

end GlobalTheory.ChernNull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZeroStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPart_over_properClosed_eq_zero : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  first | exact @GlobalTheory.ChernNull.chernPart_over_closed | exact GlobalTheory.ChernNull.chernPart_over_closed | (intros; apply GlobalTheory.ChernNull.chernPart_over_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

variable {V : Type} [CommRing V] [IsDomain V]

section Data

def IsTheta (D : DegPre V) (θ : D.SecB 1 0) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : V →+* R') θ',
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      ThetaOne.OneBasisAt D f θ'

theorem exists_isTheta [IsLocalRing V] (hV : IsCN V) (D : DegPre V) : ∃ θ, IsTheta D θ :=
  ThetaOne.exists_theta hV D

def UnitAt [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) : Prop :=
  ∃ J, Good D.P.L (Z := Sp V) (closedPoint V) J ∧
    IsUnit (sval (Z := Sp V) θ b.left (closedPoint V) J)

def IntFrm (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) {β : TF (R := V) (FractionRing V) ⟶ D.P.A}
    (w : Frm D (FractionRing V) 1 β) (l : FractionRing V) : Prop :=
  ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen ∧
    ∀ z J, Good D.P.L z J → UT.cst (FractionRing V) z l * (val w (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val

def Exhausts (P : PolAV (Sp V)) (N : ℕ) {C : Type} (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c

end Data

variable {I : Ideal V} {D : DegData V I} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G)

def Ext (x : TFK (R := V) (FractionRing V) ⟶ A.A) (h : 𝟙_ (Over (Sp V)) ⟶ G) : Prop :=
  x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) = (toUnit (TF (R := V) (FractionRing V)) ≫ h).left

def FrRel (w₀ : W0 U) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G)
    (l : FractionRing V) : Prop :=
  ∃ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen ∧
    ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) e (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val

def Lies (w₀ : W0 U) (g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g'.b)
    (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre (FractionRing V) k g'.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A (FractionRing V) k) (s' : Fam D.toPre (FractionRing V) k) (v : FractionRing V),
      U.ExpandsF (FractionRing V) k w₀ s s' → ValAt s x e v → SumF I (FractionRing V) (coef s' g' wk) v

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FibMove

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem polFib_move : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  intro S S' G _ L A _ L' f φ hL hL' hφ hLL' g R _ x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, α, hg, hα, hPL⟩
    refine ⟨P, α ≫ φ, hg, hα.comp hφ, ?_⟩
    exact LBIso.trans P.isLB (pull_isLB hL' α) (pull_isLB hL _) hPL
      (LBIso.trans (pull_isLB hL' α) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL _)
        (RigidBundleGlue.LBIso.pull hLL' α) (lbIso_pull_comp hL φ α).symm)
  · rintro ⟨P, β, hg, hβ, hPL⟩
    have w : β ≫ G.hom = P.A.hom ≫ (x ≫ f) := hβ.1.w
    let α : P.A.left ⟶ A.left := hφ.1.lift β (P.A.hom ≫ x) (by rw [w, Category.assoc])
    have e₁ : α ≫ φ = β := hφ.1.lift_fst _ _ _
    have e₂ : α ≫ A.hom = P.A.hom ≫ x := hφ.1.lift_snd _ _ _
    refine ⟨P, α, hg, IsGrpPullback.cancel hφ (hβ.congr rfl e₁.symm) e₂, ?_⟩
    have h1 : LBIso P.L (L.pull (α ≫ φ)) := by rw [e₁]; exact hPL
    exact LBIso.trans P.isLB (pull_isLB hL _) (pull_isLB hL' α) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL' α)
        (lbIso_pull_comp hL φ α) (RigidBundleGlue.LBIso.pull hLL'.symm α))
  · rintro R' _ i ⟨P, α, hg, hα, hPL⟩
    obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
    refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
    exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL' _) hPL'.symm
      (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL' α) ψ) (pull_isLB hL' _)
        (RigidBundleGlue.LBIso.pull hPL ψ) (lbIso_pull_comp hL' α ψ).symm)

end GlobalTheory.UMin.FibMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  first | exact @GlobalTheory.UMin.FibMove.polFib_move | exact GlobalTheory.UMin.FibMove.polFib_move | (intros; apply GlobalTheory.UMin.FibMove.polFib_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantMSqTorsionAlgClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantMSqTorsionAlgClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)
  let c' : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())
  have hvc : v = fun _ => GlobalTheory.Ex.fnOf c' := funext fun u =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm
  rw [hvc] at hv
  obtain ⟨thP, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP
  have hgen := ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg
  have up := ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())
  rw [hi] at up
  obtain ⟨r, hr'⟩ := hgen θ
  have e₁ : SecM.ofSec G θ = r • SecM.ofSec G th := Subtype.ext (funext hr')
  have q' := ThG.smul hL e₁ up
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩
  convert q' using 1
  simp [GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantMSqTorsionAlgClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  first | exact @GlobalTheory.UMin.exists_thG_of_polFib | exact GlobalTheory.UMin.exists_thG_of_polFib | (intros; apply GlobalTheory.UMin.exists_thG_of_polFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibre
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.TorsList

theorem card_torsion_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {g : ℕ} {K : Type} [Field K]
    {x : Sp K ⟶ S} (hx : PolFib G L g x) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {p : Over.mk (t ≫ x) ⟶ G // p ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨P, α, hg, h, -⟩ := hx
  subst hg
  rw [← GlobalTheory.TorsionCover.card_torsion P.A P.isAb P.smoothDim t hn]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

theorem exists_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  intro S G _ _ L g m K _ _ x hm hx
  have hpow : (m ^ 2) ^ (2 * g) = m ^ (4 * g) := by rw [← pow_mul]; congr 1; ring
  have hm2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hc : Nat.card {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} = m ^ (4 * g) := by
    have := card_torsion_comp G L hx (𝟙 (Sp K)) hm2
    rw [Category.id_comp, hpow] at this
    exact this
  have hfin : Finite {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hm0)
  let e := Finite.equivFinOfCardEq hc
  refine ⟨fun a => (e.symm a).1, fun a b hab => e.symm.injective (Subtype.ext hab), fun a => (e.symm a).2, ?_⟩
  intro K' _ _ i p hp
  have hm' : ((m ^ 2 : ℕ) : K') ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hm2
  have hc' := card_torsion_comp G L hx (spMap i) hm'
  rw [hpow] at hc'
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hepi : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  let F : {q : Over.mk x ⟶ G // q ^ (m ^ 2) = 1} → {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    fun q => ⟨preHom u q.1, by rw [← map_pow, q.2, map_one]⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : spMap i ≫ a.1.left = spMap i ≫ b.1.left := congrArg (fun z => (Subtype.val z).left) hab
    exact (cancel_epi (spMap i)).1 h1
  have hfin' : Finite {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ hm0)
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hF, by rw [hc, hc']⟩).2 ⟨p, hp⟩
  refine ⟨e q, ?_⟩
  show p.left = spMap i ≫ (e.symm (e q)).1.left
  rw [Equiv.symm_apply_apply]
  exact (congrArg (fun z => (Subtype.val z).left) hq).symm

end GlobalTheory.UMin.TorsList
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveListMSqTorsionPolarisedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  first | exact @GlobalTheory.UMin.TorsList.exists_torsion_list | exact GlobalTheory.UMin.TorsList.exists_torsion_list | (intros; apply GlobalTheory.UMin.TorsList.exists_torsion_list <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre S G L g m K x hmK hP
  have hex : ∀ a, ∃ c : K, ThG G L ρ m θ (pt a) (GlobalTheory.ZH.fn c) := by
    intro a
    exact GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  choose c hc using hex
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstantList_algClosed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  first | exact @GlobalTheory.UMin.exists_thList | exact GlobalTheory.UMin.exists_thList | (intros; apply GlobalTheory.UMin.exists_thList <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

section TorPart

variable {T T' : Scheme.{0}} {G₀ : Over T} [GrpObj G₀] {G₁ : Over T'} [GrpObj G₁] {X X' : Type} [AddCommGroup X]
  [AddCommGroup X']

def IsTorPart (tι : splitTorus T X ⟶ G₀) : Prop :=
  IsMonHom tι ∧ ∃ (B : Over T) (_ : GrpObj B) (q : G₀ ⟶ B), IsProper B.hom ∧ IsMonHom q ∧ IsPullback tι (toUnit _) q η[B]

theorem isTorPart_id : IsTorPart (𝟙 (splitTorus T X)) :=
  ⟨inferInstance, 𝟙_ _, inferInstance, toUnit _, inferInstanceAs (IsProper (𝟙 T)), inferInstance,
    haveI : IsIso η[𝟙_ (Over T)] := by rw [show η[𝟙_ (Over T)] = 𝟙 _ from toUnit_unique _ _]; infer_instance
    IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩⟩

theorem IsTorPart.mono {tι : splitTorus T X ⟶ G₀} (h : IsTorPart tι) : Mono tι := by
  obtain ⟨-, B, _, q, -, -, hk⟩ := h
  exact ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩

theorem IsTorPart.pull {f : T' ⟶ T} {φ : G₁.left ⟶ G₀.left} (hφ : IsGrpPullback G₁ G₀ f φ) {tι : splitTorus T X ⟶ G₀}
    (h : IsTorPart tι) : IsTorPart (pullTorus hφ tι) := by
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus hφ tι q hk
  exact ⟨inferInstance, _, inferInstance, q', inferInstanceAs (IsProper (pullback.snd _ _)), hq', hk'⟩

theorem IsTorPart.equiv {tι : splitTorus T X ⟶ G₀} (h : IsTorPart tι) (e : X ≃+ X') :
    IsTorPart (torusMap T e.toAddMonoidHom ≫ tι) := by
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  have : IsIso (torusMap T e.toAddMonoidHom) := ⟨torusMap T e.symm.toAddMonoidHom, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp, by
    rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_id]; congr 1; ext x; simp⟩
  refine ⟨inferInstance, B, inferInstance, q, hB, hq, ?_⟩
  have h1 : IsPullback (torusMap T e.toAddMonoidHom) (toUnit _) (toUnit _) (𝟙 (𝟙_ (Over T))) :=
    IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩
  simpa using h1.paste_horiz hk

theorem isTorPart_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup; IsTorPart E.i :=
  ⟨E.i_hom, E.B, E.grpB, E.q, E.isAbelian.proper, E.q_hom, E.isKernel⟩

theorem isTorPart_gtTorus {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type} [CommRing A] {ρ : R →+* A}
    {D : DegPre R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {H : Over (Sp A)} [GrpObj H]
    {φ : H.left ⟶ G.left} (g : GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback H G (spMap ρ) φ) : IsTorPart (gtTorus g hρ h) :=
  IsTorPart.pull (isGrpPullback_thickLift hρ h) ⟨g.i_hom, _, inferInstance, g.q, by
    have := D.P.isAb.proper
    exact inferInstanceAs (IsProper (pullback.snd _ _)), g.q_hom, g.isKernel⟩

theorem IsTorPart.factor {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {H : Over (Sp A)} [GrpObj H]
    {tι : splitTorus (Sp A) X ⟶ H} (h : IsTorPart tι) [Module.Free ℤ X'] [Module.Finite ℤ X']
    (i : splitTorus (Sp A) X' ⟶ H) (hi : IsMonHom i) : ∃ r : X →+ X', i = torusMap _ r ≫ tι := by
  have hm := h.mono
  obtain ⟨hι, B, _, q, hB, hq, hk⟩ := h
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have ht : i ≫ q = toUnit _ ≫ η[_] := splitTorus_hom_proper_trivial_local A X' _ (i ≫ q) inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ tι = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono tι, MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc, Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem IsTorPart.cancel {A : Type} [CommRing A] [Nontrivial A] {H : Over (Sp A)} [GrpObj H]
    {tι : splitTorus (Sp A) X ⟶ H} (h : IsTorPart tι) {r r' : X →+ X'} (e : torusMap _ r ≫ tι = torusMap _ r' ≫ tι) :
    r = r' := by
  have := h.mono
  exact GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono tι).1 e)

theorem IsTorPart.exists_equiv {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {H : Over (Sp A)} [GrpObj H]
    [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Free ℤ X'] [Module.Finite ℤ X'] {tι : splitTorus (Sp A) X ⟶ H}
    {tι' : splitTorus (Sp A) X' ⟶ H} (h : IsTorPart tι) (h' : IsTorPart tι') :
    ∃ e : X ≃+ X', tι' = torusMap _ e.toAddMonoidHom ≫ tι := by
  obtain ⟨r, hr⟩ := h.factor tι' h'.1
  obtain ⟨s, hs⟩ := h'.factor tι h.1
  have e₁ : s.comp r = AddMonoidHom.id X := h.cancel (by
    rw [GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, ← hr, ← hs, GlobalTheory.SplitTorus.torusMap_id, Category.id_comp])
  have e₂ : r.comp s = AddMonoidHom.id X' := h'.cancel (by
    rw [GlobalTheory.SplitTorus.torusMap_comp, Category.assoc, ← hs, ← hr, GlobalTheory.SplitTorus.torusMap_id, Category.id_comp])
  exact ⟨⟨⟨r, s, fun x => DFunLike.congr_fun e₁ x, fun x => DFunLike.congr_fun e₂ x⟩, map_add r⟩, hr⟩

end TorPart

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {G : Over M.Z}

def IsExt (gγ : Over.mk M.pt ⟶ G) (W : M.Z.Opens) (h : W.toScheme ⟶ G.left) : Prop :=
  h ≫ G.hom = W.ι ∧ ∀ x : Sp Ω ⟶ W.toScheme, x ≫ W.ι = M.pt → x ≫ h = gγ.left

def ExtNear (gγ : Over.mk M.pt ⟶ G) (w : M.Z) : Prop := ∃ W h, w ∈ W ∧ IsExt gγ W h

def ValAt (gγ : Over.mk M.pt ⟶ G) {T : Scheme.{0}} (s : T ⟶ M.Z) (v : T ⟶ G.left) : Prop :=
  ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ G.left) (s' : T ⟶ W.toScheme), IsExt gγ W h ∧ s' ≫ W.ι = s ∧ s' ≫ h = v

theorem ValAt.over {gγ : Over.mk M.pt ⟶ G} {T : Scheme.{0}} {s : T ⟶ M.Z} {v : T ⟶ G.left} (h : ValAt gγ s v) :
    v ≫ G.hom = s := by
  obtain ⟨W, h, s', ⟨h1, -⟩, rfl, rfl⟩ := h
  rw [Category.assoc, h1]

theorem ValAt.comp {gγ : Over.mk M.pt ⟶ G} {T T' : Scheme.{0}} {s : T ⟶ M.Z} {v : T ⟶ G.left} (h : ValAt gγ s v)
    (g : T' ⟶ T) : ValAt gγ (g ≫ s) (g ≫ v) := by
  obtain ⟨W, h, s', h1, rfl, rfl⟩ := h
  exact ⟨W, h, g ≫ s', h1, Category.assoc _ _ _, Category.assoc _ _ _⟩

theorem ExtNear.exists_valAt {gγ : Over.mk M.pt ⟶ G} {A : Type} [CommRing A] [IsLocalRing A] (s : Sp A ⟶ M.Z)
    (h : ExtNear gγ (s (closedPoint A))) : ∃ v, ValAt gγ s v := by
  obtain ⟨W, h, hw, he⟩ := h
  have hr : Set.range s ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ((IsLocalRing.specializes_closedPoint x).map s.continuous).mem_open W.isOpen hw
  exact ⟨_, W, h, IsOpenImmersion.lift W.ι s hr, he, IsOpenImmersion.lift_fac _ _ _, rfl⟩

theorem ValAt.unique [IsSeparated G.hom] {gγ : Over.mk M.pt ⟶ G} {T : Scheme.{0}} {s : T ⟶ M.Z} {v v' : T ⟶ G.left}
    (h : ValAt gγ s v) (h' : ValAt gγ s v') : v = v' := by
  obtain ⟨W, h, t, ⟨h1, h2⟩, ht, rfl⟩ := h
  obtain ⟨W', h', t', ⟨h1', h2'⟩, ht', rfl⟩ := h'
  by_cases hT : IsEmpty T
  · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
  obtain ⟨x₀⟩ := not_isEmpty_iff.1 hT
  have hne : ((W ⊓ W' : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨s x₀, by rw [← ht]; exact (t x₀).2, by rw [← ht']; exact (t' x₀).2⟩
  have : Nonempty (W ⊓ W' : M.Z.Opens).toScheme := ⟨⟨_, hne.some_mem⟩⟩
  have : IsIntegral (W ⊓ W' : M.Z.Opens).toScheme := isIntegral_of_isOpenImmersion (W ⊓ W').ι
  have hr : Set.range M.pt ⊆ Set.range (W ⊓ W').ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x := IsOpenImmersion.lift (W ⊓ W').ι M.pt hr
  have hx : x ≫ (W ⊓ W').ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (x ≫ (W ⊓ W').ι) := hx ▸ M.isDominant_pt
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion x (W ⊓ W').ι
  have key : M.Z.homOfLE (inf_le_left : W ⊓ W' ≤ W) ≫ h = M.Z.homOfLE (inf_le_right : W ⊓ W' ≤ W') ≫ h' := by
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x ?_
    · rw [Category.assoc, Category.assoc, h1, h1', Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    · rw [← Category.assoc, ← Category.assoc, h2 _ (by rw [Category.assoc, Scheme.homOfLE_ι, hx]),
        h2' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hx])]
  have hs : Set.range s ⊆ Set.range (W ⊓ W').ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨by rw [← ht]; exact (t w).2, by rw [← ht']; exact (t' w).2⟩
  let u := IsOpenImmersion.lift (W ⊓ W').ι s hs
  have hu : u ≫ (W ⊓ W').ι = s := IsOpenImmersion.lift_fac _ _ _
  have e : t = u ≫ M.Z.homOfLE inf_le_left := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hu, ht]
  have e' : t' = u ≫ M.Z.homOfLE inf_le_right := by
    rw [← cancel_mono W'.ι, Category.assoc, Scheme.homOfLE_ι, hu, ht']
  rw [e, e', Category.assoc, Category.assoc, key]

variable {I T : Type} (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ)

def Compat {X : Type} [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) {A : Type} [CommRing A] (s : Sp A ⟶ M.Z)
    (a : o →+* A) {G₀ : Over (Sp A)} (φ : G₀.left ⟶ G.left) (tι : splitTorus (Sp A) X ⟶ G₀) : Prop :=
  (∀ e, tι.left ≫ φ ≫ (f e).left = (torusMap (Sp A) (m e) ≫ tι).left ≫ φ) ∧
  ∀ t, ∃ z : Over.mk (𝟙 (Sp A)) ⟶ splitTorus (Sp A) X,
    (∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val)) ∧ ValAt (gγ t) s ((z ≫ tι).left ≫ φ)

variable [GrpObj G]

def LatAt {X : Type} [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w : M.Z) : Prop :=
  ∃ (κ : Type) (_ : Field κ) (s : Sp κ ⟶ M.Z) (a : o →+* κ) (G₀ : Over (Sp κ)) (_ : GrpObj G₀) (φ : G₀.left ⟶ G.left)
    (tι : splitTorus (Sp κ) X ⟶ G₀), s (closedPoint κ) = w ∧ s ≫ M.s = spMap a ∧ IsGrpPullback G₀ G s φ ∧ IsTorPart tι ∧
    Compat f gγ ζ L m c s a φ tι


variable (G) in
def RkAt (w : M.Z) (r : ℕ) : Prop :=
  ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (κ : Type) (_ : Field κ)
    (s : Sp κ ⟶ M.Z) (G₀ : Over (Sp κ)) (_ : GrpObj G₀) (φ : G₀.left ⟶ G.left) (tι : splitTorus (Sp κ) X ⟶ G₀),
    s (closedPoint κ) = w ∧ IsGrpPullback G₀ G s φ ∧ IsTorPart tι ∧ Module.finrank ℤ X = r

variable {f gγ ζ L}


omit [GrpObj G] in
theorem Compat.equiv {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {m : I → X →+ X} {c : T → X →+ ZMod L}
    {m' : I → X' →+ X'} {c' : T → X' →+ ZMod L} {A : Type} [CommRing A] {s : Sp A ⟶ M.Z} {a : o →+* A}
    {G₀ : Over (Sp A)} {φ : G₀.left ⟶ G.left} {tι : splitTorus (Sp A) X ⟶ G₀} (h : Compat f gγ ζ L m c s a φ tι)
    (e : X ≃+ X') (hm : ∀ i x, e (m i x) = m' i (e x)) (hc : ∀ t x, c' t (e x) = c t x) :
    Compat f gγ ζ L m' c' s a φ (torusMap _ e.toAddMonoidHom ≫ tι) := by
  refine ⟨fun i => ?_, fun t => ?_⟩
  · rw [Over.comp_left, Category.assoc, h.1 i, ← Category.assoc, ← Over.comp_left, ← Category.assoc, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp]
    congr 4
    ext x
    exact hm i x
  · obtain ⟨z, hz, hv⟩ := h.2 t
    refine ⟨z ≫ torusMap _ e.symm.toAddMonoidHom, fun χ => ?_, ?_⟩
    · obtain ⟨χ, rfl⟩ := e.surjective χ
      rw [hc, ← hz]
      ext
      rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
        ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]
      simp
    · rw [Category.assoc, ← Category.assoc (torusMap _ _), ← GlobalTheory.SplitTorus.torusMap_comp,
        show e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id X from by ext x; simp,
        GlobalTheory.SplitTorus.torusMap_id, Category.id_comp]
      exact hv


omit [GrpObj G] in
theorem Compat.pull {X : Type} [AddCommGroup X] {m : I → X →+ X} {c : T → X →+ ZMod L} {A B : Type} [CommRing A]
    [CommRing B] {s : Sp A ⟶ M.Z} {a : o →+* A} {G₀ : Over (Sp A)} [GrpObj G₀] {φ : G₀.left ⟶ G.left}
    {tι : splitTorus (Sp A) X ⟶ G₀} (h : Compat f gγ ζ L m c s a φ tι) (b : A →+* B) {G₁ : Over (Sp B)} [GrpObj G₁]
    {ψ : G₁.left ⟶ G₀.left} (hψ : IsGrpPullback G₁ G₀ (spMap b) ψ) :
    Compat f gγ ζ L m c (spMap b ≫ s) (b.comp a) (ψ ≫ φ) (pullTorus hψ tι) := by
  refine ⟨fun i => ?_, fun t => ?_⟩
  · rw [← pullTorus_torusMap_comp, ← Category.assoc, ← Category.assoc, ← Category.assoc, pullTorus_left, pullTorus_left]
    simp only [Category.assoc]
    rw [h.1 i]
  · obtain ⟨z, hz, hv⟩ := h.2 t
    have hw : (spMap b ≫ z.left) ≫ (splitTorus (Sp A) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp B)) ⟶ splitTorus (Sp B) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left := (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    refine ⟨z', fun χ => ?_, ?_⟩
    · ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Aˣ) : A))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    · have := hv.comp (spMap b)
      convert this using 1
      rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc (pullTorus hψ tι).left, pullTorus_left,
        Category.assoc, ← Category.assoc, hz']
      simp only [Category.assoc]

end GlobalTheory.Poinc.FibLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.WeilGeomPt

theorem exists_weilIs_geomPt : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (n : ℕ), 0 < n → (n : κ) ≠ 0 → ∀ y y' : Over.mk x ⟶ B, y ^ n = 1 → y' ^ n = 1 → ∃ e : (Γ((Over.mk x).left, ⊤))ˣ, Out.WeilIs B M n y y' e := by
  intro S B _ _ M hA hM κ _ _ x n _ _ y y' hy hy'
  obtain ⟨e, -, he⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hM hy hy'
  exact ⟨e, he⟩

end GlobalTheory.WeilGeomPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (n : ℕ), 0 < n → (n : κ) ≠ 0 → ∀ y y' : Over.mk x ⟶ B, y ^ n = 1 → y' ^ n = 1 → ∃ e : (Γ((Over.mk x).left, ⊤))ˣ, Out.WeilIs B M n y y' e := by
  first | (exact @GlobalTheory.WeilGeomPt.exists_weilIs_geomPt) | (exact GlobalTheory.WeilGeomPt.exists_weilIs_geomPt) | (intros; apply GlobalTheory.WeilGeomPt.exists_weilIs_geomPt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.FlagCell

def uniR {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun a b => if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem uniR_apply {R : Type*} [CommRing R] {m : ℕ} (n : Low m → R) (a b : Fin m) :
    uniR n a b = if h : b < a then n ⟨(a, b), h⟩ else if a = b then 1 else 0 := rfl

theorem map_uniR {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {m : ℕ} (n : Low m → R) :
    (uniR n).map f = uniR fun s => f (n s) := by
  ext a b
  simp only [Matrix.map_apply, uniR_apply]
  split_ifs <;> simp

end GlobalTheory.FlagCell
end
end
