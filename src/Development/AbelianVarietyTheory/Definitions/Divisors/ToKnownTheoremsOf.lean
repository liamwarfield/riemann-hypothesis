module

public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompleteOfCompactBalls
public import ReciprocityTheory.AnalyticForms.LeviForms.Energy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
namespace GlobalTheory.CovTop

structure Hypotheses2 : Prop where

  p1 : GlobalTheory.Published.ToroidalCompactification

  p2 : GlobalTheory.Published.VolGe

  p3 : GlobalTheory.Published.VolNef

  p4 : GlobalTheory.Published.ArCalc

  p5 : GlobalTheory.Published.AbelianDeRham

  p6 : GlobalTheory.Published.TamagawaSpecialUnitary

  p8 : GlobalTheory.Published.RayClassFieldSt

  p12 : GlobalTheory.Published.SemistableReductionSt

  p13 : GlobalTheory.Published.StrongApproxSU

  p14 : GlobalTheory.Published.GreenSeriesSt

  p16 : GlobalTheory.Published.GoodChernWeil

  p19 : GlobalTheory.Published.LandherrSt

  p20 : GlobalTheory.Published.HasseNormSt

  p22 : GlobalTheory.Published.SemiAbelianHomExtension

  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove

  p25 : GlobalTheory.Published.principalPolarisationOneSection

  p26 : GlobalTheory.Published.AbMulNSt

  q1 : GlobalTheory.Published.GrothendieckMessing

  q3 : GlobalTheory.Published.DeRhamCanonicalExtension

  q4 : GlobalTheory.Published.PrismaticDieudonneHodge

  q6 : GlobalTheory.Published.KawamataViehweg

  q7 : GlobalTheory.Published.NefNumerics

  q8 : GlobalTheory.Published.L2ExtensionLogCanonical

  q9 : GlobalTheory.Published.ArithHilbertSamuel

  q10 : GlobalTheory.Published.ChowFormExists

  q11 : GlobalTheory.Published.CycleHeights

  q13 : GlobalTheory.Published.SerreHolomorphicSections

  q15 : GlobalTheory.Published.NadelVanishingAndNonKltDivisor

  q16 : GlobalTheory.Published.Principalisation

  q18 : GlobalTheory.Published.FormalAlgebraisation

end GlobalTheory.CovTop
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}


instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver




section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

abbrev genAt (Δ : Y.Dv) (x : Y.X) : Y.Fn := ((eqn Δ x)⁻¹ : Y.Fnˣ)


omit [NumberField F] in
theorem generatesAt_genAt (Δ : Y.Dv) (x : Y.X) : Δ.GeneratesAt x (genAt Δ x) := by
  rw [genAt, Units.val_inv_eq_inv_val]
  exact CartierDiv.isEqn_iff_generatesAt_inv.1 (Base.isEqn_eqn Δ x)

def lnN (m : C.Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ) : ℝ := Real.log (C.pn Y σ Δ m (C.cx Y σ f) y) / 2

def lnRatio (m m' : C.Met Y σ Δ) (y : Pts Y σ) : ℝ :=
  lnN m (genAt Δ (under y)) y - lnN m' (genAt Δ (under y)) y

end Norms

structure Cover (Y : Var F) : Type 1 where

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  G : Scheme.{0}
  [intG : IsIntegral G]

  j : G ⟶ X

  π : G ⟶ Y.X

  pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))
  [fin : IsFinite π]
  [surj : Surjective π]

  φ : Y.Fn →+* G.functionField

  φ_spec : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ Y.X.fromSpecStalk (genericPoint Y.X)

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

def deg : ℕ := V.π.residueDegree (genericPoint V.G)

theorem deg_pos : 0 < V.deg := by
  let := (V.π.residueFieldMap (genericPoint V.G)).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π (genericPoint V.G))) (V.G.residueField (genericPoint V.G)) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

def ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : Cover Y where
  X := M.X
  int := M.ar.isIntegral
  p := M.p
  ar := M.ar
  normal := h
  G := Y.X
  j := M.j
  π := 𝟙 _
  pb := by simpa using M.pb
  φ := RingHom.id _
  φ_spec := (Category.comp_id _).trans ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm

theorem deg_ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : (ofModel M h).deg = 1 :=
  Scheme.Hom.residueDegree_id _

def Induces (A : Adl C Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r i : V.G.functionField))))

theorem induces_ofModel {A : Adl C Y} {M : TrueGeo.Model Y} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X)
    {L : HermLB M.p} {k : ℕ+} (hL : A.Induced M L k 0) : (ofModel M h).Induces A L k := by
  obtain ⟨-, r, hr, h₁, h₂⟩ := hL
  have hg (x : Y.X) : ((k : ℕ) • A.D).GeneratesAt x (genAt A.D x ^ (k : ℕ)) := by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn A.D x).nsmul k)
    rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
  refine ⟨r, hr.isRatSec, fun i x hx => (hr.isEqn i x hx).generatesAt_iff.1 (hg x), fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · obtain rfl : y = z := Subtype.ext (e₁.trans (Category.comp_id _))
    have := h₁ σ y y' i _ e₂ hi (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at this
    rw [mul_pow, ← Real.exp_nat_mul]
    refine Eq.trans ?_ this
    congr 2
    ring
  · obtain rfl : z = y.1 := (Category.comp_id _).symm.trans e₁
    have := h₂ v e y yt i e₂ hi
    rw [Pi.zero_apply, mul_zero, sub_zero, Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this

end Cover

end GlobalTheory.Mean4O
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnramPtsDefinite
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}


theorem mem_holSub_model {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem mul_mem_cuspOn_of_isSec {Z : Comp Xo c} {G₀ : WTZ E} (h0 : Even G₀.2) {s : Rul Xo c}
    (hs : s ∈ secZ Xo c (exZ Dw G₀)) (hZ : s ∈ suppOn Z)
    (hh : ∀ σ, GoodEmb c σ → ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G₀ k) (rdU (U σ) s k))
    (hb : ∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C)
    {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * s ∈ cuspOn U Z (G + G₀) := by
  refine ⟨?_, mul_mem_suppOn _ hZ⟩
  have hf' := mem_cuspW.1 hf.1
  refine mem_cuspW.2 ⟨exZ_add_eq (Dw := Dw) G G₀ ▸ mul_mem_secZ hf'.1 hs, fun σ hσ => ?_⟩
  rw [AllWt.rdU_mul, mem_holSub_model]
  intro k
  rw [modelWt_add (U σ) hG h0 k]
  refine (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_model _ _ _).1 (hf'.2 σ hσ) k) _ ⟨hh σ hσ k, ?_⟩
  obtain ⟨C, hC⟩ := hb σ hσ
  refine ⟨max 0 (C / lieFacZ Dw x G₀), fun y _ => ?_⟩
  by_cases hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
  · refine le_max_of_le_right ((le_div_iff₀' (lieFacZ_pos x G₀)).2 ?_)
    have := hC _ hy
    unfold homN ptN at this
    exact this
  · have := rdU_eq_zero (U σ) hZ hy
    simp only at this
    simp [Data.pnorm, this]


end GlobalTheory.FlatTw
end
end
