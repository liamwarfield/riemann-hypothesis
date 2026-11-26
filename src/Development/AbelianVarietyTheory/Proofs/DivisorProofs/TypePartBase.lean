module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix

namespace GlobalTheory.LiftLower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) : ℂ :=
  star (fun a => σ (S.basis.repr f a)) ⬝ᵥ (S.H.map σ) *ᵥ fun a => σ (S.basis.repr g a)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levSW (i : Fin D.R.m) : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i R.triv)

abbrev chiW (i : Fin D.R.m) : GA D (Wc D i) → ℂ := Lev.levChi _ (R.βW i) (R.datWp i R.triv)

def partH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) c).comap (R.HW i σ).e

def IsNormSys (i : Fin D.R.m) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Prop :=
  ∀ P d, (¬ ∃ Rp, Hecke₂ (Wc D i) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P d Rp) → c P d = 0

def projH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.HW i σ).H →ₗ[ℂ] (R.HW i σ).H :=
  ∑ g, RealDat.eC (A := A) σ g • R.gW i σ g


variable (D) in
def hookPlus (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) (aPl D i (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) ρ) : ℝ)

variable {R}

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i σ A.μ0 R.triv c = partH R i σ c := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
    rw [Q_base h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart partH
  rw [e]

theorem e_projH (h : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e (projH R i σ x) = postOn _ (R.eWf i σ) ((R.HW i σ).e x) := by
  unfold projH RealDat.eWf gaL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  ext v g
  simp only [LinearMap.smul_apply, map_smul, h i σ, postOn_apply, LinearMap.sum_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
  rfl

end GlobalTheory.LiftLower

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.ThetaSumNe

theorem exists_mem_schA_thetaSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  intro F _ _ κ _
  classical
  let V := κ → mixedEmbedding.mixedSpace F
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := (GlobalTheory.SchANonzero.intPts F κ).indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F κ
  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨pureA F f g, hmem, ?_⟩
  set t : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) with ht
  have hsum : Summable t := summable_pureA F f hg
  have hre : ∀ ξ, (t ξ).re = b (fun i => mixedEmbedding F (ξ i)) *
      (g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))).re := fun ξ => by
    simp only [ht, pureA_algebraMap, hf, Complex.re_ofReal_mul]
  have hg0 : ∀ y, 0 ≤ (g y).re := fun y => by
    by_cases hy : y ∈ GlobalTheory.SchANonzero.intPts F κ
    · simp [g, Set.indicator_of_mem hy]
    · simp [g, Set.indicator_of_notMem hy]
  have hnn : ∀ ξ, 0 ≤ (t ξ).re := fun ξ => by
    rw [hre]; exact mul_nonneg (b.nonneg) (hg0 _)
  have hz : (t 0).re = 1 := by
    rw [hre]
    have h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.SchANonzero.intPts F κ := fun i _ v => by
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) 0) v ∈ v.adicCompletionIntegers F
      rw [map_zero]
      exact zero_mem (v.adicCompletionIntegers F)
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    rw [hx, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply, Complex.one_re, one_mul]
  have hpos : 0 < ∑' ξ, (t ξ).re :=
    (Complex.reCLM.summable hsum).tsum_pos hnn 0 (by show 0 < (t 0).re; rw [hz]; exact one_pos)
  intro h
  have : (thetaSum F (pureA F f g)).re = ∑' ξ, (t ξ).re := Complex.re_tsum hsum
  rw [h, Complex.zero_re] at this
  exact hpos.ne' this.symm

end GlobalTheory.ThetaSumNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  first | exact @GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | exact GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | (intros; apply GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def NormPin {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (k : Fin F.n)
    (Pm : (F.Di k).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)) : Prop :=
  ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
    (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
    Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
    (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di k).EF a b) ∧
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ j z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (F.ex k Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
        (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ (F.ex k Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
        (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
        Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
    (∀ j z (pt : Sp ℂ ⟶ Gx y.x),
      pt ≫ Formalism.L2.PjFree.gxFst y.x = (F.ex k Pm z).left →
      pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) = θ z * fr j z) ∧
    MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
    (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

def Pinned (U : Formalism.L2.PjFree.Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
      (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (F.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) ∧
      IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) Pm ∧ (U.un k x).x = F.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)

def MoveMatch (U U' : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (k' : U'.Comp) {δ : GL (Fin r) E}
    (h : GlobalTheory.LevelCusp.IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) : Prop :=
  ∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)), FrMove ρ ν (U.un k x) y' →
    y'.x = (U'.un k' ⟨_, h.mem_dom x.2⟩).x ∧ y'.u = (U'.un k' ⟨_, h.mem_dom x.2⟩).u

theorem exists_frBor_gen (z y : FrPt Xo c (CAt σ)) (hx : y.x = z.x) (hu : y.u = z.u) :
    ∃ t₀ : (CAt σ)ˣ, FrBor (fun i => Option.elim i t₀ (fun _ => 1)) z y := by
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 hx
  refine ⟨a, (GlobalTheory.Frames.frBor_iff_frChg _ _ _).2 ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne,
      fun τ i => Matrix.one_apply_eq i, hx, fun τ i => ?_, hbc⟩⟩
  rw [hu]
  exact (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c (CAt σ) z z z).1.2.1 τ i

theorem exists_pinned_of_isUnf {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) :
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ), Pinned U e F ik φ ∧
      ∀ k (x : (U.X k).dom) (Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)),
        (∀ a j, Pm a j = Formalism.L2.PjFree.perFr (U.X k) x.1 (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2) →
        GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → NormPin F (ik k) Pm (U.un k x) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, h1, h2⟩ := hU
  refine ⟨g, e, F, ik, φ, ⟨h1, fun k x => ?_⟩, fun k x Pm hPm hx => ?_⟩
  · obtain ⟨P, a, b, c, d, -⟩ := h2 k x
    exact ⟨P, a, b, c, d⟩
  · obtain ⟨P, a, -, -, -, d⟩ := h2 k x
    obtain rfl : Pm = P := AddMonoidHom.ext fun v => funext fun j => (hPm v j).trans (a v j).symm
    exact d hx

end GlobalTheory.GeoLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open Formalism.L2.NTheta in
theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n = R.r) :
    StrictAnti fun a : Fin n => lamAt h a := by
  intro a b hab
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have h3 := lamAt_add_add_le h (b - a) a (by omega)
  rw [show (a : ℕ) + (b - a) = b by omega] at h3
  have h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith


open Formalism.L2.NTheta in
theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := by rw [hpq, hn]; exact odd_r R
  ext x
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact ⟨⟨a, by have := a.2; omega⟩, by simp⟩
    · exact ⟨⟨p + a, by have := a.2; omega⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩
      simp [ha, show p + ((a : ℕ) - p) = a by omega]


open Formalism.L2.NTheta in
theorem isEnum_holPar_kapW {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n)
    {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q (kapW h p q)) lam ε) (a : Fin n) :
    lam a = (lamAt h a : ℝ) ∧ ε a = decide ((a : ℕ) < p) := by
  obtain ⟨hs, f, hf, hS⟩ := he
  rw [holPar_kapW_eq h hn hpq] at hS
  have hg := lamAt_strictAnti h hn
  have hfs : StrictAnti f := fun a b hab => by
    have := hs hab
    rw [hf, hf] at this
    exact_mod_cast this
  have m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a) := fun a => by
    have : (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p)) := fun a => by
    have : (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a) := by
      rw [← hS]; exact Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have e : f = fun a : Fin n => lamAt h a := by
    refine (StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m1 a
      exact ⟨b, congrArg Prod.fst hb⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m2 a
      exact ⟨b, congrArg Prod.fst hb⟩
  subst e
  refine ⟨hf a, ?_⟩
  obtain ⟨b, hb⟩ := m1 a
  obtain rfl : b = a := hg.injective (congrArg Prod.fst hb)
  exact (congrArg Prod.snd hb).symm

theorem holShape_of_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)] at he
    rw [← hs ρ]
    exact isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  refine ⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩
  · rw [nNeg_shape (by omega) fun a => (key ρ a).2]
    omega
  · choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a
    exact ⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbeddingStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicShape_integralWeight_goodEmbedding : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.HolDict.holShape_of_good | exact GlobalTheory.HolDict.holShape_of_good | (intros; apply GlobalTheory.HolDict.holShape_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftWeight

theorem one_le_aPl_last (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n + 1 = p) :
    1 ≤ aPl D i p τ n := by
  subst hp
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hlt : n < D.R.k + (i : ℕ) := by omega
  have h1 : ¬ n < D.R.k - 1 := by omega
  have h2 : n - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨n - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by simp only; omega)
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) n = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right h1, dite_eq_left h2, hidx]
  have hg := (D.hc τ).gap_be i
  have hq : ((D.R.k + (i : ℕ) : ℕ) : ℚ) = (n : ℚ) + 1 := by
    rw [← hn]; push_cast; ring
  simp only [aPl, if_pos hlt]
  rw [hlam, hq]
  have hfl : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - ((n : ℚ) + 1 - ((n : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

theorem kapTop_lastPos (D : D7) (i : Fin D.R.m) : (kapTop D i).LastPos := by
  intro τ k hk
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hW := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D τ)
  have hs : ((Wc D i).sig (tauE D τ)).1 = D.R.k + (i : ℕ) := by
    show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = D.R.k + (i : ℕ)
    rw [hW]
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ)
    omega
  have hk' : (k : ℕ) + 1 = D.R.k + (i : ℕ) := by
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
    omega
  exact one_le_aPl_last D i τ _ k hs (hk'.trans hs.symm)

end GlobalTheory.LiftWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def toFun {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) :
    IndSp (points (Fin n)) ((ofChar (GlobalTheory.SmGL.torusChar χ)).comp (leviTorus (w.adicCompletion E) (Fin n)).symm.toMonoidHom)
      →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) where
  toFun f := f.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toFun_injective {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) : Function.Injective (toFun w χ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toFun_intertwines {n : ℕ} (χ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (g) (f) :
    toFun w χ (prinSeries χ g f) = rightReg ℂ _ ℂ g (toFun w χ f) := rfl

theorem hasSatGL_prinSeries {n : ℕ} (α : Fin n → ℂˣ) :
    HasSatGL w (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (Finset.univ.val.map α) := by
  have hK : KO (w.adicCompletion E) (Fin n) = KGL w (n := n) := SphCompletion.KO_completion w n
  constructor
  · obtain ⟨φ, h, h1, -⟩ := Formalism.UG.Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
    obtain ⟨f, hf, rfl⟩ := (SphCompletion.isSpherical_iff E w n α _).1 h
    refine (Submodule.ne_bot_iff _).2 ⟨f, hK ▸ hf, fun h0 => ?_⟩
    subst h0
    simp at h1
  · intro x hx h0
    have hx' : x ∈ fixed (prinSeries fun i => unrChar (w.adicCompletion E) (α i)) (KO (w.adicCompletion E) (Fin n)) :=
      hK ▸ hx
    have hs := (SphCompletion.isSpherical_iff E w n α x.1.1).2 ⟨x, hx', rfl⟩
    exact IsSatVecGL.of_map (toFun w _) (toFun_intertwines w _) (toFun_injective w _)
      (isSatVecGL_of_isSpherical hs fun h => h0 (toFun_injective w _ (h.trans (map_zero _).symm)))

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_parab_one (g : GL (Fin 1) k) : g ∈ parab k (points (Fin 1)) :=
  mem_parab_iff.2 fun a b _ _ hab => absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl _)

theorem cB_one (μ : kˣ →* ℂˣ) (p : parab k (points (Fin 1))) :
    PrinProd.cB (fun _ : Fin 1 => μ) p = μ (Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k)) := by
  rw [PrinProd.cB_eq, Fin.prod_univ_one, Fin.prod_univ_one]
  have h : PrinProd.dg p 0 = Matrix.GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    ext
    rw [PrinProd.val_dg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    rfl
  rw [h]
  simp

def oneEquiv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    (detRep (Fin 1) μ).Equiv (prinSeries fun _ : Fin 1 => μ) := by
  let Ψ : ℂ →ₗ[ℂ] IndSp (points (Fin 1))
      ((ofChar (GlobalTheory.SmGL.torusChar fun _ : Fin 1 => μ)).comp (leviTorus k (Fin 1)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun g => (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * c, fun p g => by
          show _ = PrinProd.sB (fun _ : Fin 1 => μ) p _
          rw [PrinProd.sB_apply, cB_one]
          beta_reduce
          rw [map_mul, map_mul, Units.val_mul, mul_assoc]⟩,
        MultiIrr.mem_smooth_of_eventually _ (Filter.mem_of_superset
          (IsOpen.mem_nhds (hμ.detChar (n := Fin 1)) (one_mem _)) fun u hu x => by
            have hu' : detChar (Fin 1) μ u = 1 := hu
            show (μ (Matrix.GeneralLinearGroup.det (x * u)) : ℂ) * c = (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * c
            rw [map_mul (Matrix.GeneralLinearGroup.det), map_mul, ← detChar_apply (n := Fin 1) μ u, hu', mul_one])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_add _ _ _))
      map_smul' := fun c d => Subtype.ext (Subtype.ext (funext fun g => mul_left_comm _ _ _)) }
  refine Representation.Equiv.mk' ⟨Ψ, fun g => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    (fun F => F.1.1 1) (fun c => ?_) (fun F => Subtype.ext (Subtype.ext (funext fun g => ?_)))
  · show (μ (Matrix.GeneralLinearGroup.det x) : ℂ) * (detRep (Fin 1) μ g c) =
      (μ (Matrix.GeneralLinearGroup.det (x * g)) : ℂ) * c
    simp [detRep, ofChar_apply, mul_assoc]
  · show (μ (Matrix.GeneralLinearGroup.det (1 : GL (Fin 1) k)) : ℂ) * c = c
    simp
  · show (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * F.1.1 1 = F.1.1 g
    have h := parInd_law (points (Fin 1)) _ F ⟨g, mem_parab_one g⟩ 1
    rw [mul_one] at h
    rw [h]
    change _ = PrinProd.sB (fun _ : Fin 1 => μ) ⟨g, mem_parab_one g⟩ _
    rw [PrinProd.sB_apply, cB_one]

end GlobalTheory.PrinSat

namespace GlobalTheory.PrinSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LFun GlobalTheory.SplitWeil

theorem hasSatGL_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv σ) {B : Multiset ℂˣ} (h : HasSatGL w σ B) : HasSatGL w ρ B := by
  let f : V →ₗ[ℂ] W := e.toLinearEquiv.toLinearMap
  have hi : ∀ g y, f (ρ g y) = σ g (f y) := fun g y => e.toIntertwiningMap.isIntertwining _ _ g y
  have inj : Function.Injective f := e.toLinearEquiv.injective
  constructor
  · obtain ⟨y, hy⟩ := h.exists_vec
    have hfy : f (e.toLinearEquiv.symm y) = y := e.toLinearEquiv.apply_symm_apply y
    have hs : IsSatVecGL w ρ (e.toLinearEquiv.symm y) B := IsSatVecGL.of_map f hi inj (by rw [hfy]; exact hy)
    exact (Submodule.ne_bot_iff _).2 ⟨_, hs.2.1, hs.1⟩
  · intro x hx h0
    have hfx : f x ∈ fixed σ (KGL w (n := n)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hi, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
    exact IsSatVecGL.of_map f hi inj (h.2 _ hfx fun h1 => h0 (inj (h1.trans (map_zero f).symm)))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_unrChar_of_ord {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ} (hϖ : ord k ϖ = 1) :
    χ = unrChar k (χ ϖ) := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  refine MonoidHom.ext fun x => ?_
  have h1 : o (x / ϖ ^ ord k x) = 1 := by
    rw [map_div, map_zpow, show o ϖ = .ofAdd 1 from congrArg Multiplicative.ofAdd hϖ, ← ofAdd_zsmul,
      smul_eq_mul, mul_one]
    exact div_self' _
  have h2 := h _ (ord_eq_zero_iff.1 (ofAdd_eq_one.1 h1))
  rw [map_div, map_zpow, div_eq_one] at h2
  exact h2

theorem ord_unif {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ord (w.adicCompletion E) (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)) = 1 := by
  have h : Valued.v ((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [SphCompletion.ord_completion, h, WithZero.log_exp, neg_neg]

end GlobalTheory.PrinSat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.HeckeEpsAbs

variable {E : Type} [Field E] [NumberField E]

theorem norm_gaussSumAt_sq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hχ : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow χ w a c ha hχ hu hc

theorem norm_locK {χ : HChar E} (hu : IsUnitary χ) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ‖((χ.locK w x : ℂˣ) : ℂ)‖ = 1 := hu _

theorem absNorm_pos (w : HeightOneSpectrum (𝓞 E)) : 0 < Ideal.absNorm w.asIdeal :=
  Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem natCast_pow_cpow {N : ℕ} (hN : (N : ℂ) ≠ 0) (k : ℕ) (t : ℂ) :
    (((N ^ k : ℕ) : ℂ)) ^ t = (N : ℂ) ^ ((k : ℂ) * t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, ← Complex.cpow_add _ _ hN]
    congr 1; push_cast; ring

theorem prod_natCast_cpow {ι : Type} (S : Finset ι) (f : ι → ℕ) (t : ℂ) :
    ∏ i ∈ S, ((f i : ℕ) : ℂ) ^ t = (((∏ i ∈ S, f i : ℕ)) : ℂ) ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]

theorem locEps_eq_mul (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (s : ℂ) :
    locEps χ w k s = locEps χ w k (1 / 2) * (((Ideal.absNorm w.asIdeal ^ (k + diffExp w) : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (absNorm_pos w).ne'
  rw [natCast_pow_cpow hN]
  simp only [locEps]
  have e : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s * ((k + diffExp w : ℕ) : ℂ)) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 / 2) * ((k + diffExp w : ℕ) : ℂ)) *
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((k + diffExp w : ℕ) : ℂ) * (1 / 2 - s)) := by
    rw [← Complex.cpow_add _ _ hN]; congr 1; ring
  rw [e]; ring

theorem norm_locEps_half {χ : HChar E} (hu : IsUnitary χ) {w : HeightOneSpectrum (𝓞 E)} {k : ℕ} (hk : ExpAt χ w k) :
    ‖locEps χ w k (1 / 2)‖ = 1 := by
  have hNpos : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast absNorm_pos w
  have hG : ‖(if k = 0 then (1 : ℂ) else gaussSumAt χ w k (unif w ^ (k + diffExp w)))‖ =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ ((k : ℝ) / 2) := by
    split_ifs with h
    · simp [h]
    · have := norm_gaussSumAt_sq χ w k _ h hk hu (valuation_unif_pow w _)
      rw [← Real.sqrt_sq (norm_nonneg _), this, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      ring_nf
  rw [locEps, norm_mul, norm_mul, norm_mul, norm_locK hu, hG, Complex.norm_natCast_cpow_of_pos (absNorm_pos w),
    Complex.norm_natCast_cpow_of_pos (absNorm_pos w), one_mul, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  convert Real.rpow_zero _ using 2
  simp
  ring

theorem absNorm_different_eq_prod (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ w, w ∉ S → diffExp w = 0) :
    Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ diffExp w := by
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hm : ∀ w : HeightOneSpectrum (𝓞 E), w.maxPowDividing (differentIdeal ℤ (𝓞 E)) = w.asIdeal ^ diffExp w := by
    intro w
    rw [w.maxPowDividing_eq_pow_multiset_count hD, diffExp, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hD]
  have h := Ideal.finprod_heightOneSpectrum_factorization hD
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_] at h
  · conv_lhs => rw [← h]
    rw [map_prod]
    simp only [hm, map_pow]
  · intro w hw
    by_contra h'
    apply hw
    show w.maxPowDividing _ = 1
    rw [hm, hS w h', pow_zero]

theorem finEps_eq (χ : HChar E) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ) :
    finEps χ a s = finEps χ a (1 / 2) *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ) ^ (1 / 2 - s)) := by
  classical
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  set S : Finset (HeightOneSpectrum (𝓞 E)) := ((Ideal.finite_factors hD).union a.support.finite_toSet).toFinset with hSdef
  have hS : ∀ w, w ∉ S → diffExp w = 0 ∧ a w = 0 := by
    intro w hw
    simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hw
    exact ⟨multiplicity_eq_zero_of_not_dvd hw.1, hw.2⟩
  have hsub : ∀ f : HeightOneSpectrum (𝓞 E) → ℂ, (∀ w, diffExp w = 0 → a w = 0 → f w = 1) → Function.mulSupport f ⊆ S := by
    intro f hf w hw
    by_contra h
    exact hw (hf w (hS w h).1 (hS w h).2)
  have e1 : ∀ z, finEps χ a z = ∏ w ∈ S, locEps χ w (a w) z := fun z =>
    finprod_eq_prod_of_mulSupport_subset _ (hsub _ fun w h0 h1 => by rw [h1]; exact locEps_eq_one χ h0 z)
  have e3 : (((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ)) =
      ∏ w ∈ S, Ideal.absNorm w.asIdeal ^ (a w + diffExp w) := by
    rw [← absNorm_differentIdeal E (𝓞 E), absNorm_different_eq_prod S fun w hw => (hS w hw).1, Finsupp.prod,
      Finset.prod_subset (s₁ := a.support) (s₂ := S) ?_ ?_, ← Finset.prod_mul_distrib]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [← pow_add, add_comm]
    · intro w hw
      simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe]
      exact Or.inr hw
    · intro w _ hw
      rw [Finsupp.notMem_support_iff.1 hw, pow_zero]
  rw [e1, e1, e3, ← prod_natCast_cpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ => locEps_eq_mul χ w (a w) s

theorem norm_finEps_half {χ : HChar E} (hu : IsUnitary χ) {a : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) :
    ‖finEps χ a (1 / 2)‖ = 1 := by
  have hf := finite_mulSupport_locEps χ a (1 / 2)
  rw [finEps, finprod_eq_prod_of_mulSupport_subset _ hf.coe_toFinset.ge, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_locEps_half hu (ha w)

theorem norm_archEps {I : Type} [Fintype I] (n : I → ℤ) : ‖archEps n‖ = 1 := by
  simp [archEps]

end GlobalTheory.HeckeEpsAbs

namespace GlobalTheory.Published

open GlobalTheory.HeckeEpsAbs

theorem HeckeTateFunctionalEquation.abs (h : HeckeTateFunctionalEquation) : HeckeFunctionalEquationAbs := by
  intro E _ _ _ I _ φ hφ χ n a Λ Λ' hu hi hn ha hΛ hΛ'
  obtain ⟨Λ₀, Λ₀', h1, h2, h3⟩ := h E I φ hφ χ n a hu hi hn ha
  obtain rfl := hΛ.unique h1
  obtain rfl := hΛ'.unique h2
  refine ⟨archEps n * finEps χ a (1 / 2), ?_, fun s => ?_⟩
  · rw [norm_mul, norm_archEps, norm_finEps_half hu ha, one_mul]
  · rw [h3 s, finEps_eq χ a s]
    ring

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ContMapReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_evInf (w : InfinitePlace F) : Continuous (evInf F w) := by
  show Continuous (fun a : AF F => a.1 w)
  exact (continuous_apply w).comp continuous_fst

def phiW (w : InfinitePlace F) : AF F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp (evInf F w).toRingHom

theorem continuous_phiW (w : InfinitePlace F) : Continuous (phiW (F := F) w) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_evInf w)

theorem piInf_smul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : AE F E) :
    piInf τ (a • x) = phiW w a * piInf τ x := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  simp [piInf, compInf, infEmb, phiW, Algebra.TensorProduct.algebraMap_apply]

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf (E := E) τ) := by
  letI : Module (AF F) ℂ := Module.compHom ℂ (phiW (F := F) w)
  haveI : ContinuousSMul (AF F) ℂ := ⟨by
    show Continuous (fun p : AF F × ℂ => phiW w p.1 * p.2)
    exact ((continuous_phiW w).comp continuous_fst).mul continuous_snd⟩
  let L : AE F E →ₗ[AF F] ℂ :=
    { toFun := piInf τ
      map_add' := map_add _
      map_smul' := fun a x => by rw [piInf_smul]; rfl }
  exact IsModuleTopology.continuous_of_linearMap L

theorem contmap {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)}
    (γ : Multiplicative ℝ →* UG (cA σ) J) (hγ : Continuous γ) (w : InfinitePlace F) (τ : EmbOver E w) :
    Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  have h1 : Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E))) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))
  exact h1.matrix_map (continuous_piInf τ)

end GlobalTheory.ContMapReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponentStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitaryOneParameter_realPlaceComponent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {β : Type} [Fintype β] [DecidableEq β] {J : Matrix β β (AE F E)} (γ : Multiplicative ℝ →* UG (cA σ) J), Continuous γ → ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous (fun t : ℝ => ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf τ)) := by
  first | exact @GlobalTheory.ContMapReal.contmap | exact GlobalTheory.ContMapReal.contmap | (intros; apply GlobalTheory.ContMapReal.contmap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.PolRangeInf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def adAt (w : InfinitePlace F) (c : w.Completion) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) (Pi.single w c)

theorem piInf_adAt_same (v : InfinitePlace F) (τ : EmbOver E v) (c : v.Completion) (x : E) :
    piInf τ (adAt v c ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding v c * τ.1 x := by
  change infEmb τ (evInf F v (adAt v c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt v c) = c := by
    change (Pi.single v c : Ainf F) v = c
    exact Pi.single_eq_same v c
  rw [this, infEmb_tmul]

theorem piInf_adAt_ne {v w : InfinitePlace F} (h : v ≠ w) (τ : EmbOver E v) (c : w.Completion) (x : E) :
    piInf τ (adAt w c ⊗ₜ[F] x) = 0 := by
  change infEmb τ (evInf F v (adAt w c) ⊗ₜ[F] x) = _
  have : evInf F v (adAt w c) = 0 := by
    change (Pi.single w c : Ainf F) v = 0
    exact Pi.single_eq_of_ne h c
  rw [this, TensorProduct.zero_tmul, map_zero]

theorem ext_symm_real {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) :
    InfinitePlace.Completion.extensionEmbedding w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t) =
      (t : ℂ) := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]

theorem smul_adAt_tmul (u : AF F) (hu : evI F u = 0) (w : InfinitePlace F) (c : w.Completion) (x : E) :
    u • (adAt w c ⊗ₜ[F] x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 0 := by
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  rw [TensorProduct.smul_tmul', smul_eq_mul]
  have : u * adAt w c = 0 := by
    refine Prod.ext ?_ ?_
    · change u.1 * (adAt w c).1 = 0
      rw [hu1, zero_mul]
    · change u.2 * (adAt w c).2 = 0
      exact mul_eq_zero_of_right _ rfl
  rw [this, TensorProduct.zero_tmul]

theorem exists_at_inf_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ),
    ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  intro F E _ _ _ _ _ σ h τ z
  haveI : IsTotallyReal F := h.1
  haveI : IsTotallyComplex E := h.2.1
  have hξ : ∀ w, ∃ ξ : E, ((τ w).1 ξ).im ≠ 0 := fun w => by
    by_contra hc
    push_neg at hc
    exact IsTotallyComplex.complexEmbedding_not_isReal (τ w).1
      (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_eq_iff_im.2 (hc x)))
  choose ξ hξ using hξ
  let s : InfinitePlace F → ℝ := fun w => (z w).im / ((τ w).1 (ξ w)).im
  let r : InfinitePlace F → ℝ := fun w => (z w).re - s w * ((τ w).1 (ξ w)).re
  let cR : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  refine ⟨∑ w, (adAt w (cR w (r w)) ⊗ₜ[F] (1 : E) + adAt w (cR w (s w)) ⊗ₜ[F] ξ w), ?_, fun v => ?_⟩
  · intro u hu
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_adAt_tmul u hu, smul_adAt_tmul u hu, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single v]
      · rw [map_add (f := _), piInf_adAt_same, piInf_adAt_same]
        simp only [cR, ext_symm_real, map_one, mul_one]
        have h0 := hξ v
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, r]
          ring
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add, zero_mul,
            add_zero, s]
          field_simp
      · intro w _ hw
        rw [map_add (f := _), piInf_adAt_ne (Ne.symm hw), piInf_adAt_ne (Ne.symm hw), add_zero]
      · intro hv; exact absurd (Finset.mem_univ v) hv

end GlobalTheory.PolRangeInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValueStatement
open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : InfinitePlace F → ℂ), ∃ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := by
  first | exact @GlobalTheory.PolRangeInf.exists_at_inf_values | exact GlobalTheory.PolRangeInf.exists_at_inf_values | (intros; apply GlobalTheory.PolRangeInf.exists_at_inf_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIff
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem good_iff_labE_and_lab_conj :
    ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (GoodEmb T.Q.c (res T σ) ↔ labE σ (lab σ ρ) = tauE D ρ) ∧ lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ :=
  fun _ T _ hl ha σ ρ => ⟨GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ, GlobalTheory.ConjReading.lab_conj σ ρ⟩

end GlobalTheory.HolRead
end
