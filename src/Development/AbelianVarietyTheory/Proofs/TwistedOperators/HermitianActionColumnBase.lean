module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

variable {D : D7} (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frPinv_mul_frP : frPinv S b * frP S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := by
  unfold frPinv frP; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _

def frPinvGL : GL (Fin S.rank) (Lev.EAf D) :=
  ⟨(frPinv S b).map (eToEAf D), (frP S b).map (eToEAf D),
    by rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _),
    by rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)⟩

theorem frPinvGL_inv_val : (frPinvGL S b)⁻¹.val = (frP S b).map (eToEAf D) := rfl

def reWi (x : WO S T) : WO (reS S b) T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frP S b).map (incA D))

theorem mapA_frPinv_mul_frP : (frPinv S b).map (incA D) * (frP S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frPinv_mul_frP]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem map_frP_mul_map_frPinv : (frP S b).map (incA D) * (frPinv S b).map (incA D) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem reW_reWi (x : WO S T) : reW S T b (reWi S T b x) = x := by
  unfold reW reWi
  rw [Matrix.mul_assoc, map_frP_mul_map_frPinv, Matrix.mul_one]

theorem reWi_reW (x : WO (reS S b) T) : reWi S T b (reW S T b x) = x := by
  have h := Matrix.mul_assoc (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from x) ((frPinv S b).map (incA D))
    ((frP S b).map (incA D))
  rw [mapA_frPinv_mul_frP, Matrix.mul_one] at h
  exact h

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T := AddMonoidHom.mk' (reW S T b) (reW_add S T b)

theorem reW_nsmul (k : ℕ) (x : WO (reS S b) T) : reW S T b (k • x) = k • reW S T b x :=
  map_nsmul (reWHom S T b) k x

theorem reW_bijective : Function.Bijective (reW S T b) :=
  Function.bijective_iff_has_inverse.2 ⟨reWi S T b, reWi_reW S T b, reW_reWi S T b⟩

theorem isHalf_reW_iff (e : AE D) (x : WO (reS S b) T) : IsHalf e (reW S T b x) ↔ IsHalf e x := by
  have key : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) (AE D)),
      IsHalf e M → IsHalf e (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) M N) := by
    intro M N h i j
    simp only [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, h i l]
  constructor
  · intro h
    have h2 := key _ ((frP S b).map (incA D)) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · intro h
    exact key x _ h

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ)
    (hs : ∀ x y, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y))
    (u : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T u (reF S T b f) = reF S T b (heisO ψ S T (reW S T b u) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, hs, reW_add]

end GlobalTheory.AdSpan.ReVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def emb {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y : Mx D a b) : WO V W :=
  HMul.hMul (HMul.hMul (P.map (incA D)) (y : Matrix (Fin a) (Fin b) (AE D))) (Q.map (incA D))

def meanX {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)) (F : WO V W → ℂ)
    (x : WO V W) : ℂ :=
  ∫ y in 𝓨, F (emb V W P Q y + x) ∂μ

theorem emb_add {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (y y' : Mx D a b) :
    emb V W P Q (y + y') = emb V W P Q y + emb V W P Q y' := by
  simp only [emb, Matrix.mul_add, Matrix.add_mul]

theorem emb_zero {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : emb V W P Q (0 : Mx D a b) = 0 := by
  simp [emb]

theorem meanX_translate : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → ∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∀ y₀ : Mx D a b, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F (GlobalTheory.IsoMean.emb V W P Q y₀ + x) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F x := by
  intro D V W a b P Q hiso ψ hψ μ 𝓨 hμ F hF x hx y₀
  obtain ⟨hHaar, h𝓨, -⟩ := hμ
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e

  set f : Mx D a b → ℂ := fun y => F (emb V W P Q y + x) with hf
  have per : ∀ γ ∈ ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range, ∀ y, f (γ + y) = f y := by
    rintro _ ⟨γ, rfl⟩ y
    have hr : emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
      simp [emb, ratW, Matrix.map_mul]
    simp only [hf]
    rw [emb_add, add_assoc, hr, hF.quasi, ← hr, l2, hH0 _ _ (hiso _ _), skew, hH0 _ _ (hx _), neg_zero,
      add_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]
  have e1 : meanX V W P Q μ 𝓨 F (emb V W P Q y₀ + x) = ∫ y in 𝓨, f (y₀ + y) ∂μ := by
    unfold meanX
    congr 1; funext y
    simp only [hf, emb_add]
    congr 1; abel
  rw [e1]
  haveI : Countable D.host.E := by
    haveI : FiniteDimensional ℚ D.host.E := inferInstance
    exact (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have hmp : MeasurePreserving (fun y : Mx D a b => y₀ + y) μ μ := measurePreserving_add_left μ y₀
  have hemb : MeasurableEmbedding (fun y : Mx D a b => y₀ + y) := (MeasurableEquiv.addLeft y₀).measurableEmbedding
  haveI : Countable (Matrix (Fin a) (Fin b) D.host.E) := inferInstanceAs (Countable (Fin a → Fin b → D.host.E))
  haveI : Countable (((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range) := (Set.countable_range _).to_subtype
  rw [← hmp.setIntegral_image_emb hemb f 𝓨]
  haveI : VAddInvariantMeasure (Mx D a b) (Mx D a b) μ := ⟨fun c s _ => measure_preimage_add μ c s⟩
  have h2 := h𝓨.vadd_of_comm y₀
  rw [← Set.image_vadd] at h2
  exact h2.setIntegral_eq h𝓨 fun g y => per g g.2 y

theorem coef_integral_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (κ : Measure (Mx D a b)), κ.IsAddHaarMeasure → ∀ (g : GA D V) (h : GA D W), (∀ y : Mx D a b, actO V W g h (GlobalTheory.IsoMean.emb V W P Q y) = GlobalTheory.IsoMean.emb V W P Q y) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ y : Mx D a b, actO V W g h x = x + GlobalTheory.IsoMean.emb V W P Q y) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν) ∂κ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) f u * star (f' u) ∂ν) ∂κ := by
  intro D V W a b P Q ψ χS χT ω hω κ hκ g h hfix hunip ν 𝓕 hν h𝓕 f f' hf hf' w hw
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  have hψ := hω.std
  obtain ⟨y₀, hy₀⟩ := hunip w hw
  have key : ∀ y : Mx D a b,
      ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) u * star (ω (g, h) f' u) ∂ν =
        ∫ u in 𝓕, heisO ψ V W (w + emb V W P Q y) f u * star (f' u) ∂ν := by
    intro y
    have e : ω (g, h) (heisO ψ V W (w + emb V W P Q y) f) =
        heisO ψ V W (w + emb V W P Q (y₀ + y)) (ω (g, h) f) := by
      have hadd : actO V W g h (w + emb V W P Q y) = actO V W g h w + actO V W g h (emb V W P Q y) := by
        simp only [actO, Matrix.mul_add, Matrix.add_mul]
      rw [hω.om_heis g h _ f hf, hadd, hy₀, hfix, emb_add, add_assoc]
    rw [← e]
    exact GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ V W ν 𝓕 hν h𝓕 (ω (g, h)) (fun f hf => hω.om_pres _ f hf)
      (fun f hf => hω.om_unit ν 𝓕 hν h𝓕 _ f hf) _ f' (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf'
  rw [← integral_add_left_eq_self _ y₀]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end GlobalTheory.IsoMean

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParameters
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes GlobalTheory.Chain.ParOfNodeGap

namespace GlobalTheory.ArchRec.ParChain

theorem num_bound_two {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 1 ≤ m) (hN : 8 * m ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ 3 := by
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN' : 8 * (m : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) := by gcongr
      _ ≤ (m : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm' (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_natCast _ _
  have h2 : 60 * (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) * (60 * (m : ℝ) ^ 2) := by ring
    _ ≤ 2 * (N : ℝ) * (N : ℝ) ^ 2 := by gcongr
    _ = 2 * (N : ℝ) ^ 3 := by ring

theorem stepGap_of_gap {D : D7} (h : NodeGap D) (k : Fin D.R.m) : StepGap D k := by
  intro τ
  obtain ⟨N, hN, hgap⟩ := h
  set h₀ : ℝ := (D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1 with hh
  have hg : ∀ (i : ℕ) (h : i + 1 < D.R.m),
      h₀ ≤ (((D.hc τ).b ⟨i + 1, h⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
    intro i h
    have := hgap τ ⟨i, by omega⟩ h
    rw [hh]
    exact_mod_cast this
  have hS : NcGapGe (lamS D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hT : NcGapGe (lamT D k τ) h₀ := by
    rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hs
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ _ _).1 hy
    exact le_val_sub _ hg _ _ a b hs
  have hr : ∀ j, j ≤ D.R.m → D.R.rankY j ≤ N := fun j hj => by
    have := Nat.mul_le_mul_right D.R.t hj
    unfold Ranks.rankX' at hN
    unfold Ranks.rankY
    omega
  have h3 : 8 * D.R.m ≤ N := by
    have h8 : 8 ≤ D.R.t := by
      have := D.R.rank_add_five_le; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have := Nat.mul_le_mul_left D.R.m h8
    unfold Ranks.rankX' at hN
    omega
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have h1 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ^ 3 < h₀ := by
    have h2 : (D.R.rankY ((k : ℕ) + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr _ k.2
    have h3 := pow_le_pow_left₀ (by positivity) h2 3
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
    linarith
  have h2 := num_bound_two (minSig_lamS_le k τ) (hr _ k.2.le) (by have := D.R.two_le_m; omega) h3
  exact ⟨fun x hx y hy hs => h1.trans_le (hS x hx y hy hs), fun x hx y hy hs => h1.trans_le (hT x hx y hy hs),
    fun x hx y hy hs => le_trans (by linarith) (hS x hx y hy hs)⟩

theorem parChain : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  intro D k τ
  obtain ⟨al, be, ga, de, hA, hb, h1, h2⟩ := exists_lists_chain k τ
  refine ⟨al, be, ga, de, ⟨hA, hb, fun hG => ?_⟩, eq_signed_iff.2 h1, eq_signed_iff.2 h2⟩
  have h := stepGap_of_gap hG k τ
  have hr : D.R.rankY ((k : ℕ) + 1) = D.R.rankY k + D.R.t := by simp only [Ranks.rankY]; ring
  rw [hr] at h
  refine (hypG_iff hA.2.2.2.2.2.2.1 (h1 ▸ card_lamS k τ)).2 ?_
  rwa [← h1, ← h2]

end GlobalTheory.ArchRec.ParChain

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParametersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_centred_block_parameters : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  first | exact @GlobalTheory.ArchRec.ParChain.parChain | exact GlobalTheory.ArchRec.ParChain.parChain | (intros; apply GlobalTheory.ArchRec.ParChain.parChain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.LowerTower

open GlobalTheory.SmallerSource GlobalTheory.FockAlg

theorem lamA_mem (al be ga de : List ℚ) (a : Ix (al.length + be.length) (ga.length + de.length)) :
    lamA al be ga de a ∈ al ++ be ++ ga ++ de := by
  rw [List.append_assoc (al ++ be)]
  cases a with
  | inl i => exact List.mem_append_left _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) i)
  | inr j => exact List.mem_append_right _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) j)

theorem tensNo_first (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hpq : 1 ≤ p + q) (lam : Ix p q → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair r s) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair r s) (blattner lam) a ≤ 0))
    (hno : ∀ μ', ¬ JointShape p q r s (blattner lam) μ') :
    TensNo (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) := by
  intro MM f hf
  by_contra hne
  obtain ⟨hadm, hirr⟩ := discrete_series_gk_admissible_irreducible X h5 hpq lam
  obtain ⟨hone, -, hcone⟩ := hD p q lam hlam
  have hex : ∃ v, IsHW (X.ds p q lam).HK.act (blattner lam) v := by
    have hnb : hwSub (X.ds p q lam).HK.act (blattner lam) ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hone
      exact zero_ne_one hone
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    exact ⟨v, hv0, hv⟩
  have hflow := GlobalTheory.T.degW_blattner_le_of_blattnerCone p q (X.ds p q lam).HK lam (cPair r s) θ hcone hsign
  obtain ⟨⟨μ, P, hPJ, hP1, hP2, -⟩, -⟩ :=
    GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub p q r s (X.ds p q lam).HK MM f hirr hadm hf hne (blattner lam) hex hflow
  have hbot := ((GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 (blattner lam) μ).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 (blattner lam) ⊓ hwSub (X.fock p q r s).act2 μ ⊓
      Submodule.span ℂ (X.fock p q r s).J :=
    ⟨⟨hP1.2, hP2.2⟩, Submodule.subset_span hPJ⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hP1.1 hmem

theorem tensNo_second (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam)) :
    TensNo (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam) := by
  intro MM f hf
  set c := TensorProduct.comm ℂ (X.ds r s lam).HK.V MM.V with hc
  have hcm : ∀ (A : Module.End ℂ (X.ds r s lam).HK.V) (B : Module.End ℂ MM.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hg : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK ((c : _ →ₗ[ℂ] _) ∘ₗ f) := by
    refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct1 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
    · have := LinearMap.congr_fun (hf.1 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct2 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
  have h0 := intw_eq_zero X (GlobalTheory.JointHarm.fock_polynomials X) hD h5 hrs lam hlam θ hsign hno MM _ hg
  refine LinearMap.ext fun P => ?_
  have : c (f P) = 0 := LinearMap.congr_fun h0 P
  exact c.map_eq_zero_iff.1 this

theorem no_map_lower : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  intro X hD h5 t al be ga de hA i hi
  have ht : 1 ≤ t := hA.1
  have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  obtain ⟨-, hpar, hpar', hsign, hsign'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨hno, -, hno'⟩ := GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi
  refine ⟨fun hr hs => ?_, fun hbig hp hq => ?_⟩
  · refine tensNo_first X hD h5 (by omega) _ hpar 0 ?_ (hno hr hs)
    rw [cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith
  · refine tensNo_second X hD h5 (by omega) _ hpar' ((t : ℚ) / 2) ?_ (hno' (.inl ?_) hp hq).1
    · rw [cPair_sub hp hq]
      exact hsign'
    · rintro ⟨a, ha⟩
      have := hbig _ (lamA_mem al be ga de a)
      rw [ha, abs_of_nonneg (by positivity)] at this
      linarith

end GlobalTheory.LowerTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoThetaTensorIntertwinerLowerTowerMembersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noThetaTensorIntertwiner_lowerTowerMembers : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  first | exact @GlobalTheory.LowerTower.no_map_lower | exact GlobalTheory.LowerTower.no_map_lower | (intros; apply GlobalTheory.LowerTower.no_map_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDef
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAct

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

def ActsLin (θ : InfFam D) (M : DSModel V S) (k : GA D V) : Prop :=
  ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ),
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T)

theorem actsLin_one (M : DSModel V S) : ActsLin θ M 1 := by
  refine ⟨LinearMap.id, ?_⟩
  intro J χ T _ g
  rw [mul_one]
  rfl

theorem actsLin_mul {M : DSModel V S} {a b : GA D V} (ha : ActsLin θ M a) (hb : ActsLin θ M b) :
    ActsLin θ M (a * b) := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  refine ⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩
  calc evAt M (g * (a * b)) T = evAt M ((g * a) * b) T := by rw [mul_assoc]
    _ = φb (evAt M (g * a) T) := hφb J χ T hT (g * a)
    _ = φb (φa (evAt M g T)) := by rw [hφa J χ T hT g]

theorem actsLin_atTau {M : DSModel V S} (hM : AllPlus M) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ActsLin θ M (atTau θ V τ u) := by
  classical
  have htop : M.sm τ = ⊤ := (AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1
  let A : M.sm τ →ₗ[ℂ] M.sm τ :=
    (M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)
  let F : ∀ i, M.sm i →ₗ[ℂ] M.sm i := Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A
  refine ⟨MultilinearMap.compLinearMapₗ F, ?_⟩
  intro J χ T hT g
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT
  ext v
  have hv : (fun i => F i (v i)) = Function.update v τ (A (v τ)) := by
    funext i
    by_cases h : i = τ
    · subst h
      simp [F]
    · simp [F, h]
  have hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ) := rfl
  have key := congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g
  rw [evAt_apply]
  simp only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [evAt_apply, hv, key]
  rfl

theorem real_acts : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  intro D θ V S M hθ hM k hk
  classical
  obtain ⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k := ⟨_, hLarch k, hLinv k hk⟩
  have haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := hUa
  have h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    intro τ
    simp [Formalism.QuantumDeterminants.UH]
  have hL1 : L 1 = 1 := by
    have h := hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)
    rw [mul_one] at h
    calc L 1 = (L 1)⁻¹ * (L 1 * L 1) := by group
      _ = (L 1)⁻¹ * L 1 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hpart : ∀ s : Finset D.what₂.Tau,
      ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1 := by
        funext τ
        simp
      rw [he, hL1]
      exact actsLin_one M
    | insert x s hx ih =>
      have hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ ∈ s
        · simpa [h] using haU τ
        · simpa [h] using h1U τ
      have hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ = x
        · subst h
          simpa using haU τ
        · simpa [Pi.mulSingle_apply, h] using h1U τ
      have hsplit : (fun τ => if τ ∈ insert x s then a τ else 1)
          = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1 := by
        funext τ
        by_cases h : τ = x
        · subst h
          simp [hx]
        · simp [h, Pi.mulSingle_apply]
      rw [hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]
      exact actsLin_mul (actsLin_atTau hM x (haU x)) ih
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a := by
    funext τ
    simp
  have := hpart Finset.univ
  rw [hall, hkL] at this
  exact this

end GlobalTheory.RealAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointActsLinearlyOnMultiplicityValuesPosDefStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoint_acts_linearly_on_multiplicity_values_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  first | exact @GlobalTheory.RealAct.real_acts | exact GlobalTheory.RealAct.real_acts | (intros; apply GlobalTheory.RealAct.real_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ThetaL2InnerProduct

open GlobalTheory.OrientedHeis GlobalTheory.Size Filter
open scoped Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun a _ hf => GlobalTheory.OrientedHeis.theta_smul a hf

theorem ipTh_eq (f f' : WO S T → ℂ) : ipTh μ 𝓕 f f' = GlobalTheory.Ker.ipO μ 𝓕 f f' := rfl

theorem bound_near (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) : ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ w, ‖ω p f w‖ ≤ C := by
  obtain ⟨K, hK, hKγ⟩ := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.2
  have hcont : Continuous fun q : (GA D S × GA D T) × WO S T => ω q.1 f q.2 :=
    GlobalTheory.ThetaJointCont.continuous_om_oriented hω hf
  have hc0 : ContinuousOn (fun w : WO S T => ω p₀ f w) K :=
    (hcont.comp (by fun_prop : Continuous fun w : WO S T => (p₀, w))).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc0
  refine ⟨M + 1, ?_⟩
  have hev : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖ω p f y‖ < M + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hlt : ‖ω p₀ f y‖ < M + 1 := lt_of_le_of_lt (hM y hy) (lt_add_one M)
    exact hcont.norm.continuousAt.eventually_lt continuousAt_const hlt
  filter_upwards [hev] with p hp w
  obtain ⟨γ, hγ, hγK⟩ := hKγ w
  rw [← theta_norm_periodic hω.std (hω.om_pres p f hf) γ hγ w]
  exact (hp _ hγK).le

theorem continuousOn_ip (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    {γ : X → GA D S × GA D T} {U : Set X} (hγ : ContinuousOn γ U) {F E : WO S T → ℂ}
    (hF : IsThetaFunO ψ S T F) (hE : IsThetaFunO ψ S T E) :
    ContinuousOn (fun x => ipTh μ 𝓕 (ω (γ x) F) E) U := by
  intro x₀ hx₀
  obtain ⟨C, hC⟩ := bound_near hω hF (γ x₀)
  obtain ⟨CE, hCE⟩ := theta_bounded hω.std hE
  have hfin : μ 𝓕 ≠ ⊤ := (measure_dom hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  unfold ipTh
  refine continuousWithinAt_of_dominated (bound := fun _ => C * CE) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (integrableOn_mul_conj hω.std hμ h𝓕 (hω.om_pres (γ x) F hF) hE).aestronglyMeasurable
  · have ht : Tendsto γ (𝓝[U] x₀) (𝓝 (γ x₀)) := hγ x₀ hx₀
    filter_upwards [ht.eventually hC] with x hx
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hx w) (hCE w) (norm_nonneg _) ((norm_nonneg _).trans (hx w))
  · refine Filter.Eventually.of_forall fun w => ?_
    exact ((hω.om_cont F hF w).continuousAt.comp_continuousWithinAt (hγ x₀ hx₀)).mul continuousWithinAt_const

theorem weaklyContinuous_unitaryAction_of_realUnitaryHom (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} {ι : Type} (G : Mn n) (γ : Mn n → GA D S × GA D T)
    (h1 : γ 1 = 1) (hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, γ (g * g') = γ g * γ g')
    (hc : ContinuousOn γ (Formalism.QuantumDeterminants.UH G)) (pt : MvPolynomial ι ℂ →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (hd : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P, ∃ F', DerAll ψ ω (fun t => γ (NormedSpace.exp (t • X))) (pt P) F') :
    L2UnitaryRepresentationData G (fun g F => ω (γ g) F) pt (ipTh μ 𝓕) (thetaSpace ψ S T) := {
  mem := hpt
  pt_lin := fun z P Q => by rw [map_add (f := _), map_smul]
  ip_lin := fun z F hF F' hF' E hE => by
    rw [ipTh_eq, ipTh_eq, ipTh_eq, ipO_add_left hω.std hμ h𝓕 ((thetaSpace ψ S T).smul_mem z hF) hF' hE,
      ipO_smul_left]
  ip_symm := fun F _ E _ => by rw [ipTh_eq, ipTh_eq, ipO_conj]
  ip_pos := fun F hF hne => by
    have htheta : IsThetaFunO ψ S T F := hF
    have hc : Continuous F := htheta.cont
    have h0 : GlobalTheory.Ker.ipO μ 𝓕 F F ≠ 0 := fun h => hne ((ipO_self_eq_zero_iff hω.std hμ h𝓕 hF).1 h)
    rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc] at h0
    rw [ipTh_eq, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc, Complex.ofReal_re]
    exact lt_of_le_of_ne (sq_nonneg _) (fun h => h0 (by rw [← h]; simp))
  stable := fun g _ F hF => hω.om_pres _ F hF
  lin := fun g _ z F _ F' _ => by simp only [map_add (f := _), map_smul]
  one := fun F _ => by
    show ω (γ 1) F = F
    rw [h1, map_one]
    rfl
  mul := fun g hg g' hg' F _ => by
    show ω (γ (g * g')) F = ω (γ g) (ω (γ g') F)
    rw [hmul g hg g' hg', map_mul]
    rfl
  unit := fun g _ F hF E hE => by
    show ipTh μ 𝓕 (ω (γ g) F) (ω (γ g) E) = ipTh μ 𝓕 F E
    rw [ipTh_eq, ipTh_eq, ipO_om hω hμ h𝓕 hF hE (γ g)]
  cont := fun F hF E hE => by
    have : FirstCountableTopology (Mn n) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
    exact continuousOn_ip hω hμ h𝓕 hc hF hE
  der := fun X hX P P' hPP' E hE => by
    obtain ⟨F', hF'1, hF'2⟩ := hd X hX P
    have heq : F' = pt P' := by
      funext z
      have hz := hF'1 1 z
      simp only [one_mul, map_one, one_apply_eq_self] at hz
      exact hz.unique (hPP' z)
    have hder := hF'2 μ 𝓕 hμ h𝓕 E hE
    rw [heq] at hder
    exact hder }

theorem exists_l2_unitary_theta_of_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  intro D ψ θ S T χS χT ω τ hθ hω frS εS frT εT aS aT pt hpt hL μ 𝓕 hμ h𝓕
  refine ⟨thetaSpace ψ S T, ?_, ?_⟩
  · have hcS := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ S τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D S τ) (fun g => (atTau θ S τ g, (1 : GA D T)))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ]; rfl)
      (fun g hg g' hg' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hg hg', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun X hX P => ⟨_, hL.1 X hX P⟩)
  · have hcT := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D T τ) (fun h => ((1 : GA D S), atTau θ T τ h))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ]; rfl)
      (fun h hh h' hh' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hh hh', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun Y hY P => ⟨_, hL.2 Y hY P⟩)

end GlobalTheory.ThetaL2InnerProduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnThetaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceGroups_act_unitarily_weakly_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  first | exact @GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | exact GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | (intros; apply GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain <;> assumption)
end
end
