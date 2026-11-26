module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NcardRationalPointsTranslatedCompactLePow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl UA)
open Formalism.L2.Theta (GA GfC finHom frameMat)
open Formalism.IndefR.Lev (EAf finE)
open Formalism.IndefR.Datum (IsSelfDualC)
open Formalism.UG (cT hform)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsomCorrection

section Algebra

variable {A : Type} [CommRing A] (σ : A →+* A)

theorem cT_mul_rect {l m n : ℕ} (M : Matrix (Fin l) (Fin m) A) (N : Matrix (Fin m) (Fin n) A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  rw [cT, Matrix.map_mul, transpose_mul]
  rfl

theorem gram_of_form {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x : Matrix (Fin m) (Fin n) A)
    (h : ∀ i j, hform σ J' (x *ᵥ Pi.single i 1) (x *ᵥ Pi.single j 1) = J i j) :
    cT σ x * J' * x = J := by
  ext i j
  rw [← h i j]
  simp only [hform, mulVec_single_one, Matrix.mul_apply, cT, transpose_apply, map_apply, col_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite σ]

theorem exists_unitary {m n : ℕ} (J' : Matrix (Fin m) (Fin m) A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Matrix (Fin m) (Fin n) A) (y' : Matrix (Fin n) (Fin m) A) (h1 : y * y' = 1) (h2 : y' * y = 1)
    (hb : Function.Surjective x.mulVec) (hx : cT σ x * J' * x = J) (hy : cT σ y * J' * y = J) :
    ∃ g : GL (Fin m) A, cT σ g.1 * J' * g.1 = J' ∧ g.1 * y = x := by
  have hu : IsUnit (x * y') := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro v
    obtain ⟨w, rfl⟩ := hb v
    exact ⟨y *ᵥ w, by rw [mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]⟩
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [hu.unit_spec, cT_mul_rect]
    have e : cT σ y' * cT σ y = 1 := by
      rw [← cT_mul_rect, h1, cT, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]
    calc cT σ y' * cT σ x * J' * (x * y') = cT σ y' * (cT σ x * J' * x) * y' := by simp only [Matrix.mul_assoc]
      _ = (cT σ y' * cT σ y) * J' * (y * y') := by rw [hx, ← hy]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [e, h1, Matrix.one_mul, Matrix.mul_one]
  · rw [hu.unit_spec, Matrix.mul_assoc, h2, Matrix.mul_one]

end Algebra

variable {D : D7}

theorem exists_finE (V : HSp D) (g : GL (Fin V.rank) (EAf D)) (hg : g ∈ UA D.sp.cm V.gram) :
    ∃ k ∈ GfC V, finE V k = g := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨g, hg⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 b.1
  refine ⟨⟨k, (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ b.2⟩⟩, k1, ?_⟩
  have e := congrArg Subtype.val hb
  have e2 := GlobalTheory.Mass.coe_swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram b
  refine Eq.trans ?_ (e2.symm.trans e)
  exact congrArg (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D)) k2

theorem mA_mul (X Y Z : HSp D) (f : X.V →ₗ[D.host.E] Y.V) (g : Y.V →ₗ[D.host.E] Z.V) :
    mA Z Y g * mA Y X f = mA Z X (g.comp f) := by
  rw [mA, mA, mA, ← Matrix.map_mul, frameMat, frameMat, frameMat, LinearMap.toMatrix_comp X.frame Y.frame Z.frame]

theorem mA_id (X : HSp D) : mA X X LinearMap.id = 1 := by
  rw [mA, frameMat, LinearMap.toMatrix_id, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem vA_frame (X : HSp D) (i : Fin X.rank) : vA X (X.frame i) = Pi.single i 1 := by
  funext j
  have : Formalism.L2.Herm.crd X (X.frame i) j = X.frame.repr (X.frame i) j := rfl
  rw [vA, this, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm, RingHom.map_one]
  · rw [if_neg h, if_neg (Ne.symm h), RingHom.map_zero]

theorem gram_mA (Y Y' : HSp D) (f : Y.V →ₗ[D.host.E] Y'.V) (hf : HSpace.IsIsomEmb Y Y' f) :
    HMul.hMul (HMul.hMul (cT (cjA D) (mA Y' Y f)) (Y'.gram.map (inc D))) (mA Y' Y f) = Y.gram.map (inc D) := by
  refine gram_of_form _ _ _ _ fun i j => ?_
  rw [← vA_frame, ← vA_frame, mA_mulVec_vA, mA_mulVec_vA, ← hA_eq, hA_vA, HSpace.hD, hf]
  rfl

theorem correction_of_transport : ∀ D : D7, TransportSt D → CorrectionSt D := by
  intro D hT Y Y' io hio Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  have hr : Y.rank = Y'.rank := by rw [← Y.rank_eq, ← Y'.rank_eq, io.finrank_eq]
  obtain ⟨⟨x, hx⟩, -⟩ := hT Y Y' hr Λ Λ' hΛ hΛ' S hS n be be' hbe hbe'
  obtain ⟨g, hg, hgx⟩ := exists_unitary (cjA D) (Y'.gram.map (inc D)) (Y.gram.map (inc D)) x
    (mA Y' Y io.toLinearMap) (mA Y Y' io.symm.toLinearMap)
    (by rw [mA_mul, LinearEquiv.comp_symm, mA_id]) (by rw [mA_mul, LinearEquiv.symm_comp, mA_id]) hx.1.1.2
    (gram_of_form _ _ _ _ fun i j => (hx.1.2 _ _).trans (hform_single _ _ i j)) (gram_mA Y Y' _ hio)
  obtain ⟨k, hk, e⟩ := exists_finE Y' g hg
  refine ⟨k, hk, ?_⟩
  rw [e, hgx]
  exact hx

end GlobalTheory.AdIsomCorrection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.correctionSt_of_transportSt : ∀ D : D7, TransportSt D → CorrectionSt D := by
  first | exact @GlobalTheory.AdIsomCorrection.correction_of_transport | exact GlobalTheory.AdIsomCorrection.correction_of_transport | (intros; apply GlobalTheory.AdIsomCorrection.correction_of_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
set_option autoImplicit false

namespace GlobalTheory.HeckePointLaw

theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  heckePointLaws_of_transport GlobalTheory.T.heckeIsogeny_thetaGenerator_transport

end GlobalTheory.HeckePointLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

variable {D : D7}

def resT (PP : Pl D.host.E) (x : EAf D) : kP PP :=
  if hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ else 0

def hT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
    (Formalism.L2.SG.HidaSetting.hA X.B.I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) x)
      (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) h.symm) y))

def argT (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (M : GL (Fin (Yc D 0).rank) (EAf D)) : EAf D :=
  (∑ a, hT X h (f0T X h a) (Matrix.mulVec M.val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) +
    ∑ i : Fin D.R.k, if hi : i.1 + 1 < D.R.k then
      hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h ⟨i.1 + 1, hi⟩)) else 0

def sideAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) : Bool :=
  decide (GlobalTheory.StdFrames.cpt PP (ewT X h) = 1)

def wA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem conjPrime_asIdeal (PP : Pl D.host.E) :
    (GlobalTheory.IdemSupport.cP PP).asIdeal = PP.asIdeal.map (GlobalTheory.IdemSupport.cO D) := by
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, Ideal.mem_map_of_equiv]
  constructor
  · intro hx
    exact ⟨GlobalTheory.IdemSupport.cO D x, hx, GlobalTheory.IdemSupport.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [GlobalTheory.IdemSupport.cO_cO]
    exact hy

def conjRes (PP : Pl D.host.E) : kP PP ≃+* kP (GlobalTheory.IdemSupport.cP PP) :=
  Ideal.quotientEquiv _ _ (GlobalTheory.IdemSupport.cO D) (conjPrime_asIdeal PP)

end GlobalTheory.SeeConjChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.GKExtensionToSmoothVectors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gkExtension :
    GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D :=
  fun h₁ h₂ D => ⟨GlobalTheory.T.gKModuleMapCuspForms_extends_multiplicitySpace h₁ h₂ D, GlobalTheory.KFiniteDetermined.restrInj D⟩

end GlobalTheory.GKExtensionToSmoothVectors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D := by
  first | exact @GlobalTheory.GKExtensionToSmoothVectors.gkExtension | exact GlobalTheory.GKExtensionToSmoothVectors.gkExtension | (intros; apply GlobalTheory.GKExtensionToSmoothVectors.gkExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjGroup

open Classical Formalism.L2.SG.HidaSetting

abbrev II (D : D7) : AutInst := Formalism.L2.SG.InstExistsPf.instOf D

section Red
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def redV (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) : Fin n → kP PP :=
  fun i => if h : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _).mulVec v i ∈
      Formalism.L2.Herm.intAf F E then resS F PP ⟨_, h⟩ else 0

end Red

def basisOrRevDual {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then b else fun i => bd (Fin.rev i)

def dualOrRevBasis {M : Type} {k : ℕ} (w : Bool) (b bd : Fin k → M) : Fin k → M := if w then bd else fun i => b (Fin.rev i)

def LocAt {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D))
    (ew : EAf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool) : Prop :=
  ((g : 𝓞 D.host.E) ∈ PP.asIdeal) ∧
    (∀ h1 : ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, resS D.host.F PP ⟨ew, h1⟩ = if w then 1 else 0) ∧
    (∀ h1 : sigA (II D) ew ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      resS D.host.F PP ⟨sigA (II D) ew, h1⟩ = if w then 0 else 1) ∧
    RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0)

end GlobalTheory.SeeConjGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
noncomputable section

open GlobalTheory.KernelSeminorm GlobalTheory.Size GlobalTheory.FockCompare GlobalTheory.ThetaGrowth
open scoped NNReal

namespace GlobalTheory.WeilSobolev

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem sobO_om_le (hom : IsWeilDatumO ψ S T χS χT om) (hc : Chart θ σ) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (g : GA D S) (h : GA D T) {ρ : ℝ≥0}
    (hρ : ∀ a, ‖mov θ g⁻¹ h⁻¹ (letter a)‖ ≤ ρ) (d : ℕ) :
    ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (om (g, h) f) ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d * sobO ψ θ μ 𝓕 d f := by
  induction d with
  | zero =>
    intro f hf
    rw [sobO_zero, sobO_zero, l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf, pow_zero, one_mul]
  | succ d ih =>
    intro f hf
    have e1 : sobO ψ θ μ 𝓕 (d + 1) (om (g, h) f) =
        l2O μ 𝓕 (om (g, h) f) + ∑ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) :=
      Translate.wordSum_succ _ _ d _
    have e2 : ∀ a, sobO ψ θ μ 𝓕 d (heisDer ψ θ a (om (g, h) f)) ≤
        ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
          (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d *
        (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * sobO ψ θ μ 𝓕 (d + 1) f) := by
      intro a
      rw [← dv_letter hc hom.std a, dv_om hom hc g h (letter a) hf]
      refine (ih _ (theta_dv hc hom.std _ hf)).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      exact sobO_dvL_le hc hom.std d (hρ a) ⟨f, hf⟩
    have e3 : l2O μ 𝓕 (om (g, h) f) ≤ sobO ψ θ μ 𝓕 (d + 1) f := by
      rw [l2O_om_apply_eq_of_isThetaFunO hom hμ h𝓕 hf]
      exact (sobO_zero (ψ := ψ) (θ := θ)).ge.trans (sobO_mono (Nat.zero_le _))
    rw [e1]
    refine (add_le_add e3 (Finset.sum_le_sum fun a _ => e2 a)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h1 : (1 : ℝ≥0∞) ≤ ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d :=
      one_le_pow₀ (ENNReal.one_le_coe_iff.2 le_self_add)
    rw [pow_succ]
    generalize sobO ψ θ μ 𝓕 (d + 1) f = s at *
    generalize ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) *
        (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ) : ℝ≥0) : ℝ≥0∞) ^ d = q at *
    calc s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s))
        ≤ q * s + (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : ℝ≥0∞) *
          (q * (((Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) * s)) :=
          add_le_add (le_mul_of_one_le_left' h1) le_rfl
      _ = _ := by push_cast; ring

theorem sobO_weil_le_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  intro D ψ θ hθ ε M X χ χ' ω hω Φ hΦ C₁ hC₁ μ 𝓕 hμ k
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hψ : IsStdChar D ψ (-1) := hω.std
  obtain ⟨B, hB⟩ := (hC₁.image (continuous_ofSgn_symm ε M)).exists_bound_of_continuousOn
    (GlobalTheory.RatCount.continuous_normInf hθ (sgn ε M)).continuousOn
  obtain ⟨CT, hCT⟩ := (GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ X).2
  obtain ⟨L, hL, hL0⟩ : ∃ L : ℝ, (∀ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ ≤ L) ∧ 0 ≤ L :=
    ⟨∑ a, ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖,
      fun a => Finset.single_le_sum (f := fun a => ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ a), by positivity⟩
  obtain ⟨c0, hc0, hc0'⟩ : ∃ c0 : ℝ, c0 = |CT| * L * |B| ∧ 0 ≤ c0 := ⟨_, rfl, by positivity⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, K = (Fintype.card (D.what₂.Tau × Fin X.rank × Fin (sgn ε M).rank × Bool) : ℝ≥0) :=
    ⟨_, rfl⟩
  refine ⟨k, (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal,
    by positivity, fun y hy h => ?_⟩
  have hy' : (ofSgn ε M).symm y ∈ (ofSgn ε M).symm '' C₁ := ⟨y, hy, rfl⟩
  have eω : ω (y, h) Φ = (ω.toSgn ε) ((ofSgn ε M).symm y, h) Φ := by
    simp [WRep.toSgn]
  have hH : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ X h
  obtain ⟨H, hH'⟩ : ∃ H : ℝ, H = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) := ⟨_, rfl⟩
  rw [← hH'] at hH ⊢
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = c0 * H := ⟨⟨c0 * H, by positivity⟩, rfl⟩
  have hρ : ∀ a, ‖mov θ ((ofSgn ε M).symm y)⁻¹ h⁻¹ (letter a)‖ ≤ ρ := by
    intro a
    refine (norm_mov_le_normInf _ _ _).trans ?_
    rw [inv_inv, GlobalTheory.RatCount.normInf_inv]
    have h1 : normInf θ X h ≤ |CT| * H := (hCT h).trans (by rw [← hH']; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
    have h2 : normInf θ (sgn ε M) ((ofSgn ε M).symm y) ≤ |B| :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB _ hy').trans (le_abs_self _))
    have h3 := GlobalTheory.RatCount.normInf_nonneg θ X h
    have h4 := GlobalTheory.RatCount.normInf_nonneg θ (sgn ε M) ((ofSgn ε M).symm y)
    rw [hρdef]
    calc normInf θ X h * ‖(letter a : GlobalTheory.FockCompare.RW X (sgn ε M))‖ * normInf θ (sgn ε M) ((ofSgn ε M).symm y)
        ≤ (|CT| * H) * L * |B| := by gcongr; exact hL a
      _ = c0 * H := by rw [hc0]; ring
  have key := GlobalTheory.WeilSobolev.sobO_om_le hω hc hμ.1 hμ.2.1 ((ofSgn ε M).symm y) h hρ k Φ hΦ
  rw [eω]
  have hs := sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΦ k
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hs) key).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hK]
  have hQ : ((1 + K * (K * ρ) : ℝ≥0) : ℝ) ≤ (1 + (K : ℝ) * K * c0) * H := by
    push_cast
    rw [hρdef]
    have : (0 : ℝ) ≤ K := K.2
    nlinarith [mul_nonneg (mul_nonneg this this) hc0']
  calc _ ≤ ((1 + (K : ℝ) * K * c0) * H) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (NNReal.coe_nonneg _) hQ k) ENNReal.toReal_nonneg
    _ = (1 + (K : ℝ) * K * c0) ^ k * (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k Φ).toReal * H ^ k := by
        rw [mul_pow]; ring

end GlobalTheory.WeilSobolev

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  first | exact @GlobalTheory.WeilSobolev.sobO_weil_le_height | exact GlobalTheory.WeilSobolev.sobO_weil_le_height | (intros; apply GlobalTheory.WeilSobolev.sobO_weil_le_height <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPow
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.LevelSupBound

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm GlobalTheory.SupremumSobolevWords GlobalTheory.HeisTaylor
open scoped NNReal Topology

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem word_theta_level (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (h0 : u.map (infPart D) = 0) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
      heisO ψ S T u f = f → IsThetaFunO ψ S T (wordAct (heisDer ψ θ) l f) ∧
        heisO ψ S T u (wordAct (heisDer ψ θ) l f) = wordAct (heisDer ψ θ) l f := by
  intro l
  induction l with
  | nil => exact fun hf hu => ⟨hf, hu⟩
  | cons a l ih =>
    intro f hf hu
    obtain ⟨h1, h2⟩ := ih hf hu
    have e : wordAct (heisDer ψ θ) (a :: l) f = dv θ σ S T (letter a) (wordAct (heisDer ψ θ) l f) := by
      rw [dv_letter hc hψ]
      rfl
    rw [e]
    exact ⟨theta_dv hc hψ _ h1, dv_level hc hψ _ h0 h2⟩

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (p : ℕ) (f : WO S T → ℂ),
      sobO ψ θ μ 𝓕 p (wordAct (heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (p + l.length) f := by
  intro l
  induction l with
  | nil => intro p f; simp [wordAct]
  | cons a l ih =>
    intro p f
    refine (sobO_heisDer_le p a).trans ?_
    refine (ih (p + 1) f).trans_eq ?_
    congr 1
    simp only [List.length_cons]
    omega

theorem nsmul_fin {u : WO S T} (hinf : u.map (infPart D) = 0) (n : ℕ) : (n • u).map (infPart D) = 0 := by
  ext i j
  have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
  exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))

theorem pointwise (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T))
    (hK₀ : IsCompact K₀) :
    ∃ C : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ y : WO S T,
        ‖f y‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ Module.finrank ℝ (RW T S)) *
          sobO ψ θ μ 𝓕 (Module.finrank ℝ (RW T S)) f := by
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  set N := Module.finrank ℝ (RW T S) with hN
  let b : Module.Basis (Fin N) ℝ (RW T S) := Module.finBasis ℝ (RW T S)
  obtain ⟨c, hcube⟩ := cube_dilate_bound_at hψ hc b h0 hK₀
  let card : ℝ≥0 := Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
  let Q : ℝ≥0 := 1 + card * ‖fun i => b i‖₊
  refine ⟨NNReal.sqrt (4 ^ N * c) * Q ^ N, fun μ 𝓕 hm n hn f hf hl y => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, sobO ψ θ μ 𝓕 N f = s :=
    ⟨_, (ENNReal.coe_toNNReal (sobO_ne_top hψ hθ hm.1 hm.2.1 hf N)).symm⟩
  let ρ : ℝ≥0 := (n : ℝ≥0) * ‖fun i => b i‖₊
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ (ρ : ℝ)) ∧ F = (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • n • b i)) A (c * ((1 + card * ρ) ^ N * s : ℝ≥0) ^ 2) y
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ f ⟨[], le_rfl, by simp, rfl⟩
  · have hQ : 1 + card * ρ ≤ Q * n := by
      have h1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn
      calc 1 + card * ρ ≤ n + card * ρ := add_le_add h1 le_rfl
        _ = Q * n := by simp only [Q, ρ]; ring
    have key' : (‖f y‖₊ : ℝ≥0) ^ 2 ≤ 4 ^ N * (c * ((1 + card * ρ) ^ N * s) ^ 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      simpa using key
    have hb : (‖f y‖₊ : ℝ≥0) ≤ NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s := by
      rw [← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero]
      refine key'.trans ?_
      have e : (NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s) ^ 2 = 4 ^ N * (c * ((Q * n) ^ N * s) ^ 2) := by
        rw [mul_assoc, mul_assoc, mul_pow (NNReal.sqrt _), NNReal.sq_sqrt]
        ring_nf
      rw [e]
      gcongr
    rw [hs, enorm_eq_nnnorm]
    have e2 : ENNReal.ofReal (((NNReal.sqrt (4 ^ N * c) * Q ^ N : ℝ≥0) : ℝ) * (n : ℝ) ^ N) =
        ((NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [e2, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hb
  · rintro p _ ⟨l, h1, h2, rfl⟩
    refine ⟨(wd l).2.cont, fun i => ⟨_, ⟨l ++ [n • b i], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (n • b i) (wd l).2⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        refine norm_nsmul_le.trans ?_
        simp only [ρ, NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => b i) i) (Nat.cast_nonneg n)
    · simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    refine (hcube μ 𝓕 hm n hn _ (wd l).2 (fun u hu hinf => ?_) y).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2) c.coe_nonneg)
    · exact words_level hc hψ (nsmul_fin hinf n) l ⟨f, hf⟩ (hl u hu hinf)
    · refine ENNReal.toReal_le_coe_of_le_coe ((l2O_foldl_dvL_le_pow_mul_sobO hc hψ N l (by simpa using h1) h2 _).trans ?_)
      rw [hs, ← ENNReal.coe_pow, ← ENNReal.coe_mul]

theorem supN_word_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  intro D ψ hψ θ hθ V X K₀ h0 hK₀ μ 𝓕 hm
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨C, hC⟩ := pointwise (S := V) (T := X) hψ hθ h0 hK₀
  refine ⟨Module.finrank ℝ (RW X V), Module.finrank ℝ (RW X V), C, C.2, fun n hn f hf hl l => iSup_le fun y => ?_⟩
  have hw := fun u hu hinf => word_theta_level hc hψ (nsmul_fin (S := V) (T := X) hinf n) l hf (hl u hu hinf)
  have ht : IsThetaFunO ψ V X (wordAct (heisDer ψ θ) l f) :=
    (hw 0 (mem_of_mem_nhds h0) (Matrix.map_zero _ (map_zero _))).1
  refine (hC μ 𝓕 hm n hn _ ht (fun u hu hinf => (hw u hu hinf).2) y).trans ?_
  exact mul_le_mul' le_rfl (sobO_word_le μ 𝓕 l _ f)

end GlobalTheory.LevelSupBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  first | exact @GlobalTheory.LevelSupBound.supN_word_le | exact GlobalTheory.LevelSupBound.supN_word_le | (intros; apply GlobalTheory.LevelSupBound.supN_word_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinAvgSpan

open Formalism.REAL MeasureTheory GlobalTheory.SeriesToClosure Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom

theorem continuous_integral_K {n : ℕ} {ε : Fin n → Bool} {X : Type*} [TopologicalSpace X] (F : X → KG ε → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ k, F x k ∂(muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ k, g k ∂(muK ε)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (GlobalTheory.ExpansionAverage.integrable_K g.continuous)
          (GlobalTheory.ExpansionAverage.integrable_K h.continuous)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hL : Continuous L := AddMonoidHomClass.continuous_of_bound L ((muK ε).real Set.univ) fun g => by
    show ‖∫ k, g k ∂(muK ε)‖ ≤ _
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      ContinuousMap.norm_coe_le_norm g k)).trans (le_of_eq (mul_comm _ _))
  exact hL.comp (ContinuousMap.curry ⟨_, hF⟩).continuous

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_conjAt (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) :
    Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
    fun k => conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))

theorem continuous_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    Continuous (Function.uncurry fun (x : GA D V) (k : KG ε) => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) :=
  (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul ((continuous_conjAt hθ hP hJ).comp continuous_snd)))

theorem integrable_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) (x : GA D V) :
    Integrable (fun k => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) (muK ε) :=
  GlobalTheory.ExpansionAverage.integrable_K (he.mul (hφ.comp (continuous_const.mul (continuous_conjAt hθ hP hJ))))

theorem continuous_avg (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) : Continuous (avg θ V τ ε P e φ) :=
  continuous_integral_K _ (continuous_integrand hθ hP hJ he hφ)

theorem avg_add_left (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e₁ e₂ : KG ε → ℂ} (h₁ : Continuous e₁) (h₂ : Continuous e₂) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    avg θ V τ ε P (e₁ + e₂) φ = avg θ V τ ε P e₁ φ + avg θ V τ ε P e₂ φ := funext fun x => by
  simp only [avg, Pi.add_apply, add_mul]
  exact integral_add (integrable_integrand hθ hP hJ h₁ hφ x) (integrable_integrand hθ hP hJ h₂ hφ x)

theorem avg_smul_left (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P (c • e) φ = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem avg_add_right (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ₁ φ₂ : GA D V → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    avg θ V τ ε P e (φ₁ + φ₂) = avg θ V τ ε P e φ₁ + avg θ V τ ε P e φ₂ := funext fun x => by
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hθ hP hJ he h₁ x) (integrable_integrand hθ hP hJ he h₂ x)

theorem avg_smul_right (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P e (c • φ) = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_left_comm (e _) c]
  exact integral_const_mul c _

theorem rTr_avg_same (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : P * g * P⁻¹ ∈ Kset ε) :
    ∃ k₀ : KG ε, ∀ (e : KG ε → ℂ) (φ : GA D V → ℂ),
      rTr V (atTau θ V τ g) (avg θ V τ ε P e φ) = avg θ V τ ε P (fun k => e (k₀⁻¹ * k)) φ := by
  obtain ⟨k₀, hk₀'⟩ : P * g * P⁻¹ ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
  have hk₀ : toMK k₀ = P * g * P⁻¹ := hk₀'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have eg : g = P⁻¹ * toMK k₀ * P := by
    rw [hk₀]
    calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul _ hd, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨k₀, fun e φ => funext fun x => ?_⟩
  have key : ∀ k : KG ε, atTau θ V τ g * atTau θ V τ (P⁻¹ * toMK k * P) =
      atTau θ V τ (P⁻¹ * toMK (k₀ * k) * P) := fun k => by
    rw [eg, ← at_mul hθ hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k₀)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))]
    rfl
  simp only [rTr, avg, mul_assoc x, key]
  rw [← integral_mul_left_eq_self (μ := muK ε)
    (fun k => e (k₀⁻¹ * k) * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) k₀]
  simp only [inv_mul_cancel_left]

theorem rTr_avg_other (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    rTr V (atTau θ V τ' g) (avg θ V τ ε P e φ) = avg θ V τ ε P e (rTr V (atTau θ V τ' g) φ) := funext fun x => by
  simp only [rTr, avg, mul_assoc x]
  congr 1
  funext k
  rw [GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _
    (conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))) g hg]

end GlobalTheory.KFinAvgSpan

namespace GlobalTheory.KFinAvgSpan


set_option maxHeartbeats 1600000 in
theorem exists_stab_insert : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  intro D θ hθ N τ e he s hτs W' hW'fin hW'c hW'stab
  obtain ⟨F, hFfin, heF, hFc, hFtr⟩ := he
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI := hFfin
  haveI := hW'fin
  let B : F →ₗ[ℂ] W' →ₗ[ℂ] (GA D N.V → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ)
        (b : GA D N.V → ℂ))
      (fun a₁ a₂ b => avg_add_left hθ hP hJ (hFc _ a₁.2) (hFc _ a₂.2) (hW'c _ b.2))
      (fun c a b => avg_smul_left c _ _)
      (fun a b₁ b₂ => avg_add_right hθ hP hJ (hFc _ a.2) (hW'c _ b₁.2) (hW'c _ b₂.2))
      (fun c a b => avg_smul_right c _ _)
  have hB : ∀ (a : F) (b : W'), TensorProduct.lift B (a ⊗ₜ b) =
      GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ) :=
    fun a b => by rw [TensorProduct.lift.tmul]; rfl
  have hcont : ∀ t, Continuous (TensorProduct.lift B t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact continuous_const
    | tmul a b => rw [hB]; exact continuous_avg hθ hP hJ (hFc _ a.2) (hW'c _ b.2)
    | add u v hu hv => rw [map_add (f := _)]; exact hu.add hv
  refine ⟨LinearMap.range (TensorProduct.lift B), inferInstance, ?_, ?_, fun f hf => ⟨⟨e, heF⟩ ⊗ₜ ⟨f, hf⟩, hB _ _⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact hcont t
  · intro τ'' hτ'' g hg hK w hw
    obtain ⟨t, rfl⟩ := hw
    suffices h : ∀ (a : F) (b : W'), rTr N.V (atTau θ N.V τ'' g)
        (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)) ∈
          LinearMap.range (TensorProduct.lift B) by
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | tmul a b => rw [hB]; exact h a b
      | add u v hu hv =>
        rw [map_add (f := _)]
        exact add_mem hu hv
    intro a b
    rcases hτ'' with h | hs
    · rw [h] at hK ⊢
      obtain ⟨k₀, hk⟩ := rTr_avg_same hθ hP hJ hK
      have hk' := hk (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)
      refine ⟨⟨_, (hFtr _ a.2 k₀⁻¹).1⟩ ⊗ₜ b, ?_⟩
      rw [hB, hk']
    · have hne : τ ≠ τ'' := fun h => hτs (h ▸ hs)
      rw [rTr_avg_other hθ hP hJ hne hg]
      exact ⟨a ⊗ₜ ⟨_, hW'stab τ'' hs g hg hK b b.2⟩, hB _ _⟩

end GlobalTheory.KFinAvgSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAveragesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDim_stable_space_maxCompactAverages : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  first | exact @GlobalTheory.KFinAvgSpan.exists_stab_insert | exact GlobalTheory.KFinAvgSpan.exists_stab_insert | (intros; apply GlobalTheory.KFinAvgSpan.exists_stab_insert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjReadIota

variable {D : D7}

theorem mem_Kset_iff_mem_St (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ (x.1 : GL (Fin (Yc D 0).rank) (EAf D)) ∈ St β := by
  rw [GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame] at hβ
  refine ⟨GlobalTheory.ConjPlaceRed.mem_St_of_Kset D β x hβ, fun hx => ?_⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).1 hx
  intro v
  constructor
  · intro hv
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).1 (h1 v ((GlobalTheory.ConjPlaceRed.mem_Lf D v).2 hv))
  · intro hv
    have h3 := h2 _ ((GlobalTheory.ConjPlaceRed.mem_Lf D _).2 hv)
    have e : Matrix.mulVec ((x.1 : GL (Fin (Yc D 0).rank) (EAf D))⁻¹).val
        (Matrix.mulVec (x.1 : GL (Fin (Yc D 0).rank) (EAf D)).val v) = v := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have h4 : v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) := e ▸ h3
    exact (GlobalTheory.ConjPlaceRed.mem_Lf D v).1 h4

theorem instanceIota_real_finite_stabilizer_unitary_characterization {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (κ : GA D (Yc D 0)) :
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2 ∈ I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  subst h
  have e : (Formalism.IndefR.RationalEmbedding.iota D).symm (Formalism.IndefR.RationalEmbedding.iota D κ) = κ := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ
  have h1 := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [e] at h1 hf
  change ((Formalism.IndefR.RationalEmbedding.iota D κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧
    ((Formalism.IndefR.RationalEmbedding.iota D κ).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ↔ finE (Yc D 0) κ ∈ St β) ∧
    finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram
  refine ⟨h1.symm, ?_, ?_⟩
  · rw [mem_Kset_iff_mem_St β hβ]
    exact iff_of_eq (congrArg (· ∈ St β) hf.symm)
  · have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this

theorem read_iota : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ κ : GA D (Yc D 0), (((iotaX X h).toMulEquiv κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧ (((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  intro D X h β hβ κ
  exact instanceIota_real_finite_stabilizer_unitary_characterization h β hβ κ

end GlobalTheory.SeeConjReadIota
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.instanceIota_readout_realTrivial_stabilizer_unitary : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ κ : GA D (Yc D 0), (((iotaX X h).toMulEquiv κ).1 = 1 ↔ κ ∈ GfC (Yc D 0)) ∧ (((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset ↔ finE (Yc D 0) κ ∈ St β) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram := by
  first | exact @GlobalTheory.SeeConjReadIota.read_iota | exact GlobalTheory.SeeConjReadIota.read_iota | (intros; apply GlobalTheory.SeeConjReadIota.read_iota <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteLiftZfin

open Matrix

theorem isCuspFun_of_posDef {D : D7} {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) (φ : GA D V → ℂ) :
    IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hτ : ∀ a, tauE D τ0 (star a) = starRingEnd ℂ (tauE D τ0 a) := D.sp.cm.cmUnram.2.1 (tauE D τ0)
  have h1 := congrArg (tauE D τ0) (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have hx : star (fun i => tauE D τ0 (C i ⟨0, hr⟩)) ⬝ᵥ (gramAt D V τ0 *ᵥ fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gramAt, Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm
  have h2 : (fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    by_contra hne
    have := (hV τ0).dotProduct_mulVec_pos hne
    rw [hx] at this
    exact lt_irrefl _ this
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact (tauE D τ0).injective ((congrFun h2 i).trans (map_zero (tauE D τ0)).symm)

end GlobalTheory.DefiniteLiftZfin
end
end
