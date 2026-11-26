module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairCompactLineAction
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipIntegrand

theorem pde_ne_q_of_setting {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {large₂ : SizeData₂ D} {F : Face D A}
    (h : HidaSetting large₂ R F) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

theorem flatIntegrand_lc_cpt : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, IsLocallyConstant (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) ∧ HasCompactSupport (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hch _ _ t Φ _ β _ w X Y
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := pde_ne_q_of_setting hS
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc w.2
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hcond : HasConductor (psiAt ch.W w.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w.1 w.2).square 0 hm 0 hm).cond
  refine ⟨?_, hasCompactSupport_flatIntegrand one_le_sLen _ hT _ _ X Y⟩
  have hmv : Continuous ((locGrid ch.G t w).moveArgs .one ((repsAt ch.G t w).elt (β w))) := continuous_pi fun b =>
    (continuous_const.matrix_mul (continuous_apply b)).matrix_mul continuous_const
  have hψ : IsLocallyConstant fun e => ((psiAt ch.W w.1 (-phase X e) : Circle) : ℂ) :=
    ((hcond.isLocallyConstant.comp Subtype.val).comp_continuous (continuous_phase X).neg)
  exact ((IsLocallyConstant.const _).mul ((IsLocallyConstant.const _).mul
    ((isLocallyConstant_of_isTensor hT).comp_continuous (hmv.comp (continuous_fill one_le_sLen X Y))))).mul hψ

end GlobalTheory.FlipIntegrand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, IsLocallyConstant (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) ∧ HasCompactSupport (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) := by
  first | exact @GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | exact GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | (intros; apply GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinkLawIffPeriodLinkQuasi
section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.QuasiFamilyPeriods
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

def conjTr (l : Link B L' ζ') (S : HSp D) (f : WO B.L S → ℂ) : WO S L' → ℂ := fun w => star (f (l.κ S w))

def JacobiConj (ψ : AddChar (AF D.host.F) ℂ) (J : JacLev D ρ) (l : Link B L' ζ') : Prop :=
  ∀ n ∈ flagN J.d, ∀ f : WO B.L J.W₀ → ℂ,
    conjTr l J.W₀ (jacT ψ J.d B.L (yZero B.L ρ B.ζ) n f) = jacS ψ J.d L' (zEll L' ρ ζ') n (conjTr l J.W₀ f)

structure IsQuasiFam (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (Y : GA D S → WO S L → ℂ) : Prop where
  cont : Continuous fun p : GA D S × WO S L => Y p.1 p.2
  quasi : ∀ h γ w, Y h (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * Y h w
  left : ∀ γ ∈ GQ S, ∀ h w, Y (γ * h) w = Y h (w ⬝ mt S γ)

structure PeriodsAgree (s : StepBF ψ B J) (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ)
    (G' : GA D J.W → ℂ) : Prop where

  handInt : ∀ (h : GA D J.W₀) (w : WO J.W₀ L'), IntegrableOn
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) B.vA.𝓕 B.vA.μ

  kerInt : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    IntegrableOn (fun h₀ => φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h) B.vA.𝓕 B.vA.μ

  ker_eq : ∀ n ∈ flagN J.d, ∀ h : GA D J.W₀,
    ∫ h₀ in B.vA.𝓕, φ h₀ * fjKer ψ J.d B.o B.ζ s.om₀ Ξ h₀ n h ∂B.vA.μ = J.ker ψ ζ' (handBF s l φ Ξ) n h

  absProd : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ G' Ξ)

  absCons : AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjSrcKerFun ψ J.d (J.ker ψ ζ' (handBF s l φ Ξ)) G')

  per_eq : J.perAll ψ B s.om₀ φ G' Ξ = J.per ψ ζ' (handBF s l φ Ξ) G'

def PeriodLink (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsThetaFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

def PeriodLinkQuasi (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ l : Link B L' ζ',
    JacobiConj ψ J l ∧
    ∀ φ : GA D B.A → ℂ, IsContAut B.A φ → ∀ Ξ : WO B.V₀ J.W₀ → ℂ, IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) ∧
      ∀ G' : GA D J.W → ℂ, RapidDec J.W G' → PeriodsAgree s l φ Ξ G'

end GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct ENNReal NNReal ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuasiFamilyPeriods (conjTr JacobiConj PeriodsAgree PeriodLink PeriodLinkQuasi)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ}
  {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}

theorem heisO_heisO (S T : HSp D) (x y : WO S T) (F : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y F) = ψ (symplOH S T x y) • heisO ψ S T (x + y) F := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_left,
    AddChar.map_add_eq_mul, add_assoc]
  ring

end GlobalTheory.LinkCompare

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.MovedAlg

variable {D : D7}

def IsAlgComb (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ F : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO S T), (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, (w p).map (infPart D) = 0) ∧
    F = ∑ p, c p • heisO ψ S T (w p) f₀

theorem isAlg_mul {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a * b) := by
  rw [← mem_algebraicClosure_iff] at ha hb ⊢
  exact mul_mem ha hb

section Comb

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem IsAlgComb.zero : IsAlgComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, by simp⟩

theorem IsAlgComb.smul {a : ℂ} (ha : IsAlgebraic ℚ a) {F : WO S T → ℂ} (h : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (a • F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := h
  refine ⟨n, fun p => a * c p, w, fun p => isAlg_mul ha (hc p), hw, ?_⟩
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem IsAlgComb.add {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) (hF' : IsAlgComb ψ S T f₀ F') :
    IsAlgComb ψ S T f₀ (F + F') := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨m, c', w', hc', hw', rfl⟩ := hF'
  refine ⟨n + m, Fin.append c c', Fin.append w w', fun p => ?_, fun p => ?_, ?_⟩
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hc q
    · simpa using hc' q
  · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
    · simpa using hw q
    · simpa using hw' q
  · rw [Fin.sum_univ_add]
    simp

theorem IsAlgComb.finsum : ∀ {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ), (∀ p, IsAlgebraic ℚ (c p)) →
    (∀ p, IsAlgComb ψ S T f₀ (F p)) → IsAlgComb ψ S T f₀ (∑ p, c p • F p)
  | 0, _, _, _, _ => by simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | n + 1, c, F, hc, hF => by
    rw [Fin.sum_univ_succ]
    exact (IsAlgComb.smul (hc 0) (hF 0)).add (IsAlgComb.finsum _ _ (fun p => hc _) fun p => hF _)

theorem heisO_sum_smul (u : WO S T) {n : ℕ} (c : Fin n → ℂ) (F : Fin n → WO S T → ℂ) :
    heisO ψ S T u (∑ p, c p • F p) = ∑ p, c p • heisO ψ S T u (F p) := by
  funext z
  simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem IsAlgComb.Heisenberg₂
    (hψ : ∀ u v : WO S T, u.map (infPart D) = 0 → v.map (infPart D) = 0 → IsAlgebraic ℚ (ψ (symplOH S T u v)))
    {u : WO S T} (hu : u.map (infPart D) = 0) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T f₀ F) :
    IsAlgComb ψ S T f₀ (heisO ψ S T u F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  refine ⟨n, fun p => c p * ψ (symplOH S T u (w p)), fun p => u + w p,
    fun p => isAlg_mul (hc p) (hψ _ _ hu (hw p)), fun p => ?_, ?_⟩
  · rw [Matrix.map_add _ (map_add (infPart D)), hu, hw p, add_zero]
  · rw [heisO_sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [GlobalTheory.LinkCompare.heisO_heisO, smul_smul]

end Comb

theorem om_algComb {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X)
    (hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)))
    (t : T) (x : GA D A) (h : GA D WW)
    (h0 : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) X.vac)) {F : WO (GlobalTheory.Grid.neg A) WW → ℂ}
    (hF : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F) : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (x, h) F) := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  have e : ∀ p, X.ω t (x, h) (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac) =
      heisO W.ψ (GlobalTheory.Grid.neg A) WW (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p))
        (X.ω t (x, h) X.vac) := fun p =>
    (hX.is.weil t).om_heis ((GlobalTheory.Grid.ofSgn true A).symm x) h (w p) X.vac hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, e]
  exact IsAlgComb.finsum _ _ hc fun p => IsAlgComb.Heisenberg₂ hψ (GlobalTheory.FinApprox.actO_fin _ _ (hw p)) h0

end GlobalTheory.MovedAlg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopLevelInv

section Local

variable {k : Type} [Field k]

def colMove {G : Grid k} (j : ℕ) (κ : GL (Fin (topRank G (j + 1))) k) (x : ColArgs G) : ColArgs G :=
  Function.update (Function.update x j ((κ⁻¹).val * x j)) (j + 1) (x (j + 1) * κ.val)


open Classical in
def stepVol [MeasurableSpace k] (ν : Measure k) (n : Type) [Fintype n] (c : ℕ) (n' : Type) [Fintype n'] :
    Measure (StepVar n c n' → k) := Measure.pi fun _ => ν

theorem varsVol_eq [MeasurableSpace k] (G : Grid k) (ν : Measure k) :
    varsVol G ν = Measure.pi fun j : Fin (G.m - 1) => stepVol ν (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j)) := rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem gdet_of_mem_N {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : gdet g = 1 := by
  refine (show N k n c p ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    (Subgroup.closure_le _).2 fun g hg => ?_) hg
  apply Units.ext
  change g.val.det = 1
  rw [(GlobalTheory.RootEx.Model.inN_tri hg).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : g.val.toSquareBlock (lev p) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    rw [hg i j (by rw [hi, hj]), Matrix.one_apply, Matrix.one_apply]
    simp [Subtype.ext_iff]
  rw [this, det_one]

theorem gdet_of_mem_symN {g : GL (n ⊕ Fin c) k} (hg : g ∈ symN k n c) : gdet g = 1 :=
  (show symN k n c ≤ (Matrix.GeneralLinearGroup.det (n := n ⊕ Fin c) (R := k)).ker from
    sup_le (fun _ h => gdet_of_mem_N h) fun _ h => gdet_of_mem_N h) hg

theorem gdet_embX (g : GL n k) : gdet (embX c g) = gdet g :=
  Units.ext (by
    change (fromBlocks g.val 0 0 (1 : Matrix (Fin c) (Fin c) k)).det = g.val.det
    rw [det_fromBlocks_zero₂₁, det_one, mul_one])

theorem gdet_toFrame {G : Grid k} (hs : 1 ≤ G.s) {j : ℕ} (hj : j < G.m) (g : GL (Fin (G.rank (G.m, j))) k) :
    gdet (toFrame hs hj g) = gdet g :=
  Units.ext (det_submatrix_equiv_self _ _)

theorem exists_of_mem_symPr {G : Grid k} (hs : 1 ≤ G.s) {J : G.Level} {g : G.VertexGroup} {j : ℕ} (hj : j < G.m)
    {κ : GL (Fin (topRank G j)) k} (hκ : κ ∈ symPr (conjLevel hs J g hj)) :
    ∃ u ∈ J (G.m, j), ∃ v ∈ symN k (Fin (topRank G j)) (G.m - 1 - j),
      toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹) = v * embX _ κ ∧ gdet κ = gdet u := by
  obtain ⟨v, hv, _, ⟨u, hu, rfl⟩, h⟩ := hκ
  refine ⟨u, hu, v, hv, h, ?_⟩
  have := congrArg gdet h
  rw [gdet_mul, gdet_of_mem_symN hv, one_mul, gdet_embX] at this
  rw [← this]
  change gdet (toFrame hs hj (g (G.m, j) * u * (g (G.m, j))⁻¹)) = _
  rw [gdet_toFrame, gdet_mul, gdet_mul, mul_right_comm, ← gdet_mul, mul_inv_cancel]
  simp

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def movedPt (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) :=
  Function.update (Function.update x ⟨j, by omega⟩ (actO _ _ 1⁻¹ (g : GA D (G.V (.top (j + 1))))⁻¹ (x ⟨j, by omega⟩)))
    ⟨j + 1, hj⟩ (actO _ _ (g : GA D (G.V (.top (j + 1))))⁻¹ 1⁻¹ (x ⟨j + 1, hj⟩))

theorem movedFn_apply (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1)))
    (x : ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T))) (j' : Fin D.R.m) :
    movedFn S d j hj g j' (x j') = (d.1 j').fn (movedPt t j hj g x j') := by
  rcases eq_or_ne j' ⟨j + 1, hj⟩ with rfl | h1
  · simp only [movedFn, movedPt, Function.update_self]
  rcases eq_or_ne j' ⟨j, by omega⟩ with rfl | h2
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_self]
  · simp only [movedFn, movedPt, Function.update_of_ne h1, Function.update_of_ne h2]

def kapAt (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) (j + 1))) (Kw w) :=
  inBasis (topRank_eq G t w hj.le) (S.βp (j + 1)) w (finG (G.V (.top (j + 1))) k)

theorem kapAt_mem (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    kapAt S t j hj k w ∈ (S.term t Φ β w).pr (j + 1) j.succ_pos hj :=
  Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w

theorem givenLevel_col (t : T) (w : Pl D.host.E) (j : ℕ) : givenLevel G t w (D.R.m, j + 1) = KO (Kw w) _ := by
  have key : ∀ i, 0 < i → givenLevel G t w (i, j + 1) = KO (Kw w) _ := by
    rintro (_ | i) h
    · omega
    · rfl
  exact key _ (by have := D.R.two_le_m; omega)

theorem valuation_gdet_kapAt (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {j : ℕ} (hj : j + 1 < D.R.m)
    {k : FinPt G (.top (j + 1))} (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) (w : locPl G t) :
    valuation (Kw w.1) (gdet (kapAt S t j hj k w) : Kw w.1) = 1 := by
  obtain ⟨u, hu, -, -, -, h⟩ := exists_of_mem_symPr (G := locGrid G t w) one_le_sLen hj (kapAt_mem S hj hk w)
  rw [h]
  exact valuation_gdet_of_mem_KO (givenLevel_col t w.1 j ▸ hu)

end GlobalTheory.TopLevelInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupMaxCompactSkewHermitia
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupMaxCompactSkewHermitia
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CompactLine

theorem exists_line_in_kInf_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ B n W r s hb hW k hk
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ (W.θ w) (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf]; exact hA w
  obtain ⟨γ, hγ, Y, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin n) r s
    B.emb (incM F W.J) Complex.I A W.θ hb.cm hA1 hAθ k hk.1 hk.2
  refine ⟨γ, hγ, hγ1, fun t => ⟨hγ.2 t, fun w => ?_⟩⟩
  obtain ⟨A', hAA⟩ := (hA w).2
  exact commute_of_gen (A w) A' hAA _ _ (Y w) (hKC w) t.toAdd (hAθ w) (hgen t.toAdd w)

end GlobalTheory.CompactLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupMaxCompactSkewHermitiaStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_one_parameter_subgroup_maxCompact_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, γ (Multiplicative.ofAdd (1 : ℝ)) = k ∧
      ∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb := by
  first | exact @GlobalTheory.CompactLine.exists_line_in_kInf_skew | exact GlobalTheory.CompactLine.exists_line_in_kInf_skew | (intros; apply GlobalTheory.CompactLine.exists_line_in_kInf_skew <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.KerStabCpt

theorem isHecke_quot' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_quot' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) (hk : k = n + m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isPair_small' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E}
    {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_quot' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_quot' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem algD_eq_polData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) : algD M B.ψ B.emb = GlobalTheory.ThK.PolData B M := by
  unfold algD GlobalTheory.ThK.PolData
  congr 1
  ext Φ
  constructor
  · rintro ⟨f, φ, hf, hφ, hv, rfl⟩; exact ⟨f, hf, φ, hφ, hv, rfl⟩
  · rintro ⟨f, hf, φ, hφ, hv, rfl⟩; exact ⟨f, φ, hf, hφ, hv, rfl⟩

end GlobalTheory.SquareAgree.KerStabCpt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SplitParity

theorem exists_eq_of_sigR_fixed {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (z : R ⊗[F] E) (hz : sigR R σ z = z) : ∃ r : R, algebraMap R (R ⊗[F] E) r = z := by
  obtain ⟨δ, b, -, hb0, hb1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have hz' := B.sum_repr z
  rw [Fin.sum_univ_two] at hz'
  set x := B.repr z 0
  set y := B.repr z 1
  have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
    rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
      map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [← hz', e] at hz
  have h2 : (2 * y) • B 1 = 0 := by
    have : x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0 := by rw [hz, sub_self]
    rw [two_mul, add_smul]
    linear_combination (-1 : R ⊗[F] E) * this
  have h3 : 2 * y = 0 := by
    have := congrArg (fun w => B.repr w 1) h2
    simpa using this
  have h4 : y = 0 := by
    have hu : (2 : R) * algebraMap F R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
    calc y = algebraMap F R (1 / 2) * (2 * y) := by linear_combination (-y) * hu
      _ = 0 := by rw [h3, mul_zero]
  refine ⟨x, ?_⟩
  rw [← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.SplitParity

namespace GlobalTheory.SplitParity

theorem exists_idF_of_fixed (D : D7) (u : (AE D)ˣ) (hu : cA D (u : AE D) = u) : ∃ y, idF D y = u := by
  have hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z := fun z hz =>
    exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
      (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz
  obtain ⟨r, hr⟩ := hfx _ hu
  have hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D) := by
    have h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨r', hr'⟩ := hfx _ hu'
  have m1 : r * r' = 1 := GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩
  exact hr

theorem exists_int_add_half : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ),
    IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  intro D χ n τ a _ hr ha
  classical
  obtain ⟨N, hN, ⟨θ, hθ⟩, hχ⟩ := ha
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := by rw [hχ θ hθ x x1 xo, xτ]; simp
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := exists_idF_of_fixed D x hfix
  obtain ⟨⟨ε, hε⟩, hrχ⟩ := hr
  have c1 := hrχ ε hε y
  have c2 := hη1.2 ε hε y
  rw [hy] at c1 c2
  have c2' : ((ε y : Circle) : ℂ) = -1 := by rw [← hηc, c2, pow_one]
  have c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n := by rw [c1, Circle.coe_pow, c2']
  have hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ) := by rw [← hcx, c1', zpow_natCast]
  have hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1 := by
    rw [zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  rcases Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho
  · refine ⟨k, ?_⟩
    have : ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ) := by rw [hk]
    push_cast at this
    linarith
  · rw [ho.neg_one_zpow] at hP
    norm_num at hP

end GlobalTheory.SplitParity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_eq_exponent_add_half_index : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ), IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  first | exact @GlobalTheory.SplitParity.exists_int_add_half | exact GlobalTheory.SplitParity.exists_int_add_half | (intros; apply GlobalTheory.SplitParity.exists_int_add_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem kap_add_big (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ bigN D + 1) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := SqNum.Model.gap_le D C i j τ
  have h2 := (GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

theorem isValChar_shift {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s s' : ℕ}
    {κ κ' : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E}
    (h : IsValChar φ s κ 𝔣 Q χ) (e : ∀ i, (κ i : ℤ) + s = κ' i + s') : IsValChar φ s' κ' 𝔣 Q χ := by
  obtain ⟨a, b, c, d⟩ := h
  have : (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s := funext fun i => (e i).symm
  exact ⟨a, b, this ▸ c, d⟩

theorem cmPhi_comp_eq {D : D7} (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (τ τ' : D.what₂.Tau) :
    (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = (cmPhi D τ').comp (algebraMap D.host.K D.host.E) := by
  obtain ⟨w, hw, hφw⟩ := hfd.2.2.2.2.2.2.2
  refine GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0 := by linear_combination hs - hw
  rcases mul_eq_zero.1 h0 with h | h
  · rw [sub_eq_zero.1 h, hφw, hφw]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]


open Classical in
theorem ratio_algebraic (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (t : T) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ bigN D + 1) (Λ Λ₀ : ℂ → ℂ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) :
    IsAlgebraic ℚ (Λ s / Λ₀ s) := by
  haveI := hcm
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1
  have e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s := fun τ =>
    (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm
  have hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) :=
    isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) :=
    hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e
  have hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q := hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t
  have hQram := GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)

  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have htor0 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
    (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
  simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]

  obtain ⟨k, hk, hko⟩ := hL.xi_fin t
  have hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1 := fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y
  have hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1 := fun u hu => by
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a
  have hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker := by
    refine sup_le ?_ fun u hu' => hu u hu'
    rintro _ ⟨a, rfl⟩
    have := finPart_mul_inf (Lc.xiH t) a
    rw [hinf a, mul_one] at this
    exact this
  let ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ := QuotientGroup.lift _ (finPart (Lc.xiH t)) hker

  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  have hK2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩ := hTR D.host.E D.host.K D.host.d δ
    ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q
    (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv0
  have e1 : T₀ = Λ₀ s := hT₀.unique htor0
  have e2 : Tf ψ = Λ s :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)
  rw [← e1, ← e2]
  exact hAlg ψ

end GlobalTheory.RowEx.RatioField

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem inNF_ratios (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} [Finite T] {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl)) :
    InNF fun _ σ => ∀ i j, LRatiosIn G σ μ₀ i j := by
  let S : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)),
    {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t =>
      (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_
    rintro _ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩
    rw [h1.unique h1', h2.unique h2']
  have hSa : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩ := hz
    exact ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral,
    fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩
  simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩

end GlobalTheory.RowEx.RatioField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridStandardVacuumScalarEqProdLocalPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem isIdemAt_idemAt {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    Formalism.L2.NTheta.IsIdemAt (idemAt w) w := by
  have h : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w := by
    rcases Good.locPl_cases hw with ⟨a, b⟩ | ⟨-, -, b⟩
    · exact b ▸ G.pl.w_split _ a
    · first
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b h
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)
      | exact GlobalTheory.ParahoricLift.exists_isIdemAt fun h => (hL.Q_pl t w b).2 w b ((GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h)
  exact Classical.epsilon_spec h

theorem chi_charUnramAt (G : GridData L sc) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∉ G.pl.S0) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.ch.chi k) v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq k h1 h2) w).2 (G.ch.unr k h1 h2 w (by rwa [hw]))

theorem eta_charUnramAt {μ₀ : T} (hL : L.Is μ₀) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D L.eta v :=
  GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)

theorem attChr_charUnramAt {χ η : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hχ : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v) (hη : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D η v) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.attChr χ η n) v := by
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · exact GlobalTheory.SeeSaw.WeilLines.charUnram_mul hχ (GlobalTheory.SeeSaw.WeilLines.charUnram_inv hη)
  · exact hχ

theorem notMem_S0_of_no_place_above (G : GridData L sc) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) : v ∉ G.pl.S0 := by
  classical
  intro h
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl
    exact Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ h)
  exact hv _ hw (G.pl.under_w h)

end GlobalTheory.RowVacScalar

theorem GlobalTheory.RowVacScalar.vacScalar_eq_prod : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i : ℕ), i + 1 ≤ D.R.m →
    ∀ q : GA D (G.pS (.chi i D.R.m)) × GA D (G.pT (.chi i D.R.m)), q.1 ∈ GfC (G.pS (.chi i D.R.m)) → q.2 ∈ GfC (G.pT (.chi i D.R.m)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.1).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latS (.chi i D.R.m) : Set (Fin (G.pS (.chi i D.R.m)).rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt _ q.2).map (finPart D)).mulVec y ∈
        latHat D.host.F D.host.E (S.N.latT (.chi i D.R.m) : Set (Fin (G.pT (.chi i D.R.m)).rank → D.host.E))) →
    ∀ c : ℂ, W.om (.chi i D.R.m) q (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) →
    c = ∏ w : locPl G t, GlobalTheory.RowVacScalar.splitScal G (.chi i D.R.m) w.1 q.1 q.2 := by
  intro D T L sc G W U S μ₀ hL t i hi q hq1 hq2 hS hT c hc
  classical
  have hp : (Pair.chi i D.R.m : Pair T).InRange D.R.m := by
    simp only [Pair.InRange, Pair.big, Node.InRange]; omega
  have hW := W.om_is (.chi i D.R.m) hp
  have sd := GlobalTheory.RowVertexInv.FactorTheta.selfDual S hi
  have hv := (S.Z.vac_is (.chi i D.R.m) ⟨hi, rfl⟩).2
  have key := GlobalTheory.T.weilLatticeVacuum_eq_prod_splitPlace_factors hW sd.1 sd.2 (locPl G t) (fun w hw => isIdemAt_idemAt hL G t hw)
    (Good.under_injOn hL G t) (fun v hv' => by
      have hχ := chi_charUnramAt G (k := D.R.m - i) (by omega) (by omega) (notMem_S0_of_no_place_above G t hv')
      exact ⟨attChr_charUnramAt hχ (eta_charUnramAt hL v) _, attChr_charUnramAt hχ (eta_charUnramAt hL v) _⟩)
    q.1 hq1 q.2 hq2 hS hT _ hv.theta hv.lat
  have hne := GlobalTheory.RowVertexInv.FactorTheta.vac_ne_zero S hi
  have e1 : c • S.Z.vac (.chi i D.R.m) = (∏ w ∈ locPl G t, splitScal G (.chi i D.R.m) w q.1 q.2) • S.Z.vac (.chi i D.R.m) :=
    hc.symm.trans key
  rw [Finset.prod_coe_sort (locPl G t) (fun w => splitScal G (.chi i D.R.m) w q.1 q.2)]
  exact smul_left_injective ℂ hne e1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GEquivCx


set_option maxHeartbeats 400000 in
theorem pGEquiv_of_baseW : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.BaseW F.lv2 → R.toRealDat.ExAt → R.PGEquiv F := by
  intro hCR D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hB hE
  have hC : GlobalTheory.Hk3.Core R.toRealDat F.lv2 :=
    ⟨hB.lev, hB.grp, hB.fam, hB.models, RealDat.chain_of_weak hB.chain hE, RealDat.thP_of_weak hB.thP hE⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftGroupEquiv.th_thG_act hCR R.toRealDat F.lv2 hC
  refine ⟨fun t g x => ?_, fun j t g x => ?_⟩
  · exact h1 t g x
  · have e : cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t ((A3.A.fam.L j t).r g x)) =
        R.gW j (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j t (R.jV j t x)) :=
      (congrArg (fun y => cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • y) (h2 j t g x)).trans
        (LinearMap.map_smul _ _ _).symm
    exact e

end GlobalTheory.GEquivCx
end
