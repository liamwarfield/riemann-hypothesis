module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDiscriminantTwelfthRootOfIdeal
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

end GlobalTheory.Glob.IntegralWittCoefficients
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.MovesOne

theorem finM_one {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  unfold finM Formalism.L2.Theta.mt
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem moves_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  intro D V n hn N h
  ext x
  rw [h x, inv_one, finM_one, Matrix.one_mulVec]
  simp only [GlobalTheory.SplitDec.rat_int_iff]
  exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩

end GlobalTheory.AdForm.MovesOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTranslate_one_eq_standardLattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  first | exact @GlobalTheory.AdForm.MovesOne.moves_one | exact GlobalTheory.AdForm.MovesOne.moves_one | (intros; apply GlobalTheory.AdForm.MovesOne.moves_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacTIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

def MoveT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c₀ : ℂ) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

theorem vacT_iff {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)} {i : ℕ}
    {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {μ : (AE (I.rec7 l Z))ˣ →* Circle} {om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} :
    VacT I l Z θ i hi c₀ μ om vac ↔ ∀ g ∈ GfC _, ∀ h ∈ GfC _, MoveT I l Z θ i hi c₀ μ om vac g h := Iff.rfl

theorem xiS_smul {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c : ℂ) (F : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :
    ColDat.xiS θ i hi (c • F) = fun z => c * ColDat.xiS θ i hi F z := by
  funext z
  simp only [ColDat.xiS, xiN, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.AdForm.VacAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

end GlobalTheory.ThetaLineStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRootProd

theorem mu_root_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  intro D V μ n hn hres e he s g hs x₀ x x₁ h0 hx hx1
  have r0 : IsDetRoot V s x₀ := Formalism.L2.Theta.isDetAt_root he V s hs x₀ h0
  have r : IsDetRoot V (s * g) (x₀ * x) := GlobalTheory.Member.isDetRoot_mul V s g x₀ x r0 hx
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 (s * g) (x₀ * x) x₁ r hx1
  obtain ⟨⟨η, hη⟩, hall⟩ := hres
  have hμ := hall η hη a
  obtain ⟨k, hk⟩ := hn
  rw [ha, map_mul, hμ, hk, ← two_mul, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one, map_mul]

end GlobalTheory.SplitRootProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_detRootChar_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  first | exact @GlobalTheory.SplitRootProd.mu_root_mul | exact GlobalTheory.SplitRootProd.mu_root_mul | (intros; apply GlobalTheory.SplitRootProd.mu_root_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacAllBase

theorem thetaSpace_std_line {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i + 1 ≤ B.R.m) : ∀ F ∈ Formalism.L2.Th1.H.Th (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))), ∃ c : ℂ, F = c • I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) := by
  intro F hF
  let Bk : Formalism.L2.Ker.Base (I.rec7 l Z) ⊤ I.J.δ := GlobalTheory.Mem.Col2.Th.VacIn.toRec (D := I.rec7 l Z) I.J.V
  have hS : Bk.StdOK := GlobalTheory.FourthRootStd.stdOK Bk (GlobalTheory.Glob.IntegralWittCoefficients.isCurveIdeal_top _)
    ((GlobalTheory.Mem.Col2.Th.isDiscriminantTwelfthRoot_host_iff (I.rec7 l Z) ⊤ I.J.δ).1 hI.amb_ok.delta)
  have hLa : LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) (Formalism.MainNotions.TaylorLogMetric.tor0 (I.rec7 l Z) ⊤ I.J.δ) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := by
    rw [← Formalism.L2.KerInert.RepComb.lamK_eq, Formalism.L2.KerInert.RepComb.lamK, GlobalTheory.ThetaLineStd.aaOf_top]
    rfl
  have hH : (HV (ι := (I.rec7 l Z).what₂.Tau) (a := B.R.N i) (b := B.R.N (i + 1)) I.A.sc) = formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) :=
    Formalism.L2.KerInert.RepComb.HV_eq_formV _
  rw [hLa, alV, hH] at hF
  have hF' : F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf (I.rec7 l Z) ⊤ I.J.δ)) (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1))) (Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor) (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1)))) := by
    refine Formalism.L2.Ker.Th_congr _ _ _ _ (fun x hx => ?_) hF
    obtain ⟨m, hm⟩ := Bk.qInt0 hS _ _ x hx
    exact (Formalism.L2.Ker.al_eq _ Bk.tor x m hm).symm
  obtain ⟨c, hc⟩ := Formalism.L2.PairingIndexBounds.Eq.J.thZeroSpans hS _ _ F hF'
  refine ⟨c, ?_⟩
  have hM : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1))) = Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) := rfl
  obtain ⟨x, hx, hIx⟩ := GlobalTheory.NatAtStd.Iop_self (I.rec7 l Z) Bk.tor (Formalism.MainNotions.TaylorLogMetric.La (I.rec7 l Z) Bk.tor (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))))
  have hfix : (fun z => Formalism.MainNotions.TaylorLogMetric.al (I.rec7 l Z) Bk.tor x * Formalism.MainNotions.TaylorLogMetric.U (I.rec7 l Z) Bk.tor x (Bk.thZero (B.R.N i) (B.R.N (i + 1))) z) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) :=
    funext fun z => (Bk.thZeroMem hS _ _).2 x hx z
  have hMz : Bk.thMoved (B.R.N i) (B.R.N (i + 1)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i)) (Formalism.MainNotions.StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N (i + 1))) = Bk.thZero (B.R.N i) (B.R.N (i + 1)) := by
    unfold Formalism.L2.Ker.Base.thMoved Formalism.L2.Ker.Base.thHalf
    rw [hIx, hIx, hfix, hfix]
  rw [hM, hMz]
  exact hc

theorem moveT_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om _ hom
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have key := GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi)
    I.A.δ I.A.sc hstd μ om hom vac hvac 1 (one_mem _) 1 (one_mem _)
  have S1 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := GlobalTheory.T.adelicTranslate_one_eq_standardLattice
  have S2 : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D μ n → Even n → ∀ (V : HSp D) (x : (AE D)ˣ),
      IsDetRoot V 1 x → μ x = 1 := GlobalTheory.T.character_eq_one_of_isDetRoot_of_even
  have S3 := thetaSpace_std_line I hI l Z i hi
  by_cases hex : Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N i)) ∧
      Moves _ (rankN (I.rec7 l Z) (i + 1) hi) 1 (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E (B.R.N (i + 1)))
  · obtain ⟨-, hmem, hne⟩ := key _ _ hex.1 hex.2
    obtain ⟨c, hc⟩ := S3 _ hmem
    refine ⟨c, ?_, ?_⟩
    · rintro rfl
      apply hne
      exact hc.trans (zero_smul _ _)
    · intro N N' hN hN' x y hx hy
      obtain rfl := S1 _ _ _ _ N hN
      obtain rfl := S1 _ _ _ _ N' hN'
      have hx1 : μ x = 1 := S2 _ _ _ hom.resS hstd.rk.2.2.1 _ x hx
      have hy1 : μ y = 1 := S2 _ _ _ hom.resT hstd.rk.2.2.2 _ y hy
      rw [hx1, hy1]
      show xiN θ _ _ _ _ I.A.δ I.A.sc _ = _
      refine hc.trans ?_
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, Circle.coe_one, inv_one, mul_one]
      rfl
  · refine ⟨1, one_ne_zero, ?_⟩
    intro N N' hN hN'
    exact absurd ⟨S1 _ _ _ _ N hN ▸ hN, S1 _ _ _ _ N' hN' ▸ hN'⟩ hex

end GlobalTheory.AdForm.VacAllBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_at_identity_nonzero_constant : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac 1 1 := by
  first | exact @GlobalTheory.AdForm.VacAllBase.moveT_one | exact GlobalTheory.AdForm.VacAllBase.moveT_one | (intros; apply GlobalTheory.AdForm.VacAllBase.moveT_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.VacSplit

open Formalism.L2.Th1.H

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} {A₁ A₂ : AddSubgroup V} {F : V → ℂ}
    (h : inter H α A₁ A₂ F ≠ 0) : relIdx A₁ A₂ ≠ 0 := by
  intro h0
  apply h
  funext z
  simp [inter, h0]

theorem inter_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V) :
    inter H α A₁ A₂ 0 = 0 := by
  funext z
  simp [inter, opU]

theorem inter_const_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A₁ A₂ : AddSubgroup V)
    (c : ℂ) (F : V → ℂ) (z : V) : inter H α A₁ A₂ (fun w => c * F w) z = c * inter H α A₁ A₂ F z := by
  unfold inter
  have e : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) (fun w => c * F w) z =
      c * (α ((Quotient.out q : A₂) : V) * opU H ((Quotient.out q : A₂) : V) F z) := fun q => by
    simp only [opU]; ring
  simp only [e]
  rw [← mul_finsum]
  ring

theorem mem_LamC_toHom {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (z : VCx D.what₂.Tau a b) (hz : z ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    ∃ γ, z = embH (tauE D) δ (toHom S T hS hT γ) := by
  obtain ⟨x, -, rfl⟩ := hz
  refine ⟨(LinearMap.toMatrix' x).reindex (finCongr hT).symm (finCongr hS).symm, ?_⟩
  congr 1
  subst hS hT
  simp [toHom]

end GlobalTheory.AdForm.VacSplit

namespace GlobalTheory.AdForm.VacSplit

open GlobalTheory.ThetaMove Formalism.L2.Th1.H


set_option maxHeartbeats 1600000 in
theorem moveT_split : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (s * g) (s' * h) := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac0 hvac _a μ om _hμ hW c₀ g h hg hh hmv e he s s' hs hs'
  intro N₁ N₁' hN₁ hN₁' x₁ y₁ hx₁ hy₁
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  obtain ⟨hstdAll, -, hemb, -, hroot⟩ := GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ
  have hstd := hstdAll i hi
  have hAA : I.A.AA = ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) := I.A_AA
  have hSr := rankN (I.rec7 l Z) i hi0
  have hTr := rankN (I.rec7 l Z) (i + 1) hi
  obtain ⟨N, hN⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).1 g
  obtain ⟨N', hN'⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).1 h
  obtain ⟨x, hx⟩ := hroot _ g
  obtain ⟨y, hy⟩ := hroot _ h
  have key := hmv N N' hN hN' x y hx hy
  have hsG : s ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs
  have hs'G : s' ∈ GfC _ := GlobalTheory.WeilProduct.mem_GfC_of_suppAt he hs'
  have xv := fun g₀ (hg₀ : g₀ ∈ GfC _) h₀ (hh₀ : h₀ ∈ GfC _) M M' (hM : Moves _ hSr g₀ M) (hM' : Moves _ hTr h₀ M') =>
    GlobalTheory.T.movedWeilVacuum_eq_vacuum_of_movedLattices (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW (vac0) hvac g₀ hg₀ h₀ hh₀ M M' hM hM'

  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 hI.amb_ok).1
  have hχ := GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi
  have hE := (GlobalTheory.Core.Ht2.family_laws I hI hX l Z).1
  have hfam := GlobalTheory.NatFamily.family (I.rec7 l Z) ⊤ I.J.δ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have ha : Even (B.R.N i) := hSr ▸ hstd.rk.2.2.1
  have hb : Even (B.R.N (i + 1)) := hTr ▸ hstd.rk.2.2.2
  have hMv : GlobalTheory.ThetaMove.Moves I.A (B.R.N i) (B.R.N (i + 1)) := by
    show GlobalTheory.ThetaMove.Moves (I.J.amb B I.chi) _ _
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact GlobalTheory.ThetaMove.SeamMoves.moves_ambOf B.fields _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD _ _ hX (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hcc hχ hE
      hfam.2.1 (hfam.2.2 _ _) ha hb
  have hemb' : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hemb
  have hlam : ∀ M M', lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' =
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M'
    show LamC (B.fields.embC I.A.σ₀) I.A.δ I.A.AA M M' = _
    rw [hemb', hAA]
    rfl
  have hvacT : ∀ M M', Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) M M' = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) M M' := by
    intro M M' hM hM'
    funext z
    exact inv_mul_cancel_left₀ (hMv.2.2.2.2.1 M M' hM hM').1 _
  obtain ⟨hNsd, ΛS, hcS, hΛS⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 g N hN
  obtain ⟨hN'sd, ΛT, hcT, hΛT⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 h N' hN'
  obtain ⟨hN₁sd, ΛS₁, hcS₁, hΛS₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hSr hstd.gS).2 (s * g) N₁ hN₁
  obtain ⟨hN₁'sd, ΛT₁, hcT₁, hΛT₁⟩ := (GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual _ _ _ hTr hstd.gT).2 (s' * h) N₁' hN₁'
  have v0 := xv g hg h hh N N' hN hN'
  have v1 := xv (s * g) (mul_mem hsG hg) h hh N₁ N' hN₁ hN'
  have v2 := xv (s * g) (mul_mem hsG hg) (s' * h) (mul_mem hs'G hh) N₁ N₁' hN₁ hN₁'
  have hc1 : om (s, 1) (om (g, h) (vac0)) = om (s * g, h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hc2 : om (1, s') (om (s * g, h) (vac0)) = om (s * g, s' * h) (vac0) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hth0 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' ≠ 0 := by
    intro h0
    apply v0.2.2
    refine key.trans (funext fun z => ?_)
    show _ = (0 : ℂ)
    rw [h0, Pi.zero_apply, mul_zero]
  have hv1 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' ≠ 0 := by
    intro h0
    apply hth0
    rw [← hvacT N N' hNsd hN'sd, hMv.2.2.2.2.2.2 N₁ N N' hN₁sd hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, h0, inter_zero]
  have hv2 : I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' ≠ 0 := by
    intro h0
    apply hv1
    rw [← hvacT N₁ N' hN₁sd hN'sd, hMv.2.2.2.2.2.1 N₁ N₁' N' hN₁sd hN₁'sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, h0, inter_zero]
  have hrel1 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N') (lam I.A N₁ N') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N N')
    rw [← hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd, hvacT N₁ N' hN₁sd hN'sd]
    exact hv1
  have hrel2 : relIdx (lam I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N') (lam I.A N₁ N₁') ≠ 0 := by
    apply inter_ne_zero (H := HV I.A.sc) (α := alV I.A.d I.A.sc) (F := vac I.A (a := B.R.N i) (b := B.R.N (i + 1)) N₁ N')
    rw [← hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd, hvacT N₁ N₁' hN₁sd hN₁'sd]
    exact hv2
  rw [hlam N N', hlam N₁ N'] at hrel1
  rw [hlam N₁ N', hlam N₁ N₁'] at hrel2
  have hfacts : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)), Formalism.L2.Col.IsSdLat M → Formalism.L2.Col.IsSdLat M' →
      IsSelfDual (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M') ∧
      IsSemiChar (HV I.A.sc) (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M')
        (alV (I.rec7 l Z).host.d I.A.sc) := by
    intro M M' hM hM'
    have := (hMv.2.2.2.2.1 M M' hM hM').2.2
    rw [← hlam M M']
    exact this
  haveI : Nonempty (I.rec7 l Z).what₂.Tau := Fintype.card_pos_iff.1 hX.f_pos
  have hinj := GlobalTheory.ThetaMove.embH_injective (a := B.R.N i) (b := B.R.N (i + 1)) (tauE (I.rec7 l Z)) hstd.ne
  have memL : ∀ (M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N i) → (I.rec7 l Z).host.E)) (M' : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin (B.R.N (i + 1)) → (I.rec7 l Z).host.E)) x, embH (tauE (I.rec7 l Z)) I.A.δ x ∈
      LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' ↔
      x ∈ perO ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) M M' := by
    intro M M' x
    exact ⟨fun ⟨y, hy, e⟩ => hinj e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.AdTh.SplitClass.exists_detAt _ he.1 s'
  have st1 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS ΛS₁ ΛT ΛT hΛS hΛS₁
    hΛT hΛT e he s 1 hs (GlobalTheory.LeviSplitChar.suppAt_one e _) x₀ 1 hx₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _)
    (by rw [hcS, hcS₁, hcT]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr g s h 1 N N' N₁ N' hN hN' hN₁ (by rwa [one_mul]))
    _ _ (fun γ v hv => by rw [hcS, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS ΛT N N' hcS hcT hΛS hΛT γ v hv).trans (memL N N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N') (hfacts N₁ N' hN₁sd hN'sd).1 (hfacts N N' hNsd hN'sd).2 (hfacts N₁ N' hN₁sd hN'sd).2 hrel1
    (om (g, h) (vac0)) (by rw [hcS, hcT]; exact v0.1) v0.2.1.2 (by rw [hc1]; exact v1.2.1.2) (by rw [hc1]; exact v1.2.2)
  have mv1 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' := by
    have c7 := hMv.2.2.2.2.2.2 N N₁ N' hNsd hN₁sd hN'sd
    rw [hvacT N N' hNsd hN'sd, hvacT N₁ N' hN₁sd hN'sd, hlam N N', hlam N₁ N'] at c7
    exact c7.symm
  have mv2 : inter (HV I.A.sc) (alV (I.rec7 l Z).host.d I.A.sc)
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N')
      (LamC (tauE (I.rec7 l Z)) I.A.δ ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) N₁ N₁')
      (I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N') = I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N₁' := by
    have c6 := hMv.2.2.2.2.2.1 N₁ N' N₁' hN₁sd hN'sd hN₁'sd
    rw [hvacT N₁ N' hN₁sd hN'sd, hvacT N₁ N₁' hN₁sd hN₁'sd, hlam N₁ N', hlam N₁ N₁'] at c6
    exact c6.symm
  have e1 : xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (s * g, h) (vac0)) = fun z =>
      ((μ x₀ : ℂ))⁻¹ * (c₀ * ((μ x : ℂ))⁻¹ * (μ y : ℂ)) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N₁ N' z := by
    rw [← hc1]
    refine st1.trans (funext fun z => ?_)
    rw [show xiN θ _ _ hSr hTr I.A.δ I.A.sc (om (g, h) (vac0)) = _ from key]
    erw [inter_const_mul]
    erw [mv1]
    simp only [map_one, Circle.coe_one, mul_one]
    ring
  have st2 := GlobalTheory.T.splitPlacePair_moves_latticeVacuumReading (I.rec7 l Z) ψ θ _ _ _ _ hSr hTr I.A.δ I.A.sc hstd (μ) (om) hW ΛS₁ ΛS₁ ΛT ΛT₁ hΛS₁ hΛS₁
    hΛT hΛT₁ e he 1 s' (GlobalTheory.LeviSplitChar.suppAt_one e _) hs' 1 y₀ (GlobalTheory.LeviSplitChar.isDetAt_one e _) hy₀
    (by rw [hcS₁, hcT, hcT₁]; exact GlobalTheory.T.homLatticeCompletion_moves_by_translatePair _ _ _ _ _ hSr hTr (s * g) 1 h s' N₁ N' N₁ N₁' hN₁ hN' (by rwa [one_mul]) hN₁')
    _ _ (fun γ v hv => by rw [hcS₁, hcT]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT N₁ N' hcS₁ hcT hΛS₁ hΛT γ v hv).trans (memL N₁ N' _).symm)
    (fun γ v hv => by rw [hcS₁, hcT₁]; exact (GlobalTheory.T.rationalFinitePart_mem_homLatticeCompletion_iff _ ψ θ _ _ _ _ hSr hTr _ _ hstd ΛS₁ ΛT₁ N₁ N₁' hcS₁ hcT₁ hΛS₁ hΛT₁ γ v hv).trans (memL N₁ N₁' _).symm)
    (mem_LamC_toHom _ _ hSr hTr _ N₁ N₁') (hfacts N₁ N₁' hN₁sd hN₁'sd).1 (hfacts N₁ N' hN₁sd hN'sd).2
    (hfacts N₁ N₁' hN₁sd hN₁'sd).2 hrel2
    (om (s * g, h) (vac0)) (by rw [hcS₁, hcT]; exact v1.1) v1.2.1.2 (by rw [hc2]; exact v2.2.1.2) (by rw [hc2]; exact v2.2.2)
  have rx := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (μ) _ hstd.rk.2.2.1 hW.resS e he s g hs x₀ x x₁ hx₀ hx hx₁
  have ry := GlobalTheory.T.splitPlace_detRootChar_mul _ _ (μ) _ hstd.rk.2.2.2 hW.resT e he s' h hs' y₀ y y₁ hy₀ hy hy₁
  rw [← hc2]
  refine st2.trans (funext fun z => ?_)
  rw [e1]
  erw [inter_const_mul]
  erw [mv2]
  rw [rx, ry]
  simp only [map_one, Circle.coe_one, inv_one, one_mul, Circle.coe_mul, mul_inv]
  ring

end GlobalTheory.AdForm.VacSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ e, IsSplitIdem (I.rec7 l Z) e → ∀ s s', SuppAt e _ s → SuppAt e _ s' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (s * g) (s' * h) := by
  first | exact @GlobalTheory.AdForm.VacSplit.moveT_split | exact GlobalTheory.AdForm.VacSplit.moveT_split | (intros; apply GlobalTheory.AdForm.VacSplit.moveT_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitInduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.VacConst

theorem suppAt_one {D : D7} (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := by
  intro i j
  have h : mt V 1 - 1 = 0 := by rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]
  rw [h, Matrix.zero_apply, mul_zero]

theorem split_induction {D : D7} (V : HSp D) (P : GA D V → Prop)
    (hP : ∀ g ∈ GfC V, P g → ∀ e, IsSplitIdem D e → ∀ s, Formalism.L2.Theta.SuppAt e V s → P (s * g))
    {s : GA D V} (hs : s ∈ splitPart V) : s ∈ GfC V ∧ ∀ g ∈ GfC V, P g → P (s * g) := by
  induction hs using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx, fun g hg h => hP g hg h e he x hx⟩
  | inv_mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    have hx' := GlobalTheory.SplitHecke.Stab.suppAt_inv hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx', fun g hg h => hP g hg h e he _ hx'⟩
  | one => exact ⟨one_mem _, fun g _ h => by rwa [one_mul]⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨mul_mem ihx.1 ihy.1, fun g hg h => ?_⟩
    rw [mul_assoc]
    exact ihx.2 _ (mul_mem ihy.1 hg) (ihy.2 g hg h)

end GlobalTheory.AdForm.VacConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderStdLatticeStabilizers
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderStdLatticeStabilizers
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.StabMoveTup

theorem unramAt_of_chrEq_mul {D : D7} {c : (AE D)ˣ →* Circle} {χ ξ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c (χ * ξ))
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) P) → χ.UnrAt P)
    (hξ : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ ξ.UnrAt P → IsSplitPl D.host P)
    {v ε} (hv : GlobalTheory.WeilParts.NonSplitAt D v ε) : GlobalTheory.WeilParts.UnramAt ε c := by
  refine GlobalTheory.UnramOver.unramAt_of_unrAt D c _ hc v ε hv.1 fun P hP => Formalism.L2.Host.HChar.UnrAt.mul (hu P fun k hk => ?_) ?_
  · obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP
  · by_contra hn
    obtain ⟨e, he⟩ := GlobalTheory.ChoiceAdm.exists_idem (hξ P hn)
    exact GlobalTheory.AdTh.RecPair.under_ne he hv hP

theorem moveT_mul_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  intro B X I hI hPins l Z ψ θ hψ hθ i hi vac hvac a μ om hchr hW c₀ g h hg hh hM k hk k' hk' mk mk' N N' hN hN' x y hx hy
  have hP := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hPins l Z ψ θ hψ hθ).1 i hi
  have b := StabMove.intG_of_moves _ mk
  have b' := StabMove.intG_of_moves _ mk'
  have a₁ := b.inv hP.gS
  have a₁' := b'.inv hP.gT
  rw [inv_inv] at a₁ a₁'
  have hξ : ∀ P, ¬ (I.xi a).UnrAt P → IsSplitPl B.host P := fun P hn =>
    ((GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host B.fields.K B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1.2.2.2 P hn).1
  obtain ⟨x₁, y₁, rx, ry, e⟩ := StabMove.om_vac hP hW
    (fun v ε hv => unramAt_of_chrEq_mul hchr (I.C.isMu0 ⟨i, hi⟩).unr hξ hv) hvac hk hk' a₁ a₁'
  obtain ⟨x₀, sx⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 g
  obtain ⟨y₀, sy⟩ := (GlobalTheory.Member.isDetRoot_laws _ _).1 h
  have e0 := hM N N' (StabMove.moves_of_mul _ a₁ b hN) (StabMove.moves_of_mul _ a₁' b' hN') x₀ y₀ sx sy
  have ex := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sx rx) hx
  have ey := StabMove.root_eq hW.resS hP.rk.2.2.1 ((GlobalTheory.Member.isDetRoot_laws _ _).2.2.2 _ _ _ _ sy ry) hy
  rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, e, map_smul, ex, ey]
  refine (GlobalTheory.AdForm.VacAll.xiS_smul _ _ _ _ _).trans ?_
  funext z
  have e1 := congrFun e0 z
  rw [e1]
  simp only [map_mul, Circle.coe_mul, Circle.coe_inv, mul_inv]
  ring

end GlobalTheory.AdForm.StabMoveTup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderStdLatticeStabilizersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_invariant_under_stdLattice_stabilizers : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ k ∈ GfC _, ∀ k' ∈ GfC _, Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) k (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) k' (Formalism.L2.Col.stdLat (I.rec7 l Z).host.E _) → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g * k) (h * k') := by
  first | exact @GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab | exact GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab | (intros; apply GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFiniteParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFiniteParts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAllRat

theorem moveT_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ r r', IsRatFin _ r → IsRatFin _ r' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (r * g) (r' * h) := by
  intro B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hμ hom c₀ g h hg hh H r r' hr hr'
  have hp := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  obtain ⟨n, hn, hord⟩ := htw.1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hinf := Formalism.L2.Host.HChar.HasInfQ.mul_triv (I.C.isMu0 ⟨i, hi⟩).inf
    (Formalism.L2.Host.HChar.inf_eq_one_of_order hn hord)
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ hμ).2 hinf
  have hv := hvac.2
  exact GlobalTheory.AdForm.RatMove.move_rat _ _ hp hom (fun τ => -e τ) (fun τ => by
      have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
      exact e1 ▸ hexp τ) ⟨hv.theta, hv.fock⟩ (Th.VacIn.toRec (D := I.rec7 l Z) I.J.V)
    (GlobalTheory.AdForm.RatMove.curveIdeal_top _) hI.amb_ok.delta c₀ hg hh H hr hr'

end GlobalTheory.AdForm.VacAllRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFinitePartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_invariant_rationalFiniteParts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ r r', IsRatFin _ r → IsRatFin _ r' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (r * g) (r' * h) := by
  first | exact @GlobalTheory.AdForm.VacAllRat.moveT_rat | exact GlobalTheory.AdForm.VacAllRat.moveT_rat | (intros; apply GlobalTheory.AdForm.VacAllRat.moveT_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuples
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

theorem vacT_twist {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)}
    {i : ℕ} {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {μ₀ μ : (AE (I.rec7 l Z))ˣ →* Circle}
    {om₀ om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} (hv : IsThetaFunO ψ _ _ vac)
    (h0 : IsWeilDatumO ψ _ _ μ₀ μ₀ om₀) (h1 : IsWeilDatumO ψ _ _ μ μ om) (H : VacT I l Z θ i hi c₀ μ₀ om₀ vac) :
    VacT I l Z θ i hi c₀ μ om vac := by
  intro g hg h hh N N' hN hN' x y hx hy
  have e := GlobalTheory.WeilChange.weilData_differ_by_splitFac _ ψ _ _ μ₀ μ₀ μ μ om₀ om h0 h1 g h x y hx hy vac hv
  rw [e, xiS_smul, H g hg h hh N N' hN hN' x y hx hy]
  funext z
  have a1 : (μ₀ x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have a2 : (μ₀ y : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [splitFacO, Circle.coe_mul, Circle.coe_inv]
  field_simp

end GlobalTheory.AdForm.VacAll

namespace GlobalTheory.AdForm.VacAll

theorem vacT_one : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  obtain ⟨c₀, hc₀, h1⟩ := GlobalTheory.T.movedVacuum_at_identity_nonzero_constant I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  refine ⟨c₀, hc₀, vacT_iff.2 fun g hg h hh => ?_⟩
  obtain ⟨r, s, k, hr, hs, hk, hkL, rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) hstd.gS g hg
  obtain ⟨r', s', k', hr', hs', hk', hkL', rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) (i + 1) hi) hstd.gT h hh
  have h2 := GlobalTheory.T.movedVacuum_invariant_under_stdLattice_stabilizers I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ 1 1 (one_mem _) (one_mem _) h1 k hk k' hk' hkL hkL'
  rw [one_mul, one_mul] at h2
  have h3 := GlobalTheory.AdForm.VacConst.split_induction _ (fun g => MoveT I l Z θ i hi c₀ μ om vac g k') (fun g hg H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ g k' hg hk' H e he t 1 ht
      (GlobalTheory.AdForm.VacConst.suppAt_one e _)
    rwa [one_mul] at this) hs
  have hsk := mul_mem h3.1 hk
  have h4 := GlobalTheory.AdForm.VacConst.split_induction _ (fun h => MoveT I l Z θ i hi c₀ μ om vac (s * k) h) (fun h hh H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ (s * k) h hsk hh H e he 1 t
      (GlobalTheory.AdForm.VacConst.suppAt_one e _) ht
    rwa [one_mul] at this) hs'
  have h5 := GlobalTheory.T.movedVacuum_invariant_rationalFiniteParts I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ _ _ hsk (mul_mem h4.1 hk')
    (h4.2 k' hk' (h3.2 k hk h2)) r r' hr hr'
  rw [mul_assoc, mul_assoc]
  exact h5

theorem vacT_all : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac
  by_cases hex : ∃ (a : I.ι) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))),
      ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) ∧ IsWeilDatumO ψ _ _ μ μ om
  · obtain ⟨a₀, μ₀, om₀, hc0, hw0⟩ := hex
    obtain ⟨c₀, hc, H⟩ := vacT_one hSA I hI hP l Z ψ θ hψ hθ i hi vac hvac a₀ μ₀ om₀ hc0 hw0
    exact ⟨c₀, hc, fun a μ om _ hw => vacT_twist hvac.2.2 hw0 hw H⟩
  · exact ⟨1, one_ne_zero, fun a μ om hc hw => (hex ⟨a, μ, om, hc, hw⟩).elim⟩

end GlobalTheory.AdForm.VacAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuplesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_movedVacuum_all_tuples : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  first | exact @GlobalTheory.AdForm.VacAll.vacT_all | exact GlobalTheory.AdForm.VacAll.vacT_all | (intros; apply GlobalTheory.AdForm.VacAll.vacT_all <;> assumption)
end
