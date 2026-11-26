module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TranslateToSecondModelCuspFormMapValueAutomorphi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.UnrPlDict

open GlobalTheory.IdemSupport

variable {D : D7}

theorem exists_glue_kill {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)} (hu : UnrAt χ w)
    {e : AE D} (hd : GlobalTheory.IdemSupport.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w e)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ χ y = 1 := by
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hm : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (x : AE D) w *
      GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((x⁻¹ : (AE D)ˣ) : AE D) w = 1 := by
    rw [← ev_mul, Units.mul_inv, map_one]
    try rfl
  let u : (w.adicCompletion D.host.E)ˣ :=
    ⟨_, _, hm, by rw [mul_comm]; exact hm⟩
  have hU : Formalism.L2.Host.IsUnitAt w u := by
    rw [GlobalTheory.LFun.EulerTie.isUnitAt_iff]
    exact ⟨(hΦ.int _).1 h1 w, (hΦ.int _).1 h2 w⟩
  refine ⟨GlobalTheory.LFun.locIdele D.host.F w u, (GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd rfl).symm, ?_⟩
  have := congrArg (fun z : ℂˣ => (z : ℂ)) (hu u hU)
  exact Circle.ext this

theorem unrPl_of_unrAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle,
    (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  intro D v w hw χ hχ e f hp x hx h1 h2
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · have hd' := delta_conj hΦ hd
    obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_glue_kill (hχ (cP w) ((under_cP w).trans hw)) hd' x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

end GlobalTheory.UnrPlDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_char_trivial_on_integral_units_at_place : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle, (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  first | exact @GlobalTheory.UnrPlDict.unrPl_of_unrAt | exact GlobalTheory.UnrPlDict.unrPl_of_unrAt | (intros; apply GlobalTheory.UnrPlDict.unrPl_of_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParameters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_hecke_of_mem_partFull {D : D7} {c : Com D} {s : PiLocalization₂ D} (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (hu : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D s.V))
    (hR : Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R) (v : SmT s.M) :
    heckeLin s.V R (PiLocalization₂.val u v) = e P d • PiLocalization₂.val u v := by
  have h := ((mem_partFull c.θ s.M _ _ c.S e _).1 hu).2 P d R hR
  have key : heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = e P d • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    apply PiTensorProduct.ext
    ext x
    have := h x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.smul_apply] at this ⊢
    convert congrFun this _ using 2 <;> simp [PiTensorProduct.lift_symm]
  exact congrFun (congrArg DFunLike.coe key) v |>.trans rfl

theorem partPar : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c)
    (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e →
    (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  intro hP D c hc j hj s hs u e hu
  obtain ⟨hval, hHk, hconj⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hP D c hc j hj s hs
  obtain ⟨-, hlat⟩ := GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs
  obtain ⟨-, hsph, -⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  have hlev : ∀ v, ∀ k ∈ levS s.V s.β s.L, ∀ g, (fun g => conj (PiLocalization₂.val u v g)) (g * k) =
      (fun k => conj (Lev.levChi s.V s.β s.L k)) k * (fun g => conj (PiLocalization₂.val u v g)) g := by
    intro v k hk g
    simp only [(hval u v).2.2.2 k hk g, map_mul]
  have hhk : ∀ v P d R, Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R →
      heckeLin s.V R (fun g => conj (PiLocalization₂.val u v g)) = (fun P d => conj (e P d)) P d • (fun g => conj (PiLocalization₂.val u v g)) := by
    intro v P d R hR
    rw [hconj, val_hecke_of_mem_partFull u e hu P d R ((hHk P d R).2 hR) v]
    funext g
    simp [map_mul]
  have hne : ∀ v, PiLocalization₂.val u v ≠ 0 → (fun g => conj (PiLocalization₂.val u v g)) ≠ 0 := by
    intro v h0 h
    apply h0
    funext g
    simpa using congrFun h g
  have hiff : ∀ v B, PiLocalization₂.val u v ≠ 0 →
      (ParFun c s (PiLocalization₂.val u v) B ↔ GlobalTheory.LFun.IsSysParamD D c.S s.V.rank (fun P d => conj (e P d)) B) := by
    intro v B h0
    unfold ParFun
    rw [hlat]
    exact GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph (hne v h0) (hlev v) (hhk v) B
  have second : ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
    intro w B hw hB
    refine ⟨?_, fun v hv => (hiff v B hv).2 ((hiff w B hw).1 hB)⟩
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun hu0 => ?_, second⟩
  have hu1 : (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ≠ 0 := fun h => hu0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hu1 (LinearMap.ext hh)
  obtain ⟨C, hC⟩ := (hval u v).2.1
  have hbdd : (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj.comp (hval u v).1), fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [(hval u v).2.2.1 γ hγ g]
    · simpa using hC g
  obtain ⟨B, hB, -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsph
    _ hbdd (hne v hv) (hlev v) (fun P d => conj (e P d)) (hhk v)
  have hpf : ParFun c s (PiLocalization₂.val u v) B := by
    unfold ParFun
    rw [hlat]
    exact hB
  exact ⟨B, second v B hv hpf⟩

end GlobalTheory.ChainOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParametersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s => ∀ (u : s.CC c) (e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ), PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e → (u ≠ 0 → ∃ B, IsPar u B) ∧ ∀ w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → IsPar u B := by
  first | exact @GlobalTheory.ChainOnto.partPar | exact GlobalTheory.ChainOnto.partPar | (intros; apply GlobalTheory.ChainOnto.partPar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ChainOnto.ParClosed

variable {D : D7}

theorem chS_succ (c : Com D) (k : ℕ) : c.chS (k + 1) = c.μ (k + 1) * c.eps (k + 1) := by
  unfold Com.chS Com.eps Lift.chrStep
  split_ifs <;> simp

theorem chT_succ (c : Com D) (k : ℕ) : c.chT (k + 1) = c.μ (k + 1) * c.eps k := by
  unfold Com.chT Com.eps Lift.chrStep
  rcases Nat.even_or_odd k with hk | hk
  · have h1 : Odd (k + 1) := hk.add_one
    have h2 : ¬ Odd k := Nat.not_odd_iff_even.2 hk
    simp [h1, h2]
  · have h1 : ¬ Odd (k + 1) := Nat.not_odd_iff_even.2 hk.add_one
    simp [h1, hk]

theorem eps_succ (c : Com D) (k : ℕ) :
    c.chS (k + 1) * (c.chT (k + 1))⁻¹ * c.eps k = c.eps (k + 1) := by
  rw [chS_succ, chT_succ]
  exact by
    have h : ∀ a b e : (AE D)ˣ →* Circle, a * b * (a * e)⁻¹ * e = b := fun a b e => by
      rw [_root_.mul_inv_rev, mul_comm e⁻¹ a⁻¹, mul_comm a b]
      simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]
    exact h _ _ _

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem vf_mul (χ ψ : (AE D)ˣ →* Circle) : vf (χ * ψ) = vf χ * vf ψ := by
  funext w; simp [vf]

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_eq (χS χT : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    stepPar χS χT t B = GlobalTheory.LFun.twist B (vf (χS * χT⁻¹)) + GlobalTheory.LFun.segFam (vf χS) t := by
  funext w; simp [stepPar, GlobalTheory.LFun.twist, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = GlobalTheory.LFun.twist (B + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i)) D.R.t) (vf (c.eps k)) := by
  induction k with
  | zero =>
    have h1 : vf (1 : (AE D)ˣ →* Circle) = 1 := funext fun w => GlobalTheory.LFun.val_one (F := D.host.F) w
    simp [chainPar, Com.eps, h1]
  | succ k ih =>
    rw [chainPar_succ, ih, stepPar_eq, GlobalTheory.LFun.twist_twist, ← vf_mul, eps_succ, Finset.sum_Icc_succ_top (by omega),
      ← add_assoc, GlobalTheory.LFun.twist_add (B + _), GlobalTheory.LFun.twist_segFam, ← vf_mul, chS_succ, mul_comm (c.eps (k + 1))]

theorem twist_vf (μ e : (AE D)ˣ →* Circle) : (vf (μ * e))⁻¹ * vf e = (vf μ)⁻¹ := by
  funext w; simp [vf, mul_comm]

theorem vf_quot (μ ν : (AE D)ˣ →* Circle) : (vf ν)⁻¹ * vf μ = vf (μ * ν⁻¹) := by
  funext w; simp [vf, mul_comm]

end GlobalTheory.ChainOnto.ParClosed


open GlobalTheory.ChainOnto.ParClosed in
theorem GlobalTheory.ChainOnto.chainPar_twist_chT : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ),
    GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ =
      GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ +
        ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  intro D c B k
  change GlobalTheory.LFun.twist (chainPar c B k) (vf (c.chT (k + 1)))⁻¹ =
    GlobalTheory.LFun.twist B (vf (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (vf (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t
  rw [chainPar_closed, GlobalTheory.LFun.twist_twist, chT_succ, twist_vf, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam, vf_quot]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterTwistNextTargetCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char : ∀ (D : D7) (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ), GlobalTheory.LFun.twist (chainPar c B k) (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹ = GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ + ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.segFam (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)) D.R.t := by
  first | exact @GlobalTheory.ChainOnto.chainPar_twist_chT | exact GlobalTheory.ChainOnto.chainPar_twist_chT | (intros; apply GlobalTheory.ChainOnto.chainPar_twist_chT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSet
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.VacOffS

variable {D : D7}

theorem exists_under (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 D.host.E)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem latO_at_le {S T : HSp D} {LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {NS NT : ℕ}
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ LS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ LT)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E)) (fun u => u = v) ≤
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set M : ℕ := NS * NT with hMdef
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hv
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  have hval : HeightOneSpectrum.valuation D.host.F v (M : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ intAf D.host.F, α = algebraMap D.host.F _ (M : D.host.F) * γ := by
    refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
    · rw [map_mul, AlgHom.commutes]
      by_cases hw : w = v
      · subst hw
        refine mul_mem (hα w) ?_
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀, hval, inv_one]
      · rw [hP w hw, zero_mul]; exact zero_mem _
    · rw [mul_comm α, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]
  have hs' : s ∈ L0c D S := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact hs
  have ht' : t ∈ L0c D T := by rw [GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]; exact ht
  refine AddSubgroup.subset_closure ⟨γ, hγ, fun w hw => (hw trivial).elim, a, ha, _, hS s hs', _, hT t ht', ?_⟩
  ext i j
  simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.VacLat.pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  congr 1
  rw [Algebra.smul_def, map_natCast, hMdef]
  simp only [star_mul', star_natCast, Nat.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.ChainOnto.VacOffS


open GlobalTheory.ChainOnto.VacOffS in
theorem GlobalTheory.ChainOnto.fock_vacFin_off :
    ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  intro D _ c hc k _ s s' hs hs' p hp φ v hv
  classical
  obtain ⟨ξ, f₀, hf₀, e, he, hth⟩ := hp.vec
  obtain ⟨NS, hNS, hNSv⟩ := hs.base
  obtain ⟨NT, hNT, hNTv⟩ := hs'.base
  obtain ⟨hr, ξ', hL⟩ := hs.lev
  have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    obtain ⟨P, hP⟩ := exists_under (D := D) v
    have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
    have h1 := hNSv P hPv
    have h2 := hNTv P hPv
    intro h
    rw [← hP] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact h1 h
    · exact h2 h
  have hle := latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
  have hoff : ∀ PP ∈ s.L.Pg ∪ ∅, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
    intro PP hPP h0
    rw [Finset.union_empty, hL] at hPP
    exact hv (Finset.mem_image.2 ⟨PP, hPP, h0⟩)
  have hfix : ∀ u ∈ latO s.V s'.V (frameLat s.V : Set (Fin s.V.rank → D.host.E))
      (frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
      heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
        (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
  refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
  · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vectors_lattice_vacua_off_finite_set : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  first | exact @GlobalTheory.ChainOnto.fock_vacFin_off | exact GlobalTheory.ChainOnto.fock_vacFin_off | (intros; apply GlobalTheory.ChainOnto.fock_vacFin_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

open Formalism.UG (IsInertAt)

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def secW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) :
    w.adicCompletion D.host.E →+ AE D :=
  (GlobalTheory.EmbChart.tensAt D.host.E v).toAddMonoidHom.comp
    (GlobalTheory.LFun.InertChart.complEquiv hw h).symm.toRingHom.toAddMonoidHom

def uPt (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E))
    (aT : GL (Fin T.rank) (w.adicCompletion D.host.E))
    (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) : WO S T :=
  (k • (aT.1 * x * (aS⁻¹).1)).map (secW hw h)

def thW (ψ : AddChar (AF D.host.F) ℂ) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (k : w.adicCompletion D.host.E) : AddChar (w.adicCompletion D.host.E) ℂ :=
  ψ.compAddMonoidHom ((Algebra.trace (AF D.host.F) (AE D)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (incA D D.host.xi0)).comp ((secW hw h).comp (AddMonoidHom.mulLeft k))))

variable {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
  {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
  {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}

theorem thW_apply (ψ : AddChar (AF D.host.F) ℂ) (z : w.adicCompletion D.host.E) :
    thW ψ hw h k z = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * secW hw h (k * z))) := rfl

theorem uPt_add (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    uPt hw h k aS aT (x + y) = uPt hw h k aS aT x + uPt hw h k aS aT y := by
  ext i j
  simp [uPt, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem uPt_zero : uPt hw h k aS aT (0 : Matrix (Fin T.rank) (Fin S.rank) _) = 0 := by
  ext i j
  simp [uPt]

theorem infPart_tensAt (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    infPart D (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) ⊗ₜ[D.host.F] x = 0
    rw [show (fstA D.host.F) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin v a)) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem infPart_secW (z : w.adicCompletion D.host.E) : infPart D (secW hw h z) = 0 :=
  infPart_tensAt _

theorem map_infPart_uPt (x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    (uPt hw h k aS aT x).map (infPart D) = 0 := by
  ext i j
  exact infPart_secW _

section Anti

open Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil

variable {L : Type} [Field L]

theorem antiJ_herm (σ : L →+* L) (n : ℕ) (i j : Fin n) : σ (antiJ L n i j) = antiJ L n j i := by
  simp only [antiJ]
  rw [show j.val + i.val = i.val + j.val from add_comm _ _]
  split_ifs <;> simp

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem antiG_mem (n : ℕ) : GlobalTheory.SphTheta.antiG L n ∈ GLint (Fin n) (intL L) := by
  let A : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hA : A.map (intL L).subtype = antiJ L n := by
    ext i j
    show ((if i.val + j.val + 1 = n then 1 else 0 : intL L) : L) = antiJ L n i j
    simp only [antiJ]
    split_ifs <;> simp
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) (intL L) => M.map (intL L).subtype :=
    fun M N e => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun e i) j)
  have hAA : A * A = 1 := hinj (by
    show (A * A).map (intL L).subtype = (1 : Matrix (Fin n) (Fin n) (intL L)).map (intL L).subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA]
    exact P.fIwasawa_antiJ_mul_antiJ)
  exact ⟨⟨A, A, hAA, hAA⟩, Units.ext hA⟩

end Anti

section Build

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {X : Type} (u : X → WO S T) (f : WO S T → ℂ)

def spanT : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ (Set.range fun x => heisO ψ S T (u x) f)

variable {ψ u f}

theorem mem_spanT_of {g : Module.End ℂ (WO S T → ℂ)} (hg : ∀ x, g (heisO ψ S T (u x) f) ∈ spanT ψ u f) {m : WO S T → ℂ}
    (hm : m ∈ spanT ψ u f) : g m ∈ spanT ψ u f := by
  have key : spanT ψ u f ≤ (spanT ψ u f).comap g := Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    exact hg x)
  exact key hm

theorem heis_mem_spanT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) {m : WO S T → ℂ} (hm : m ∈ spanT ψ u f) :
    heisO ψ S T (u x) m ∈ spanT ψ u f :=
  mem_spanT_of (g := GlobalTheory.SplitScalar.heisL ψ S T (u x)) (fun y => by
    show heisO ψ S T (u x) (heisO ψ S T (u y) f) ∈ spanT ψ u f
    rw [GlobalTheory.SplitScalar.heisO_heisO, ← hu]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x + y, rfl⟩)) hm

theorem self_mem_spanT [Zero X] (hu : u 0 = 0) : f ∈ spanT ψ u f :=
  Submodule.subset_span ⟨0, by
    show heisO ψ S T (u 0) f = f
    rw [hu, GlobalTheory.SplitScalar.heisO_zero]⟩


variable (ψ u f) in
def rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) : Module.End ℂ (spanT ψ u f) :=
  (GlobalTheory.SplitScalar.heisL ψ S T (u x)).restrict fun _ hm => heis_mem_spanT hu x hm

theorem coe_rhoT [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (x : X) (m : spanT ψ u f) :
    (rhoT ψ u f hu x m : WO S T → ℂ) = heisO ψ S T (u x) m := rfl


variable (ψ u f) in
def omT {G : Type} [Monoid G] (π : G →* Module.End ℂ (WO S T → ℂ))
    (hπ : ∀ g, ∀ m ∈ spanT ψ u f, π g m ∈ spanT ψ u f) : G →* Module.End ℂ (spanT ψ u f) where
  toFun g := (π g).restrict (hπ g)
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    show π 1 m = m
    rw [map_one, Module.End.one_apply])
  map_mul' g g' := LinearMap.ext fun m => Subtype.ext (by
    show π (g * g') m = π g (π g' m)
    rw [map_mul, Module.End.mul_apply])

theorem span_rhoT_eq_top [Add X] (hu : ∀ x y, u (x + y) = u x + u y) (hf : f ∈ spanT ψ u f) :
    Submodule.span ℂ (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) = ⊤ := by
  have e : (Set.range fun x => rhoT ψ u f hu x ⟨f, hf⟩) =
      ((↑) : spanT ψ u f → WO S T → ℂ) ⁻¹' Set.range fun x => heisO ψ S T (u x) f := by
    ext m
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  rw [e]
  exact Submodule.span_span_coe_preimage

end Build

end GlobalTheory.InertFrameLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal Pointwise

variable {D : D7}

theorem borel_Mx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  · intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

theorem lintegral_resS {S A B T : HSp D} (o : OrthDec S A B) (μ : Measure (WO S T)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (WO S T)) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (μA : Measure (WO A T)) (μB : Measure (WO B T))
    [μA.IsAddHaarMeasure] [μB.IsAddHaarMeasure] (FA : Set (WO A T)) (FB : Set (WO B T))
    (hA : IsAddFundamentalDomain (ratL T A) FA μA) (hB : IsAddFundamentalDomain (ratL T B) FB μB) :
    ∃ c : ℝ≥0, ∀ Φ : WO A T × WO B T → ℝ≥0∞, (∀ γ ∈ ratL T S, ∀ x, Φ (o.resS T (γ + x)) = Φ (o.resS T x)) →
      ∫⁻ x in 𝓕, Φ (o.resS T x) ∂μ = c • ∫⁻ y, Φ y ∂((μA.restrict FA).prod (μB.restrict FB)) := by
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  haveI : Countable (ratL T S) :=
    (TopologicalSpace.separableSpace_iff_countable.1 inferInstance : Countable (ratMx D T.rank S.rank))
  haveI : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun _ => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  let e : WO S T ≃ₜ (WO A T × WO B T) :=
    { (o.resS T).toEquiv with continuous_toFun := o.continuous_resS T, continuous_invFun := o.continuous_resS_symm T }
  let em := e.toMeasurableEquiv
  haveI : (μ.map em).IsAddHaarMeasure :=
    (o.resS T).isAddHaarMeasure_map μ (o.continuous_resS T) (o.continuous_resS_symm T)
  obtain ⟨c, hmeq⟩ : ∃ c : ℝ≥0, μ.map em = c • μA.prod μB :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map em) (μA.prod μB)⟩
  refine ⟨c, fun Φ hper => ?_⟩
  have hqmp : QuasiMeasurePreserving em μ (μA.prod μB) :=
    ⟨em.measurable.aemeasurable, by rw [hmeq]; exact Measure.smul_absolutelyContinuous⟩
  have hprod := isAddFundamentalDomain_prod hA hB
  have hmem : ∀ g : (ratL T A).prod (ratL T B), (o.resS T).symm (g : WO A T × WO B T) ∈ ratL T S := fun g => by
    rw [o.mem_ratL_resS, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 g.2
  have hP : IsAddFundamentalDomain (ratL T S) (em ⁻¹' (FA ×ˢ FB)) μ := by
    refine hprod.preimage_of_equiv hqmp (e := fun g => ⟨_, hmem g⟩) ⟨fun g g' h => ?_, fun h => ?_⟩ fun g x => ?_
    · exact Subtype.ext ((o.resS T).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resS T h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resS T h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resS T).symm_apply_apply h
    · change o.resS T ((o.resS T).symm (g : WO A T × WO B T) + x) = (g : WO A T × WO B T) + o.resS T x
      rw [map_add (f := _), AddEquiv.apply_symm_apply]
  rw [h𝓕.setLIntegral_eq hP (fun x => Φ (o.resS T x)) (fun g x => hper g g.2 x)]
  change ∫⁻ x in em ⁻¹' (FA ×ˢ FB), Φ (em x) ∂μ = _
  rw [← lintegral_map_equiv _ em, ← em.restrict_map, hmeq, Measure.restrict_smul, lintegral_smul_measure,
    Measure.prod_restrict]

end GlobalTheory.WeilSliceUnit

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal

variable {D : D7}

theorem enorm_sq_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ γ ∈ ratL T S, ∀ x, ‖f (γ + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
  rintro _ ⟨g, rfl⟩ x
  have h : ‖f (ratW T S g + x)‖ = ‖f x‖ := by rw [hf.quasi, norm_mul, hψ.1.2.1, one_mul]
  show ‖f (ratW T S g + x)‖ₑ ^ 2 = _
  rw [← ofReal_norm, ← ofReal_norm, h]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  intro D ψ S A B T o μ 𝓕 hμ h𝓕 f hf
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  obtain ⟨μA, FA, hA⟩ := exists_isCovolOne D T.rank A.rank
  obtain ⟨μB, FB, hB⟩ := exists_isCovolOne D T.rank B.rank
  haveI := hA.1
  haveI := hB.1
  have hFA : IsAddFundamentalDomain (ratL T A) FA μA := hA.2.1
  have hFB : IsAddFundamentalDomain (ratL T B) FB μB := hB.2.1
  obtain ⟨c, hc⟩ := lintegral_resS o μ 𝓕 h𝓕 μA μB FA FB hFA hFB
  have hslice := GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf
  have hΦ0 : Measurable fun y : WO A T × WO B T => ‖f ((o.resS T).symm y)‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hf.cont.comp (o.continuous_resS_symm T)))).measurable
  have e0 : ∀ hψ : IsStdChar D ψ (-1), ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ = c • ∫⁻ y, ‖f ((o.resS T).symm y)‖ₑ ^ 2
      ∂((μA.restrict FA).prod (μB.restrict FB)) := by
    intro hψ
    have h := hc (fun y => ‖f ((o.resS T).symm y)‖ₑ ^ 2) (fun γ hγ x => by
      simp only [AddEquiv.symm_apply_apply]; exact enorm_sq_periodic hψ hf γ hγ x)
    simpa only [AddEquiv.symm_apply_apply] using h
  refine ⟨fun χ χ' om hW p => ?_, fun χ χ' om hW p => ?_⟩
  · have hψ := hW.std
    have hF := hslice.1 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod_symm _ hΦ1.aemeasurable, lintegral_prod_symm _ hΦ0.aemeasurable]
    refine lintegral_congr fun v => ?_
    show ∫⁻ u in FA, ‖om p (fun u => f ((o.resS T).symm (u, v))) u‖ₑ ^ 2 ∂μA =
      ∫⁻ u in FA, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μA
    exact hW.om_unit μA FA hA.1 hFA p (fun u => f ((o.resS T).symm (u, v))) (hbox.1 v)
  · have hψ := hW.std
    have hF := hslice.2 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod _ hΦ1.aemeasurable, lintegral_prod _ hΦ0.aemeasurable]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v in FB, ‖om p (fun v => f ((o.resS T).symm (u, v))) v‖ₑ ^ 2 ∂μB =
      ∫⁻ v in FB, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μB
    exact hW.om_unit μB FB hB.1 hFB p (fun v => f ((o.resS T).symm (u, v))) (hbox.2 u)

end GlobalTheory.WeilSliceUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_one_variable_preserves_sq_norm_orthogonal_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.WeilSliceUnit.main | exact GlobalTheory.WeilSliceUnit.main | (intros; apply GlobalTheory.WeilSliceUnit.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi

theorem exists_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → ∃ v₀ : M.Vec, ConjVec X h θ M v₀ := by
  intro hcl D X h θ S M hS hθ _hgap hιE
  subst hS
  obtain ⟨-, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.SeeInt.exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ
    X.B.w X.B.lam X.lam_eq X.ds X.low M
  refine ⟨fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hc2 τ⟩, c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x,
    fun τ => ?_⟩
  exact LinearIsometryEquiv.apply_symm_apply _ _

end GlobalTheory.Core.Mi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealPointMove

theorem translate_eq_move : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  intro D θ hθ V S M J χ T hT k hk v
  refine ⟨fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
    GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩,
    fun τ => rfl, fun x => ?_⟩
  have key := GlobalTheory.RealEquiv.mult_realElt D V S θ M J χ T (Submodule.subset_span hT)
    (fun τ => infMat D.sp.cm.sig V.gram (θ τ) k) (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) v
    (fun τ => ⟨M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ),
      GlobalTheory.UnifEvery.rep_mem_sm M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V k τ) (v τ).2⟩) (fun τ => rfl)
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hk] at key
  rw [key]
  rfl

end GlobalTheory.RealPointMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_map_right_translate_real_point : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → ∀ k ∈ GinfC V, ∀ v : M.Vec, ∃ v' : M.Vec, (∀ τ, (v' τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) k) (v τ)) ∧ ∀ x, T v (x * k) = T v' x := by
  first | exact @GlobalTheory.RealPointMove.translate_eq_move | exact GlobalTheory.RealPointMove.translate_eq_move | (intros; apply GlobalTheory.RealPointMove.translate_eq_move <;> assumption)
end
end
