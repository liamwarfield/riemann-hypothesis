module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZero
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeLEqToricSumNeZeroStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  first | exact @GlobalTheory.ToricValue.exists_heckeL_toricSum | exact GlobalTheory.ToricValue.exists_heckeL_toricSum | (intros; apply GlobalTheory.ToricValue.exists_heckeL_toricSum <;> assumption)
end
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem sum_th_empty_ne_zero : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok → IsLamTie0 X Z → ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∑ δ, X.th i ∅ lam δ) ≠ 0 ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ hT i hi lam
  obtain ⟨ι, j, a, s, hs, u, T, hu, hTs, hEq⟩ := hT i hi lam
  refine ⟨?_, s, hs⟩
  have h1 : 1 ≤ s := by
    have := hs.2.1
    exact_mod_cast this
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := hs.2.2
  obtain ⟨Λ, -, hne, hiff⟩ := GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero D.R D.host _ (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0)
    (Z.lam0 (X.l i) j a) (GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 h2)
  have hT0 : T ≠ 0 := by rw [(hiff T).1 hTs]; exact hne
  intro h0
  rw [h0, map_zero] at hEq
  exact mul_ne_zero hu ((map_ne_zero ι).2 hT0) hEq.symm

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GroundTheory.Global

namespace GlobalTheory.AbsTwist

variable {F : Type} [Field F] [NumberField F]

theorem eq_zero_of_normOne (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) (x : IdeleGroup F) (hx : x ∈ IdeleGroup.normOneSubgroup F) :
    f x = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup F
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ n : ℕ, f (x ^ n) = n * f x := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hm, ih]; push_cast; ring
  have hb : ∀ n : ℕ, (n : ℝ) * |f x| ≤ C := fun n => by
    obtain ⟨k, hk'⟩ := hxD _ (pow_mem hx n)
    have := hC _ hk'
    rwa [hm, hk, zero_add, hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at this
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |f x|)
  rw [div_lt_iff₀ (abs_pos.2 h)] at hn
  exact absurd (hb n) (not_le.2 hn)

theorem module_expScalar (t : ℝ) :
    (IdeleGroup.ideleModule F (GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)) : ℝ) =
      Real.exp ((Module.finrank ℚ F : ℝ) * t) :=
  GlobalTheory.HeckeOne.ideleNorm_expScalar F t

theorem exists_eq_mul_log_module (f : IdeleGroup F → ℝ) (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x + f y)
    (hk : ∀ k, f (IdeleGroup.diagonal F k) = 0) :
    ∃ a : ℝ, ∀ x, f x = a * Real.log (IdeleGroup.ideleModule F x : ℝ) := by
  let e : ℝ → IdeleGroup F := fun t => GlobalTheory.HeckeOne.mixedIdele F (GlobalTheory.HeckeOne.expScalar F t)
  have hadd : ∀ s t, f (e (s + t)) = f (e s) + f (e t) := fun s t => by
    simp only [e]
    rw [GlobalTheory.HeckeOne.expScalar_add, map_mul, hm]
  have hcont : Continuous fun t => f (e t) :=
    hc.comp ((GlobalTheory.HeckeOne.continuous_mixedIdele F).comp (GlobalTheory.HeckeOne.continuous_expScalar F))
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨f (e 1) / Module.finrank ℚ F, fun x => ?_⟩
  set t : ℝ := Real.log (IdeleGroup.ideleModule F x : ℝ) / Module.finrank ℚ F with ht
  have h1 := map_real_smul (AddMonoidHom.mk' (fun t => f (e t)) hadd) hcont t 1
  simp only [smul_eq_mul, mul_one, AddMonoidHom.mk'_apply] at h1
  have h2 : IdeleGroup.ideleModule F (e t) = IdeleGroup.ideleModule F x := Subtype.ext (by
    have h3 := module_expScalar (F := F) t
    rw [ht, mul_div_cancel₀ _ hn, Real.exp_log (IdeleGroup.ideleModule F x).2] at h3
    exact h3)
  have h4 : (e t)⁻¹ * x ∈ IdeleGroup.normOneSubgroup F := by
    rw [IdeleGroup.normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
  have h5 := hm (e t) ((e t)⁻¹ * x)
  rw [mul_inv_cancel_left, eq_zero_of_normOne f hc hm hk _ h4, add_zero, h1, ht] at h5
  rw [h5]; ring


open GlobalTheory.Mem.Chr.CharModel in
theorem exists_norm_eq_exp (ω : HChar F) :
    ∃ c : ℝ, ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ = Real.exp (c * logNorm F x) := by
  have h0 : ∀ x, ‖((ω.1 x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (Units.ne_zero _)
  obtain ⟨a, ha⟩ := exists_eq_mul_log_module (F := F) (fun x => Real.log ‖((ω.1 x : ℂˣ) : ℂ)‖)
    ((Units.continuous_val.comp ω.2.1).norm.log h0)
    (fun x y => by rw [map_mul, Units.val_mul, norm_mul, Real.log_mul (h0 x) (h0 y)])
    (fun k => by
      have : ω.1 (IdeleGroup.diagonal F k) = 1 := ω.2.2 k
      rw [this]; simp)
  obtain ⟨b, hb⟩ := exists_eq_mul_log_module (F := F) (logNorm F) (continuous_logNorm F) (logNorm_mul F)
    (logNorm_principal F)
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine absChar_not_unitary (F := F) fun x => ?_
    change ‖Complex.exp (1 * logNorm F x)‖ = 1
    rw [hb]; simp
  refine ⟨a / b, fun x => ?_⟩
  rw [← Real.exp_log (norm_pos_iff.2 (Units.ne_zero (ω.1 x))), ha x, hb x]
  congr 1
  field_simp

end GlobalTheory.AbsTwist

namespace GlobalTheory.CuspRep.CG

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.CharModel GlobalTheory.HeckeGal.Model

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_val_apply (t : ℝ) (x : Ideles E) :
    (((absPow E t).1 x : ℂˣ) : ℂ) = Complex.exp ((t : ℂ) * logNorm E x) := rfl


omit [_root_.NumberField.IsTotallyComplex E] in
theorem absPow_neg_mul (t : ℝ) : absPow E (-t) * absPow E t = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change (((absPow E (-t)).1 x : ℂˣ) : ℂ) * (((absPow E t).1 x : ℂˣ) : ℂ) = 1
  rw [absPow_val_apply, absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem exists_isUnitary_twist_absPow (π : CG E a) (ha : 1 ≤ a) :
    ∃ (π₀ : CG E a) (t : ℝ), π₀.IsUnitary ∧ π = π₀.twist (absPow E t) := by
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  obtain ⟨c, hc⟩ := GlobalTheory.AbsTwist.exists_norm_eq_exp ω
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  refine ⟨π.twist (absPow E (-(c / a))), c / a, ⟨_, fun x => ?_, hω.twist _⟩, ?_⟩
  · change ‖((ω.1 x : ℂˣ) : ℂ) * ((((absPow E (-(c / a))).1 x) ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_pow_eq_pow_val, absPow_val_apply, norm_mul, norm_pow, hc x,
      show ((-(c / a) : ℝ) : ℂ) * (logNorm E x : ℂ) = ((-(c / a) * logNorm E x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_eq_one_iff]
    field_simp
    ring
  · rw [← twist_mul, absPow_neg_mul, twist_one]

theorem HasSat.twist {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    {ν : HChar E} (hν : ν.UnrAt w) : (π.twist ν).HasSat w (B.map (· * ν.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ ν w B hν h


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_val_absPow (t : ℝ) (w : HeightOneSpectrum (𝓞 E)) :
    ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) := by
  have hq : 1 < Ideal.absNorm w.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm w
  rw [(absPow_isAbsPow E t).2.1 w, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hq), Complex.neg_re,
    Complex.ofReal_re]

theorem HasSat.twist_absPow {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B)
    (t : ℝ) : (π.twist (absPow E t)).HasSat w (B.map (· * (absPow E t).val w)) ∧
      ‖(((absPow E t).val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-t) :=
  ⟨h.twist ((absPow_isAbsPow E t).1 w), norm_val_absPow t w⟩

end GlobalTheory.CuspRep.CG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.WeilPairing


set_option maxHeartbeats 1000000 in
theorem thetaInner_weilRep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  intro D ψ V W χV χW om μ 𝓕 hom hc p a b ha hb
  have h := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hom μ 𝓕 hc p b a hb ha
  have e : ∀ (f g : WO V W → ℂ), thetaIP μ 𝓕 f g = ∫ w in 𝓕, g w * (starRingEnd ℂ) (f w) ∂μ := fun f g => by
    unfold thetaIP
    congr 1
    funext w
    exact mul_comm _ _
  rw [e, e]
  exact h

end GlobalTheory.WeilPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pairing_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  first | exact @GlobalTheory.WeilPairing.thetaInner_weilRep | exact GlobalTheory.WeilPairing.thetaInner_weilRep | (intros; apply GlobalTheory.WeilPairing.thetaInner_weilRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
open NumberField Formalism.IndefR.NX

namespace GlobalTheory

theorem isKsForm_of_formsIso {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G') :
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  intro f hA'
  obtain ⟨n, b, hmem, _hKi, hKs, hLi, hLs⟩ := hA'
  have hmem' : ∀ i, f.e.symm (b i) ∈ A.WK := fun i => (f.wk _).2 (by simpa using hmem i)
  have hLi' : LinearIndependent LL (fun i => f.e.symm (b i)) :=
    hLi.map' f.e.symm.toLinearMap (LinearEquiv.ker _)
  refine ⟨n, fun i => f.e.symm (b i), hmem', ?_, ?_, hLi', ?_⟩
  · refine LinearIndependent.restrict_scalars (K := LL) ?_ hLi'
    intro r s h
    have h' : algebraMap Ks LL r = algebraMap Ks LL s := by
      simpa [Algebra.algebraMap_eq_smul_one] using h
    exact (algebraMap Ks LL).injective h'
  · apply le_antisymm
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 hmem')
    · intro y hy
      have hy' : f.e y ∈ Submodule.span Ks' (Set.range b) := by rw [hKs]; exact (f.wk y).1 hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ks').1 hy'
      have hyeq : y = ∑ i, f.eK.symm (c i) • f.e.symm (b i) := by
        have : y = f.e.symm (∑ i, c i • b i) := by rw [hc]; simp
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul LL (c i) (b i), LinearEquiv.map_smul, ← algebraMap_smul LL (f.eK.symm (c i)),
          ← f.eK_LL, RingEquiv.apply_symm_apply]
      rw [hyeq]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have : Set.range (fun i => f.e.symm (b i)) = f.e.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, show (⇑f.e.symm : WL' → WL) = ⇑(f.e.symm : WL' →ₗ[LL] WL) from rfl, Submodule.span_image, hLs,
      Submodule.map_top, LinearEquiv.range]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIsoStatement
open NumberField Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKsForm_of_algebraicFormsIso : ∀ {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G'),
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  first | exact @GlobalTheory.isKsForm_of_formsIso | exact GlobalTheory.isKsForm_of_formsIso | (intros; apply GlobalTheory.isKsForm_of_formsIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ρ : IrrGL (k := k)} {hρ : ρ.IsCusp} {c d c' d' : ℤ} {h : c ≤ d} {h' : c' ≤ d'} {Δ Δ' : Segment k}

theorem first_mem_carrier (Δ : Segment k) : Δ.first ∈ Δ.carrier := mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩

theorem nu_mem_icc {a : ℤ} : ρ.nu a ∈ (icc ρ hρ c d h).carrier ↔ c ≤ a ∧ a ≤ d := by
  simp only [mem_icc, IrrGL.nu_intCast_inj hρ.1]
  exact ⟨fun ⟨_, h1, h2, e⟩ => e ▸ ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2, rfl⟩⟩

theorem eq_icc_of_first_eq (hρ : ρ.IsCusp) (e : Δ.first = ρ.nu c) :
    Δ = icc ρ hρ c (c + Δ.len - 1) (Int.le_sub_one_of_lt (lt_add_of_pos_right c (Nat.cast_pos.2 Δ.len_pos))) :=
  ext_first e (by simp only [icc, len_ofFirst]; omega)

theorem exists_eq_icc_of_mem (hρ : ρ.IsCusp) {a : ℤ} (ha : ρ.nu a ∈ Δ.carrier) :
    ∃ (c d : ℤ) (h : c ≤ d), Δ = icc ρ hρ c d h := by
  obtain ⟨b, -, hb⟩ := mem_carrier.1 ha
  refine ⟨a - b, _, _, eq_icc_of_first_eq hρ ?_⟩
  have := congrArg (fun x => IrrGL.nu x (-(b : ℂ))) hb
  simpa [sub_eq_add_neg] using this

theorem icc_subset_icc : (icc ρ hρ c d h).carrier ⊆ (icc ρ hρ c' d' h').carrier ↔ c' ≤ c ∧ d ≤ d' := by
  refine ⟨fun H => ⟨(nu_mem_icc.1 (H (nu_mem_icc.2 ⟨le_rfl, h⟩))).1, (nu_mem_icc.1 (H (nu_mem_icc.2 ⟨h, le_rfl⟩))).2⟩,
    fun ⟨h1, h2⟩ x hx => ?_⟩
  obtain ⟨a, h3, h4, rfl⟩ := mem_icc.1 hx
  exact nu_mem_icc.2 ⟨h1.trans h3, h4.trans h2⟩

theorem exists_carrier_eq_union_icc :
    (∃ Γ : Segment k, Γ.carrier = (icc ρ hρ c d h).carrier ∪ (icc ρ hρ c' d' h').carrier) ↔
      c' ≤ d + 1 ∧ c ≤ d' + 1 := by
  constructor
  · rintro ⟨Γ, hΓ⟩
    obtain ⟨e, f, hef, rfl⟩ := exists_eq_icc_of_mem (Δ := Γ) hρ (a := c)
      (by rw [hΓ]; exact Or.inl (nu_mem_icc.2 ⟨le_rfl, h⟩))
    have key : ∀ a : ℤ, (e ≤ a ∧ a ≤ f) ↔ (c ≤ a ∧ a ≤ d) ∨ (c' ≤ a ∧ a ≤ d') := fun a => by
      simpa only [Set.mem_union, nu_mem_icc] using Set.ext_iff.1 hΓ (ρ.nu a)
    have := key c; have := key d'; have := key c'; have := key d; have := key (d + 1); have := key (d' + 1)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨icc ρ hρ (min c c') (max d d') (by omega), Set.ext fun x => ?_⟩
    simp only [Set.mem_union, mem_icc]
    constructor
    · rintro ⟨a, h3, h4, rfl⟩
      by_cases ha : c ≤ a ∧ a ≤ d
      · exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
      · exact Or.inr ⟨a, by omega, by omega, rfl⟩
    · rintro (⟨a, h3, h4, rfl⟩ | ⟨a, h3, h4, rfl⟩) <;> exact ⟨a, by omega, by omega, rfl⟩

theorem linked_icc : (icc ρ hρ c d h).Linked (icc ρ hρ c' d' h') ↔
    (c < c' ∧ c' ≤ d + 1 ∧ d < d') ∨ (c' < c ∧ c ≤ d' + 1 ∧ d' < d) := by
  rw [Linked, exists_carrier_eq_union_icc, icc_subset_icc, icc_subset_icc]
  omega

theorem precedes_icc : (icc ρ hρ c d h).Precedes (icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d' := by
  have key : (∃ j : ℕ, 0 < j ∧ (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j) ↔ c < c' := by
    have e : ∀ j : ℕ, (icc ρ hρ c' d' h').first = (icc ρ hρ c d h).first.nu j ↔ c' = c + j := fun j => by
      rw [← IrrGL.nu_intCast_inj hρ.1]
      simp [icc]
    simp only [e]
    exact ⟨fun ⟨j, h1, h2⟩ => by omega, fun H => ⟨(c' - c).toNat, by omega, by omega⟩⟩
  rw [Precedes, linked_icc, key]
  omega

theorem Linked.exists_eq_icc (H : Linked Δ Δ') : ∃ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
    Δ = icc ρ hρ c d h ∧ Δ' = icc ρ hρ c' d' h' := by
  obtain ⟨⟨Γ, hΓ⟩, -⟩ := H
  have key : ∀ D : Segment k, D.carrier ⊆ Γ.carrier → ∃ (c d : ℤ) (h : c ≤ d), D = icc Γ.first Γ.isCusp_first c d h :=
    fun D hD => by
      obtain ⟨a, -, ha⟩ := mem_carrier.1 (hD D.first_mem_carrier)
      exact ⟨a, _, _, eq_icc_of_first_eq _ (by simpa using ha.symm)⟩
  obtain ⟨c, d, h, e⟩ := key Δ (hΓ ▸ Set.subset_union_left)
  obtain ⟨c', d', h', e'⟩ := key Δ' (hΓ ▸ Set.subset_union_right)
  exact ⟨_, _, c, d, c', d', h, h', e, e'⟩

theorem linked_iff_precedes : Linked Δ Δ' ↔ Precedes Δ Δ' ∨ Precedes Δ' Δ := by
  refine ⟨fun H => ?_, fun H => H.elim (·.1) (·.1.symm)⟩
  obtain ⟨ρ, hρ, c, d, c', d', h, h', rfl, rfl⟩ := H.exists_eq_icc
  simpa only [precedes_icc] using linked_icc.1 H

theorem precedes_iff : Precedes Δ Δ' ↔
    ∃ j : ℕ, 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len ∧ Δ'.first = Δ.first.nu j := by
  have key : ∀ j : ℕ, Δ'.first = Δ.first.nu j → (Precedes Δ Δ' ↔ 0 < j ∧ j ≤ Δ.len ∧ Δ.len < j + Δ'.len) := fun j e => by
    have e1 := eq_icc_of_first_eq (Δ := Δ) (c := 0) Δ.isCusp_first (by simp)
    have e2 := eq_icc_of_first_eq (Δ := Δ') (c := j) Δ.isCusp_first (by simpa using e)
    refine (iff_of_eq (congrArg₂ Precedes e1 e2)).trans (precedes_icc.trans ?_)
    omega
  refine ⟨fun H => ?_, fun ⟨j, h1, h2, h3, e⟩ => (key j e).2 ⟨h1, h2, h3⟩⟩
  obtain ⟨j, -, e⟩ := H.2
  obtain ⟨h1, h2, h3⟩ := (key j e).1 H
  exact ⟨j, h1, h2, h3, e⟩

theorem exists_first_eq_of_transGen (H : Relation.TransGen Precedes Δ Δ') :
    ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j := by
  induction H with
  | single H => exact H.2
  | tail _ H ih =>
    obtain ⟨i, hi, e⟩ := ih
    obtain ⟨j, -, e'⟩ := H.2
    exact ⟨i + j, by omega, by rw [e', e, IrrGL.nu_nu, Nat.cast_add]⟩

theorem not_transGen_precedes_self (Δ : Segment k) : ¬ Relation.TransGen Precedes Δ Δ := fun H => by
  obtain ⟨j, hj, e⟩ := exists_first_eq_of_transGen H
  exact hj.ne ((IrrGL.nu_natCast_inj Δ.isCusp_first.1).1 (by simpa using e))

theorem Precedes.asymm (H : Precedes Δ Δ') : ¬ Precedes Δ' Δ := fun H' =>
  not_transGen_precedes_self Δ ((Relation.TransGen.single H).tail H')

theorem lt_of_precedes_nu {x y : ℝ} (H : (Δ.nu x).Precedes (Δ.nu y)) : x < y := by
  obtain ⟨-, j, hj, e⟩ := H
  have e' : Δ.first.nu y = Δ.first.nu ((x + j : ℝ) : ℂ) := by
    push_cast
    exact e.trans (Δ.first.nu_nu x j)
  have : (0 : ℝ) < j := Nat.cast_pos.2 hj
  rw [(IrrGL.nu_ofReal_inj Δ.isCusp_first.1).1 e']
  linarith

theorem not_precedes_nu (Δ : Segment k) {x y : ℝ} (hxy : y < x) : ¬ (Δ.nu x).Precedes (Δ.nu y) := fun H =>
  hxy.asymm (lt_of_precedes_nu H)

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

theorem exists_list_pairwise_not_rel {α : Type*} {r : α → α → Prop} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (m : Multiset α) : ∃ l : List α, (l : Multiset α) = m ∧ l.Pairwise fun a b => ¬ r a b := by
  classical
  let p : α → α → Prop := fun a b => Relation.ReflTransGen r b a
  haveI : IsPartialOrder α p :=
    { refl := fun _ => .refl
      trans := fun _ _ _ h h' => h'.trans h
      antisymm := fun a b h h' => by
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with e | h
        · exact e
        · exact absurd (h.trans_left h') (hr _) }
  obtain ⟨s, hs, hps⟩ := extend_partialOrder p
  refine ⟨m.sort s, m.sort_eq s, (m.pairwise_sort s).imp fun {a b} hab h => ?_⟩
  obtain rfl : a = b := antisymm hab (hps _ _ (.single h))
  exact hr a (.single h)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOrderedForm (𝔪 : Multiset (Segment k)) :
    ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪 := by
  obtain ⟨l, rfl, hl⟩ := exists_list_pairwise_not_rel Segment.not_transGen_precedes_self 𝔪
  exact ⟨l.get, (Fin.univ_val_map l.get).trans (congrArg _ (List.ofFn_get l)), List.pairwise_iff_get.1 hl⟩

theorem isOrderedForm_tw_iff {h : ℕ} {Δ : Fin h → Segment k} {𝔪 : Multiset (Segment k)} (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪 :=
  ⟨fun H => by simpa only [Multiset.map_map, Function.comp_def, Segment.tw_tw_inv, Multiset.map_id'] using H.tw χ⁻¹ hχ.inv,
    fun H => H.tw χ hχ⟩

theorem precedes_and_orderedForms (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] :
    ((∀ Δ Δ' : Segment k, Δ.Precedes Δ' → ¬ Δ'.Precedes Δ) ∧
      (∀ Δ : Segment k, ¬ Relation.TransGen Segment.Precedes Δ Δ) ∧
      ∀ 𝔪 : Multiset (Segment k), ∃ Δ : Fin 𝔪.card → Segment k, IsOrderedForm Δ 𝔪) ∧
    ((∀ (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (c d c' d' : ℤ) (h : c ≤ d) (h' : c' ≤ d'),
        (Segment.icc ρ hρ c d h).Precedes (Segment.icc ρ hρ c' d' h') ↔ c < c' ∧ c' ≤ d + 1 ∧ d < d') ∧
      ∀ Δ Δ' : Segment k, Δ.Linked Δ' ↔ Δ.Precedes Δ' ∨ Δ'.Precedes Δ) ∧
    (∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Linked (Δ'.tw χ hχ) ↔ Δ.Linked Δ') ∧
      (∀ Δ Δ' : Segment k, (Δ.tw χ hχ).Precedes (Δ'.tw χ hχ) ↔ Δ.Precedes Δ') ∧
      ∀ (h : ℕ) (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)),
        IsOrderedForm (fun i => (Δ i).tw χ hχ) (𝔪.map (·.tw χ hχ)) ↔ IsOrderedForm Δ 𝔪) ∧
    ∀ (Δ : Segment k) (x y : ℝ), y < x → ¬ (Δ.nu x).Precedes (Δ.nu y) :=
  ⟨⟨fun _ _ => Segment.Precedes.asymm, Segment.not_transGen_precedes_self, exists_isOrderedForm⟩,
    ⟨fun _ _ _ _ _ _ _ _ => Segment.precedes_icc, fun _ _ => Segment.linked_iff_precedes⟩,
    fun χ hχ => ⟨fun _ _ => Segment.linked_tw_iff χ hχ, fun _ _ => Segment.precedes_tw_iff χ hχ,
      fun _ _ _ => isOrderedForm_tw_iff χ hχ⟩,
    fun Δ _ _ h => Δ.not_precedes_nu h⟩

end GlobalTheory.LocGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segment_nu_nu (Δ : Segment k) (a b : ℂ) : (Δ.nu a).nu b = Δ.nu (a + b) :=
  Segment.ext_first (show (Δ.first.nu a).nu b = Δ.first.nu (a + b) from IrrGL.nu_nu _ _ _) rfl

theorem isLSeg_nu {Δ : Segment k} {x : IrrGL (k := k)} (h : IsLSeg Δ x.rep) (s : ℂ) : IsLSeg (Δ.nu s) (x.nu s).rep :=
  (h.tw _ _).of_equiv (x.twEquiv _ _)

theorem univ_map_speh_segments (d m : ℕ) (Δ : Fin m → Segment k) (s : Fin m → ℝ) :
    Finset.univ.val.map (fun p : Fin (d * m) => ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)) = ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) := by
  rw [Fin.univ_val_map]
  congr 1
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have : ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j) := fun h => by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv_apply_val]; ring
  simp only [Function.comp, this]

end SlopeTestRemainingChoices

theorem speh_quotient_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        GlobalTheory.SmGL.twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  intro k _ _ _ _ _ hLM hprec hstage a V _ _ σ m δ Δ s hΔ hδu hs hd hσ d n hdn W _ _ σ' hirr hf
  obtain ⟨φ⟩ := hσ
  obtain ⟨f, hfs⟩ := hf
  let y : Fin d → Fin m → IrrGL (k := k) := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = a := fun _ => hd
  let Y : Fin (d * m) → IrrGL (k := k) := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = n := by
    rw [← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (prodIrr (y i) (hN i)) :=
    fun i => (twistEquiv φ _).trans (prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _))
  obtain ⟨e2⟩ := hstage d m y (fun _ => a) n hN hdn hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact isLSeg_nu (isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, segment_nu_nu] at hP
    have key := hprec (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j') (hδu j')
      (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ))) (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hLM k _ (d * m) n Y hM' hLF
  obtain ⟨ψ⟩ := hπ.equiv_of_surjective hirr (f.comp E.symm.toIntertwiningMap)
    (hfs.comp E.symm.toLinearEquiv.surjective)
  exact ⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsLStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        GlobalTheory.SmGL.twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  first | exact @GlobalTheory.speh_quotient_isL | exact GlobalTheory.speh_quotient_isL | (intros; apply GlobalTheory.speh_quotient_isL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

noncomputable section

namespace GlobalTheory.SupercuspUnitary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def scal (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {h | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ y, l (ρ h y) = c * l y}
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], fun y => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha, hb, mul_assoc]
  one_mem' := ⟨1, by simp, fun y => by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun y => ?_⟩
    have h := ha (ρ a⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

def term (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))

theorem term_mul {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (v w : V) (g : G) {h : G}
    (hh : h ∈ scal ρ l) : term ρ l v w (g * h) = term ρ l v w g := by
  obtain ⟨c, hc, hl⟩ := (scal ρ l).inv_mem hh
  have h1 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [term, mul_inv_rev, map_mul, Module.End.mul_apply, hl]
  linear_combination (l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))) * h1

theorem term_inv_mul (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (x g : G) :
    term ρ l v w (x⁻¹ * g) = term ρ l (ρ x v) (ρ x w) g := by
  simp only [term, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

def qterm (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (q : G ⧸ scal ρ l) : ℂ :=
  term ρ l v w q.out

theorem qterm_mk (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) :
    qterm ρ l v w (g : G ⧸ scal ρ l) = term ρ l v w g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (scal ρ l) g
  rw [qterm, hh, term_mul v w g h.2]

theorem center_le_scal {ρ : Representation ℂ G V} (l : Module.Dual ℂ V)
    (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) :
    Subgroup.center G ≤ scal ρ l := fun z hz' => by
  obtain ⟨c, hc, h⟩ := hz z hz'
  exact ⟨c, hc, fun y => by rw [h, map_smul, smul_eq_mul]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_scal {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual) :
    IsOpen (scal ρ l : Set G) := by
  refine (scal ρ l).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((show IsOpen
    {g : G | ρ.dual g l = l} from hl).mem_nhds (by
      simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg => ⟨1, by simp, fun y => ?_⟩)
  have h1 : (ρ.dual g l) (ρ g y) = l (ρ g y) := by rw [show ρ.dual g l = l from hg]
  rw [Representation.dual_apply] at h1
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply] at h1
  rw [one_mul, h1]

theorem exists_finset {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual)
    (hsc : IsSupercuspidal ρ) (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v)
    (v : V) : ∃ s : Finset (G ⧸ scal ρ l), ∀ g : G, l (ρ g⁻¹ v) ≠ 0 → (g : G ⧸ scal ρ l) ∈ s := by
  obtain ⟨C, hC, hCz⟩ := hsc.2 v l hl
  haveI := QuotientGroup.discreteTopology (isOpen_scal hl)
  have hD : ((fun c : G => ((c⁻¹ : G) : G ⧸ scal ρ l)) '' C).Finite :=
    (hC.image (by fun_prop)).finite_of_discrete
  refine ⟨hD.toFinset, fun g hg => ?_⟩
  obtain ⟨z, hz', c, hc, e⟩ := hCz g⁻¹ hg
  rw [Set.Finite.mem_toFinset]
  refine ⟨c, hc, QuotientGroup.eq.2 ?_⟩
  have h2 : (c⁻¹)⁻¹ * g = z⁻¹ := by rw [← inv_inv g, e]; group
  rw [h2]
  exact center_le_scal l hz (inv_mem hz')

end GlobalTheory.SupercuspUnitary

namespace GlobalTheory


open GlobalTheory.SupercuspUnitary in
theorem isUnitarisable_of_isSupercuspidal : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual →
    l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ →
    (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  intro G V _ _ _ _ _ ρ l hl hl0 hirr hsc hz
  have hfin : ∀ v w, (Function.support (qterm ρ l v w)).Finite := fun v w => by
    obtain ⟨s, hs⟩ := exists_finset hl hsc hz v
    refine s.finite_toSet.subset fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Function.mem_support, qterm_mk] at hq
      exact hs g (left_ne_zero_of_mul hq)

  have hadd1 : ∀ v v' w q, qterm ρ l (v + v') w q = qterm ρ l v w q + qterm ρ l v' w q := by
    intro v v' w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), add_mul]
  have hsmul1 : ∀ (a : ℂ) v w q, qterm ρ l (a • v) w q = a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w' q, qterm ρ l v (w + w') q = qterm ρ l v w q + qterm ρ l v w' q := by
    intro v w w' q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add (f := _), mul_add]
  have hsmul2 : ∀ (a : ℂ) v w q, qterm ρ l v (a • w) q = starRingEnd ℂ a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_smul, smul_eq_mul, map_mul]
      ring
  have hconj : ∀ v w q, qterm ρ l w v q = starRingEnd ℂ (qterm ρ l v w q) := by
    intro v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_mul, Complex.conj_conj]
      ring
  have hinv : ∀ (x : G) v w q, qterm ρ l (ρ x v) (ρ x w) q = qterm ρ l v w (x⁻¹ • q) := by
    intro x v w q
    induction q using QuotientGroup.induction_on with
    | H g => rw [MulAction.Quotient.smul_mk, smul_eq_mul, qterm_mk, qterm_mk, term_inv_mul]
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∑ᶠ q, qterm ρ l v w q)
    (fun v v' w => by simp only [hadd1]; exact finsum_add_distrib (hfin v w) (hfin v' w))
    (fun a v w => by simp only [hsmul1, RingHom.id_apply, smul_eq_mul, mul_finsum])
    (fun v w w' => by simp only [hadd2]; exact finsum_add_distrib (hfin v w) (hfin v w'))
    (fun a v w => by simp only [hsmul2, smul_eq_mul, mul_finsum])
  have hB : ∀ v w, B v w = ∑ᶠ q, qterm ρ l v w q := fun v w => LinearMap.mk₂'ₛₗ_apply _ _ _
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun x v w => ?_⟩
  · rw [hB, hB, map_finsum _ (hfin v w)]
    exact finsum_congr fun q => hconj v w q
  · have hex : ∃ g : G, l (ρ g v) ≠ 0 := by
      by_contra! h0
      let U : Subrepresentation ρ :=
        { toSubmodule := ⨅ g : G, LinearMap.ker (l ∘ₗ (ρ g : V →ₗ[ℂ] V))
          apply_mem_toSubmodule := fun g y hy => by
            simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
            intro g'
            rw [← Module.End.mul_apply, ← map_mul]
            exact hy _ }
      haveI := hirr
      rcases eq_bot_or_eq_top U with hU | hU
      · have hvU : v ∈ U.toSubmodule := by
          simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
          exact h0
        rw [hU] at hvU
        exact hv ((Submodule.mem_bot ℂ).1 hvU)
      · refine hl0 (LinearMap.ext fun y => ?_)
        have hyU : y ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hyU
        simpa using hyU 1
    obtain ⟨g, hg⟩ := hex
    rw [hB, finsum_eq_sum _ (hfin v v), Complex.re_sum]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨((g⁻¹ : G) : G ⧸ scal ρ l), ?_, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H g' =>
        rw [qterm_mk, term, Complex.mul_conj, Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    · rw [Set.Finite.mem_toFinset, Function.mem_support, qterm_mk, term, inv_inv, Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 hg).ne'
    · rw [qterm_mk, term, inv_inv, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_pos.2 hg
  · rw [hB, hB]
    simp only [hinv]
    exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ : G) : Equiv.Perm (G ⧸ scal ρ l))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.BadPlace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


open Classical in
def datP (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (e : AE D) : WO (Vc D i) (Wc D i) → ℂ :=
  fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
      omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
    else 0

end GlobalTheory.BadPlace

end
end
