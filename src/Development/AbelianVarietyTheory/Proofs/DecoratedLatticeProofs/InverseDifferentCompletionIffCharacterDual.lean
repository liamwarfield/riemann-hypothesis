module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.DiffDual

variable {D : D7}

def TrInt (D : D7) (x : D.host.E) : Prop := ∀ o : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (x * o) = n

theorem mem_dI_iff (x : D.host.E) : x ∈ dI D ↔ TrInt D x := by
  rw [dI, Formalism.L2.Pj.dual_eq Formalism.IndefR.Fin.factPrincipalDatum D,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) _ _ _)]
  constructor
  · intro h o
    obtain ⟨n, hn⟩ := h _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply] at hn
    rw [← hn]; simp
  · intro h b hb
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨n, hn⟩ := h o
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl, hn]; simp

theorem TrInt.mul {x : D.host.E} (h : TrInt D x) (o : 𝓞 D.host.E) : TrInt D (x * o) := fun o' => by
  obtain ⟨n, hn⟩ := h (o * o')
  exact ⟨n, by rw [mul_assoc]; simpa using hn⟩

theorem trInt_coe (o : 𝓞 D.host.E) : TrInt D (o : D.host.E) := fun o' => by
  have hi : IsIntegral ℤ ((o : D.host.E) * o') := o.isIntegral_coe.mul o'.isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace (L := ℚ) hi)
  exact ⟨n, hn.symm⟩

theorem chi_tmul {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F}
    (hβ : β ∈ intAf D.host.F) {x : D.host.E} (hx : TrInt D x) : Conductor.chi ψ (β ⊗ₜ[D.host.F] x) = 1 := by
  rw [Conductor.chi, GlobalTheory.LatVac.trace_tmul]
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 _ (fun a => ?_) _ hβ
  rw [← smul_eq_mul, ← map_smul, GlobalTheory.LatVac.char_rat hψ]
  have hi : IsIntegral ℤ (algebraMap D.host.F D.host.E (a : D.host.F)) :=
    a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  obtain ⟨n, hn⟩ := hx ⟨_, hi⟩
  exact ⟨n, by rw [Algebra.smul_def, mul_comm]; exact hn⟩

theorem chi_mul_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {x : D.host.E} (hx : TrInt D x)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Conductor.chi ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨β, hβ, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact chi_tmul hψ hβ (hx.mul o)
  | zero => rw [mul_zero]; exact Conductor.chi_zero ψ
  | add y y' _ _ hy hy' => rw [mul_add, Conductor.chi_add, hy, hy', one_mul]
  | neg y _ hy =>
    have := Conductor.chi_add ψ (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * y) (((1 : Af D.host.F) ⊗ₜ[D.host.F] x) * -y)
    rwa [← mul_add, add_neg_cancel, mul_zero, Conductor.chi_zero, hy, one_mul, eq_comm] at this

theorem psiE_add (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) : psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  rw [psiE, psiE, psiE, map_add (f := _), ψ.map_add_eq_mul]

theorem psiE_zero (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  rw [psiE, map_zero, ψ.map_zero_eq_one]

theorem psiE_neg (ψ : AddChar (AF D.host.F) ℂ) (a : AE D) : psiE ψ (-a) = (psiE ψ a)⁻¹ := by
  rw [psiE, psiE, map_neg, ψ.map_neg_eq_inv]

theorem forward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idV (dI D) v) : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  induction hs using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, rfl⟩ := hy
    intro o ho
    have hinf : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] a * o) = 0 := by
      rw [RingHom.map_mul, GlobalTheory.LatVac.infPart_pair, zero_mul]
    rw [Conductor.psiE_eq_chi ψ hinf, RingHom.map_mul, GlobalTheory.LatVac.finPart_pair]
    have e : α ⊗ₜ[D.host.F] a = ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) * (α ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e, mul_assoc]
    exact chi_mul_int hψ ((mem_dI_iff a).1 ha) (Conductor.mul_mem_int (Conductor.tmul_mem hα 1) ho.2)
  | zero => intro o _; rw [zero_mul, psiE_zero]
  | add x y _ _ hx hy => intro o ho; rw [add_mul, psiE_add, hx o ho, hy o ho, one_mul]
  | neg x _ hx => intro o ho; rw [neg_mul, psiE_neg, hx o ho, inv_one]

def lift (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem lift_tmul (α : Af D.host.F) (x : D.host.E) : lift D (α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 α ⊗ₜ[D.host.F] x := rfl

theorem finPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (lift D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.finPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem infPart_lift (z : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (lift D z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul α x => rw [lift_tmul, GlobalTheory.LatVac.infPart_pair]
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem eq_lift {s : AE D} (h : infPart D s = 0) : s = lift D (finPart D s) := by
  rw [← sub_eq_zero]
  refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
  · rw [RingHom.map_sub, h, infPart_lift, sub_zero]
  · rw [RingHom.map_sub, finPart_lift, sub_self]

theorem lift_int_mem (v : Pl D) (hε : singleV D.host.F v 1 ∈ intAf D.host.F) {u : Af D.host.F ⊗[D.host.F] D.host.E}
    (hu : u ∈ intAE D) : lift D ((singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u) ∈ idV (dI D) v := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, o, rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.mul_mem_intAf hε hβ, fun w hw => ?_, (o : D.host.E),
      (mem_dI_iff _).2 (trInt_coe o), lift_tmul _ _⟩
    rw [map_mul, Conductor.ev_ne hw, zero_mul]
  | zero => rw [mul_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg, map_neg]; exact neg_mem hx

theorem backward {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (v : Pl D) {s : AE D}
    (hs : s ∈ idAt D (· = v)) (h : ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) : s ∈ idV (dI D) v := by
  have hs1 : infPart D s = 0 := hs.1
  have hinf : ∀ o, infPart D (s * o) = 0 := fun o => by
    rw [RingHom.map_mul, hs1, zero_mul]
  have hz : (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D s = finPart D s :=
    Conductor.idem_mul v _ fun w hw => (Submodule.mem_iInf _).1 hs.2 ⟨w, hw⟩
  obtain ⟨x, u, hu, e⟩ := Conductor.approx (finPart D s)
  have hε : singleV D.host.F v 1 ∈ intAf D.host.F := by
    have := Conductor.idem_mul_mem (v := v) (α := 1) (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at this
  have hx : TrInt D x := fun o => by
    have h1 := h _ (Conductor.lift_mem v o)
    have e1 : singleV D.host.F v 1 ⊗ₜ[D.host.F] (o : D.host.E) =
        (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * (1 ⊗ₜ[D.host.F] (o : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Conductor.psiE_eq_chi ψ (hinf _), RingHom.map_mul, GlobalTheory.LatVac.finPart_pair, e1, ← mul_assoc,
      mul_comm (finPart D s), hz, e, add_mul, Conductor.chi_add,
      Conductor.chi_int hψ (Conductor.mul_mem_int hu (Conductor.tmul_mem (GlobalTheory.LatVac.one_mem_intAf _) o)), mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one] at h1
    exact (Conductor.chi_rat hψ _).1 h1
  have hfin : finPart D s = singleV D.host.F v 1 ⊗ₜ[D.host.F] x +
      (singleV D.host.F v 1 ⊗ₜ[D.host.F] (1 : D.host.E)) * u := by
    rw [← hz, e, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [eq_lift hs1, hfin, map_add (f := _)]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hε, fun w hw => Conductor.ev_ne hw, x, (mem_dI_iff x).2 hx,
    lift_tmul _ _⟩) (lift_int_mem v hε hu)

theorem idV_dI_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D),
    ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 :=
  fun _ _ hψ v _ hs => ⟨fun h => forward hψ v h, backward hψ v hs⟩

end GlobalTheory.SeeSaw.DiffDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseDifferentCompletion_iff_characterDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D), ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  first | exact @GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | exact GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | (intros; apply GlobalTheory.SeeSaw.DiffDual.idV_dI_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModel_valueAtZero_equivariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 = s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  first | exact @GlobalTheory.Unf.FB.evalAt_zero_equivariant | exact GlobalTheory.Unf.FB.evalAt_zero_equivariant | (intros; apply GlobalTheory.Unf.FB.evalAt_zero_equivariant <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UnipAct

variable {D : D7}

theorem levi_mem_flag {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    d.levi u ∈ flagN d :=
  d.levi_mem_NFlag hu

theorem psiUni_mul_of_mem (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {u v : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) (hv : v ∈ UX D ρ) : psiUni ψ (u * v) = psiUni ψ u * psiUni ψ v := by
  have h : ∀ a, psiFlag ψ d (d.levi a) = psiUni ψ a := fun a => by
    have := psiFlag_levi_mul ψ d a (one_mem (stabX d))
    rwa [mul_one] at this
  rw [← h, ← h, ← h, map_mul, psiFlag_mul d ψ (levi_mem_flag d hu) (levi_mem_flag d hv)]

theorem flatFB_flagN : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ n ∈ flagN B.d, flatFB s (s.om (1, n) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s Ψ := by
  intro D hD ψ σ J B s Ψ hΨ n hn
  obtain ⟨γ, hγ, hnγ⟩ := ((GlobalTheory.T.mem_besGrp_iff_mt_mul_x0_eq_x0_mul D σ B).1 n).1 (Subgroup.mem_sup_left hn)
  have hψ : psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ γ :=
    (GlobalTheory.T.flagUnipotentRadical_surjects_unitriangular_characters_agree D σ B).2 ψ n hn 1 ⟨γ, hγ⟩ (by rw [map_one, mul_one]; exact hnγ)
  have h1 : mt B.V n⁻¹ ⬝ (x0 B ⬝ γ.1) = x0 B := by
    rw [← hnγ, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hev : ∀ M : Mx D B.V.rank (σ + 1), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n) Ψ) M 0 =
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ M) 0 := by
    intro M
    have := GlobalTheory.T.doubleMixedModel_valueAtZero_equivariant D hD ψ σ J B s Ψ hΨ 1 n hn 1 M
    simp only [map_one, mul_one] at this
    rw [this, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  have := s.vU.unit.1
  funext w
  simp only [flatFB, flatLast, flatAt, flatFun, Pi.smul_apply, smul_eq_mul, hev]
  rw [← integral_const_mul, ← integral_mul_left_eq_self _ (⟨γ, hγ⟩ : UX D (σ + 1))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hm : mt B.V n⁻¹ ⬝ (x0 B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1) = x0 B ⬝ u.1.1 := by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (x0 B), h1]
  change star (psiUni ψ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D))) *
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V n⁻¹ ⬝ (x0 B ⬝ ((⟨γ, hγ⟩ * u : UX D (σ + 1)) : GL (Fin (σ + 1)) (AE D)).1)) 0 w = _
  rw [hm, Subgroup.coe_mul, psiUni_mul_of_mem ψ J.d hγ u.2, star_mul', hψ, mul_assoc]
  rfl

end GlobalTheory.Unf.FB.UnipAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatSchwartzTargetUnipotentConjBesselCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ n ∈ flagN B.d, flatFB s (s.om (1, n) Ψ) = star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • flatFB s Ψ := by
  first | exact @GlobalTheory.Unf.FB.UnipAct.flatFB_flagN | exact GlobalTheory.Unf.FB.UnipAct.flatFB_flagN | (intros; apply GlobalTheory.Unf.FB.UnipAct.flatFB_flagN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

noncomputable section

namespace GlobalTheory.FinPl.LocGen

theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)
  have hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    rw [Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact D.host.ccK_ne_bot
  exact mul_ne_zero hc0 (inv_ne_zero hb0)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPeriodIdealLocalGeneratorAtSplitPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodIdeal_local_generator_at_split_point : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧ ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  first | exact @GlobalTheory.FinPl.LocGen.exists_gen | exact GlobalTheory.FinPl.LocGen.exists_gen | (intros; apply GlobalTheory.FinPl.LocGen.exists_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyIntIn
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel Filter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.GeoInhab
open GlobalTheory.FinPl (SplitPt latV idAt intAt Lat Pl)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt qOf)
open GlobalTheory.SymBridge (IsOrd zPos xPos IsCompl)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsUnif)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem int_dense {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  have pe : ∀ x, q.pr (q.e * x) = q.pr x := fun x => by rw [← q.sec_pr, q.pr_sec]
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pe, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pe]

theorem xi_unit (hu : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have he := (DblInhab.sec_mem_intAt q 1).2 (map_one _).le
  obtain ⟨h1, h2⟩ := hu.1 _ he
  have h3 := DblInhab.pr_le_one q h1
  have h4 := DblInhab.pr_le_one q h2
  rw [map_mul, q.pr_sec, mul_one] at h3 h4
  change valuation k ((q.pr.comp (incA D)) _) ≤ 1 at h4
  rw [map_inv₀, map_inv₀] at h4
  exact le_antisymm h3 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Witness.xi_ne (ofSplit q))))).1 h4)

theorem exists_char (hu : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ ψk, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  have hx := Witness.xi_ne (ofSplit q)
  have hv := xi_unit q hu
  have h1 : q.IsChar ψ (ψk.mulShift (ofSplit q).xi⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, hk]
    change psiE ψ (incA D D.host.xi0 * q.sec _) = _
    rw [mul_comm (incA D _), ← DblInhab.sec_mul_pr]
    change psiE ψ (q.sec (_ * (ofSplit q).xi)) = _
    rw [mul_comm, mul_inv_cancel_left₀ hx]
  have h2 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ _ hψ h1 hu
  refine ⟨ψk, hk, fun x => (Iff.trans ⟨fun h y hy => ?_, fun h y hy => ?_⟩ (h2 x))⟩
  · exact h _ (by simpa [hv] using hy)
  · have := h ((ofSplit q).xi * y) (by simpa [hv] using hy)
    rwa [AddChar.mulShift_apply, inv_mul_cancel_left₀ hx] at this

end Place

section Rat
variable {D : D7}

variable {n : Type} [Fintype n] [DecidableEq n]

end Rat

variable {D : D7}

section Loc
open GlobalTheory.Fam Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.MainNotions

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Links.RealDat D A Ks) (P : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word)
  {a : XGeo D} {y : YRat a} (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf R u (mkGeo m b)))
  {PP : Formalism.L2.DIV.Pl D.host.E} (l : LocX a R.βX PP)


end Loc

end GlobalTheory.QTw.GeoInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SeeSaw.LevRed

open GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem finE_val' (V : HSp D) (g : GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := rfl

theorem exists_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem frGL_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (Formalism.L2.DIV.frGL β y).val * β.val = β.val * (Formalism.L2.DIV.intGL F E n y).val := by
  have h0 : Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL F E n y := inv_mul_cancel_right _ _
  rw [← Units.val_mul, h0, Units.val_mul]

theorem eq_map_of_moved {S K n : Type} [CommRing S] [CommRing K] [Fintype n] [DecidableEq n] (π : S →+* K) (β : GL n S)
    (x y : Matrix n n S) (h1 : x * β.val = β.val * y) (T T' H N M : Matrix n n K) (hT : T' * T = 1)
    (hN : T * β.val.map π = N) (hM : H * N = N * M) (hx : T * x.map π = H * T) : M = y.map π := by
  have h2 : x.map π * β.val.map π = β.val.map π * y.map π := by rw [← Matrix.map_mul, h1, Matrix.map_mul]
  have h3 : N * M = N * y.map π := by
    rw [← hM, ← hN, Matrix.mul_assoc _ _ (y.map π), ← h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hx]
  have h4 : ((β⁻¹).val.map π * T') * N = 1 := by
    rw [← hN, Matrix.mul_assoc, ← Matrix.mul_assoc T', hT, Matrix.one_mul, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  calc M = ((β⁻¹).val.map π * T') * (N * M) := by rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
    _ = y.map π := by rw [h3, ← Matrix.mul_assoc, h4, Matrix.one_mul]


set_option maxHeartbeats 1000000 in
theorem red_of_movedTo (q : SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hN : MovedTo (ofSplit q) V t β N) (hM : (mt V h).map q.pr * N = N * M)
    (hx : Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β) (i j : Fin V.rank) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = (Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j) :
    valuation k (M i j - (ofSplit q).pr (z : D.host.E)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
  obtain ⟨y, hy⟩ := hx
  rw [← hy, Formalism.L2.DIV.redFn_frGL] at hz
  choose l hl using exists_lift (D := D)
  have hπ' : ∀ m : Matrix (Fin V.rank) (Fin V.rank) (AE D), (m.map (toEAf D)).map π' = m.map q.pr := fun m => by
    ext a b; exact hπ _
  have hb : (β.val.map l).map (toEAf D) = β.val := by ext a b; exact hl _
  have hN' : (mt V t).map q.pr * β.val.map π' = N := by
    rw [← hN _ hb, Matrix.map_mul]
    congr 1
    conv_lhs => rw [← hb]
    exact hπ' _
  let ψ := π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have h1 : (Lev.finE V (t⁻¹ * h * t)).val * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E _ y).val := by
    have h0 := frGL_mul β y
    rw [hy] at h0
    exact h0
  have hfin : (Lev.finE V (t⁻¹ * h * t)).val.map π' = (mt V (t⁻¹ * h * t)).map q.pr := by
    rw [finE_val', hπ']
  have h5 := eq_map_of_moved π' β _ _ h1 ((mt V t).map q.pr) ((mt V t⁻¹).map q.pr) _ N M
    (by rw [← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one', Matrix.map_one _ (map_zero _) (map_one _)]) hN' hM
    (by
      rw [hfin, ← Matrix.map_mul, ← Matrix.map_mul, ← mt_mul', ← mt_mul', mul_assoc, mul_inv_cancel_left])
  have h7 : M i j = ψ (y.val i j) := congrFun (congrFun h5 i) j
  have h6 : (ofSplit q).pr (z : D.host.E) = ψ (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
  rw [h7, h6, ← map_sub, ← hred.ker, map_sub, Formalism.L2.DIV.resS_oToS, hz]
  exact sub_self _

end GlobalTheory.SeeSaw.LevRed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FrameMoves

variable {D : D7}

theorem mulVec_of_grpOff (S : HSp D) {v : Pl D} {h : GA D S} (hh : h ∈ grpOff S (· = v))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : mt S h *ᵥ y = y := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hy' : ∀ j, GlobalTheory.FinPlLoc.idem D (· = v) * y j = y j := fun j =>
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hy j)
  ext i
  calc (mt S h *ᵥ y) i = ∑ j, mt S h i j * y j := rfl
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * mt S h i j) * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← hy' j]
        ring
    _ = ∑ j, (GlobalTheory.FinPlLoc.idem D (· = v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
        simp_rw [hij]
    _ = y i := by
        simp [Matrix.one_apply, hy' i]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem map_pr_of_grpOff (p : SplitPt D k) (S : HSp D) {h : GA D S} (hh : h ∈ grpOff S (· = p.v)) :
    (mt S h).map p.pr = 1 := by
  have hM := (GlobalTheory.FinPlLoc.mem_grpOff_iff (· = p.v) h).1 hh
  have hij : ∀ i j, GlobalTheory.FinPlLoc.idem D (· = p.v) * mt S h i j =
      GlobalTheory.FinPlLoc.idem D (· = p.v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by
    intro i j
    have := congrFun (congrFun hM i) j
    simp only [GlobalTheory.FinPlLoc.mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination (-1 : AE D) * this
  have hpr : ∀ x, p.pr x = p.pr (p.e * x) := fun x => by rw [← p.sec_pr, p.pr_sec]
  have he : GlobalTheory.FinPlLoc.idem D (· = p.v) * p.e = p.e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.LatIndHalf.e_mem_idAt p)
  rw [← Matrix.map_one p.pr (map_zero _) (map_one _)]
  ext i j
  simp only [Matrix.map_apply]
  rw [hpr, hpr ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j), ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _) p.e,
    mul_assoc, hij i j, ← mul_assoc]

theorem moves_iff_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  intro D k _ _ _ _ p A n _ _ β L Λ hL hΛ κ
  obtain ⟨h1, -, -, h4, -, -⟩ := GlobalTheory.T.splitPlaceHermitianFrame_properties D k p A n β
  obtain ⟨Λ', -, hΛ', hK⟩ := h4 L hL
  have hΛeq : Λ' = Λ := by
    ext x
    rw [hΛ' x, hΛ x]
  subst hΛeq
  obtain ⟨hv, hvAt, h', h'Off, rfl⟩ := (GlobalTheory.FinPlLoc.part_grp (· = p.v) A).1 κ
  obtain ⟨g, rfl⟩ := (h1 hv).1 hvAt
  have hoff : coordHom A p.pr β.b β.b' β.bb' β.b'b h' = 1 := by
    refine Units.ext ?_
    rw [coordHom_val, map_pr_of_grpOff p A h'Off, Matrix.mul_one, β.b'b]
    rfl
  have hg : coordHom A p.pr β.b β.b' β.bb' β.b'b (β.gl g) = g :=
    ((eq_coordHom_iff A p.pr β.b β.b' β.bb' β.b'b (β.gl g) g).1 (β.gl_mat g)).symm
  rw [map_mul, hoff, mul_one, hg, ← hK g]
  constructor
  · intro hm
    refine ⟨hvAt, fun y hy => ?_⟩
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]
  · rintro ⟨-, hm⟩ y hy
    rw [hm y hy, GlobalTheory.FinPlLoc.mt_mul, ← Matrix.mulVec_mulVec, mulVec_of_grpOff A h'Off hy]

end GlobalTheory.FrameMoves

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  first | exact @GlobalTheory.FrameMoves.moves_iff_smul | exact GlobalTheory.FrameMoves.moves_iff_smul | (intros; apply GlobalTheory.FrameMoves.moves_iff_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FlatComm

variable {D : D7}

theorem besselAnisotropicEmbedding_fixes_basePoint {σ : ℕ} (B : BesLev D σ) (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ x0 B = x0 B := by
  have h1 : mt B.V (embA B.d B.o h) ⬝ B.d.jX = B.d.jX := B.d.wittDecomp_anisotropicEmbedding_inclX _
  have h2 : mt B.V (embA B.d B.o h) *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) := by
    have e1 : mt B.V (embA B.d B.o h) ⬝ B.d.j0 = B.d.j0 ⬝ mt B.V₀ (B.o.emb (h, 1)) := B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
    have e2 := B.o.emb_jB h 1
    rw [mt_one, Matrix.mul_one] at e2
    rw [vecB, ratV_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1, Matrix.mul_assoc]
    exact congrArg (fun M => (B.d.j0 ⬝ M) *ᵥ ratV B.ζ) e2
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun h2 k
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · have := congrFun (congrFun h1 k) i
    simp only [x0, xLast, Matrix.mul_apply, Matrix.of_apply, Fin.snoc_castSucc]
    exact this

theorem continuous_psiUni {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have hv : Continuous (fun u : UX D ρ => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hs : Continuous fun u : UX D ρ => upSum u.1.1 := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    split_ifs
    · exact hv.matrix_elem i j
    · exact continuous_const
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp (ht.comp hs)

theorem sFinite_of_haar {G : Type} [MeasurableSpace G] [Group G] [TopologicalSpace G] (hl : LocallyCompactSpace G)
    (hs : SecondCountableTopology G) (μ : Measure G) (hμ : μ.IsHaarMeasure) : SFinite μ := by
  haveI : SigmaCompactSpace G := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  exact instSFiniteOfSigmaFinite


set_option maxHeartbeats 600000 in
theorem flatFB_om : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀) (h : GA D B.A), flatFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flatFB s Ψ) := by
  intro D hD ψ σ J B s Ψ hΨ g h
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D (σ + 1)
  haveI : BorelSpace (UX D (σ + 1)) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := sFinite_of_haar k1 k2 _ s.vU.unit.1
  have hstd := s.weil.std
  set p : GA D J.W × GA D B.V := (J.d.emb0 g, embA B.d B.o h) with hp
  let F : (WO J.W B.V → ℂ) → UX D (σ + 1) → WO J.W₀ B.V₀ → ℂ := fun Φ u w =>
    flatFun ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (rat x) 0 Φ w u
  have hF : ∀ Φ u, F Φ u = star (psiUni ψ u.1) •
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (x0 B ⬝ u.1.1) 0 := fun Φ u => by
    rw [← hx0]; rfl
  have hflat : ∀ Φ, flatFB s Φ = fun w => ∫ u, F Φ u w ∂s.vU.ν := fun Φ => by
    simp only [F, hx0]; rfl
  have key : ∀ u, s.om₀ (g, B.o.emb (h, 1)) (F Ψ u) = F (s.om p Ψ) u := fun u => by
    have e := GlobalTheory.Unf.FB.evalAt_zero_equivariant D hD ψ σ J B s Ψ hΨ g 1 (one_mem _) h (x0 B ⬝ u.1.1)
    rw [one_mul, ← map_inv, ← Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
    rw [hF, hF, map_smul, ← e]
  have hv : Continuous (fun u : UX D (σ + 1) => u.1.1) := Units.continuous_val.comp continuous_subtype_val
  have hc : ∀ q, Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => F (s.om q Ψ) r.1 r.2 := fun q => by
    have c := (GlobalTheory.MixCont.mixed_coords_continuous D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil Ψ hΨ).2
    have c2 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ =>
        (q, (rat x : Mx D B.V.rank (σ + 1)) ⬝ r.1.1.1, (0 : Mx D J.W₀.rank σ), r.2) :=
      continuous_const.prodMk ((continuous_const.matrix_mul (hv.comp continuous_fst)).prodMk
        (continuous_const.prodMk continuous_snd))
    have c3 := c.comp c2
    have c4 : Continuous fun r : UX D (σ + 1) × WO J.W₀ B.V₀ => star (psiUni ψ r.1.1) :=
      ((continuous_psiUni hstd.1.1 _).comp continuous_fst).star
    have c5 := c4.mul c3
    simp only [Function.comp_def] at c5
    exact c5
  have h1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl
  obtain ⟨M, hM, hb⟩ := GlobalTheory.Unf.flatFun_majorant D ψ J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT _ _ s.om s.weil s.vU x hx.1 Ψ hΨ
    {1, p} (Set.toFinite _).isCompact
  have hth : ∀ u, IsThetaFunO ψ J.W₀ B.V₀ (F Ψ u) := fun u => by
    obtain ⟨mS, mT⟩ := GlobalTheory.MixValues.mixed_values D ψ hstd
    rw [hF]
    exact GlobalTheory.OrientedHeis.theta_smul _ (mT _ _ _ _ B.d _ _ s.vT.covol _ (mS _ _ _ _ J.d _ _ s.vS.covol _ hΨ _) _)
  have main := GlobalTheory.CommInt.om_integral_comm D ψ J.W₀ B.V₀ _ _ s.om₀ s.weil₀ (UX D (σ + 1)) s.vU.ν (F Ψ) (g, B.o.emb (h, 1)) M hth
    (by have := hc 1; rwa [h1] at this) (by simp only [key]; exact hc p) hM
    (fun u w => ⟨by have := hb 1 (by simp) 0 w u; rwa [h1] at this, by rw [key]; exact hb p (by simp) 0 w u⟩)
    (GlobalTheory.Unf.Flat.flatLaw D ψ hstd J.W J.W₀ B.V B.V₀ _ _ J.d B.d s.vS s.vT s.vU x hx.1 0 Ψ hΨ).2
  rw [hflat, hflat]
  funext w
  rw [main w]
  simp only [key]

end GlobalTheory.Unf.FlatComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatIntertwinesWeilActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀) (h : GA D B.A), flatFB s (s.om (J.d.emb0 g, embA B.d B.o h) Ψ) = s.om₀ (g, B.o.emb (h, 1)) (flatFB s Ψ) := by
  first | exact @GlobalTheory.Unf.FlatComm.flatFB_om | exact GlobalTheory.Unf.FlatComm.flatFB_om | (intros; apply GlobalTheory.Unf.FlatComm.flatFB_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem charUnram_mul {χ χ' : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) (h' : CharUnramAt D χ' v) :
    CharUnramAt D (χ * χ') v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, mul_one]

theorem charUnram_inv {χ : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) : CharUnramAt D χ⁻¹ v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

end GlobalTheory.SeeSaw.WeilLines

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

end GlobalTheory.SeeSaw.WeilLines
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tuplePlace_under_not_mem_tP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, QAll W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a y m b₀ k _ _ _ _ ι v o l bas _ _ _ _ _ _ _ _ htP _ _ _ _ FY sc _ PP hQ hmem
  obtain ⟨t, ht⟩ := hQ
  apply (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u
  have h1 := (htP _).1 hmem
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast] at h1
  exact h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_value : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ PP, QAll W PP → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ v.tP := by
  first | exact @GlobalTheory.tuplePlace_under_not_mem_tP | exact GlobalTheory.tuplePlace_under_not_mem_tP | (intros; apply GlobalTheory.tuplePlace_under_not_mem_tP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumPartialProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.PartialIdemSum

theorem mul_sum_of_isIdemAt {D : D7} {x : AE D} {P : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x P) (S : Finset (Formalism.L2.DIV.Pl D.host.E)) (f : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P' ∈ S, Formalism.L2.NTheta.IsIdemAt (f P') P') :
    x * ∑ P' ∈ S, f P' = if P ∈ S then x else 0 := by
  rw [Finset.mul_sum]
  split_ifs with hP
  · rw [Finset.sum_eq_single P]
    · have h1 := (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P) P P hx (hf P hP)).1 rfl
      rw [← h1]; exact hx.1.1
    · intro P' hP' hne
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 (Ne.symm hne)
    · intro h; exact absurd hP h
  · refine Finset.sum_eq_zero fun P' hP' => ?_
    refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D x (f P') P P' hx (hf P' hP')).2 ?_
    rintro rfl; exact hP hP'

theorem sum_mul_sum_of_subset {D : D7} (S S' : Finset (Formalism.L2.DIV.Pl D.host.E)) (f g : Formalism.L2.DIV.Pl D.host.E → AE D)
    (hf : ∀ P ∈ S, Formalism.L2.NTheta.IsIdemAt (f P) P) (hg : ∀ P ∈ S', Formalism.L2.NTheta.IsIdemAt (g P) P) (hS : S ⊆ S') :
    (∑ P ∈ S, f P) * ∑ P ∈ S', g P = ∑ P ∈ S, f P := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mul_sum_of_isIdemAt (hf P hP) S' g hg, if_pos (hS hP)]

end GlobalTheory.PartialIdemSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeNotMemPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem levelPrime_not_mem_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → (∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal) → ∀ PP : Pl D.host.E, PP ∈ (pk W).Pg ∨ QAll W PP → (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP hg PP hPP
  rcases hPP with h | ⟨t, ht⟩
  · intro hm
    apply hg PP h
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    rw [Ideal.mem_comap, map_natCast]
    exact hm
  · exact (hP.bot.hyp.2.2.2.1.lev.Q_off t PP ht).2 u

end GlobalTheory
end
