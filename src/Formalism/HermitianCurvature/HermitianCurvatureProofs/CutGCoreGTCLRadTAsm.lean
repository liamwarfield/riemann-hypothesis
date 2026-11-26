module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmB
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmA
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

def Ann {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}

theorem ann_open {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Ann z z') :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exists_pr {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) :
    ∃ Pr : V →ₗ[ℂ] V, (∀ x, Pr x ∈ S) ∧ ∀ x ∈ S, Pr x = x := by
  obtain ⟨q, hq⟩ := S.exists_isCompl
  refine ⟨S.subtype ∘ₗ S.linearProjOfIsCompl q hq, fun x => (S.linearProjOfIsCompl q hq x).2, fun x hx => ?_⟩
  exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨x, hx⟩)

def e2 : Fin 2 → ℂ := ![1, Complex.I]

def crd : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]

theorem sum_crd (v : ℂ) : ∑ t : Fin 2, crd t v • e2 t = v := by
  simp only [Fin.sum_univ_two, crd, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul, mul_one]
  exact Complex.re_add_im v

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ml_expand {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) E) (v : ℂ) :
    m (fun _ => v) = ∑ s : Fin j → Fin 2, (∏ i, crd (s i) v) • m (fun i => e2 (s i)) := by
  have h : (fun _ : Fin j => v) = fun _ => ∑ t : Fin 2, crd t v • e2 t := funext fun _ => (sum_crd v).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, m.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact m.map_smul_univ (fun i => crd (s i) v) (fun i => e2 (s i))

end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def fibS (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (ζ : ℂ) : Submodule ℂ (Wq →L[ℂ] Wp) where
  carrier := NF.Fib k r z z' μs π π' ζ
  add_mem' := by
    intro X X' hX hX' p hp
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX p hp, hX' p hp]
  zero_mem' := by
    intro p _
    simp
  smul_mem' := by
    intro s X hX p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX p hp]

theorem radR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ : Q.Fn k r E) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ NF.QR k r z z') : NF.radR k r z z' μs Φ q = Φ q.1 (NF.muZ k r μs q.2) := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq]

theorem radR_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ + Ψ) = NF.radR k r z z' μs Φ + NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ - Ψ) = NF.radR k r z z' μs Φ - NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (s : ℂ) (Φ : Q.Fn k r E) :
    NF.radR k r z z' μs (s • Φ) = s • NF.radR k r z z' μs Φ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} :
    NF.radR k r z z' μs (0 : Q.Fn k r E) = 0 := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

end

end

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

def phiP (z z' : Fin (2 * r + k + 1) → ℂ) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) (p : ℂ → (Wq →L[ℂ] Wp)) :
    (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp) :=
  (NF.QR k r z z').indicator fun q => Pr (p q.2)

def Gd (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  NF.RadBase k r z z' μs π π' ∧ ∀ x, ∀ ζ ∈ Ann z z', Pr x ∈ NF.Fib k r z z' μs π π' ζ

theorem pr_contDiff (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : ContDiff ℝ ∞ (fun x => Pr x) :=
  (LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)).contDiff

theorem phiP_mem (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    phiP z z' Pr p ∈ NF.RadSec k r z z' μs π π' := by
  refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine ((pr_contDiff Pr).comp (hp.comp contDiff_snd)).contDiffOn.congr fun q hq => ?_
    simp only [phiP, Set.indicator_of_mem hq, Function.comp]
  · simp only [phiP, Set.indicator_of_mem hq]
    exact hG.2 _ _ hq.2
  · simp only [phiP, Set.indicator_of_notMem hq]

def PhiP (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (p : ℂ → (Wq →L[ℂ] Wp)) : Q.RadSp k r z z' π π' :=
  if h : Gd z z' μs π π' Pr ∧ ContDiff ℝ ∞ p then
    ⟨Classical.choose (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2)),
     (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2))).1⟩
  else 0

theorem radR_PhiP (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    NF.radR k r z z' μs ((PhiP z z' μs π π' Pr p : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) =
      phiP z z' Pr p := by
  unfold PhiP
  rw [dite_eq_left ⟨hG, hp⟩]
  exact (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' hG.1 (phiP z z' Pr p)
      (phiP_mem hG hp))).2

theorem eq_of_radR (hG : Gd z z' μs π π' Pr) {Φ Ψ : Q.RadSp k r z z' π π'}
    (h : NF.radR k r z z' μs (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp))) :
    Φ = Ψ :=
  Subtype.ext (Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq k r z z' μs π π' hG.1 Φ Φ.2 Ψ Ψ.2 h)

theorem PhiP_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') :
    PhiP z z' μs π π' Pr (fun ζ => p ζ + p' ζ) = PhiP z z' μs π π' Pr p + PhiP z z' μs π π' Pr p' := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.add hp'), Submodule.coe_add, radR_add, radR_PhiP hG hp, radR_PhiP hG hp']
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) :
    PhiP z z' μs π π' Pr (fun ζ => s • p ζ) = s • PhiP z z' μs π π' Pr p := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.const_smul s), Submodule.coe_smul, radR_smul, radR_PhiP hG hp]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_zero (hG : Gd z z' μs π π' Pr) : PhiP z z' μs π π' Pr (fun _ => 0) = 0 := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG contDiff_const, Submodule.coe_zero, radR_zero]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

def VV (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (p : ℂ → (Wq →L[ℂ] Wp)) (ζ : ℂ) : Wq →L[ℂ] Wp :=
  NF.radR k r z z' μs ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c0, ζ)

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem VV_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => p ζ + p' ζ) ζ = VV z z' μs π π' Pr T c0 p ζ + VV z z' μs π π' Pr T c0 p' ζ := by
  unfold VV
  rw [PhiP_add hG hp hp', map_add (f := _), Submodule.coe_add, radR_add]
  rfl

theorem VV_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  unfold VV
  rw [PhiP_smul hG hp, map_smul, Submodule.coe_smul, radR_smul]
  rfl

theorem VV_smulR (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℝ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  have h := VV_smul (T := T) (c0 := c0) hG hp (s : ℂ) ζ
  simp only [Complex.coe_smul] at h
  exact h

theorem VV_zero (hG : Gd z z' μs π π' Pr) (ζ : ℂ) : VV z z' μs π π' Pr T c0 (fun _ => 0) ζ = 0 := by
  unfold VV
  rw [PhiP_zero hG, map_zero, Submodule.coe_zero, radR_zero]
  rfl

theorem VV_sum (hG : Gd z z' μs π π' Pr) {ι : Type} (s : Finset ι) (p : ι → ℂ → (Wq →L[ℂ] Wp))
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => ∑ i ∈ s, p i ζ) ζ = ∑ i ∈ s, VV z z' μs π π' Pr T c0 (p i) ζ := by
  induction s using Finset.induction_on with
  | empty => simpa using VV_zero (T := T) (c0 := c0) hG ζ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [VV_add hG (hp i) (ContDiff.sum fun j _ => hp j), ih]

theorem VV_smooth (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hc0 : c0 ∈ OmX r) :
    ContDiffOn ℝ ∞ (VV z z' μs π π' Pr T c0 p) (Ann z z') := by
  have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq k r z z' μs π π' hG.1
    ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp))
    (T (PhiP z z' μs π π' Pr p)).2
  exact hm.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc0, hζ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

theorem fn_eq_of_radR (hB : NF.RadBase k r z z' μs π π') (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ}
    (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : ∀ ζ, NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ)) :
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c' := by
  obtain ⟨hk, hz, hz', hT, hT', hsec, -, -, -, -⟩ := hB
  obtain ⟨h0, -, he⟩ := Ψ.2
  funext g
  by_cases hg : g ∈ Q.Glev k r (Fin.last r) ∧ 0 < Q.GGl k r z z' g
  · obtain ⟨hgG, hG'⟩ := hg
    have hζq : Tz k r z * Tz k r z' < Complex.normSq (Q.zetaL k r z z' (Fin.last r) g) := by
      have h1 := hG'
      unfold Q.GGl at h1
      linarith
    obtain ⟨a, ha, b, hb, hgeq⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk hz hz' hT hT' hsec hgG hG'
    generalize Q.zetaL k r z z' (Fin.last r) g = ζ at hζq hgeq
    have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζq⟩
    have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζq⟩
    have e1 := he (c, NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq) a ha b hb
    have e2 := he (c', NF.muZ k r μs ζ) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq') a ha b hb
    have e3 := h ζ
    rw [radR_apply _ hq, radR_apply _ hq'] at e3
    dsimp only at e1 e2 e3
    rw [hgeq, e1, e2, e3]
  · have n1 : (c, g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    have n2 : (c', g) ∉ Q.DomR k r z z' := fun hx => hg ⟨hx.2.1, hx.2.2⟩
    exact (h0 (c, g) n1).trans (h0 (c', g) n2).symm

theorem t_slice (hB : NF.RadBase k r z z' μs π π') (X : Q.ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2)
    (Ψ : Q.RadSp k r z z' π π') {c c' : Fin r → ℂ} (hc : c ∈ OmX r) (hc' : c' ∈ OmX r)
    (h : (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c = (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c') {ζ : ℂ} (hζ : ζ ∈ Ann z z') :
    NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c, ζ) =
      NF.radR k r z z' μs ((X.t Y a b Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c', ζ) := by
  obtain ⟨-, hz, hz', -, -, hsec, -, -, -, -⟩ := hB
  have hq : (c, ζ) ∈ NF.QR k r z z' := ⟨hc, hζ⟩
  have hq' : (c', ζ) ∈ NF.QR k r z z' := ⟨hc', hζ⟩
  rw [radR_apply _ hq, radR_apply _ hq', X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq),
    X.t_apply Y a b Ψ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec hq')]
  dsimp only
  rw [h]

def pw (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i, crd (s i) (ζ - ζ0)) • X)

theorem pw_smooth (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (pw j s ζ0 X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff.comp (contDiff_id.sub contDiff_const))).smul
    contDiff_const

def wt (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ℂ → (Wq →L[ℂ] Wp) :=
  fun ζ => (((j.factorial : ℝ)⁻¹ * ∏ i ∈ Finset.univ \ t, crd (s i) ζ) • X)

theorem wt_smooth (j : ℕ) (s : Fin j → Fin 2) (t : Finset (Fin j)) (X : Wq →L[ℂ] Wp) : ContDiff ℝ ∞ (wt j s t X) :=
  (contDiff_const.mul (contDiff_prod fun i _ => (crd (s i)).contDiff)).smul contDiff_const

theorem pw_expand (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    pw j s ζ0 X = fun ζ => ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • wt j s t X ζ := by
  funext ζ
  have hp : ∏ i, crd (s i) (ζ - ζ0) = ∏ i, (-crd (s i) ζ0 + crd (s i) ζ) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub]
    ring
  simp only [pw, wt, hp, Finset.prod_add, Finset.mul_sum, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 1
  ring


variable (z z' μs π π' Pr) in
def Bsl (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  if hG : Gd z z' μs π π' Pr then
    LinearMap.toContinuousLinearMap
      { toFun := fun X => VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0
        map_add' := fun X X' => by
          have e : pw j s ζ0 (X + X') = fun ζ => pw j s ζ0 X ζ + pw j s ζ0 X' ζ := by
            funext ζ
            simp only [pw, smul_add]
          rw [e, VV_add hG (pw_smooth j s ζ0 X) (pw_smooth j s ζ0 X')]
        map_smul' := fun c X => by
          have e : pw j s ζ0 (c • X) = fun ζ => c • pw j s ζ0 X ζ := by
            funext ζ
            simp only [pw]
            rw [smul_comm]
          rw [e, VV_smulR hG (pw_smooth j s ζ0 X)]
          rfl }
  else 0

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem Bsl_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (s : Fin j → Fin 2) (ζ0 : ℂ) (X : Wq →L[ℂ] Wp) :
    Bsl z z' μs π π' Pr T c0 j s ζ0 X = VV z z' μs π π' Pr T c0 (pw j s ζ0 X) ζ0 := by
  unfold Bsl
  rw [dite_eq_left hG]
  rfl

theorem Bsl_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) (s : Fin j → Fin 2) :
    ContDiffOn ℝ ∞ (fun ζ0 => Bsl z z' μs π π' Pr T c0 j s ζ0) (Ann z z') := by
  rw [contDiffOn_clm_apply]
  intro X
  have key : ∀ ζ0, Bsl z z' μs π π' Pr T c0 j s ζ0 X = ∑ t ∈ (Finset.univ : Finset (Fin j)).powerset,
      (∏ i ∈ t, -crd (s i) ζ0) • VV z z' μs π π' Pr T c0 (wt j s t X) ζ0 := by
    intro ζ0
    rw [Bsl_apply hG, pw_expand, VV_sum hG _ _ (fun t => (wt_smooth j s t X).const_smul _)]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact VV_smulR hG (wt_smooth j s t X) _ ζ0
  refine (ContDiffOn.sum fun t _ => ?_).congr fun ζ0 _ => key ζ0
  exact (contDiff_prod fun i _ => (crd (s i)).contDiff.neg).contDiffOn.smul (VV_smooth hG hc0)


variable (z z' μs π π' Pr T c0) in
def AA (j : ℕ) (ζ0 : ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i)))

theorem AA_apply (hG : Gd z z' μs π π' Pr) (j : ℕ) (ζ0 : ℂ)
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp)) :
    AA z z' μs π π' Pr T c0 j ζ0 m =
      VV z z' μs π π' Pr T c0 (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) ζ0 := by
  have e : (fun ζ => ((j.factorial : ℝ)⁻¹) • m (fun _ => ζ - ζ0)) =
      fun ζ => ∑ s : Fin j → Fin 2, pw j s ζ0 (m (fun i => e2 (s i))) ζ := by
    funext ζ
    rw [ml_expand m (ζ - ζ0), Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [pw, smul_smul]
  rw [e, VV_sum hG _ _ (fun s => pw_smooth j s ζ0 _)]
  unfold AA
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply, Bsl_apply hG]

theorem AA_smooth (hG : Gd z z' μs π π' Pr) (hc0 : c0 ∈ OmX r) (j : ℕ) :
    ContDiffOn ℝ ∞ (AA z z' μs π π' Pr T c0 j) (Ann z z') := by
  have e : AA z z' μs π π' Pr T c0 j = fun ζ0 => ∑ s : Fin j → Fin 2, (Bsl z z' μs π π' Pr T c0 j s ζ0).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℂ) (Wq →L[ℂ] Wp) (fun i => e2 (s i))) := rfl
  rw [e]
  exact ContDiffOn.sum fun s _ => (Bsl_smooth hG hc0 j s).clm_comp contDiffOn_const

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem radial_torus_of_jets_taylor : GTCLRadTOfCut := by
  intro hJT hJR hTay Wp Wq _ _ _ _ _ _ P Bs hpl hk hcs X Y a b
  obtain ⟨N, hN⟩ := hJT (Wq →L[ℂ] Wp) P.k P.r Bs.z Bs.z' Y a b
  have hB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  by_cases hne : ∃ ζs, ζs ∈ RadTA.Ann Bs.z Bs.z'
  swap
  · exact ⟨0, fun _ _ => 0, fun _ => contDiffOn_const, fun Φ q hq => absurd ⟨q.2, hq.2⟩ hne⟩
  obtain ⟨ζs, hζs⟩ := hne
  obtain ⟨Pr, hPr1, hPr2⟩ := RadTA.exists_pr (RadTA.fibS Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs)
  have hfib : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ =
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζs := by
    intro ζ hζ
    unfold NF.Fib
    rw [hcs.2 ζ ζs hζ hζs]
  have hG : RadTA.Gd Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr := ⟨hB, fun x ζ hζ => by rw [hfib ζ hζ]; exact hPr1 x⟩
  have hPrF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', ∀ x ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ, Pr x = x := by
    intro ζ hζ x hx
    rw [hfib ζ hζ] at hx
    exact hPr2 x hx
  have hc0 : (fun _ => (1 : ℂ)) ∈ OmX P.r := fun _ => one_ne_zero
  refine ⟨N, fun j => RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j,
    fun j => RadTA.AA_smooth hG hc0 j, ?_⟩
  rintro Φ ⟨c, ζ0⟩ hq
  have hc : c ∈ OmX P.r := hq.1
  have hζ0 : ζ0 ∈ RadTA.Ann Bs.z Bs.z' := hq.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Φ.2
  set ψ : ℂ → (Wq →L[ℂ] Wp) := fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)
    with hψdef
  have hψs : ContDiffOn ℝ ∞ ψ (RadTA.Ann Bs.z Bs.z') :=
    hmem.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc, hζ⟩
  have hψF : ∀ ζ ∈ RadTA.Ann Bs.z Bs.z', Pr (ψ ζ) = ψ ζ := fun ζ hζ => hPrF ζ hζ _ (hmem.2.1 (c, ζ) ⟨hc, hζ⟩)
  have hterm : ∀ j, ContDiff ℝ ∞
      (fun ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) := by
    intro j
    exact ((iteratedFDeriv ℝ j ψ ζ0).contDiff.comp
      (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)).const_smul _
  set tay : ℂ → (Wq →L[ℂ] Wp) := fun ζ => ∑ j ∈ Finset.range (N + 1),
      ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0) with htay
  have htays : ContDiff ℝ ∞ tay := ContDiff.sum fun j _ => hterm j
  have hR := RadTA.radR_PhiP (μs := Bs.μsec) (π := Bs.π) (π' := Bs.π') hG htays

  have hsum : ∑ j ∈ Finset.range (N + 1), RadTA.AA Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) j ζ0
        (iteratedFDeriv ℝ j ψ ζ0) = RadTA.VV Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr (X.t Y a b) (fun _ => 1) tay ζ0 :=
    (Finset.sum_congr rfl fun j _ => RadTA.AA_apply hG j ζ0 _).trans
      (RadTA.VV_sum hG (Finset.range (N + 1))
        (fun j ζ => ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ0 (fun _ => ζ - ζ0)) hterm ζ0).symm

  have hΦtc : ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c = ((RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (fun _ => 1) := by
    refine RadTA.fn_eq_of_radR hB _ hc hc0 fun ζ => ?_
    rw [hR]
    by_cases hζ : ζ ∈ RadTA.Ann Bs.z Bs.z'
    · simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩),
        Set.indicator_of_mem (show ((fun _ => (1 : ℂ)), ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc0, hζ⟩)]
    · simp only [RadTA.phiP, Set.indicator_of_notMem (show (c, ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2),
        Set.indicator_of_notMem (show ((fun _ => (1 : ℂ)), ζ) ∉ NF.QR P.k P.r Bs.z Bs.z' from fun h => hζ h.2)]
  have hT0 := RadTA.t_slice (μs := Bs.μsec) hB X Y a b (RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) hc hc0 hΦtc hζ0

  have hz : ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
        Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) ζ0 = 0 := by
    intro i hi
    let Prr : (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) := LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)
    have hev : (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (((Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ)) =ᶠ[nhds ζ0] (fun ζ => Prr (ψ ζ - tay ζ)) := by
      filter_upwards [(RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0] with ζ hζ
      rw [Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, hR]
      simp only [RadTA.phiP, Set.indicator_of_mem (show (c, ζ) ∈ NF.QR P.k P.r Bs.z Bs.z' from ⟨hc, hζ⟩)]
      show ψ ζ - Pr (tay ζ) = Pr (ψ ζ - tay ζ)
      rw [map_sub, hψF ζ hζ]
    rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
    have hcd : ContDiffAt ℝ ∞ (fun ζ => ψ ζ - tay ζ) ζ0 :=
      (hψs.sub htays.contDiffOn).contDiffAt ((RadTA.ann_open Bs.z Bs.z').mem_nhds hζ0)
    have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left Prr hcd (i := i)
      (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    have h2 : iteratedFDeriv ℝ i (fun ζ => ψ ζ - tay ζ) ζ0 = 0 :=
      hTay (Wq →L[ℂ] Wp) ψ (RadTA.Ann Bs.z Bs.z') ζ0 N (RadTA.ann_open Bs.z Bs.z') hζ0 hψs i hi
    rw [show (fun ζ => Prr (ψ ζ - tay ζ)) = Prr ∘ (fun ζ => ψ ζ - tay ζ) from rfl, h1, h2]
    ext v
    rw [ContinuousLinearMap.compContinuousMultilinearMap_coe]
    simp
  have hZ := hJR Wp Wq P Bs hpl hk (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) (c, ζ0) hq N hz
  have hdom := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR Bs.z_mem Bs.z'_mem hcs.1 hq
  have hv := hN _ _ hdom.2.1 hZ
  have ht := X.t_apply Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) _ hdom
  have hdiff : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((X.t Y a b (Φ - RadTA.PhiP Bs.z Bs.z' Bs.μsec Bs.π Bs.π' Pr tay) :
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ0) = 0 := by
    rw [RadTA.radR_apply _ hq]
    exact ht.trans hv
  rw [map_sub, Submodule.coe_sub, RadTA.radR_sub, Pi.sub_apply, sub_eq_zero] at hdiff
  rw [hdiff, hT0]
  exact hsum.symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
