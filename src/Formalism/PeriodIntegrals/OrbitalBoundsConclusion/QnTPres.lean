module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.SecondCapelliMinorContinuousLinear
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.ExpSecondHermitianMemLevel
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinorSmoothness.HasDerivAtExt
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresLie

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv (Hpk_sq k r)

lemma hpk_unit : IsUnit (Hpk k r) := ⟨⟨Hpk k r, Hpk k r, Hpk_sq k r, Hpk_sq k r⟩, rfl⟩

lemma hpk_hh (A : Mx k r) : Hpk k r * (Hpk k r * A) = A := by rw [← mul_assoc, Hpk_sq, one_mul]

lemma hpart1_skew (Z : Mx k r) :
    (hpart1 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart1 (Hpk k r) Z * Hpk k r) := by
  unfold hpart1
  rw [hpk_inv]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [← smul_neg, neg_sub]

lemma hpart2_skew (Z : Mx k r) :
    (hpart2 (Hpk k r) Z)ᴴ = -(Hpk k r * hpart2 (Hpk k r) Z * Hpk k r) := by
  unfold hpart2
  rw [hpk_inv]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, hs,
    mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc, hpk_hh, Hpk_sq, mul_one]
  rw [neg_smul, add_comm Zᴴ]

lemma skew_real (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r)) (t : ℝ) :
    ((t : ℂ) • X)ᴴ = -(Hpk k r * ((t : ℂ) • X) * Hpk k r) := by
  rw [conjTranspose_smul, hX]
  simp [Complex.star_def, Complex.conj_ofReal, mul_smul_comm, smul_mul_assoc]

lemma exp_mem_UH (Y : Mx k r) (hY : Yᴴ = -(Hpk k r * Y * Hpk k r)) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by
  show (NormedSpace.exp Y)ᴴ * Hpk k r * NormedSpace.exp Y = Hpk k r
  have e1 : Yᴴ = Hpk k r * (-Y) * (Hpk k r)⁻¹ := by
    rw [hY, hpk_inv, mul_neg, neg_mul]
  rw [← Matrix.exp_conjTranspose, e1, Matrix.exp_conj _ _ hpk_unit, hpk_inv]
  simp only [mul_assoc, hpk_hh]
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

lemma exp_fix (Y : Mx k r) (c : Fin (2 * r + k + 1)) (hY : ∀ x, Y x c = 0) :
    NormedSpace.exp Y *ᵥ bvec c = bvec c := _root_.Formalism.FourierDecayAlt.Q.EabLie.exp_fix Y c hY

lemma glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

lemma exp_mem_glev (i : Fin (r + 1)) (X : Mx k r) (hX : Xᴴ = -(Hpk k r * X * Hpk k r))
    (hc : ∀ a : Fin r, a.val < i.val → ∀ x, X x (eI k r a) = 0 ∧ X x (esI k r a) = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by
  simp only [Glev, Set.mem_setOf_eq]
  refine ⟨exp_mem_UH _ (skew_real X hX t), fun a ha => ⟨exp_fix _ _ fun x => ?_, exp_fix _ _ fun x => ?_⟩⟩
  · rw [Matrix.smul_apply, (hc a ha x).1, smul_zero]
  · rw [Matrix.smul_apply, (hc a ha x).2, smul_zero]

lemma hpk_zero (i : Fin (r + 1)) (p : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    Hpk k r (posL k r i p) (eI k r a) = 0 ∧ Hpk k r (posL k r i p) (esI k r a) = 0 := by
  have hp := p.isLt
  have ha' := a.isLt
  have hi := i.isLt
  unfold mdim at hp
  simp only [Hpk, posL, eI, esI, Fin.mk.injEq]
  constructor <;> split_ifs <;> first | rfl | (exfalso; omega)

lemma unit_col (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (c : Fin (2 * r + k + 1))
    (hcq : c ≠ posL k r i q) (hHc : Hpk k r (posL k r i p) c = 0) (x : Fin (2 * r + k + 1)) :
    (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ)) x c = 0 ∧
    (Hpk k r * (Matrix.single (posL k r i p) (posL k r i q) (1 : ℂ))ᴴ * Hpk k r) x c = 0 := _root_.Formalism.FourierDecayAlt.Q.TInvW.unit_col i p q c hcq hHc x

lemma posL_ne (i : Fin (r + 1)) (q : Fin (mdim k r i)) (a : Fin r) (ha : a.val < i.val) :
    eI k r a ≠ posL k r i q ∧ esI k r a ≠ posL k r i q := by
  have hq := q.isLt
  have ha' := a.isLt
  unfold mdim at hq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · have h2 := congrArg Fin.val h
    simp only [eI, esI, posL] at h2
    omega

lemma hpart_cols (i : Fin (r + 1)) (p q : Fin (mdim k r i)) :
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) ∧
    (∀ a : Fin r, a.val < i.val → ∀ x,
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (eI k r a) = 0 ∧
      hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1) x (esI k r a) = 0) := _root_.Formalism.FourierDecayAlt.Q.EabLie.hpart_cols i p q

theorem exp_hpart1_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart1_skew _) (hpart_cols i p q).1 t

theorem exp_hpart2_mem (i : Fin (r + 1)) (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := exp_mem_glev i _ (hpart2_skew _) (hpart_cols i p q).2 t

theorem hasDerivAt_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := _root_.Formalism.FourierDecayAlt.Q.EabLie.hasDerivAt_ext (E := E) i X hX f F U g hU hg hgG hF hfF

theorem rdV_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (i : Fin (r + 1)) (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (f F : Mx k r → E) (U : Set (Mx k r)) (g : Mx k r) (hU : IsOpen U) (hg : g ∈ U)
    (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) :
    RdV X f g = fderiv ℝ F g (g * X) := (hasDerivAt_ext i X hX f F U g hU hg hgG hF hfF).deriv

end Formalism.FourierDecayAlt.Q.TPresLie
end
end

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresMain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma sl_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (f + f') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  simp only [Pi.add_apply, hfF g hg.1 hgG, hfF' g hg.2 hgG]

lemma sl_zero : SmoothLev k r i D (0 : Mx k r → E) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

def SmoothG (k r : ℕ) (i : Fin (r + 1)) (c : Mx k r → ℂ) : Prop :=
  ∃ c' : Mx k r → ℂ, ContDiff ℝ ∞ c' ∧ ∀ x ∈ Glev k r i, c x = c' x

lemma sg_const (v : ℂ) : SmoothG k r i (fun _ => v) := by
  exact ⟨fun _ => v, contDiff_const, fun _ _ => rfl⟩

lemma sg_mul {c d : Mx k r → ℂ} (hc : SmoothG k r i c) (hd : SmoothG k r i d) :
    SmoothG k r i (fun x => c x * d x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  obtain ⟨d', hd', hdd⟩ := hd
  exact ⟨fun x => c' x * d' x, hc'.mul hd', fun x hx => by simp only [hcc x hx, hdd x hx]⟩

lemma sg_sub {c d : Mx k r → ℂ} (hc : SmoothG k r i c) (hd : SmoothG k r i d) :
    SmoothG k r i (fun x => c x - d x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  obtain ⟨d', hd', hdd⟩ := hd
  exact ⟨fun x => c' x - d' x, hc'.sub hd', fun x hx => by simp only [hcc x hx, hdd x hx]⟩

lemma sl_smul_fun {c : Mx k r → ℂ} (hc : SmoothG k r i c) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) : SmoothLev k r i D (fun x => c x • f x) := by
  obtain ⟨c', hc', hcc⟩ := hc
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => c' x • F x, hU, hgU, hc'.contDiffOn.smul hF, fun g hg hgG => ?_⟩
  simp only [hcc g hgG, hfF g hg hgG]

lemma sl_csmul (c : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) : SmoothLev k r i D (c • f) := by
  exact sl_smul_fun (sg_const c) hf

lemma sl_sum {ι : Type*} (s : Finset ι) (f : ι → Mx k r → E) (hf : ∀ j ∈ s, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (∑ j ∈ s, f j) := by
  exact Finset.sum_induction _ (fun g => SmoothLev k r i D g) (fun _ _ ha hb => sl_add ha hb) sl_zero hf

lemma sl_sum' {ι : Type*} [Fintype ι] (f : ι → Mx k r → E) (hf : ∀ j, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (fun x => ∑ j, f j x) := by
  have e : (fun x => ∑ j, f j x) = ∑ j, f j := by
    funext x
    exact (Finset.sum_apply x Finset.univ f).symm
  rw [e]
  exact sl_sum _ _ fun j _ => hf j

lemma sl_neg {f : Mx k r → E} (hf : SmoothLev k r i D f) : SmoothLev k r i D (-f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, fun x => -F x, hU, hgU, hF.neg, fun g hg hgG => by simp only [Pi.neg_apply, hfF g hg hgG]⟩

end Smooth

lemma exp_first_hermitian_mem_level (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by
  exact Formalism.FourierDecayAlt.Q.TPresLie.exp_hpart1_mem i p q t

lemma exp_second_hermitian_mem_level (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by
  exact Formalism.FourierDecayAlt.Q.TPresLie.exp_hpart2_mem i p q t

section Rd

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

private lemma Glev_mul_mem {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  refine ⟨?_, fun a ha => ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [hg.1, hh.1]
  · obtain ⟨e1, e2⟩ := hg.2 a ha
    obtain ⟨f1, f2⟩ := hh.2 a ha
    exact ⟨by rw [← Matrix.mulVec_mulVec, f1, e1], by rw [← Matrix.mulVec_mulVec, f2, e2]⟩

private lemma continuousAt_mul_exp_smul_of_mem_Glev (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    {g : Mx k r} (hg : g ∈ Glev k r i) :
    ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
  (Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX (fun x => x) (fun x => x) Set.univ g isOpen_univ
    (Set.mem_univ _) hg contDiffOn_id (fun _ _ _ => rfl)).continuousAt

lemma rdV_local (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (hD : IsOpen D) (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X f g = RdV X f' g := by
  simp only [RdV]
  apply Filter.EventuallyEq.deriv_eq
  have hc := continuousAt_mul_exp_smul_of_mem_Glev X hX hg.1
  have hD' : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' D ∈ 𝓝 (0 : ℝ) := by
    apply hc.preimage_mem_nhds
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one]
    exact hD.mem_nhds hg.2
  filter_upwards [hD'] with t ht
  exact h _ ⟨Glev_mul_mem hg.1 (hX t), ht⟩

lemma rdV_clm (X : Mx k r) (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) : RdV X (fun y => L (f y)) g = L (RdV X f g) := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hd := Formalism.FourierDecayAlt.Q.TPresLie.hasDerivAt_ext i X hX f F U g hU hgU hg.1 hF hfF
  have hd2 : HasDerivAt (fun t : ℝ => L (f (g * NormedSpace.exp ((t : ℂ) • X))))
      (L (fderiv ℝ F g (g * X))) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  simp only [RdV]
  rw [hd2.deriv, hd.deriv]

lemma eh_local (hD : IsOpen D) (p q : Fin (mdim k r i)) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) f g = EH k r (posL k r i p) (posL k r i q) f' g := by
  simp only [EH, EabH]
  rw [rdV_local _ (exp_first_hermitian_mem_level p q) hD f f' h g hg, rdV_local _ (exp_second_hermitian_mem_level p q) hD f f' h g hg]

lemma eh_clm (p q : Fin (mdim k r i)) (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f)
    (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    EH k r (posL k r i p) (posL k r i q) (fun y => L (f y)) g =
      L (EH k r (posL k r i p) (posL k r i q) f g) := by
  simp only [EH, EabH]
  rw [rdV_clm _ (exp_first_hermitian_mem_level p q) L f hf g hg, rdV_clm _ (exp_second_hermitian_mem_level p q) L f hf g hg, map_add (f := _), map_smul]

lemma mulX_cd (X : Mx k r) : ContDiff ℝ ∞ (fun g : Mx k r => g * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun j _ => ((contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin (2 * r + k + 1) → ℂ)) a)).mul
    contDiff_const

lemma eh_smooth (p q : Fin (mdim k r i)) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (EH k r (posL k r i p) (posL k r i q) f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hdF := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hF).2
  refine ⟨U, fun g => fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)) +
    Complex.I • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1)),
    hU, hgU, ?_, fun g hg hgG => ?_⟩
  · exact (hdF.clm_apply (mulX_cd _).contDiffOn).add
      ((hdF.clm_apply (mulX_cd _).contDiffOn).const_smul Complex.I)
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [rdV_ext i _ (exp_first_hermitian_mem_level p q) f F U g hU hg hgG hF hfF,
      rdV_ext i _ (exp_second_hermitian_mem_level p q) f F U g hU hg hgG hF hfF]

end Rd

section Fold

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma top_smooth (hD : IsOpen D) (c : ℂ) (p q : Fin (mdim k r i)) (f : Mx k r → E)
    (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (Top (EH k r) c (posL k r i p) (posL k r i q) f) := by
  refine sl_add (f := fun g => if posL k r i p = posL k r i q then c • f g else 0) ?_ (eh_smooth p q f hf)
  by_cases hpq : posL k r i p = posL k r i q
  · simp only [hpq, ↓reduceIte]
    exact sl_csmul c hf
  · simp only [hpq, ↓reduceIte]
    exact sl_zero

lemma top_local (hD : IsOpen D) (c : ℂ) (p q : Fin (mdim k r i)) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    Top (EH k r) c (posL k r i p) (posL k r i q) f g = Top (EH k r) c (posL k r i p) (posL k r i q) f' g := by
  simp only [Formalism.QuantumDeterminants.Top]
  rw [eh_local hD p q f f' h g hg, h g hg]

lemma top_clm (c : ℂ) (p q : Fin (mdim k r i)) (L : E →L[ℂ] E') (f : Mx k r → E)
    (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    Top (EH k r) c (posL k r i p) (posL k r i q) (fun y => L (f y)) g =
      L (Top (EH k r) c (posL k r i p) (posL k r i q) f g) := by
  simp only [Formalism.QuantumDeterminants.Top]
  rw [eh_clm p q L f hf g hg]
  split_ifs <;> simp only [map_add (f := _), map_smul, map_zero]

def foldP (k r : ℕ) (i : Fin (r + 1)) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) (f : Mx k r → E) : Mx k r → E :=
  (l.map fun x => Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2)).foldr (fun T h => T h) f

lemma iteratedOperator_nil (f : Mx k r → E) : foldP k r i [] f = f := rfl

lemma iteratedOperator_cons (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) :
    foldP k r i (x :: l) f = Top (EH k r) x.1 (posL k r i x.2.1) (posL k r i x.2.2) (foldP k r i l f) := rfl

lemma iteratedOperator_smooth (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (foldP k r i l f) := by
  induction l with
  | nil => rw [iteratedOperator_nil]; exact hf
  | cons x l ih => rw [iteratedOperator_cons]; exact top_smooth hD _ _ _ _ ih

lemma iteratedOperator_congr (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l f g = foldP k r i l f' g := by
  induction l with
  | nil => intro g hg; rw [iteratedOperator_nil, iteratedOperator_nil]; exact h g hg
  | cons x l ih =>
    intro g hg
    rw [iteratedOperator_cons, iteratedOperator_cons]
    exact top_local hD x.1 x.2.1 x.2.2 _ _ ih g hg

lemma iteratedOperator_clm_comp (hD : IsOpen D) (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i)))
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    ∀ g ∈ Glev k r i ∩ D, foldP k r i l (fun y => L (f y)) g = L (foldP k r i l f g) := by
  induction l with
  | nil => intro g hg; rw [iteratedOperator_nil, iteratedOperator_nil]
  | cons x l ih =>
    intro g hg
    rw [iteratedOperator_cons, iteratedOperator_cons, top_local hD x.1 x.2.1 x.2.2 _ (fun y => L (foldP k r i l f y)) ih g hg]
    exact top_clm x.1 x.2.1 x.2.2 L _ (iteratedOperator_smooth hD l f hf) g hg

lemma qminor_eq {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ) (f : Mx k r → E) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f =
      ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
        foldP k r i (List.ofFn fun m : Fin t => (u - ((m : ℕ) : ℂ), α (σ m), β m)) f) := by
  simp only [qminorOp, foldP, List.map_ofFn, Function.comp_def] <;> rfl

lemma qminor_smooth (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f) := by
  rw [qminor_eq]
  exact sl_sum _ _ fun σ _ => sl_csmul _ (iteratedOperator_smooth hD _ _ hf)

lemma qminor_local (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g =
      qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f' g := by
  rw [qminor_eq, qminor_eq]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iteratedOperator_congr hD _ f f' h g hg]

lemma qminor_clm (hD : IsOpen D) {t : ℕ} (α β : Fin t → Fin (mdim k r i)) (u : ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u (fun y => L (f y)) g =
      L (qminorOp (EH k r) (fun j => posL k r i (α j)) (fun j => posL k r i (β j)) u f g) := by
  rw [qminor_eq, qminor_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [iteratedOperator_clm_comp hD _ L f hf g hg]

end Fold

end Formalism.FourierDecayAlt.Q.TPresMain
end
end

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TPresMain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

lemma entry_cd (a b : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g : Mx k r => g a b) := by
  exact (contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin (2 * r + k + 1) → ℂ)) a)

lemma inv_glev {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg
  apply Matrix.inv_eq_left_inv
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg.1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]

private lemma contDiff_mulVec_apply_of_contDiff {M : Mx k r → Mx k r} (hM : ∀ a b, ContDiff ℝ ∞ (fun g => M g a b))
    (v : (Fin (2 * r + k + 1) → ℂ)) (p : Fin (2 * r + k + 1)) : ContDiff ℝ ∞ (fun g => (M g *ᵥ v) p) := by
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiff.sum fun q _ => (hM p q).mul contDiff_const

private lemma contDiff_mul_left_apply (H : Mx k r) (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (H * g) a b) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (entry_cd c b)

private lemma contDiff_hpk_conjTranspose_hpk_apply (a b : Fin (2 * r + k + 1)) :
    ContDiff ℝ ∞ (fun g : Mx k r => (Hpk k r * gᴴ * Hpk k r) a b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hs : ∀ c d : Fin (2 * r + k + 1), ContDiff ℝ ∞ (fun g : Mx k r => star (g c d)) :=
    fun c d => Complex.conjCLE.contDiff.comp (entry_cd c d)
  exact ContDiff.sum fun c _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs c d)).mul contDiff_const

lemma ybv_sg (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothG k r i (fun g => ybv k r z i g j) := by
  refine ⟨fun g => ybv k r z i g j, ?_, fun _ _ => rfl⟩
  simp only [ybv, herm, dotProduct, Matrix.mulVec_mulVec]
  exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_mulVec_apply_of_contDiff (contDiff_mul_left_apply (Hpk k r)) _ x)

lemma yv_sg (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothG k r i (fun g => yv k r z i g j) := by
  refine ⟨fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j), ?_, fun g hg => ?_⟩
  · exact contDiff_mulVec_apply_of_contDiff contDiff_hpk_conjTranspose_hpk_apply _ _
  · simp only [yv, inv_glev hg]

section Ops

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma chatL_smooth (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (hβ : ∀ j, SmoothG k r i (fun g => β g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chatL (EH k r) (posL k r i) u a β f) := by
  unfold chatL
  exact sl_sum' _ fun i0 => sl_sum' _ fun j0 =>
    sl_smul_fun (sg_mul (sg_mul (sg_const _) (hβ i0)) (ha j0)) (qminor_smooth hD _ _ u f hf)

lemma chatL_local (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β f g = chatL (EH k r) (posL k r i) u a β f' g := by
  simp only [chatL]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun j0 _ => ?_
  congr 1
  exact qminor_local hD _ _ u f f' h g hg

lemma chatL_clm (hD : IsOpen D) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β (fun y => L (f y)) g = L (chatL (EH k r) (posL k r i) u a β f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [chatL, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun j0 _ => ?_
  congr 1
  exact qminor_clm hD _ _ u L f hf g hg

private lemma smoothLev_ite_zero (P : Prop) [Decidable P] {F : Mx k r → E} (hF : P → SmoothLev k r i D F) :
    SmoothLev k r i D (fun g => if P then F g else 0) := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
    exact hF hP
  · simp only [hP, ↓reduceIte]
    exact sl_zero

lemma second_capelli_minor_smooth (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothG k r i (fun g => a g j)) (ha' : ∀ j, SmoothG k r i (fun g => a' g j))
    (hβ : ∀ j, SmoothG k r i (fun g => β g j)) (hβ' : ∀ j, SmoothG k r i (fun g => β' g j))
    (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (chat2L (EH k r) (posL k r i) u a a' β β' f) := by
  unfold chat2L
  exact sl_sum' _ fun i0 => sl_sum' _ fun i1 => sl_sum' _ fun j0 => sl_sum' _ fun j1 =>
    smoothLev_ite_zero _ fun _ => sl_smul_fun
      (sg_mul (sg_mul (sg_const _) (sg_sub (sg_mul (hβ i0) (hβ' i1)) (sg_mul (hβ i1) (hβ' i0))))
        (sg_sub (sg_mul (ha j0) (ha' j1)) (sg_mul (ha j1) (ha' j0))))
      (qminor_smooth hD _ _ u f hf)

lemma second_capelli_minor_local (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) (f f' : Mx k r → E)
    (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' f g = chat2L (EH k r) (posL k r i) u a a' β β' f' g := by
  simp only [chat2L]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ =>
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  split_ifs
  · congr 1
    exact qminor_local hD _ _ u f f' h g hg
  · rfl

lemma second_capelli_minor_continuousLinear (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' (fun y => L (f y)) g =
      L (chat2L (EH k r) (posL k r i) u a a' β β' f g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [chat2L, map_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ =>
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  split_ifs
  · rw [map_smul]
    congr 1
    exact qminor_clm hD _ _ u L f hf g hg
  · exact (map_zero L).symm

lemma tl_smooth (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (f : Mx k r → E) (hf : SmoothLev k r i D f) : SmoothLev k r i D (tL k r z z' i Y p q f) := by
  fin_cases p <;> fin_cases q
  · exact qminor_smooth hD (fun j => j) (fun j => j) _ f hf
  · exact sl_neg (chatL_smooth hD _ (fun _ => xv k r z' i) (ybv k r z i) (fun _ => sg_const _)
      (fun j => ybv_sg z j) f hf)
  · exact sl_neg (chatL_smooth hD _ (yv k r z i) (fun _ => xbv k r z' i) (fun j => yv_sg z j)
      (fun _ => sg_const _) f hf)
  · exact sl_neg (second_capelli_minor_smooth hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i)
      (fun j => yv_sg z j) (fun _ => sg_const _) (fun j => ybv_sg z j) (fun _ => sg_const _) f hf)

lemma tl_local (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (f f' : Mx k r → E) (h : ∀ x ∈ Glev k r i ∩ D, f x = f' x) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q f g = tL k r z z' i Y p q f' g := by
  fin_cases p <;> fin_cases q
  · exact qminor_local hD (fun j => j) (fun j => j) _ f f' h g hg
  · exact congrArg Neg.neg (chatL_local hD _ (fun _ => xv k r z' i) (ybv k r z i) f f' h g hg)
  · exact congrArg Neg.neg (chatL_local hD _ (yv k r z i) (fun _ => xbv k r z' i) f f' h g hg)
  · exact congrArg Neg.neg (second_capelli_minor_local hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) f f' h g hg)

lemma tl_clm (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y p q (fun y => L (f y)) g = L (tL k r z z' i Y p q f g) := by
  fin_cases p <;> fin_cases q
  · exact qminor_clm hD (fun j => j) (fun j => j) _ L f hf g hg
  · exact (congrArg Neg.neg (chatL_clm hD _ (fun _ => xv k r z' i) (ybv k r z i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (chatL_clm hD _ (yv k r z i) (fun _ => xbv k r z' i) L f hf g hg)).trans
      (map_neg L _).symm
  · exact (congrArg Neg.neg (second_capelli_minor_continuousLinear hD _ (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) L f hf g hg)).trans (map_neg L _).symm

end Ops

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z := by
  simp [UWset, UH]

lemma one_mem_Nlev : (1 : Mx k r) ∈ Nlev k r i := by
  simp [Nlev, Formalism.QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]

private lemma mul_mem_Slev_of_mem_UWset_of_mem_Nlev {z : (Fin (2 * r + k + 1) → ℂ)} {h m : Mx k r} (hh : h ∈ UWset k r z)
    (hm : m ∈ Nlev k r i) : h * m ∈ Slev k r z i := by
  simp only [Slev, Set.mem_setOf_eq]
  exact ⟨h, hh, m, hm, rfl⟩

theorem qnTPres_of (hT : TInvariant) : TPreservesFF := by
  intro Wp Wq _ _ _ _ k r z z' π π' i D Y p q hz hz' hDom J hJ
  simp only [FFl, Set.mem_setOf_eq] at hJ ⊢
  obtain ⟨hs, hL, hR, hW⟩ := hJ
  have hD : IsOpen D := hDom.1
  refine ⟨tl_smooth hD z z' Y p q J hs, ?_, ?_, ?_⟩
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) hn)
      (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') one_mem_Nlev) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (n * x) = (psi k r z cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hL x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg n hn
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (1 * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z) one_mem_Nlev)
      (1 * n) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev (one_mem_UW z') hn) g hg
    simp only [one_mul, mul_one] at e
    have hloc : ∀ x ∈ Glev k r i ∩ D,
        J (x * n) = (psi k r z' cStd n • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (J x) := by
      intro x hx
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
      exact hR x hx n hn
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q _ J hs g hg,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  · intro g hg h hh h' hh'
    have e := hT (Wq →L[ℂ] Wp) k r z z' i D J Y p q hz hz' hDom hs (h * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh one_mem_Nlev)
      (h' * 1) (mul_mem_Slev_of_mem_UWset_of_mem_Nlev hh' one_mem_Nlev) g hg
    simp only [mul_one] at e
    obtain ⟨L, hLx⟩ : ∃ L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp), ∀ A, L A = (π h).comp (A.comp (π' h')) :=
      ⟨(ContinuousLinearMap.compL ℂ Wq Wp Wp (π h)).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (π' h')),
        fun A => by simp⟩
    have hloc : ∀ x ∈ Glev k r i ∩ D, J (h * x * h') = L (J x) := by
      intro x hx
      rw [hLx]
      exact hW x hx h hh h' hh'
    rw [← e, tl_local hD z z' Y p q _ _ hloc g hg, tl_clm hD z z' Y p q L J hs g hg, hLx]

end Formalism.FourierDecayAlt.Q.TPresMain
end
end

theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := Formalism.FourierDecayAlt.Q.TPresMain.qnTPres_of qnTInv
