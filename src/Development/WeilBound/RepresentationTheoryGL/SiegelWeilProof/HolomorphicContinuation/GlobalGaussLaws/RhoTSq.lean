module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetMMUnitary
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LevFUnitary
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RotDG
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSchwartzSmul
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CoordGamma
noncomputable section

open Complex

namespace PositivityTheory.Rg.Sw.Glob.VacE

theorem coord_gamma (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 /
        (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) - I * t * σ * ((si * co : ℝ) : ℂ)) -
      I * t * σ * ((si / co : ℝ) : ℂ) = c := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  field_simp
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

theorem coord_const (c t σ co si : ℝ) (hc : 0 < c) (ht : t ^ 2 = c ^ 2) (hσ : σ ^ 2 = 1) (hco : 0 < co)
    (hs : si ^ 2 + co ^ 2 = 1) :
    ((co⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2)) *
        ((Real.pi : ℂ) / (((-t : ℝ) : ℂ) ^ 2 * (σ : ℂ) ^ 2 / ((c : ℂ) * ((co⁻¹ : ℝ) : ℂ) ^ 2) -
          I * t * σ * ((si * co : ℝ) : ℂ))) * (((|t| / Real.pi : ℝ) : ℂ)) ^ 2 =
      co + I * (σ * t / c) * si := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hco' : (co : ℂ) ≠ 0 := by exact_mod_cast hco.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htC : (t : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast ht
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hs2 : (si : ℂ) ^ 2 + (co : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have habs : ((|t| : ℝ) : ℂ) ^ 2 = (c : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq_abs]; exact_mod_cast ht
  have hden : (c : ℂ) * co - I * t * σ * si ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    rcases this with h | h
    · exact hc.ne' h
    · exact hco.ne' h
  simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div]
  rw [neg_sq, htC, hσC, div_pow, habs]
  have e1 : (c : ℂ) ^ 2 * 1 / ((c : ℂ) * ((co : ℂ))⁻¹ ^ 2) - I * t * σ * (si * co) = co * ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [e1]
  have key : (co : ℂ)⁻¹ * ((Real.pi : ℂ) / ((c : ℂ) * (co : ℂ)⁻¹ ^ 2)) *
      ((Real.pi : ℂ) / (co * ((c : ℂ) * co - I * t * σ * si))) * ((c : ℂ) ^ 2 / (Real.pi : ℂ) ^ 2) =
      (c : ℂ) / ((c : ℂ) * co - I * t * σ * si) := by
    field_simp
  rw [key, div_eq_iff hden]
  have htσ : (t : ℂ) ^ 2 * (σ : ℂ) ^ 2 = (c : ℂ) ^ 2 := by rw [htC, hσC, mul_one]
  field_simp
  linear_combination (-(c : ℂ) ^ 2) * hs2 + (si : ℂ) ^ 2 * I ^ 2 * htσ + (si : ℂ) ^ 2 * (c : ℂ) ^ 2 * Complex.I_sq

end PositivityTheory.Rg.Sw.Glob.VacE
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacE

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD

def rhoT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) (a : Fin m) : ℝ := if epsT t ε a then 1 else -1

theorem isSiegel_I (n : ℕ) : IsSiegel (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold IsSiegel
  have h : -(Complex.I / 2) • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)
      - (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ) = 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ← sub_smul, smul_smul]
    have hc : -(Complex.I / 2) * (Complex.I - star Complex.I) = 1 := by
      rw [Complex.star_def, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]; ring
    rw [hc, one_smul]
  rw [h]
  exact Matrix.PosDef.one

theorem isSch_smul {m n : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSch f) (K : ℂ) : IsSch (fun u => K * f u) := by
  obtain ⟨S, hS⟩ := hf
  refine ⟨K • S, ?_⟩
  funext u
  rw [SchwartzMap.smul_apply, hS, smul_eq_mul]

theorem isSch_DG {m n : ℕ} (hGZ : GZSch) (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (ht : |t| = c) (K : ℂ) :
    IsSch (DG (m := m) (n := n) K (fun _ _ => (c : ℂ))) := by
  have htr : ∀ b : Bool, ∀ u : Fin m → Fin n → ℂ, (gramB (n := n) (epsT t ε) b u).trace
      = ∑ a : Fin m, if epsT t ε a = b then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0 := by
    intro b u
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag, gramB, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.Qb, map_sum, map_mul,
      MvPolynomial.eval_X]
    simp
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.conj_mul']
    · rfl
  have hfun : DG (m := m) (n := n) K (fun _ _ => (c : ℂ))
      = fun u => K * gZf (n := n) ε t c (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
    funext u
    simp only [DG, gZf]
    congr 1
    simp_rw [← Complex.exp_sum]
    congr 1
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_smul, htr, htr,
      Complex.star_def, Complex.conj_I]
    simp only [smul_eq_mul]
    have hsplit : ∀ a : Fin m, ((if epsT t ε a = true then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0)
        + if epsT t ε a = false then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0)
        = ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
      intro a; cases epsT t ε a <;> simp
    have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin m)) = _) fun a _ => hsplit a
    rw [Finset.sum_add_distrib] at hs
    set A := ∑ a : Fin m, if epsT t ε a = true then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0
    set B := ∑ a : Fin m, if epsT t ε a = false then ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) else 0
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc _ = -(c : ℂ) * ∑ a : Fin m, ∑ j : Fin n, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
          simp_rw [Finset.mul_sum]
      _ = _ := by
          rw [← hs]
          linear_combination (-(c : ℂ) * A - (c : ℂ) * B) * hI
  rw [hfun]
  exact isSch_smul (hGZ m n ε t c hc ht _ (isSiegel_I n)) K

theorem rhoT_eq {m : ℕ} (t c : ℝ) (ht : |t| = c) (hc : 0 < c) (ε : Fin m → Bool) (a : Fin m) :
    rhoT t ε a = VacC.sigR ε a * t / c := by
  unfold rhoT VacC.sigR epsT
  rcases lt_or_gt_of_ne (show t ≠ 0 by rintro rfl; simp at ht; linarith) with h | h
  · have htc : t = -c := by rw [abs_of_neg h] at ht; linarith
    have hn : ¬ (0 < t) := by linarith
    rw [if_neg hn, htc, mul_div_assoc, neg_div, div_self hc.ne']
    cases ε a <;> simp
  · have htc : t = c := by rw [abs_of_pos h] at ht; exact ht
    rw [if_pos h, htc, mul_div_assoc, div_self hc.ne', mul_one]

end PositivityTheory.Rg.Sw.Glob.VacE
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacF

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem cpos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (hl0 : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 hl0; positivity

theorem tabs {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem rot_DG (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, 0 < Real.cos (φ j)) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : 0 < cLoc l τ := cpos hl0
  have hta : |tLoc l τ| = cLoc l τ := tabs
  have ht2 : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← hta, sq_abs]
  have hσ : ∀ a, (VacC.sigR ε a) ^ 2 = 1 := by intro a; unfold VacC.sigR; split_ifs <;> norm_num
  have hX1 : (dR fun j => Real.tan (φ j))ᴴ = dR fun j => Real.tan (φ j) := dR_conjTranspose _
  have hX2 : (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))ᴴ = dR fun j => -(Real.sin (φ j) * Real.cos (φ j)) :=
    dR_conjTranspose _
  have hDd : IsUnit (dR fun j => (Real.cos (φ j))⁻¹).det := by
    rw [isUnit_iff_ne_zero, dR, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by
      have := (hφ j).ne'; exact_mod_cast inv_ne_zero this
  set g1 := mkG (nU (dR fun j => Real.tan (φ j))) (inG_nU _ hX1) with hg1
  set g2 := mkG (nbar (dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) (inG_nbar _ hX2) with hg2
  set g3 := mkG (mM (dR fun j => (Real.cos (φ j))⁻¹)) (inG_mM _ hDd) with hg3
  have hk : mkG (kth φ) (inK_kth φ).1 = g1 * g2 * g3 := by
    apply Subtype.ext; apply Units.ext
    exact kth_decomp φ (fun j => (hφ j).ne')
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) := isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc hta K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL (g1 * g2) g3 _ hf0,
    hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 g2 _ (hL.1 g3 _ hf0)]
  have h3 : L g3 (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (n := n) (K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank)
        (fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2)) := by
    rw [hlev g3 _ hDd rfl _ hf0]
    exact levF_diag e (fun j => (Real.cos (φ j))⁻¹) (fun j => inv_pos.2 (hφ j)) K _
  have hf3 := hL.1 g3 _ hf0
  rw [h3] at hf3 ⊢
  set K1 : ℂ := K * (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank with hK1
  set γ1 : Fin V.rank → Fin n → ℂ := fun _ j => ((cLoc l τ : ℝ) : ℂ) * ((((Real.cos (φ j))⁻¹ : ℝ) : ℂ) ^ 2) with hγ1
  have hre1 : ∀ a j, 0 < (γ1 a j).re := by
    intro a j
    rw [hγ1]; simp only
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have := inv_pos.2 (hφ j); positivity
  set γ2 : Fin V.rank → Fin n → ℂ := fun a j => ((-tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ1 a j -
    Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.sin (φ j) * Real.cos (φ j) : ℝ) : ℂ) with hγ2
  have hX2' : -(dR fun j => -(Real.sin (φ j) * Real.cos (φ j))) = dR fun j => Real.sin (φ j) * Real.cos (φ j) := by
    rw [dR_neg]; congr 1; funext j; ring
  have hin : (fun v => chN ε (tLoc l τ) (-(dR fun j => -(Real.sin (φ j) * Real.cos (φ j)))) v *
      ftLoc ε (-tLoc l τ) (DG K1 γ1) v) = DG (K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j)) γ2 := by
    funext v
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre1, hX2']
    exact chN_DG ε (tLoc l τ) (fun j => Real.sin (φ j) * Real.cos (φ j)) _ _ v
  have hre2 : ∀ a j, 0 < (γ2 a j).re := by
    intro a j
    have e : γ2 a j = ((((-tLoc l τ) ^ 2 * (VacC.sigR ε a) ^ 2 / (cLoc l τ * ((Real.cos (φ j))⁻¹) ^ 2)) : ℝ) : ℂ) -
        Complex.I * (((tLoc l τ * VacC.sigR ε a * (Real.sin (φ j) * Real.cos (φ j))) : ℝ) : ℂ) := by
      rw [hγ2, hγ1]; push_cast; ring
    rw [e, Complex.sub_re, Complex.ofReal_re, Complex.re_mul_ofReal, Complex.I_re, zero_mul, sub_zero, hσ a, mul_one, neg_sq]
    have htne : tLoc l τ ≠ 0 := by intro h0; rw [h0, abs_zero] at hta; linarith
    have := inv_pos.2 (hφ j)
    positivity
  set K2 : ℂ := K1 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ1 a j) with hK2
  set γ3 : Fin V.rank → Fin n → ℂ := fun a j => ((tLoc l τ : ℝ) : ℂ) ^ 2 * (((VacC.sigR ε a : ℝ) : ℂ) ^ 2) / γ2 a j with hγ3
  set C0 : ℂ := ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) with hC0
  have h2 : (fun u => C0 * ftLoc ε (tLoc l τ) (DG K2 γ2) u) = DG (C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j))) γ3 := by
    funext u
    rw [ftLoc_eq, ftG_DG _ _ _ _ hre2]
    unfold DG
    ring
  have hf2 := hL.1 g2 _ hf3
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2] at hf2
  rw [hNb D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g2 _ hX2 rfl _ hf3, hin, h2]
  rw [hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL g1 _ hX1 rfl _ hf2]
  funext u
  refine (chN_DG ε (tLoc l τ) (fun j => Real.tan (φ j)) _ _ u).trans ?_
  have hγ4 : (fun a j => γ3 a j - Complex.I * (tLoc l τ : ℂ) * ((VacC.sigR ε a : ℝ) : ℂ) * ((Real.tan (φ j) : ℝ) : ℂ)) =
      fun _ _ => ((cLoc l τ : ℝ) : ℂ) := by
    funext a j
    rw [hγ3, hγ2, hγ1]
    simp only
    rw [Real.tan_eq_sin_div_cos]
    exact coord_gamma (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
      (Real.sin_sq_add_cos_sq _)
  have hK : C0 * (K2 * ∏ a, ∏ j, ((Real.pi : ℂ) / γ2 a j)) =
      K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)) := by
    have p1 : (∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ)) ^ V.rank = ∏ _a : Fin V.rank, ∏ j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have p2 : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) =
        ∏ _a : Fin V.rank, ∏ _j : Fin n, (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) := by
      rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin,
        ← pow_mul, ← pow_mul]
      ring_nf
    have hc1 : ∀ a j, (((Real.cos (φ j))⁻¹ : ℝ) : ℂ) * ((Real.pi : ℂ) / γ1 a j) * ((Real.pi : ℂ) / γ2 a j) *
        (((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ 2) =
        (Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ) := by
      intro a j
      rw [hγ2, hγ1]
      simp only
      rw [coord_const (cLoc l τ) (tLoc l τ) (VacC.sigR ε a) (Real.cos (φ j)) (Real.sin (φ j)) hc ht2 (hσ a) (hφ j)
        (Real.sin_sq_add_cos_sq _), rhoT_eq (tLoc l τ) (cLoc l τ) hta hc ε a]
      push_cast
      ring
    rw [hC0, hK2, hK1, p1, p2, ← Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun j _ => hc1 a j))]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [hγ4, hK]

end PositivityTheory.Rg.Sw.Glob.VacF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRCosSubSin
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ExistsCircleDetNe
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem exists_circle_det_ne (W : Matrix (Fin n) (Fin n) ℂ) : ∃ lam : ℂ, ‖lam‖ = 1 ∧ (W + lam • 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set p := (-W).charpoly with hp
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hev : ∀ x : ℂ, p.eval x = (W + x • 1).det := by
    intro x
    rw [hp, Matrix.eval_charpoly]
    congr 1
    rw [Matrix.scalar_apply, sub_neg_eq_add, add_comm, Matrix.smul_one_eq_diagonal]
  let r : Fin (n + 1) → ℝ := fun k => (k : ℝ) / ((n : ℝ) + 1)
  let f : Fin (n + 1) → ℂ := fun k => cexp (I * (r k : ℂ))
  have hr0 : ∀ k, 0 ≤ r k := fun k => by simp only [r]; positivity
  have hr1 : ∀ k, r k < 1 := fun k => by
    simp only [r]; rw [div_lt_one (by positivity)]; exact_mod_cast k.2
  have hf : Function.Injective f := by
    intro k k' h
    obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    have hre : r k = r k' + z * (2 * Real.pi) := by
      have := congrArg Complex.im hz
      simpa [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im] using this
    have hz0 : z = 0 := by
      by_contra hz0
      have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz0
      have habs : |(z : ℝ) * (2 * Real.pi)| < 1 := by
        rw [abs_lt]; constructor <;> linarith [hr0 k, hr0 k', hr1 k, hr1 k']
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
      nlinarith [Real.pi_gt_three]
    rw [hz0] at hre
    simp only [Int.cast_zero, zero_mul, add_zero, r] at hre
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have : (k : ℝ) = k' := by
      field_simp at hre; linarith
    exact Fin.ext (by exact_mod_cast this)
  have hroot : ∀ k, f k ∈ p.roots.toFinset := by
    intro k
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot, hev]
    apply hcon
    simp only [f]
    rw [Complex.norm_exp]
    simp
  have hcard : (Finset.univ.image f).card ≤ p.roots.toFinset.card :=
    Finset.card_le_card (fun x hx => by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx; exact hroot k)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  have h1 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  have h2 : p.natDegree = n := by
    rw [hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  omega

theorem unitary_diag (W : Matrix (Fin n) (Fin n) ℂ) (hW : Wᴴ * W = 1) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ (∀ j, ‖w j‖ = 1) ∧
      W = P * diagonal w * Pᴴ := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  obtain ⟨lam, hlam1, hdet⟩ := exists_circle_det_ne W
  have hlam0 : lam ≠ 0 := by intro h; rw [h, norm_zero] at hlam1; exact zero_ne_one hlam1
  have hconj : starRingEnd ℂ lam * lam = 1 := by
    rw [Complex.conj_mul', hlam1]; simp
  set V' := lam⁻¹ • W with hV'
  have hV'u : V'ᴴ * V' = 1 := by
    rw [hV', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hW]
    rw [RCLike.star_def, map_inv₀]
    rw [show (starRingEnd ℂ lam)⁻¹ * lam⁻¹ = (starRingEnd ℂ lam * lam)⁻¹ by rw [mul_inv], hconj, inv_one, one_smul]
  set B := 1 + V' with hB
  set A := 1 - V' with hA
  have hBdet : IsUnit B.det := by
    rw [isUnit_iff_ne_zero]
    have : B = lam⁻¹ • (W + lam • 1) := by
      rw [hB, hV', smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul, add_comm]
    rw [this, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hlam0)) hdet
  set H := (Complex.I • A) * B⁻¹ with hH
  have hHB : H * B = Complex.I • A := by
    rw [hH, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBdet, Matrix.mul_one]
  have hBc : IsUnit Bᴴ.det := by rw [Matrix.det_conjTranspose]; exact hBdet.star
  have hid : Bᴴ * A = -(Aᴴ * B) := by
    rw [hB, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hV'u]
    abel
  have hHerm : H.IsHermitian := by
    have hk : Bᴴ * Hᴴ * B = Bᴴ * H * B := by
      have e1 : Bᴴ * Hᴴ = -(Complex.I • Aᴴ) := by
        rw [← Matrix.conjTranspose_mul, hHB, Matrix.conjTranspose_smul]
        simp [RCLike.star_def, Complex.conj_I]
      rw [e1, Matrix.mul_assoc, hHB, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, hid, smul_neg]
    have hk2 : Hᴴ = H := by
      have := congrArg (fun M => (Bᴴ)⁻¹ * M * B⁻¹) hk
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hBdet, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hBc, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBdet,
        Matrix.mul_one] at this
    exact hk2
  set U : Matrix (Fin n) (Fin n) ℂ := (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℝ := hHerm.eigenvalues with hd
  have hUu : Uᴴ * U = 1 := by
    rw [hU]; exact Matrix.mem_unitaryGroup_iff'.1 hHerm.eigenvectorUnitary.2
  have hUu' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUu
  have hspec : H = U * diagonal (fun j => ((d j : ℝ) : ℂ)) * Uᴴ := by
    have := hHerm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hdI : ∀ j, ((d j : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro j h; have := congrArg Complex.im h; simp at this
  set E : Fin n → ℂ := fun j => (Complex.I - (d j : ℂ)) / (Complex.I + (d j : ℂ)) with hE
  have hHdiag : H + Complex.I • 1 = U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ := by
    have e : diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) = diagonal (fun j => ((d j : ℝ) : ℂ)) + Complex.I • 1 := by
      rw [Matrix.smul_one_eq_diagonal, diagonal_add]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu', hspec]
  have hHI : IsUnit (H + Complex.I • 1).det := by
    rw [isUnit_iff_ne_zero, hHdiag, Matrix.det_mul, Matrix.det_mul, det_diagonal]
    have hU1 : U.det * Uᴴ.det = 1 := by rw [← Matrix.det_mul, hUu', Matrix.det_one]
    intro h0
    have : U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = 0 := by
      rw [show U.det * Uᴴ.det * ∏ j, (((d j : ℝ) : ℂ) + Complex.I) = U.det * (∏ j, (((d j : ℝ) : ℂ) + Complex.I)) * Uᴴ.det by ring]
      exact h0
    rw [hU1, one_mul] at this
    exact (Finset.prod_ne_zero_iff.2 fun j _ => hdI j) this
  have hEq1 : (H + Complex.I • 1) * V' = Complex.I • 1 - H := by
    have := hHB
    rw [hB, hA, Matrix.mul_add, Matrix.mul_one, smul_sub] at this
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at this
    rw [← this]
    abel
  have hEq2 : (H + Complex.I • 1) * (U * diagonal E * Uᴴ) = Complex.I • 1 - H := by
    rw [hHdiag]
    have e1 : U * diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * Uᴴ * (U * diagonal E * Uᴴ) =
        U * (diagonal (fun j => ((d j : ℝ) : ℂ) + Complex.I) * diagonal E) * Uᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]
    rw [e1, diagonal_mul_diagonal]
    have e2 : (fun j => (((d j : ℝ) : ℂ) + Complex.I) * E j) = fun j => Complex.I - ((d j : ℝ) : ℂ) := by
      funext j
      have hdI' : Complex.I + ((d j : ℝ) : ℂ) ≠ 0 := by rw [add_comm]; exact hdI j
      rw [hE]; simp only; rw [add_comm ((d j : ℝ) : ℂ) Complex.I]; field_simp
    rw [e2, hspec]
    have e3 : diagonal (fun j => Complex.I - ((d j : ℝ) : ℂ)) = Complex.I • 1 - diagonal (fun j => ((d j : ℝ) : ℂ)) := by
      rw [Matrix.smul_one_eq_diagonal, ← diagonal_sub]
    rw [e3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUu']
  have hV'eq : V' = U * diagonal E * Uᴴ := by
    have h0 : (H + Complex.I • 1) * (V' - U * diagonal E * Uᴴ) = 0 := by
      rw [Matrix.mul_sub, hEq1, hEq2, sub_self]
    have := congrArg (fun M => (H + Complex.I • 1)⁻¹ * M) h0
    simp only [Matrix.mul_zero] at this
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHI, Matrix.one_mul, sub_eq_zero] at this
    exact this
  refine ⟨U, fun j => lam * E j, hUu, hUu', ?_, ?_⟩
  · intro j
    rw [norm_mul, hlam1, one_mul, hE]
    simp only
    rw [norm_div]
    have h1 : ‖Complex.I - ((d j : ℝ) : ℂ)‖ = ‖Complex.I + ((d j : ℝ) : ℂ)‖ := by
      rw [← Complex.norm_conj (Complex.I + _)]; simp [Complex.conj_I, Complex.conj_ofReal, ← neg_add']
      rw [← norm_neg]; congr 1; ring
    rw [h1, div_self]
    intro h0; rw [norm_eq_zero] at h0; exact hdI j (by rw [add_comm]; exact h0)
  · have : W = lam • V' := by rw [hV', smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    have hd2 : diagonal (fun j => lam * E j) = lam • diagonal E := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [this, hV'eq, hd2, Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.Rg.Sw.Glob.VacU
end
end

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacG

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem inK_blocks (k : M2 n) (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  unfold InK InG at hk
  obtain ⟨hG, hU⟩ := hk
  have hU' : k * kᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [hU', Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  rw [← fromBlocks_toBlocks k] at hc
  unfold JJ at hc
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  simp at hc
  exact ⟨hc.1, hc.2.1⟩

theorem mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : mM u = fromBlocks u 0 0 u := by
  rw [mM, Matrix.inv_eq_right_inv hu]

theorem dR_cos_add_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (I * (θ j : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm I, Complex.exp_mul_I]
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem dR_cos_sub_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (-(I * (θ j : ℂ))) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, ← neg_mul, mul_comm I,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem uni_I (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A + I • B)ᴴ * (A + I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_add, conjTranspose_smul, hs, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem uni_mI (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A - I • B)ᴴ * (A - I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_sub, conjTranspose_smul, hs, sub_mul, mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem kak (k : M2 n) (hk : InK k) :
    ∃ (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ), uᴴ * u = 1 ∧ u'ᴴ * u' = 1 ∧
      (∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) ∧ k = mM u * kth θ * mM u' := by
  obtain ⟨h21, h22⟩ := inK_blocks k hk
  have hU : kᴴ * k = 1 := hk.2
  set A := k.toBlocks₁₁ with hA0
  set B := k.toBlocks₁₂ with hB0
  have hkA : k = fromBlocks A B (-B) A := by
    conv_lhs => rw [← fromBlocks_toBlocks k]
    rw [h21, h22]
  have hE : Aᴴ * A + Bᴴ * B = 1 ∧ Aᴴ * B + -(Bᴴ * A) = 0 := by
    rw [hkA, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hU
    obtain ⟨h1, h2, -, -⟩ := hU
    refine ⟨?_, ?_⟩
    · simpa [conjTranspose_neg] using h1
    · simpa [conjTranspose_neg] using h2
  set W := A + I • B with hW0
  set V := A - I • B with hV0
  have hW : Wᴴ * W = 1 := uni_I A B hE.1 hE.2
  have hV : Vᴴ * V = 1 := uni_mI A B hE.1 hE.2
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hX : (W * Vᴴ)ᴴ * (W * Vᴴ) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
      Matrix.one_mul, hV']
  obtain ⟨P, w, hP, hP', hw, hXd⟩ := VacU.unitary_diag (W * Vᴴ) hX
  set θ : Fin n → ℝ := fun j => Complex.arg (w j) / 2 with hθ
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (I * (θ j : ℂ)) with hD
  set Db : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (-(I * (θ j : ℂ))) with hDb
  have hDDb : D * Db = 1 := by
    rw [hD, hDb, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hDbH : Dbᴴ = D := by
    rw [hD, hDb, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul, neg_neg]
  have hDb2 : Db * Db = (diagonal w)ᴴ := by
    rw [hDb, diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    have hwj : w j = cexp (↑(Complex.arg (w j)) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (w j)]
      rw [hw j, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_add]
    conv_rhs => rw [hwj]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    simp only [hθ]
    push_cast
    ring
  set u' := Db * Pᴴ * W with hu0
  have hu' : u'ᴴ * u' = 1 := by
    rw [hu0, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDbH]
    calc Wᴴ * (P * D) * (Db * Pᴴ * W) = Wᴴ * (P * (D * Db) * Pᴴ) * W := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDDb, Matrix.mul_one, hP', Matrix.mul_one, hW]
  have hPD : P * D * u' = W := by
    calc P * D * u' = P * (D * Db) * Pᴴ * W := by simp only [hu0, Matrix.mul_assoc]
      _ = W := by rw [hDDb, Matrix.mul_one, hP', Matrix.one_mul]
  have hPDb : P * Db * u' = V := by
    calc P * Db * u' = (P * (Db * Db) * Pᴴ) * W := by simp only [hu0, Matrix.mul_assoc]
      _ = (W * Vᴴ)ᴴ * W := by
          rw [hDb2, hXd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.mul_assoc]
          simp only [Matrix.mul_assoc]
      _ = V := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hCS := dR_cos_add_sin θ
  have hCSm := dR_cos_sub_sin θ
  rw [← hD] at hCS
  rw [← hDb] at hCSm
  set C := dR fun j => Real.cos (θ j) with hC0
  set S := dR fun j => Real.sin (θ j) with hS0
  have e1 : P * C * u' + I • (P * S * u') = W := by
    rw [← hPD, ← hCS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : P * C * u' - I • (P * S * u') = V := by
    rw [← hPDb, ← hCSm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hXA : P * C * u' = A := by
    have h := congrArg₂ (· + ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 : ℂ) • (P * C * u') = (2 : ℂ) • A := by
      rw [two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ two_ne_zero h2
  have hYB : P * S * u' = B := by
    have h := congrArg₂ (· - ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 * I) • (P * S * u') = (2 * I) • B := by
      rw [mul_smul, mul_smul, two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ (mul_ne_zero two_ne_zero Complex.I_ne_zero) h2
  refine ⟨P, u', θ, hP, hu', fun j => ⟨?_, ?_⟩, ?_⟩
  · have := Complex.neg_pi_lt_arg (w j)
    simp only [hθ]
    linarith
  · have := Complex.arg_le_pi (w j)
    simp only [hθ]
    linarith
  · refine hkA.trans ?_
    rw [mM_unitary P hP, mM_unitary u' hu', kth_eq, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
    rw [← hC0, ← hS0]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_zero, add_zero, hXA, hYB]

end PositivityTheory.Rg.Sw.Glob.VacG
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG

theorem row_norm {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * uᴴ = 1) (x : Fin n → ℂ) :
    ∑ j, ((‖∑ k, x k * u k j‖ ^ 2 : ℝ) : ℂ) = ∑ k, ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  have hu2 : ∀ k l, ∑ j, u k j * star (u l j) = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hu k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc ∑ j, (∑ k, x k * u k j) * star (∑ k, x k * u k j)
      = ∑ j, ∑ k, ∑ l, x k * star (x l) * (u k j * star (u l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [star_mul']
        ring
    _ = ∑ k, ∑ l, x k * star (x l) * ∑ j, u k j * star (u l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, x k * star (x k) := by
        simp only [hu2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem levF_unitary {m n : ℕ} (e : ℤ) (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (K γ0 : ℂ) :
    levF e u (DG (m := m) (n := n) K (fun _ _ => γ0)) =
      DG (K * (u.det ^ e * (star u.det) ^ ((m : ℤ) - e))) (fun _ _ => γ0) := by
  funext v
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  have key : ∀ a : Fin m, ∏ j : Fin n, Complex.exp (-γ0 * ((‖(Matrix.of v * u) a j‖ ^ 2 : ℝ) : ℂ))
      = ∏ j : Fin n, Complex.exp (-γ0 * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simpa [Matrix.mul_apply] using row_norm u hu' (v a)
  simp only [levF, DG, key]
  ring

theorem dbl_angle (ρ x : ℝ) (hρ : ρ ^ 2 = 1) :
    ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) *
      ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) =
    (Real.cos x : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin x : ℂ) := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_two_mul (x / 2)
  have hp := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc hs
  rw [hc, hs]
  generalize Real.cos (x / 2) = c at *
  generalize Real.sin (x / 2) = s at *
  push_cast
  have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
  have hρ' : (ρ : ℂ) ^ 2 = 1 := by exact_mod_cast hρ
  linear_combination (-1 : ℂ) * hp' + (s : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * Complex.I_sq - (s : ℂ) ^ 2 * hρ'

end PositivityTheory.Rg.Sw.Glob.VacH
end
end

noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacG

variable {n : ℕ}

theorem blocks_kak (u u' : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hu' : u'ᴴ * u' = 1) (θ : Fin n → ℝ) :
    mM u * kth θ * mM u' = fromBlocks (u * (dR fun j => Real.cos (θ j)) * u') (u * (dR fun j => Real.sin (θ j)) * u')
      (-(u * (dR fun j => Real.sin (θ j)) * u')) (u * (dR fun j => Real.cos (θ j)) * u') := by
  have h1 : uᴴ⁻¹ = u := Matrix.inv_eq_right_inv hu
  have h2 : u'ᴴ⁻¹ = u' := Matrix.inv_eq_right_inv hu'
  simp only [mM, kth, dR, h1, h2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, neg_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem det_mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : (mM u).det = u.det * u.det := by
  rw [mM_unitary u hu, det_fromBlocks_zero₂₁]

private theorem det_kth_eq_one (θ : Fin n → ℝ) : (kth θ).det = 1 := by
  have hL : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have hR : (fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
      (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [det_fromBlocks_zero₂₁]
    simp
  have key : fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (I • (1 : Matrix (Fin n) (Fin n) ℂ))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) * kth θ *
        fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) (-(I • (1 : Matrix (Fin n) (Fin n) ℂ)))
        (0 : Matrix (Fin n) (Fin n) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ)
      = fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) (0 : Matrix (Fin n) (Fin n) ℂ)
          (-diagonal fun j => (Real.sin (θ j) : ℂ))
          (diagonal fun j => (Real.cos (θ j) : ℂ) + I * Real.sin (θ j)) := by
    simp only [kth, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, Matrix.neg_mul]
    congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [h, diagonal_apply] <;>
      first
      | ring1
      | linear_combination Complex.sin ((θ j : ℝ) : ℂ) * I_sq
  have hprod : ∏ j, (((Real.cos (θ j) : ℂ) - I * Real.sin (θ j)) * ((Real.cos (θ j) : ℂ) + I * Real.sin (θ j))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hp := Real.sin_sq_add_cos_sq (θ j)
    generalize Real.cos (θ j) = c at *
    generalize Real.sin (θ j) = s at *
    have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
    linear_combination hp' - (s : ℂ) ^ 2 * I_sq
  have h := congrArg Matrix.det key
  rw [det_mul, det_mul, hL, hR, det_fromBlocks_zero₁₂, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib,
    hprod, one_mul, mul_one] at h
  exact h

theorem det_kth (θ : Fin n → ℝ) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) : (kth θ).det = 1 := by
  exact det_kth_eq_one θ

theorem jF_kak (e : ℤ) (p q : ℕ) (k : GR n) (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ) (hu : uᴴ * u = 1)
    (hu' : u'ᴴ * u' = 1) (hθ : ∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) (hkm : mR k = mM u * kth θ * mM u') :
    jF e p q k (I • (1 : Matrix (Fin n) (Fin n) ℂ)) =
      (u.det * u.det * (u'.det * u'.det)) ^ e * (u.det * (∏ j, cexp (-(I * (θ j : ℂ)))) * u'.det) ^ (-(p : ℤ)) *
        (u.det * (∏ j, cexp (I * (θ j : ℂ))) * u'.det) ^ (-(q : ℤ)) := by
  have hdet : (mR k).det = u.det * u.det * (u'.det * u'.det) := by
    rw [hkm, det_mul, det_mul, det_mM_unitary u hu, det_mM_unitary u' hu', det_kth θ hθ, mul_one]
  have hk2 := hkm.trans (blocks_kak u u' hu hu' θ)
  have hdm : diagonal (fun j => cexp (-(I * (θ j : ℂ)))) =
      (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show -(I * (θ a : ℂ)) = (-(θ a : ℂ)) * I by ring, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hdp : diagonal (fun j => cexp (I * (θ j : ℂ))) =
      (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [dR, diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      rw [show I * (θ a : ℂ) = (θ a : ℂ) * I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    · simp [dR, diagonal_apply, h]
  have hA : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (-(I * (θ j : ℂ)))) * u' := by
    rw [hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdm]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_neg]
    abel
  have hZ : (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, conj_I, neg_smul]
  have hB : toBlocks₂₁ (mR k) * (I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ + toBlocks₂₂ (mR k) =
      u * diagonal (fun j => cexp (I * (θ j : ℂ))) * u' := by
    rw [hZ, hk2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hdp, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg, neg_neg]
    abel
  simp only [jF, hdet, hA, hB, det_mul, det_diagonal]

end PositivityTheory.Rg.Sw.Glob.VacI
end
end

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacJ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI

variable {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
  {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
  {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem rhoT_sq {m : ℕ} (t : ℝ) (ε : Fin m → Bool) (a : Fin m) : (rhoT t ε a) ^ 2 = 1 := by
  unfold VacE.rhoT; split_ifs <;> norm_num

theorem rot_gen (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (hl0 : l τ ≠ 0) (hN : LawN) (hNb : LawNbar) (hLM : LocMul)
    (hGZ : GZSch) (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ))
    (hL : IsLocFact ω τ fr ι L) (e : ℤ)
    (hlev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (φ : Fin n → ℝ) (hφ : ∀ j, -(Real.pi / 2) < φ j ∧ φ j ≤ Real.pi / 2) (K : ℂ) :
    L (mkG (kth φ) (inK_kth φ).1) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ)))
        (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
  have hc : ∀ j, 0 < Real.cos (φ j / 2) := fun j =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [(hφ j).1, Real.pi_pos], by linarith [(hφ j).2, Real.pi_pos]⟩
  have hk : mkG (kth φ) (inK_kth φ).1 = mkG (kth fun j => φ j / 2) (inK_kth _).1 * mkG (kth fun j => φ j / 2) (inK_kth _).1 := by
    apply Subtype.ext; apply Units.ext; exact kth_half φ
  have hf0 : IsSch (DG (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) (cpos hl0) tabs K
  rw [hk, hLM D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL _ _ _ hf0,
    rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc K, rot_DG hC hl0 hN hNb hLM hGZ L hL e hlev _ hc _]
  congr 1
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact dbl_angle _ _ (rhoT_sq _ _ a)

end PositivityTheory.Rg.Sw.Glob.VacJ
