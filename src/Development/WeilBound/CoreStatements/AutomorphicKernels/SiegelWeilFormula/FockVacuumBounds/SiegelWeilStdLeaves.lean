module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Strong
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.MajorantW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.FourierZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.LamSingOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.LinRedC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.WXMain

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.WqMain
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.MulDivCancelOfEq
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.LamTendsto
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerEqualRank.UnrXDifferentiable
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped Topology Classical

def unrX (N M : ℕ) (c : ℂ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin N, (1 - c ^ (M + (i : ℕ)) * (q : ℂ) ^ (-(2 * z + N - (i : ℕ))))

theorem unrX_differentiable (N M : ℕ) (c : ℂ) (q : ℕ) (hq : q ≠ 0) : Differentiable ℂ (unrX N M c q) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold unrX
  refine Differentiable.fun_finsetProd fun i _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => -(2 * z + N - (i : ℕ)))).const_cpow (Or.inl hq')))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eSp_sq (v : HeightOneSpectrum (𝓞 F)) : eSp E v ^ 2 = 1 := by
  unfold eSp; split_ifs <;> norm_num

theorem norm_eSp (v : HeightOneSpectrum (𝓞 F)) : ‖eSp E v‖ = 1 := by
  unfold eSp; split_ifs <;> simp

theorem one_sub_eSp_ne (v : HeightOneSpectrum (𝓞 F)) :
    1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  intro h
  have h1 : eSp E v / (Ideal.absNorm v.asIdeal : ℂ) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_div, norm_eSp, Complex.norm_natCast, norm_one] at h2
  have : (1 : ℝ) / Ideal.absNorm v.asIdeal < 1 := by rw [div_lt_one (by linarith)]; exact hq
  linarith

theorem hasProd_split' {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : {v // v ∉ S} => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) :=
  hasProd_split f S D h

theorem fix_point (Z H : ℂ → ℂ) (j : ℂ) (hZ : MeromorphicOn Z Set.univ) (hH : AnalyticAt ℂ H j)
    (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) :
    MeromorphicOn (Function.update Z j (H j)) Set.univ ∧ AnalyticAt ℂ (Function.update Z j (H j)) j ∧
      Function.update Z j (H j) j = H j ∧ ∀ s, s ≠ j → Function.update Z j (H j) s = Z s := by
  refine ⟨fun z _ => (hZ z trivial).update _ _, ?_, by simp, fun s hs => Function.update_of_ne hs _ _⟩
  refine hH.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE ?_ (by simp))
  filter_upwards [he, self_mem_nhdsWithin] with s hs hs'
  rw [Function.update_of_ne (show s ≠ j from hs'), hs]

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem val_gt (S : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - c v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (j : ℂ) (hj : 1 < j.re) (hH : AnalyticAt ℂ H j) (he : ∀ᶠ s in 𝓝[≠] j, H s = Z s) : H j = Z j := by
  obtain ⟨d, hd, hdp⟩ := euler_prod (ι := {v // v ∉ S}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => c v.1) (fun v => hc v.1) 0
  have hZd : ∀ s : ℂ, 1 < s.re → Z s = d ((s - 1) / 2) := by
    intro s hs
    have h1 : 0 < ((s - 1) / 2).re := by simp; linarith
    refine (hp s hs).unique ?_
    convert hdp _ h1 using 3 with v
    push_cast
    ring_nf
  have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcd : ContinuousAt (fun s : ℂ => d ((s - 1) / 2)) j := by
    have h1 : 0 < ((j - 1) / 2).re := by simp; linarith
    have hdo : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have := (hd.differentiableAt (hdo.mem_nhds h1)).continuousAt
    exact ContinuousAt.comp (g := d) (f := fun s : ℂ => (s - 1) / 2) this
      ((continuous_id.sub continuous_const).div_const 2).continuousAt
  have hev : H =ᶠ[𝓝[≠] j] fun s => d ((s - 1) / 2) := by
    filter_upwards [he, nhdsWithin_le_nhds (ho.mem_nhds hj)] with s hs hs'
    rw [hs, hZd s hs']
  have t1 : Tendsto H (𝓝[≠] j) (𝓝 (H j)) := hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 : Tendsto H (𝓝[≠] j) (𝓝 (d ((j - 1) / 2))) :=
    (hcd.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm
  rw [tendsto_nhds_unique t1 t2, hZd j hj]

theorem lam_tendsto (S : Finset (HeightOneSpectrum (𝓞 F))) (Z H : ℂ → ℂ)
    (hp : ∀ s : ℂ, 1 < s.re →
      HasProd (fun v : {v // v ∉ S} => 1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s))
    (hH : AnalyticAt ℂ H 1) (he : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H s = Z s) :
    Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 ((∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H 1)) := by
  have hofR : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans (by simp))
      (eventually_nhdsWithin_of_forall fun s hs => ?_)
    show (s : ℂ) ≠ 1
    exact_mod_cast ne_of_gt (show (1 : ℝ) < s from hs)
  have hH1 : Tendsto (fun s : ℝ => H s) (𝓝[>] 1) (𝓝 (H 1)) :=
    (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hofR
  have hfin : Tendsto (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1)
      (𝓝 (∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)))) := by
    have hc : Continuous (fun s : ℝ => ∏ v ∈ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) := by
      refine continuous_finsetProd S fun v _ => continuous_const.sub (continuous_const.mul ?_)
      have hq : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v
        exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
      exact Continuous.const_cpow (Complex.continuous_ofReal.neg) (Or.inl hq)
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    convert this using 2
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Complex.cpow_neg_one, div_eq_mul_inv]
  refine (hfin.mul hH1).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hofR.eventually he] with s hs hs'
  have hs1 : 1 < ((s : ℂ)).re := by simpa using hs
  rw [((hasProd_split' (fun v => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) S _
    (hp s hs1)).tprod_eq), hs']

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

theorem pow_sub_of_sq (c : ℂ) (hc : c ^ 2 = 1) (N i : ℕ) (hi : i ≤ N) :
    c ^ (N + i) = c ^ (((N - i : ℕ) : ℤ)) := by
  rw [zpow_natCast]
  have : N + i = (N - i) + 2 * i := by omega
  rw [this, pow_add, pow_mul, hc, one_pow, mul_one]

theorem mul_div_cancel_of_eq (x y D : ℂ) (hD : D ≠ 0) (hy : y = D) : x * y / D = x := by
  subst hy; field_simp

theorem unrX_zero_split (m : ℕ) (c : ℂ) (hc : c ^ 2 = 1) (q : ℕ) (hne : 1 - c / q ≠ 0) :
    unrX (m + 1) (m + 1) c q 0 / (1 - c / q) =
      ∏ i : Fin m, (1 - c ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) * (q : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
  unfold unrX
  rw [Fin.prod_univ_castSucc, mul_div_cancel_of_eq _ _ _ hne]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.val_castSucc]
    rw [pow_sub_of_sq c hc (m + 1) i (by omega)]
    congr 3
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    push_cast
    ring
  · simp only [Fin.val_last]
    rw [pow_sub_of_sq c hc (m + 1) m (by omega)]
    have h1 : m + 1 - m = 1 := by omega
    rw [h1]
    push_cast
    rw [show -(2 * (0 : ℂ) + (m + 1) - m) = -1 by ring, Complex.cpow_neg_one, zpow_one, div_eq_mul_inv]

theorem lpack (hLO : LOrd) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℂ → ℂ, MeromorphicOn K Set.univ ∧ AnalyticAt ℂ K 0 ∧
      (∀ z : ℂ, 0 < z.re →
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) z) (K z)) ∧
      ∃ lam P : ℂ,
        Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F),
          (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)))) (𝓝[>] 1) (𝓝 lam) ∧
        HasProd (fun v : {v // v ∉ S} => unrX N N (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) P ∧
        K 0 * ∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) = lam * P := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  choose Z hZm hZp H hHa hHe using fun i : Fin (m + 1) => hLO F E σ hcm S (((m + 1 - i : ℕ)) : ℤ)
  have hj1 : ∀ i : Fin (m + 1), 1 ≤ m + 1 - (i : ℕ) := fun i => by omega
  have hHe' : ∀ i : Fin (m + 1), ∀ᶠ s in 𝓝[≠] (((m + 1 - i : ℕ) : ℂ)), H i s = Z i s := by
    intro i
    have h := hHe i
    rw [if_pos (by exact_mod_cast hj1 i)] at h
    simpa only [pow_zero, one_mul, Int.cast_natCast] using h
  have hHa' : ∀ i : Fin (m + 1), AnalyticAt ℂ (H i) ((m + 1 - i : ℕ) : ℂ) := fun i => by
    simpa only [Int.cast_natCast] using hHa i
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Fin (m + 1) → ℂ → ℂ,
      Zc = fun i => Function.update (Z i) ((m + 1 - i : ℕ) : ℂ) (H i ((m + 1 - i : ℕ) : ℂ)) := ⟨_, rfl⟩
  have hfix : ∀ i : Fin (m + 1), MeromorphicOn (Zc i) Set.univ ∧ AnalyticAt ℂ (Zc i) ((m + 1 - i : ℕ) : ℂ) ∧
      Zc i ((m + 1 - i : ℕ) : ℂ) = H i ((m + 1 - i : ℕ) : ℂ) ∧
      ∀ s, s ≠ ((m + 1 - i : ℕ) : ℂ) → Zc i s = Z i s := fun i => by
    subst hZc
    exact fix_point (Z i) (H i) _ (hZm i) (hHa' i) (hHe' i)
  have h0 : ∀ i : Fin (m + 1), (2 * (0 : ℂ) + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) = ((m + 1 - i : ℕ) : ℂ) := fun i => by
    rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)]
    ring
  have hqne : ∀ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hnc : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ), ‖eSp E v ^ k‖ ≤ 1 := fun v k => by
    rw [norm_zpow, norm_eSp, one_zpow]
  refine ⟨fun z => ∏ i : Fin (m + 1), Zc i (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)), ?_, ?_, ?_, ?_⟩
  · intro z _
    exact MeromorphicAt.fun_prod fun i _ => ((hfix i).1 _ trivial).comp_analyticAt
      (g := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop)
  · refine (Finset.analyticAt_prod (Finset.univ : Finset (Fin (m + 1))) fun i _ =>
      AnalyticAt.comp_of_eq (hfix i).2.1
      (f := fun z : ℂ => 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)) (by fun_prop) (h0 i)).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp [Finset.prod_apply]
  · intro z hz
    unfold unrX
    refine hasProd_prod fun i _ => ?_
    have hi : (i : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast i.2
    have hre : 1 < (2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ)).re := by
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat]
      push_cast at hi ⊢
      nlinarith
    have hne : 2 * z + ((m + 1 : ℕ) : ℂ) - (i : ℕ) ≠ ((m + 1 - i : ℕ) : ℂ) := by
      intro h
      have h' := congrArg Complex.re h
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ m + 1)] at h'
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
        Complex.re_ofNat, Complex.im_ofNat] at h'
      push_cast at h'
      nlinarith
    rw [(hfix i).2.2.2 _ hne]
    convert hZp i _ hre using 2 with v
    rw [pow_sub_of_sq _ (eSp_sq v.1) (m + 1) i (by omega)]
  ·
    have hlj : ((m + 1 - ((Fin.last m : Fin (m + 1)) : ℕ) : ℕ) : ℂ) = 1 := by simp
    have hZl : ∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z (Fin.last m) s) := fun s hs => by
      convert hZp (Fin.last m) s hs using 2 with v
      simp
    have hHl : AnalyticAt ℂ (H (Fin.last m)) 1 := hlj ▸ hHa' (Fin.last m)
    have hEl : ∀ᶠ s in 𝓝[≠] (1 : ℂ), H (Fin.last m) s = Z (Fin.last m) s := hlj ▸ hHe' (Fin.last m)
    refine ⟨(∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) * H (Fin.last m) 1,
      ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ), lam_tendsto S _ _ hZl hHl hEl, ?_, ?_⟩
    · have hfun : (fun v : {v // v ∉ S} => unrX (m + 1) (m + 1) (eSp E v.1) (Ideal.absNorm v.1.asIdeal) 0 /
          (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) = fun v => ∏ i : Fin m,
            (1 - eSp E v.1 ^ (((m + 1 - (i : ℕ) : ℕ)) : ℤ) *
              (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(((m + 1 - (i : ℕ) : ℕ)) : ℂ))) := by
        funext v
        exact unrX_zero_split m _ (eSp_sq v.1) _ (one_sub_eSp_ne v.1)
      rw [hfun]
      refine hasProd_prod fun i _ => ?_
      have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
        rw [Complex.natCast_re]
        have : 2 ≤ m + 1 - (i : ℕ) := by omega
        exact_mod_cast this
      exact hZp i.castSucc _ hre
    · show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) * _ = _
      rw [show (∏ i : Fin (m + 1), Zc i (2 * 0 + ((m + 1 : ℕ) : ℂ) - (i : ℕ))) =
          ∏ i : Fin (m + 1), H i ((m + 1 - i : ℕ) : ℂ) from
        Finset.prod_congr rfl fun i _ => by rw [h0 i]; exact (hfix i).2.2.1]
      rw [Fin.prod_univ_castSucc, hlj]
      rw [show (∏ i : Fin m, H i.castSucc ((m + 1 - (i.castSucc : ℕ) : ℕ) : ℂ)) =
          ∏ i : Fin m, Z i.castSucc ((m + 1 - i : ℕ) : ℂ) from Finset.prod_congr rfl fun i _ => by
        have hre : 1 < (((m + 1 - (i : ℕ) : ℕ)) : ℂ).re := by
          rw [Complex.natCast_re]
          have : 2 ≤ m + 1 - (i : ℕ) := by omega
          exact_mod_cast this
        exact val_gt S _ (fun v => hnc v _) _ _ (hZp i.castSucc) _ hre (hHa' i.castSucc) (hHe' i.castSucc)]
      ring

end PositivityTheory.SiegelWeilFormula.Gen.WQ

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WQ

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter PositivityTheory.SiegelWeilFormula.Gen.W
open scoped TensorProduct Matrix Topology Classical

theorem whitGenEqOf : WhitGenEqOf := by
  intro hLoc hUnr hReal hFac hLO hDE F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok hrange _ ht
    μH 𝓕 hμH h𝓕
  obtain ⟨hMn, hM1⟩ := hok
  subst hMn
  have hani : ∀ x : Fin M → E, hE σ J x x = 0 → x = 0 := by
    rcases hrange with h | h
    · omega
    · exact h
  obtain ⟨t, ht⟩ := ht
  have hT := hD.hT

  have h0 := hDE F E σ hD.cm M hM1 J hD.herm hani T hT hD.det d bs 0 0 Φf Φv isSchwartzInf_zero hD.pure
    (fun X => by simp)
  have h1 := ((h0.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr
  obtain ⟨μi, hμi⟩ := h1.1
  obtain ⟨νi, hνi⟩ := (h1.2 μi hμi).1
  obtain ⟨μv, hμv⟩ := ((h1.2 μi hμi).2 νi hνi).1
  obtain ⟨νv, hνv⟩ := (((h1.2 μi hμi).2 νi hνi).2 μv hμv).1

  have hR := hReal F E σ hD.cm M J hD.herm M le_rfl ψ hD.chr ι θ l hD.places ε fr hD.frames g P μi νi hμi hνi

  have h2 := hDE F E σ hD.cm M hM1 J hD.herm hani T hT hD.det d bs Φ (phiInf θ l fr g P) Φf Φv hR.1 hD.pure hD.prod
  obtain ⟨ginf, gv, hdinf, hdv, -, hmean⟩ :=
    (((((h2.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr).2 μi hμi).2 νi hνi).2 μv hμv |>.2 νv hνv
  obtain ⟨Wi, hWi, hWi0, ti, hti⟩ := hR.2 ginf hdinf (hermOf (Ainf F) σ T hT) (hermOf_unit σ T hT hD.det _)

  have hL := fun v => hLoc F E σ hD.cm M J hD.herm M ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v)
    (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) (gv v) (hdv v) (hermOf (Fv F v) σ T hT)
    (hermOf_unit σ T hT hD.det _)
  choose Wv hWv hWv0 tv htv using hL

  obtain ⟨tu, hU⟩ := hUnr F E σ hD.cm M J hD.herm M T hT hD.det d bs ψ hD.chr
  have hev := (hU.and hD.std).and hD.pure.2.1
  obtain ⟨S, hSout⟩ := exists_finset_of_cofinite hev
  have hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) ∧
      ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) =
        unrX M M (eSp E v) (Ideal.absNorm v.asIdeal) z := by
    intro v hv z hz
    obtain ⟨⟨hu, hs1, hs2⟩, hpv⟩ := hSout v hv
    have hL12 : L₂ v = L₁ v := SetLike.coe_injective (hs2.trans hs1.symm)
    rw [hL12, hpv]
    exact hu (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz
  have hs00 : (((M : ℂ) - M) / 2) = 0 := by simp

  have hgv : ∀ v, v ∉ S → gv v (hermOf (Fv F v) σ T hT) = unrX M M (eSp E v) (Ideal.absNorm v.asIdeal) 0 := by
    intro v hv
    have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      omega
    have heq := eq_of_eqOn_right (hWv v) (unrX_differentiable M M (eSp E v) _ hq) (max (tv v) tu) fun z hz =>
      ((htv v z (lt_of_le_of_lt (le_max_left _ _) hz)).2).trans
        ((hPv v hv z (lt_of_le_of_lt (le_max_right _ _) hz)).2)
    rw [← hWv0 v, heq, hs00]
  obtain ⟨K, hKm, hKa, hKp, lam0, P0, hlam, hP0, hKval⟩ := lpack hLO σ hD.cm S M hM1
  have hPd : Differentiable ℂ (fun z => ∏ v ∈ S, Wv v z) := Differentiable.fun_finsetProd fun v _ => hWv v
  let G : ℂ → ℂ := fun z => Wi z * ((∏ v ∈ S, Wv v z) * K z)
  have hGm : MeromorphicOn G Set.univ := fun z _ =>
    (hWi.analyticAt z).meromorphicAt.mul ((hPd.analyticAt z).meromorphicAt.mul (hKm z (Set.mem_univ z)))
  have hGa : AnalyticAt ℂ G (((M : ℂ) - M) / 2) := by
    rw [hs00]
    exact (hWi.analyticAt 0).mul ((hPd.analyticAt 0).mul hKa)

  have hGs0 : G (((M : ℂ) - M) / 2) = 2 * meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) := by
    have hP0' : HasProd (fun v : {v // v ∉ S} => gv v.1 (hermOf (Fv F v.1) σ T hT) /
        (1 - eSp E v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))) P0 := by
      convert hP0 using 2 with v
      rw [hgv v.1 v.2]
    have hp := hasProd_split' (fun v => gv v (hermOf (Fv F v) σ T hT) /
        (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ))) S P0 hP0'
    rw [hmean lam0 hlam, hp.tprod_eq]
    show Wi _ * ((∏ v ∈ S, Wv v _) * K _) = _
    rw [hWi0, Finset.prod_congr rfl fun v _ => hWv0 v, hs00, Finset.prod_div_distrib]
    have hSne : ∏ v ∈ S, (1 - eSp E v / (Ideal.absNorm v.asIdeal : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => one_sub_eSp_ne v
    field_simp
    linear_combination (ginf (hermOf (Ainf F) σ T hT) * ∏ v ∈ S, gv v (hermOf (Fv F v) σ T hT)) * hKval

  have hright : Set.EqOn G
      (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)
      (rightOf (|t| + |ti| + |tu| + ∑ v ∈ S, |tv v|)) := by
    intro z hz
    have hz' : |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| < z.re := hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    have zt : t < z.re := by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]
    have zti : ti < z.re := by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]
    have ztu : tu < z.re := by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]
    have z0 : 0 < z.re := by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have ztv : ∀ v ∈ S, tv v < z.re := fun v hv => by
      have := Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv
      linarith [le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) := by
      intro v
      by_cases hv : v ∈ S
      · exact (htv v z (ztv v hv)).1
      · exact (hPv v hv z ztu).1
    have hF := hFac F E σ M M d J T bs ψ ι θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z
      (ht z zt) (hti z zti).1 hint
    have hp := hasProd_split' (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z b ∂(νv v)) S (K z) (by
      convert hKp z z0 using 2 with v
      exact (hPv v.1 v.2 z ztu).2)
    have hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v)
        (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop
        (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
          (T.map (inclR (Fv F v))) z b ∂(νv v)) * K z)) := hp
    have hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi =
        Wi z := (hti z zti).2.symm
    rw [hIi] at hF
    have hu := tendsto_nhds_unique hF (hlim.const_mul (Wi z))
    show Wi z * ((∏ v ∈ S, Wv v z) * K z) = _
    rw [Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]
    exact hu.symm
  exact ⟨G, ⟨Set.univ, Set.mem_univ _, ⟨⟨0, fun _ _ => trivial⟩, fun _ _ _ _ => trivial⟩, hGm, ⟨_, hright⟩⟩,
    hGa, hGs0⟩

end PositivityTheory.SiegelWeilFormula.Gen.WQ

theorem PositivityTheory.SiegelWeilFormula.Gen.whitGenEqOf : PositivityTheory.SiegelWeilFormula.Gen.WhitGenEqOf := PositivityTheory.SiegelWeilFormula.Gen.WQ.whitGenEqOf

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacuumGeneratesPolynomials
namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem absThm : AbsThm := absThm_of lv (cyc_of fft) (lc_of fft) nullIff

theorem vacuum_generates_polynomials : GenCore := genCore_top (cyc_of fft) (lc_of fft) nullIff

end PositivityTheory.Rg.Sw.AbsSt
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.siegelWeilStd_of (hA : AbsThm) (hT : TAll) (hTC : ThetaCoef) (hLo : LocOpEx) (hLI : LocInst)
    (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hKP : KFinPoly) (hPK : PolyKFin) (hU : Unfold)
    (hW : WhitK) (hWE : WhitEq) (hG : AbsSt.GenCore) (hLD : LDEx) (hVK : VacK) (hSt : Step) :
    SiegelWeilStd := by
  have hBL : EisBL := PositivityTheory.RgEis.Hd.eisBL
  have hSK : SecK := Khead.secK
  have hAux : AuxiliaryPrimeFunction := kfour.auxEx
  have hRD : RDEx := Krd.rdEx
  have hFM : FockMem := KFock.fockMem
  have hLE : LiftEx := KFock.liftEx hT.1
  have hLB : LamBd := kfour.lamBd
  have hLS : LamSing := KSing.lamSing_of kfour.coefEx kfour.fourierZero Krd.denseW hAux
  have hEW : EisWk := Aeis.eisWk
  have hMain := KMain.mainOf hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW
  have hLt := Khead.headOf hBL hSK (Khead.eisStrong_of hBL) hMain
  have hEq := Atop.mainEq_of hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE
  have hVA := Atop.vacAllOfC hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW
  have hLe := Atop.mainLeOf hRD hLD hVK hPK hEq hSt hVA
  exact Atop.fieldOf hBL hSK hLt hLe

end PositivityTheory.SiegelWeilFormula

end
