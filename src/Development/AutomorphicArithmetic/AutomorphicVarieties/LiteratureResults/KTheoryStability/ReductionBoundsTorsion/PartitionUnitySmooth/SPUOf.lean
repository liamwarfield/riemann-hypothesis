module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.BQRSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GSmMin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.TransZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GTrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GRDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.RhoNonnegBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.PfGRLip
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GThick

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.PfDerB
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.QuadBd
open Matrix

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds

theorem quad_bd (N : ℕ) (V : Matrix (Fin N) (Fin N) ℂ) (M : ℝ) (hM : 0 ≤ M) (hV : ∀ a b, ‖V a b‖ ≤ M)
    (y : Fin N → ℂ) : |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ N * M * (star y ⬝ᵥ y).re := by
  have e1 : star y ⬝ᵥ (V *ᵥ y) = ∑ a, ∑ b, star (y a) * V a b * y b := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (star y ⬝ᵥ y).re = ∑ a, ‖y a‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [e2]
  calc |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ ‖star y ⬝ᵥ (V *ᵥ y)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ a, ∑ b, ‖y a‖ * M * ‖y b‖ := by
        rw [e1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        gcongr
        exact hV a b
    _ ≤ ∑ a, ∑ b, (M / 2 * ‖y a‖ ^ 2 + M / 2 * ‖y b‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        nlinarith [mul_nonneg hM (sq_nonneg (‖y a‖ - ‖y b‖))]
    _ = N * M * ∑ a, ‖y a‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

end PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds
end

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds Filter Topology

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private theorem d_rel {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gp L N) (h : HS L N)
    (z : VR L N) (w : InfinitePlace L) :
    star (z w) ⬝ᵥ (mat (actL g h) w *ᵥ z w) =
      star ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w) ⬝ᵥ
        (mat h w *ᵥ ((((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ z w)) := by
  rw [mat_actL, star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

private theorem d_key {L : Type} [Field L] [NumberField L] {N : ℕ} (x : Gp L N) (v : HS L N) (z : VR L N) :
    |qR (actL x v) z| ≤ N * ‖v‖ * qR (actL x (one L N).1) z := by
  unfold qR
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [d_rel, d_rel]
  have h1 : mat (one L N).1 w = 1 := rfl
  rw [h1, one_mulVec]
  refine quad_bd N (mat v w) ‖v‖ (norm_nonneg _) (fun a b => ?_) _
  exact ((norm_le_pi_norm (v.1 w a) b).trans (norm_le_pi_norm (v.1 w) a)).trans
    ((norm_le_pi_norm v.1 w).trans le_rfl)

theorem pf_DerB : DerB := by
  intro L _ _ N φ x B ε hB hε hd hl
  set p := actL x (one L N).1 with hp
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.comp_apply]
  set u := actL x v with hu
  have hline : HasDerivAt (fun t : ℝ => φ (p + t • u)) ((fderiv ℝ φ p) u) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
    have hD : HasFDerivAt φ (fderiv ℝ φ p) (p + (0 : ℝ) • u) := by
      simpa using hd.hasFDerivAt
    exact hD.comp_hasDerivAt (0 : ℝ) h1
  have hlim := hline.tendsto_slope_zero_right.norm
  set K : ℝ := N * ‖v‖ with hK
  have hK0 : 0 ≤ K := by positivity
  refine le_of_tendsto hlim ?_
  have hmem : Set.Ioo (0 : ℝ) (ε / (K + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hmem] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hδε : K * t ≤ ε := by
    have : (K + 1) * t < ε := by rwa [lt_div_iff₀ (by positivity), mul_comm] at ht1
    nlinarith
  have hcl : Cl (K * t) p (p + t • u) := by
    intro z
    have e : qR (p + t • u) z = qR p z + t * qR u z := by
      rw [← evR_apply, map_add (f := _), map_smul, evR_apply, evR_apply, smul_eq_mul]
    rw [e, add_sub_cancel_left, abs_mul, abs_of_pos ht0]
    have := d_key x v z
    rw [← hu, ← hp] at this
    nlinarith
  have hb := hl (K * t) (by positivity) hδε _ hcl
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, norm_mul, norm_inv, Real.norm_eq_abs,
    abs_of_pos ht0]
  rw [inv_mul_le_iff₀ ht0]
  nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.RhoNonneg
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem emb_val (γ : Gm L N) (w : InfinitePlace L) :
    ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  rfl

private theorem act_inj (γ : Gm L N) : Function.Injective (actL (emb L N γ) : HS L N → HS L N) := by
  intro a b hab
  have e := congrArg (actL (emb L N γ)⁻¹) hab
  rwa [← actL_mul, ← actL_mul, inv_mul_cancel, actL_one, actL_one] at e

private theorem inj_finsum {ι : Type} (f : HS L N →L[ℝ] HS L N) (hf : Function.Injective f)
    (g : ι → HS L N) : f (∑ᶠ i, g i) = ∑ᶠ i, f (g i) := by
  by_cases h : (Function.support g).Finite
  · exact map_finsum f h
  · have e : (Function.support fun i => f (g i)) = Function.support g := by
      ext i
      simp only [Function.mem_support, ne_eq, map_eq_zero_iff f hf]
    have h' : ¬ (Function.support fun i => f (g i)).Finite := by rwa [e]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', map_zero]

private theorem mat_rk (h : HS L N) (v : Lat L N) (w : InfinitePlace L) :
    mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl

private theorem rk_act (γ : Gm L N) (h : HS L N) (v : Lat L N) :
    rk (actL (emb L N γ) h) (γ • v) = actL (emb L N γ) (rk h v) := by
  refine HS_ext fun w => ?_
  have hv : toR (γ • v) w = ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ toR v w := by
    rw [smul_lat, toR_mulVec, emb_val]
  have hPA : (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *
      ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mat_rk, mat_actL, mat_actL, mat_rk, hv]
  set P := (((emb L N γ w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hP
  set A := ((emb L N γ w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hA
  have e1 : (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ toR v w) := by
    calc (Pᴴ * mat h w * P) *ᵥ (A *ᵥ toR v w) = Pᴴ *ᵥ (mat h w *ᵥ ((P * A) *ᵥ toR v w)) := by
          simp only [mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by rw [hPA, one_mulVec]
  rw [e1, star_mulVec, conjTranspose_conjTranspose, mul_vecMulVec, vecMulVec_mul]

private theorem zed_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : zed s (actL (emb L N γ) h) = zed s h := by
  unfold zed
  rw [← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
    (f := fun v => rho (q (actL (emb L N γ) h) v / s))]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul]

private theorem sum_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) :
    ∑ᶠ v : Lat L N, rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v =
      actL (emb L N γ) (∑ᶠ v : Lat L N, rho (q h v / s) • rk h v) := by
  rw [inj_finsum _ (act_inj γ),
    ← finsum_comp_equiv (MulAction.toPerm γ : Equiv.Perm (Lat L N))
      (f := fun v => rho (q (actL (emb L N γ) h) v / s) • rk (actL (emb L N γ) h) v)]
  refine finsum_congr fun v => ?_
  simp only [MulAction.toPerm_apply, hq, inv_smul_smul, rk_act, map_smul]

private theorem term_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (s : ℝ) (γ : Gm L N) (h : HS L N) : term s (actL (emb L N γ) h) = actL (emb L N γ) (term s h) := by
  unfold term
  rw [zed_act hq, sum_act hq, map_smul]

private theorem ret_act (hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v))
    (μ : HS L N → ℝ) (hμ : Smoothing lamD μ) (γ : Gm L N) {h : HS L N} (hh : h ∈ Pos L N) :
    ret μ (actL (emb L N γ) h) = actL (emb L N γ) (ret μ h) := by
  have hi : μ (actL (emb L N γ) h) = μ h := hμ.inv γ h hh
  unfold ret
  rw [hi, map_add (f := _), map_smul, inj_finsum _ (act_inj γ)]
  congr 1
  exact finsum_congr fun k => by rw [term_act hq, map_smul]

private def Psd (h : HS L N) : Prop := ∀ w, (mat h w).PosSemidef

private theorem psd_rk (h : HS L N) (v : Lat L N) : Psd (rk h v) := fun w => by
  rw [mat_rk]
  exact posSemidef_vecMulVec_self_star _

private theorem psd_add {a b : HS L N} (ha : Psd a) (hb : Psd b) : Psd (a + b) := fun w => by
  rw [mat_add]; exact (ha w).add (hb w)

private theorem psd_smul {a : HS L N} (ha : Psd a) {c : ℝ} (hc : 0 ≤ c) : Psd (c • a) := fun w => by
  rw [mat_smul]; exact (ha w).smul hc

private theorem psd_zero : Psd (0 : HS L N) := fun w => by
  rw [mat_zero]; exact PosSemidef.zero

private theorem psd_finsum {ι : Type} (g : ι → HS L N) (hg : ∀ i, Psd (g i)) : Psd (∑ᶠ i, g i) :=
  finsum_induction Psd psd_zero (fun _ _ => psd_add) hg

private theorem rho_nonneg (x : ℝ) : 0 ≤ rho x := Real.smoothTransition.nonneg _

private theorem psd_term (s : ℝ) (h : HS L N) : Psd (term s h) := by
  unfold term
  refine psd_smul (psd_finsum _ fun v => psd_smul (psd_rk h v) (rho_nonneg _)) ?_
  exact inv_nonneg.2 (mul_nonneg (sq_nonneg s) (finsum_nonneg fun v => rho_nonneg _))

private theorem psd_qR {a : HS L N} (ha : Psd a) (z : VR L N) : 0 ≤ qR a z :=
  Finset.sum_nonneg fun w _ => (Complex.le_def.1 ((ha w).dotProduct_mulVec_nonneg (z w))).1

theorem pf_GREqv : GREqv := by
  intro hB L _ _ N hN μ hμ h hh
  have hq : ∀ (γ : Gm L N) (h : HS L N) (v : Lat L N), q (actL (emb L N γ) h) v = q h (γ⁻¹ • v) :=
    (hB L N hN).2.1
  obtain ⟨c, C, hc, hcmp⟩ := hμ.cmp
  have hD : 0 < lamD h := ((hB L N hN).1 _ ((hB L N hN).1 h hh).2.2.2.1).1
  have hμp : 0 < μ h := lt_of_lt_of_le (mul_pos hc hD) (hcmp h hh).1
  set S := ∑ᶠ k : ℤ, rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h with hSdef
  have hS : Psd S := psd_finsum _ fun k => psd_smul (psd_term _ _) (rho_nonneg _)
  have hr : ret μ h = μ h • h + S := rfl
  refine ⟨fun γ => ret_act hq μ hμ γ hh, fun w => ?_, fun z => ?_⟩
  · rw [hr, mat_add, mat_smul]
    exact ((hh w).smul hμp).add_posSemidef (hS w)
  · have e : qR (μ h • h + S) z = μ h * qR h z + qR S z := by
      simp only [← evR_apply, map_add (f := _), map_smul, smul_eq_mul]
    rw [hr, e]
    linarith [psd_qR hS z]

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.PfGFin
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

set_option maxHeartbeats 800000 in
theorem pf_GFin : GFin := by
  intro hSHt hSm hRS hRE hRL hRD hRLip hTh hPr hBu hNr hDB
  intro L _ _ hTC
  refine ⟨1, fun N hN => ?_⟩
  obtain ⟨μ, hμ⟩ := hSm L N hN
  obtain ⟨cL, hcL, hL⟩ := hRL L N hN μ hμ
  obtain ⟨cD, hcD, hD⟩ := hRD L hTC N hN μ hμ
  obtain ⟨K, hKc, hKP, hKt⟩ := hTh L hTC N hN (min cL cD) (lt_min hcL hcD)
  obtain ⟨ψ, K', Cψ, hK'c, hK'P, hψ, hψsupp, hψb, hψsum, hψlip⟩ := hBu L N K hKc hKP
  obtain ⟨nf, Cn, hCn, hnS, hnt, hnEq, hnH, hnLL, hnLip⟩ := hNr L N hN
  obtain ⟨Cr, hCr, hrLip⟩ := hRLip L N hN μ hμ
  obtain ⟨c0, hc0, hc0le⟩ := (hSHt L hTC N hN).2.2.1
  have hPopen : IsOpen (Pos L N) := (hPr L N).1
  have hcone : ∀ t : ℝ, 0 < t → ∀ h ∈ Pos L N, t • h ∈ Pos L N := by
    intro t ht h hh
    unfold Pos at hh ⊢
    intro w
    have e : mat (t • h) w = t • mat h w := by simp
    rw [e]
    exact (hh w).smul ht
  have hnP : ∀ h ∈ Pos L N, nf h ∈ Pos L N := by
    intro h hh
    obtain ⟨t, ht, e⟩ := hnt h hh
    rw [e]
    exact hcone t ht h hh
  have hFP : ∀ h ∈ Pos L N, ret μ (nf h) ∈ Pos L N := fun h hh =>
    (hRE L N hN μ hμ (nf h) (hnP h hh)).2.1
  have hFeq : ∀ γ : Gm L N, ∀ h ∈ Pos L N, ret μ (nf (ac γ h)) = ac γ (ret μ (nf h)) := by
    intro γ h hh
    rw [hnEq γ h hh, (hRE L N hN μ hμ (nf h) (hnP h hh)).1 γ]
  have hinv : ∀ (γ : Gm L N) (h : HS L N), actL ((emb L N) γ)⁻¹ h = ac γ⁻¹ h := by
    intro γ h
    rw [← map_inv]
  have hretS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ret μ) (Pos L N) := hRS L N hN μ hμ
  have hFS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ret μ (nf h)) (Pos L N) :=
    hretS.comp hnS (fun h hh => hnP h hh)
  have hFc : ContinuousOn (fun h => ret μ (nf h)) (Pos L N) := hFS.continuousOn
  have hφS : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun h => ψ (ret μ (nf h))) (Pos L N) :=
    hψ.comp_contDiffOn hFS
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  refine ⟨⟨fun h => ψ (ret μ (nf h)), hφS, ?_, ?_, ?_, ?_, ⟨Cψ, fun h _ => hψb _⟩, ?_⟩⟩
  · intro h0
    obtain ⟨V, hV, hV0, hVP⟩ := exists_compact_subset hPopen h0.2
    have hW : IsCompact ((fun h => ret μ (nf h)) '' V) := hV.image_of_continuousOn (hFc.mono hVP)
    have hWP : (fun h => ret μ (nf h)) '' V ⊆ Pos L N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hFP y (hVP hy)
    have hfin := (hPr L N).2 _ (hW.union hK'c) (Set.union_subset hWP hK'P)
    refine ⟨Subtype.val ⁻¹' interior V,
      continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hV0), ?_⟩
    refine (hfin.preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hS, hU⟩
    have hk := hψsupp _ hS
    rw [hinv, hFeq _ _ h.2] at hk
    exact ⟨_, Or.inl ⟨h, interior_subset hU, rfl⟩, Or.inr hk⟩
  · intro h hh
    have h1 : min cL cD ≤ lam (ret μ (nf h)) := (min_le_left cL cD).trans (hL (nf h) (hnP h hh))
    have h2 : min cL cD ≤ lamD (ret μ (nf h)) := (min_le_right cL cD).trans (hD (nf h) (hnP h hh))
    obtain ⟨γ0, hγ0⟩ := hKt (ret μ (nf h)) (hFP h hh) h1 h2
    rw [← hψsum (ret μ (nf h)) (hFP h hh) ⟨γ0, hγ0⟩]
    refine finsum_congr fun γ => ?_
    rw [hinv, hinv, hFeq _ _ hh]
  · have hcl : closure {k : ↑(Pos L N) | ψ (ret μ (nf ↑k)) ≠ 0} ⊆
        {k : ↑(Pos L N) | ret μ (nf ↑k) ∈ K'} := by
      apply closure_minimal
      · intro k hk
        exact hψsupp _ hk
      · exact hK'c.isClosed.preimage hFc.restrict
    refine (((hPr L N).2 K' hK'c hK'P).preimage inv_injective.injOn).subset ?_
    rintro γ ⟨h, hh, hg⟩
    have a := hcl hh
    have b := hcl hg
    simp only [Set.mem_setOf_eq] at a b
    change ret μ (nf (actL ((emb L N) γ)⁻¹ ↑h)) ∈ K' at b
    rw [hinv, hFeq _ _ h.2] at b
    exact ⟨_, a, b⟩
  · intro r hr h hh
    simp only [hnH r hr h hh]
  · refine ⟨(N : ℝ) * (Cψ * Cr * Cn * (1 + c0⁻¹)), fun x => ?_⟩
    have h0P : actL x ↑(one L N) ∈ Pos L N := (x • one L N).2
    obtain ⟨t, htp, et⟩ := hnt _ h0P
    have hprod : lam (nf (actL x ↑(one L N))) * lamD (nf (actL x ↑(one L N))) =
        lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)) := by
      rw [et]
      exact hnLL t htp _ h0P
    have hhtx : (lam (actL x ↑(one L N)) * lamD (actL x ↑(one L N)))⁻¹ = ht x := rfl
    have hx0 : c0 ≤ ht x := hc0le x
    have hxnn : 0 ≤ ht x := hc0.le.trans hx0
    have hB : 0 ≤ Cψ * Cr * (1 + ht x) * Cn :=
      mul_nonneg (mul_nonneg (mul_nonneg hCψ hCr) (by linarith)) hCn
    have hε : (0 : ℝ) < 1 / (4 * (Cn + 1)) := by positivity
    have hdiff : DifferentiableAt ℝ (fun h => ψ (ret μ (nf h))) (actL x ↑(one L N)) :=
      (hφS.contDiffAt (hPopen.mem_nhds h0P)).differentiableAt (by simp)
    have key := hDB L N (fun h => ψ (ret μ (nf h))) x (Cψ * Cr * (1 + ht x) * Cn)
      (1 / (4 * (Cn + 1))) hB hε hdiff (by
        intro δ hδ0 hδε k hk
        have hm : δ * (4 * (Cn + 1)) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hδε
          exact hδε
        have hδ4 : δ ≤ 1 / 4 := by nlinarith
        have hCnδ : Cn * δ ≤ 1 / 4 := by nlinarith
        have c1 := hnLip δ hδ0 hδ4 _ h0P k hk
        have c2 := hrLip (Cn * δ) (mul_nonneg hCn hδ0) hCnδ _ (hnP _ h0P) (nf k) c1
        rw [hprod, hhtx] at c2
        have c3 := hψlip _ (mul_nonneg (mul_nonneg hCr (by linarith))
          (mul_nonneg hCn hδ0)) _ (hFP _ h0P) _ c2
        exact le_of_le_of_eq c3 (by ring))
    show _ ≤ _ * ht x ^ 1
    rw [pow_one]
    have e1 : 1 ≤ c0⁻¹ * ht x := by
      rw [inv_mul_eq_div, le_div_iff₀ hc0]
      linarith
    have e2 : 1 + ht x ≤ (1 + c0⁻¹) * ht x := by nlinarith
    have hK0 : 0 ≤ (N : ℝ) * (Cψ * Cr * Cn) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hCψ hCr) hCn)
    calc _ ≤ (N : ℝ) * (Cψ * Cr * (1 + ht x) * Cn) := key
      _ = (N : ℝ) * (Cψ * Cr * Cn) * (1 + ht x) := by ring
      _ ≤ (N : ℝ) * (Cψ * Cr * Cn) * ((1 + c0⁻¹) * ht x) := mul_le_mul_of_nonneg_left e2 hK0
      _ = _ := by ring

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GbGSmooth
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

private def gb_g (s : ℝ) : ℝ := 1 / 2 + (s - 1 / 2) * Real.smoothTransition (2 * s - 1)

private theorem actL_mul_apply_eq_actL_actL {L : Type} [Field L] [NumberField L] {N : ℕ} (g g' : Gp L N) (h : HS L N) :
    actL (g * g') h = actL g (actL g' h) := by
  show actM (g * g') h = actM g (actM g' h)
  simp only [actM, LinearMap.coe_mk, AddHom.coe_mk]
  unfold mkHS
  apply Subtype.ext
  funext w i j
  simp only [mat, Pi.mul_apply, _root_.mul_inv_rev, Units.val_mul, Matrix.conjTranspose_mul, Matrix.of_apply]
  rw [show ∀ X : Matrix (Fin N) (Fin N) ℂ, (of fun i j => X i j) = X from fun _ => rfl]
  simp only [Matrix.mul_assoc]

private theorem contDiff_gb_g_and_half_le_and_eq_of_one_le : ContDiff ℝ (↑(⊤ : ℕ∞)) gb_g ∧ (∀ s, 1 / 2 ≤ gb_g s) ∧ ∀ s, 1 ≤ s → gb_g s = s := by
  refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
  · unfold gb_g
    fun_prop
  · unfold gb_g
    by_cases hs : s ≤ 1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      simp
    · have := Real.smoothTransition.nonneg (2 * s - 1)
      nlinarith
  · unfold gb_g
    rw [Real.smoothTransition.one_of_one_le (by linarith)]
    ring

private theorem norm_sub_le_two_mul_mul_norm_of_cl (hB : Basic) {L : Type} [Field L] [NumberField L] {N : ℕ} (δ : ℝ) (hδ : 0 ≤ δ)
    (h : HS L N) (hh : h ∈ Pos L N) (k : HS L N) (hk : Cl δ h k) : ‖k - h‖ ≤ 2 * δ * ‖h‖ := by
  have hc : 0 ≤ 2 * δ * ‖h‖ := by positivity
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : k = h := Subtype.ext (funext fun w => funext fun i => i.elim0)
    rw [this, sub_self, norm_zero]
    exact hc
  have E := (hB L N hN).2.2.2.2.1 δ hδ h hh k hk
  have hle : ∀ w i, ‖(h : InfinitePlace L → Fin N → Fin N → ℂ) w i i‖ ≤ ‖h‖ := fun w i =>
    ((norm_le_pi_norm _ i).trans (norm_le_pi_norm _ i)).trans (norm_le_pi_norm (h : InfinitePlace L → Fin N → Fin N → ℂ) w)
  show ‖((k - h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ)‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hc).2 fun w => (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
  have e := E w (Pi.single i 1) (Pi.single j 1)
  simp [mat] at e
  have d : ((k - h : HS L N) : InfinitePlace L → Fin N → Fin N → ℂ) w i j =
      (k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j := rfl
  rw [d]
  have x1 := (Complex.abs_re_le_norm ((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i)).trans (hle w i)
  have y1 := (Complex.abs_re_le_norm ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j)).trans (hle w j)
  have xy : ((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re ≤ ‖h‖ * ‖h‖ := by
    calc _ ≤ |((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re| := le_abs_self _
      _ = |((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re| * |((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re| := abs_mul _ _
      _ ≤ ‖h‖ * ‖h‖ := mul_le_mul x1 y1 (abs_nonneg _) (norm_nonneg _)
  have hd := norm_nonneg ((k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j)
  have h4 : 0 ≤ 4 * δ ^ 2 := by positivity
  have e2 : ‖(k : InfinitePlace L → Fin N → Fin N → ℂ) w i j - (h : InfinitePlace L → Fin N → Fin N → ℂ) w i j‖ ^ 2 ≤ (2 * δ * ‖h‖) ^ 2 := by
    calc _ ≤ _ := e
      _ = 4 * δ ^ 2 * (((h : InfinitePlace L → Fin N → Fin N → ℂ) w i i).re * ((h : InfinitePlace L → Fin N → Fin N → ℂ) w j j).re) := by ring
      _ ≤ 4 * δ ^ 2 * (‖h‖ * ‖h‖) := mul_le_mul_of_nonneg_left xy h4
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ hd hc two_ne_zero).1 e2

theorem pf_GBump : GBump := by
  intro hB hP L _ _ N K hK hKP
  have hPo : IsOpen (Pos L N) := (hP L N).1
  obtain ⟨ε, hε, hεK⟩ := hK.exists_cthickening_subset_open hPo hKP
  have hK'c : IsCompact (Metric.cthickening ε K) := hK.cthickening
  obtain ⟨f, hfs, hfc, hfr⟩ := (Metric.isOpen_thickening (δ := ε) (E := K)).exists_contDiff_support_eq (n := ⊤)
  have f0 : ∀ x, 0 ≤ f x := fun x => (hfr ⟨x, rfl⟩).1
  have f1 : ∀ x, f x ≤ 1 := fun x => (hfr ⟨x, rfl⟩).2
  obtain ⟨m, hm, hmK⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ f x := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hfc.continuous.continuousOn
      refine ⟨f x0, ?_, fun x hx => hmin hx⟩
      have : x0 ∈ f.support := by rw [hfs]; exact Metric.self_subset_thickening hε K hx0
      exact lt_of_le_of_ne (f0 x0) (Ne.symm this)
  set φ : HS L N → ℝ := fun x => f x / m with hφdef
  have φ0 : ∀ x, 0 ≤ φ x := fun x => div_nonneg (f0 x) hm.le
  have φ1 : ∀ x, φ x ≤ 1 / m := fun x => div_le_div_of_nonneg_right (f1 x) hm.le
  have φK : ∀ x ∈ K, 1 ≤ φ x := fun x hx => (one_le_div hm).2 (hmK x hx)
  have φs : ∀ x, φ x ≠ 0 → x ∈ Metric.cthickening ε K := fun x hx => by
    have : x ∈ f.support := fun h0 => hx (by simp [hφdef, h0])
    rw [hfs] at this
    exact Metric.thickening_subset_cthickening ε K this
  have φc : ContDiff ℝ (↑(⊤ : ℕ∞)) φ := hfc.div_const m
  set τ : Gm L N → HS L N →L[ℝ] HS L N := fun γ => actL ((emb L N γ)⁻¹) with hτ
  have hfin : ∀ B : Set (HS L N), IsCompact B → B ⊆ Pos L N →
      {γ | ∃ h ∈ B, τ γ h ∈ Metric.cthickening ε K}.Finite := by
    intro B hBc hBP
    have F := (hP L N).2 (B ∪ Metric.cthickening ε K) (hBc.union hK'c) (Set.union_subset hBP hεK)
    refine F.inv.subset ?_
    rintro γ ⟨h, hh, hγ⟩
    show ∃ h ∈ _, ac γ⁻¹ h ∈ _
    refine ⟨h, Or.inl hh, Or.inr ?_⟩
    show actL (emb L N γ⁻¹) h ∈ _
    rw [map_inv]
    exact hγ
  set S : HS L N → ℝ := fun h => ∑ᶠ γ, φ (τ γ h) with hS
  have τmul : ∀ γ δ h, τ δ (τ γ h) = τ (γ * δ) h := by
    intro γ δ h
    simp only [hτ]
    rw [← actL_mul_apply_eq_actL_actL, map_mul, _root_.mul_inv_rev]
  have Sinv : ∀ γ h, S (τ γ h) = S h := by
    intro γ h
    simp only [hS, τmul]
    exact finsum_comp_equiv (Equiv.mulLeft γ) (f := fun δ => φ (τ δ h))
  have Sloc : ∀ h0 ∈ Pos L N, ContDiffAt ℝ (↑(⊤ : ℕ∞)) S h0 := by
    intro h0 hh0
    obtain ⟨r, hr, hrP⟩ := Metric.isOpen_iff.1 hPo h0 hh0
    have hBc : IsCompact (Metric.closedBall h0 (r / 2)) := isCompact_closedBall h0 (r / 2)
    have hBP : Metric.closedBall h0 (r / 2) ⊆ Pos L N :=
      (Metric.closedBall_subset_ball (by linarith)).trans hrP
    have heq : ∀ h ∈ Metric.ball h0 (r / 2), S h = ∑ γ ∈ (hfin _ hBc hBP).toFinset, φ (τ γ h) := by
      intro h hh
      apply finsum_eq_sum_of_support_subset
      intro γ hγ
      rw [Set.Finite.coe_toFinset]
      exact ⟨h, Metric.ball_subset_closedBall hh, φs _ hγ⟩
    have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun h => ∑ γ ∈ (hfin _ hBc hBP).toFinset, φ (τ γ h)) :=
      ContDiff.sum fun γ _ => φc.comp (τ γ).contDiff
    exact hc.contDiffAt.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Metric.ball_mem_nhds h0 (by linarith)) heq)
  have Sfin : ∀ h ∈ Pos L N, (Function.support fun γ => φ (τ γ h)).Finite := fun h hh =>
    (hfin {h} isCompact_singleton (by simpa using hh)).subset fun γ hγ => ⟨h, rfl, φs _ hγ⟩
  obtain ⟨gc, g12, gid⟩ := contDiff_gb_g_and_half_le_and_eq_of_one_le
  have gpos : ∀ s, 0 < gb_g s := fun s => lt_of_lt_of_le (by norm_num) (g12 s)
  set ψ : HS L N → ℝ := fun h => φ h / gb_g (S h) with hψ
  have ψc : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ Pos L N
    · exact φc.contDiffAt.div (gc.contDiffAt.comp x (Sloc x hx)) (gpos _).ne'
    · have hxK : x ∉ Metric.cthickening ε K := fun h => hx (hεK h)
      have ev : ψ =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds hxK] with y hy
        have : φ y = 0 := by_contra fun h => hy (φs y h)
        simp [hψ, this]
      exact contDiffAt_const.congr_of_eventuallyEq ev
  have ψ0 : ∀ h, 0 ≤ ψ h := fun h => div_nonneg (φ0 h) (gpos _).le
  have ψb : ∀ h, ψ h ≤ 2 / m := fun h => by
    show φ h / gb_g (S h) ≤ 2 / m
    rw [div_le_iff₀ (gpos _)]
    calc φ h ≤ 1 / m := φ1 h
      _ = 2 / m * (1 / 2) := by ring
      _ ≤ 2 / m * gb_g (S h) := mul_le_mul_of_nonneg_left (g12 _) (by positivity)
  have ψs : ∀ h, ψ h ≠ 0 → h ∈ Metric.cthickening ε K := fun h hh =>
    φs h (fun h0 => hh (by simp [hψ, h0]))
  obtain ⟨Lc, hL⟩ := ψc.lipschitzWith_of_hasCompactSupport
    (HasCompactSupport.intro hK'c fun x hx => by_contra fun h => hx (ψs x h)) (by simp)
  obtain ⟨R, hR⟩ := hK'c.isBounded.exists_norm_le
  set R0 := max R 0 with hR0
  have hR0n : 0 ≤ R0 := le_max_right _ _
  have hLn : (0 : ℝ) ≤ Lc := Lc.2
  have hC : 0 ≤ 16 / m + 4 * Lc * R0 := by positivity
  refine ⟨ψ, Metric.cthickening ε K, 16 / m + 4 * Lc * R0, hK'c, hεK, ψc, ψs, ?_, ?_, ?_⟩
  · intro h
    rw [abs_of_nonneg (ψ0 h)]
    have : 2 / m ≤ 16 / m := by gcongr; norm_num
    linarith [ψb h, show 0 ≤ 4 * (Lc : ℝ) * R0 by positivity]
  · rintro h hh ⟨γ0, hγ0⟩
    have hsupp := Sfin h hh
    have Sge : 1 ≤ S h := by
      have e : τ γ0⁻¹ h = ac γ0 h := by
        simp only [hτ, map_inv, inv_inv]
      calc 1 ≤ φ (τ γ0⁻¹ h) := by rw [e]; exact φK _ hγ0
        _ ≤ S h := single_le_finsum γ0⁻¹ hsupp (fun j => φ0 _)
    have hfun : (fun γ => ψ (actL ((emb L N γ)⁻¹) h)) = fun γ => φ (τ γ h) * (gb_g (S h))⁻¹ := by
      funext γ
      show φ (τ γ h) / gb_g (S (τ γ h)) = _
      rw [Sinv, div_eq_mul_inv]
    rw [hfun, ← finsum_mul, gid _ Sge]
    exact mul_inv_cancel₀ (show S h ≠ 0 by linarith)
  · intro δ hδ h hh k hk
    by_cases hne : ψ k = ψ h
    · rw [hne, sub_self, abs_zero]
      positivity
    have hbd := norm_sub_le_two_mul_mul_norm_of_cl hB δ hδ h hh k hk
    by_cases hδ4 : 1 / 4 ≤ δ
    · have e1 : |ψ k - ψ h| ≤ 2 / m + 2 / m := by
        calc |ψ k - ψ h| ≤ |ψ k| + |ψ h| := abs_sub _ _
          _ ≤ 2 / m + 2 / m := by
            rw [abs_of_nonneg (ψ0 k), abs_of_nonneg (ψ0 h)]
            exact add_le_add (ψb k) (ψb h)
      have e2 : 16 / m * (1 / 4) ≤ 16 / m * δ := mul_le_mul_of_nonneg_left hδ4 (by positivity)
      have e3 : 0 ≤ 4 * (Lc : ℝ) * R0 * δ := by positivity
      have e4 : 2 / m + 2 / m = 16 / m * (1 / 4) := by ring
      nlinarith
    · push_neg at hδ4
      have hnh : ‖h‖ ≤ 2 * R0 := by
        have hor : h ∈ Metric.cthickening ε K ∨ k ∈ Metric.cthickening ε K := by
          by_contra hc
          push_neg at hc
          apply hne
          rw [show ψ k = 0 from by_contra fun H => hc.2 (ψs k H),
            show ψ h = 0 from by_contra fun H => hc.1 (ψs h H)]
        rcases hor with hm' | hm'
        · have := hR h hm'
          have : R ≤ R0 := le_max_left _ _
          linarith
        · have h1 := hR k hm'
          have h2 : R ≤ R0 := le_max_left _ _
          have h3 : ‖h‖ ≤ ‖k‖ + ‖k - h‖ := by
            have := norm_sub_le k (k - h)
            simpa using this
          have h4 : 2 * δ * ‖h‖ ≤ ‖h‖ / 2 := by nlinarith [norm_nonneg h]
          linarith
      have d1 : |ψ k - ψ h| ≤ Lc * ‖k - h‖ := by
        have := hL.dist_le_mul k h
        rwa [Real.dist_eq, dist_eq_norm] at this
      have d2 : (Lc : ℝ) * ‖k - h‖ ≤ Lc * (2 * δ * (2 * R0)) :=
        mul_le_mul_of_nonneg_left (hbd.trans (mul_le_mul_of_nonneg_left hnh (by positivity))) hLn
      have d3 : 0 ≤ 16 / m * δ := by positivity
      nlinarith

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GProdScale
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DiagForm
open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm

theorem exT {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (hh : h.PosDef) :
    ∃ T : Matrix (Fin N) (Fin N) ℂ, Tᴴ * h * T = 1 := by
  have hH := hh.1
  have key := hH.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at key
  simp only [Unitary.coe_star, star_star, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose] at key
  have hpos := hh.eigenvalues_pos
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal (fun i => ((Real.sqrt (hH.eigenvalues i))⁻¹ : ℂ)), ?_⟩
  rw [conjTranspose_mul, diagonal_conjTranspose]
  have e : ∀ (D E V : Matrix (Fin N) (Fin N) ℂ), (D * Vᴴ * h * (V * E)) = D * (Vᴴ * h * V) * E := by
    intro D E V
    simp only [Matrix.mul_assoc]
  rw [e, key, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have hi := hpos i
  have hs : (0:ℝ) < Real.sqrt (hH.eigenvalues i) := Real.sqrt_pos.mpr hi
  have hsq : Real.sqrt (hH.eigenvalues i) * Real.sqrt (hH.eigenvalues i) = hH.eigenvalues i := Real.mul_self_sqrt hi.le
  simp only [Pi.star_apply, Function.comp_apply, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hr : (Real.sqrt (hH.eigenvalues i))⁻¹ * hH.eigenvalues i * (Real.sqrt (hH.eigenvalues i))⁻¹ = 1 := by
    have hs2 : Real.sqrt (hH.eigenvalues i) ^ 2 = hH.eigenvalues i := Real.sq_sqrt hi.le
    field_simp
    linarith [hs2, hsq]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simpa using hc

theorem detMono {N : ℕ} (h k : Matrix (Fin N) (Fin N) ℂ) (hh : h.PosDef) (hk : k.PosSemidef) (c : ℝ)
    (hc : 0 < c) (hle : ∀ x : Fin N → ℂ, (star x ⬝ᵥ (k *ᵥ x)).re ≤ c * (star x ⬝ᵥ (h *ᵥ x)).re) :
    k.det.re ≤ c ^ N * h.det.re := by
  obtain ⟨T, hT⟩ := exT h hh
  have quad : ∀ (B M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ),
      star v ⬝ᵥ (Bᴴ * M * B) *ᵥ v = star (B *ᵥ v) ⬝ᵥ M *ᵥ (B *ᵥ v) := by
    intro B M v
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hk' : (Tᴴ * k * T).PosSemidef := hk.conjTranspose_mul_mul_same T
  have hev : ∀ i, hk'.1.eigenvalues i ≤ c := by
    intro i
    rw [hk'.1.eigenvalues_eq]
    have hv := hle (T *ᵥ (hk'.1.eigenvectorBasis i).ofLp)
    rw [← quad T k, ← quad T h, hT, one_mulVec] at hv
    have hn : star (hk'.1.eigenvectorBasis i).ofLp ⬝ᵥ (hk'.1.eigenvectorBasis i).ofLp = 1 := by
      have := (hk'.1.eigenvectorBasis).orthonormal.1 i
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, this]
      simp
    rw [hn] at hv
    simpa using hv
  have hprod : (Tᴴ * k * T).det.re ≤ c ^ N := by
    rw [hk'.1.det_eq_prod_eigenvalues]
    erw [← Complex.ofReal_prod, Complex.ofReal_re]
    calc ∏ i, hk'.1.eigenvalues i ≤ ∏ _i : Fin N, c :=
          Finset.prod_le_prod₀ (fun i _ => hk'.eigenvalues_nonneg i) (fun i _ => hev i)
      _ = c ^ N := by simp
  have e : ∀ X : ℂ, star T.det * X * T.det = (Complex.normSq T.det : ℂ) * X := by
    intro X
    rw [← Complex.mul_conj, Complex.star_def]
    ring
  have hd1 := congrArg Matrix.det hT
  rw [det_mul, det_mul, det_conjTranspose, det_one, e] at hd1
  rw [det_mul, det_mul, det_conjTranspose, e, Complex.re_ofReal_mul] at hprod
  have hre := congrArg Complex.re hd1
  rw [Complex.re_ofReal_mul, Complex.one_re] at hre
  have hnd : 0 < Complex.normSq T.det := by
    refine lt_of_le_of_ne (Complex.normSq_nonneg _) fun h0 => ?_
    rw [← h0, zero_mul] at hre
    exact zero_ne_one hre
  refine le_of_mul_le_mul_left ?_ hnd
  calc Complex.normSq T.det * k.det.re ≤ c ^ N := hprod
    _ = Complex.normSq T.det * (c ^ N * h.det.re) := by
      rw [mul_left_comm, hre, mul_one]

theorem lipAlg (δ Ah Ak H K : ℝ) (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4) (hAh : 0 < Ah) (h1 : (1 - δ) * Ah ≤ Ak)
    (h2 : Ak ≤ (1 + δ) * Ah) (hH : 0 ≤ H) (hK : |K - H| ≤ δ * H) :
    |Ak⁻¹ * K - Ah⁻¹ * H| ≤ 3 * δ * (Ah⁻¹ * H) := by
  have hAk : 0 < Ak := by nlinarith
  have e : Ak⁻¹ * K - Ah⁻¹ * H = (Ah * (K - H) + H * (Ah - Ak)) / (Ak * Ah) := by
    field_simp
    ring
  have e2 : 3 * δ * (Ah⁻¹ * H) = 3 * δ * H * Ak / (Ak * Ah) := by
    field_simp
  rw [e, e2, abs_div, abs_of_pos (mul_pos hAk hAh)]
  apply div_le_div_of_nonneg_right _ (mul_pos hAk hAh).le
  have hd : |Ah - Ak| ≤ δ * Ah := by
    rw [abs_le]
    constructor <;> nlinarith
  have h3 : 0 ≤ 3 * Ak - 2 * Ah := by nlinarith
  calc |Ah * (K - H) + H * (Ah - Ak)| ≤ |Ah * (K - H)| + |H * (Ah - Ak)| := abs_add_le _ _
    _ = Ah * |K - H| + H * |Ah - Ak| := by rw [abs_mul, abs_mul, abs_of_pos hAh, abs_of_nonneg hH]
    _ ≤ Ah * (δ * H) + H * (δ * Ah) := by gcongr
    _ ≤ 3 * δ * H * Ak := by nlinarith [mul_nonneg (mul_nonneg hδ hH) h3]

end PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm
end

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL PositivityTheory.KB PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux PositivityTheory.KB.SmoothPartitionUnityBasic.LipschitzAlgebraNorm
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

section GNrmHelpers

set_option linter.unusedSectionVars false

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private def gP (h : HS L N) : ℝ := ∏ w : InfinitePlace L, ((mat h w).det.re) ^ w.mult

private theorem g_qR_single [DecidableEq (InfinitePlace L)]
    (h : HS L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    qR h (Pi.single w x) = (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  unfold qR
  rw [Finset.sum_eq_single w (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
    (fun hw => absurd (Finset.mem_univ w) hw), Pi.single_eq_same]

private theorem g_cl_at {δ : ℝ} {h k : HS L N}
    (hcl : Cl δ h k) (w : InfinitePlace L) (x : Fin N → ℂ) :
    |(star x ⬝ᵥ (mat k w *ᵥ x)).re - (star x ⬝ᵥ (mat h w *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (mat h w *ᵥ x)).re := by
  classical
  have := hcl (Pi.single w x)
  rwa [g_qR_single, g_qR_single] at this

private theorem g_qR_smul (c : ℝ) (h : HS L N) (z : VR L N) : qR (c • h) z = c * qR h z := by
  rw [← evR_apply, map_smul, evR_apply, smul_eq_mul]

private theorem g_det_pos {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) : 0 < (mat h w).det.re :=
  (Complex.pos_iff.1 (hh w).det_pos).1

private theorem g_gP_pos {h : HS L N} (hh : h ∈ Pos L N) : 0 < gP h :=
  Finset.prod_pos fun w _ => pow_pos (g_det_pos hh w) _

private theorem g_prod_scale (c : ℝ) (f : InfinitePlace L → ℝ) :
    ∏ w : InfinitePlace L, (c ^ N * f w) ^ w.mult = c ^ (N * Module.finrank ℚ L) * ∏ w, f w ^ w.mult := by
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul]

private theorem g_det_smul (r : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) : (r • M).det.re = r ^ N * M.det.re := by
  have : r • M = (r : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [this, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private theorem g_gP_smul (r : ℝ) (h : HS L N) : gP (r • h) = r ^ (N * Module.finrank ℚ L) * gP h := by
  unfold gP
  simp only [mat_smul, g_det_smul]
  exact g_prod_scale r _

private theorem g_emb_val (γ : Gm L N) (w : InfinitePlace L) :
    (((emb L N γ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  ext i j
  simp [emb, toP, toK, embO, Matrix.GeneralLinearGroup.map_apply]

private theorem g_ginv (γ : Gm L N) (w : InfinitePlace L) :
    ((((emb L N γ) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w) := by
  rw [← g_emb_val, map_inv, Pi.inv_apply]

private theorem g_gP_ac (γ : Gm L N) (h : HS L N) : gP (actL (emb L N γ) h) = gP h := by
  unfold gP
  set u : L := algebraMap (𝓞 L) L ((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).det with hu
  have hw : ∀ w : InfinitePlace L, (mat (actL (emb L N γ) h) w).det.re = w u ^ 2 * (mat h w).det.re := by
    intro w
    rw [mat_actL, g_ginv, det_mul, det_mul, det_conjTranspose]
    have e : (((γ⁻¹ : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)).map (embO w)).det = w.embedding u := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e]
    have e2 : star (w.embedding u) * (mat h w).det * w.embedding u =
        ((Complex.normSq (w.embedding u) : ℝ) : ℂ) * (mat h w).det := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
    rw [e2, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  simp only [hw, mul_pow, Finset.prod_mul_distrib]
  have hn : |Algebra.norm ℚ u| = 1 := by
    have := NumberField.Units.norm L (Matrix.GeneralLinearGroup.det (γ⁻¹ : Gm L N))
    simpa [hu, Matrix.GeneralLinearGroup.val_det_apply] using this
  have hu1 : ∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult = 1 := by
    rw [show (∏ w : InfinitePlace L, (w u ^ 2) ^ w.mult) = (∏ w : InfinitePlace L, w u ^ w.mult) ^ 2 by
      rw [← Finset.prod_pow]; refine Finset.prod_congr rfl fun w _ => ?_; rw [← pow_mul, ← pow_mul, mul_comm]]
    rw [InfinitePlace.prod_eq_abs_norm]
    rw [hn, Rat.cast_one, one_pow]
  rw [hu1, one_mul]

private theorem g_ent (w : InfinitePlace L) (a b : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun h : HS L N => mat h w a b) := by
  have e : (fun h : HS L N => mat h w a b) =
      (fun x : InfinitePlace L → Fin N → Fin N → ℂ => x w a b) ∘ (HSsub L N).subtypeL := rfl
  rw [e]
  exact (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) a) b).comp (HSsub L N).subtypeL.contDiff

private theorem g_gP_cd : ContDiff ℝ (⊤ : ℕ∞) (gP : HS L N → ℝ) := by
  unfold gP
  refine contDiff_prod fun w _ => ContDiff.pow ?_ _
  have := Complex.reCLM.contDiff.comp (cd_det (k := (⊤ : ℕ∞)) (fun h : HS L N => mat h w) (fun i j => g_ent w i j))
  simpa [Function.comp_def] using this

end GNrmHelpers

theorem pf_GNrm : GNrm := by
  intro hB L _ _ N hN
  classical
  obtain ⟨-, -, -, h4, -, -⟩ := hB L N hN
  have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hNd : (0 : ℝ) < (N : ℝ) * (Module.finrank ℚ L : ℝ) := mul_pos (Nat.cast_pos.2 hN) (Nat.cast_pos.2 hd)
  set a : ℝ := ((N : ℝ) * (Module.finrank ℚ L : ℝ))⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hNd
  have hNa : ((N * Module.finrank ℚ L : ℕ) : ℝ) * a = 1 := by
    rw [ha, Nat.cast_mul, mul_inv_cancel₀ hNd.ne']
  have hpow : ∀ c : ℝ, 0 ≤ c → (c ^ (N * Module.finrank ℚ L)) ^ a = c := fun c hc => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, hNa, Real.rpow_one]
  refine ⟨fun h => (gP h ^ (-a)) • h, 3, by norm_num, ?c1, ?c2, ?c3, ?c4, ?c5, ?c6⟩
  · have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun h : HS L N => gP h ^ (-a)) (Pos L N) := fun h hh =>
      ((g_gP_cd (L := L) (N := N)).contDiffAt.rpow_const_of_ne (g_gP_pos hh).ne').contDiffWithinAt
    exact hs.smul (contDiff_id.contDiffOn (s := Pos L N))
  · intro h hh
    exact ⟨_, Real.rpow_pos_of_pos (g_gP_pos hh) _, rfl⟩
  · intro γ h hh
    dsimp only
    rw [ac, ac, g_gP_ac, map_smul]
  · intro r hr h hh
    dsimp only
    rw [g_gP_smul, Real.mul_rpow (by positivity) (g_gP_pos hh).le, smul_smul]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, mul_neg, hNa, Real.rpow_neg_one]
    field_simp
  · intro r hr h hh
    have hq : ∀ (c : ℝ) (k : HS L N) (y : Lat L N), q (c • k) y = c * q k y := fun c k y => by
      rw [← ev_apply, map_smul, ev_apply, smul_eq_mul]
    have hlam : ∀ (c : ℝ), 0 < c → ∀ k : HS L N, lam (c • k) = c * lam k := fun c hc k => by
      unfold lam
      simp only [hq]
      rw [Real.mul_iInf_of_nonneg hc.le]
    have hdual : dualH (r • h) = r⁻¹ • dualH h := HS_ext fun w => by
      simp only [dualH, mat_mkHS, mat_smul]
      have hdet : IsUnit (mat h w).det := (Matrix.isUnit_iff_isUnit_det _).1 (hh w).isUnit
      rw [Matrix.inv_eq_left_inv (B := r⁻¹ • (mat h w)⁻¹) (by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
          Matrix.nonsing_inv_mul _ hdet]), transpose_smul]
    unfold lamD
    rw [hdual, hlam r hr, hlam r⁻¹ (inv_pos.2 hr), mul_mul_mul_comm, mul_inv_cancel₀ hr.ne', one_mul]
  · intro δ hδ hδ4 h hh k hcl
    have hk : k ∈ Pos L N := (h4 δ hδ (by linarith) h hh k hcl).1
    have hat := fun w x => g_cl_at hcl w x
    have h1δ : 0 < 1 - δ := by linarith
    have hup : ∀ w, (mat k w).det.re ≤ (1 + δ) ^ N * (mat h w).det.re := fun w =>
      detMono _ _ (hh w) (hk w).posSemidef (1 + δ) (by linarith) (fun x => by
        have := (abs_le.1 (hat w x)).2; rw [add_mul, one_mul]; linarith)
    have hlo : ∀ w, (1 - δ) ^ N * (mat h w).det.re ≤ (mat k w).det.re := fun w => by
      have h0 := detMono _ _ (hk w) (hh w).posSemidef (1 - δ)⁻¹ (inv_pos.2 h1δ) (fun x => by
        rw [le_inv_mul_iff₀ h1δ]
        have := (abs_le.1 (hat w x)).1; rw [sub_mul, one_mul]; linarith)
      have := mul_le_mul_of_nonneg_left h0 (pow_nonneg h1δ.le N)
      rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h1δ.ne', one_pow, one_mul] at this
    have hPup : gP k ≤ (1 + δ) ^ (N * Module.finrank ℚ L) * gP h := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (g_det_pos hk w).le _)
        (fun w _ => pow_le_pow_left₀ (g_det_pos hk w).le (hup w) _)
    have hPlo : (1 - δ) ^ (N * Module.finrank ℚ L) * gP h ≤ gP k := by
      unfold gP
      rw [← g_prod_scale]
      exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) _)
        (fun w _ => pow_le_pow_left₀ (mul_nonneg (pow_nonneg h1δ.le N) (g_det_pos hh w).le) (hlo w) _)
    have hPh := g_gP_pos hh
    have hPk := g_gP_pos hk
    have hA2 : gP k ^ a ≤ (1 + δ) * gP h ^ a := by
      have := Real.rpow_le_rpow hPk.le hPup ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ (by linarith)] at this
    have hA1 : (1 - δ) * gP h ^ a ≤ gP k ^ a := by
      have := Real.rpow_le_rpow (by positivity) hPlo ha0.le
      rwa [Real.mul_rpow (by positivity) hPh.le, hpow _ h1δ.le] at this
    intro z
    dsimp only
    rw [g_qR_smul, g_qR_smul, Real.rpow_neg hPk.le, Real.rpow_neg hPh.le]
    have hH : 0 ≤ qR h z := Finset.sum_nonneg fun w _ => re_nonneg_psd (hh w).posSemidef (z w)
    exact lipAlg δ _ _ _ _ hδ hδ4 (Real.rpow_pos_of_pos hPh a) hA1 hA2 hH (hcl z)

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
end

namespace PositivityTheory.KB

open SmoothPartitionUnityBasic

theorem sPU_of : SHt → SPU := fun hH =>
  have hC := pf_GCount pf_Basic
  have hT := pf_GTrans pf_Basic pf_TransZ
  have hE := pf_GREqv pf_Basic
  have hL := pf_GTLip pf_Basic hC
  have hP := pf_GProper pf_Basic
  pf_GFin hH (gSmMin pf_Basic hC) (pf_GRSmooth pf_Basic) hE (pf_GRLow pf_Basic hC hE hL) (pf_GRDual pf_Basic hT hE hL)
    (pf_GRLip pf_Basic hE hL) (pf_GThick pf_Basic hT) hP (pf_GBump pf_Basic hP) (pf_GNrm pf_Basic) pf_DerB

end PositivityTheory.KB
