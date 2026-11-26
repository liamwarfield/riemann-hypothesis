module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
noncomputable section

open scoped ContDiff Topology

namespace UpperTheory.V.Lit.Geo

theorem hkSmooth : HkSmooth := by
  intro V F _ _ _ _ _ _ Y hY W hW q w hw
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  have hWat : ∀ p ∈ Y, ContDiffAt ℝ ∞ W p := fun p hp => hW.1.contDiffAt (hY.mem_nhds hp)
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w p := fun p hp => hw.contDiffAt (hY.mem_nhds hp)
  have hfd : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p = ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p := by
    intro p hp t
    have hd : DifferentiableAt ℝ W p := (hWat p hp).differentiableAt (by simp)
    exact ((hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)).fderiv
  have hflowc : ∀ z : V × ℝ, z.1 ∈ Y → ContDiffAt ℝ ∞ (fun y : V × ℝ => flow W y.2 y.1) z := by
    intro z hz
    exact contDiffAt_fst.add (contDiffAt_snd.smul ((hWat z.1 hz).comp z contDiffAt_fst))
  have hSo : IsOpen {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    have h := ContinuousOn.isOpen_inter_preimage (f := fun y : V × ℝ => flow W y.2 y.1)
      (s := Prod.fst ⁻¹' Y) (t := Y) ?_ (hY.preimage continuous_fst) hY
    · exact h
    · intro z hz
      exact (hflowc z hz).continuousAt.continuousWithinAt
  have hsm : ContDiffOn ℝ ∞ (fun z : V × ℝ => hk W z.2 w z.1) {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    apply UpperTheory.V.Lit.Dr.altSmooth (V × ℝ) V F q
    intro v
    have hf : ContDiffAt ℝ ∞ (fun y : V × ℝ => w (flow W y.2 y.1)) z := (hwat _ hz.2).comp z (hflowc z hz.1)
    have hu : ∀ i : Fin (q + 1), ContDiffAt ℝ ∞ ((Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) i) z := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (hWat z.1 hz.1).comp z contDiffAt_fst
      · simp only [Fin.cons_succ]
        exact contDiffAt_const.add (contDiffAt_snd.smul
          ((((hWat z.1 hz.1).fderiv_right hinf).comp z contDiffAt_fst).clm_apply contDiffAt_const))
    have h3 := UpperTheory.V.Lit.Dr.applySmooth (V × ℝ) V F (q + 1) (fun y : V × ℝ => w (flow W y.2 y.1))
      (Fin.cons (fun y : V × ℝ => W y.1)
        (fun (j : Fin q) (y : V × ℝ) => v j + y.2 • fderiv ℝ W y.1 (v j)) : Fin (q + 1) → V × ℝ → V) z hf hu
    apply h3.congr_of_eventuallyEq
    have hnb : {y : V × ℝ | y.1 ∈ Y} ∈ 𝓝 z := (hY.preimage continuous_fst).mem_nhds hz.1
    filter_upwards [hnb] with y hy
    simp only [hk, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, hfd y.1 hy y.2]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  have hmaps : ∀ p ∈ Y, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y} :=
    fun p hp t ht => ⟨hp, hW.2 p hp t ht⟩
  refine ⟨hSo, hsm, ?_, ?_⟩
  · intro p hp
    have hc : ContinuousOn ((fun z : V × ℝ => hk W z.2 w z.1) ∘ (fun t : ℝ => (p, t))) (Set.Icc 0 1) :=
      hsm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hmaps p hp t ht)
    simpa [Function.comp_def] using hc
  · have h4 := UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y {z : V × ℝ | z.1 ∈ Y ∧ flow W z.2 z.1 ∈ Y}
      (fun z => hk W z.2 w z.1) hY hSo (fun z hz => hmaps z.1 hz.1 z.2 hz.2) hsm
    exact h4

end UpperTheory.V.Lit.Geo
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDer
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_bound {φ : Sm E a} (h : BddDer φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X : Lie E a) (g : GA E a), ‖(lie E a X φ).1 g‖ ≤ B * ‖X‖ := by
  let b := Module.finBasis ℝ (Lie E a)
  choose c hc using fun k => h (b k) []
  have hc' : ∀ k g, ‖(lie E a (b k) φ).1 g‖ ≤ c k := fun k g => by simpa using hc k g
  have h0 : ∀ k, 0 ≤ c k := fun k => (norm_nonneg _).trans (hc' k 1)
  refine ⟨∑ k, ‖LinearMap.toContinuousLinearMap (b.coord k)‖ * c k,
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (h0 k), fun X g => ?_⟩
  let L : Lie E a →ₗ[ℝ] ℂ :=
    { toFun := fun X => (lie E a X φ).1 g
      map_add' := fun X X' => by rw [map_add (f := _)]; rfl
      map_smul' := fun r X => by rw [map_smul]; rfl }
  have e : L X = ∑ k, b.repr X k • L (b k) := by
    conv_lhs => rw [← b.sum_repr X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  change ‖L X‖ ≤ _
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, mul_right_comm]
  exact mul_le_mul ((LinearMap.toContinuousLinearMap (b.coord k)).le_opNorm X) (hc' k g) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem val_bound {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C)
    (g : GA E a) : ‖hv (Y g)‖ ≤ a * C ^ 2 + 1 := by
  obtain ⟨x, h1, h2, -⟩ := h.root g 1 (by simp)
  have hC : 0 ≤ C := (norm_nonneg _).trans h2
  have hp : (0 : ℝ) ≤ a * C ^ 2 + 1 := by positivity
  have e : (Y g).1 = x.val * star x.val - 1 := by rw [h1, one_smul, add_sub_cancel_left]
  have hx : ∀ i j, ‖x.val i j‖ ≤ C := fun i j =>
    ((norm_le_pi_norm (toL x.val i) j).trans (norm_le_pi_norm (toL x.val) i)).trans h2
  change ‖toL (Y g).1‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j => ?_
  change ‖(Y g).1 i j‖ ≤ _
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) ?_)
  · calc ∑ k, ‖x.val i k * star x.val k j‖ ≤ ∑ _k : Fin a, C ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (norm_mul_le _ _).trans ?_
          rw [Matrix.star_apply, norm_star, sq]
          exact mul_le_mul (hx i k) (hx j k) (norm_nonneg _) hC
      _ = a * C ^ 2 := by simp
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem fieldDer : FieldDer := by
  intro E _ _ _ a U Y C h
  choose φ hφ hb using h.sm
  choose B hB0 hB using fun i j w => lie_bound (hb i j w)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  have hP' : ∀ v : HV E a, LinearMap.toContinuousLinearMap P v.1 = v := fun v => LinearMap.congr_fun hP v
  let B' : Lie E a := fun i j w => (B i j w : ℂ)
  have hle : ∀ i j w, B i j w ≤ ‖B'‖ := fun i j w =>
    calc B i j w ≤ ‖B' i j w‖ := by simpa [B'] using le_abs_self _
      _ ≤ ‖B'‖ := ((norm_le_pi_norm (B' i j) w).trans (norm_le_pi_norm (B' i) j)).trans (norm_le_pi_norm B' i)
  refine ⟨max (a * C ^ 2 + 1) (‖LinearMap.toContinuousLinearMap P‖ * ‖B'‖), le_max_of_le_left (by positivity),
    fun g => ⟨le_max_of_le_left (val_bound h g), fun c X h0 hX => ?_⟩⟩
  let D : Lie E a := fun i j w => (lie E a X (φ i j w)).1 g
  have hD : HasDerivAt (fun t => (hv (Y (g * infGL E a (c t)))).1) D 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w =>
      (hasDerivAt_curve (φ i j w) g c X h0 hX).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => (hφ i j w _).symm)
  have hn : ‖D‖ ≤ ‖B'‖ * ‖X‖ := by
    have hp : 0 ≤ ‖B'‖ * ‖X‖ := by positivity
    exact (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j =>
      (pi_norm_le_iff_of_nonneg hp).2 fun w =>
        (hB i j w X g).trans (mul_le_mul_of_nonneg_right (hle i j w) (norm_nonneg _))
  refine ⟨LinearMap.toContinuousLinearMap P D, ?_, ?_⟩
  · refine ((LinearMap.toContinuousLinearMap P).le_opNorm_of_le hn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact ((LinearMap.toContinuousLinearMap P).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hP' _).symm)

end UpperTheory.V.Lit.Geo
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullMatBd
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem mul_bd (x y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (x * y)‖ ≤ a * (‖toL x‖ * ‖toL y‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖∑ k, x i k * y k j‖ ≤ _
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL x‖ * ‖toL y‖) fun k _ => ?_).trans (by simp))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL x i) k).trans (norm_le_pi_norm (toL x) i)
  · exact (norm_le_pi_norm (toL y k) j).trans (norm_le_pi_norm (toL y) k)

private theorem star_bd (x : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (star x)‖ ≤ ‖toL x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖star (x j i)‖ ≤ _
  rw [norm_star]
  exact (norm_le_pi_norm (toL x j) i).trans (norm_le_pi_norm (toL x) j)

private theorem sand_bd {C : ℝ} (h : GL (Fin a) (Cinf E)) (hC : ‖toL h.val‖ ≤ C) (v : HV E a) :
    ‖sand h v‖ ≤ (a * a * C * C) * ‖v‖ := by
  have h0 : 0 ≤ C := (norm_nonneg _).trans hC
  change ‖toL (h.val * Matrix.of v.1 * star h.val)‖ ≤ _
  have h1 : ‖toL (h.val * Matrix.of v.1)‖ ≤ a * (C * ‖v‖) :=
    (mul_bd _ _).trans (by
      change (a : ℝ) * (‖toL h.val‖ * ‖v‖) ≤ _
      gcongr)
  calc _ ≤ _ := mul_bd _ _
    _ ≤ a * ((a * (C * ‖v‖)) * C) := by
      gcongr
      exact (star_bd _).trans hC
    _ = _ := by ring

private theorem exists_cpt (C : ℝ) : ∃ K : Set (Lie E a), IsCompact K ∧ K ⊆ invSet E a ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → toL h.val ∈ K := by
  have hc : IsClosed {z : Lie E a × Lie E a | toL (Matrix.of z.1 * Matrix.of z.2) = toL 1} := by
    refine isClosed_eq ?_ continuous_const
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous fun z : Lie E a × Lie E a => ∑ k, z.1 i k * z.2 k j
    fun_prop
  refine ⟨Prod.fst '' ((Metric.closedBall 0 C ×ˢ Metric.closedBall 0 C) ∩ _),
    (((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right hc).image continuous_fst, ?_, ?_⟩
  · rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
    have e : Matrix.of z.1 * Matrix.of z.2 = 1 := hz
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse e)
  · intro h h1 h2
    exact ⟨(toL h.val, toL (h⁻¹).val), ⟨⟨mem_closedBall_zero_iff.2 h1, mem_closedBall_zero_iff.2 h2⟩,
      congrArg toL h.mul_inv⟩, rfl⟩

private theorem mat_bd (Ξ : AlgRep E a) (C : ℝ) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ h : GL (Fin a) (Cinf E), ‖toL h.val‖ ≤ C → ‖toL (h⁻¹).val‖ ≤ C → ∀ y, ‖Ξ.mat h *ᵥ y‖ ≤ B * ‖y‖ := by
  obtain ⟨K, hK, hs, hm⟩ := exists_cpt (E := E) (a := a) C
  have hb : ∀ i j, ∃ b : ℝ, ∀ x ∈ K, ‖extGL (fun y => Ξ.mat y i j) x‖ ≤ b := fun i j =>
    hK.exists_bound_of_continuousOn ((matSmooth E a Ξ i j).1.continuousOn.mono hs)
  choose b hb using hb
  have h0 : 0 ≤ ∑ i, ∑ j, |b i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ i, ∑ j, |b i j|, h0, fun h h1 h2 y => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_⟩
  change ‖∑ j, Ξ.mat h i j * y j‖ ≤ _
  calc _ ≤ ∑ j, |b i j| * ‖y‖ := by
        refine norm_sum_le_of_le _ fun j _ => (norm_mul_le _ _).trans
          (mul_le_mul ?_ (norm_le_pi_norm y j) (norm_nonneg _) (abs_nonneg _))
        have := hb i j _ (hm h h1 h2)
        rw [extGL_val] at this
        exact this.trans (le_abs_self _)
    _ = (∑ j, |b i j|) * ‖y‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, |b i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

end

theorem UpperTheory.V.Lit.Geo.matBd :
    MatBd := by
  intro E _ _ _ a Ξ C
  obtain ⟨B, hB, h⟩ := mat_bd Ξ C
  refine ⟨max B (a * a * C * C), le_max_of_le_left hB, fun g h1 h2 => ⟨fun y => (h g h1 h2 y).trans ?_,
    fun v => (sand_bd g h1 v).trans ?_, fun v => (sand_bd g⁻¹ h2 v).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsLie
open UpperTheory.V.Lit.Geo GlobalTheory.CuspRep Filter Topology

theorem UpperTheory.V.Lit.Geo.Pf.csLie :
    UpperTheory.V.Lit.Geo.Pf.CsLie := by
  intro E _ _ _ a φ X ⟨R, hR⟩
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  obtain ⟨h1, -, h3, -⟩ := qhtFacts E a
  obtain ⟨B, hB⟩ := h3 _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image ccont.inv)
  refine ⟨B * R, fun g hg => ?_⟩
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve φ g c X c0 cder
  have hz : (fun t : ℝ => φ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine hR _ (not_le.1 fun hle => ?_)
    have h := hB (g * infGL E a (c t)) _ ⟨t, ht, rfl⟩
    simp only [Pi.inv_apply, mul_inv_cancel_right] at h
    have hp := h1 (g * infGL E a (c t))
    have hg1 := h1 g
    have hB0 : 0 ≤ B := by
      by_contra hn
      nlinarith [not_le.1 hn]
    exact absurd (h.trans (mul_le_mul_of_nonneg_left hle hB0)) (not_le.2 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
noncomputable section

open UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

theorem pbD : PbD := by
  intro V' V F _ _ _ _ _ _ _ _ q H w p hH hw
  have hr : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hinf : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    exact_mod_cast le_top
  refine ⟨?_, extDeriv_pullback (hw.differentiableAt (by simp)) hH hr⟩
  apply altSmooth V' V' F q (pb H w) p
  intro v
  have h1 : ContDiffAt ℝ ∞ (fun y => w (H y)) p := hw.comp p hH
  have h2 : ∀ i, ContDiffAt ℝ ∞ (fun y => fderiv ℝ H y (v i)) p := fun i =>
    (hH.fderiv_right hinf).clm_apply contDiffAt_const
  have h3 := applySmooth V' V F q (fun y => w (H y)) (fun i y => fderiv ℝ H y (v i)) p h1 h2
  simpa [pb, Function.comp_def] using h3

end UpperTheory.V.Lit.Geo
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfChiOne
open UpperTheory.V.Lit.Geo


open NumberField Formalism.L2.Host GroundTheory.Global in
private theorem norm_of_normOne {E : Type} [Field E] [NumberField E] (χ : HChar E) {y : IdeleGroup E}
    (hy : y ∈ IdeleGroup.normOneSubgroup E) : ‖((χ.1 y : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have h := hM _ hk
    have h1 : χ.1 (IdeleGroup.diagonal E k) = 1 := χ.2.2 k
    have h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z :=
      (map_mul χ.1 _ _).trans (by rw [h1, one_mul])
    rwa [h2] at h
  have hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1 := fun z hz => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
    have h3 := hb _ (pow_mem hz n)
    have h4 : χ.1 (z ^ n) = χ.1 z ^ n := map_pow χ.1 z n
    rw [h4, Units.val_pow_eq_pow_val, norm_pow] at h3
    exact (not_le.2 hn) h3
  have h5 := hle _ (inv_mem hy)
  have h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹ := map_inv χ.1 y
  rw [h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))] at h5
  exact le_antisymm (hle _ hy) h5

theorem UpperTheory.V.Lit.Geo.Pf.chiOne :
    UpperTheory.V.Lit.Geo.Pf.ChiOne := by
  intro E _ _ _ a χ s _ g
  exact norm_of_normOne χ g.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldDef
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem sand_comp (g h : GL (Fin a) (Cinf E)) (v : HV E a) : sand g (sand h v) = sand (g * h) v := by
  rw [map_mul]; rfl

private theorem unitary_of_eq {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← sand_comp, ← e, sand_comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

private theorem hv_adHerm (k : Kinf E a) (X : Herm E a) : hv (adHerm k X) = sand (Unitary.toUnits k) (hv X) := rfl

end

theorem UpperTheory.V.Lit.Geo.fieldDef :
    FieldDef := by
  classical
  intro E _ _ _ a U Y C hY
  refine ⟨fun s p => if h : p ∈ cone E a then
    sand h.choose (hv (Y (infGL E a h.choose * finGL E a s.out))) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := unitary_of_eq hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, hu, map_mul (finGL E a), ← mul_assoc, hY.lev _ u.2, ← sand_comp, ← hv_adHerm,
    map_mul (infGL E a), mul_assoc, infGL_comm, ← mul_assoc, hY.cpt]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfInvLie
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

private theorem left_lie (X : Lie E a) (φ : Sm E a) (x : GA E a) (h : ∀ g, φ.1 (x * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (x * g) = (lie E a X φ).1 g := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have h1 := hasDerivAt_curve φ (x * g) c X c0 cder
  have h2 := hasDerivAt_curve φ g c X c0 cder
  simp only [mul_assoc, h] at h1
  exact h1.unique h2

theorem UpperTheory.V.Lit.Geo.Pf.invLie :
    UpperTheory.V.Lit.Geo.Pf.InvLie := by
  intro E _ _ _ a φ h
  exact ⟨⟨ContAut.continuous_of_isOpen_stab E a φ h.level, h.left, h.centre⟩, fun X =>
    ⟨fun γ => left_lie X φ _ (h.left γ), fun t => left_lie X φ _ (h.centre t), level_lie X φ h.level⟩⟩

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfLevInv
open UpperTheory.V.Lit.Geo
open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private def levSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem stab_open {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.levInv :
    UpperTheory.V.Lit.Geo.Pf.LevInv := by
  intro E _ _ _ a ha U hU Ξ r χ h1 hχ q α hα X j
  have hφ : IsLevelFn U Ξ (cmp j (α X)) :=
    mem_tens.1 (span_le_tens (N := levSub U Ξ) (fun φ h => h) (hα.val X)) j
  generalize cmp j (α X) = φ at hφ
  refine ⟨fun γ g => ?_, fun t g => ?_, ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hφ.1]
  · have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
      rw [hχ.2, hφ.2.2 _ h1, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
    rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
    refine stab_open (finRep E a) _ (hU.inter (isOpen_ker_chiDet (a := a) χ)) ⟨U.one_mem, by simp⟩ ?_
    rintro k ⟨hk, h2⟩
    have h1' : rt E a (finGL E a k) φ = φ := hφ.2.1 k hk
    have h2' : chiDet a χ (finGL E a k) = 1 := h2
    change rt E a (finGL E a k) (mulChi a χ φ) = _
    rw [rt_mulChi, h1', h2']
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldSm
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem sub_smooth {f : X → HV E a} {x : X} (h : ContDiffAt ℝ ∞ (fun y => (f y).1) x) :
    ContDiffAt ℝ ∞ f x := by
  obtain ⟨r, hr⟩ := (HV E a).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have e : f = fun y => LinearMap.toContinuousLinearMap r (f y).1 :=
    funext fun y => (LinearMap.congr_fun hr (f y)).symm
  rw [e]
  exact (LinearMap.toContinuousLinearMap r).contDiff.contDiffAt.comp x h

private theorem sand_smooth {σ : X → GL (Fin a) (Cinf E)} {v : X → HV E a} {x : X}
    (h : ∀ i j, ContDiffAt ℝ ∞ (fun y => (σ y).val i j) x) (hv : ∀ i j, ContDiffAt ℝ ∞ (fun y => (v y).1 i j) x) :
    ContDiffAt ℝ ∞ (fun y => sand (σ y) (v y)) x := by
  refine sub_smooth (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_)
  have e : (fun y => (sand (σ y) (v y)).1 i j) =
      fun y => ∑ l, (∑ k, (σ y).val i k * (v y).1 k l) * star ((σ y).val j l) := by
    funext y
    change ((σ y).val * Matrix.of (v y).1 * star (σ y).val) i j = _
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiffAt.sum fun l _ => (ContDiffAt.sum fun k _ => (h i k).mul (hv k l)).mul ?_
  exact (starL' ℝ : Cinf E ≃L[ℝ] Cinf E).contDiff.contDiffAt.comp x (h j l)

end UpperTheory.V.Lit.Geo

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.fieldSm :
    FieldSm := by
  intro E _ _ _ a U Y C hY W hW s p₀ hp₀
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ∞ (fun p => sand (τ p) (hv (Y (infGL E a (τ p) * finGL E a x)))) p₀ := by
    refine sand_smooth (fun i j => contDiffAt_pi.1 (contDiffAt_pi.1 hτ i) j) fun i j => contDiffAt_pi.2 fun w => ?_
    obtain ⟨φ, hφ, -⟩ := hY.sm i j w
    have := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at this
    simp only [infGL_comm]
    exact this
  refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
  have := hW (τ p) x
  rwa [hp] at this
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullRetrFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem retr_left (γ : GL (Fin a) E) (t : ℝ) (g : GA E a) :
    (retractOne (ratGL E a γ * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1 := by
  let y : KernelIndexFullLattice.G1 E a := ⟨ratGL E a γ, Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩⟩
  change (retractOne ((y : GA E a) * splitCentre E a t * g) : KernelIndexFullLattice.G1 E a).1 = _
  rw [mul_assoc, retractOne_coe_mul, retractOne_mul, KernelIndexFullLattice.splitEq_holds E a t, retractOne_centralSection, one_mul]
  rfl

private theorem split_eq (s : {r : ℝ // 0 < r}) :
    splitCentre E a (Real.log s.1 / (a * Module.finrank ℚ E)) = Reduction.centralSection E a s := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [KernelIndexFullLattice.splitEq_holds E a]
  refine congrArg (Reduction.centralSection E a) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log s.2]

private theorem retr_split (g : GA E a) : ∃ t : ℝ, (retractOne g : KernelIndexFullLattice.G1 E a).1 = splitCentre E a t * g :=
  ⟨_, by rw [split_eq (Reduction.detModule E a g)⁻¹, coe_retractOne, ← centralSection_inv_mul_comm, map_inv]⟩

private theorem split_retr (g : GA E a) :
    splitCentre E a (Real.log (Reduction.detModule E a g).1 / (a * Module.finrank ℚ E)) *
      (retractOne g : KernelIndexFullLattice.G1 E a).1 = g := by
  rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, split_eq, coe_retractOne, inv_mul_cancel_right]

private theorem cont_inf : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem compact_box (C : ℝ) :
    IsCompact {h : GL (Fin a) (Cinf E) | ‖toL h.val‖ ≤ C ∧ ‖toL (h⁻¹).val‖ ≤ C} := by
  have hB : IsCompact {x : Matrix (Fin a) (Fin a) (Cinf E) | ‖toL x‖ ≤ C} := by
    have h := isCompact_closedBall (0 : Lie E a) C
    have e : Metric.closedBall (0 : Lie E a) C = {x : Lie E a | ‖x‖ ≤ C} := Set.ext fun _ => mem_closedBall_zero_iff
    rw [e] at h
    exact h
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  refine and_congr Iff.rfl ⟨fun hx => ⟨_, hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, e⟩
  have e' : y = (x⁻¹).val := MulOpposite.op_injective e
  rwa [e'] at hy

end UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.retrFacts :
    RetrFacts := by
  intro E _ _ _ a
  refine ⟨retr_split, retr_left, fun C => ?_⟩
  have hc : Continuous fun h : GL (Fin a) (Cinf E) =>
      Real.log (Reduction.detModule E a (infGL E a h)).1 / (a * Module.finrank ℚ E) :=
    ((continuous_subtype_val.comp (Reduction.continuous_detModule.comp cont_inf)).log
      fun h => (Reduction.detModule E a (infGL E a h)).2.ne').div_const _
  obtain ⟨T, hT⟩ := (compact_box (E := E) (a := a) C).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨T, fun g h h1 h2 => ⟨_, hT h ⟨h1, h2⟩, ?_⟩⟩
  rw [retractOne_mul, Subgroup.coe_mul, ← mul_assoc, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm, mul_assoc, split_retr]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CuspRapid
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem qht_bdd (g : GA E a) :
    BddBelow (Set.range fun γ : GL (Fin a) E => height (K := E) (ratGL E a γ * (retractOne g : KernelIndexFullLattice.G1 E a).1)) :=
  ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩

private theorem qht_nonneg (g : GA E a) : 0 ≤ qht g :=
  le_ciInf fun _ => (height_pos _).le

private theorem decay {φ : Sm E a} (hφ : IsCuspForm φ) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖φ.1 g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  have h0 := KernelIndexFullLattice.brCusp_holds E a φ hφ
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨C, hC⟩ := exists_norm_le_height_pow_neg_siegel h0 hω hωB ht N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E a γ * g.1 ∈ Reduction.normOneGL (K := E) (n := a) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  have h := hC b hb ρ hρ hs kk hkk _ hγx hxe
  rw [h0.1.isLeftInvariant γ g.1] at h
  have hp := height_pos (AdelicGLn.diagonal E a γ * g.1)
  have hq : qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
    have h1 := ciInf_le (qht_bdd (E := E) (a := a) g.1) γ
    rw [retractOne_coe] at h1
    unfold qht
    rw [retractOne_coe]
    exact h1
  rw [le_mul_inv_iff₀ (pow_pos hp N)] at h
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (qht_nonneg _) hq N) (norm_nonneg _)).trans h

private theorem ev_cmp {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) (i : Fin d) :
    ev m g i = (cmp i m).1 g := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Submodule.coe_add]
  | tmul φ v => simp [ev, mul_comm]

private theorem cmp_rTensor {d : ℕ} (T : Module.End ℂ (Sm E a)) (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (i : Fin d) :
    cmp i (T.rTensor _ m) = T (cmp i m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp

private theorem prodA_mem (π : CuspSub E a) (Ξ : AlgRep E a) (l : List (Lie E a)) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ tens Ξ.d π.V) : (l.map (smA Ξ)).prod m ∈ tens Ξ.d π.V := by
  induction l with
  | nil => exact hm
  | cons X l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, mem_tens]
    intro i
    rw [smA_apply, cmp_rTensor]
    exact π.stable (.lie X) _ (mem_tens.1 ih i)

private theorem decay_tens (π : CuspSub E a) {d : ℕ} (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (hm : m ∈ tens d π.V) (N : ℕ) :
    ∃ C : ℝ, ∀ g : KernelIndexFullLattice.G1 E a, ‖ev m g.1‖ * qht (E := E) (a := a) g.1 ^ N ≤ C := by
  choose C hC using fun i => decay (π.cusp _ (mem_tens.1 hm i)) N
  refine ⟨∑ i, C i, fun g => ?_⟩
  have hq : 0 ≤ qht (E := E) (a := a) g.1 ^ N := pow_nonneg (qht_nonneg _) N
  have h1 : ‖ev m g.1‖ ≤ ∑ i, ‖(cmp i m).1 g.1‖ := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_
    rw [ev_cmp]
    exact Finset.single_le_sum (f := fun i => ‖(cmp i m).1 g.1‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  refine (mul_le_mul_of_nonneg_right h1 hq).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hC i g

end

theorem UpperTheory.V.Lit.Geo.cuspRapid :
    CuspRapid := by
  intro E _ _ _ a π Ξ q ω hω l X N
  exact decay_tens π _ (prodA_mem π Ξ l (ω X) (hω X)) N
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.DegreeHermitianFormula
noncomputable section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.Lit.Geo

def OneStep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a)
    (Y : GA E a → Herm E a) (C : ℝ), IsFld U Y C → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : Co Ξ q, IsLev U Ξ η →
      ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧ ∀ (g : GA E a) (M M' : ℝ), 0 ≤ M → 0 ≤ M' →
        (∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + (Y g).1 → Bd η (g * infGL E a h) M) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ h : GL (Fin a) (Cinf E), h.val * star h.val = 1 + t • (Y g).1 →
          Bd (Ξ := Ξ) (dCo (smLie Ξ) η) (g * infGL E a h) M') → Bd η' g (B * (M + M'))

def BdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    ∃ (T : Finset (Fin q → Herm E a)) (B : ℝ), 0 ≤ B ∧ ∀ (α : Co Ξ q) (g : GA E a) (M : ℝ), 0 ≤ M →
      (∀ X ∈ T, ‖ev (α X) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ M) → Bd α g (B * M)

def BdCompact : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q), IsLev U Ξ α → ∀ R : ℝ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ g : GA E a, qht g ≤ R → Bd α g M

def BdGrowth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q),
    (Moderate α → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C * qht g ^ N)) ∧
    (Rapid α → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA E a, Bd α g (C / qht g ^ N))

def Prim : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (f : GA E a → ℝ) (Y : GA E a → Herm E a) (C c f₀ : ℝ),
    IsStep U f Y C c f₀ → ∀ (q : ℕ) (η : Co Ξ q), IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ∃ η' : Co Ξ q, IsLev U Ξ η' ∧ dCo (smLie Ξ) η' = dCo (smLie Ξ) η ∧
        ∀ g : GA E a, f g ≤ n * c → Bd η' g (Real.exp (D * (n + 1)))

def CutBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ) (u : Sm E a) (η ζ : Co Ξ q),
    (∀ (X : Fin (q + 1) → Herm E a) g, ev (dCo (smLie Ξ) ζ X) g = u.1 g • ev (dCo (smLie Ξ) η X) g +
      ∑ i : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ) * (lie E a (toL (X i).1) u).1 g) • ev (η (i.removeNth X)) g) →
    ∀ (g : GA E a) (s b M M' : ℝ), 0 ≤ M → 0 ≤ M' → 0 ≤ b →
      ‖1 - u.1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ s →
      (∀ X, ‖(lie E a X u).1 (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ b * ‖X‖) →
      (b = 0 ∨ Bd η g M) → Bd (Ξ := Ξ) (dCo (smLie Ξ) η) g M' →
      Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (s * M' + (q + 1) * b * M)

def Approx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ U : Subgroup (GL (Fin a) (Af E)),
    IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (q : ℕ) (η : Co Ξ q),
    IsLev U Ξ η → Moderate (Ξ := Ξ) (dCo (smLie Ξ) η) → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, ∃ ζ : Co Ξ q, IsLev U Ξ ζ ∧
      CSupp ζ ∧ CSupp (Ξ := Ξ) (dCo (smLie Ξ) ζ) ∧ ∀ g : GA E a,
        (qht g ≤ R → Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g 0) ∧
        Bd (Ξ := Ξ) (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) g (C * qht g ^ N)

def PtRetr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ (q : ℕ) (α β : Co Ξ q), IsLev U Ξ α → IsLev U Ξ β → ∀ g : GA E a,
      ptIp χ G e α β g = ∑ I : Fin q → Fin n,
        star (ev (α fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1) ⬝ᵥ
          G *ᵥ ev (β fun i => e (I i)) (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1

def PtBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (Ξ : AlgRep E a) (r : ℝ) (χ : HChar E) (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (n : ℕ) (e : Fin n → Herm E a),
    IsData Ξ r χ G e → ∀ q : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ α β : Co Ξ q, IsLev U Ξ α → IsLev U Ξ β → ∀ (g : GA E a) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' → Bd α g M → Bd β g M' → ‖ptIp χ G e α β g‖ ≤ B * M * M'

theorem ptIp_sub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ} (χ : HChar E)
    (G : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) {n : ℕ} (e : Fin n → Herm E a) (α β β' : Co Ξ q) (g : GA E a) :
    ptIp χ G e α (β - β') g = ptIp χ G e α β g - ptIp χ G e α β' g := by
  simp only [ptIp, AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, dotProduct_sub,
    Finset.sum_sub_distrib, mul_sub]

theorem firstGeometricCondition_of_properties (h1 : PairFacts) (h2 : QhtFacts) (h3 : LevD) (h4 : BdGrowth) (h5 : Approx) (h6 : PtBd)
    (h7 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
      IsFiniteMeasure (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)) : G1 := by
  intro E _ _ _ a ha μ _ U hUo hUc Ξ r χ G n e hD q β η hβ hη hR hδ hM
  haveI := h7 E a μ
  obtain ⟨N, C, hC, hA⟩ := h5 E a ha U hUo hUc Ξ q η hη hM
  obtain ⟨C', hC', hB⟩ := (h4 E a Ξ (q + 1) β).2 hR (N + 1)
  obtain ⟨B, hB0, hP⟩ := h6 E a ha U hUo Ξ r χ G n e hD (q + 1)
  have hdη := (h3 E a U Ξ q η hη).1
  have hq := (h2 E a).1
  have key : ∀ R : ℝ, 0 < R → ‖pair μ χ G e β (dCo (smLie Ξ) η)‖ ≤
      B * C' * C * (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ).real Set.univ / R := fun R hR0 => by
    obtain ⟨ζ, hζ, hc, hc', hg⟩ := hA R
    have hdζ := (h3 E a U Ξ q ζ hζ).1
    have hγ := (h3 E a U Ξ (q + 1) _ hdη).2 _ hdζ
    have i1 := (h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).1 β _ hβ hdη hR hM
    have i2 := ((h1 E a ha μ U hUo Ξ r χ G n e hD (q + 1)).2.1 _ β hdζ hβ hc').2
    have z : pair μ χ G e β (dCo (smLie Ξ) ζ) = 0 := by
      rw [(h1 E a ha μ U hUo Ξ r χ G n e hD q).2.2.2 β ζ hβ hζ (Or.inr hc), hδ]
      simp [pair, ptIp]
    have e1 : pair μ χ G e β (dCo (smLie Ξ) η) = pair μ χ G e β (dCo (smLie Ξ) η - dCo (smLie Ξ) ζ) := by
      rw [← sub_zero (pair μ χ G e β (dCo (smLie Ξ) η)), ← z]
      simp only [pair, ptIp_sub]
      exact (integral_sub i1 i2).symm
    rw [e1, mul_div_right_comm]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have q1 := hq x.out
    have q0 : 0 < qht x.out := one_pos.trans_le q1
    by_cases hx : qht x.out ≤ R
    · refine (hP β _ hβ hγ x.out _ 0 (by positivity) le_rfl (hB _) ((hg _).1 hx)).trans ?_
      rw [mul_zero]
      positivity
    · refine (hP β _ hβ hγ x.out _ _ (by positivity) (by positivity) (hB _) (hg _).2).trans ?_
      have e2 : B * (C' / qht x.out ^ (N + 1)) * (C * qht x.out ^ N) = B * C' * C / qht x.out := by
        field_simp
        ring
      rw [e2]
      exact div_le_div_of_nonneg_left (by positivity) hR0 (not_le.1 hx).le
  exact norm_le_zero_iff.1 (ge_of_tendsto (tendsto_const_nhds.div_atTop Filter.tendsto_id)
    ((Filter.eventually_gt_atTop 0).mono key))

end UpperTheory.V.Lit.Geo
end
end
