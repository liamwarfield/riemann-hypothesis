module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SphereMeanSubstitutedEqIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightDecompositionLocalTerms
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteLocalHeightTerm
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ArchimedeanLocalHeightTerm
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem archimedean_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ) (sg : K →+* ℂ) :
    d.localHeightAtEmbedding (d.wx x) c sg =
      blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg F) -
        blockSphereMean (d.D + 1) (d.N + 1) (MvPolynomial.map sg (d.translatedForm x F)) +
        Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0)
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hmi := MvPolynomial.map_injective (σ := TVar d.D d.N) sg sg.injective
  have hFc0 : MvPolynomial.map sg F' ≠ 0 := (map_ne_zero_iff _ hmi).2 hFne
  have ha1c : MvPolynomial.map sg a1' ≠ 0 :=
    (map_ne_zero_iff _ hmi).2 (mul_ne_zero (by simpa using hκ3) ha10)
  have hb1c : MvPolynomial.map sg b1 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb10
  have ha2c : MvPolynomial.map sg a2 ≠ 0 := (map_ne_zero_iff _ hmi).2 ha20
  have hb2c : MvPolynomial.map sg b2 ≠ 0 := (map_ne_zero_iff _ hmi).2 hb20
  have hFcmh := isMultiHomogeneous_map_ring _ F' hFmh sg
  obtain ⟨αa1, hαa10, hαa1⟩ := hintMH_map (hintMH_C_mul κ3 ha1) sg
  obtain ⟨αb1, hαb10, hαb1⟩ := hintMH_map hb1 sg
  obtain ⟨αa2, hαa20, hαa2⟩ := hintMH_map ha2 sg
  obtain ⟨αb2, hαb20, hαb2⟩ := hintMH_map hb2 sg
  have I1 := hint_fubini hn hFc0 hFcmh
  have Ia1 := hint_logInt_tail hn ha1c hαa1 hαa10 0
  have Ib1 := hint_logInt_tail hn hb1c hαb1 hαb10 0
  have Ia2 := hint_logInt_tail hn ha2c hαa2 hαa20 0
  have Ib2 := hint_logInt_tail hn hb2c hαb2 hαb20 0
  have hind : ∀ (z : BlockSphere d.D (d.N + 1))
      (q : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ) (α : Fin (d.D + 1) → ℕ),
      α 0 = 0 → IsMultiHomogeneous α q → ∀ t0 : Fin (d.N + 1) → ℂ,
      MvPolynomial.eval (hintPt t0 z) q = MvPolynomial.eval (hintPt 0 z) q := by
    intro z q α h0 hq t0
    refine hint_eval_indep hq h0 _ _ ?_
    rintro ⟨i, j⟩ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
    rfl

  have hpt : ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)),
      (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
        -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P)) =
        (∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
            ∂(sphereProb (d.N + 1))) -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ +
          Real.log ‖sg κ‖ + d.delc c * (harmonic d.N : ℝ) / 2 ∧
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
    filter_upwards [d.norm_at_sg_B hd h c sg, hint_ae_tail hn hb1c hαb1 hαb10 0,
      hint_ae_tail hn hb2c hαb2 hαb20 0, hint_ae_tail hn ha2c hαa2 hαa20 0] with z hz hb1z hb2z ha2z
    beta_reduce at hz
    obtain ⟨hfin, hcard, hcl1, hcl2⟩ := hz
    set S := d.ST c sg (d.tOf z) with hS
    have hpe := congrArg (fun q => MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg q)) hpoly
    simp only [map_mul, MvPolynomial.map_C, MvPolynomial.eval_C] at hpe

    have hb1z' : d.evT sg 0 (d.tOf z) b1 ≠ 0 := by rw [hint_evT_eq]; exact hb1z
    have hprod1 := hcl1 ra a1' b1 0 hra0 hb10 hkey1 hb1z'
    have hPra : ∀ P ∈ S, P ra ≠ 0 := fun P _ => (map_ne_zero_iff P P.injective).2 hra0
    have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), P ra) ≠ 0 := by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      exact Finset.prod_ne_zero_iff.2 fun P hP => hPra P (hfin.mem_toFinset.1 hP)
    have ha1z : d.evT sg 0 (d.tOf z) a1' ≠ 0 := by
      intro h0; rw [h0, zero_div] at hprod1; exact hprod0 hprod1.symm
    rw [hint_evT_eq, hint_evT_eq] at hprod1
    rw [hint_evT_eq] at ha1z
    have hsum1 : ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [hint_log_finprod _ hfin _ hPra, ← hprod1, norm_div,
        Real.log_div (norm_ne_zero_iff.2 ha1z) (norm_ne_zero_iff.2 hb1z)]

    have hsk : sg κ ≠ 0 := (map_ne_zero sg).2 hκ
    have hlhs0 : sg κ * MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1') *
        MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hsk ha1z) ha2z
    rw [hpe] at hlhs0
    have hFXz : MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F')) ≠ 0 := by
      intro h0; apply hlhs0; rw [h0]; ring
    have hlogFX : Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖ =
        Real.log ‖sg κ‖ + Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ +
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      have hl := congrArg (fun w : ℂ => Real.log ‖w‖) hpe
      simp only [norm_mul] at hl
      rw [Real.log_mul (by positivity) (norm_ne_zero_iff.2 ha2z),
        Real.log_mul (norm_ne_zero_iff.2 hsk) (norm_ne_zero_iff.2 ha1z),
        Real.log_mul (by positivity) (norm_ne_zero_iff.2 hb1z),
        Real.log_mul (norm_ne_zero_iff.2 hFXz) (norm_ne_zero_iff.2 hb2z)] at hl
      linarith
    refine ⟨?_, hlogFX⟩

    have hlin : ∀ᵐ s ∂(sphereProb (d.N + 1)), ∀ P ∈ S,
        ∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j ≠ 0 :=
      (Filter.eventually_all_finite hfin).2 fun P _ => hint_lin_ae _ (d.hint_U_coord_ne hd c P)
    have hptU : ∀ᵐ s ∂(sphereProb (d.N + 1)),
        Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖ =
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
            Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
            ∑ P ∈ hfin.toFinset,
              Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
      filter_upwards [hlin] with s hs
      have haz' : d.evT sg (spherePoint s) (d.tOf z) a2 ≠ 0 := by
        rw [hint_evT_eq, hind z _ _ hαa20 hαa2]; exact ha2z
      have hq := hcl2 (F' * b2) a2 (spherePoint s) ha20 hkey2 haz'
      rw [hint_evT_eq, hint_evT_eq, map_mul, map_mul, hind z _ _ hαa20 hαa2,
        hind z (MvPolynomial.map sg b2) _ hαb20 hαb2] at hq
      have hL : ∀ P ∈ S, (∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        intro P hP
        have := hs P hP
        simpa [hintU, mul_comm] using this
      have hprod0' : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
          ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
        rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
        exact Finset.prod_ne_zero_iff.2 fun P hP => hL P (hfin.mem_toFinset.1 hP)
      have heq : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F') =
          MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2) *
            (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
              ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) /
            MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2) := by
        rw [← hq]; field_simp
      rw [heq, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero ha2z hprod0')
        (norm_ne_zero_iff.2 hb2z), Real.log_mul (norm_ne_zero_iff.2 ha2z)
        (norm_ne_zero_iff.2 hprod0'), ← hint_log_finprod _ hfin _ hL,
        finsum_mem_eq_finite_toFinset_sum _ hfin]
      have : ∀ P ∈ hfin.toFinset, Real.log ‖∑ j, spherePoint s j *
          P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ =
          Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
        intro P _; simp [hintU, mul_comm]
      rw [Finset.sum_congr rfl this]; ring
    have hInt : ∀ P ∈ hfin.toFinset, Integrable (fun s : UnitSphereC (d.N + 1) =>
        Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖) (sphereProb (d.N + 1)) :=
      fun P _ => (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
        (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).1
    have hval : ∀ P ∈ hfin.toFinset, ∫ s, Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j *
        spherePoint s j‖ ∂(sphereProb (d.N + 1)) = Real.log ‖d.hintU c P‖ - (harmonic d.N : ℝ) / 2 := by
      intro P _
      have := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
        (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).2
      simpa using this
    have hintS : ∫ s, Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F')‖
        ∂(sphereProb (d.N + 1)) =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a2)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b2)‖ +
          ∑ P ∈ hfin.toFinset, Real.log ‖d.hintU c P‖ - d.delc c * (harmonic d.N : ℝ) / 2 := by
      rw [integral_congr_ae hptU, integral_add (integrable_const _) (integrable_finsetSum _ hInt),
        integral_const, integral_finsetSum _ hInt, Finset.sum_congr rfl hval, Finset.sum_sub_distrib,
        Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, hcard]
      simp only [probReal_univ, one_smul, nsmul_eq_mul]
      ring

    have hPe : ∀ P : Ω c →+* ℂ, -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) =
        Real.log ‖d.hintU c P‖ - Real.log ‖P ra‖ := by
      intro P
      have hw := d.eq_ratio_base_smul hd c hmem
      have hn1 : d.nrm c d.wL (d.wx x c) P = ‖P ra‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
        conv_lhs => rw [hw]
        exact hd.nrm_smul c P _ (hd.w_mem _ c) (hd.w_base c) hra0
      have hpos := hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)
      have hU := d.hint_one_le_U hd c P
      rw [hn1, d.hint_be_eq hd c P, mul_comm ‖P ra‖, mul_div_mul_left _ _ hpos.ne',
        Real.log_div (norm_ne_zero_iff.2 ((map_ne_zero P).2 hra0)) (by linarith)]
      ring
    change ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S), -Real.log (d.nrm c d.wL (d.wx x c) P / d.be c P) = _
    have hsum1' : ∑ P ∈ hfin.toFinset, Real.log ‖P ra‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a1')‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b1)‖ := by
      rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]; exact hsum1
    rw [finsum_mem_congr rfl fun P _ => hPe P, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.sum_sub_distrib, hsum1', hintS, hlogFX]
    ring

  have IFX : Integrable (fun z : BlockSphere d.D (d.N + 1) =>
      Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg (d.translatedForm x F'))‖)
      (blockSphereProb d.D (d.N + 1)) := by
    refine (((((integrable_const (Real.log ‖sg κ‖)).add Ia1).add Ia2).sub Ib2).sub Ib1).congr ?_
    filter_upwards [hpt] with z hz
    rw [hz.2]; rfl
  unfold localHeightAtEmbedding
  rw [integral_congr_ae (hpt.mono fun z hz => hz.1)]
  rw [integral_add ?_ (integrable_const _), integral_add ?_ (integrable_const _),
    integral_sub I1 IFX, integral_const, integral_const, d.sphereMean_fubini hFc0 hFcmh, d.sphereMean_substituted_eq_integral]
  · simp only [probReal_univ, one_smul]
  · exact I1.sub IFX
  · exact (I1.sub IFX).add (integrable_const _)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem finite_local_height_term (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N) (κ : K) (hκ : κ ≠ 0)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (hFne : F ≠ 0) (hFx : d.translatedForm x F ≠ 0) (hs : d.heightSubstitutionCondition h x c F κ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    d.localHeightAtPrime h (d.wx x) c la * logNorm la =
      Real.log (gaussAbs (FinitePlace.mk la) F) -
        Real.log (gaussAbs (FinitePlace.mk la) (d.translatedForm x F)) +
        Real.log (FinitePlace.mk la κ) := by
  let : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  set ra := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with hra
  have hmem := d.linearCombination_mem_section hd x c
  have hra0 : ra ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)

  obtain ⟨κ3, hκ3, hN⟩ := (d.norm_factorization hd h).1 c ra hra0
  obtain ⟨a1, b1, ha1, hb1, hsplit1⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit1] at hN
  have hraS : algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hra0
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hraS).map (Algebra.norm (KTf K d.D d.N))).ne_zero
  have hb10 : b1 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha10 : a1 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a1' : KTp K d.D d.N := MvPolynomial.C κ3 * a1 with ha1'
  have hkey1 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a1' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb10
    rw [hN, ha1', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp

  obtain ⟨F', hF', hF'0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  have hFF : F' = F := hinj (hF'.trans hF.symm)
  subst hFF
  obtain ⟨a2, b2, ha2, hb2, hsplit2⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2) := by
    rw [hF, ← hsplit2]; rfl
  have hb20 : b2 ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have ha20 : a2 ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hFne (hinj hfZ)
  have hkey2 : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2 =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F' * b2) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b2 ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb20
    rw [map_mul, hfZ]
    field_simp

  have hpoly : MvPolynomial.C κ * a1' * a2 = d.translatedForm x F' * b2 * b1 := by
    apply mul_left_cancel₀ hFne
    apply hinj
    have hs' := hs
    unfold heightSubstitutionCondition at hs'
    rw [map_mul] at hkey2
    have hCk : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) =
        algebraMap K (KTf K d.D d.N) κ := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    simp only [map_mul, hCk]
    linear_combination (-(algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F' *
        algebraMap K (KTf K d.D d.N) κ * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2)) * hkey1 +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1 *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a2) * hs' +
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.translatedForm x F') *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b1) * hkey2

  have hfin := (d.places_over_la hd h la c).1
  have hZ : ∀ w ∈ d.PlOver la c, d.ordMM c (d.Wres c w) (d.wx x c) =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra)).untopD 0 - (w (d.rationalBaseRow c)).untopD 0 := by
    intro w hw
    obtain ⟨hv, -, j0, hj0, hint, hunit⟩ := d.admissible_over_prime hd h la c w hw
    exact d.ordMinMax_at_good_place hd c w hv j0 hj0 hint hunit hmem (hx c)
  have hNla : d.localHeightAtPrime h (d.wx x) c la =
      (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) ra) : ℝ) - (d.nLa h c la (d.rationalBaseRow c) : ℝ) := by
    unfold localHeightAtPrime nLa
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hZ w (hfin.mem_toFinset.1 hw)]; push_cast; ring

  have ha1'0 : a1' ≠ 0 := mul_ne_zero (by simpa using hκ3) ha10
  have hw0 : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  have p1 := d.pf_fin hd h c _ hraS a1' b1 ha1'0 hb10 hkey1 la
  have p2 := d.pf_fin hd h c _ hw0 (F' * b2) a2 (mul_ne_zero hFne hb20) ha20 hkey2 la

  set v := FinitePlace.mk la with hv
  have hg := congrArg (gaussAbs v) hpoly
  rw [gauss_abs_mul v _ _ (mul_ne_zero (by simpa using hκ) ha1'0) ha20,
    gauss_abs_mul v _ _ (by simpa using hκ) ha1'0, HeightMultiplicativity.gaussAbs_C,
    gauss_abs_mul v _ _ (mul_ne_zero hFx hb20) hb10,
    gauss_abs_mul v _ _ hFx hb20] at hg
  have hl := congrArg Real.log hg
  have hk0 : 0 < v κ := (FinitePlace.pos_iff).2 hκ
  have q1 := gauss_abs_pos_of_ne_zero v a1' ha1'0
  have q2 := gauss_abs_pos_of_ne_zero v a2 ha20
  have q3 := gauss_abs_pos_of_ne_zero v _ hFx
  have q4 := gauss_abs_pos_of_ne_zero v b2 hb20
  have q5 := gauss_abs_pos_of_ne_zero v b1 hb10
  have q6 := gauss_abs_pos_of_ne_zero v F' hFne
  rw [Real.log_mul (by positivity) q2.ne', Real.log_mul hk0.ne' q1.ne',
    Real.log_mul (by positivity) q5.ne', Real.log_mul q3.ne' q4.ne'] at hl
  rw [gauss_abs_mul v _ _ hFne hb20, Real.log_mul q6.ne' q4.ne'] at p2
  rw [hNla]
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem finsum_finset_sum_comm' {α β : Type*} (s : Finset β) (f : β → α → ℝ)
    (hf : ∀ b ∈ s, (Function.support (f b)).Finite) :
    ∑ᶠ a, ∑ b ∈ s, f b a = ∑ b ∈ s, ∑ᶠ a, f b a := by
  first
    | exact finsum_sum_comm s (fun a b => f b a) hf
    | (classical
       induction s using Finset.induction_on with
       | empty => simp
       | insert b s hb ih =>
         simp only [Finset.sum_insert hb]
         rw [finsum_add_distrib (hf b (Finset.mem_insert_self b s))
           ((s.finite_toSet.biUnion fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')).subset
             (Function.support_finset_sum)), ih fun b' hb' => hf b' (Finset.mem_insert_of_mem hb')])

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem height_decomposition_local_terms (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    (Function.support fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la).Finite ∧
    (∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.localHeightAtEmbedding (d.wx x) c) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 F + d.delc c * (harmonic d.N : ℝ) / 2 := by
  obtain ⟨hFne, hFx⟩ := d.fZ_and_substituted_ne_zero hd h x hx c F hF
  obtain ⟨κ, hκ, hs⟩ := d.substituted_factorization_exists hd h x hx c F hF
  have hfin := d.finite_local_height_term hd h x hx c F κ hκ hF hFne hFx hs
  have harch := d.archimedean_local_height_term hd h x hx c F κ hκ hF hFne hs
  rw [(d.height_substituted_eq_finsum hd h x hx c F hF).2]
  set G : FinitePlace K → ℝ := fun v => Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v F) -
    Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (d.translatedForm x F)) + Real.log (v κ) with hG
  have hg : (fun la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) =
      fun la => G (FinitePlace.equivHeightOneSpectrum.symm la) := by
    funext la; rw [hfin la]; rfl
  have s1 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite F hFne
  have s2 := ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hFx
  have s3 : (Function.support fun v : FinitePlace K => Real.log (v κ)).Finite := by
    refine (FinitePlace.hasFiniteMulSupport hκ).subset fun v hv => ?_
    intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
  have sG : (Function.support G).Finite := ((s1.union s2).union s3).subset (by
    intro v hv; by_contra hn; apply hv
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    simp only [hG, hn.1.1, hn.1.2, hn.2]; ring)
  have hsumG : ∑ᶠ la, d.localHeightAtPrime h (d.wx x) c la * logNorm la = ∑ᶠ v, G v := by
    rw [hg]; exact finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
  refine ⟨?_, ?_⟩
  · rw [hg]
    exact (sG.image FinitePlace.equivHeightOneSpectrum).subset (by
      intro la hla; exact ⟨FinitePlace.equivHeightOneSpectrum.symm la, hla, by simp⟩)
  rw [hsumG, hG, finsum_add_distrib ((s1.union s2).subset (Function.support_sub _ _)) s3,
    finsum_sub_distrib s1 s2]
  have hpf : (∑ᶠ v : FinitePlace K, Real.log (v κ)) + ∑ σ : K →+* ℂ, Real.log ‖σ κ‖ = 0 := by
    classical
    have hm := FinitePlace.hasFiniteMulSupport hκ
    set U := hm.toFinset
    have hsub1 : Function.mulSupport (fun v : FinitePlace K => v κ) ⊆ U := by
      intro v hv; exact hm.mem_toFinset.mpr hv
    have hsub2 : Function.support (fun v : FinitePlace K => Real.log (v κ)) ⊆ U := by
      intro v hv; apply hsub1; intro h1; apply hv; simp only; rw [show v κ = 1 from h1, Real.log_one]
    have hprod := FinitePlace.prod_eq_inv_abs_norm hκ
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub1] at hprod
    rw [finsum_eq_sum_of_support_subset _ hsub2, ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq κ hκ,
      ← Real.log_prod fun v _ => (FinitePlace.pos_iff.mpr hκ).ne', hprod]
    push_cast
    rw [Real.log_inv]; ring
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    rw [NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold meanK ReciprocityTheory.MultiplicativeHeights.h0
  simp_rw [harch]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp
  linarith [hpf]

theorem height_minMax_eq_sum_heights (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 := by
  have hc := fun c => d.height_decomposition_local_terms hd h hI2be x hx c (F c) (hF c)
  have hla : ∀ la, d.NlaMM h (d.wx x) la * logNorm la = ∑ c, d.localHeightAtPrime h (d.wx x) c la * logNorm la := by
    intro la
    simp only [NlaMM, localHeightAtPrime, Finset.sum_mul]
  have hsg : d.NsgMM (d.wx x) = fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg := by
    funext sg
    rfl
  have hmean : meanK (fun sg => ∑ c, d.localHeightAtEmbedding (d.wx x) c sg) = ∑ c, meanK (d.localHeightAtEmbedding (d.wx x) c) := by
    simp only [meanK, Finset.sum_div]
    rw [Finset.sum_comm]
  unfold HgtMM mahlerMeasureHeight
  simp only [hla]
  rw [finsum_finset_sum_comm' Finset.univ (fun c la => d.localHeightAtPrime h (d.wx x) c la * logNorm la) (fun c _ => (hc c).1)]
  rw [hsg, hmean, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun c _ => (hc c).2, Finset.sum_add_distrib]
  simp only [del, Nat.cast_sum, Finset.sum_mul, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem HeightMinMaxFormula (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) :
    d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2 :=
  d.height_minMax_eq_sum_heights hd h hI2be x hx F hF

end Data

end ReciprocityTheory.ChartRestriction.G.T0
