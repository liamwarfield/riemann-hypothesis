module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_smul_homog (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum,
    MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℂ))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ m ⟨k, y⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem mcPts_smul {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts J) :
    (fun p => c p.1 * z p) ∈ mcPts J := by
  obtain ⟨S0, hS0, rfl⟩ := hJ
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hle : Ideal.span S0 ≤ RingHom.ker ((MvPolynomial.eval (fun p => c p.1 * z p)).comp
        (MvPolynomial.map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS0 s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      rw [eval_smul_homog s a ha c z, hz.2 s (Ideal.subset_span hs), mul_zero]
    have := hle hf
    simpa using this

theorem mem_mcPts_of_sameOrbit {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (hz' : z' ∈ mcPts J) : z ∈ mcPts J := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mcPts_smul hJ c hc hz'

theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p => c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

theorem segre_update [DecidableEq K] (z : (Σ k, ι k) → ℂ) (p : (k : K) → ι k) (k : K) (i : ι k) :
    segre z (Function.update p k i) = z ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, z ⟨l, p l⟩ := by
  unfold segre
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [Finset.ne_of_mem_erase hl]

theorem sameOrbit_of_segre {z z' : (Σ k, ι k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (μ : ℂ)
    (hμ : μ ≠ 0) (h : segre z = μ • segre z') : SameOrbit z z' := by
  classical
  choose p0 hp0 using hz'
  have hz0 : ∀ k, z ⟨k, p0 k⟩ ≠ 0 := by
    have hs : segre z p0 ≠ 0 := by
      rw [h, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ (Finset.prod_ne_zero_iff.mpr fun k _ => hp0 k)
    intro k hk
    exact hs (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hR : ∀ k, ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hz0 l
  have hR' : ∀ k, ∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hp0 l
  refine ⟨fun k => μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩,
    fun k => div_ne_zero (mul_ne_zero hμ (hR' k)) (hR k), ?_⟩
  funext q
  obtain ⟨k, i⟩ := q
  have e := congrFun h (Function.update p0 k i)
  rw [Pi.smul_apply, smul_eq_mul, segre_update, segre_update] at e
  show z ⟨k, i⟩ = μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / (∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩) * z' ⟨k, i⟩
  field_simp [hR k]
  linear_combination e

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem analyticAt_coord {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : AnalyticAt ℂ γ y) (p : Σ k, ι k) : AnalyticAt ℂ (fun y' => γ y' p) y :=
  analyticAt_pi_iff.mp h p

theorem pot_contDiffAt {L : HermLine ι} (hL : IsSmoothHerm L) {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y := by
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hL.contDiffAt (isOpen_blockNonzero.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγr : ContDiffAt ℝ 2 γ y := (hγ.contDiffAt (n := 2)).restrict_scalars ℝ
  exact (hh.comp y hγr).log (L.pos _ hy).ne'

theorem density_eq {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {A : HermLine ι}
    {s : MRing ι} {P : Ideal (MRing ι)} (hs : IsSectionOn P A s)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
      logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y := by
  obtain ⟨a, ha, hsm, -⟩ := hs
  have hy0 := hy
  choose i0 hi0 using hy0
  obtain ⟨c, hc⟩ : ∃ c : (Fin e → ℂ) → K → ℂ,
      ∀ y' k, c y' k = γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := ⟨_, fun _ _ => rfl⟩
  have hnz : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 y, (∀ k, γ y' ⟨k, i0 k⟩ ≠ 0) ∧ (∀ k, c y' k ≠ 0) ∧
      γ' y' = bsmul (c y') (γ y') := by
    filter_upwards [hnz, hseg] with y' h0 hs'
    obtain ⟨h1, h2⟩ := eq_bsmul_of_segre_eq i0 h0 hs'
    have hcy : c y' = fun k => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := funext (hc y')
    refine ⟨h0, fun k => ?_, by rw [hcy]; exact h2⟩
    rw [hc]
    exact div_ne_zero (h1 k) (h0 k)
  obtain ⟨-, hc0, hyrel⟩ := hrel.self_of_nhds
  have hlog : logNorm A s (γ' y) = logNorm A s (γ y) := by
    rw [hyrel]
    exact logNorm_bsmul A ha hsm hc0 _
  rw [hlog]
  congr 1
  have hj : ∀ j, cxHessian (fun y' => pot L j (γ' y')) y = cxHessian (fun y' => pot L j (γ y')) y := by
    intro j
    have hcan : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := by
      intro k
      have hfun : (fun y' => c y' k) = fun y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ :=
        funext fun y' => hc y' k
      rw [hfun]
      exact (analyticAt_coord hγ' _).div (analyticAt_coord hγ _) (hi0 k)
    have hG : AnalyticAt ℂ
        (fun y' => ∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
      have hk : ∀ k, AnalyticAt ℂ
          (fun y' => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
        intro k
        refine analyticAt_const.mul (((hcan k).div analyticAt_const (hc0 k)).clog ?_)
        show c y k / c y k ∈ Complex.slitPlane
        rw [div_self (hc0 k)]
        exact Complex.one_mem_slitPlane
      have h := Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun (k : K) (y' : Fin e → ℂ) => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k))
        (c := y) Finset.univ (fun k _ => hk k)
      convert h using 1
      funext y'
      rw [Finset.sum_apply]
    have hev : (fun y' => pot L j (γ' y')) =ᶠ[𝓝 y] fun y' => pot L j (γ y') +
        (∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)).re +
        ∑ k, ((L j).a k : ℝ) * Real.log ‖c y k‖ := by
      filter_upwards [hrel] with y' hy'
      obtain ⟨h0, hck, h2⟩ := hy'
      have hpos : 0 < (L j).h (γ y') := (L j).pos _ fun k => ⟨i0 k, h0 k⟩
      have hne : ∀ k ∈ Finset.univ, ‖c y' k‖ ^ (L j).a k ≠ 0 :=
        fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hck k))
      have key : ∀ k, Real.log (‖c y' k‖ / ‖c y k‖) = Real.log ‖c y' k‖ - Real.log ‖c y k‖ :=
        fun k => Real.log_div (norm_ne_zero_iff.mpr (hck k)) (norm_ne_zero_iff.mpr (hc0 k))
      have hb : (L j).h (bsmul (c y') (γ y')) = (∏ k, ‖c y' k‖ ^ (L j).a k) * (L j).h (γ y') :=
        (L j).smul _ _ hck
      simp only [pot]
      rw [h2, hb, Real.log_mul (Finset.prod_ne_zero_iff.mpr hne) hpos.ne',
        Real.log_prod hne]
      simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re, norm_div, key,
        Real.log_zpow, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [cxHessian_congr hev]
    exact cxHessian_add_re _ (pot_contDiffAt (hL j) hγ hy) hG
  simp only [maDensity, hj]

theorem sheet_analyticAt (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := _root_.mem_nhds_iff.mp (h.2.mono fun _ h' => h'.1)
  rw [analyticAt_pi_iff]
  intro p
  exact hA e U _ hUo (fun y' hy' => (differentiableAt_pi.mp (hU hy') p).differentiableWithinAt) y hyU

theorem sheetIndep_of (hA : OsgoodStatement) (hfib : FibreFiniteStatement) : SheetIndepStatement := by
  intro K _ ι _ P e Ψ L A s hvar hgood hL _ hs
  have hbad := badSet_null hA (hfib K ι P e Ψ hvar hgood)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with y hy w γ γ' h h'
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y') := by
    by_contra hne
    exact hy ⟨w, γ, γ', h, h', hne⟩
  exact density_eq hL hs (sheet_analyticAt hA h) (sheet_analyticAt hA h') h.2.self_of_nhds.2.1.1 hseg

theorem sheetIndep : SheetIndepStatement := sheetIndep_of osgood fibreFinite

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def HermLine.inv (B : HermLine ι) : HermLine ι where
  a := -B.a
  h z := (B.h z)⁻¹
  pos z hz := inv_pos.mpr (B.pos z hz)
  smul c z hc := by
    rw [B.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, zpow_neg]

theorem logNorm_inv_one (B : HermLine ι) (z : (Σ k, ι k) → ℂ) :
    logNorm B.inv 1 z = Real.log (B.h z) := by
  simp [logNorm, HermLine.inv]

theorem isSmoothHerm_inv {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm B.inv := (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} from hB).inv
  fun z hz => (B.pos z hz).ne'

theorem isSectionOn_inv_one {P : Ideal (MRing ι)} (hP : P.IsPrime) {B : HermLine ι}
    (hB : B.a = 0) : IsSectionOn P B.inv 1 := by
  classical
  refine ⟨0, fun k => ?_, ?_, ?_⟩
  · simp [HermLine.inv, hB]
  · intro m hm k
    have hm0 : m = 0 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    subst hm0
    simp
  · intro h
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 h)

theorem h_eq_of_sameOrbit {B : HermLine ι} (hB : B.a = 0) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : B.h z = B.h z' := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [B.smul c z' hc, hB]
  simp

theorem maDens_congr {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) : ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ i, ReciprocityTheory.AnForm.hessC (φ i) z = ReciprocityTheory.AnForm.hessC (ψ i) z := by
    intro i
    have h2 : fderiv ℝ (fderiv ℝ (φ i)) z = fderiv ℝ (fderiv ℝ (ψ i)) z :=
      ((h i).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  simp only [ReciprocityTheory.AnForm.maDens, hH]

theorem mInt_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Φ' : Fin e → LocPot X} {g g' : X → ℝ}
    (hΦ : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Φ' j y)
    (hg : ∀ x, g x = g' x) : mInt A Φ g = mInt A Φ' g' := by
  unfold ReciprocityTheory.AnForm.M.mInt
  by_cases h : Nonempty (ChartPartition A)
  · rw [dite_eq_left h, dite_eq_left h]
    unfold ReciprocityTheory.AnForm.M.integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [hg, hΦ j y hy]
  · rw [dite_eq_right h, dite_eq_right h]

theorem locDens_cons_congr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas (e + 1) X)
    {Q Q' : LocPot X} (Φ : Fin e → LocPot X)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (fun y' => Q.φ ((A.chart j).symm y) ((A.chart j).symm y'))
      =ᶠ[𝓝 y] fun y' => Q'.φ ((A.chart j).symm y) ((A.chart j).symm y')) :
    ∀ j, ∀ y ∈ (A.chart j).target,
      locDens A (Fin.cons Q Φ) j y = locDens A (Fin.cons Q' Φ) j y := by
  intro j y hy
  unfold ReciprocityTheory.AnForm.M.locDens
  apply maDens_congr
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact h j y hy
  | succ i =>
    simp only [Fin.cons_succ]
    exact Filter.EventuallyEq.rfl

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem contDiffOn_lift (R : AnLogRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hopen : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  rw [contDiffOn_pi]
  intro p
  exact ((R.holo x p j).contDiffOn hopen.uniqueDiffOn).restrict_scalars ℝ

theorem contDiffOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hl := contDiffOn_lift R x j
  have hmaps : Set.MapsTo (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun y hy => (R.mem x _ hy.2).1
  have hL' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hL
  exact (hL'.comp hl hmaps).log fun y hy => (L.pos _ (hmaps hy)).ne'

theorem smoothOn_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := fun j => contDiffOn_potOf R hL x j

theorem smooth_diag (R : AnLogRes P J e) {B : HermLine ι} (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    R.A.Smooth (fun x => Real.log (B.h (R.lift x x))) := by
  intro j
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  have hyt : y ∈ (R.A.chart j).target := hy.1
  refine ⟨(R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U ((R.A.chart j).symm y),
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U _), ⟨hyt, R.mem_U _⟩, ?_⟩
  have hc := contDiffOn_potOf R hB ((R.A.chart j).symm y) j
  refine (hc.mono Set.inter_subset_right).congr fun y' hy' => ?_
  change Real.log (B.h (R.lift ((R.A.chart j).symm y') ((R.A.chart j).symm y'))) =
    Real.log (B.h (R.lift ((R.A.chart j).symm y) ((R.A.chart j).symm y')))
  rw [h_eq_of_sameOrbit hB0 (R.compat _ _ _ ⟨R.mem_U _, hy'.2.2⟩)]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M OnePoint Filter Topology MeasureTheory

namespace ProjectiveLineResolution


end ProjectiveLineResolution

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def pC (P : Ideal (MRing ι)) : Ideal (MRingOver ℂ ι) :=
  Ideal.span (map (Int.castRingHom ℂ) '' (P : Set (MRing ι)))

theorem mcPts_eq_pC (P : Ideal (MRing ι)) :
    mcPts P = {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ pC P, eval z f = 0} := by
  ext z
  simp only [mcPts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun f hf => ?_⟩
    have hle : pC P ≤ RingHom.ker (MvPolynomial.eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact h2 g hg)
    exact RingHom.mem_ker.1 (hle hf)
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun f hf => h2 _ (Ideal.subset_span ⟨f, hf, rfl⟩)⟩

def PCRadicalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → (pC P).IsRadical

def PCEquidimStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes,
      ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

def PCContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P

def PCMinContractStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∀ Q ∈ (pC P).minimalPrimes, Q.comap (map (Int.castRingHom ℂ)) = P

def jacMinors {s : ℕ} (G : Fin s → MRing ι) (c : ℕ) : Set (MRing ι) :=
  {d | ∃ (a : Fin c → Fin s) (b : Fin c → Σ k, ι k),
    d = Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))}

def JacNotInPStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∃ (s : ℕ) (G : Fin s → MRing ι), (∀ i, ∃ a, IsMultiHomog (G i) a) ∧
      Ideal.span (Set.range G) = P ∧
      ¬ Ideal.span (jacMinors G (Fintype.card (Σ k, ι k) - (e + Fintype.card K))) ≤ P

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
