module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace LelongRegularise

theorem mdisc_eq_zero_of_eq_zero {D : ℕ} (B : Fin (D + 1) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
    (h : B 0 = 0) : ReciprocityTheory.AnForm.mdisc B = 0 := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  refine mul_eq_zero_of_right _ ?_
  have hu : (Finset.univ : Finset (Fin (D + 1))) = insert 0 (Finset.univ.erase 0) :=
    (Finset.insert_erase (Finset.mem_univ 0)).symm
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert (Finset.notMem_erase 0 _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t ht => ?_
  have h0t : (0 : Fin (D + 1)) ∉ t := fun h0 => Finset.notMem_erase 0 _ (Finset.mem_powerset.1 ht h0)
  have hc : t.card ≤ D := by
    have := Finset.card_le_card (Finset.mem_powerset.1 ht)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [Finset.sum_insert h0t, h, zero_add, Finset.card_insert_of_notMem h0t]
  have he : D + 1 - t.card = (D + 1 - (t.card + 1)) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem maDens_eq_zero_of_eventually {D : ℕ} (F : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    {y : Fin (D + 1) → ℂ} (h : F 0 =ᶠ[𝓝 y] fun _ => 0) : ReciprocityTheory.AnForm.maDens F y = 0 := by
  have h2 : fderiv ℝ (fderiv ℝ (F 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp
  have hH : ReciprocityTheory.AnForm.hessC (F 0) y = 0 := by
    ext i j
    simp [ReciprocityTheory.AnForm.hessC, h2]
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_eq_zero_of_eq_zero (fun k => ReciprocityTheory.AnForm.hessC (F k) y) hH]
  simp

theorem abs_half_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |Real.log (t ^ 2 + ε) / 2| ≤ |Real.log t| + |Real.log (2 * t)| := by
  have ht2 : 0 < t ^ 2 := by positivity
  have hlo : Real.log t ≤ Real.log (t ^ 2 + ε) / 2 := by
    have : Real.log (t ^ 2) ≤ Real.log (t ^ 2 + ε) := Real.log_le_log ht2 (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hup : Real.log (t ^ 2 + ε) ≤ 2 * (|Real.log t| + |Real.log (2 * t)|) := by
    have h1 : Real.log (t ^ 2 + ε) ≤ Real.log (t ^ 2 + 1) := Real.log_le_log (by positivity) (by linarith)
    have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht.ne'
    rcases le_total t 1 with h | h
    · have : Real.log (t ^ 2 + 1) ≤ Real.log (2 ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := neg_abs_le (Real.log t)
      linarith
    · have : Real.log (t ^ 2 + 1) ≤ Real.log ((2 * t) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this
      push_cast at this
      have a1 := le_abs_self (Real.log (2 * t))
      have a2 := abs_nonneg (Real.log t)
      linarith
  rw [abs_le]
  constructor
  · have a1 := neg_abs_le (Real.log t)
    have a2 := abs_nonneg (Real.log (2 * t))
    linarith
  · linarith

theorem exists_poly_of_linEval_eq_zero {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} {u : Fin n → ℂ} (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    (hu : linForm u ∉ J) :
    ∃ P : MvPolynomial (Fin d) ℂ, P ≠ 0 ∧
      ∀ y x, x ∈ ComplexSets.fibre J A y → linEval u x = 0 → MvPolynomial.eval y P = 0 := by
  classical
  have := hJ
  set a := Ideal.Quotient.mk J (linForm u) with ha_def
  have ha : a ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hint : (projHom J A).toRingHom.IsIntegralElem a := hA.finite.to_isIntegral _
  have hex : ∃ k, ∃ p : Polynomial (MvPolynomial (Fin d) ℂ), p.Monic ∧ p.natDegree = k ∧
      p.eval₂ (projHom J A).toRingHom a = 0 := by
    obtain ⟨p, hpm, hp⟩ := hint
    exact ⟨_, p, hpm, rfl, hp⟩
  obtain ⟨p, hpm, hpk, hp⟩ := Nat.find_spec hex
  refine ⟨p.coeff 0, fun h0 => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := Polynomial.X_dvd_iff.2 h0
    have hqm : q.Monic := Polynomial.monic_X.of_mul_monic_left hpm
    have hq : q.eval₂ (projHom J A).toRingHom a = 0 := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_X] at hp
      exact (mul_eq_zero.1 hp).resolve_left ha
    have hlt : q.natDegree < Nat.find hex := by
      rw [← hpk, Polynomial.natDegree_X_mul hqm.ne_zero]
      omega
    exact Nat.find_min hex hlt ⟨q, hqm, rfl, hq⟩
  · rintro y x ⟨hx, hxy⟩ hux
    have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) hp
    rw [Polynomial.hom_eval₂, IndefiniteRowSideFullHecke.ComplexSets.lift_eval_comp_projHom J A hx, map_zero] at h
    have hax : (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) a = 0 := by
      rw [ha_def, Ideal.Quotient.lift_mk, ← hux]
      simp [linForm, linEval]
    rw [hax, Polynomial.eval₂_at_zero, hxy] at h
    exact h

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : ι → ℂ, MvPolynomial.eval w g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖w‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm w i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r)
    (fun w => MvPolynomial.eval w g ≠ 0)).mpr fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem norm_chartDens_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ}
    (hy : ∀ x ∈ ComplexSets.fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (logReg u ε) (vecCons f φ) y‖ ≤
      chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖)
          (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h2 : ‖linEval ((2 : ℂ) • u) x‖ = 2 * ‖linEval u x‖ := by
        have : linEval ((2 : ℂ) • u) x = 2 * linEval u x := by
          simp [linEval, Finset.mul_sum, mul_assoc]
        rw [this, norm_mul]
        norm_num
      rw [h2]
      exact abs_half_log_le (norm_pos_iff.2 (hy x hx)) hε hε1
    · have hM : ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ hs.choose) y = 0 := by
        obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs.choose_spec
        refine maDens_eq_zero_of_eventually _ ?_
        have hc : ContinuousAt hs.choose y := by
          rw [← hx.2]
          exact hsd.continuousOn.continuousAt (hU.mem_nhds hxU)
        have hx' : x ∉ tsupport f := fun h => hxB (hR h)
        have hn : (tsupport f)ᶜ ∈ 𝓝 (hs.choose y) := by
          rw [← hx.2, hsx]
          exact (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
        filter_upwards [hc.preimage_mem_nhds hn] with w hw
        simp only [Matrix.cons_val_zero, Function.comp_apply]
        exact image_eq_zero_of_notMem_tsupport hw
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp

end LelongRegularise

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LocalLimitGlueOn
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology Set Function
open scoped ContDiff Manifold

theorem tendsto_of_forall_local_on_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} {l : Filter ι} (T : ι → (E → ℝ) → ℝ) (L : (E → ℝ) → ℝ)
    (hT : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → ∀ᶠ ε in l, T ε (f + g) = T ε f + T ε g)
    (hL : ∀ f g : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ContDiff ℝ ∞ g →
      HasCompactSupport g → L (f + g) = L f + L g)
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hloc : ∀ p ∈ tsupport f, ∃ N ∈ 𝓝 p, ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ N → Tendsto (fun ε => T ε g) l (𝓝 (L g))) :
    Tendsto (fun ε => T ε f) l (𝓝 (L f)) := by
  choose N hN hNf using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) (isClosed_tsupport f)
    (fun p : tsupport f => interior (N p.1 p.2)) (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hN x hx)⟩)
  obtain ⟨g, hg⟩ : ∃ g : tsupport f → E → ℝ, g = fun i x => ρ i x * f x := ⟨_, rfl⟩
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i => by
    rw [hg]; exact (ρ i).contMDiff.contDiff.mul hf
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => by
    rw [hg]; exact hfc.mul_left
  have hgN : ∀ i, tsupport (g i) ⊆ N i.1 i.2 := fun i => by
    rw [hg]; exact tsupport_mul_subset_left.trans ((hρ i).trans interior_subset)
  have hfin : {i | (support (ρ i) ∩ tsupport f).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hfc
  have hsum : f = ∑ i ∈ hfin.toFinset, g i := by
    funext x
    simp only [Finset.sum_apply, hg]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport f
    · rw [← finsum_eq_sum_of_support_subset (fun i => ρ i x), ρ.sum_eq_one hx, one_mul]
      intro i hi
      simp only [Set.Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨x, hi, hx⟩
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hT0 : ∀ᶠ ε in l, T ε 0 = 0 := by
    filter_upwards [hT 0 0 contDiff_const HasCompactSupport.zero contDiff_const
      HasCompactSupport.zero] with ε h
    simpa using h
  have hL0 : L 0 = 0 := by
    simpa using hL 0 0 contDiff_const HasCompactSupport.zero contDiff_const HasCompactSupport.zero
  have key : ∀ s : Finset (tsupport f), ContDiff ℝ ∞ (∑ i ∈ s, g i) ∧
      HasCompactSupport (∑ i ∈ s, g i) ∧
      (∀ᶠ ε in l, T ε (∑ i ∈ s, g i) = ∑ i ∈ s, T ε (g i)) ∧
      L (∑ i ∈ s, g i) = ∑ i ∈ s, L (g i) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact ⟨contDiff_const, HasCompactSupport.zero, hT0, hL0⟩
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [Finset.sum_insert ha]
      refine ⟨(hgs a).add h1, (hgc a).add h2, ?_, ?_⟩
      · filter_upwards [hT (g a) _ (hgs a) (hgc a) h1 h2, h3] with ε e1 e2
        rw [e1, e2]
      · rw [hL (g a) _ (hgs a) (hgc a) h1 h2, h4]
  obtain ⟨-, -, hTs, hLs⟩ := key hfin.toFinset
  rw [hsum, hLs]
  exact (tendsto_finsetSum _ fun i _ => hNf i.1 i.2 (g i) (hgs i) (hgc i) (hgN i)).congr'
    (hTs.mono fun ε h => h.symm)

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem mem_minimalPrimes_sup_linForm {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} (hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
  have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
  refine ⟨hWm.1.1, fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
  have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  simpa [linForm, linEval] using this

theorem lelongSides_add (hAdd : VarIntAdd.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (g₁ g₂ : (Fin n → ℂ) → ℝ) (h1 : ContDiff ℝ ∞ g₁)
    (h1c : HasCompactSupport g₁) (h2 : ContDiff ℝ ∞ g₂) (h2c : HasCompactSupport g₂) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), varInt J (d + 1) (g₁ + g₂) (vecCons (logReg u ε) φ) =
      varInt J (d + 1) g₁ (vecCons (logReg u ε) φ) + varInt J (d + 1) g₂ (vecCons (logReg u ε) φ)) ∧
    (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d (g₁ + g₂) φ) =
      (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₁ φ) +
      ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g₂ φ := by
  classical
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWJ, -⟩ := mem_minimalPrimes_sup_linForm hWm
    have hφW : ∀ i, SmoothNear (zeroSet W) (φ i) := fun i => by
      obtain ⟨U, hU, hSU, hC⟩ := hφ i
      exact ⟨U, hU, hWJ.trans hSU, hC⟩
    rw [hAdd n d W g₁ g₂ φ hWp h1.continuous h1c h2.continuous h2c hφW, mul_add]

theorem lelongLimit_off_small (hOff : LelongLimitOffZero.Statement) (hAdd : VarIntAdd.Statement)
    {n d : ℕ} {J I : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hφ : ∀ i, SmoothNear (zeroSet J) (φ i))
    (hloc : ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ)))
    (g : (Fin n → ℂ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgI : Disjoint (tsupport g) (zeroSet I)) :
    Tendsto (fun ε => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (𝓝[>] 0)
      (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
          (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)) := by
  classical
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local_on_tsupport
    (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
      (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd hJ hφ g₁ g₂ h1 h1c h2 h2c).1)
    (fun g₁ g₂ h1 h1c h2 h2c => (lelongSides_add hAdd (u := u) hJ hφ g₁ g₂ h1 h1c h2 h2c).2)
    g hg hgc fun q hq => ?_
  by_cases hq0 : q ∈ zeroSet J ∩ {x | linEval u x = 0}
  · exact hloc q hq0.1 hq0.2 (Set.disjoint_left.1 hgI hq)
  · refine ⟨_, hclosed.isOpen_compl.mem_nhds hq0, fun g' hg' hg'c hg'N => ?_⟩
    have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
        (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g' φ) = 0 := by
      refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
      rw [finsum_eq_dif]
      by_cases hWm : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes
      · obtain ⟨-, hWJ, hWu⟩ := mem_minimalPrimes_sup_linForm hWm
        rw [dite_eq_left hWm, varInt_eq_zero_of_vanish W g' φ fun x hx =>
          image_eq_zero_of_notMem_tsupport fun hxs => hg'N hxs ⟨hWJ hx, hWu x hx⟩, mul_zero]
      · rw [dite_eq_right hWm]
    simp only [h0]
    exact hOff n d J u g' φ hJ hdim hu hg' hg'c hφ
      (Set.disjoint_left.2 fun x hx hx' => hg'N hx hx')

theorem LelongLimitOnZero.proof (hOff : LelongLimitOffZero.Statement)
    (hGood : LelongLimitGoodPoints.Statement) (hSmall : LelongMassNearSmall.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimitOnZero.Statement := by
  classical
  intro n d J u φ p hJ hdim hu hφ _ _
  refine ⟨Set.univ, Filter.univ_mem, fun f hf hfc _ => ?_⟩
  obtain ⟨I, hI, hIdim, hloc⟩ := hGood n d J u φ hJ hdim hu hφ
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨χ, hχ, ⟨U, hU, hIU, hχ1⟩, hTχ, hLχ⟩ :=
    hSmall n d J I u φ f hJ hdim hu hφ hI hIdim hf hfc (δ / 3) (by positivity)
  have hχf : ContDiff ℝ ∞ (fun x => χ x * f x) := hχ.mul hf
  have hχfc : HasCompactSupport (fun x => χ x * f x) := hfc.mul_left
  have hg : ContDiff ℝ ∞ (fun x => (1 - χ x) * f x) := (contDiff_const.sub hχ).mul hf
  have hgc : HasCompactSupport (fun x => (1 - χ x) * f x) := hfc.mul_left
  have hgI : Disjoint (tsupport fun x => (1 - χ x) * f x) (zeroSet I) := by
    refine Disjoint.mono_right hIU (Disjoint.closure_left ?_ hU)
    refine Set.disjoint_left.2 fun x hx hxU => hx ?_
    simp [hχ1 x hxU]
  have hsum : (fun x => χ x * f x) + (fun x => (1 - χ x) * f x) = f := by
    funext x
    simp only [Pi.add_apply]
    ring
  obtain ⟨hTadd, hLadd⟩ := lelongSides_add hAdd (u := u) hJ hφ _ _ hχf hχfc hg hgc
  rw [hsum] at hTadd hLadd
  refine ((Metric.tendsto_nhds.1
    (lelongLimit_off_small hOff hAdd hJ hdim hu hφ hloc _ hg hgc hgI) (δ / 3) (by positivity)).and
    (hTχ.and hTadd)).mono fun ε ⟨h1, h2, h3⟩ => ?_
  rw [Real.dist_eq] at h1 ⊢
  rw [h3, hLadd]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2 hLχ
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hLχ.1, hLχ.2]

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def SliceLocalDimGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
        ∀ L ∈ O, ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseSliceGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def TransverseSliceGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        IsOpen {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} ∧
          Dense {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q}

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def CMLocusOpen.Statement : Prop :=
  ∀ (n : ℕ) (I P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime], I ≤ P →
    IsCohenMacaulayLocalRing (Localization.AtPrime P ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime P))) →
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ P ∧ ∀ (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q → g ∉ Q →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMProjDimCriterion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial CategoryTheory

def CMProjDimCriterion.Statement : Prop :=
  ∀ (n : ℕ) (I Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q →
    (IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))) ↔
      ∃ ℓ : ℕ, HasProjectiveDimensionLE (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q ⧸
          I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))) ℓ ∧
        (ℓ : ℕ∞) ≤ (I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q))).height)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchGermDimOne.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    0 < m → (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
      ringKrullDim (curveLocalRing I q) = 1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelOpenMapping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def NormalModelOpenMapping.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : NormalModel J) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn M.ideal) →
    ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ φ '' U = zeroSetIn M.ideal ∩ O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrderBranchesMeet
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def SameOrderBranchesMeet.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c c' : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder c' f) →
      ∃ x ∈ c.image ∩ c'.image, x ≠ q

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchImageNhdOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchImageNhdOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ c : VarBranch I 1 q, ∀ x ∈ c.image ∩ N, x ≠ q →
        ∃ U ∈ 𝓝 x, zeroSet I ∩ U ⊆ c.image

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInCurveComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchInCurveComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ J ∈ I.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) ∧
        ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchSameOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchSameOrder.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c d : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) →
      ∀ f : MvPolynomial (Fin n) ℂ, branchOrder c f = branchOrder d f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermProjectionStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PrimeGermProjectionStep.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime → P ≠ ⊥ →
    (∀ (τ : Type) [Fintype τ], Fintype.card τ < Fintype.card σ →
      ∀ (v : τ → ℂ) (Q : Ideal (holGerms v)), Q.IsPrime →
        ∃ (d : ℕ) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection v Q B) →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthTransverseSlice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def LengthTransverseSlice.Statement : Prop :=
  ∀ (n d : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ),
    W ∈ I.minimalPrimes → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → q ∈ zeroSet W →
    (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) → IsCohenMacaulayAt I q →
    IsTransverseSliceAt W L q →
      localMult I W = localMult (sliceIdeal I L q) (RingHom.ker (eval q))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimUpperZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceLocalDimUpperZariski.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ F : MvPolynomial (Fin d × Fin n) ℂ, F ≠ 0 ∧
        ∀ L : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F ≠ 0 →
          ringKrullDim (localRingAt (sliceIdeal J L q) q) ≤ (1 : ℕ)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermProjectionFunctionForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def GermProjectionFunctionForm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (p i) w) → IsFiniteGermProjection w (holGermIdeal w p) A →
      (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → IsGermCombination w p (fun z => h (A z)) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) ∧
      (∀ i : σ, ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
        IsGermCombination w p (fun z => z i ^ n + ∑ j, b j (A z) * z i ^ (j : ℕ))) ∧
      (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
        ∃ (s : Finset (σ → ℕ)) (a : (σ → ℕ) → (Fin d → ℂ) → ℂ), (∀ m ∈ s, AnalyticAt ℂ (a m) (A w)) ∧
          IsGermCombination w p (fun z => g z - ∑ m ∈ s, a m (A z) * ∏ i, z i ^ m i))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneUniformiser
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCodimOneUniformiser.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ) (x : MvPolynomial σ ℂ),
    P.IsPrime → Q.IsPrime → P ≤ Q → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
    x ∈ Q → x ∉ P →
      ∃ (g a b t : MvPolynomial σ ℂ) (k : ℕ), g ∈ Q ∧ 0 < k ∧ a ∉ Q ∧ b ∉ Q ∧ t ∉ Q ∧
        b * x - a * g ^ k ∈ P ∧ ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ P ⊔ Ideal.span {g}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianRankOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def JacobianRankOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ)
    (t : MvPolynomial σ ℂ), Q.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (d : ℕ) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial σ ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j)))) + d =
          Fintype.card σ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchInOneBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedBranchInOneBranch.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q)
    (ν : VarBranch I 1 q) (ρ : ℝ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 → 0 < ρ →
    (∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ∃ b, ∃ ρ' > 0, ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ' → ν.toFun (fun _ ↦ τ) ∈ (c b).image

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveCoordinateGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def IsCoordinateGraphNear {n : ℕ} (X : Set (Fin n → ℂ)) (x : Fin n → ℂ) : Prop :=
  x ∈ X ∧ ∃ W : Set (Fin n → ℂ), IsOpen W ∧ x ∈ W ∧ ∃ (i : Fin n) (V : Set ℂ) (g : ℂ → Fin n → ℂ),
    IsOpen V ∧ DifferentiableOn ℂ g V ∧ (∀ t ∈ V, g t i = t) ∧ ∀ z ∈ W, z ∈ X ↔ (z i ∈ V ∧ g (z i) = z)

def CurveCoordinateGraph.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ x ∈ zeroSet I, x ∈ Metric.ball q ε → x ≠ q → IsCoordinateGraphNear (zeroSet I) x

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∃ P : MaximalSpectrum (curveNormalisation I q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceUnmixedGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ)
              (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
            P ≤ RingHom.ker (eval q) →
              P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMinimalPrimePlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def MinimalPrimePlace.Statement : Prop :=
  ∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → J ∈ I.minimalPrimes → J ≤ RingHom.ker (eval q) →
    ∀ P' : MaximalSpectrum (curveNormalisation J q), ∃ P : MaximalSpectrum (curveNormalisation I q),
      ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
            (algebraMap (curveLocalRing I q) (curveNormalisation I q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
        Ring.ord (Localization.AtPrime P'.asIdeal)
          (algebraMap (curveNormalisation J q) (Localization.AtPrime P'.asIdeal)
            (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)))

end

end GroundTheory.Heights₂.Heights
end
