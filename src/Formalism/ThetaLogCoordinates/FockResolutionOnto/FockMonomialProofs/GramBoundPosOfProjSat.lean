module

public import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementH
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound
public import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.MahlerMeasure.CoarseLevelSlackInequalities
public import Formalism.PolynomialDimension.MultinomialDepth.TieOps
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.Vanish

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundUnconditionalOfSat
namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section Last

variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]

theorem resSatL_mono (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    {c c' : ℕ} (hc : c ≤ c') (h : ResSatL p LL J M ρ c) : ResSatL p LL J M ρ c' := by
  unfold ResSatL at h ⊢
  intro x hx hxI
  obtain ⟨g, hgY, hgI, hge⟩ := h x hx hxI
  refine ⟨((p : ℚ_[p]) ^ (c' - c)) • g, Submodule.smul_mem _ _ hgY, ?_, ?_⟩
  · have e : ((p : ℚ_[p]) ^ (c' - c)) • g = ((p : ℤ_[p]) ^ (c' - c)) • g := by
      rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ (c' - c)) g]
      simp
    rw [e]
    exact Submodule.smul_mem _ _ hgI
  · have hl : initPart (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ (c' - c)) • g)
        = ((p : ℚ_[p]) ^ (c' - c)) • initPart (Fin.last K, ρ) 0 g :=
      (resL p (Fin.last K, ρ) 0).map_smul _ g
    rw [hl, hge, smul_smul, ← pow_add, Nat.sub_add_cancel hc]

theorem resOntoK_of_resSatL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (c0 : ℕ) (h : ResSatL p LL J M ρ c0) : ResOntoK p LL J M ρ := by
  classical
  unfold ResOntoK
  unfold ResSatL at h
  intro x hx
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ_[p])
    (x.support.image fun m => AddMonoidAlgebra.coeff x m)
  have hb' : ∀ m, ∃ y : ℤ_[p], algebraMap ℤ_[p] ℚ_[p] y = (b : ℤ_[p]) • AddMonoidAlgebra.coeff x m := by
    intro m
    by_cases hm : m ∈ x.support
    · obtain ⟨y, hy⟩ := hb _ (Finset.mem_image_of_mem _ hm)
      exact ⟨y, hy⟩
    · refine ⟨0, ?_⟩
      have h0 : AddMonoidAlgebra.coeff x m = 0 := by
        by_contra hne
        exact hm (MvPolynomial.mem_support_iff.2 hne)
      rw [h0, smul_zero, map_zero]
  choose y hy using hb'
  have hbx : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) • x ∈ IntPol p (Fin (K + 1) × Fin r) := by
    refine LinearMap.mem_range.2 ⟨∑ m ∈ x.support, monomial m (y m), ?_⟩
    change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (∑ m ∈ x.support, monomial m (y m)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff x]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hy m, MvPolynomial.smul_monomial]
    congr 1
  obtain ⟨g, hgY, hgI, hge⟩ := h _ (Submodule.smul_mem _ _ hx) hbx
  have hs0 : algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hp0 : ((p : ℚ_[p]) ^ c0) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine ⟨((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ • g, Submodule.smul_mem _ _ hgY, ?_⟩
  rw [initPart_smul, hge, smul_smul, smul_smul]
  have h1 : ((p : ℚ_[p]) ^ c0 * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]))⁻¹ * (p : ℚ_[p]) ^ c0
      * algebraMap ℤ_[p] ℚ_[p] (b : ℤ_[p]) = 1 := by
    field_simp
  rw [h1, one_smul]

theorem resMMZL (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 c0 : ℕ) (hHP : HypP p LL ρ e1) (hHE : HypE p LL ρ e1) (hSat : ResSatL p LL J M ρ c0)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ XH p LL J M ρ w)
    (hxI : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ MMwZ p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ (e1 + c0)) • x := by
  obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
  obtain ⟨h0, hh0, hh0I, hres⟩ := hSat x hxX hxI
  obtain ⟨PE, hPE, -, hInt⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
  have hY := wtComp_Y LL J M w h0 hh0
  have hW := wtComp_mem (p := p) LL (K + 1) w h0
  refine ⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr
    ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW),
      hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩
  change resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _
  change resL p (Fin.last K, ρ) 0 h0 = _ at hres
  rw [map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres,
    wtComp_fix LL (K + 1) w _ (Submodule.smul_mem _ _ hxW), map_smul,
    eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩), smul_smul, ← pow_add]

theorem satAtL (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e e1 c0 : ℕ) (hr : 2 ≤ r) (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true)
    (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hS : ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) :
    SatAt p LLw J M ρ w e (e1 + c0) := by
  intro x hx hxI
  obtain ⟨y, hy, rfl⟩ :=
    (grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 hS) x).mp hx
  rw [pow_mul_int_iff] at hxI
  obtain ⟨h, hh, hres⟩ := resMMZL (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ
    (shiftWt w ρ e) e1 c0 hP hE hS y hy hxI
  refine (graded_eq_holds p K r LLw J M ρ w e hv he _).mpr ⟨h, hh, ?_⟩
  rw [hres, mul_smul_comm]

theorem setLast_total_le (LL : Letters (K + 1)) (o : ℕ) (ho : o ≤ LL.deg (Fin.last K)) :
    (setLast LL o).total ≤ LL.total := by
  unfold Letters.total
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = Fin.last K
  · subst hi
    simpa [setLast] using ho
  · simp [setLast, Function.update_of_ne hi]

end Last

theorem graded_bound_saturation_holds : GradedBoundOfSaturation := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 3) * e1) (e1 + c0) κ
      (projAtOf_of highest_vector_projection p K r LLw J M ρ w e e1 hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 3) * e1 + 2 * (e1 + c0) = (K + 5) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

theorem kapC_mono (p n : ℕ) {d d' : ℕ} (h : d ≤ d') : kapC p n d ≤ kapC p n d' := by
  unfold kapC
  exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))

theorem hypPE_setLast {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r) :
    ∀ o ≤ LLw.deg (Fin.last K),
      HypP p (setLast LLw o) ρ (kapC p r LLw.total) ∧ HypE p (setLast LLw o) ρ (kapC p r LLw.total) :=
  fun o ho =>
    ⟨Formalism.InvariantFactorPaths.PW.Top.dischargeP p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho)),
      Formalism.InvariantFactorPaths.PW.Top.dischargeE p (K + 1) r (setLast LLw o) ρ _ (kapC_mono p r (setLast_total_le LLw o ho))⟩

section Ties

variable {N : ℕ}

theorem grid_le (T : TieData) (Yl n₀ dd : Fin T.t → ℕ) (n : Fin T.t → ℕ)
    (hn : n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))) :
    ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
  intro i
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.1 (Fintype.mem_piFinset.1 hn i)
  rw [← hji]
  have hj' : j ≤ Yl i - 1 := by
    have := Finset.mem_range.1 hj
    omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _

theorem takeD_vec_last (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (n : Fin T.t → ℕ) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).vec (Fin.last (T.pos i)) = true := by
  obtain ⟨h1, hv, -⟩ := hadm.2.1 i
  simp [Letters.takeD, Letters.setTies, show T.pos i < N by omega, hv]

end Ties

end Formalism.InvariantFactorPaths.L4
end

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

theorem projAt2_of (hX : HighestVectorProjectionPos) (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ) (hK : 1 ≤ K) (hr : 2 ≤ r)
    (hρ : (ρ : ℕ) = r - 1) (hv : LLw.vec (Fin.last K) = true) (he : e ≤ LLw.deg (Fin.last K))
    (hP : HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hE : HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1)
    (hO : ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ) :
    ProjAt p LLw J M ρ w e ((K + 1) * e1) := by
  classical
  obtain ⟨Pr', hPr'⟩ := hX p K r (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e) e1
    hK hr hρ hv hP hE
  have hSp := grSpan_eq LLw J M ρ w e e1 hr hρ hv he hP hE hO
  refine ⟨(LinearMap.mulLeft ℚ_[p] (X (Fin.last K, ρ) ^ e : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])) ∘ₗ Pr' ∘ₗ
    strip p (Fin.last K, ρ) e, ?_⟩
  intro m hm
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  by_cases hme : m (Fin.last K, ρ) = e
  · obtain ⟨m', rfl⟩ : ∃ m', m = Finsupp.single (Fin.last K, ρ) e + m' :=
      ⟨m - Finsupp.single (Fin.last K, ρ) e, (add_tsub_cancel_of_le (by
        rw [Finsupp.single_le_iff]; exact hme.ge)).symm⟩
    have hm0 : m' (Fin.last K, ρ) = 0 := by simpa using hme
    have hmD := (multiDeg_pow LLw ρ e he m').mp hm
    obtain ⟨h1, h2, h3⟩ := hPr' m' hmD hm0
    rw [strip_monomial_eq _ _ _ hm0]
    refine ⟨(hSp _).mpr ⟨_, h1, rfl⟩, ?_, ?_⟩
    · rw [← mul_smul_comm, pow_mul_int_iff]; exact h2
    · intro g hg
      obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
      rw [monomial_single_add, fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy),
        fock_pow_mul _ _ _ _ (xH_le_free _ J _ ρ _ y hy), h3 y hy]
  · rw [strip_monomial_ne _ _ _ hme, map_zero, mul_zero]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, ?_⟩
    intro g hg
    obtain ⟨y, hy, rfl⟩ := (hSp g).mp hg
    rw [fock_eq_zero_of _ 0 (fun _ => Or.inr (by simp)), fock_eq_zero_of]
    intro n
    by_cases hn : n = m
    · left
      rw [hn]
      exact coeff_pow_mul_ne _ _ y (xH_le_free _ J _ ρ _ y hy) m hme
    · right
      rw [coeff_monomial, if_neg (Ne.symm hn)]

theorem graded_bound_pos_of_proj (hX : HighestVectorProjectionPos) : GradedBoundOfSaturationPos := by
  intro p _ K r _ LLw q J M ρ e1 c0 κ hK hr hρ hv hPE hS hκ w e k g hli hspan
  by_cases he : e ≤ LLw.deg (Fin.last K)
  · obtain ⟨hP, hE⟩ := hPE (LLw.deg (Fin.last K) - e) (Nat.sub_le _ _)
    refine graded_piece_bound_holds p K r LLw J M ρ w e ((K + 1) * e1) (e1 + c0) κ
      (projAt2_of hX p K r LLw J M ρ w e e1 hK hr hρ hv he hP hE (resOntoK_of_resSatL _ J _ ρ c0 (hS e he)))
      (satAtL LLw J M ρ w e e1 c0 hr hρ hv he hP hE (hS e he)) ?_ k g hli hspan
    have : (K + 1) * e1 + 2 * (e1 + c0) = (K + 3) * e1 + 2 * c0 := by ring
    rw [this]; exact hκ
  · rw [graded_bot_holds p K r LLw J M ρ w e (not_le.mp he)] at hspan
    have hk : k = 0 := by
      by_contra hk
      have h0 : g ⟨0, Nat.pos_of_ne_zero hk⟩ ∈ Submodule.span ℤ_[p] (Set.range g) :=
        Submodule.subset_span ⟨_, rfl⟩
      rw [hspan, Submodule.mem_bot] at h0
      exact hli.ne_zero _ h0
    subst hk
    simp

section Zero

variable {p : ℕ} [Fact p.Prime]

theorem self_lift {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hF : x ∈ FreeOf p (Fin.last K, ρ))
    (hY : x ∈ Y p LL J M) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ 0) • x := by
  refine ⟨x, hY, hi, ?_⟩
  rw [pow_zero, one_smul, ← resL_apply, resL_of_free _ x hF]

theorem pol_le_ycond_total {r N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : ℤ) (hc : (LL.total : ℤ) ≤ c) :
    Pol p r LL ≤ YCond p LL j ((c : ℤ) : WithTop ℤ) := by
  refine le_ycond LL j _ _ ?_ (fun a b x hx => Formalism.CountingSumsFrames.glAct_pol LL j a b x hx)
  intro x hx
  rw [Pol, mem_restrictSupport_iff] at hx
  rw [mem_restrictSupport_iff]
  intro m hm
  have h1 : MultiDeg LL m := hx hm
  have h2 := abs_wt_le LL j (0 : Fin r) m
  have h3 : (∑ v, m v) = LL.total := by
    rw [Fintype.sum_prod_type]
    unfold Letters.total
    exact Finset.sum_congr rfl fun i _ => h1 i
  show ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((c : ℤ) : WithTop ℤ)
  rw [WithTop.coe_le_coe]
  have h4 := le_abs_self (wt LL j (0 : Fin r) m)
  rw [h3] at h2
  omega

end Zero

theorem restricted_saturation_zero : ResSatLZero := by
  intro p _ r _ LL q J M ρ hr hρ hv x hx hxi
  obtain ⟨hxP, hxF, hxk⟩ := (mem_xsp LL J M ρ x).mp hx
  by_cases hfin : ∃ k, 0 + 1 ≤ J k ∧ M k ≠ ⊤
  · obtain ⟨k1, hk1, hM1⟩ := hfin
    have hne : (univ.filter fun k => 0 + 1 ≤ J k).Nonempty := ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1⟩⟩
    obtain ⟨k0, hk0, hmin⟩ := Finset.exists_min_image _ M hne
    have hk0' : 0 + 1 ≤ J k0 := (Finset.mem_filter.mp hk0).2
    have hmin' : ∀ k, 0 + 1 ≤ J k → M k0 ≤ M k := fun k hk =>
      hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    have hM0 : M k0 ≠ ⊤ := fun h => hM1 (top_le_iff.mp (h ▸ hmin' k1 hk1))
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hM0
    by_cases hcd : c < LL.total
    · have hT : x ∈ TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) := by
        rw [hc]; exact ((hxk k0).1 hk0').2
      have htot : LL.total = LL.deg (Fin.last 0) := by
        unfold Letters.total
        simp
      have hV := space_vanishing_holds p 0 r LL ρ c (LL.deg (Fin.last 0)) hr hρ hv (by
        rw [htot] at hcd
        simpa using hcd)
      rw [setLast_self] at hV
      have hx0 : x = 0 := by
        have : x ∈ Pol p r LL ⊓ FreeOf p (Fin.last 0, ρ) ⊓
            TypesLE p LL (0 + 1) (univ.erase ρ) ((c : ℤ) : WithTop ℤ) :=
          Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxP, hxF⟩, hT⟩
        rw [hV] at this
        exact (Submodule.mem_bot _).mp this
      subst hx0
      exact self_lift LL J M ρ 0 hxF (Submodule.zero_mem _) hxi
    · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
      by_cases hk : 0 + 1 ≤ J k
      · exact ycond_mono LL (J k) _ _ (hc ▸ hmin' k hk) (pol_le_ycond_total LL (J k) c (not_lt.mp hcd) hxP)
      · exact (hxk k).2 hk
  · refine self_lift LL J M ρ x hxF ((mem_y LL J M x).mpr ⟨hxP, fun k => ?_⟩) hxi
    by_cases hk : 0 + 1 ≤ J k
    · have : M k = ⊤ := by
        by_contra hne
        exact hfin ⟨k, hk, hne⟩
      rw [this, Formalism.CountingSumsFrames.ycond_top]
      exact Submodule.mem_top
    · exact (hxk k).2 hk

end Formalism.InvariantFactorPaths.L4
