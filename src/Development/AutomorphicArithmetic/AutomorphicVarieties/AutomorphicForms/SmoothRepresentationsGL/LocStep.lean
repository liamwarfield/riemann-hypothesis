module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocStep
noncomputable section

open Matrix Topology

namespace UpperTheory.V.Af.Smo

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

private theorem colM_mul_neg (m : Fin n) (u v : Fin n → R) (huv : u + v = 0) : colM m u * colM m v = 1 := by
  have h0 : (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then u i else 0) *
      (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then v i else 0) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Matrix.of_apply]
    by_cases h1 : k ≤ m
    · have : ¬ (i ≤ m ∧ k.val = m.val + 1) := fun h => by
        have := Fin.le_def.1 h1
        omega
      rw [if_neg this, zero_mul]
    · have : ¬ (k ≤ m ∧ j.val = m.val + 1) := fun h => h1 h.1
      rw [if_neg this, mul_zero]
  unfold colM
  rw [add_mul, mul_add, mul_add, h0, one_mul, one_mul, mul_one, add_zero, add_assoc, add_eq_left]
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
  split_ifs
  · rw [add_comm]; exact congrFun huv i
  · simp

private def colU (m : Fin n) (u : Fin n → R) : GL (Fin n) R :=
  ⟨colM m u, colM m (-u), colM_mul_neg m _ _ (by simp), colM_mul_neg m _ _ (by simp)⟩

private def dlt (m : Fin n) (ξ : Fin n → R) : (Fin n → R) →+ R where
  toFun u := dotLe m ξ u - u m
  map_zero' := by simp [dotLe]
  map_add' u v := by
    have : dotLe m ξ (u + v) = dotLe m ξ u + dotLe m ξ v := by
      unfold dotLe
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · simp [mul_add]
      · simp
    rw [this, Pi.add_apply]; ring

private theorem dlt_apply (m : Fin n) (ξ u : Fin n → R) : dlt m ξ u = dotLe m ξ u - u m := rfl

private theorem dlt_one (m : Fin n) (u : Fin n → R) : dlt m ((1 : Matrix (Fin n) (Fin n) R) m) u = 0 := by
  rw [dlt_apply, sub_eq_zero]
  unfold dotLe
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

private theorem dlt_single (m : Fin n) (ξ : Fin n → R) (j : Fin n) (hj : j ≤ m) (y : R) :
    dlt m ξ (Pi.single j y) = (ξ j - (1 : Matrix (Fin n) (Fin n) R) m j) * y := by
  rw [dlt_apply]
  unfold dotLe
  rw [Finset.sum_eq_single j]
  · by_cases h : m = j
    · subst h; simp [sub_mul]
    · simp [hj, Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

end Alg

section Top

variable {K : Type} [NormedField K] [CompleteSpace K] {n : ℕ}

private theorem img_nhds (U : OpenSubgroup (GL (Fin n) K)) :
    {M : Matrix (Fin n) (Fin n) K | ∃ s ∈ U, s.val = M} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) := by
  letI I := Matrix.linftyOpNormedRing (n := Fin n) (α := K)
  have hcs : @CompleteSpace (Matrix (Fin n) (Fin n) K) I.toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → K))
  have h := (@Units.isOpenMap_val (Matrix (Fin n) (Fin n) K) I
    (@instHasSummableGeomSeriesOfCompleteSpace _ (@NormedRing.toNonUnitalNormedRing _ I) hcs)) _ U.isOpen
  exact h.mem_nhds ⟨1, U.one_mem, rfl⟩

private theorem col_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∀ᶠ u in 𝓝 (0 : Fin n → K), ∃ s ∈ U, s.val = colM m u := by
  have hc : Continuous fun u : Fin n → K => colM m u := by
    unfold colM
    refine continuous_const.add (continuous_matrix fun i j => ?_)
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply i
    · exact continuous_const
  have h0 : colM m (0 : Fin n → K) = 1 := by
    ext i j; simp [colM]
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this (img_nhds U)

private theorem row_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ ξ : Fin n → K, (∀ j, j ≤ m → ξ j - (1 : Matrix (Fin n) (Fin n) K) m j ∈ V) →
      ∃ s ∈ U, s.val = rowM m ξ := by
  have hc : Continuous fun u : Fin n → K => rowM m (u + (1 : Matrix (Fin n) (Fin n) K) m) := by
    unfold rowM
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs
    · exact (continuous_apply j).add continuous_const
    · exact continuous_const
  have h0 : rowM m ((0 : Fin n → K) + (1 : Matrix (Fin n) (Fin n) K) m) = 1 := by
    ext i j
    simp only [rowM, Matrix.of_apply, zero_add]
    split_ifs with h
    · rw [h.1]
    · rfl
  have h1 := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at h1
  obtain ⟨ε, hε, h2⟩ := Metric.mem_nhds_iff.1 (h1 (img_nhds U))
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds _ hε, fun ξ hξ => ?_⟩
  have h3 : (fun j => if j ≤ m then ξ j - (1 : Matrix (Fin n) (Fin n) K) m j else 0) ∈
      Metric.ball (0 : Fin n → K) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    split_ifs with h
    · exact hξ j h
    · simpa using hε
  obtain ⟨s, hs, e⟩ := h2 h3
  refine ⟨s, hs, e.trans ?_⟩
  ext i j
  simp only [rowM, Matrix.of_apply, Pi.add_apply]
  by_cases h : i = m ∧ j ≤ m
  · simp [h]
  · rw [if_neg h, if_neg h]

private theorem step_gen (hA : AvgChar) (ψ : AddChar K ℂ) (hψ : ∀ᶠ x in 𝓝 (0 : K), ψ x = 1)
    (hD : ∀ V ∈ 𝓝 (0 : K), ∃ L : AddSubgroup K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, (∀ y ∈ L, ψ (x * y) = 1) → x ∈ V) (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ (c : GL (Fin n) K →₀ ℂ) (h : (Fin n → K) → ℂ),
      h ((1 : Matrix (Fin n) (Fin n) K) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → ∃ s ∈ U, s.val = rowM m ξ) ∧
      ∀ W : GL (Fin n) K → ℂ, (∀ g, ∀ u ∈ U, W (g * u) = W g) → ∀ p ξ,
        (∀ u (t : GL (Fin n) K), t.val = colM m u → W (p * t) = ψ (dotLe m ξ u) * W p) →
        comb c W p = h ξ * W p := by
  classical
  obtain ⟨V, hV, hrow⟩ := row_nhds m U
  obtain ⟨L₁, ho, hc, hL₁⟩ := hD V hV
  let L : AddSubgroup (Fin n → K) := AddSubgroup.pi Set.univ fun _ => L₁
  have hLo : IsOpen (L : Set (Fin n → K)) := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hLc : IsCompact (L : Set (Fin n → K)) := isCompact_univ_pi fun _ => hc
  let N : Set (Fin n → K) := {u | u ∈ L ∧ (∃ s ∈ U, s.val = colM m u) ∧ ψ (u m) = 1}
  have hN : N ∈ 𝓝 (0 : Fin n → K) := by
    have hψm : ∀ᶠ u in 𝓝 (0 : Fin n → K), ψ (u m) = 1 :=
      (continuous_apply m).continuousAt (x := (0 : Fin n → K)) hψ
    exact Filter.inter_mem (hLo.mem_nhds L.zero_mem) (Filter.inter_mem (col_nhds m U) hψm)
  let L₀ := AddSubgroup.closure N
  have hle : L₀ ≤ L := (AddSubgroup.closure_le _).2 fun u hu => hu.1
  have hL₀ : IsOpen (L₀ : Set (Fin n → K)) :=
    L₀.isOpen_of_mem_nhds (Filter.mem_of_superset hN AddSubgroup.subset_closure)
  have hidx : L₀.relIndex L ≠ 0 := by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
    have := AddSubgroup.quotient_finite_of_isOpen (L₀.addSubgroupOf L) (hL₀.preimage continuous_subtype_val)
    exact AddSubgroup.index_ne_zero_of_finite
  obtain ⟨T, hT, hTL, hsum⟩ := hA _ L₀ L hle hidx
  have hcard : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  refine ⟨∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m)),
    fun ξ => if ∀ u ∈ L, ψ (dlt m ξ u) = 1 then 1 else 0, ?_, fun ξ hξ => ?_, fun W hW p ξ hp => ?_⟩
  · simp [dlt_one]
  · have h1 : ∀ u ∈ L, ψ (dlt m ξ u) = 1 := by
      by_contra h
      exact hξ (if_neg h)
    refine hrow ξ fun j hj => hL₁ _ fun y hy => ?_
    rw [← dlt_single m ξ j hj]
    refine h1 _ fun k _ => ?_
    by_cases h : k = j
    · subst h; simpa using hy
    · rw [Pi.single_eq_of_ne h]; exact L₁.zero_mem
  · have e1 : comb (∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m))) W p =
        (T.card : ℂ)⁻¹ * (∑ t ∈ T, ψ (dlt m ξ t)) * W p := by
      unfold comb
      rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; ring), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finsupp.sum_single_index (by simp), hp t (colU m t) rfl, dlt_apply, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    by_cases h0 : W p = 0
    · simp [h0]
    congr 1
    dsimp only
    split_ifs with h
    · rw [Finset.sum_congr rfl fun t ht => h t (hTL t ht)]
      simp [hcard]
    · push Not at h
      have h2 : ∀ x ∈ L₀, ψ.compAddMonoidHom (dlt m ξ) x = 1 := by
        intro x hx
        induction hx using AddSubgroup.closure_induction with
        | mem u hu =>
          obtain ⟨-, ⟨s, hs, e⟩, h3⟩ := hu
          have h4 := hp u s e
          rw [hW p s hs] at h4
          have h5 : ψ (dotLe m ξ u) = 1 := mul_right_cancel₀ h0 (by rw [← h4, one_mul])
          rw [AddChar.compAddMonoidHom_apply, dlt_apply, AddChar.map_sub_eq_div, h5, h3, div_one]
        | zero => simp
        | add x y _ _ hx hy => rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
        | neg x _ hx => rw [AddChar.map_neg_eq_inv, hx, inv_one]
      have := hsum _ h2 h
      simp only [AddChar.compAddMonoidHom_apply] at this
      rw [this, mul_zero]

end Top

end UpperTheory.V.Af.Smo

theorem UpperTheory.V.Af.Smo.locStep :
    UpperTheory.V.Af.Smo.AvgChar → UpperTheory.V.Af.Smo.LocDual → UpperTheory.V.Af.Smo.LocStep := by
  intro hA hD E _ _ w ψ hψ h1 n m _ U
  exact UpperTheory.V.Af.Smo.step_gen hA ψ hψ (hD E w ψ h1) m U
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ArchKir
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lmul_lmul {E : Type} [Field E] [NumberField E] {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Rinf E))
    (x : Lie E n) : lmul (toL a) (lmul (toL b) x) = lmul (toL (a * b)) x := by
  change toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)
  rw [Matrix.mul_assoc]

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

theorem UpperTheory.V.Af.Smo.archKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.ArchStep → UpperTheory.V.Af.Smo.LinChange → UpperTheory.V.Af.Smo.ArchKir := by
  classical
  intro hC hR hA hL E _ _ n m
  induction m with
  | zero =>
    intro _
    refine ⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩
    · have : supN (1 : GL (Fin n) (Rinf E)).val = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h
        · exact Matrix.one_apply_ne (fun e => by subst e; omega)
        · rfl
      simp only [this]
      simp [psiR]
    · simp only [hw p hp, mul_assoc]
      exact integral_const_mul _ _
  | succ m ih =>
    intro hm
    obtain ⟨H, H1, hH⟩ := ih (by omega)
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨h, h1, hu, hh⟩ := hA E n m' hm
    obtain ⟨c, c1, hc⟩ := hL E n
    refine ⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_,
      fun α => ?_⟩
    · have hs : IsUnit (rowM m' ((1 : GL (Fin n) (Rinf E)).val m')) := by
        rw [Units.val_one, rowM_one]; exact isUnit_one
      have e : hs.unit = 1 := Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])
      simp only [dif_pos hs, e]
      simp [h1, c1, H1]
    · obtain ⟨β₀, hβ₀⟩ := hH α
      obtain ⟨β, hβ⟩ := hh β₀
      refine ⟨β, fun w wm wb hw p hp => ?_⟩
      obtain ⟨C, hCb⟩ := wb
      have key := hβ (fun x => w (lmul (toL p.val) x)) (p.val m')
        (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by
          obtain ⟨ν, hν, hs, e⟩ := hC (Rinf E) n m' hm p hp u
          simp only [lmul_lmul]
          rw [e, ← lmul_lmul, hw ν hν, hs])
      rw [key]
      by_cases h0 : h (p.val m') = 0
      · simp [h0]
      have hs := hu _ h0
      simp only [dif_pos hs]
      have hy := hR (Rinf E) n m' p hs.unit hp hs.unit_spec
      have e1 := hβ₀ w wm ⟨C, hCb⟩ hw _ hy
      have e2 := hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)
      have e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      simp only [lmul_lmul, e3] at e2
      rw [hs.unit_spec] at e2
      rw [e2, e1]
      ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthStep
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

theorem UpperTheory.V.Af.Smo.orthStep :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.OrthStep := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
    have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
    generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ = ν at *
    have : SFinite ν := sfinite_of_finite ν
    have : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
    have : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g) := fun g γ x => by
      show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)
      rw [mul_assoc]
      exact hl γ _
    have hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x := fun x γ g => by
      show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x
      unfold chart
      split_ifs with hx
      · exact hr _ γ g
      · rfl
    let F : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n → ℂ := fun z =>
      CuspidalSpectrum.cuspQuot (hF z.2) z.1
    have hFmk : ∀ (y : Reduction.normOneGL (K := E) (n := n)) x,
        F (RightCosetSpace.mk (Reduction.rationalGLOne (K := E) (n := n)) y, x) = chart f y.1 x := fun _ _ => rfl
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hFb : ∀ z, ‖F z‖ ≤ C := by
      rintro ⟨q, x⟩
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [hFmk]
      unfold chart
      split_ifs
      · exact hC _
      · simpa using hC0
    have hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0 := by
      intro q x hx
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [hFmk]
      exact dif_neg hx
    have hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)))) ×ˢ invSet E n) :=
      isOpen_univ.prod TR.isOpen_invSet
    have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
      rintro ⟨q, x⟩ ⟨-, hx⟩
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne (K := E) (n := n))).prodMap
        (IsOpenQuotientMap.id (X := Lie E n))
      refine ContinuousAt.continuousWithinAt ?_
      refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
      have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
        (hcc E n f hf).1.continuousAt ((isOpen_univ.prod TR.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
      have h2 : Continuous fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      exact ContinuousAt.comp (f := fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n))
        (x := (y, x)) h1 h2.continuousAt
    have hFm : Measurable F := by
      have hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ :=
        (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩
      have := hFc.measurable_piecewise hc hopen.measurableSet
      rwa [Set.piecewise_same] at this
    have hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n =>
        (a z.1 * F z) * β z.2)
        (ν.prod volume) := by
      have hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n => β z.2)
          (ν.prod volume) :=
        (β.integrable (μ := volume)).comp_snd _
      refine hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul]
      exact mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))
    have e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x := by
      intro q
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]
      simp only [hFmk, mul_assoc]
    have e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0 := by
      intro x
      rw [integral_mul_const]
      by_cases hx : x ∈ invSet E n
      · have hx' : IsUnit (Matrix.of x) := hx
        have e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q := by
          intro q
          obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
          rw [hFmk, CuspidalSpectrum.cuspQuot_mk]
          exact dif_pos hx'
        simp only [e]
        rw [h0, zero_mul]
      · simp [hF0 _ x hx]
    simp only [e1]
    rw [integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]
    simp only [e2, integral_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Vanish
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R T : Type} [CommRing R] [CommRing T] {n m : ℕ} (φ : R →+* T) {p : GL (Fin n) R}
    (h : IsY m p.val) : IsY m (GeneralLinearGroup.map φ p).val := fun i hi =>
  ⟨by change φ (p.val i i) = 1; rw [(h i hi).1, map_one],
    fun j hj => by change φ (p.val i j) = 0; rw [(h i hi).2 j hj, map_zero]⟩

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := fun i _ =>
  ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_mul {R : Type} [CommRing R] {n m : ℕ} {p q : GL (Fin n) R}
    (hp : IsY m p.val) (hq : IsY m q.val) : IsY m (p * q).val := by
  intro i hi
  have key : ∀ j, j ≤ i → (p * q).val i j = q.val i j := by
    intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, (hp i hi).1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hp i hi).2 k h, zero_mul]
      · rw [(hq k (hi.trans h.le)).2 j (hj.trans_lt h), mul_zero]
    · simp
  exact ⟨by rw [key i le_rfl, (hq i hi).1], fun j hj => by rw [key j hj.le, (hq i hi).2 j hj]⟩

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem exists_part (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (Af E)) :
    ∃ s : GL (Fin n) (Af E), SuppIn S s ∧ ∀ w ∈ S, cmp w s = cmp w g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w _ => map_one _, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert v S hv ih =>
    obtain ⟨s, h1, h2⟩ := ih
    refine ⟨s * locGL E n v (cmp v g), fun w hw => ?_, fun w hw => ?_⟩
    · rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, h1 w hw.2, one_mul]
      exact GlobalTheory.CuspRep.pLoc_locGL_of_ne hw.1 _
    · rw [map_mul]
      rcases Finset.mem_insert.1 hw with rfl | h
      · rw [h1 w hv, one_mul]
        exact GlobalTheory.CuspRep.pLoc_locGL _ _
      · rw [h2 w h, show cmp w (locGL E n v (cmp v g)) = 1 from
          GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : w = v => hv (e ▸ h)) _, mul_one]

private theorem af_ext {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y :=
  DFunLike.ext _ _ h

private theorem isY_af {m : ℕ} {s : GL (Fin n) (Af E)} (h : ∀ w, IsY m (cmp w s).val) : IsY m s.val := fun i hi =>
  ⟨af_ext fun w => by rw [map_one]; exact (h w i hi).1,
    fun j hj => af_ext fun w => by rw [map_zero]; exact (h w i hi).2 j hj⟩

private theorem pFin_finGL (k : GL (Fin n) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E n k) = k := by
  rw [finGL, GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]
  rfl

variable [IsTotallyReal E]

private theorem isY_ad {m : ℕ} {g : GA E n} (h1 : IsY m (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : IsY m (GeneralLinearGroup.map (pFin E) g).val) : IsY m g.val := fun i hi =>
  ⟨TR.ad_ext (by rw [map_one]; exact (h1 i hi).1) (by rw [map_one]; exact (h2 i hi).1),
    fun j hj => TR.ad_ext (by rw [map_zero]; exact (h1 i hi).2 j hj) (by rw [map_zero]; exact (h2 i hi).2 j hj)⟩

private theorem exists_dec (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E n)
    (h1 : IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val) :
    ∃ p k, InPS S p ∧ Away S k ∧ g = p * finGL E n k := by
  obtain ⟨s, hs, hg⟩ := exists_part S (GeneralLinearGroup.map (pFin E) g)
  have e : GeneralLinearGroup.map (pFin E) (infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s) = s := by
    rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s, s⁻¹ * GeneralLinearGroup.map (pFin E) g,
    ⟨isY_ad ?_ ?_, ?_⟩, fun w hw => ?_, ?_⟩
  · rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]
    exact h1
  · rw [e]
    refine isY_af fun w => ?_
    by_cases hw : w ∈ S
    · rw [hg w hw]; exact h2 w hw
    · rw [hs w hw]; exact isY_one
  · rw [e]; exact hs
  · rw [map_mul, map_inv, hg w hw, inv_mul_cancel]
  · rw [mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]

end

theorem UpperTheory.V.Af.Smo.vanish :
    UpperTheory.V.Af.Smo.SphAll → UpperTheory.V.Af.Smo.InjP → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Vanish := by
  intro hSA hI hD hWB hEM E _ _ _ n hn S B f hf hS hK h0
  have hW : ∀ p, InPS S p → ∀ k, Away S k → whittaker f (p * finGL E n k) = 0 := fun p hp =>
    hSA E n S B (whittaker f) (hWB E n f hf).2.2
      (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) f (hS w hw).2).1 hf⟩)
      (fun g k hk => by
        unfold whittaker
        simp only [← mul_assoc, hK _ k hk]) p hp.2 (h0 p hp)
  have hX := hI E n hn f hf {g | IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val ∧
      ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val}
    (fun γ hγ g hg => by
      have h : IsY (n - 1) (ratGL E n γ).val := isY_map _ hγ
      refine ⟨?_, fun w hw => ?_⟩
      · rw [map_mul]; exact isY_mul (isY_map _ h) hg.1
      · rw [map_mul, map_mul]; exact isY_mul (isY_map _ (isY_map _ h)) (hg.2 w hw))
    (fun g hg => by
      obtain ⟨p, k, hp, hk, rfl⟩ := exists_dec S g hg.1 hg.2
      exact hW p hp k hk)
  refine Continuous.ext_on (hD E n S) hf.cont continuous_const ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : f (finGL E n k) = 0 := hX _ ⟨by rw [TR.pInf_finGL]; exact isY_one, fun w hw => by
    rw [pFin_finGL, hk w hw]; exact isY_one⟩
  exact (hf.left γ _).trans h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.PrSLocNe
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem pr_comm {S : Finset (HeightOneSpectrum (𝓞 E))} {x k : GL (Fin n) (Af E)} (hx : SuppIn S x)
    (hk : Away S k) : k * x = x * k := by
  refine cmp_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases h : w ∈ S
  · rw [hk w h, mul_one, one_mul]
  · rw [hx w h, mul_one, one_mul]

private theorem pr_sLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : pLoc E w (sLoc E w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x

private theorem pr_sLoc_ne {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (x : w.adicCompletion E) :
    pLoc E v (sLoc E w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x

private theorem pr_loc {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S)
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : InKS S (locGL E n w k) := by
  have h1 : ∀ v, v ≠ w → cmp v (locGL E n w k) = 1 := fun v hv =>
    GlobalTheory.CuspRep.map_cornerGL_of_zero _ _ (pr_sLoc_ne hv) k
  have h2 : cmp w (locGL E n w k) = k :=
    GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) (pr_sLoc w) k
  refine ⟨fun v hv => h1 v fun e => hw (e ▸ hv), fun v => ?_⟩
  by_cases h : v = w
  · subst h; rw [h2]; exact hk
  · rw [h1 v h]; exact one_mem _

private theorem pr_fop {S : Finset (HeightOneSpectrum (𝓞 E))} {c : GL (Fin n) (Af E) →₀ ℂ}
    (hc : ∀ x ∈ c.support, SuppIn S x) {f : GA E n → ℂ} (hf : ∀ g k, InKS S k → f (g * finGL E n k) = f g)
    (g : GA E n) (k : GL (Fin n) (Af E)) (hk : InKS S k) : fop c f (g * finGL E n k) = fop c f g := by
  unfold fop
  refine Finsupp.sum_congr fun x hx => ?_
  rw [mul_assoc, ← map_mul, pr_comm (hc x hx) hk.1, map_mul, ← mul_assoc, hf _ _ hk]

private theorem pr_wh {f : GA E n → ℂ} {u : GA E n} (hf : ∀ g, f (g * u) = f g) (g : GA E n) :
    whittaker f (g * u) = whittaker f g := by
  unfold whittaker
  simp only [← mul_assoc, hf]

variable [IsTotallyReal E]

private theorem pr_conv {f : GA E n → ℂ} {k : GL (Fin n) (Af E)} (hf : ∀ g, f (g * finGL E n k) = f g)
    (α : Lie E n → ℂ) (g : GA E n) : conv f α (g * finGL E n k) = conv f α g := by
  unfold Af.Smo.conv
  congr 1
  funext x
  congr 1
  unfold chart
  split_ifs with h
  · rw [mul_assoc, ← TR.infGL_comm, ← mul_assoc, hf]
  · rfl

private theorem pr_mem (π : CuspSub E n) (c : GL (Fin n) (Af E) →₀ ℂ) {φ : TR.Sm E n} (hφ : φ ∈ π.V) :
    ∃ ψ ∈ π.V, ψ.1 = fop c φ.1 := by
  refine ⟨∑ x ∈ c.support, c x • TR.act (.fin x) φ,
    π.V.sum_mem fun x _ => π.V.smul_mem _ (π.stable _ _ hφ), ?_⟩
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply]
  rfl

end

theorem UpperTheory.V.Af.Smo.pair :
    UpperTheory.V.Af.Smo.Seed → UpperTheory.V.Af.Smo.SetUp → UpperTheory.V.Af.Smo.KillP → UpperTheory.V.Af.Smo.Vanish → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.WhLin → UpperTheory.V.Af.Smo.ConvNice → UpperTheory.V.Af.Smo.EigOfSat → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Pair := by
  intro hSeed hSet hKill hVan hWB hWL hCN hES hEM E _ _ _ n hn π π' hc hc' hs
  obtain ⟨hN, φ, hφ, α, hα⟩ := hSeed E n π hc
  obtain ⟨hN', φ', hφ', α', hα'⟩ := hSeed E n π' hc'
  obtain ⟨S, B, hS, hK, hK'⟩ := hSet E n π π' hs φ hφ φ' hφ'
  obtain ⟨V, hV⟩ := (hN φ hφ).level
  obtain ⟨V', hV'⟩ := (hN' φ' hφ').level
  obtain ⟨c, H, hH, hc, hop⟩ := hKill E n hn S (V ⊓ V')

  have side : ∀ (σ : CuspSub E n), (∀ φ ∈ σ.V, Nice φ.1) → (∀ w ∉ S, σ.HasSat w (B w)) → ∀ φ ∈ σ.V,
      ∀ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1 → (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) →
      (∀ g, ∀ u ∈ V ⊓ V', φ.1 (g * finGL E n u) = φ.1 g) →
      ∃ ψ ∈ σ.V, ∃ β : 𝓢(Lie E n, ℂ), Nice (conv ψ.1 β) ∧ (∀ w ∉ S, EigAt w (B w) (conv ψ.1 β)) ∧
        (∀ g k, InKS S k → conv ψ.1 β (g * finGL E n k) = conv ψ.1 β g) ∧
        ∀ p, InPS S p → whittaker (conv ψ.1 β) p = H p := by
    intro σ hN hsat φ hφ α hα hK hU
    obtain ⟨ψ, hψ, e⟩ := pr_mem σ c hφ
    obtain ⟨β, hβ⟩ := hop α
    have hK₁ : ∀ g k, InKS S k → ψ.1 (g * finGL E n k) = ψ.1 g := by
      rw [e]; exact pr_fop hc hK
    refine ⟨ψ, hψ, β, (hCN E n _ (hN ψ hψ) β).1, fun w hw => ?_, fun g k hk => pr_conv (fun g => hK₁ g k hk) _ g,
      fun p hp => ?_⟩
    · exact (hEM E n w (B w) _ (hES E n σ w (B w) (hsat w hw) ψ hψ
        fun g k hk => hK₁ g _ (pr_loc hw hk))).2.1 (hN ψ hψ) β
    · obtain ⟨b1, b2, b3⟩ := hWB E n _ (hN φ hφ)
      rw [(hCN E n _ (hN ψ hψ) β).2, e, ((hWL E n _ (hN φ hφ)).1 c).2,
        hβ _ b1 b2 b3 (fun g u hu => pr_wh (fun g => hU g u hu) g) p hp, hα, mul_one]
  obtain ⟨ψ, hψ, β, n1, e1, k1, w1⟩ := side π hN (fun w hw => (hS w hw).2.1) φ hφ α hα hK
    fun g u hu => hV g u hu.1
  obtain ⟨ψ', hψ', β', n2, e2, k2, w2⟩ := side π' hN' (fun w hw => (hS w hw).2.2) φ' hφ' α' hα' hK'
    fun g u hu => hV' g u hu.2
  obtain ⟨n3, w3⟩ := (hWL E n _ n1).2 _ n2
  refine ⟨ψ, hψ, ψ', hψ', β, β', sub_eq_zero.1 (hVan E n hn S B _ n3
    (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) _ (e1 w hw)).2.2 _ (e2 w hw)⟩) (fun g k hk => ?_) fun p hp => ?_),
    fun h0 => ?_⟩
  · rw [Pi.sub_apply, Pi.sub_apply, k1 g k hk, k2 g k hk]
  · rw [w3, Pi.sub_apply, w1 p hp, w2 p hp, sub_self]
  · have h1 : InPS S (1 : GA E n) := by
      refine ⟨fun i _ => ⟨by simp, fun j hj => ?_⟩, fun w _ => by rw [map_one, map_one]⟩
      exact Matrix.one_apply_ne hj.ne'
    have h2 := w1 1 h1
    rw [h0, hH] at h2
    simp [whittaker] at h2
end
