module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InvarianceOfDomain

open Metric Set MeasureTheory

variable {n : ℕ}

theorem brouwer_closedBall (hB : BrouwerFixedPoint.Statement) {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {h : (Fin n → ℝ) → Fin n → ℝ} (hc : ContinuousOn h (closedBall a r))
    (hm : MapsTo h (closedBall a r) (closedBall a r)) : ∃ x ∈ closedBall a r, h x = x := by
  have haff : MapsTo (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) (closedBall a r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]
  have hcont : ContinuousOn (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) :=
    by fun_prop
  have hcomp : ContinuousOn (fun x : Fin n → ℝ => h (a + r • x)) (closedBall 0 1) := hc.comp hcont haff
  obtain ⟨x, hx, hfix⟩ := hB n (fun x => r⁻¹ • (h (a + r • x) - a)) (by fun_prop)
    (by
      intro x hx
      have hy := hm (haff hx)
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
        inv_mul_le_iff₀ hr, mul_one]
      exact hy)
  refine ⟨a + r • x, haff hx, ?_⟩
  have h2 : r • (r⁻¹ • (h (a + r • x) - a)) = r • x := by rw [hfix]
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h2
  exact sub_eq_iff_eq_add'.mp h2

def smoothSubalgebra (n : ℕ) : Subalgebra ℝ C(Fin n → ℝ, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : (Fin n → ℝ) → ℝ)}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_mul]
    exact ContDiff.mul hg hh
  add_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_add]
    exact ContDiff.add hg hh
  algebraMap_mem' c := by
    simp only [mem_ofPred_eq]
    convert (contDiff_const (c := c) : ContDiff ℝ 1 fun _ : Fin n → ℝ => c) using 1
    ext x
    simp

theorem smoothSubalgebra_separatesPoints : (smoothSubalgebra n).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z => z i, ⟨⟨fun z => z i, continuous_apply i⟩, ?_, rfl⟩, hi⟩
  show ContDiff ℝ 1 fun z : Fin n → ℝ => z i
  exact contDiff_apply ℝ (fun _ => ℝ) i

theorem exists_differentiable_near {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (G : (Fin n → ℝ) → Fin n → ℝ) (hG : Continuous G) {η : ℝ} (hη : 0 < η) :
    ∃ P : (Fin n → ℝ) → Fin n → ℝ, Differentiable ℝ P ∧ ∀ y ∈ S, ‖P y - G y‖ < η := by
  have h : ∀ i : Fin n, ∃ g ∈ smoothSubalgebra n, ∀ y ∈ S, ‖(g : (Fin n → ℝ) → ℝ) y - G y i‖ < η :=
    fun i => ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      smoothSubalgebra_separatesPoints ⟨fun y => G y i, (continuous_apply i).comp hG⟩ hS hη
  choose g hg hgS using h
  refine ⟨fun y i => g i y, differentiable_pi.2 fun i => ?_, fun y hy => ?_⟩
  · exact (show ContDiff ℝ 1 (g i : (Fin n → ℝ) → ℝ) from hg i).differentiable one_ne_zero
  · rw [pi_norm_lt_iff hη]
    intro i
    simpa using hgS i y hy

theorem exists_small_avoid {P : (Fin n → ℝ) → Fin n → ℝ} (hP : Differentiable ℝ P) (c a : Fin n → ℝ)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ v : Fin n → ℝ, ‖v‖ < δ ∧ ∀ y ∈ sphere c ρ, P y ≠ a + v := by
  have hnull : volume (P '' sphere c ρ) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hP.differentiableOn
      (Measure.addHaar_sphere_of_ne_zero volume c hρ.ne')
  by_contra! hall
  have hsub : ball a δ ⊆ P '' sphere c ρ := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hall (z - a) (by rwa [mem_ball, dist_eq_norm] at hz)
    exact ⟨y, hy, by rw [hyz]; abel⟩
  have hle := measure_mono (μ := volume) hsub
  rw [hnull] at hle
  exact (measure_ball_pos volume a hδ).ne' (nonpos_iff_eq_zero.mp hle)

theorem exists_pos_le {s : Set (Fin n → ℝ)} (hs : IsCompact s) {g : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g s) (hpos : ∀ y ∈ s, 0 < g y) : ∃ δ > 0, ∀ y ∈ s, δ ≤ g y := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨y0, hy0, hmin⟩ := hs.exists_isMinOn hne hg
    exact ⟨g y0, hpos y0 hy0, fun y hy => hmin hy⟩

noncomputable def radialPush (c : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  c + max 1 (ρ / ‖y - c‖) • (y - c)

theorem radialPush_of_le {c y : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hy : ρ ≤ dist y c) :
    radialPush c ρ y = y := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := hρ.trans_le hy
  have h1 : ρ / ‖y - c‖ ≤ 1 := (div_le_one hpos).2 hy
  rw [radialPush, max_eq_left h1, one_smul, add_sub_cancel]

theorem radialPush_mem_sphere {c y : Fin n → ℝ} {ρ : ℝ} (hy : dist y c < ρ) (hyc : y ≠ c) :
    radialPush c ρ y ∈ sphere c ρ := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc)
  have h1 : 1 ≤ ρ / ‖y - c‖ := (one_le_div hpos).2 hy.le
  rw [mem_sphere, dist_eq_norm, radialPush, max_eq_right h1, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (hpos.trans hy).le hpos.le), div_mul_cancel₀ ρ hpos.ne']

theorem continuousOn_radialPush (c : Fin n → ℝ) (ρ : ℝ) : ContinuousOn (radialPush c ρ) {y | y ≠ c} := by
  have hn : ContinuousOn (fun y : Fin n → ℝ => ρ / ‖y - c‖) {y | y ≠ c} := by
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) ?_
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  have hm : ContinuousOn (fun y : Fin n → ℝ => max 1 (ρ / ‖y - c‖)) {y | y ≠ c} :=
    continuousOn_const.sup hn
  unfold radialPush
  fun_prop

theorem mem_interior_image (hB : BrouwerFixedPoint.Statement) {f : (Fin n → ℝ) → Fin n → ℝ}
    {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hc : ContinuousOn f (closedBall a r))
    (hi : InjOn f (closedBall a r)) : f a ∈ interior (f '' closedBall a r) := by
  have hK : IsCompact (closedBall a r) := isCompact_closedBall a r

  obtain ⟨G, hGf⟩ : ∃ G : C(Fin n → ℝ, Fin n → ℝ), ∀ x ∈ closedBall a r, G (f x) = x := by
    have : CompactSpace (closedBall a r) := isCompact_iff_compactSpace.mp hK
    have hce : Topology.IsClosedEmbedding ((closedBall a r).domRestrict f) :=
      hc.domRestrict.isClosedEmbedding hi.injective
    obtain ⟨G, hG⟩ := ContinuousMap.exists_extension' hce ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨G, fun x hx => congrFun hG ⟨x, hx⟩⟩
  have hGa : G (f a) = a := hGf a (mem_closedBall_self hr.le)
  by_contra hno

  obtain ⟨ρ3, hρ3, hρG⟩ := Metric.continuousAt_iff.mp G.continuous.continuousAt (r / 4) (by positivity)
  obtain ⟨ρ, hρ, hρlt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < ρ3 := ⟨ρ3 / 3, by positivity, by linarith⟩
  have hGnear : ∀ y, dist y (f a) ≤ 2 * ρ → dist (G y) a < r / 4 := fun y hy => by
    have h1 := hρG (show dist y (f a) < ρ3 by linarith)
    rwa [hGa] at h1

  obtain ⟨c, hcball, hcK⟩ : ∃ c, dist c (f a) < ρ ∧ c ∉ f '' closedBall a r := by
    by_contra! hall
    exact hno (mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨ρ, hρ, fun c hc => hall c (mem_ball.1 hc)⟩))
  have hfK : IsCompact (f '' closedBall a r) := hK.image_of_continuousOn hc
  have hS1c : IsCompact (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) :=
    hfK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hSc : IsCompact ((f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ) :=
    hS1c.union (isCompact_sphere c ρ)

  have hS1pos : ∀ y ∈ f '' closedBall a r ∩ {y | ρ ≤ dist y c}, 0 < dist (G y) a := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    rw [hGf x hx, dist_pos]
    intro hxa
    subst hxa
    rw [mem_ofPred_eq, dist_comm] at hy
    linarith
  obtain ⟨δ0, hδ0, hδ0le⟩ :=
    exists_pos_le hS1c (G.continuous.dist continuous_const).continuousOn hS1pos
  obtain ⟨δ, hδ, hδδ0, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ r / 4 :=
    ⟨min δ0 (r / 4), lt_min hδ0 (by positivity), min_le_left _ _, min_le_right _ _⟩

  obtain ⟨P, hPd, hPS⟩ := exists_differentiable_near hSc G G.continuous (half_pos hδ)
  obtain ⟨v, hv, hPv⟩ := exists_small_avoid hPd c a hρ (half_pos hδ)
  have hQG : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ,
      ‖P y - v - G y‖ < δ := fun y hy => by
    have h1 := hPS y hy
    calc ‖P y - v - G y‖ = ‖(P y - G y) - v‖ := by congr 1; abel
      _ ≤ ‖P y - G y‖ + ‖v‖ := norm_sub_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 hv
      _ = δ := add_halves δ
  have hQne : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ, P y - v ≠ a := by
    rintro y (hy | hy) hQa
    · have h1 := hQG y (Or.inl hy)
      have h2 := hδ0le y hy
      rw [hQa, norm_sub_rev] at h1
      rw [dist_eq_norm] at h2
      linarith
    · exact hPv y hy (eq_add_of_sub_eq hQa)

  have hfc : ∀ x ∈ closedBall a r, f x ≠ c := fun x hx h => hcK ⟨x, hx, h⟩
  have hΦS : ∀ x ∈ closedBall a r,
      radialPush c ρ (f x) ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ := by
    intro x hx
    by_cases hle : ρ ≤ dist (f x) c
    · rw [radialPush_of_le hρ hle]
      exact Or.inl ⟨⟨x, hx, rfl⟩, hle⟩
    · exact Or.inr (radialPush_mem_sphere (not_le.1 hle) (hfc x hx))
  have hΦc : ContinuousOn (fun x => radialPush c ρ (f x)) (closedBall a r) :=
    (continuousOn_radialPush c ρ).comp hc (fun x hx => hfc x hx)
  have hPΦ : ContinuousOn (fun x => P (radialPush c ρ (f x))) (closedBall a r) :=
    hPd.continuous.comp_continuousOn hΦc
  have hH : ContinuousOn (fun x => x - (P (radialPush c ρ (f x)) - v - a)) (closedBall a r) := by
    have h1 := (hPΦ.sub (continuousOn_const (c := v))).sub (continuousOn_const (c := a))
    exact continuousOn_id.sub h1

  obtain ⟨x, hxK, hfix⟩ := brouwer_closedBall hB (a := a) hr
    (h := fun x => x - (P (radialPush c ρ (f x)) - v - a)) hH (by
      intro x hx
      have hGx : G (f x) = x := hGf x hx
      rw [mem_closedBall, dist_eq_norm]
      show ‖x - (P (radialPush c ρ (f x)) - v - a) - a‖ ≤ r
      by_cases hle : ρ ≤ dist (f x) c
      · rw [radialPush_of_le hρ hle]
        have h1 := hQG (f x) (Or.inl ⟨⟨x, hx, rfl⟩, hle⟩)
        rw [hGx] at h1
        calc ‖x - (P (f x) - v - a) - a‖ = ‖-(P (f x) - v - x)‖ := by congr 1; abel
          _ = ‖P (f x) - v - x‖ := norm_neg _
          _ ≤ r := by linarith
      · have hzS := radialPush_mem_sphere (not_le.1 hle) (hfc x hx)
        have hxa : dist x a < r / 4 := by
          rw [← hGx]
          apply hGnear
          calc dist (f x) (f a) ≤ dist (f x) c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith [not_le.1 hle]
        generalize radialPush c ρ (f x) = z at hzS ⊢
        have h1 := hQG z (Or.inr hzS)
        have hza : dist (G z) a < r / 4 := by
          apply hGnear
          have hzc : dist z c = ρ := mem_sphere.mp hzS
          calc dist z (f a) ≤ dist z c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith
        rw [dist_eq_norm] at hxa hza
        calc ‖x - (P z - v - a) - a‖ = ‖(x - a) - (P z - v - G z) - (G z - a)‖ := by congr 1; abel
          _ ≤ ‖(x - a) - (P z - v - G z)‖ + ‖G z - a‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + ‖P z - v - G z‖ + ‖G z - a‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ r := by linarith)
  exact hQne _ (hΦS x hxK) (sub_eq_zero.mp (sub_eq_self.mp hfix))

theorem proof (hB : BrouwerFixedPoint.Statement) : InvarianceOfDomain.Statement := by
  intro n U f hU hc hi
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have h := mem_interior_image hB (half_pos hr) (hc.mono hsub) (hi.mono hsub)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp h)
    (Set.image_mono hsub)

end InvarianceOfDomain

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGridProductLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology MvPolynomial

theorem GridProductLowerBound.exists_grid_prod_ne_zero {σ : Type} [Fintype σ] {N k : ℕ} (hk : k ≤ N)
    (v : Fin k → σ → ℂ) (hv : ∀ m, v m ≠ 0) :
    ∃ u : σ → Fin (N + 1), ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i ≠ 0 := by
  classical
  set P : MvPolynomial σ ℂ := ∏ m, ∑ i, X i * C (v m i) with hP
  have hlin : ∀ m, ∑ i, X i * C (v m i) ≠ (0 : MvPolynomial σ ℂ) := by
    intro m h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hv m)
    have := congrArg (eval (Pi.single i 1)) h
    simp [Pi.single_apply] at this
    exact hi this
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun m _ => hlin m
  let S : σ → Finset ℂ := fun _ => Finset.univ.image fun j : Fin (N + 1) => ((j : ℕ) : ℂ)
  have hS : ∀ i, (S i).card = N + 1 := fun i => by
    simp only [S]
    rw [Finset.card_image_of_injective _ fun a b h => Fin.ext (by exact_mod_cast h)]
    simp
  have htot : P.totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ m, (∑ i, X i * C (v m i) : MvPolynomial σ ℂ).totalDegree ≤ ∑ _m : Fin k, 1 :=
          Finset.sum_le_sum fun m _ => totalDegree_finsetSum_le fun j _ =>
            (totalDegree_mul _ _).trans (by simp [totalDegree_X, totalDegree_C])
      _ = k := by simp
  have hdeg : ∀ i, P.degreeOf i < (S i).card := fun i => by
    rw [hS i]
    exact Nat.lt_succ_of_le (((degreeOf_le_totalDegree _ _).trans htot).trans hk)
  by_contra hne
  push Not at hne
  refine hP0 (eq_zero_of_eval_zero_at_prod_finset P S hdeg fun x hx => ?_)
  choose u _ hu using fun i => Finset.mem_image.1 (hx i)
  have := hne u
  simp only [hu] at this
  simpa [hP, map_prod] using this

theorem GridProductLowerBound.proof : GridProductLowerBound.Statement := by
  classical
  intro σ _ N Z z₀ hZ hz₀
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε > 0, ∀ x ∈ Z, ε ≤ dist z₀ x := by
    rw [Metric.mem_closure_iff] at hz₀
    push Not at hz₀
    exact hz₀
  obtain ⟨R, hR⟩ := hZ.subset_closedBall z₀
  set K : Set (σ → ℂ) := Metric.closedBall 0 (R + ε / 2) \ Metric.ball 0 (ε / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hK0 : ∀ w ∈ K, w ≠ 0 := by
    rintro w hw rfl
    simp [hK, hε] at hw
  let g : (k : ℕ) → (Fin k → σ → ℂ) → ℝ := fun k v =>
    Finset.univ.sup' Finset.univ_nonempty fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖
  have hbd : ∀ k, ∃ μ > (0 : ℝ), k ≤ N → ∀ v ∈ Set.univ.pi (fun _ : Fin k => K), μ ≤ g k v := by
    intro k
    by_cases hk : k ≤ N
    · rcases (Set.univ.pi fun _ : Fin k => K).eq_empty_or_nonempty with he | hne
      · exact ⟨1, one_pos, fun _ v hv => by simp [he] at hv⟩
      have hgc : Continuous (g k) := Continuous.finset_sup'_apply
        (f := fun (u : σ → Fin (N + 1)) (v : Fin k → σ → ℂ) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖) _
        fun u _ => continuous_norm.comp (continuous_finsetProd _ fun m _ => continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).comp (continuous_apply m)))
      obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_univ_pi fun _ => hKc).exists_isMinOn hne hgc.continuousOn
      obtain ⟨u, hu⟩ := GridProductLowerBound.exists_grid_prod_ne_zero hk v₀
        fun m => hK0 _ (hv₀ m (Set.mem_univ _))
      exact ⟨g k v₀, (norm_pos_iff.2 hu).trans_le (Finset.le_sup' (fun u : σ → Fin (N + 1) =>
        ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v₀ m i‖) (Finset.mem_univ u)), fun _ v hv => isMinOn_iff.1 hmin v hv⟩
    · exact ⟨1, one_pos, fun h => absurd h hk⟩
  choose μf hμf0 hμf using hbd
  refine ⟨(Finset.range (N + 1)).inf' ⟨0, Finset.mem_range.2 N.succ_pos⟩ μf,
    (Finset.lt_inf'_iff _).2 fun k _ => hμf0 k, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro z hz s hs hcard
  set e := s.equivFin
  set v : Fin s.card → σ → ℂ := fun m => z - (e.symm m : σ → ℂ) with hvdef
  have hv : v ∈ Set.univ.pi fun _ : Fin s.card => K := by
    intro m _
    have hx := hs (e.symm m).2
    have h1 := hεZ _ hx
    have h2 := Metric.mem_closedBall.1 (hR hx)
    have h3 := Metric.mem_ball.1 hz
    have h4 := dist_triangle z₀ z (e.symm m : σ → ℂ)
    have h5 := dist_triangle z z₀ (e.symm m : σ → ℂ)
    rw [dist_comm z₀ z] at h4
    rw [dist_comm] at h2
    simp only [hK, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, hvdef, ← dist_eq_norm,
      not_lt]
    constructor <;> linarith
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun u : σ → Fin (N + 1) => ‖∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i‖)
  refine ⟨u, ?_⟩
  have hprod : ∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i) = ∏ m, ∑ i, ((u i : ℕ) : ℂ) * v m i := by
    rw [← Finset.prod_coe_sort, ← e.symm.prod_comp]
    rfl
  rw [hprod]
  have hle := (Finset.inf'_le μf (Finset.mem_range_succ_iff.2 hcard)).trans (hμf _ hcard v hv)
  simp only [g] at hle
  rwa [hu] at hle

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCompactHolomorphicFibreFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace CompactHolomorphicFibreFinite

theorem sum_normSq_sub {k : ℕ} (v p : Fin k → ℂ) :
    ∑ i, Complex.normSq (v i - p i) =
      ∑ i, Complex.normSq (v i) + ∑ i, Complex.normSq (p i) -
        2 * (∑ i, v i * (starRingEnd ℂ) (p i)).re := by
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_sub]

theorem proof (hCurve : NonIsolatedFibreCurve.Statement) : CompactHolomorphicFibreFinite.Statement := by
  intro k m U f y hU hf hZ
  set Z := {v | v ∈ U ∧ f v = y} with hZdef
  by_contra hinf
  have hD : derivedSet Z ⊆ Z := (isClosed_iff_derivedSet_subset Z).1 hZ.isClosed
  have hDc : IsCompact (derivedSet Z) := hZ.of_isClosed_subset (isClosed_derivedSet Z) hD
  obtain ⟨a, -, ha⟩ := hZ.isCountablyCompact.exists_accPt_of_infinite subset_rfl hinf
  let φ : (Fin k → ℂ) → ℝ := fun v => ∑ i, Complex.normSq (v i)
  have hφc : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact Complex.continuous_normSq.comp (continuous_apply i)
  obtain ⟨p, hpD, hpmax⟩ := hDc.exists_isMaxOn ⟨a, ha⟩ hφc.continuousOn
  have hpZ : p ∈ Z := hD hpD
  have hZeq : {v | v ∈ U ∧ f v = f p} = Z := by rw [hpZ.2]
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγZ⟩ :=
    hCurve k m U f p hU hf hpZ.1 (by rw [hZeq]; exact hpD)
  rw [hZeq] at hγZ

  have hγD : ∀ τ ∈ ball (0 : ℂ) r, γ τ ∈ derivedSet Z := by
    intro τ hτ
    rw [mem_derivedSet, accPt_iff_nhds]
    intro N hN
    have hτn : ball (0 : ℂ) r ∈ 𝓝 τ := isOpen_ball.mem_nhds hτ
    have hcont : ContinuousAt γ τ := hγd.continuousOn.continuousAt hτn
    have hev : ∀ᶠ s in 𝓝[≠] τ, (s ∈ ball (0 : ℂ) r ∧ γ s ∈ N) ∧ s ≠ τ :=
      (((show ∀ᶠ s in 𝓝 τ, s ∈ ball (0 : ℂ) r from hτn).and
        (show ∀ᶠ s in 𝓝 τ, γ s ∈ N from hcont hN)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨s, ⟨hs, hsN⟩, hne⟩ := hev.exists
    exact ⟨γ s, ⟨hsN, hγZ hs⟩, fun h => hne (hγi hs hτ h)⟩
  let h : ℂ → ℂ := fun τ => ∑ i, γ τ i * (starRingEnd ℂ) (p i)
  have hhd : DifferentiableOn ℂ h (ball 0 r) := by
    intro τ hτ
    refine DifferentiableWithinAt.fun_sum fun i _ => ?_
    exact (differentiableWithinAt_pi.1 (hγd τ hτ) i).mul_const _
  have hexp : ∀ τ, ∑ i, Complex.normSq (γ τ i - p i) = φ (γ τ) + φ p - 2 * (h τ).re :=
    fun τ => sum_normSq_sub (γ τ) p
  have hnn : ∀ τ, 0 ≤ ∑ i, Complex.normSq (γ τ i - p i) :=
    fun τ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hh0 : (h 0).re = φ p := by
    have e := hexp 0
    simp only [hγ0, sub_self, map_zero, Finset.sum_const_zero] at e
    linarith
  have hle : ∀ τ ∈ ball (0 : ℂ) r, (h τ).re ≤ φ p := by
    intro τ hτ
    have h1 : φ (γ τ) ≤ φ p := hpmax (hγD τ hτ)
    have h2 := hexp τ
    have h3 := hnn τ
    linarith
  have hmax : IsMaxOn (norm ∘ fun τ => Complex.exp (h τ)) (ball 0 r) 0 := by
    intro τ hτ
    simp only [Function.comp_apply, Complex.norm_exp]
    rw [hh0]
    exact Real.exp_le_exp.2 (hle τ hτ)
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) r).isPreconnected
    isOpen_ball hhd.cexp (mem_ball_self hr) hmax
  have hτ : ((r / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hre : (h ((r / 2 : ℝ) : ℂ)).re = φ p := by
    have e := congrArg (fun z : ℂ => ‖z‖) (hconst hτ)
    simp only [Function.const_apply, Complex.norm_exp] at e
    rw [← hh0]
    exact Real.exp_injective e
  have hzero : ∑ i, Complex.normSq (γ ((r / 2 : ℝ) : ℂ) i - p i) = 0 := by
    have h1 : φ (γ ((r / 2 : ℝ) : ℂ)) ≤ φ p := hpmax (hγD _ hτ)
    have h2 := hexp ((r / 2 : ℝ) : ℂ)
    have h3 := hnn ((r / 2 : ℝ) : ℂ)
    linarith
  have hγp : γ ((r / 2 : ℝ) : ℂ) = γ 0 := by
    rw [hγ0]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).1 hzero i
      (Finset.mem_univ i)
    exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 hi)
  have h0 := hγi hτ (mem_ball_self hr) hγp
  simp only [Complex.ofReal_eq_zero] at h0
  exact (half_pos hr).ne' h0

end CompactHolomorphicFibreFinite

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepWeightMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

theorem measurable_poincareDeepWeight' : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem integrableOn_inv_log_sq_mul :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by
  have hρ1 : Real.exp (-(Real.exp 1 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := Real.exp_pos 1; linarith)
  have hcont0 : ContinuousAt (fun r : ℝ => -(Real.log r)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun r : ℝ => -(Real.log r)⁻¹) ?_ ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact hcont0.continuousWithinAt
    · have hl : Real.log x ≠ 0 := (Real.log_neg h (hx.2.trans_lt hρ1)).ne
      exact ((Real.continuousAt_log h.ne').inv₀ hl).neg.continuousWithinAt
  · intro x hx
    have hl : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hρ1)).ne
    have hx0 : x ≠ 0 := hx.1.ne'
    have : HasDerivAt (fun r : ℝ => -(Real.log r)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0).inv hl).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring
  · intro x hx
    exact inv_nonneg.2 (mul_nonneg (sq_nonneg _) hx.1.le)

theorem ofReal_mul_poincareDeepWeight_le (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
  · rw [abs_of_pos hr]
    split_ifs with hc
    · have hl : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
      rw [hl] at hc
      have hlr : Real.log r < -(Real.exp 1 / 2) := by linarith
      have hl0 : Real.log r ≠ 0 := (hlr.trans (by have := Real.exp_pos 1; linarith)).ne
      rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2))) from ⟨hr, ((Real.log_lt_iff_lt_exp hr).1 hlr).le⟩), ← ENNReal.ofReal_mul hr.le, hl]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
      ring
    · simp

theorem lintegral_poincareDeepWeight_lt_top :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by
  set ρ := Real.exp (-(Real.exp 1 / 2))
  set h : ℝ → ENNReal := (Set.Ioc 0 ρ).indicator
    (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) with hh
  have hm : Measurable h := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.pow_const 2).mul measurable_id).inv.div_const 4)
  rw [← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (poincareDeepWeight (Complex.polarCoord.symm p))
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, h p.1 * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
        rw [polarCoord_target]
        refine lintegral_mono fun p => ?_
        simp only [poincareDeepWeight, Complex.norm_polarCoord_symm, smul_eq_mul, mul_one, hh]
        exact ofReal_mul_poincareDeepWeight_le p.1
    _ = (∫⁻ r in Set.Ioi 0, h r) * ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi, 1 := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hm.aemeasurable aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ ?_
        · refine (setLIntegral_le_lintegral _ _).trans_lt ?_
          rw [hh, lintegral_indicator measurableSet_Ioc]
          exact ((integrableOn_inv_log_sq_mul).div_const 4).lintegral_lt_top
        · rw [setLIntegral_one, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top

theorem TubeDeepWeightMass.proof : TubeDeepWeightMass.Statement := by
  intro d R
  set T : Set (Fin d → ℂ) := {w | ∀ i, ‖w i‖ ≤ R} with hTdef
  have hT : volume T < ⊤ := by
    have hsub : T ⊆ Metric.closedBall (0 : Fin d → ℂ) |R| := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => (hw i).trans (le_abs_self R)
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
  have hpre : {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R} =
      MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 ⁻¹' (Set.univ ×ˢ T) := by
    ext z
    simp [hTdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have key := e.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : ℂ × (Fin d → ℂ) => ENNReal.ofReal (poincareDeepWeight p.1) * (fun _ => (1 : ENNReal)) p.2)
    (Set.univ ×ˢ T)
  rw [hpre]
  simp only [mul_one] at key
  have h0 : ∀ z : Fin (d + 1) → ℂ, (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 z).1 = z 0 := fun z => rfl
  simp only [h0] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := (volume : Measure ℂ).restrict Set.univ)
    (ν := (volume : Measure (Fin d → ℂ)).restrict T)
    (ENNReal.measurable_ofReal.comp measurable_poincareDeepWeight').aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [mul_one, Function.comp_apply] at this
  rw [this, Measure.restrict_univ, setLIntegral_one]
  exact ENNReal.mul_lt_top lintegral_poincareDeepWeight_lt_top hT

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreTor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreTor.mem_of_smul_mem {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
  set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L
  rw [smul_eq_C_mul] at h
  have h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx
  have h2 : C (MvPolynomial.C (eval t u)) * x ∈ J := by
    have := J.sub_mem h h1
    rwa [← sub_mul, ← map_sub, sub_sub_cancel] at this
  have hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ)) :=
    (hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))
  exact (Ideal.unit_mul_mem_iff_mem J hunit).1 h2

theorem GenericFibreTor.proof (hGF : GenericFreeness.Statement.{0, 0, 0}) :
    GenericFibreTor.Statement := by
  classical
  intro σ _ ι _ L
  obtain ⟨F, hF0, hfree⟩ := hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
    (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  refine ⟨F, hF0, fun t ht x hx => ?_⟩
  rw [MvPolynomial.ker_map] at hx ⊢
  obtain ⟨hxL, hxI⟩ := Ideal.mem_inf.1 hx
  rw [MvPolynomial.mem_map_C_iff] at hxI
  have hflat' : Module.Flat (Localization.Away F)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    @Module.Flat.of_free _ _ _ _ _ hfree
  have hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F) := IsLocalization.flat _ (Submonoid.powers F)
  have : Module.Flat (MvPolynomial σ ℂ)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _
  let g := LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  let π := (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap
  let a : x.support → MvPolynomial σ ℂ := fun m => AddMonoidAlgebra.coeff x m.1
  let e : x.support → MvPolynomial ι (MvPolynomial σ ℂ) := fun m => monomial m.1 1
  have hsum : ∑ m, a m • e m = x := by
    calc ∑ m, a m • e m = ∑ m : x.support, monomial m.1 (AddMonoidAlgebra.coeff x m.1) :=
          Finset.sum_congr rfl fun m _ => by simp [a, e, smul_monomial]
      _ = x := by
          rw [Finset.sum_coe_sort x.support (fun v => monomial v (AddMonoidAlgebra.coeff x v))]
          exact (MvPolynomial.as_sum x).symm
  have hrel : ∑ m, a m • g (π (e m)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← map_smul, ← map_sum, hsum]
    simp [g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]
  have htriv : Module.IsTrivialRelation a (fun m => g (π (e m))) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, A, y, hy, hA⟩ := htriv
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y
  choose q hq using hb
  choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)
  have hm : ∀ m, ∃ c : Submonoid.powers F,
      c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j) := by
    intro m
    apply IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← hq j, ← hr j, map_smul, map_smul]
    rfl
  choose c hc using hm
  set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)
  have hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L := by
    intro m
    have h1 := hc m
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul] at h1
    have h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    have h3 := Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2
    convert h3 using 1
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rfl
  have hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this, hA j, mul_zero, zero_smul]
  have hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm]
  have hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
    rw [hkey]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)
  have hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0 := by
    rintro u ⟨n, rfl⟩
    rw [map_pow]
    exact pow_ne_zero n ht
  have hVb : V * b ∈ Submonoid.powers F :=
    (Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2
  exact GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionLocalUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem exists_forall_ne_zero_of_isOpen {E ι : Type} [TopologicalSpace E] (s : Finset ι)
    (G : ι → E → ℂ) (U : Set E) (hc : ∀ i ∈ s, ContinuousOn (G i) U)
    (hne : ∀ i ∈ s, ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, G i t ≠ 0) :
    ∀ W : Set E, IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, ∀ i ∈ s, G i t ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rintro W - - ⟨t, ht⟩
    exact ⟨t, ht, by simp⟩
  | insert a s ha ih =>
    intro W hWo hWU hW
    obtain ⟨t₀, ht₀W, ht₀⟩ := hne a (Finset.mem_insert_self a s) W hWo hWU hW
    have hW'o : IsOpen (W ∩ G a ⁻¹' {0}ᶜ) :=
      ((hc a (Finset.mem_insert_self a s)).mono hWU).isOpen_inter_preimage hWo isOpen_compl_singleton
    obtain ⟨t, ⟨htW, hta⟩, hts⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi)) _ hW'o (Set.inter_subset_left.trans hWU)
      ⟨t₀, ht₀W, ht₀⟩
    refine ⟨t, htW, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hta
    · exact hts i hi

theorem ProperOpenProjectionLocalUnbranched.proof (hFin : CompactHolomorphicFibreFinite.Statement)
    (hLoc : IsolatedFibreLocalUnbranched.Statement) : ProperOpenProjectionLocalUnbranched.Statement := by
  classical
  intro σ _ X B k f d A D hB hf hXB hD hAD hprop hopen y₀ hy₀
  have zerosX : ∀ z, z ∈ X ∩ B → ∀ i, f i z = 0 := fun z hz => by
    rw [hXB] at hz
    exact hz.2
  have memX : ∀ z, z ∈ B → (∀ i, f i z = 0) → z ∈ X ∩ B := fun z hz h0 => by
    rw [hXB]
    exact ⟨hz, h0⟩

  set F := {x | x ∈ X ∩ B ∧ A x = y₀} with hF
  have hFc : IsCompact F := by
    have := hprop {y₀} (Set.singleton_subset_iff.2 hy₀) isCompact_singleton
    simpa only [Set.mem_singleton_iff] using this

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U₀ : Set (Fin n → ℂ) := L.symm ⁻¹' B with hU₀
  set Φ : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hΦ
  set yv : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) y₀ with hyv
  have hU₀o : IsOpen U₀ := hB.preimage L.symm.continuous
  have hΦd : DifferentiableOn ℂ Φ U₀ := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hΦ, Fin.append_left]
      exact (hf i).differentiableOn.comp L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hΦ, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U₀ ∧ Φ v = yv} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU₀, hF, hΦ, hyv]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨memX _ hv fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, hA⟩
      refine ⟨hv.2, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [zerosX _ hv i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U₀ ∧ Φ v = yv} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U₀ Φ yv hU₀o hΦd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  have hloc : ∀ x ∈ F, ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), IsOpen M ∧ x ∈ M ∧
      AnalyticAt ℂ g y₀ ∧ (¬ ∀ᶠ t in 𝓝 y₀, g t = 0) ∧
      ∀ z ∈ X ∩ B ∩ M, g (A z) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O := by
    intro x hx
    have hiso : ∃ W ∈ 𝓝 x, ∀ x' ∈ X ∩ B ∩ W, A x' = A x → x' = x := by
      refine ⟨(F \ {x})ᶜ, hFfin.sdiff.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl, ?_⟩
      rintro x' ⟨hx'XB, hx'W⟩ hx'A
      by_contra hne
      exact hx'W ⟨⟨hx'XB, hx'A.trans hx.2⟩, hne⟩
    obtain ⟨M, g, hM, hg, hg0, hsec⟩ := hLoc σ X B k f d A hB hf hXB hopen x hx.1 hiso
    rw [hx.2] at hg hg0
    exact ⟨interior M, g, isOpen_interior, mem_interior_iff_mem_nhds.2 hM, hg, hg0,
      fun z hz => hsec z ⟨hz.1, interior_subset hz.2⟩⟩
  choose! M g hMo hxM hga hgne hsec using hloc
  set s := hFfin.toFinset with hs
  have hsF : ∀ x, x ∈ s ↔ x ∈ F := fun x => hFfin.mem_toFinset

  obtain ⟨r₀, hr₀, hr₀D⟩ := nhds_basis_closedBall.mem_iff.1 (hD.mem_nhds hy₀)
  set Mall := ⋃ x ∈ F, M x with hMall
  have hMallo : IsOpen Mall := isOpen_biUnion fun x hx => hMo x hx
  set C := {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ r₀} \ Mall with hC
  have hCc : IsCompact C := (hprop _ hr₀D (isCompact_closedBall y₀ r₀)).diff hMallo
  have hAC : y₀ ∉ A '' C := by
    rintro ⟨c, ⟨⟨hcXB, -⟩, hcM⟩, hcA⟩
    exact hcM (Set.mem_biUnion (show c ∈ F from ⟨hcXB, hcA⟩) (hxM c ⟨hcXB, hcA⟩))
  have hev : ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ ∧ t ∉ A '' C ∧ ∀ x ∈ s, AnalyticAt ℂ (g x) t := by
    refine (show ∀ᶠ t in 𝓝 y₀, t ∈ ball y₀ r₀ from ball_mem_nhds y₀ hr₀).and
      ((show ∀ᶠ t in 𝓝 y₀, t ∉ A '' C from
        ((hCc.image A.continuous).isClosed.isOpen_compl).mem_nhds hAC).and ?_)
    exact (Filter.eventually_all_finset s).2 fun x hx => (hga x ((hsF x).1 hx)).eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hgan : ∀ x ∈ s, AnalyticOnNhd ℂ (g x) (ball y₀ r) := fun x hx t ht => (hball t ht).2.2 x hx
  refine ⟨ball y₀ r, fun t => ∏ x ∈ s, g x t, isOpen_ball, mem_ball_self hr, ?_,
    Finset.analyticOnNhd_fun_prod s hgan, ?_, ?_⟩
  · intro t ht
    exact hr₀D (ball_subset_closedBall (hball t ht).1)
  · intro W hWo hWU hW
    have hne : ∀ x ∈ s, ∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ ball y₀ r → W.Nonempty →
        ∃ t ∈ W, g x t ≠ 0 := by
      intro x hx W hWo hWU hW
      by_contra hcon
      push Not at hcon
      obtain ⟨t, htW⟩ := hW
      have hzt : g x =ᶠ[𝓝 t] 0 := by
        filter_upwards [hWo.mem_nhds htW] with u hu using hcon u hu
      have hEq := (hgan x hx).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball y₀ r).isPreconnected (hWU htW) hzt
      exact hgne x ((hsF x).1 hx) (by
        filter_upwards [ball_mem_nhds y₀ hr] with u hu using hEq hu)
    obtain ⟨t, htW, ht⟩ := exists_forall_ne_zero_of_isOpen s g (ball y₀ r)
      (fun x hx => (hgan x hx).continuousOn) hne W hWo hWU hW
    exact ⟨t, htW, Finset.prod_ne_zero_iff.2 ht⟩
  · intro y hyU hgy x' hx'XB hx'A
    have hx'M : x' ∈ Mall := by
      by_contra hn
      refine (hball y hyU).2.1 ⟨x', ⟨⟨hx'XB, ?_⟩, hn⟩, hx'A⟩
      rw [hx'A]
      exact ball_subset_closedBall (hball y hyU).1
    obtain ⟨x, hxF, hx'x⟩ := Set.mem_iUnion₂.1 hx'M
    have hgx : g x (A x') ≠ 0 := by
      rw [hx'A]
      exact Finset.prod_ne_zero_iff.1 hgy x ((hsF x).2 hxF)
    exact hsec x hxF x' ⟨hx'XB, hx'x⟩ hgx

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
