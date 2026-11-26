module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmGood
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullOmEquiv
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omEquiv :
    OmEquiv := by
  intro Γ V S _ _ _ _ d G W hW q γ
  have hρρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := fun x => by simpa using G.ρ_inv_apply γ⁻¹ x
  have hσ : ∀ s, G.σ γ (G.σ γ⁻¹ s) = s := fun s => by simp
  have hout : ∀ p, p ∉ G.Y → G.ρ γ⁻¹ p ∉ G.Y := fun p hp h => hp (by simpa [hρρ] using G.maps γ _ h)
  have heq : ∀ s, ∀ p ∈ G.Y, W s (G.ρ γ p) = G.ρ γ (W (G.σ γ⁻¹ s) p) := fun s p hp => by
    have := hW.equiv γ (G.σ γ⁻¹ s) p hp
    rwa [hσ] at this
  have hnat := fun s => pbNat V (Fin d → ℂ) G.Y G.isOpen (G.ρ γ) (mulVecL (G.ξ γ)) (W (G.σ γ⁻¹ s)) (W s)
    (hW.field _) (hW.field s) (G.maps γ) (heq s) q
  have hrel : ∀ (k : ℕ) (w : G.Om k) (s : S), ∀ p ∈ G.Y, ∀ v : Fin k → V,
      ((G.act k γ w).1 s (G.ρ γ p)) (fun i => G.ρ γ (v i)) = mulVecL (G.ξ γ) (w.1 (G.σ γ⁻¹ s) p v) := by
    intro k w s p hp v
    simp only [Geo.act_apply, mulVecL_apply, Geo.ρ_inv_apply]
  have hz : ∀ (k : ℕ) (w : G.Om k) (s : S) (p : V), p ∉ G.Y → w.1 s p = 0 :=
    fun k w s p hp => (w.2 s).2 p hp
  have hsm := fun (k : ℕ) (w : G.Om k) (s : S) => (w.2 s).1
  obtain ⟨hA, hB⟩ := omApply Γ V S d G W hW q
  refine ⟨fun w => ?_, fun w => ?_⟩
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hA w _ _ hp', hA (G.act q γ w) s p hp]
      have := (hnat s).1 (w.1 (G.σ γ⁻¹ s)) ((G.act q γ w).1 s) (hrel q w s) 1 ⟨zero_le_one, le_rfl⟩
        (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hB w _ _ hp', hB (G.act (q + 1) γ w) s p hp]
      have := ((hnat s).2 (w.1 (G.σ γ⁻¹ s)) ((G.act (q + 1) γ w).1 s) (hrel (q + 1) w s)).2
        (hsm _ w _) (hsm _ _ s) (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbBasic
open UpperTheory.V.Lit.Geo

private theorem UpperTheory.V.Lit.Geo.euler_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (hd : DifferentiableAt ℝ W p) (hh : ∀ t : ℝ, 0 < t → W (t • p) = t • W p) (t : ℝ) :
    fderiv ℝ (flow W t) p p = flow W t p := by
  have hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1 :=
    hp1.comp_hasDerivAt (1 : ℝ) hr
  have h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1 := by
    have hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const (W p)
    rw [one_smul] at hl
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hh s hs
  have heul : fderiv ℝ W p p = W p := by
    have := h1.unique h2
    rwa [one_smul] at this
  have hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)
  rw [hf.fderiv]
  simp [flow, heul]

theorem UpperTheory.V.Lit.Geo.pbBasic :
    PbBasic := by
  intro V F _ _ _ _ _ _ Y hY W hW hh q
  have hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p := fun p hp =>
    (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p := fun p hp t =>
    euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t
  refine ⟨fun w hw => ?_, fun w _ hw => ?_⟩
  · intro p hp v i hi
    rw [pb_apply]
    apply hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i
    simp [hi, he p hp]
  · intro p hp v i hi
    have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0 := by
      intro t ht
      rw [hk_apply]
      apply hw (flow W t p) (hW.2 p hp t ht) _ i.succ
      simp [hi, he p hp]
    show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0
    by_cases hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1
    · have hc := (ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint
      simp only [ContinuousAlternatingMap.apply_apply] at hc
      rw [← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht
    · rw [intervalIntegral.integral_undef hint]
      rfl
end

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omGood :
    OmGood := by
  intro Γ V S _ _ _ _ d G W hW q
  have hsub : ∀ (q : ℕ) (w w' : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → (∀ s, RadBasic G.Y (w'.1 s)) →
      ∀ s, RadBasic G.Y ((w - w').1 s) := by
    intro q w w' h h' s p hp v i hi
    have e : (w - w').1 s p v = w.1 s p v - w'.1 s p v := rfl
    rw [e, h s p hp v i hi, h' s p hp v i hi, sub_self]
  have hpb : ∀ (q : ℕ) (w : G.Om q), (∀ s, RadBasic G.Y (w.1 s)) → ∀ s, RadBasic G.Y ((pbOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).1 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).1 _ (h s) p hp v i hi
  have hhom : ∀ (q : ℕ) (w : G.Om (q + 1)), (∀ s, RadBasic G.Y (w.1 s)) →
      ∀ s, RadBasic G.Y ((homOm G W w).1 s) := by
    intro q w h s p hp v i hi
    rw [(omApply Γ V S d G W hW q).2 w s p hp]
    exact (pbBasic V _ G.Y G.isOpen (W s) (hW.field s) (hW.homog s) q).2 _ (w.2 s).1 (h s) p hp v i hi
  obtain ⟨h1, h2, -, h4⟩ := omHom Γ V S d G W hW
  refine ⟨fun w hw => ⟨⟨fun γ => ?_, hpb q w hw.basic, ?_⟩, ⟨fun γ => ?_, hw.dbasic, ?_⟩⟩,
    fun w w' hw hw' => ⟨fun γ => ?_, hsub q w w' hw.basic hw'.basic, ?_⟩,
    fun w hw => ⟨fun γ => ?_, hhom q w hw.basic, ?_⟩⟩
  · rw [(omEquiv Γ V S d G W hW q γ).1 w, hw.inv γ]
  · rw [h1]
    exact hpb _ _ hw.dbasic
  · rw [← dEquiv Γ V S d G q γ w, hw.inv γ]
  · rw [h2]
    intro s p _ v i _
    rfl
  · rw [map_sub, hw.inv γ, hw'.inv γ]
  · rw [map_sub]
    exact hsub _ _ _ hw.dbasic hw'.dbasic
  · rw [(omEquiv Γ V S d G W hW q γ).2 w, hw.inv γ]
  · rw [eq_sub_of_add_eq (h4 q w).symm]
    exact hsub _ _ _ (hsub _ _ _ (hpb _ _ hw.basic) hw.basic) (hhom _ _ hw.dbasic)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

private theorem hv_coord (E : Type) [Field E] [NumberField E] (a : ℕ) :
    ∃ L : Fin a × Fin a × InfinitePlace E → ℂ →L[ℝ] HV E a,
      ∀ v : HV E a, v = ∑ n ∈ Finset.univ, L n (v.1 n.1 n.2.1 n.2.2) := by
  classical
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  refine ⟨fun n => LinearMap.toContinuousLinearMap (P ∘ₗ LinearMap.single ℝ (fun _ => Fin a → Cinf E) n.1 ∘ₗ
    LinearMap.single ℝ (fun _ => Cinf E) n.2.1 ∘ₗ LinearMap.single ℝ (fun _ => ℂ) n.2.2), fun v => ?_⟩
  have h1 : P v.1 = v := LinearMap.congr_fun hP v
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  refine h1.symm.trans (congrArg P ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.sum_prod_type, ← map_sum]
  simp only [LinearMap.coe_single, Finset.univ_sum_single]

theorem UpperTheory.V.Lit.Geo.Cs.zwSz :
    ZwSz := by
  intro E _ _ _ a U Y C hY W hW k
  obtain ⟨B, -, hB⟩ := fieldDer E a U Y C hY
  obtain ⟨τ, h1, hτ, -, hs, -, he⟩ := secOne E a
  obtain ⟨L, hL⟩ := hv_coord E a
  choose φ hφ hb using hY.sm
  have e1 : toL (τ (hOne E a)).val = oneL E a := by rw [h1]; rfl
  have hc : ∀ i j w, ∃ c : ℝ, 0 ≤ c ∧ ∀ g, Sz k (chart (φ i j w).1 g) (oneL E a) (c * 1) := fun i j w => by
    refine chartSz E a k (fun _ => 1) (fun _ => zero_le_one) (φ i j w) fun l => ?_
    rcases l with _ | ⟨X, l⟩
    · refine ⟨B, fun g => ?_⟩
      rw [mul_one]
      change ‖(φ i j w).1 g‖ ≤ B
      rw [hφ]
      refine le_trans ?_ (hB g).1
      exact ((norm_le_pi_norm (toL (Y g).1 i j) w).trans (norm_le_pi_norm (toL (Y g).1 i) j)).trans
        (norm_le_pi_norm (toL (Y g).1) i)
    · obtain ⟨c, hc⟩ := hb i j w X l
      exact ⟨c, fun g => by rw [mul_one]; exact hc g⟩
  choose c _ hc using hc
  obtain ⟨b₁, hb₁⟩ := exists_sz k (fun p => toL (τ p).val) (hOne E a)
  obtain ⟨b₂, hb₂⟩ := exists_sz k (fun p => sand (τ p)) (hOne E a)
  obtain ⟨D, -, hD⟩ := compSz (HV E a) (Lie E a) ℂ k b₁
  refine ⟨2 ^ k * b₂ * ∑ n ∈ Finset.univ, ‖L n‖ * (D * (c n.1 n.2.1 n.2.2 * 1)), fun g x => ?_⟩
  have s0 : ∀ i j w, ContDiffAt ℝ ∞ (chart (φ i j w).1 (pt g x)) (toL (τ (hOne E a)).val) := fun i j w =>
    contDiffAt_chart (φ i j w).2 _ (val_mem_invSet _)
  have s1 : ∀ i j w, ContDiffAt ℝ ∞ (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) := fun i j w =>
    ContDiffAt.comp (g := chart (φ i j w).1 (pt g x)) (f := fun p => toL (τ p).val) (hOne E a) (s0 i j w) hτ
  have z1 : ∀ i j w, Sz k (fun p => chart (φ i j w).1 (pt g x) (toL (τ p).val)) (hOne E a) (D * (c i j w * 1)) :=
    fun i j w => hD _ (fun p => toL (τ p).val) _ _ hτ (s0 i j w) (fun m _ hm => hb₁ m hm) (by rw [e1]; exact hc i j w _)
  have s2 : ∀ n : Fin a × Fin a × InfinitePlace E,
      ContDiffAt ℝ ∞ (fun p => L n (chart (φ n.1 n.2.1 n.2.2).1 (pt g x) (toL (τ p).val))) (hOne E a) := fun n =>
    (L n).contDiff.contDiffAt.comp (hOne E a) (s1 _ _ _)
  have z2 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).2.2 _ Finset.univ _ _ (fun n _ => s2 n)
    (fun n _ => (appSz (HV E a) ℂ (HV E a) k (hOne E a)).2.1 (L n) _ _ (s1 n.1 n.2.1 n.2.2) (z1 _ _ _))
  have z3 := (appSz (HV E a) (HV E a) (HV E a) k (hOne E a)).1 _ _ _ _ hs (ContDiffAt.sum fun n _ => s2 n) hb₂ z2
  refine z3.congr (he.mono fun p hp => ?_)
  have e2 := hW (g * τ p) x
  have e3 : sand (g * τ p) (hOne E a) = sand g p := by rw [map_mul, ContinuousLinearMap.mul_apply, hp]
  rw [e3] at e2
  simp only [chart_val, hφ, Zw, e2, ← pt_mul]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  exact congrArg _ (hL (hv (Y (pt (g * τ p) x)))).symm
end
