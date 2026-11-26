module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreSectionsCovering
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology Matrix

theorem FibreSectionsCovering.proof : FibreSectionsCovering.Statement := by
  intro n e N A Ω X hX hfib hsec
  let f : X → Ω := Set.MapsTo.restrict _ X Ω hX
  show IsCoveringMap f
  have hAc : Continuous (fun x : Fin n → ℂ => A *ᵥ x) :=
    (Matrix.mulVecLin A).continuous_of_finiteDimensional
  choose O V' g hO hAO hV' hxV' hg hgx hAg hXV' using hsec

  have key : ∀ x₀ (h₀ : x₀ ∈ X) x, x ∈ X → x ∈ V' x₀ h₀ → g x₀ h₀ (A *ᵥ x) = x := by
    intro x₀ h₀ x hx hxv
    have hx' : x ∈ g x₀ h₀ '' O x₀ h₀ := hXV' x₀ h₀ ▸ ⟨hx, hxv⟩
    obtain ⟨o, ho, rfl⟩ := hx'
    rw [hAg x₀ h₀ o ho]

  have inX : ∀ x₀ (h₀ : x₀ ∈ X) w, w ∈ O x₀ h₀ → g x₀ h₀ w ∈ X ∧ g x₀ h₀ w ∈ V' x₀ h₀ := by
    intro x₀ h₀ w hw
    have h : g x₀ h₀ w ∈ X ∩ V' x₀ h₀ := hXV' x₀ h₀ ▸ ⟨w, hw, rfl⟩
    exact h
  rcases Nat.eq_zero_or_pos N with hN | hN
  · have : IsEmpty X := by
      refine ⟨fun x => ?_⟩
      have h := hfib _ (hX x.2)
      rw [hN, Nat.cast_zero, Set.encard_eq_zero] at h
      have hm : (x : Fin n → ℂ) ∈ {x' | x' ∈ X ∧ A *ᵥ x' = A *ᵥ (x : Fin n → ℂ)} := ⟨x.2, rfl⟩
      rw [h] at hm
      exact hm
    exact IsCoveringMap.of_isEmpty _
  intro y

  have hFenc : {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)}.encard = N := hfib y y.2
  have hFfin := Set.finite_of_encard_eq_coe hFenc
  have := hFfin.to_subtype
  have hFcard : Nat.card {x | x ∈ X ∧ A *ᵥ x = (y : Fin (e + 1) → ℂ)} = N := by
    rw [Nat.card_coe_set_eq, Set.ncard_def, hFenc]
    rfl
  let eq := (Finite.equivFinOfCardEq hFcard).symm
  let pt : Fin N → Fin n → ℂ := fun i => (eq i : Fin n → ℂ)
  have pt_mem : ∀ i, pt i ∈ X ∧ A *ᵥ pt i = y := fun i => (eq i).2
  have pt_inj : Function.Injective pt := fun i j h => eq.injective (Subtype.ext h)
  let G : Fin N → (Fin (e + 1) → ℂ) → Fin n → ℂ := fun i => g (pt i) (pt_mem i).1
  let OO : Fin N → Set (Fin (e + 1) → ℂ) := fun i => O (pt i) (pt_mem i).1
  let VV : Fin N → Set (Fin n → ℂ) := fun i => V' (pt i) (pt_mem i).1
  have hGy : ∀ i, G i y = pt i := fun i => by
    rw [← (pt_mem i).2]
    exact hgx (pt i) (pt_mem i).1
  have hOy : ∀ i, OO i ∈ 𝓝 (y : Fin (e + 1) → ℂ) := fun i =>
    (hO _ _).mem_nhds (by have h : A *ᵥ pt i ∈ OO i := hAO _ _; rwa [(pt_mem i).2] at h)
  have hGc : ∀ i, ∀ w ∈ OO i, ContinuousAt (G i) w := fun i w hw =>
    (hg _ _).continuousOn.continuousAt ((hO _ _).mem_nhds hw)
  have hS : ∀ᶠ w in 𝓝 (y : Fin (e + 1) → ℂ), (∀ i, w ∈ OO i) ∧ ∀ i j, i ≠ j → G i w ≠ G j w := by
    refine (Filter.eventually_all.2 hOy).and
      (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_)
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ h => absurd hij h
    · have hne : G i y ≠ G j y := by
        rw [hGy, hGy]
        exact fun h => hij (pt_inj h)
      exact (((hGc i y (mem_of_mem_nhds (hOy i))).ne_iff_eventually_ne
        (hGc j y (mem_of_mem_nhds (hOy j)))).1 hne).mono fun _ hw _ => hw
  obtain ⟨W, hWS, hWo, hyW⟩ := mem_nhds_iff.1 hS
  have hWO : ∀ i, ∀ w ∈ W, w ∈ OO i := fun i w hw => (hWS hw).1 i
  have hWd : ∀ w ∈ W, ∀ i j, i ≠ j → G i w ≠ G j w := fun w hw => (hWS hw).2
  have hGX : ∀ i, ∀ w ∈ W, G i w ∈ X := fun i w hw => (inX _ _ w (hWO i w hw)).1
  have hGV : ∀ i, ∀ w ∈ W, G i w ∈ VV i := fun i w hw => (inX _ _ w (hWO i w hw)).2
  have hAG : ∀ i, ∀ w ∈ W, A *ᵥ G i w = w := fun i w hw => hAg _ _ w (hWO i w hw)
  have hfc : Continuous f := (hAc.comp continuous_subtype_val).subtype_mk fun x => hX x.2
  have hres : ∀ i (q : Ω) (hq : (q : Fin (e + 1) → ℂ) ∈ W),
      f ⟨G i q, hGX i q hq⟩ = q := fun i q hq =>
    Subtype.ext (hAG i q hq)
  let V : Set Ω := {p | (p : Fin (e + 1) → ℂ) ∈ W}
  let U : Fin N → Set X := fun i => {x | (x : Fin n → ℂ) ∈ VV i ∧ A *ᵥ (x : Fin n → ℂ) ∈ W}
  have hVo : IsOpen V := continuous_subtype_val.isOpen_preimage _ hWo
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    continuous_subtype_val.isOpen_preimage _ ((hV' _ _).inter (hWo.preimage hAc))

  have hUG : ∀ i (x : X), x ∈ U i → G i (A *ᵥ (x : Fin n → ℂ)) = x := fun i x hx =>
    key _ _ _ x.2 hx.1
  have open_iff : ∀ i {W' : Set Ω}, W' ⊆ V → (IsOpen W' ↔ IsOpen (f ⁻¹' W' ∩ U i)) := by
    intro i W' hW'V
    refine ⟨fun h => (hfc.isOpen_preimage _ h).inter (hUo i), fun h => ?_⟩
    obtain ⟨T', hT'o, hT'eq⟩ := isOpen_induced_iff.1 h
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpW : (p : Fin (e + 1) → ℂ) ∈ W := hW'V hp
    have hGp : G i p ∈ T' := by
      have hm : (⟨G i p, hGX i p hpW⟩ : X) ∈ f ⁻¹' W' ∩ U i := by
        refine ⟨?_, hGV i p hpW, ?_⟩
        · show f ⟨G i p, hGX i p hpW⟩ ∈ W'
          rw [hres i p hpW]
          exact hp
        · show A *ᵥ G i p ∈ W
          rw [hAG i p hpW]
          exact hpW
      rw [← hT'eq] at hm
      exact hm
    rw [mem_nhds_subtype]
    refine ⟨W ∩ G i ⁻¹' T', Filter.inter_mem (hWo.mem_nhds hpW)
      ((hGc i p (hWO i p hpW)).preimage_mem_nhds (hT'o.mem_nhds hGp)), ?_⟩
    rintro q ⟨hqW, hqT⟩
    have hm : (⟨G i q, hGX i q hqW⟩ : X) ∈ Subtype.val ⁻¹' T' := hqT
    rw [hT'eq] at hm
    have h1 := hm.1
    rw [Set.mem_preimage, hres i q hqW] at h1
    exact h1
  have inj : ∀ i, (U i).InjOn f := by
    intro i x hx x' hx' hxx'
    have h : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (x' : Fin n → ℂ) := congrArg Subtype.val hxx'
    apply Subtype.ext
    rw [← hUG i x hx, ← hUG i x' hx', h]
  have surj : ∀ i, (U i).SurjOn f V := by
    intro i p hp
    refine ⟨⟨G i p, hGX i p hp⟩, ⟨hGV i p hp, ?_⟩, hres i p hp⟩
    show A *ᵥ G i p ∈ W
    rw [hAG i p hp]
    exact hp
  have disj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hxi hxj => ?_
    exact hWd _ hxi.2 i j hij ((hUG i x hxi).trans (hUG j x hxj).symm)
  have exh : f ⁻¹' V ⊆ ⋃ i, U i := by
    intro x hx
    have hxW : A *ᵥ (x : Fin n → ℂ) ∈ W := hx
    set w := A *ᵥ (x : Fin n → ℂ) with hw
    have hwΩ : w ∈ Ω := hX x.2
    have hFw := hfib w hwΩ
    have hsub : Set.range (fun i => G i w) ⊆ {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      rintro _ ⟨i, rfl⟩
      exact ⟨hGX i w hxW, hAG i w hxW⟩
    have hinj : Function.Injective (fun i => G i w) := by
      intro i j h
      by_contra hij
      exact hWd w hxW i j hij h
    have heq : Set.range (fun i => G i w) = {x' | x' ∈ X ∧ A *ᵥ x' = w} := by
      refine ((Set.finite_of_encard_eq_coe hFw).subset hsub).eq_of_subset_of_encard_le hsub ?_
      rw [hFw]
      rw [hinj.encard_range]
      simp
    have hxmem : (x : Fin n → ℂ) ∈ Set.range (fun i => G i w) := by
      rw [heq]
      exact ⟨x.2, rfl⟩
    obtain ⟨i, hi⟩ := hxmem
    refine Set.mem_iUnion.2 ⟨i, ?_, hxW⟩
    show (x : Fin n → ℂ) ∈ VV i
    rw [← hi]
    exact hGV i w hxW
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Ω → X) := ⟨fun _ => ⟨pt ⟨0, hN⟩, (pt_mem _).1⟩⟩
  let T := IsOpen.trivializationDiscrete (f := f) U V hVo open_iff inj surj disj exh
  have hyT : y ∈ T.baseSet := hyW
  exact (IsEvenlyCovered.of_trivialization hyT).to_isEvenlyCovered_preimage

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSeparateWeierstrassDivision
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CoeffEqZeroOfForallEvalEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ K : Fin N → Fin N → ℂ, ∀ (c : Fin N → ℂ) (t : ℂ),
      ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        ∑ i : Fin N, (∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  refine ⟨fun i j => a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ), fun c t => ?_⟩
  have hj : ∀ j : Fin N, (t + a) ^ (j : ℕ) =
      ∑ i : Fin N, t ^ (i : ℕ) * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ)) := by
    intro j
    have hr := Fin.sum_univ_eq_sum_range (fun i => t ^ i * (a ^ ((j : ℕ) - i) * ((j : ℕ).choose i : ℂ))) N
    rw [hr, add_pow]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 (show (j : ℕ) + 1 ≤ N by omega))]
    · exact Finset.sum_congr rfl fun i _ => by ring
    · intro i _ hi
      simp only [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  simp_rw [hj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_monic_shift_coeff (N : ℕ) (a : ℂ) :
    ∃ (K₀ : Fin N → ℂ) (K : Fin N → Fin N → ℂ), ∀ (c : Fin N → ℂ) (t : ℂ),
      (t + a) ^ N + ∑ j : Fin N, c j * (t + a) ^ (j : ℕ) =
        t ^ N + ∑ i : Fin N, (K₀ i + ∑ j : Fin N, c j * K i j) * t ^ (i : ℕ) := by
  obtain ⟨K, hK⟩ := exists_shift_coeff N a
  refine ⟨fun i => a ^ (N - (i : ℕ)) * (N.choose i : ℂ), K, fun c t => ?_⟩
  have hr := Fin.sum_univ_eq_sum_range (fun i => a ^ (N - i) * (N.choose i : ℂ) * t ^ i) N
  rw [hK, add_pow, Finset.sum_range_succ]
  simp only [add_mul, Finset.sum_add_distrib, hr, Nat.sub_self, pow_zero, Nat.choose_self,
    Nat.cast_one, mul_one]
  have : ∑ x ∈ Finset.range N, t ^ x * a ^ (N - x) * (N.choose x : ℂ) =
      ∑ x ∈ Finset.range N, a ^ (N - x) * (N.choose x : ℂ) * t ^ x :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

theorem coeff_eq_zero_of_forall_eval_eq_zero {N : ℕ} (e : Fin N → ℂ)
    (he : ∀ t : ℂ, ∑ i : Fin N, e i * t ^ (i : ℕ) = 0) (i : Fin N) : e i = 0 := by
  classical
  have hp : (∑ j : Fin N, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ)) = 0 :=
    Polynomial.funext fun t => by simpa [Polynomial.eval_finsetSum] using he t
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj] using this

theorem analyticAt_coord {ι : Type} [Fintype ι] (i : ι) (z : ι → ℂ) :
    AnalyticAt ℂ (fun w : ι → ℂ => w i) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).analyticAt z

theorem weierstrassDivision_in_coordinate (h : WeierstrassPolynomialDivision.Statement)
    {σ : Type} [Fintype σ] [DecidableEq σ] (k : σ) (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (N : ℕ)
    (b : Fin N → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ)
    (hb : ∀ j, AnalyticAt ℂ (b j) y₀)
    (hG : ∀ T : ℂ, T ^ N + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u₀ k) ^ N)
    (hf : AnalyticAt ℂ f (y₀, u₀)) :
    ∃ (q : (Fin d → ℂ) × (σ → ℂ) → ℂ) (e : Fin N → (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → ℂ),
      AnalyticAt ℂ q (y₀, u₀) ∧ (∀ i, AnalyticAt ℂ (e i) (y₀, fun m => u₀ m)) ∧
      ∀ᶠ x in 𝓝 (y₀, u₀), f x = q x * (x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ)) +
        ∑ i, e i (x.1, fun m => x.2 m) * x.2 k ^ (i : ℕ) := by
  obtain ⟨K₀, K, hK⟩ := exists_monic_shift_coeff N (u₀ k)
  obtain ⟨K', hK'⟩ := exists_shift_coeff N (-u₀ k)

  let ι : σ → Option (Fin d ⊕ {m // m ≠ k}) := fun m =>
    if hm : m = k then none else some (Sum.inr ⟨m, hm⟩)

  let φ : (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) → (Fin d → ℂ) × (σ → ℂ) := fun z =>
    (fun i => y₀ i + z (some (Sum.inl i)), fun m => u₀ m + z (ι m))

  let ψ' : (Fin d → ℂ) × ({m // m ≠ k} → ℂ) → (Fin d ⊕ {m // m ≠ k} → ℂ) := fun x' l =>
    Sum.elim (fun i => x'.1 i - y₀ i) (fun m => x'.2 m - u₀ m) l
  let ψ : (Fin d → ℂ) × (σ → ℂ) → (Option (Fin d ⊕ {m // m ≠ k}) → ℂ) := fun x o =>
    Option.elim o (x.2 k - u₀ k) (ψ' (x.1, fun m => x.2 m))

  let c : Fin N → (Fin d ⊕ {m // m ≠ k} → ℂ) → ℂ := fun i w =>
    K₀ i + ∑ j, b j (fun l => y₀ l + w (Sum.inl l)) * K i j
  have hc_an : ∀ i, AnalyticAt ℂ (c i) 0 := by
    intro i
    have hy : AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => fun l => y₀ l + w (Sum.inl l)) 0 :=
      AnalyticAt.pi (f := fun l (w : Fin d ⊕ {m // m ≠ k} → ℂ) => y₀ l + w (Sum.inl l)) fun l =>
        analyticAt_const.add (analyticAt_coord (Sum.inl l) 0)
    have hb' : ∀ j, AnalyticAt ℂ (fun w : Fin d ⊕ {m // m ≠ k} → ℂ => b j (fun l => y₀ l + w (Sum.inl l))) 0 := by
      intro j
      refine (hb j).comp_of_eq hy ?_
      funext l; simp
    exact analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => (hb' j).fun_mul analyticAt_const)
  have hc0 : ∀ i, c i 0 = 0 := by
    refine coeff_eq_zero_of_forall_eval_eq_zero (fun i => c i 0) fun t => ?_
    have h1 := hK (fun j => b j y₀) t
    have h2 := hG (t + u₀ k)
    have hy : (fun l => y₀ l + (0 : Fin d ⊕ {m // m ≠ k} → ℂ) (Sum.inl l)) = y₀ := by funext l; simp
    simp only [c, hy]
    rw [add_sub_cancel_right] at h2
    linear_combination h1.symm.trans h2
  have hφ : AnalyticAt ℂ φ 0 :=
    (AnalyticAt.pi (f := fun i (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => y₀ i + z (some (Sum.inl i))) fun i =>
      analyticAt_const.add (analyticAt_coord _ 0)).prod
    (AnalyticAt.pi (f := fun m (z : Option (Fin d ⊕ {m // m ≠ k}) → ℂ) => u₀ m + z (ι m)) fun m => analyticAt_const.add (analyticAt_coord _ 0))
  have hφ0 : φ 0 = (y₀, u₀) := by
    simp [φ]
  have hφψ : ∀ x, φ (ψ x) = x := by
    intro x
    refine Prod.ext (funext fun i => ?_) (funext fun m => ?_)
    · simp [φ, ψ, ψ']
    · by_cases hm : m = k
      · subst hm; simp [φ, ψ, ι]
      · simp [φ, ψ, ψ', ι, hm]
  have hψ' : AnalyticAt ℂ ψ' (y₀, fun m => u₀ m) := by
    rw [analyticAt_pi_iff]
    intro l
    cases l with
    | inl i => exact ((analyticAt_coord i _).comp analyticAt_fst).sub analyticAt_const
    | inr m => exact ((analyticAt_coord m _).comp analyticAt_snd).sub analyticAt_const
  have hψ'0 : ψ' (y₀, fun m => u₀ m) = 0 := by
    funext l; cases l <;> simp [ψ']
  have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
    analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m) fun m =>
      (analyticAt_coord _ _).comp analyticAt_snd)
  have hψ : AnalyticAt ℂ ψ (y₀, u₀) := by
    rw [analyticAt_pi_iff]
    intro o
    cases o with
    | none => exact ((analyticAt_coord k _).comp analyticAt_snd).sub analyticAt_const
    | some l => exact (analyticAt_coord l _).comp (hψ'.comp_of_eq hπ rfl)
  have hψ0 : ψ (y₀, u₀) = 0 := by
    funext o; cases o with
    | none => simp [ψ]
    | some l => simp only [ψ, Option.elim_some]; exact congrFun hψ'0 l
  have hg : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ hφ0
  obtain ⟨q, a, hq, ha, hev⟩ := h _ N c (f ∘ φ) hc_an hc0 hg
  refine ⟨q ∘ ψ, fun i x' => ∑ j, a j (ψ' x') * K' i j, hq.comp_of_eq hψ hψ0, fun i => ?_, ?_⟩
  · exact Finset.analyticAt_fun_sum _ fun j _ => ((ha j).comp_of_eq hψ' hψ'0).fun_mul analyticAt_const
  · have ht : Tendsto ψ (𝓝 (y₀, u₀)) (𝓝 0) := hψ0 ▸ hψ.continuousAt.tendsto
    filter_upwards [ht.eventually hev] with x hx
    rw [Function.comp_apply, hφψ] at hx
    rw [hx]
    have hy : (fun l => y₀ l + ψ x (some (Sum.inl l))) = x.1 := by funext l; simp [ψ, ψ']
    have hc' : ∀ i, c i (fun l => ψ x (some l)) = K₀ i + ∑ j, b j x.1 * K i j := by
      intro i; simp only [c]; rw [hy]
    have h1 := hK (fun j => b j x.1) (x.2 k - u₀ k)
    rw [sub_add_cancel] at h1
    have hn : ψ x none = x.2 k - u₀ k := rfl
    have hw : weierstrassPolynomial c (ψ x) = x.2 k ^ N + ∑ j, b j x.1 * x.2 k ^ (j : ℕ) := by
      unfold weierstrassPolynomial
      simp only [hc', hn]
      exact h1.symm
    have hr := hK' (fun j => a j (ψ' (x.1, fun m => x.2 m))) (x.2 k)
    rw [← sub_eq_add_neg] at hr
    rw [hw, Function.comp_apply, ← hr]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem SeparateWeierstrassDivision.proof (h : WeierstrassPolynomialDivision.Statement) :
    SeparateWeierstrassDivision.Statement := by
  suffices H : ∀ (N : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ], Fintype.card σ = N →
      ∀ (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
        (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
        (∀ m j, AnalyticAt ℂ (b m j) y₀) →
        (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
        AnalyticAt ℂ f (y₀, u₀) →
        ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
          (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
          ∀ᶠ x in 𝓝 (y₀, u₀),
            f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
              ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ) by
    intro σ _ _ d y₀ u₀ n b f hb hG hf
    exact H _ σ rfl d y₀ u₀ n b f hb hG hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ _ _ hN d y₀ u₀ n b f hb hG hf
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨k⟩⟩
  ·
    refine ⟨fun _ _ => 0, fun _ y => f (y, u₀), fun _ => analyticAt_const,
      fun _ => hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl, Eventually.of_forall fun x => ?_⟩
    have hx : x = (x.1, u₀) := Prod.ext rfl (Subsingleton.elim _ _)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, mul_one, zero_add,
      Fintype.sum_unique]
    rw [← hx]
  · obtain ⟨q, e, hq, he, hev⟩ :=
      weierstrassDivision_in_coordinate h k d y₀ u₀ (n k) (b k) f (hb k) (hG k) hf
    have hlt : Fintype.card {m // m ≠ k} < N :=
      hN ▸ Fintype.card_subtype_lt (p := fun m => m ≠ k) (x := k) (by simp)
    have IH := fun i => ih _ hlt {m // m ≠ k} rfl d y₀ (fun m => u₀ m) (fun m => n m)
      (fun m => b m) (e i) (fun m j => hb m j) (fun m T => hG m T) (he i)
    choose V R hV hR hVR using IH
    have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
      analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m)
        fun m => (analyticAt_coord _ _).comp analyticAt_snd)
    refine ⟨fun m x => if hm : m = k then q x else
        ∑ i, V i ⟨m, hm⟩ (x.1, fun m' => x.2 m') * x.2 k ^ (i : ℕ),
      fun α y => R (α k) (fun m' => α m') y, fun m => ?_, fun α => hR _ _, ?_⟩
    · by_cases hm : m = k
      · simpa [hm] using hq
      · simp only [hm, dite_false]
        exact Finset.analyticAt_fun_sum _ fun i _ =>
          ((hV i ⟨m, hm⟩).comp_of_eq hπ rfl).fun_mul
            (((analyticAt_coord k _).comp analyticAt_snd).fun_pow _)
    · have hT : Tendsto (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m' : {m // m ≠ k} => x.2 m'))
          (𝓝 (y₀, u₀)) (𝓝 (y₀, fun m' => u₀ m')) := hπ.continuousAt.tendsto
      filter_upwards [hev, hT.eventually (Filter.eventually_all.2 hVR)] with x hx hx'
      rw [hx, Fintype.sum_eq_add_sum_subtype_ne _ k,
        ← (Equiv.piSplitAt k (fun m => Fin (n m))).symm.sum_comp, Fintype.sum_prod_type]
      have hne : ∀ m : {m // m ≠ k}, ¬ ((m : σ) = k) := fun m => m.2
      simp_rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
      simp only [Equiv.piSplitAt_symm_apply, dite_true, hne, dite_false, Subtype.coe_eta, hx']
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [add_assoc]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
