module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbit
open Module

namespace GlobalTheory.GenEigenFinOrbit

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem foldr_eq_prod (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp [ih, Module.End.mul_apply]

theorem map_lt_of_pow_eq_zero {N : Submodule ℂ V} (g : End ℂ V) (K : ℕ)
    (hg : N.map g ≤ N) (hK : ∀ n ∈ N, (g ^ K) n = 0) (hN : N ≠ ⊥) : N.map g < N := by
  refine lt_of_le_of_ne hg fun h => hN ?_
  have hk : ∀ k : ℕ, N.map (g ^ k) = N := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih => rw [pow_succ, Module.End.mul_eq_comp, Submodule.map_comp, h, ih]
  rw [← hk K, eq_bot_iff]
  rintro _ ⟨n, hn, rfl⟩
  simp [hK n hn]

section Family
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)

include hst in
theorem map_prod_le (gs : List (End ℂ V)) (hgs : ∀ g ∈ gs, g ∈ G) : N.map gs.prod ≤ N := by
  induction gs with
  | nil => simp [Module.End.one_eq_id]
  | cons g gs ih =>
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp]
    exact (Submodule.map_mono (ih fun x hx => hgs x (by simp [hx]))).trans
      (hst g (hgs g (by simp)))

include hcomm hst hnil in
theorem finrank_map_prod_le [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by
  induction gs with
  | nil => rw [List.prod_nil, Module.End.one_eq_id, Submodule.map_id]; simp
  | cons g gs ih =>
    have hgs' : ∀ x ∈ gs, x ∈ G := fun x hx => hgs x (by simp [hx])
    have hg : g ∈ G := hgs g (by simp)
    specialize ih hgs'
    set M := N.map gs.prod with hM
    have hMN : M ≤ N := map_prod_le G N hst gs hgs'
    haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hMN
    have hc : Commute g gs.prod :=
      Commute.list_prod_right _ _ fun x hx => hcomm g hg x (hgs' x hx)
    have hMst : M.map g ≤ M := by
      rw [hM, ← Submodule.map_comp, ← Module.End.mul_eq_comp, hc.eq, Module.End.mul_eq_comp,
        Submodule.map_comp]
      exact Submodule.map_mono (hst g hg)
    rw [List.prod_cons, Module.End.mul_eq_comp, Submodule.map_comp, ← hM, List.length_cons]
    by_cases h0 : M = ⊥
    · rw [h0, Submodule.map_bot]; simp
    · have hlt := Submodule.finrank_lt_finrank_of_lt
        (map_lt_of_pow_eq_zero g K hMst (fun n hn => hnil g hg n (hMN hn)) h0)
      omega

include hcomm hst hnil in
theorem map_prod_eq_bot [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) (hlen : finrank ℂ N ≤ gs.length) : N.map gs.prod = ⊥ := by
  haveI : FiniteDimensional ℂ (N.map gs.prod) :=
    Submodule.finiteDimensional_of_le (map_prod_le G N hst gs hgs)
  rw [← Submodule.finrank_eq_zero]
  have := finrank_map_prod_le G N K hcomm hst hnil gs hgs
  omega

include hcomm hst hnil in
theorem exists_common_kernel [FiniteDimensional ℂ N] (hN : N ≠ ⊥) :
    ∃ n ∈ N, n ≠ 0 ∧ ∀ g ∈ G, g n = 0 := by
  classical
  let Pr : ℕ → Prop := fun l => ∃ gs : List (End ℂ V), (∀ g ∈ gs, g ∈ G) ∧ gs.length = l ∧
    N.map gs.prod ≠ ⊥
  have hex : ∃ l, ¬ Pr l := ⟨finrank ℂ N, fun ⟨gs, hgs, hl, hne⟩ =>
    hne (map_prod_eq_bot G N K hcomm hst hnil gs hgs hl.ge)⟩
  have h0 : Pr 0 := ⟨[], by simp, rfl, by simpa [Module.End.one_eq_id] using hN⟩
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
    · exact h
  obtain ⟨gs, hgs, hl, hne⟩ : Pr (Nat.find hex - 1) :=
    not_not.1 (Nat.find_min hex (by omega))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨gs.prod n, map_prod_le G N hst gs hgs ⟨n, hn, rfl⟩, hx0, fun g hg => ?_⟩
  by_contra hne'
  apply Nat.find_spec hex
  refine ⟨g :: gs, ?_, by simp [hl]; omega, ?_⟩
  · intro x hx; simp at hx; rcases hx with rfl | hx; exacts [hg, hgs x hx]
  · intro hbot
    apply hne'
    have : (g :: gs).prod n ∈ N.map (g :: gs).prod := ⟨n, hn, rfl⟩
    rw [hbot] at this
    simpa [Module.End.mul_apply] using this

end Family

theorem sub_pow_coe {U : Submodule ℂ V} (z : End ℂ V) (F : End ℂ U)
    (hF : ∀ u : U, (F u : V) = z u) (c : ℂ) (k : ℕ) (u : U) :
    (((F - c • 1) ^ k) u : V) = ((z - algebraMap ℂ (End ℂ V) c) ^ k) (u : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    simp [hF]

end GlobalTheory.GenEigenFinOrbit

namespace GlobalTheory


open GenEigenFinOrbit in
theorem mem_span_genEigen_of_finiteDimensional_orbit :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)),
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V),
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) →
    Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D →
    (∀ (χ' : Module.End ℂ V → ℂ) (u : V),
      u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 →
      (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) →
    ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧
      ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) →
        zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  intro V _ _ A hA X' D ψ hfin hD hX
  set U := Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) with hU
  have hUst : ∀ z ∈ A, Set.MapsTo z U U := by
    intro z hz
    have : U.map z ≤ U := by
      rw [hU, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨z * w, A.mul_mem hz hw, rfl⟩
    exact fun u hu => this ⟨u, hu, rfl⟩
  have hψU : ψ ∈ U := Submodule.subset_span ⟨1, A.one_mem, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : A → End ℂ U, ∀ (i : A) (u : U), (f i u : V) = (i : End ℂ V) u :=
    ⟨fun i => (i : End ℂ V).restrict (hUst i i.2), fun _ _ => rfl⟩
  have hcommAll : ∀ i j, Commute (f i) (f j) := by
    intro i j
    show f i * f j = f j * f i
    ext u
    have := congrArg (fun T : End ℂ V => T (u : V)) (hA i i.2 j j.2)
    simpa [Module.End.mul_apply, hf] using this
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcommAll i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top _)
  set T := {ψ' | ψ' ∈ U ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D →
        (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} with hT
  have key : ∀ χ : A → ℂ, ∀ x ∈ ⨅ i, (f i).maxGenEigenspace (χ i),
      (x : V) ∈ Submodule.span ℂ T := by
    classical
    intro χ x hx
    set N := (⨅ i, (f i).maxGenEigenspace (χ i)).map U.subtype with hNdef
    have hxN : (x : V) ∈ N := ⟨x, hx, rfl⟩
    have hNU : N ≤ U := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNU
    obtain ⟨χ', hχ'⟩ : ∃ χ' : End ℂ V → ℂ, ∀ z (hz : z ∈ A), χ' z = χ ⟨z, hz⟩ :=
      ⟨fun y => if h : y ∈ A then χ ⟨y, h⟩ else 0, fun z hz => dif_pos hz⟩
    set G : Set (End ℂ V) := {g | ∃ z ∈ A, g = z - algebraMap ℂ _ (χ' z)} with hG
    have hGA : ∀ g ∈ G, g ∈ A := by
      rintro _ ⟨z, hz, rfl⟩
      exact A.sub_mem hz (A.algebraMap_mem _)
    have hcommG : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a :=
      fun a ha b hb => hA a (hGA a ha) b (hGA b hb)
    have hNst : ∀ z ∈ A, N.map z ≤ N := by
      rintro z hz _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨f ⟨z, hz⟩ y, ?_, hf ⟨z, hz⟩ y⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at hy ⊢
      intro i
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommAll i ⟨z, hz⟩) (χ i) (hy i)
    have hstG : ∀ g ∈ G, N.map g ≤ N := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨v, hv, rfl⟩
      simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
      exact N.sub_mem (hNst z hz ⟨v, hv, rfl⟩) (N.smul_mem _ hv)
    have hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ finrank ℂ U) n = 0 := by
      rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
      have hy' := (Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hy) ⟨z, hz⟩
      rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
        LinearMap.mem_ker] at hy'
      rw [hχ' z hz, Submodule.subtype_apply, ← sub_pow_coe z (f ⟨z, hz⟩) (hf ⟨z, hz⟩), hy']
      rfl
    by_cases hN : N = ⊥
    · rw [hN, Submodule.mem_bot] at hxN
      rw [hxN]
      exact zero_mem _
    obtain ⟨n, hnN, hn0, hnker⟩ := exists_common_kernel G N (finrank ℂ U) hcommG hstG hnil hN
    have heig : ∀ z ∈ A, z n = χ' z • n := by
      intro z hz
      have := hnker _ ⟨z, hz, rfl⟩
      simpa [sub_eq_zero] using this
    obtain ⟨χ0, hχ0X, hχ0⟩ := hX χ' n (hNU hnN) hn0 heig
    apply Submodule.subset_span
    refine ⟨hNU hxN, χ0, hχ0X, fun zs hlen hzs => ?_⟩
    rw [foldr_eq_prod]
    have hmap : zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ0 z)) =
        zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ' z)) :=
      List.map_congr_left fun z hz => by rw [hχ0 z (hzs z hz)]
    rw [hmap]
    have hbot := map_prod_eq_bot G N (finrank ℂ U) hcommG hstG hnil
      (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z))
      (by
        intro g hg
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
        exact ⟨z, hzs z hz, rfl⟩)
      (by rw [List.length_map, hlen]; exact (Submodule.finrank_mono hNU).trans hD)
    have hmem : (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod (x : V) ∈
        N.map (zs.map fun z => z - algebraMap ℂ (End ℂ V) (χ' z)).prod := ⟨_, hxN, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem : (⟨ψ, hψU⟩ : U) ∈ ⨆ χ : A → ℂ, ⨅ i, (f i).maxGenEigenspace (χ i) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : U => (x : V) ∈ Submodule.span ℂ T) hmem key
    (by simp) (fun x y hx hy => by simpa using add_mem hx hy)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanGenEigenOfFiniteDimensionalOrbitStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_genEigen_of_finiteDimensional_orbit_alt : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → ∀ (X' : Set (Module.End ℂ V → ℂ)) (D : ℕ) (ψ : V), FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) → Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A)) ≤ D → (∀ (χ' : Module.End ℂ V → ℂ) (u : V), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) → u ≠ 0 → (∀ z ∈ A, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ A, χ' z = χ z) → ψ ∈ Submodule.span ℂ {ψ' | ψ' ∈ Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' A) ∧ ∃ χ ∈ X', ∀ zs : List (Module.End ℂ V), zs.length = D → (∀ z ∈ zs, z ∈ A) → zs.foldr (fun z f => z f - χ z • f) ψ' = 0} := by
  first | exact @GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | exact GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit | (intros; apply GlobalTheory.mem_span_genEigen_of_finiteDimensional_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.PoincareUnfold

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

open MeasureTheory in
open scoped Pointwise in
private lemma setIntegral_exp_linear_fundamentalDomain_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [VAddInvariantMeasure L V μ] [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D μ)
    (hDm : MeasurableSet D) (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (hint : ∀ y ∈ L, ∃ z : ℤ, φ y = z) :
    ∫ v in D, Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) ∂μ = 0 := by
  set f : V → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) with hf
  have hper : ∀ (g : L) (v : V), f (g +ᵥ v) = f v := by
    intro g v
    obtain ⟨z, hz⟩ := hint g g.2
    have hgv : (g +ᵥ v : V) = (g : V) + v := rfl
    simp only [hf, hgv, map_add (f := _), hz]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I z]; ring_nf
    rw [this, one_mul]
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  set w : V := (1 / (2 * φ u)) • u with hw
  have hφw : φ w = 1 / 2 := by
    rw [hw, map_smul, smul_eq_mul]; field_simp
  have hshift : ∀ v, f (w + v) = -f v := by
    intro v
    simp only [hf, map_add (f := _), hφw]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    rw [this, neg_one_mul]
  have hD' : IsAddFundamentalDomain L (w +ᵥ D) μ := hD.vadd_of_comm w
  have h1 : ∫ v in D, f v ∂μ = ∫ v in w +ᵥ D, f v ∂μ := hD.setIntegral_eq hD' hper
  have h2 : ∫ v in w +ᵥ D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := by
    rw [← integral_indicator (hDm.const_vadd w), ← integral_indicator hDm]
    · rw [← integral_add_left_eq_self (μ := μ) _ w]
      congr 1
      ext v
      by_cases hv : v ∈ D
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show w + v ∈ w +ᵥ D from Set.vadd_mem_vadd_set hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        rwa [← vadd_eq_add, Set.vadd_mem_vadd_set_iff]

  have h3 : ∫ v in D, f v ∂μ = -∫ v in D, f v ∂μ := by
    calc ∫ v in D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := h1.trans h2
      _ = ∫ v in D, -f v ∂μ := setIntegral_congr_fun hDm fun v _ => hshift v
      _ = -∫ v in D, f v ∂μ := integral_neg _
  have h4 : (2 : ℂ) * ∫ v in D, f v ∂μ = 0 := by
    rw [two_mul]; nth_rewrite 2 [h3]; ring
  simpa using h4


open MeasureTheory in
open scoped Pointwise in
theorem _root_.GlobalTheory.PoincareUnfold.unfold_poincare_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ,
    (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ →
    ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) →
    (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) →
    ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) →
    l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) →
    (∀ v, ∑' x, Q x * F (j x + v) =
      ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) →
    ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  intro V _ _ _ _ _ μ _ Γ _ j hj C hfin hspan n t Q hQsupp ht hQper F hF a l ha hl0 hl hint H
  classical
  set L : Submodule ℤ V := (C.map j).toIntSubmodule with hLdef
  have hmemL : ∀ y, y ∈ L ↔ ∃ c ∈ C, j c = y := fun y => by
    exact AddSubgroup.mem_map
  have hLset : (L : Set V) = j '' (C : Set Γ) := by
    ext y; simp only [SetLike.mem_coe, hmemL, Set.mem_image]
  have hj0 : ∀ c, j c = 0 ↔ c = 0 := fun c => ⟨fun h => hj (by rw [h, map_zero]), fun h => by
    rw [h, map_zero]⟩
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    set T : Finset ℝ := insert 1 (((hfin 1).toFinset.filter (· ≠ 0)).image fun c => ‖j c‖)
    have hTne : T.Nonempty := Finset.insert_nonempty _ _
    refine ⟨T.min' hTne, ?_, ?_⟩
    · show 0 < T.min' hTne
      rw [Finset.lt_min'_iff]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨c, hc, rfl⟩
      · exact one_pos
      · rw [Finset.mem_filter] at hc
        exact norm_pos_iff.2 fun h => hc.2 ((hj0 c).1 h)
    · rintro ⟨y, hy⟩ hdist
      obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
      have hlt : ‖j c‖ < T.min' hTne := by simpa [dist_eq_norm] using hdist
      have hle1 : T.min' hTne ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      by_cases hc0 : c = 0
      · ext; simp [hc0]
      · exfalso
        have hmem : ‖j c‖ ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨c, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hc, by linarith⟩, hc0⟩, rfl⟩)
        exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hspan⟩
  haveI : VAddInvariantMeasure L V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  set ψ : C → L := fun c => ⟨j c, (hmemL _).2 ⟨c, c.2, rfl⟩⟩ with hψ
  have hψinj : Function.Injective ψ := fun c c' h => Subtype.ext (hj (congrArg Subtype.val h))
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨c, hc, hcy⟩ := (hmemL y).1 y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  haveI : Countable L := (Module.Free.chooseBasis ℤ L).repr.injective.countable
  haveI : Countable C := hψinj.countable
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) with hDdef
  have hD : IsAddFundamentalDomain L D μ := ZLattice.isAddFundamentalDomain _ μ
  have hDfin : μ D < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  refine ⟨ZLattice.covolume L μ, ZLattice.covolume_pos L μ, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hD]
  have hR : ∫ v in D, (∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) ∂μ =
      ((μ.real D : ℝ) : ℂ) * a 0 := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set E : Γ → V → ℂ := fun x v => Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ)) with hE
    have hEnorm : ∀ x v, ‖E x v‖ₑ = 1 := by
      intro x v
      rw [← ofReal_norm_eq_enorm]
      simp only [hE]
      rw [show (2 * Real.pi * Complex.I * ((l x v : ℝ) : ℂ)) = ((2 * Real.pi * l x v : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hEcont : ∀ x, Continuous (E x) := fun x => by
      simp only [hE]
      fun_prop
    set s := Function.support a with hs
    have hscount : s.Countable := ha.of_norm.countable_support
    haveI : Countable s := hscount.to_subtype
    have hsub : ∀ v, ∑' x, a x * E x v = ∑' x : s, a x * E x v := fun v =>
      (tsum_subtype_eq_of_support_subset fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro h; exact hx (by rw [h, zero_mul])).symm
    have hchar : ∀ x, ∫ v in D, a x * E x v ∂μ =
        if x = 0 then ((μ.real D : ℝ) : ℂ) * a 0 else 0 := by
      intro x
      rw [integral_const_mul]
      split_ifs with hx
      · subst hx
        simp only [hE, hl0, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          setIntegral_const, Complex.real_smul, mul_one]
        ring
      · by_cases hax : a x = 0
        · rw [hax, zero_mul]
        · rw [setIntegral_exp_linear_fundamentalDomain_eq_zero μ L hD hDm (l x) (hl x hx)
            (fun y hy => by
              obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
              exact hint x hax c hc), mul_zero]
    show ∫ v in D, (∑' x, a x * E x v) ∂μ = _
    simp_rw [hsub]
    rw [integral_tsum]
    · rw [tsum_subtype_eq_of_support_subset (f := fun x => ∫ v in D, a x * E x v ∂μ)]
      · simp_rw [hchar]
        exact tsum_ite_eq 0 _
      · intro x hx
        rw [Function.mem_support, hchar] at hx
        split_ifs at hx with h0
        · subst h0
          intro h; exact hx (by rw [h, mul_zero])
        · exact absurd rfl hx
    · intro x
      exact ((hEcont x).const_mul (a x) |>.aestronglyMeasurable)
    · simp_rw [enorm_mul, hEnorm, mul_one, lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hDfin.ne
      simp_rw [enorm_eq_nnnorm]
      refine ENNReal.tsum_coe_ne_top_iff_summable.2 ?_
      rw [← NNReal.summable_coe]
      exact ha.subtype (· ∈ s)
  have hLHS : ∫ v in D, (∑' x, Q x * F (j x + v)) ∂μ = (∑ k, Q (t k)) * ∫ v, F v ∂μ := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set e : Fin n × C → Γ := fun p => t p.1 + p.2 with he
    have heinj : Function.Injective e := by
      rintro ⟨k, c⟩ ⟨k', c'⟩ h
      simp only [he] at h
      have hk : k = k' := ht k k' (by
        rw [show t k - t k' = c' - c by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]]
        exact C.sub_mem c'.2 c.2)
      subst hk
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have hsupp : ∀ v, Function.support (fun x => Q x * F (j x + v)) ⊆ Set.range e := by
      intro v x hx
      have hQx : Q x ≠ 0 := fun h => hx (by simp [h])
      obtain ⟨k, hk⟩ := hQsupp x hQx
      exact ⟨(k, ⟨x - t k, hk⟩), by simp [he]⟩
    set g : Fin n × C → V → ℂ := fun p v => Q (t p.1) * F (j (t p.1) + (j p.2 + v)) with hg
    have hrw : ∀ v, ∑' x, Q x * F (j x + v) = ∑' p, g p v := by
      intro v
      rw [← heinj.tsum_eq (hsupp v)]
      refine tsum_congr fun p => ?_
      simp only [he, hg, map_add (f := _), hQper _ _ p.2.2, add_assoc]
    have hunf : ∀ G : V → ℂ, Integrable G μ → ∫ v, G v ∂μ = ∑' c : C, ∫ v in D, G (j c + v) ∂μ := by
      intro G hG
      rw [hD.integral_eq_tsum' G hG,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hunfl : ∀ G : V → ENNReal, ∫⁻ v, G v ∂μ = ∑' c : C, ∫⁻ v in D, G (j c + v) ∂μ := by
      intro G
      rw [hD.lintegral_eq_tsum' G,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hfinite : ∑' p, ∫⁻ v in D, ‖g p v‖ₑ ∂μ ≠ ⊤ := by
      simp_rw [hg, enorm_mul]
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
      rw [ENNReal.tsum_prod (f := fun k (c : C) =>
        ‖Q (t k)‖ₑ * ∫⁻ v in D, ‖F (j (t k) + (j c + v))‖ₑ ∂μ), tsum_fintype]
      refine (ENNReal.sum_lt_top.2 fun k _ => ?_).ne
      rw [ENNReal.tsum_mul_left, ← hunfl (fun v => ‖F (j (t k) + v)‖ₑ)]
      exact ENNReal.mul_lt_top enorm_lt_top (hF.comp_add_left (j (t k))).hasFiniteIntegral
    have hmeas : ∀ p, AEStronglyMeasurable (g p) (μ.restrict D) := fun p =>
      (((hF.comp_add_left (j (t p.1))).comp_add_left (j p.2)).aestronglyMeasurable.const_mul
        _).restrict
    have hsumm : Summable (fun p => ∫ v in D, g p v ∂μ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal hfinite) fun p => ?_
      refine (norm_integral_le_lintegral_norm _).trans_eq ?_
      simp_rw [ofReal_norm_eq_enorm]
    simp_rw [hrw]
    rw [integral_tsum hmeas hfinite, hsumm.tsum_prod, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, integral_const_mul]
    rw [tsum_mul_left, ← hunf _ (hF.comp_add_left (j (t k))), integral_add_left_eq_self]
  rw [← hLHS, ← hR]
  exact setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun v _ => H v

end GlobalTheory.PoincareUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourierStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfold_poincareSeries_lattice_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ, (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ → ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) → (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) → ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) → l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) → (∀ v, ∑' x, Q x * F (j x + v) = ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) → ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  first | exact @GlobalTheory.PoincareUnfold.unfold_poincare_fourier | exact GlobalTheory.PoincareUnfold.unfold_poincare_fourier | (intros; apply GlobalTheory.PoincareUnfold.unfold_poincare_fourier <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeToNumberField
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_numberField_of_finiteType_rat (R : Type) [CommRing R] [Nontrivial R] [Algebra ℚ R]
    [Algebra.FiniteType ℚ R] : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (φ : R →+* K), True := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℚ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m) Ideal.Quotient.mk_surjective
  haveI : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  haveI : CharZero (R ⧸ m) := algebraRat.charZero _
  have hfin := (inferInstance : Module.Finite ℚ (R ⧸ m))
  haveI : @FiniteDimensional ℚ (R ⧸ m) _ _ (@Algebra.toModule ℚ (R ⧸ m) _ _ DivisionRing.toRatAlgebra) := by
    have e : (Ideal.Quotient.algebra ℚ : Algebra ℚ (R ⧸ m)) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    convert hfin
    first
      | exact (congrArg (@Algebra.toModule ℚ (R ⧸ m) _ _) e).symm
      | (rw [← e]; rfl)
  haveI : NumberField (R ⧸ m) := ⟨⟩
  exact ⟨R ⧸ m, inferInstance, inferInstance, Ideal.Quotient.mk m, trivial⟩

theorem exists_numberField_point_ne_zero :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A →
      ∀ a : A, a ≠ 0 → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (χ : A →+* K), χ a ≠ 0 := by
  intro A _ _ _ hA a ha
  classical
  obtain ⟨s, hs⟩ := hA.out
  let F := FractionRing A
  let f : A →+* F := algebraMap A F
  let B : Subalgebra ℚ F := Algebra.adjoin ℚ (insert (f a)⁻¹ ((s.image f : Finset F) : Set F))
  have hmem : ∀ x : A, f x ∈ B := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap n =>
      have : f (algebraMap ℤ A n) = algebraMap ℚ F (n : ℚ) := by simp [f]
      rw [this]; exact B.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact B.mul_mem hx hy
  have hinv : (f a)⁻¹ ∈ B := Algebra.subset_adjoin (Set.mem_insert _ _)
  haveI hBft : Algebra.FiniteType ℚ B := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨insert (f a)⁻¹ (s.image f), by simp [B]⟩
  have hfa : f a ≠ 0 := by
    simpa [f] using (IsFractionRing.injective A F).ne ha
  let ψ : A →+* B := f.codRestrict B hmem
  have hu : IsUnit (ψ a) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(f a)⁻¹, hinv⟩, Subtype.ext ?_⟩
    show f a * (f a)⁻¹ = 1
    exact mul_inv_cancel₀ hfa
  obtain ⟨K, _, _, φ, -⟩ := exists_numberField_of_finiteType_rat B
  exact ⟨K, inferInstance, inferInstance, φ.comp ψ, (hu.map φ).ne_zero⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BurnsideSurjOfIrred
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrreducible
universe u_1 u_2

namespace GlobalTheory.IrreducibleMembership

theorem mem_of_irreducible {K : Type u_1} {V : Type u_2} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (h : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hf1 : f = 1 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hf1]
    exact S.one_mem
  · have hso : IsSimpleOrder (Submodule S V) := by
      refine ⟨fun N => ?_⟩
      have hN := h (N.restrictScalars K) fun g hg v hv => by
        have hmem : (⟨g, hg⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact hmem
      rcases hN with hN | hN
      · left
        exact (Submodule.restrictScalars_eq_bot_iff K S V).1 hN
      · right
        exact (Submodule.restrictScalars_eq_top_iff K S V).1 hN
    have hsimp : IsSimpleModule S V := ⟨⟩
    have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) K
    let F : Module.End (Module.End S V) V :=
      { toFun := f
        map_add' := f.map_add
        map_smul' := fun g v => by
          obtain ⟨c, hc⟩ := hbij.2 g
          rw [← hc]
          simp }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
    have hfr : f = (r : Module.End K V) := by
      refine b.ext fun i => ?_
      have := hr (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
      exact this
    rw [hfr]
    exact r.2

end GlobalTheory.IrreducibleMembership
end

namespace GlobalTheory.CompanionTheory.Burnside

theorem mem_of_irred {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Subalgebra K (Module.End K V))
    (hirr : ∀ N : Submodule K V, (∀ f ∈ S, ∀ v ∈ N, f v ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : Module.End K V) : f ∈ S := by
  first
  | exact @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible
  | (apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IrreducibleMembership.mem_of_irreducible ..)

theorem burnside_surj_of_irred {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by
  intro f
  have h := mem_of_irred ρ.range (fun N hN => hirr N fun a w hw => hN (ρ a) ⟨a, rfl⟩ w hw) f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

end GlobalTheory.CompanionTheory.Burnside
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom
namespace GlobalTheory

open CommRing

theorem natCast_mul_mem_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    (n : ℕ) (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range)
    (I : (Submodule B B')ˣ) (x : B') : (n : B') * x ∈ (I : Submodule B B') := by
  have h1 : (1 : B') ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B') := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Submodule.one_le.mp le_rfl
  have key : ∀ y ∈ ((I⁻¹ : (Submodule B B')ˣ) : Submodule B B') * (I : Submodule B B'),
      ((n : B') * x) * y ∈ (I : Submodule B B') := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun j _ i hi => ?_) (fun y z hy hz => ?_)
    · obtain ⟨b, hb⟩ := hn (x * j)
      have : (n : B') * x * (j * i) = b • i := by
        rw [Algebra.smul_def, hb]; ring
      rw [this]; exact Submodule.smul_mem _ b hi
    · rw [mul_add]; exact Submodule.add_mem _ hy hz
  simpa using key 1 h1

theorem finite_units_submodule {B B' : Type} [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Finite ℤ B'] (n : ℕ) (hn0 : n ≠ 0)
    (hn : ∀ b' : B', (n : B') * b' ∈ (algebraMap B B').range) :
    Finite (Submodule B B')ˣ := by
  set C : Submodule ℤ B' := (Ideal.span {(n : ℤ)}) • (⊤ : Submodule ℤ B') with hCdef
  haveI : NeZero n := ⟨hn0⟩
  haveI : Finite (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod n).symm.toEquiv
  haveI : Finite (B' ⧸ C) := Submodule.finite_quotient_smul _ Module.Finite.fg_top
  haveI : Finite (Submodule ℤ (B' ⧸ C)) :=
    Finite.of_injective (fun N => (N : Set (B' ⧸ C))) SetLike.coe_injective
  have hC : ∀ I : (Submodule B B')ˣ, C ≤ (I : Submodule B B').restrictScalars ℤ := by
    intro I
    refine Submodule.smul_le.mpr fun r hr x _ => ?_
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have : (k * n : ℤ) • x = (n : B') * (k • x) := by
      rw [zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
    rw [Submodule.restrictScalars_mem, this]
    exact natCast_mul_mem_units_submodule n hn I _
  let f : (Submodule B B')ˣ → Submodule ℤ (B' ⧸ C) := fun I =>
    Submodule.map C.mkQ ((I : Submodule B B').restrictScalars ℤ)
  refine Finite.of_injective f fun I J h => ?_
  have hIJ : (I : Submodule B B').restrictScalars ℤ = (J : Submodule B B').restrictScalars ℤ := by
    have := congrArg (Submodule.comap C.mkQ) h
    simp only [f, Submodule.comap_map_mkQ] at this
    rwa [sup_eq_right.mpr (hC I), sup_eq_right.mpr (hC J)] at this
  exact Units.ext (Submodule.restrictScalars_injective ℤ _ _ hIJ)

theorem isOfFinOrder_of_isOfFinOrder_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B']
    [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 →
    (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B,
    IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  intro B B' _ _ _ φ n hφ hn0 hn M hM
  letI : Algebra B B' := φ.toAlgebra
  haveI : FaithfulSMul B B' := (faithfulSMul_iff_algebraMap_injective B B').mpr hφ
  haveI := finite_units_submodule (B := B) (B' := B') n hn0 (fun b' => hn b')
  obtain ⟨k, hk, hpow⟩ := hM.exists_pow_eq_one
  have e : CommRing.Pic.mapRingHom φ = CommRing.Pic.mapAlgebra B B' :=
    CommRing.Pic.mapRingHom_algebraMap
  have hmem : M ^ k ∈ CommRing.relPic B B' := by
    rw [CommRing.relPic, MonoidHom.mem_ker, map_pow, ← e]; exact hpow
  rw [← Submodule.range_unitsToPic] at hmem
  obtain ⟨I, hI⟩ := hmem
  have hfo : IsOfFinOrder (M ^ k) := by
    rw [← hI]; exact (Submodule.unitsToPic B B').isOfFinOrder (isOfFinOrder_of_finite I)
  obtain ⟨m, hm, hm1⟩ := hfo.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul]; exact hm1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Module.Finite ℤ B'] (φ : B →+* B') (n : ℕ), Function.Injective φ → n ≠ 0 → (∀ b' : B', (n : B') * b' ∈ φ.range) → ∀ M : CommRing.Pic B, IsOfFinOrder (CommRing.Pic.mapRingHom φ M) → IsOfFinOrder M := by
  first | exact @GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | exact GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom | (intros; apply GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZero
open TopologicalSpace Order

namespace GlobalTheory.DimDrop

theorem length_le_topologicalKrullDim_of_last_subset {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  have hsub : ∀ i, (q i : Set X) ⊆ Z := fun i x hx => h (q.monotone (Fin.le_last i) hx)
  have irr : ∀ i, IsIrreducible (Subtype.val ⁻¹' (q i : Set X) : Set Z) := by
    intro i
    haveI : IrreducibleSpace (q i : Set X) := Subtype.irreducibleSpace (q i).isIrreducible
    have := (IrreducibleSpace.isIrreducible_univ (q i : Set X)).image (Set.inclusion (hsub i))
      (continuous_inclusion (hsub i)).continuousOn
    rw [Set.image_univ, Set.range_inclusion] at this
    exact this
  let f : Fin (q.length + 1) → IrreducibleCloseds Z := fun i =>
    ⟨Subtype.val ⁻¹' (q i : Set X), irr i, (q i).isClosed.preimage continuous_subtype_val⟩
  have hf : ∀ i j, f i = f j → q i = q j := by
    intro i j e
    have e' : (Subtype.val ⁻¹' (q i : Set X) : Set Z) = Subtype.val ⁻¹' (q j : Set X) :=
      congrArg SetLike.coe e
    have e'' := congrArg (Set.image (Subtype.val : Z → X)) e'
    rw [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (hsub i), Set.inter_eq_right.2 (hsub j)] at e''
    exact SetLike.coe_injective e''
  let p : LTSeries (IrreducibleCloseds Z) :=
    { length := q.length
      toFun := f
      step := fun i => by
        have hs : q i.castSucc < q i.succ := q.step i
        show f i.castSucc < f i.succ
        refine lt_of_le_of_ne ?_ fun e => hs.ne (hf _ _ e)
        intro x hx
        exact hs.le hx }
  exact LTSeries.length_le_krullDim p

theorem topologicalKrullDim_lt_of_isClosed (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨p, hp⟩ := le_krullDim_iff.1 hlt
  let q : LTSeries (IrreducibleCloseds S) :=
    p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
      (IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hql : q.length = d := hp
  have hWC : (q.last : Set S) ⊆ C := by
    show closure (Subtype.val '' (p.last : Set C)) ⊆ C
    refine closure_minimal ?_ hC
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨Z, hZc, hWZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ q.last.isIrreducible
  by_cases hEq : (q.last : Set S) = Z
  · refine hZ Z hZc ?_ (hEq ▸ hWC)
    have := length_le_topologicalKrullDim_of_last_subset Z q hEq.le
    rwa [hql] at this
  · let Zt : IrreducibleCloseds S := ⟨Z, hZc.1, isClosed_of_mem_irreducibleComponents Z hZc⟩
    have hlt' : q.last < Zt := lt_of_le_of_ne hWZ fun e => hEq (congrArg SetLike.coe e)
    have h1 := LTSeries.length_le_krullDim (q.snoc Zt hlt')
    have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      have e : (q.snoc Zt hlt').length = d + 1 := by simp [hql]
      rw [e] at h1
      exact h1.trans hS
    norm_cast at h2
    omega

theorem finite_of_topologicalKrullDim_nonpos (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    [T0Space S] (h : topologicalKrullDim S ≤ 0) : Finite S := by
  have hm := Order.krullDim_nonpos_iff_forall_isMax.1 h
  have hcomp : ∀ x : S, closure ({x} : Set S) ∈ irreducibleComponents S := by
    intro x
    refine ⟨isIrreducible_singleton.closure, fun T hT hle => ?_⟩
    have := hm ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      (b := ⟨closure T, hT.closure, isClosed_closure⟩) (fun y hy => subset_closure (hle hy))
    exact subset_closure.trans this
  haveI : Finite (irreducibleComponents S) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact Finite.of_injective (fun x => (⟨closure {x}, hcomp x⟩ : irreducibleComponents S))
    fun x y hxy => (inseparable_iff_closure_eq.2 (congrArg Subtype.val hxy)).eq

theorem dim_drop : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S],
    (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d →
      (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) →
      topologicalKrullDim C < d) ∧
    (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  intro S _ _
  exact ⟨fun C d hC hS hZ => topologicalKrullDim_lt_of_isClosed S C d hC hS hZ,
    fun _ h => finite_of_topologicalKrullDim_nonpos S h⟩

end GlobalTheory.DimDrop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimDropAndFiniteOfDimZeroStatement
open TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S], (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d → (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) → topologicalKrullDim C < d) ∧ (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  first | exact @GlobalTheory.DimDrop.dim_drop | exact GlobalTheory.DimDrop.dim_drop | (intros; apply GlobalTheory.DimDrop.dim_drop <;> assumption)
end
end
