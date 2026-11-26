module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups
open MeasureTheory

namespace GlobalTheory

theorem continuous_prod_ofFn_curves {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (hc : ∀ i, Continuous (c i)) :
    Continuous fun t : Fin N → ℝ => (List.ofFn fun i => c i (t i)).prod := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hc 0).comp (continuous_apply 0)).mul
      ((ih (fun i => c i.succ) (fun i => hc i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

theorem integral_cube_succ_last (N : ℕ) (s : ℝ) (f : (Fin (N + 1) → ℝ) → ℝ) (hf : Continuous f) :
    IntegrableOn (fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r))
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
    ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
  set T : Set (Fin N → ℝ) := Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s) with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_Icc
  have hG : Continuous fun z : (Fin N → ℝ) × ℝ => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) :=
    hf.comp (Continuous.finSnoc (n := N) (A := fun _ => ℝ) continuous_fst continuous_snd)
  refine ⟨?_, ?_⟩
  · exact (continuous_parametric_integral_of_continuous
      (f := fun t r => f (Fin.snoc (α := fun _ => ℝ) t r)) hG isCompact_Icc).continuousOn.integrableOn_compact hTc
  · let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hp : MeasurePreserving e (volume : Measure (Fin (N + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℝ) (Fin.last N)
    have hsymm : ∀ z : ℝ × (Fin N → ℝ), e.symm z = Fin.snoc (α := fun _ => ℝ) z.2 z.1 := by
      intro z
      simp [e, MeasurableEquiv.piFinSuccAbove]
    have hS : Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) =
        e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_prod, hT, Set.mem_pi, Set.mem_univ, true_implies]
      rw [Fin.forall_fin_succ', and_comm]
      simp [e, Fin.init]
    have hsw : (fun z : (Fin N → ℝ) × ℝ => f (e.symm z.swap)) =
        fun z => f (Fin.snoc (α := fun _ => ℝ) z.1 z.2) := by
      funext z
      rw [hsymm]
      rfl
    calc ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), f t
        = ∫ t in e ⁻¹' (Set.Icc (0 : ℝ) s ×ˢ T), f (e.symm (e t)) := by
          rw [hS]
          simp only [MeasurableEquiv.symm_apply_apply]
      _ = ∫ z in Set.Icc (0 : ℝ) s ×ˢ T, f (e.symm z) ∂((volume : Measure ℝ).prod volume) :=
          hp.setIntegral_preimage_emb e.measurableEmbedding (fun z => f (e.symm z)) _
      _ = ∫ z in T ×ˢ Set.Icc (0 : ℝ) s, f (e.symm z.swap)
            ∂((volume : Measure (Fin N → ℝ)).prod volume) :=
          (setIntegral_prod_swap _ _ _).symm
      _ = ∫ t in T, ∫ r in Set.Icc (0 : ℝ) s, f (Fin.snoc (α := fun _ => ℝ) t r) := by
          rw [setIntegral_prod]
          · simp only [hsymm, Prod.swap_prod_mk]
          · rw [hsw]
            exact hG.continuousOn.integrableOn_compact (hTc.prod isCompact_Icc)

private theorem sq_norm_le_sobolev_of_hasDerivAt {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (γ : ℝ → G) (hγc : Continuous γ) (hγ0 : γ 0 = 1) (hγ : ∀ a b, γ (a + b) = γ a * γ b)
    (f g : G → H) (hg : Continuous g) (hd : ∀ x, HasDerivAt (fun t => f (x * γ t)) (g x) 0)
    (s : ℝ) (hs : 0 < s) (x : G) :
    ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in Set.Icc (0 : ℝ) s, ‖f (x * γ r)‖ ^ 2) +
      2 * s * ∫ r in Set.Icc (0 : ℝ) s, ‖g (x * γ r)‖ ^ 2 := by
  have key := sobolev_endpoint_one_variable H (fun r => f (x * γ r)) (fun r => g (x * γ r)) s hs
    (fun r _ => by
      have h1 : HasDerivAt (fun t => f (x * γ r * γ t)) (g (x * γ r)) (r - r) := by
        rw [sub_self]
        exact hd _
      have h2 := h1.comp_sub_const r r
      convert h2 using 1
      funext t
      rw [mul_assoc, ← hγ, add_sub_cancel])
    (hg.comp (continuous_const.mul hγc)).continuousOn
  rw [intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at key
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  simp only [hγ0, mul_one] at key
  exact key

private theorem sobolev_iter_lemma_2 {G V H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : ℕ → Set V) (Fr : V → G → H) (s be : ℝ) (y : G) (P₀ : ℕ)
    (hs : 0 < s) (hA : Monotone A) (N : ℕ) :
    ∀ (c : Fin N → ℝ → G) (D : Fin N → V → V) (C : ℝ), 0 ≤ C →
      (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
      (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧
        ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) →
      (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) →
      (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) →
      ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  induction N with
  | zero =>
    intro c D C hC hc hF hb hI u hu
    have h := hI u hu
    have hset : Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) s) = Set.univ := by
      ext t
      simp
    rw [hset, Measure.restrict_univ, volume_pi, Measure.pi_of_empty, integral_dirac] at h
    simpa using h
  | succ N ih =>
    intro c D C hC hc hF hb hI u hu
    have hmain := ih (fun i => c i.castSucc) (fun i => D i.castSucc)
      ((2 / s + 2 * s * be ^ 2) * C) (by positivity) (fun i => hc i.castSucc)
      (fun p w hw => ⟨(hF p w hw).1, fun i => (hF p w hw).2 i.castSucc⟩)
      (fun p hp w hw i => hb p (by omega) w hw i.castSucc) ?_ u hu
    · calc ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * ((2 / s + 2 * s * be ^ 2) * C) * ‖u‖ ^ 2 :=
            hmain
        _ = (2 / s + 2 * s * be ^ 2) ^ (N + 1) * C * ‖u‖ ^ 2 := by ring
    · intro w hw
      have hw1 : w ∈ A (P₀ + (N + 1)) := hA (by omega) hw
      have hDw : D (Fin.last N) w ∈ A (P₀ + (N + 1)) := by
        have h := ((hF (P₀ + N) w hw).2 (Fin.last N)).1
        rwa [add_assoc] at h
      have hbw : ‖D (Fin.last N) w‖ ≤ be * ‖w‖ := hb (P₀ + N) (by omega) w hw (Fin.last N)
      have hpc : Continuous fun t : Fin (N + 1) → ℝ => (List.ofFn fun i => c i (t i)).prod :=
        continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
      have hpc' : Continuous fun t : Fin N → ℝ =>
          (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod :=
        continuous_prod_ofFn_curves N _ (fun i => (hc i.castSucc).1)
      have hcw : Continuous (Fr w) := (hF _ w hw).1
      have hcDw : Continuous (Fr (D (Fin.last N) w)) := (hF _ _ hDw).1
      obtain ⟨i1, e1⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcw.comp (continuous_const.mul hpc)).norm.pow 2)
      obtain ⟨i2, e2⟩ := integral_cube_succ_last N s
        (fun t => ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
        ((hcDw.comp (continuous_const.mul hpc)).norm.pow 2)
      have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
          (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod =
            (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r := by
        intro t r
        rw [List.ofFn_succ']
        simp only [List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
          Fin.snoc_castSucc, Fin.snoc_last]
      simp only [hsn, ← mul_assoc] at i1 e1 i2 e2
      have hL : IntegrableOn (fun t : Fin N → ℝ =>
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2)
          (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
        ((hcw.comp (continuous_const.mul hpc')).norm.pow 2).continuousOn.integrableOn_compact
          (isCompact_univ_pi fun _ => isCompact_Icc)
      have hstep : ∀ t : Fin N → ℝ,
          ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod)‖ ^ 2 ≤
            2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2 :=
        fun t => sq_norm_le_sobolev_of_hasDerivAt (c (Fin.last N)) (hc _).1 (hc _).2.1 (hc _).2.2 (Fr w) _ hcDw
          ((hF _ w hw).2 (Fin.last N)).2 s hs _
      have hDsq : ‖D (Fin.last N) w‖ ^ 2 ≤ (be * ‖w‖) ^ 2 := by gcongr
      calc _ ≤ ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
            (2 / s * (∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr w (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) +
            2 * s * ∫ r in Set.Icc (0 : ℝ) s,
              ‖Fr (D (Fin.last N) w)
                (y * (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c (Fin.last N) r)‖ ^ 2) :=
            setIntegral_mono hL ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s))) hstep
        _ = 2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr w (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) +
            2 * s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
              ‖Fr (D (Fin.last N) w) (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2) := by
            rw [integral_add (i1.const_mul (2 / s)) (i2.const_mul (2 * s)), integral_const_mul,
              integral_const_mul, e1, e2]
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * ‖D (Fin.last N) w‖ ^ 2) :=
            add_le_add (mul_le_mul_of_nonneg_left (hI w hw1) (by positivity))
              (mul_le_mul_of_nonneg_left (hI _ hDw) (by positivity))
        _ ≤ 2 / s * (C * ‖w‖ ^ 2) + 2 * s * (C * (be * ‖w‖) ^ 2) := by gcongr
        _ = (2 / s + 2 * s * be ^ 2) * C * ‖w‖ ^ 2 := by ring

theorem sobolev_iterated_one_parameter_subgroups : ∀ (G V H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup V] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (N P₀ : ℕ) (c : Fin N → ℝ → G) (A : ℕ → Set V) (D : Fin N → V → V) (Fr : V → G → H) (s be C : ℝ) (y : G), 0 < s → 0 ≤ be → 0 ≤ C → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → Monotone A → (∀ p, ∀ u ∈ A p, Continuous (Fr u) ∧ ∀ i, D i u ∈ A (p + 1) ∧ ∀ x, HasDerivAt (fun t => Fr u (x * c i t)) (Fr (D i u) x) 0) → (∀ p ≤ P₀ + N, ∀ u ∈ A p, ∀ i, ‖D i u‖ ≤ be * ‖u‖) → (∀ u ∈ A (P₀ + N), ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖Fr u (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ C * ‖u‖ ^ 2) → ∀ u ∈ A P₀, ‖Fr u y‖ ^ 2 ≤ (2 / s + 2 * s * be ^ 2) ^ N * C * ‖u‖ ^ 2 := by
  intro G V H _ _ _ _ _ _ _ N P₀ c A D Fr s be C y hs _ hC hc hA hF hb hI u hu
  exact sobolev_iter_lemma_2 A Fr s be y P₀ hs hA N c D C hC hc hF hb hI u hu

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  have hmem : ∀ u : A, u ∈ Ideal.span {p} → c u ∈ Ideal.span {p} := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu ⊢
    have := map_dvd c hu
    rwa [hp] at this
  let σ : (Fin m → Fin m → Ideal.span {p}) →+ (Fin m → Fin m → Ideal.span {p}) :=
    { toFun := fun H a b => ⟨c (H b a).1, hmem _ (H b a).2⟩
      map_zero' := by
        funext a b
        exact Subtype.ext (by simp)
      map_add' := fun H K => by
        funext a b
        exact Subtype.ext (by simp) }
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    funext a b
    exact Subtype.ext (hc _)
  have hs : ∀ (r : A) x, σ (r • x) = c r • σ x := fun r x => by
    funext a b
    exact Subtype.ext (map_mul c r _)
  have h := (card_fixed_sq c hc hω σ hσ hs).1
  let e : {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ≃
      {x : Fin m → Fin m → Ideal.span {p} // σ x = x} :=
    { toFun := fun H => ⟨fun a b => ⟨H.1 a b, Ideal.mem_span_singleton.2 (H.2.2 a b)⟩, by
        funext a b
        exact Subtype.ext (H.2.1 a b)⟩
      invFun := fun x => ⟨fun a b => (x.1 a b).1,
        fun a b => congrArg Subtype.val (congrFun (congrFun x.2 a) b),
        fun a b => Ideal.mem_span_singleton.1 (x.1 a b).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {u : A // p ∣ u} ≃ Ideal.span {p} :=
    Equiv.subtypeEquivRight fun u => Ideal.mem_span_singleton.symm
  rw [Nat.card_congr e, h, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

end GlobalTheory.GramCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSqStatement
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_matrices_dvd_sq : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → ∀ (m : ℕ), Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2 = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  first | exact @GlobalTheory.GramCount.card_hermitian_dvd_sq | exact GlobalTheory.GramCount.card_hermitian_dvd_sq | (intros; apply GlobalTheory.GramCount.card_hermitian_dvd_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PackingGeometricMeanSubspaces
open Finset

namespace GlobalTheory

theorem packing_geometric_mean_subspaces : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (U : ι → Submodule ℝ W) (N : ℕ), (∀ v, Module.finrank ℝ (U v) ≤ N) → ∀ (α : Type) (T : Finset α) (y : α → ι → W) (la X : ℝ), 0 < la → 0 < X → (∀ t ∈ T, ∀ v, y t v ∈ U v ∧ ‖y t v‖ ≤ X) → (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → la ≤ (∏ v, ‖y t v - y t' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → (T.card : ℝ) ≤ (1 + 2 * X / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ U N hU α T y la X hla hX hT hsep
  classical
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hexp : (1 : ℝ) / Fintype.card ι ≠ 0 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    positivity

  have hinj : Set.InjOn y T := by
    intro t ht t' ht' he
    by_contra hne
    have h := hsep t ht t' ht' hne
    rw [he] at h
    simp only [sub_self, norm_zero] at h
    have h0 : (∏ _v : ι, (0 : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl
    rw [h0, Real.zero_rpow hexp] at h
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  ·
    subst hN
    have hzero : ∀ t ∈ T, y t = 0 := by
      intro t ht
      funext v
      have hb : U v = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp (hU v))
      have hm := (hT t ht v).1
      rw [hb, Submodule.mem_bot] at hm
      exact hm
    have h1 : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact hinj ha hb (by rw [hzero a ha, hzero b hb])
    simp only [zero_mul, pow_zero]
    exact_mod_cast h1
  ·
    have key := packing_geometric_mean_separated ι
      (fun v => ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ)) N hN
      (fun v => by
        simp only [Module.finrank_prod, Module.finrank_fin_fun]
        have := hU v
        omega)
      la
      (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))))
      (fun _ => X) hla (fun _ => hX)
    have hnormpt : ∀ (v : ι) (a : U v),
        ‖((a, (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) :
          ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖(a : W)‖ := by
      intro v a
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      rfl
    obtain ⟨-, hbound⟩ := key (by
      intro s hs s' hs' hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs hs'
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := hs'
      have hab : (a : α) ≠ b := by
        intro h
        apply hne
        rw [Subtype.ext h]
      have e : ∀ v, ‖((⟨y a v, (hT a a.2 v).1⟩ : U v),
            (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) -
          ((⟨y b v, (hT b b.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ =
          ‖y a v - y b v‖ := by
        intro v
        rw [Prod.mk_sub_mk, sub_zero, hnormpt]
        rfl
      simp only [e]
      exact hsep a a.2 b b.2 hab)
    have hset : {s ∈ (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) :
          Set (∀ v, ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))) |
          ∀ v, ‖s v‖ ≤ (fun _ => X) v} =
        ↑(T.attach.image (fun t : T => fun v =>
          ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) := by
      apply Set.sep_eq_self_iff_mem_true.mpr
      intro s hs
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs
      obtain ⟨a, rfl⟩ := hs
      intro v
      rw [hnormpt]
      exact (hT a a.2 v).2
    have hinj' : Function.Injective (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))) := by
      intro a b hab
      apply Subtype.ext
      apply hinj a.2 b.2
      funext v
      have := congrFun hab v
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
      exact this.1
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj',
      Finset.card_attach] at hbound
    have hX' : (∏ _v : ι, X) ^ ((1 : ℝ) / Fintype.card ι) = X := by
      rw [Finset.prod_const, Finset.card_univ, one_div]
      exact Real.pow_rpow_inv_natCast hX.le hcard.ne'
    rw [hX'] at hbound
    exact hbound

end GlobalTheory
end
