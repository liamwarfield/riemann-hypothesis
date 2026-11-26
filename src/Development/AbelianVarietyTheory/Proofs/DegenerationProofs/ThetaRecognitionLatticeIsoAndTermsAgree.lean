module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaMatchingExistsRightTorusTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueAddEquivOfCompatibleCongr
open Module

namespace GlobalTheory

private theorem int_eq_zero_of_forall_pow_dvd (n : ℕ) (hn : 2 ≤ n) (c : ℤ)
    (h : ∀ j : ℕ, (n : ℤ) ^ j ∣ c) : c = 0 := by
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h c.natAbs) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

private theorem eq_zero_of_forall_pow_nsmul_dvd (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (n : ℕ) (hn : 2 ≤ n) (z : X) (h : ∀ j : ℕ, ∃ μ : X, z = n ^ j • μ) :
    z = 0 := by
  set b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_pow_dvd n hn _ fun j => ?_
  obtain ⟨μ, hμ⟩ := h j
  refine ⟨b.repr μ i, ?_⟩
  rw [hμ, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  ring

theorem _root_.GlobalTheory.existsUnique_addEquiv_of_compatible_congr :
    ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (n : ℕ), 2 ≤ n → ∀ r : ℕ → X → X' → Prop, (∀ j x, ∃ x', r j x x') → (∀ j x', ∃ x, r j x x') → (∀ j x y x' y', r j x x' → r j y y' → r j (x + y) (x' + y')) → (∀ j x y x' y', r j x x' → r j y y' → ((∃ μ, y = x + n ^ j • μ) ↔ ∃ μ', y' = x' + n ^ j • μ')) → (∀ j x x' μ μ', r j x x' → r j (x + n ^ j • μ) (x' + n ^ j • μ')) → (∀ x, ∃ x', ∀ j, r j x x') → (∀ x', ∃ x, ∀ j, r j x x') → ∃! e : X ≃+ X', ∀ j x, r j x (e x) := by
  intro X X' _ _ _ _ _ _ n hn r _ _ hadd hcong _ hfwd hbwd
  have sepR : ∀ x x' y', (∀ j, r j x x') → (∀ j, r j x y') → x' = y' := by
    intro x x' y' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X' n hn (y' - x') fun j => ?_)).symm
    obtain ⟨μ', hμ'⟩ := (hcong j x x x' y' (hx j) (hy j)).1 ⟨0, by simp⟩
    exact ⟨μ', by rw [hμ', add_sub_cancel_left]⟩
  have sepL : ∀ x y x', (∀ j, r j x x') → (∀ j, r j y x') → x = y := by
    intro x y x' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X n hn (y - x) fun j => ?_)).symm
    obtain ⟨μ, hμ⟩ := (hcong j x y x' x' (hx j) (hy j)).2 ⟨0, by simp⟩
    exact ⟨μ, by rw [hμ, add_sub_cancel_left]⟩
  choose f hf using hfwd
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y =>
    sepR _ _ _ (hf (x + y)) fun j => hadd j x y _ _ (hf x j) (hf y j)
  have bij : Function.Bijective f := by
    refine ⟨fun x y hxy => sepL x y (f x) (hf x) fun j => ?_, fun x' => ?_⟩
    · rw [hxy]
      exact hf y j
    · obtain ⟨x, hx⟩ := hbwd x'
      exact ⟨x, sepR _ _ _ (hf x) hx⟩
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) bij, fun j x => hf x j, fun e he => ?_⟩
  ext x
  exact sepR x (e x) (f x) (fun j => he j x) (hf x)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TendstoTsumZeroOfEventuallyNotMemRange
open Module Filter Topology

namespace GlobalTheory

theorem eq_zero_of_forall_pow_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ}
    (hn : 2 ≤ n) {x : X} (hx : ∀ j : ℕ, ∃ μ : X, x = n ^ j • μ) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨μ, hμ⟩ := hx (b.repr x i).natAbs
  have hd : ((n : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := by
    refine ⟨b.repr μ i, ?_⟩
    conv_lhs => rw [hμ]
    simp [map_nsmul]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem tendsto_tsum_zero_of_eventually_notMem_range {K X Y : Type} [NontriviallyNormedField K]
    [IsUltrametricDist K] (τ : X → K) (hτ : Tendsto τ cofinite (𝓝 0)) (f : ℕ → Y → X)
    (hf : ∀ z, τ z ≠ 0 → ∀ᶠ j in atTop, ∀ μ, f j μ ≠ z) :
    Tendsto (fun j => ∑' μ, τ (f j μ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS : {z | ¬ ‖τ z‖ < ε / 2}.Finite := by
    have := hτ (Metric.ball_mem_nhds (0 : K) (half_pos hε))
    rw [Filter.mem_map, Filter.mem_cofinite] at this
    convert this using 1
    ext z
    simp
  have hev : ∀ᶠ j in atTop, ∀ z ∈ {z | ¬ ‖τ z‖ < ε / 2}, ∀ μ, f j μ ≠ z :=
    (hS.eventually_all).2 fun z hz => hf z (fun h0 => hz (by rw [h0, norm_zero]; exact half_pos hε))
  filter_upwards [hev] with j hj
  rw [dist_zero_right]
  refine lt_of_le_of_lt
    (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun μ => ?_) (half_lt_self hε)
  by_contra h
  exact hj (f j μ) (show ¬ ‖τ (f j μ)‖ < ε / 2 from fun h' => h h'.le) μ rfl

theorem mem_class_of_le {X : Type} [AddCommGroup X] {n : ℕ} {α : ℕ → X}
    (hα : ∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) {z : X} {j k : ℕ} (hjk : j ≤ k)
    (hz : ∃ μ, z = α k + n ^ k • μ) : ∃ μ, z = α j + n ^ j • μ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d generalizing z with
  | zero => simpa using hz
  | succ d ih =>
    obtain ⟨μ, rfl⟩ := hz
    obtain ⟨ν, hν⟩ := hα (j + d)
    apply ih
    refine ⟨ν + n • μ, ?_⟩
    rw [← add_assoc, hν, pow_succ, mul_smul, smul_add]
    abel

theorem tendsto_tsum_pow_classes :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n →
      ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : ℕ → X,
      (∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) →
      (∀ χ : X, (∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds (σ χ))) ∧
      ((¬ ∃ χ : X, ∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds 0)) := by
  classical
  intro K X _ _ _ _ _ _ n hn σ hσ α hα
  have hinj : ∀ j, Function.Injective (fun μ : X => α j + n ^ j • μ) := by
    intro j μ ν h
    simp only [add_right_inj] at h
    have hne : ((n ^ j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero j (by omega : n ≠ 0)
    have h' : ((n ^ j : ℕ) : ℤ) • μ = ((n ^ j : ℕ) : ℤ) • ν := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact smul_right_injective X hne h'
  have hsum : ∀ τ : X → K, Tendsto τ cofinite (𝓝 0) → ∀ j, Summable (fun μ => τ (α j + n ^ j • μ)) :=
    fun τ hτ j => NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hτ.comp (hinj j).tendsto_cofinite)
  have hfar : ∀ z w : X, z ≠ w → ∀ᶠ j in atTop, ¬ ∃ μ, z = w + n ^ j • μ := by
    intro z w hzw
    by_contra h
    rw [Filter.not_eventually] at h
    simp only [not_not] at h
    apply hzw
    have h0 : z - w = 0 := by
      refine eq_zero_of_forall_pow_nsmul hn (fun j => ?_)
      obtain ⟨i, ⟨μ, hμ⟩, hji⟩ := (h.and_eventually (eventually_ge_atTop j)).exists
      refine ⟨n ^ (i - j) • μ, ?_⟩
      rw [hμ, add_sub_cancel_left, ← mul_smul, ← pow_add, Nat.add_sub_cancel' hji]
    exact sub_eq_zero.mp h0
  constructor
  · intro χ hχ
    let τ := Function.update σ χ 0
    have hτ : Tendsto τ cofinite (𝓝 0) := by
      apply hσ.congr'
      filter_upwards [(Set.finite_singleton χ).compl_mem_cofinite] with z hz
      simp [τ, Set.mem_compl_singleton_iff.mp hz]
    have h2 := tendsto_tsum_zero_of_eventually_notMem_range τ hτ (fun j μ => α j + n ^ j • μ) (by
      intro z hz
      have hzχ : z ≠ χ := by
        rintro rfl
        simp [τ] at hz
      filter_upwards [hfar z χ hzχ] with j hj μ hμ
      apply hj
      obtain ⟨ν, hν⟩ := hχ j
      have hμ' : z = α j + n ^ j • μ := hμ.symm
      refine ⟨μ - ν, ?_⟩
      rw [hμ', hν, smul_sub]
      abel)
    have heq : ∀ j, ∑' μ, σ (α j + n ^ j • μ) = σ χ + ∑' μ, τ (α j + n ^ j • μ) := by
      intro j
      obtain ⟨μj, hμj⟩ := hχ j
      rw [(hsum σ hσ j).tsum_eq_add_tsum_ite μj]
      congr 1
      · rw [hμj]
      · refine tsum_congr fun μ => ?_
        by_cases h : μ = μj
        · subst h
          simp [τ, ← hμj]
        · have hne : α j + n ^ j • μ ≠ χ := fun h' => h (hinj j (h'.trans hμj))
          simp [τ, h, hne]
    have h3 := tendsto_const_nhds (x := σ χ) |>.add h2
    rw [add_zero] at h3
    exact h3.congr (fun j => (heq j).symm)
  · intro hno
    apply tendsto_tsum_zero_of_eventually_notMem_range σ hσ (fun j μ => α j + n ^ j • μ)
    intro z _
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ ∃ μ, z = α j0 + n ^ j0 • μ := by
      by_contra h
      exact hno ⟨z, fun j => by
        by_contra h'
        exact h ⟨j, h'⟩⟩
    filter_upwards [eventually_ge_atTop j0] with j hj μ hμ
    exact hj0 (mem_class_of_le hα hj ⟨μ, hμ.symm⟩)

end GlobalTheory
end

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem exists_char_pow {K X : Type} [Field K] [IsAlgClosed K] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {k : ℕ} (hk : k ≠ 0) (t : Multiplicative X →* Kˣ) :
    ∃ s : Multiplicative X →* Kˣ, s ^ k = t := by
  have h : ∀ u : Kˣ, ∃ v : Kˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hk)
    have : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z this, Units.ext (by simpa using hz)⟩
  choose v hv using h
  let b := Module.finBasis ℤ X
  refine ⟨TorsionFourier.charOfValues b fun i => v (t (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, v (t (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = t (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b t, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hv]

section
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']

theorem class_sum_eq [IsAlgClosed K] {M : ℕ} (hM : ‖(M : K)‖ = 1) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (α : X) (α' : X')
    (E : {t : Multiplicative X →* Kˣ // t ^ M = 1} → {t : Multiplicative X' →* Kˣ // t ^ M = 1})
    (hE : Function.Bijective E)
    (hα : ∀ t, (E t).1 (Multiplicative.ofAdd α') = t.1 (Multiplicative.ofAdd α))
    (hs : ∀ t, ∑' β, σ' β * ((E t).1 (Multiplicative.ofAdd β) : K) =
      c * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) :
    ∑' μ, σ' (α' + M • μ) = c * ∑' μ, σ (α + M • μ) := by
  have h0 : (M : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hM
    exact zero_ne_one hM
  have hp : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  haveI : NeZero (M : K) := ⟨h0⟩
  haveI : NeZero M := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  obtain ⟨hf, h1, -⟩ := fourier_extraction_tsum_class K X M ζ hp hM hζ σ hσ α
  obtain ⟨-, h2, -⟩ := fourier_extraction_tsum_class K X' M ζ hp hM hζ σ' hσ' α'
  have hc : M ^ finrank ℤ X = M ^ finrank ℤ X' := by
    rw [← TorsionFourier.natCard_torsionChars (K := K) hp hζ, ← TorsionFourier.natCard_torsionChars (K := K) hp hζ]
    exact Nat.card_eq_of_bijective E hE
  have hc' : (M : K) ^ finrank ℤ X = (M : K) ^ finrank ℤ X' := by exact_mod_cast congrArg (Nat.cast : ℕ → K) hc
  rw [← finsum_comp E hE] at h2
  simp only [hα, hs] at h2
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ M = 1}
  rw [finsum_eq_sum_of_fintype] at h1 h2
  apply mul_left_cancel₀ (pow_ne_zero (finrank ℤ X') h0)
  rw [← h2, ← hc', mul_left_comm, ← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => mul_left_comm _ _ _

theorem limit_class {n : ℕ} (hn : 2 ≤ n) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (x : X) (α' : ℕ → X')
    (hα : ∀ j, ∃ μ, α' (j + 1) = α' j + n ^ j • μ)
    (hs : ∀ j, ∑' μ, σ' (α' j + n ^ j • μ) = c * ∑' μ, σ (x + n ^ j • μ)) :
    (∀ x', (∀ j, ∃ μ, x' = α' j + n ^ j • μ) → σ' x' = c * σ x) ∧
      (c * σ x ≠ 0 → ∃ x', ∀ j, ∃ μ, x' = α' j + n ^ j • μ) := by
  have h1 := ((tendsto_tsum_pow_classes K X n hn σ hσ (fun _ => x) fun j => ⟨0, by simp⟩).1 x
    fun j => ⟨0, by simp⟩).const_mul c
  have h2 := tendsto_tsum_pow_classes K X' n hn σ' hσ' α' hα
  simp only [hs] at h2
  refine ⟨fun x' hx => tendsto_nhds_unique (h2.1 x' hx) h1, fun hc => ?_⟩
  by_contra h
  exact hc (tendsto_nhds_unique h1 (h2.2 h))
end

section
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

theorem r_left {k : ℕ} {p q : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (e : N.QEq p q) : μ.r k q p' :=
  (μ.eqv k p q p' p' h e).2 ⟨0, by simp, by simp⟩

theorem r_right {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') (e : N'.QEq p' q') : μ.r k p q' :=
  (μ.eqv k p p p' q' h ⟨0, by simp, by simp⟩).2 e

theorem qeq_right {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') (e : μ.r k p q') : N'.QEq p' q' :=
  (μ.eqv k p p p' q' h ⟨0, by simp, by simp⟩).1 e

theorem eq_of_qeq {N : NumD C} {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (e : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  rw [e, left_eq_add] at h1
  have hz : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0) (by simpa using h1)
    exact this
  rw [hz, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext e h2.symm)

theorem r_one {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j 1
  have h := μ.mul _ _ _ _ _ hu hu
  rw [mul_one] at h
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ hu h)
  have hsymm : ∀ {a b : N'.QT (n ^ j)}, N'.QEq a b → N'.QEq b a := by
    rintro a b ⟨w, hw, hw'⟩
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right], by rw [hw', N'.io_neg, mul_inv_cancel_right]⟩
  refine r_right μ hu (hsymm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul]
  exact mul_left_cancel hz

theorem r_pow {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (i : ℕ) :
    μ.r k (p ^ i) (p' ^ i) := by
  induction i with
  | zero => simpa using r_one μ hk
  | succ i ih => rw [pow_succ, pow_succ]; exact μ.mul _ _ _ _ _ ih h

theorem r_inv {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  have h1 := r_one μ hk
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j p⁻¹
  have h2 := μ.mul _ _ _ _ _ h hu
  rw [mul_inv_cancel] at h2
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 (qeq_right μ h1 h2)
  have hsymm : ∀ {a b : N'.QT (n ^ j)}, N'.QEq a b → N'.QEq b a := by
    rintro a b ⟨w, hw, hw'⟩
    exact ⟨-w, by rw [hw, smul_neg, add_neg_cancel_right], by rw [hw', N'.io_neg, mul_inv_cancel_right]⟩
  refine r_right μ hu (hsymm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩))
  rw [one_mul] at hz
  rw [← hz, inv_mul_cancel_left]

theorem r_incl {k K : ℕ} (k' : ℕ) (hK : K = k * k') (hk : k' ≠ 0) {p : N.QT k} {p' : N'.QT k} {q : N.QT K}
    {q' : N'.QT K} (h1 : q.1.1 = p.1.1 ^ k') (h2 : q.1.2 = p.1.2) (h3 : q'.1.1 = p'.1.1 ^ k')
    (h4 : q'.1.2 = p'.1.2) : μ.r k p p' ↔ μ.r K q q' := by
  subst hK
  exact μ.incl k k' p p' q q' hk h1 h2 h3 h4

theorem exists_one_of_inG {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem tot_G (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (p : N.QT k) (hp : p.1.1 = 1) :
    ∃ p', μ.r k p p' ∧ p'.1.1 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j p
  obtain ⟨q, e, hq⟩ := exists_one_of_inG ((hA.2 j p u hu).1.1 ⟨0, by simp [hp]⟩)
  exact ⟨q, r_right μ hu e, hq⟩

theorem cotot_G (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (p' : N'.QT k) (hp : p'.1.1 = 1) :
    ∃ p, μ.r k p p' ∧ p.1.1 = 1 := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.cotot j p'
  obtain ⟨q, e, hq⟩ := exists_one_of_inG ((hA.2 j u p' hu).1.2 ⟨0, by simp [hp]⟩)
  exact ⟨q, r_left μ hu e, hq⟩

theorem exists_tor_of_inT {N : NumD C} {k : ℕ} {p : N.QT k} (h : N.InT p) :
    ∃ t ht, N.QEq p (N.qTor t ht) := by
  obtain ⟨q, e, h1, h2⟩ := h
  obtain ⟨t, ht⟩ := (N.exists_tor_iff _).2 h2
  have h3 : t ^ k = 1 := by
    apply N.tor_injective
    rw [N.tor_pow, ht, N.mem_QT.1 q.2, h1, N.tor_one]
    exact N.io_zero
  refine ⟨t, h3, ?_⟩
  have : q = N.qTor t h3 := Subtype.ext (Prod.ext h1 ht.symm)
  exact this ▸ e

theorem inT_tor {N : NumD C} {k : ℕ} (t : Multiplicative N.X →* Cˣ) (ht : t ^ k = 1) : N.InT (N.qTor t ht) :=
  ⟨N.qTor t ht, ⟨0, by simp, by simp⟩, rfl, rfl⟩

theorem thetaMatching_exists_right_torus_torsion (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (t : Multiplicative N.X →* Cˣ) (ht : t ^ k = 1) :
    ∃ t' ht', μ.r k (N.qTor t ht) (N'.qTor t' ht') := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.tot j (N.qTor t ht)
  obtain ⟨t', ht', e⟩ := exists_tor_of_inT ((hA.2 j _ u hu).2.1 (inT_tor t ht))
  exact ⟨t', ht', r_right μ hu e⟩

theorem thetaMatching_exists_left_torus_torsion (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) (t' : Multiplicative N'.X →* Cˣ) (ht' : t' ^ k = 1) :
    ∃ t ht, μ.r k (N.qTor t ht) (N'.qTor t' ht') := by
  obtain ⟨j, rfl⟩ := hk
  obtain ⟨u, hu⟩ := μ.cotot j (N'.qTor t' ht')
  obtain ⟨t, ht, e⟩ := exists_tor_of_inT ((hA.2 j u _ hu).2.2 (inT_tor t' ht'))
  exact ⟨t, ht, r_left μ hu e⟩

theorem exists_torus_bij (hn : n ≠ 0) (hA : μ.A) {k : ℕ} (hk : ∃ j, k = n ^ j) :
    ∃ E : {t : Multiplicative N.X →* Cˣ // t ^ k = 1} → {t : Multiplicative N'.X →* Cˣ // t ^ k = 1},
      Function.Bijective E ∧ ∀ t, μ.r k (N.qTor t.1 t.2) (N'.qTor (E t).1 (E t).2) := by
  have hk0 : k ≠ 0 := by obtain ⟨j, rfl⟩ := hk; exact pow_ne_zero _ hn
  choose f hf h using thetaMatching_exists_right_torus_torsion μ hA hk
  refine ⟨fun t => ⟨f t.1 t.2, hf t.1 t.2⟩, ⟨fun s t e => ?_, fun t' => ?_⟩, fun t => h t.1 t.2⟩
  · have e' : N'.qTor _ (hf s.1 s.2) = N'.qTor _ (hf t.1 t.2) :=
      congrArg (fun u : {t : Multiplicative N'.X →* Cˣ // t ^ k = 1} => N'.qTor u.1 u.2) e
    have h1 := h s.1 s.2
    rw [e'] at h1
    have := eq_of_qeq hk0 (μ.inj k _ _ _ h1 (h t.1 t.2)) rfl
    exact Subtype.ext (N.tor_injective (congrArg (fun q : N.QT k => q.1.2) this))
  · obtain ⟨t, ht, e⟩ := thetaMatching_exists_left_torus_torsion μ hA hk t'.1 t'.2
    refine ⟨⟨t, ht⟩, Subtype.ext (N'.tor_injective ?_)⟩
    exact congrArg (fun q : N'.QT k => q.1.2) (eq_of_qeq hk0 (qeq_right μ (h t ht) e) rfl)

def Cl (j : ℕ) (x : N.X) (x' : N'.X) : Prop :=
  ∃ p p', μ.r (n ^ j) p p' ∧ p.1.1.toAdd = x ∧ p'.1.1.toAdd = x'

theorem Cl.add {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    Cl μ j (x + y) (x' + y') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  exact ⟨_, _, μ.mul _ _ _ _ _ h h', rfl, rfl⟩

theorem Cl.cong (hA : μ.A) {j : ℕ} {x y : N.X} {x' y' : N'.X} (h : Cl μ j x x') (h' : Cl μ j y y') :
    (∃ z, y = x + n ^ j • z) ↔ ∃ z', y' = x' + n ^ j • z' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  obtain ⟨q, q', h', rfl, rfl⟩ := h'
  have := (hA.2 j _ _ (μ.mul _ _ _ _ _ (r_inv μ ⟨j, rfl⟩ h) h')).1
  simp only [← neg_add_eq_iff_eq_add]
  exact this

theorem Cl.shift {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') (z : N.X) (z' : N'.X) :
    Cl μ j (x + n ^ j • z) (x' + n ^ j • z') := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  exact ⟨p * N.qTriv _ z, p' * N'.qTriv _ z',
    r_right μ (r_left μ h ((N.qEq_iff _ _).2 ⟨z, rfl⟩)) ((N'.qEq_iff _ _).2 ⟨z', rfl⟩), rfl, rfl⟩

theorem Cl.down (hn : n ≠ 0) {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ (j + 1) x x') : Cl μ j x x' := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  refine ⟨⟨(p.1.1, p.1.2 ^ n), ?_⟩, ⟨(p'.1.1, p'.1.2 ^ n), ?_⟩, ?_, rfl, rfl⟩
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p.2
  · rw [NumD.mem_QT, ← pow_mul, ← pow_succ']; exact p'.2
  · exact (r_incl μ n (pow_succ n j) hn rfl rfl rfl rfl).2 (r_pow μ ⟨_, rfl⟩ h n)

theorem Cl.tor {j : ℕ} {x : N.X} {x' : N'.X} (h : Cl μ j x x') {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ j = 1}
    {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ j = 1} (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    t' (Multiplicative.ofAdd x') = t (Multiplicative.ofAdd x) := by
  obtain ⟨p, p', h, rfl, rfl⟩ := h
  have := μ.wp _ _ _ _ _ e h
  rwa [NumD.wp_qTor, NumD.wp_qTor] at this
end

end GlobalTheory.MatchTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem txT_tendsto {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hq : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : Tendsto (N.txT m p) cofinite (𝓝 0) := by
  have h0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine squeeze_zero_norm (a := fun χ => Real.exp (-q χ)) (fun χ => ?_)
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq.pos))
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 m hm p χ, hp, toAdd_one, zero_add, ← natCast_zsmul, QuadraticMap.map_smul]
  have : (((m : ℤ) * (m : ℤ)) • q χ) / (m : ℝ) ^ 2 = q χ := by
    rw [zsmul_eq_mul]; push_cast; field_simp
  rw [this]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hq.th _)

theorem exists_txT_ne {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by
  obtain ⟨t, ht, hx⟩ := hT.good (N.c x)
  obtain ⟨b, rfl⟩ := hT.div t
  obtain ⟨γ, rfl⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT 0).1 b
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ ^ (n ^ 1) ^ 2)).2 (by rw [NumD.Gt.pow_b, pow_one, sq, pow_mul, ht])
  obtain ⟨s, rfl⟩ := exists_char_pow (k := (n ^ 1) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')) s
  refine ⟨⟨(1, γ * (N.tor s)⁻¹), ?_⟩, rfl, ?_⟩
  · rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
    exact N.io_zero.symm
  · rw [← norm_ne_zero_iff, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hq).2 _ hn.pow]
    refine mul_ne_zero (Real.exp_pos _).ne' ?_
    simp [hx]

theorem tx_twist {C : Type} [NormedField C] {N : NumD C} {M m : ℕ} (hM : Odd M) (hm : Odd m)
    (p : N.QT (m ^ 2)) (P : N.QT ((M * m) ^ 2)) (hp : p.1.1 = 1) (hP : P.1.1 = 1) (h : p.1.2 = P.1.2 ^ M)
    (s : Multiplicative N.X →* Cˣ) (hs : s ^ (M * m) ^ 2 = 1) :
    N.tx (M * m) (P * N.qTor s hs) = ∑' β, N.txT m p β * ((s ^ (M * m)) (Multiplicative.ofAdd β) : C) := by
  refine tsum_congr fun β => ?_
  rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (M * m) (hM.mul hm) P (P * N.qTor s hs) β).2 s (mul_one _) rfl,
    GlobalTheory.T.degenerationSeriesTerms_nest C N M m hM hm P p (by rw [hP, hp, one_pow]) h, hP, map_one, one_pow, one_mul, toAdd_one, zero_add,
    ofAdd_nsmul, map_pow, mul_comm]
  rfl

section
variable {C : Type} [NormedField C] [IsAlgClosed C] {N N' : NumD C} {n g : ℕ} (μ : Match N N' n)

theorem tx_eq {m : ℕ} (hm : ∃ j, m = n ^ j) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r _ p p') :
    N'.tx m p' = μ.c₀ * N.tx m p := by
  obtain ⟨j, rfl⟩ := hm
  exact μ.tx j p p' h

theorem twisted_eq (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (hA : μ.A) (i j : ℕ)
    {p : N.QT ((n ^ j) ^ 2)} {p' : N'.QT ((n ^ j) ^ 2)} (h : μ.r _ p p') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1)
    {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ i = 1} {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ i = 1}
    (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    ∑' β, N'.txT (n ^ j) p' β * (t' (Multiplicative.ofAdd β) : C) =
      μ.c₀ * ∑' β, N.txT (n ^ j) p β * (t (Multiplicative.ofAdd β) : C) := by
  have h0 : ∀ a, n ^ a ≠ 0 := fun a => pow_ne_zero _ hn.pos.ne'
  have hL0 : n ^ i * n ^ j ≠ 0 := mul_ne_zero (h0 _) (h0 _)
  have hL : ∃ a, (n ^ i * n ^ j) ^ 2 = n ^ a := ⟨(i + j) * 2, by ring⟩
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT i).2.1 p.1.2
  have hp1 : p.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N.mem_QT.1 p.2, hp]; exact N.io_zero
  have hp1' : p'.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N'.mem_QT.1 p'.2, hp']; exact N'.io_zero
  let P : N.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, γ), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = n ^ i * ((n ^ j) ^ 2 * n ^ i) by ring, pow_mul, hγ, pow_mul, hp1, one_pow]
    exact N.io_zero.symm⟩
  obtain ⟨P', hPP, hP'⟩ := tot_G μ hA hL P rfl
  let Q' : N'.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, p'.1.2), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = (n ^ j) ^ 2 * (n ^ i) ^ 2 by ring, pow_mul, hp1', one_pow]
    exact N'.io_zero.symm⟩
  have h1 : μ.r _ (P ^ n ^ i) Q' :=
    (r_incl μ (p := p) (p' := p') (q := P ^ n ^ i) (q' := Q') ((n ^ i) ^ 2) (by ring) (pow_ne_zero _ (h0 i)) (by rw [hp, one_pow]; exact one_pow _) hγ
      (by rw [hp', one_pow]) rfl).1 h
  have h2 : Q' = P' ^ n ^ i := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h1 (r_pow μ hL hPP _))
    (by change 1 = P'.1.1 ^ n ^ i; rw [hP', one_pow])
  have h3 : p'.1.2 = P'.1.2 ^ n ^ i := congrArg (fun q : N'.QT _ => q.1.2) h2
  obtain ⟨s, rfl⟩ := exists_char_pow hL0 t
  have hs : s ^ (n ^ i * n ^ j) ^ 2 = 1 := by rw [sq, pow_mul, pow_mul _ (n ^ i), ht, one_pow]
  obtain ⟨s', hs', hss⟩ := thetaMatching_exists_right_torus_torsion μ hA hL s hs
  have ht'' : t' ^ (n ^ i * n ^ j) ^ 2 = 1 := by
    rw [show (n ^ i * n ^ j) ^ 2 = n ^ i * (n ^ i * (n ^ j) ^ 2) by ring, pow_mul, ht', one_pow]
  have h4 : μ.r _ (N.qTor s hs ^ (n ^ i * n ^ j)) (N'.qTor t' ht'') :=
    (r_incl μ (p := N.qTor _ ht) (p' := N'.qTor t' ht') (q := N.qTor s hs ^ (n ^ i * n ^ j))
      (q' := N'.qTor t' ht'') (n ^ i * (n ^ j) ^ 2) (by ring) (mul_ne_zero (h0 i) (pow_ne_zero _ (h0 j)))
      ((one_pow _).trans (one_pow _).symm) (N.tor_pow _ _).symm (one_pow _).symm rfl).1 e
  have h5 := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h4 (r_pow μ hL hss _)) (one_pow _).symm
  have h6 : t' = s' ^ (n ^ i * n ^ j) :=
    N'.tor_injective ((congrArg (fun q : N'.QT _ => q.1.2) h5).trans (N'.tor_pow _ _).symm)
  rw [h6, ← tx_twist hn.pow hn.pow p P hp rfl hγ.symm s hs, ← tx_twist hn.pow hn.pow p' P' hp' hP' h3 s' hs']
  exact tx_eq μ ⟨i + j, (pow_add _ _ _).symm⟩ (μ.mul _ _ _ _ _ hPP hss)
end

theorem main : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  intro C _ _ _ _ N N' q q' n g g' hpr hn hn1 hq hq' hT hT' μ hA
  have hC : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  have hn0 := hpr.ne_zero
  have key : ∀ i j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)), μ.r _ p p' → p.1.1 = 1 → p'.1.1 = 1 →
      ∀ α α', Cl μ i α α' →
      ∑' z, N'.txT (n ^ j) p' (α' + n ^ i • z) = μ.c₀ * ∑' z, N.txT (n ^ j) p (α + n ^ i • z) := by
    intro i j p p' h hp hp' α α' hα
    obtain ⟨E, hE, hr⟩ := exists_torus_bij μ hn0 hA ⟨i, rfl⟩
    exact class_sum_eq (by rw [Nat.cast_pow, norm_pow, hn1, one_pow]) _ _ (txT_tendsto hq hn.pow p hp)
      (txT_tendsto hq' hn.pow p' hp') _ α α' E hE (fun t => hα.tor μ (hr t))
      fun t => twisted_eq μ hn hC hT hA i j h hp hp' (hr t)
  have tot : ∀ j x, ∃ x', Cl μ j x x' := fun j x => by
    obtain ⟨p, hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT j).2.2.1 x
    obtain ⟨p', h⟩ := μ.tot j p
    exact ⟨_, p, p', h, hp, rfl⟩
  have cotot : ∀ j x', ∃ x, Cl μ j x x' := fun j x' => by
    obtain ⟨p', hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' hC hT' j).2.2.1 x'
    obtain ⟨p, h⟩ := μ.cotot j p'
    exact ⟨_, p, p', h, rfl, hp⟩
  have hL : ∃ a, (n ^ 1) ^ 2 = n ^ a := ⟨2, by ring⟩
  have hf : ∀ x, ∃ x', ∀ j, Cl μ j x x' := fun x => by
    choose α hα using fun j => tot j x
    obtain ⟨p, hp, hx⟩ := exists_txT_ne hq hn hC hT x
    obtain ⟨p', h, hp'⟩ := tot_G μ hA hL p hp
    obtain ⟨x', hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
      μ.c₀ x α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).1 ⟨0, by simp⟩)
      fun i => key i 1 p p' h hp hp' _ _ (hα i)).2 (mul_ne_zero μ.c₀_ne hx)
    refine ⟨x', fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ 0 z
  have hg : ∀ x', ∃ x, ∀ j, Cl μ j x x' := fun x' => by
    choose α hα using fun j => cotot j x'
    obtain ⟨p', hp', hx⟩ := exists_txT_ne hq' hn hC hT' x'
    obtain ⟨p, h, hp⟩ := cotot_G μ hA hL p' hp'
    obtain ⟨x, hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq' hn.pow p' hp') (txT_tendsto hq hn.pow p hp)
      μ.c₀⁻¹ x' α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).2 ⟨0, by simp⟩)
      fun i => by rw [key i 1 p p' h hp hp' _ _ (hα i), inv_mul_cancel_left₀ μ.c₀_ne]).2
      (mul_ne_zero (inv_ne_zero μ.c₀_ne) hx)
    refine ⟨x, fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ z 0
  obtain ⟨e, he, -⟩ := existsUnique_addEquiv_of_compatible_congr N.X N'.X n hpr.two_le (Cl μ) tot cotot
    (fun _ _ _ _ _ h h' => h.add μ h') (fun _ _ _ _ _ h h' => h.cong μ hA h') (fun _ _ _ _ _ h => h.shift μ _ _) hf hg
  refine ⟨e, fun j p p' h => ((he j _).cong μ hA ⟨p, p', h, rfl, rfl⟩).1 ⟨0, by simp⟩, fun j p p' h hp hp' χ => ?_⟩
  exact (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
    μ.c₀ χ (fun _ => e χ) (fun j => ⟨0, by simp⟩) fun i => key i j p p' h hp hp' _ _ (he i χ)).1 _
    fun j => ⟨0, by simp⟩

end GlobalTheory.MatchTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgreeStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  first | exact @GlobalTheory.MatchTerm.main | exact GlobalTheory.MatchTerm.main | (intros; apply GlobalTheory.MatchTerm.main <;> assumption)
end
