module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresIndep
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DensePiDecomposition
open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff {σ O : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    simp [h0]
  | insert i s _ ih =>
    intro f hf
    let h : MvPowerSeries σ O := fun n => if n i = 0 then coeff n f else 0
    have hh : ∀ n, coeff n h = if n i = 0 then coeff n f else 0 := fun _ => rfl
    have h1 : h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) := by
      refine ih h fun n hn => ?_
      rw [hh]
      split_ifs with hi
      · refine hf n fun j hj => ?_
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact hi
        · exact hn j hj
      · rfl
    have h2 : (X i : MvPowerSeries σ O) ∣ f - h := by
      refine X_dvd_iff.2 fun n hn => ?_
      rw [map_sub, hh, if_pos hn, sub_self]
    have h3 : f - h ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨i, rfl⟩)
    simpa using Ideal.add_mem _ h3 h1

open MvPowerSeries in
private theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp {σ O : Type} [CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O) :
    ∃ (c : O) (g : σ → MvPowerSeries σ O),
      f = algebraMap O (MvPowerSeries σ O) c + ∑ i, g i * X i := by
  classical
  have h := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.mem_span_of_coeff Finset.univ
    (f - algebraMap O (MvPowerSeries σ O) (coeff 0 f)) (by
      intro n hn
      have h0 : n = 0 := by
        ext i
        simpa using hn i (Finset.mem_univ i)
      subst h0
      simp [MvPowerSeries.algebraMap_apply])
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨coeff 0 f, g, by rw [hg]; ring⟩

theorem UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {X : Type} [inst_2 : AddCommGroup X] {R : Type}
      [inst_3 : CommRing R] [inst_4 : Algebra O R] [inst_5 : UpperTheory.V.Alg.IsCO O R] (W : UpperTheory.V.Alg.WPres O X R),
      (∀ (s : W.σ), W.z s ∈ IsLocalRing.maximalIdeal R) →
        ∀ (N : ℕ) (x : R), ∃ a ∈ W.A, x - a ∈ IsLocalRing.maximalIdeal R ^ N := by
  intro O _ _ X _ R _ _ _ W hz N
  induction N with
  | zero => intro x; exact ⟨0, W.A.zero_mem, by simp⟩
  | succ N ih =>
    intro x
    obtain ⟨f, rfl⟩ := W.surj x
    obtain ⟨c, g, rfl⟩ := UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.exists_decomp f
    choose a ha hm using fun i => ih (W.π (g i))
    refine ⟨algebraMap O R c + ∑ i, a i * W.z i, ?_, ?_⟩
    · exact W.A.add_mem (W.A.algebraMap_mem c)
        (W.A.sum_mem fun i _ => W.A.mul_mem (ha i) (W.part_le_A (W.z_mem i)))
    · have he : W.π (algebraMap O _ c + ∑ i, g i * MvPowerSeries.X i)
          - (algebraMap O R c + ∑ i, a i * W.z i) = ∑ i, (W.π (g i) - a i) * W.z i := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_add (f := _), AlgHom.commutes, map_sum, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, sub_mul]
        rfl
      rw [he, pow_succ]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (hm i) (hz i)
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pi_span_X {O σ : Type} [CommRing O] (s : Finset σ) :
    ∀ f : MvPowerSeries σ O, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → coeff n f = 0) →
      f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X s

private theorem pi_wcomp_mul {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X} (j : X)
    (a : MvPowerSeries σ O) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt c) :
    wcomp O wt j (a * h) = wcomp O wt (j - c) a * h := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 (wcomp O wt (j - c) a) * coeff p.2 h =
      if Finsupp.weight wt n = j then coeff p.1 a * coeff p.2 h else 0 := by
    intro p hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · have hn : Finsupp.weight wt n = Finsupp.weight wt p.1 + c := by
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add (f := _), h2]
      rw [coeff_wcomp, hn]
      by_cases h1 : Finsupp.weight wt p.1 = j - c
      · rw [if_pos h1, if_pos (by rw [h1]; abel)]
      · rw [if_neg h1, if_neg (fun h => h1 (by rw [← h]; abel)), zero_mul]
    · rw [hh _ h2]; simp
  rw [Finset.sum_congr rfl key]
  split_ifs <;> simp

section

variable {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type} [CommRing R]
  [Algebra O R] [IsCO O R] (W : WPres O X R)

private theorem pi_max_le (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i} := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := pi_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : algebraMap O R (constantCoeff f) ∈ W.part 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  have h5 := h2 (Ideal.span {y | y ∈ maximalIdeal R ∧ ∃ i, y ∈ W.part i})
    fun s => Ideal.subset_span ⟨hz s, _, W.z_mem s⟩
  simpa using add_mem h5 (Ideal.subset_span ⟨h3, _, h4⟩)

private theorem pi_pow_le (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) :
    maximalIdeal R ^ N ≤ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i} := by
  induction N with
  | zero =>
    intro x _
    have : (1 : R) ∈ Ideal.span {y | y ∈ maximalIdeal R ^ 0 ∧ ∃ i, y ∈ W.part i} :=
      Ideal.subset_span ⟨by simp, 0, SetLike.GradedOne.one_mem⟩
    simpa using Ideal.mul_mem_left _ x this
  | succ N ih =>
    refine le_trans (le_of_eq (pow_succ _ _)) (le_trans (Ideal.mul_mono ih (pi_max_le W hz)) ?_)
    rw [Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨a, ⟨ha, i, hi⟩, b, ⟨hb, k, hk⟩, rfl⟩
    refine Ideal.subset_span ⟨?_, i + k, SetLike.GradedMul.mul_mem hi hk⟩
    rw [pow_succ]
    exact Ideal.mul_mem_mul ha hb

private theorem pi_dense (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (x : R) :
    ∃ a ∈ W.A, x - a ∈ maximalIdeal R ^ N :=
  by apply _root_.UpperTheory.Reformulated.B.AdicDensityOfPresentationSubalgebra.pi_dense <;> assumption

private theorem pi_homog (hz : ∀ s, W.z s ∈ maximalIdeal R) (N : ℕ) (f : MvPowerSeries W.σ O)
    (hf : W.π f ∈ maximalIdeal R ^ N) (j : X) : W.π (wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
  have key : ∀ y ∈ Ideal.span {y | y ∈ maximalIdeal R ^ N ∧ ∃ i, y ∈ W.part i},
      ∃ g, W.π g = y ∧ ∀ a j, W.π (wcomp O W.wt j (a * g)) ∈ maximalIdeal R ^ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨ht, i, g, hg, rfl⟩ := ht
      refine ⟨g, rfl, fun a j => ?_⟩
      rw [pi_wcomp_mul W.wt j a hg, map_mul]
      exact Ideal.mul_mem_left _ _ ht
    | zero => exact ⟨0, map_zero _, fun a j => by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨g', rfl, hg'⟩ := hz
      refine ⟨g + g', map_add _ _ _, fun a j => ?_⟩
      rw [mul_add, map_add (f := _), map_add (f := _)]
      exact add_mem (hg a j) (hg' a j)
    | smul r y _ hy =>
      obtain ⟨g, rfl, hg⟩ := hy
      obtain ⟨q, rfl⟩ := W.surj r
      refine ⟨q * g, map_mul _ _ _, fun a j => ?_⟩
      rw [← mul_assoc]
      exact hg _ j
  obtain ⟨g, hg, hg'⟩ := key _ (pi_pow_le W hz N hf)
  have h1 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hg, sub_self]
  have h2 := W.homog _ h1 j
  rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at h2
  rw [h2]
  simpa using hg' 1 j

end

theorem UpperTheory.V.Alg.pres_indep :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ W' : WPres O X R, (∀ s, W'.z s ∈ maximalIdeal R) → (∀ s, W'.z s ∈ W.part (W'.wt s)) → ∀ j, W'.part j = W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz W' hz' hw j
  have hle : ∀ i, ∀ x ∈ W'.part i, x ∈ W.part i :=
    UpperTheory.V.Alg.map_part O X R W' hz' R W hz (AlgHom.id O R) hw
  refine le_antisymm (hle j) fun x hx => ?_
  refine UpperTheory.V.Alg.part_closed O X R W' hz' j x fun N => ?_
  obtain ⟨a, ha, hxa⟩ := pi_dense W' hz' N x
  have ha' : a ∈ ⨆ i, W'.part i := ha
  have hself : ∀ g ∈ wtPart O W.wt j, wcomp O W.wt j g = g := by
    intro g hg
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hg n h).symm
  have key : ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j := by
    refine Submodule.iSup_induction W'.part
      (motive := fun a => ∃ f, W.π f = a ∧ W.π (wcomp O W.wt j f) ∈ W'.part j) ha' ?_ ?_ ?_
    · intro i y hy
      obtain ⟨f, hf, hfy⟩ := hle i y hy
      have hfy' : W.π f = y := hfy
      refine ⟨f, hfy', ?_⟩
      by_cases hij : i = j
      · subst hij
        rw [hself f hf, hfy']
        exact hy
      · have : wcomp O W.wt j f = 0 := by
          ext n
          rw [coeff_wcomp]
          split_ifs with h
          · rw [hf n (fun h' => hij (h'.symm.trans h))]; simp
          · simp
        rw [this, map_zero]
        exact zero_mem _
    · exact ⟨0, map_zero _, by simp⟩
    · rintro a b ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
      refine ⟨f + g, by rw [map_add (f := _), hf, hg], ?_⟩
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hf' hg'
  obtain ⟨f, hf, hf'⟩ := key
  obtain ⟨g, hg, hgx⟩ := hx
  have hgx' : W.π g = x := hgx
  refine ⟨_, hf', ?_⟩
  have := pi_homog W hz N (g - f) (by rwa [map_sub, hgx', hf]) j
  rwa [map_sub, hself g hg, map_sub, hgx'] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartKer
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma order_of_mem {K τ : Type} [CommRing K] (n : ℕ) :
    ∀ g ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ n, (n : ℕ∞) ≤ g.order := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · refine le_trans ?_ le_order_mul
      push_cast
      exact add_le_add (ih a ha) (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · intro a b ha hb
      exact le_trans (le_min ha hb) min_order_le_add

private lemma coeff_map_zero {O K σ τ : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ]
    (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0) (N : ℕ) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < N → coeff m f = 0) (n : τ →₀ ℕ) (hn : n.degree < N) :
    coeff n (ψ f) = 0 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | N ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | N ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | N ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  have h1 : ψ f ∈ RingHom.ker (constantCoeff : MvPowerSeries τ K →+* K) ^ N := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hb, map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hπ : ψ (monomial m 1) = m.prod fun i k => ψ (MvPowerSeries.X i) ^ k := by
      rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
      simp
    rw [map_mul, hπ]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ hψ m (hμ hm))
  refine coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem N _ h1))
  exact_mod_cast hn

private lemma homog_ker {O K σ τ X : Type} [CommRing O] [CommRing K] [Algebra O K] [Fintype σ] [AddCommGroup X]
    (w : σ → X) (wt : τ → X) (ψ : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (MvPowerSeries.X i)) = 0)
    (hg : ∀ j, ∀ f ∈ wtPart O w j, ψ f ∈ wtPart K wt j) : IsHomog O w (RingHom.ker ψ) := by
  classical
  intro f hf j
  rw [RingHom.mem_ker] at hf ⊢
  ext n
  rw [map_zero]
  by_cases hn : Finsupp.weight wt n = j
  swap
  · exact hg j _ (wcomp_mem O w j f) n hn
  have hfin : {m : σ →₀ ℕ | m.degree ≤ n.degree}.Finite := Finsupp.finite_of_degree_le _
  set T : Finset X := insert j (hfin.toFinset.image (Finsupp.weight w)) with hT
  have h1 := coeff_map_zero ψ hψ (n.degree + 1) (f - ∑ i ∈ T, wcomp O w i f) (fun m hm => by
    have hm' : Finsupp.weight w m ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 (Nat.lt_succ_iff.1 hm)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos hm', sub_self]) n (Nat.lt_succ_self _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, hf, zero_sub, map_neg, neg_eq_zero, map_sum, map_sum,
    Finset.sum_eq_single_of_mem j (Finset.mem_insert_self _ _)] at h1
  · exact h1
  · intro i _ hi
    exact hg i _ (wcomp_mem O w i f) n (fun h => hi (h.symm.trans hn))

theorem UpperTheory.V.Alg.chart_ker :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      (RingHom.ker φ).IsPrime ∧ IsHomog O W.wt (RingHom.ker (φ.comp W.π)) ∧ RingHom.ker φ ≤ RingHom.ker (W.origin h) ∧
      (∀ D ∈ PtDer (W.origin h) O, ∀ f, φ f = 0 → D f = 0) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R') (x' : R' →ₐ[O] O) (φ' : R' →ₐ[O] MvPowerSeries τ (FractionRing O)), Function.Surjective p → x'.comp p = W.origin h → φ'.comp p = φ →
        IsChart (fun j => (W.part j).map p.toLinearMap) x' wt φ' := by
  intro O X R _ _ _ _ _ _ W h τ _ wt φ H
  have hle : ∀ f, φ f = 0 → W.origin h f = 0 := fun f hf => by
    have := H.const f
    rw [hf, map_zero] at this
    exact IsFractionRing.injective O (FractionRing O) (by rw [← this, map_zero])
  haveI : IsDomain (MvPowerSeries τ (FractionRing O)) := NoZeroDivisors.to_isDomain _
  refine ⟨RingHom.ker_isPrime _, ?_, hle, ?_, ?_⟩
  · refine homog_ker W.wt wt _ (fun i => ?_) (fun j f hf => H.graded j _ ⟨f, hf, rfl⟩)
    rw [AlgHom.comp_apply, H.const, W.origin_π]
    simp
  · intro D hD f hf
    obtain ⟨c, hc, hcf⟩ := H.inj f (hle f hf) (fun i => by rw [hf, map_zero])
    have key : ∀ g ∈ RingHom.ker (W.origin h) ^ 2, D g = 0 := by
      intro g hg
      rw [pow_two] at hg
      refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) ?_
      · rw [RingHom.mem_ker] at ha hb
        rw [hD a b, ha, hb, zero_smul, zero_smul, add_zero]
      · intro a b ha hb
        rw [map_add (f := _), ha, hb, add_zero]
    have := key _ hcf
    rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro R' _ _ p x' φ' hp hx hφ
    have hx1 : ∀ f, x' (p f) = W.origin h f := fun f => by rw [← hx]; rfl
    have hφ1 : ∀ f, φ' (p f) = φ f := fun f => by rw [← hφ]; rfl
    refine ⟨?_, fun f => ?_, fun i => ?_, fun f hf hl => ?_⟩
    · rintro j _ ⟨f, hf, rfl⟩
      show φ' (p f) ∈ _
      rw [hφ1]
      exact H.graded j f hf
    · obtain ⟨f, rfl⟩ := hp f
      rw [hφ1, hx1, H.const]
    · obtain ⟨f, hf⟩ := H.onto i
      exact ⟨p f, by rw [hφ1]; exact hf⟩
    · obtain ⟨f, rfl⟩ := hp f
      rw [hx1] at hf
      rw [hφ1] at hl
      obtain ⟨c, hc, hcf⟩ := H.inj f hf hl
      refine ⟨c, hc, ?_⟩
      rw [← map_smul]
      have h1 : RingHom.ker (W.origin h) ≤ (RingHom.ker x').comap p := fun g hg => by
        rw [Ideal.mem_comap, RingHom.mem_ker, hx1]
        exact hg
      exact Ideal.le_comap_pow (K := RingHom.ker x') p 2 (Ideal.pow_right_mono h1 2 hcf)
end
