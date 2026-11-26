module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem weight_zero_power_series_surjective (O : Type) [CommRing O] {σ τ X : Type} [Finite τ] [AddCommGroup X] (wt : σ → X)
    (g : τ → (σ →₀ ℕ)) (hg0 : ∀ s, g s ≠ 0) (hgw : ∀ s, Finsupp.weight wt (g s) = 0)
    (hgen : ∀ n, Finsupp.weight wt n = 0 → ∃ d : τ →₀ ℕ, Finsupp.linearCombination ℕ g d = n) :
    ∃ φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O,
      (∀ F, φ F ∈ wtPart O wt 0) ∧ ∀ f ∈ wtPart O wt 0, ∃ F, φ F = f := by
  classical
  let a : τ → MvPowerSeries σ O := fun s => monomial (g s) 1
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun s => by
    show constantCoeff (monomial (g s) (1 : O)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg (hg0 s).symm]
  have hprod : ∀ d : τ →₀ ℕ, (d.prod fun s e => a s ^ e) = monomial (Finsupp.linearCombination ℕ g d) (1 : O) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' =>
      rw [Finsupp.prod_add_index' (by simp) (fun s m n => pow_add _ _ _), h, h', map_add (f := _), monomial_mul_monomial,
        one_mul]
    | single s k =>
      rw [Finsupp.prod_single_index (by simp), Finsupp.linearCombination_single]
      show (monomial (g s) (1 : O)) ^ k = _
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, monomial_mul_monomial, one_mul, succ_nsmul]
  have hw : ∀ d : τ →₀ ℕ, Finsupp.weight wt (Finsupp.linearCombination ℕ g d) = 0 := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' => rw [map_add (f := _), map_add (f := _), h, h', add_zero]
    | single s k => rw [Finsupp.linearCombination_single, map_nsmul, hgw, nsmul_zero]
  have hco : ∀ (F : MvPowerSeries τ O) n, coeff n (substAlgHom ha F) =
      ∑ᶠ d, coeff d F * (if n = Finsupp.linearCombination ℕ g d then 1 else 0) := by
    intro F n
    rw [coe_substAlgHom, coeff_subst ha]
    refine finsum_congr fun d => ?_
    rw [hprod, coeff_monomial, smul_eq_mul]
  refine ⟨substAlgHom ha, fun F n hn => ?_, fun f hf => ?_⟩
  · rw [hco]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (hw d)
  · choose! e he using hgen
    let F : MvPowerSeries τ O := fun d =>
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0
    have hF : ∀ d, coeff d F =
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0 :=
      fun _ => rfl
    refine ⟨F, ?_⟩
    ext n
    rw [hco]
    by_cases hn : Finsupp.weight wt n = 0
    · rw [finsum_eq_single _ (e n)]
      · rw [hF, he n hn, if_pos rfl, if_pos rfl, mul_one]
      · intro d hd
        by_cases h : n = Finsupp.linearCombination ℕ g d
        · rw [hF, ← h, if_neg hd, zero_mul]
        · rw [if_neg h, mul_zero]
    · rw [hf n hn]
      refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
      rw [if_neg, mul_zero]
      rintro rfl
      exact hn (hw d)

theorem UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsCO O (W.gr 0) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _
  obtain ⟨g, hg, hgen, -⟩ := UpperTheory.V.Alg.gordan W.σ X W.wt
  obtain ⟨φ, hφ, hs⟩ := weight_zero_power_series_surjective O W.wt (fun s : g => (s : W.σ →₀ ℕ)) (fun s => (hg s s.2).1)
    (fun s => (hg s s.2).2) (fun n hn => by
      have h := hgen n hn
      induction h using AddSubmonoid.closure_induction with
      | mem x hx => exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp⟩
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy ihx ihy =>
        have hw : ∀ z ∈ AddSubmonoid.closure (g : Set (W.σ →₀ ℕ)), Finsupp.weight W.wt z = 0 := by
          intro z hz
          induction hz using AddSubmonoid.closure_induction with
          | mem x hx => exact (hg x hx).2
          | zero => exact map_zero _
          | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
        obtain ⟨d, hd⟩ := ihx (hw x hx)
        obtain ⟨d', hd'⟩ := ihy (hw y hy)
        exact ⟨d + d', by rw [map_add (f := _), hd, hd']⟩)
  have hp : ∀ F, W.π (φ F) ∈ W.part 0 := fun F => ⟨φ F, hφ F, rfl⟩
  let p : MvPowerSeries g O →ₐ[O] W.gr 0 :=
    { toFun := fun F => ⟨⟨W.π (φ F), W.part_le_A (hp F)⟩, hp F⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun F G => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun F G => Subtype.ext (Subtype.ext (by simp))
      commutes' := fun c => Subtype.ext (Subtype.ext (by
        show W.π (φ (algebraMap O _ c)) = algebraMap O R c
        rw [AlgHom.commutes, AlgHom.commutes])) }
  haveI : IsCO O (MvPowerSeries g O) := UpperTheory.V.Alg.co_mvps O O g
  haveI : Nontrivial (W.gr 0) := ⟨⟨0, 1, fun h =>
    zero_ne_one (α := R) (congrArg (fun x : W.gr 0 => ((x : W.A) : R)) h)⟩⟩
  refine UpperTheory.V.Alg.co_quot O (MvPowerSeries g O) (W.gr 0) p ?_
  rintro ⟨⟨x, hxA⟩, f, hf, hx⟩
  obtain ⟨F, rfl⟩ := hs f hf
  exact ⟨F, Subtype.ext (Subtype.ext hx)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresMaximalIdealGrZeroEqSupSpanMonomials
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.monomial_mem_weight_zero {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (m : σ →₀ ℕ) (hm : Finsupp.weight wt m = 0) : (monomial m (1 : O) : MvPowerSeries σ O) ∈ wtPart O wt 0 := by
  classical
  intro n hn
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hm

theorem UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO O (W.gr 0)], (∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R) ∧
      ∃ u : Finset (W.gr 0), (∀ b ∈ u, ∃ n : W.σ →₀ ℕ, n ≠ 0 ∧ Finsupp.weight W.wt n = 0 ∧ ((b : W.A) : R) = n.prod fun s k => W.z s ^ k) ∧
        maximalIdeal (W.gr 0) = (maximalIdeal O).map (algebraMap O (W.gr 0)) ⊔ Ideal.span (u : Set (W.gr 0)) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz _
  classical
  let φ : W.gr 0 →ₐ[O] R :=
    { toFun := fun b => ((b : W.A) : R)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hφ : ∀ b : W.gr 0, φ b = ((b : W.A) : R) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
  have h1 : ∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R := fun b => by
    rw [← hφ, ← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
  refine ⟨h1, ?_⟩
  let mk : ∀ f : MvPowerSeries W.σ O, f ∈ wtPart O W.wt 0 → W.gr 0 := fun f hf =>
    ⟨⟨W.π f, W.part_le_A (j := 0) ⟨f, hf, rfl⟩⟩, ⟨f, hf, rfl⟩⟩
  have hmk : ∀ f hf, φ (mk f hf) = W.π f := fun _ _ => rfl
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W {n | n ≠ 0 ∧ Finsupp.weight W.wt n = 0} 0
    (fun n hn => hn.2)
  let U : μ → W.gr 0 := fun m => mk (monomial m.1 1) (UpperTheory.V.Alg.monomial_mem_weight_zero W.wt m.1 (hμ m.2).2)
  have hU : ∀ m : μ, φ (U m) = m.1.prod fun s k => W.z s ^ k := fun m => by
    show W.π (monomial m.1 1) = _
    rw [monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
    simp only [map_pow, WPres.z]
  have hUm : ∀ m : μ, U m ∈ maximalIdeal (W.gr 0) := fun m => by
    rw [h1, ← hφ, hU]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 (hμ m.2).1
    exact Ideal.prod_mem _ hs (Ideal.pow_mem_of_mem _ (hz s) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs)))
  have hle : Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) ≤ maximalIdeal (W.gr 0) := by
    rw [Ideal.span_le]
    intro b hb
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hUm m
  refine ⟨Finset.univ.image U, fun b hb => ?_, le_antisymm (fun b hb => ?_) (sup_le ?_ hle)⟩
  · obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨m.1, (hμ m.2).1, (hμ m.2).2, hU m⟩
  · obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
    obtain ⟨c, hc, hsum⟩ := hspan (f - C (constantCoeff f)) (fun n hn => by
      rw [map_sub, coeff_C]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg h0, sub_zero]
        exact hf n fun h => hn ⟨h0, h⟩)
    have hb' : b - algebraMap O (W.gr 0) (constantCoeff f) = ∑ m : μ, mk (c m.1) (hc m.1) * U m := by
      apply hinj
      have h2 := congrArg W.π hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, ← Finset.sum_coe_sort] at h2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, AlgHom.commutes, hφ, ← hfb, ← W.π.commutes]
      simp only [map_mul] at h2 ⊢
      exact h2
    have hs : b - algebraMap O (W.gr 0) (constantCoeff f) ∈
        Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) := by
      rw [hb']
      exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem U (Finset.mem_univ m))))
    have h3 : algebraMap O (W.gr 0) (constantCoeff f) ∈ maximalIdeal (W.gr 0) := by
      simpa using Ideal.sub_mem _ hb (hle hs)
    have h4 : constantCoeff f ∈ maximalIdeal O := fun h => h3 (h.map _)
    rw [← add_sub_cancel (algebraMap O (W.gr 0) (constantCoeff f)) b]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h4) hs
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha h
    exact ha (IsLocalHom.map_nonunit a h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {X : Type} [AddCommGroup X]

private lemma prod_pow_mem {S σ : Type} [CommRing S] (I : Ideal S) (z : σ → S) (hz : ∀ i, z i ∈ I)
    (m : σ →₀ ℕ) {n : ℕ} (hn : n ≤ m.degree) : (m.prod fun i k => z i ^ k) ∈ I ^ n := by
  refine Ideal.pow_le_pow_right hn ?_
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _

private lemma π_monomial (W : WPres O X R) (m : W.σ →₀ ℕ) :
    W.π (monomial m 1) = m.prod fun i k => W.z i ^ k := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
  simp [WPres.z]

private lemma exists_order (W : WPres O X R) (h : W.HasOrigin) (n : ℕ) :
    ∀ x ∈ RingHom.ker (W.origin h) ^ n, ∃ f, W.π f = x ∧ (n : ℕ∞) ≤ f.order := by
  induction n with
  | zero =>
    intro x _
    obtain ⟨f, hf⟩ := W.surj x
    exact ⟨f, hf, by simp⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
    · obtain ⟨f, rfl, hf⟩ := ih a ha
      obtain ⟨g, rfl⟩ := W.surj b
      rw [RingHom.mem_ker, W.origin_π] at hb
      refine ⟨f * g, map_mul _ _ _, le_trans ?_ (le_order_mul)⟩
      push_cast
      exact add_le_add hf (one_le_order_iff_constCoeff_eq_zero.2 hb)
    · rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
      exact ⟨f + g, map_add _ _ _, le_trans (le_min hf hg) (min_order_le_add)⟩

private lemma z_mem_ker (W : WPres O X R) (h : W.HasOrigin) (i : W.σ) : W.z i ∈ RingHom.ker (W.origin h) := by
  rw [RingHom.mem_ker, WPres.z, W.origin_π]
  simp

private lemma monomial_mem {σ : Type} (wt : σ → X) (m : σ →₀ ℕ) (c : O) :
    monomial m c ∈ wtPart O wt (Finsupp.weight wt m) := fun k hk => by
  classical
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hk rfl

private lemma A_fin (W : WPres O X R) (x : R) (hx : x ∈ W.A) :
    ∃ (T : Finset X) (f : MvPowerSeries W.σ O), W.π f = x ∧
      ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0 := by
  classical
  have hx' : x ∈ ⨆ j, W.part j := hx
  refine Submodule.iSup_induction W.part (motive := fun x => ∃ (T : Finset X) (f : MvPowerSeries W.σ O),
    W.π f = x ∧ ∀ m, Finsupp.weight W.wt m ∉ T → coeff m f = 0) hx' ?_ ?_ ?_
  · rintro j _ ⟨f, hf, rfl⟩
    exact ⟨{j}, f, rfl, fun m hm => hf m (by simpa using hm)⟩
  · exact ⟨∅, 0, map_zero _, fun _ _ => map_zero _⟩
  · rintro _ _ ⟨T, f, rfl, hf⟩ ⟨U, g, rfl, hg⟩
    refine ⟨T ∪ U, f + g, map_add _ _ _, fun m hm => ?_⟩
    rw [Finset.mem_union, not_or] at hm
    rw [map_add (f := _), hf m hm.1, hg m hm.2, add_zero]

private lemma A_sum (W : WPres O X R) (g : MvPowerSeries W.σ O) (hx : W.π g ∈ W.A) :
    ∃ T : Finset X, W.π g = ∑ j ∈ T, W.π (wcomp O W.wt j g) := by
  classical
  obtain ⟨T, f, hf, hT⟩ := A_fin W _ hx
  refine ⟨T, ?_⟩
  have h1 : f = ∑ j ∈ T, wcomp O W.wt j f := by
    ext m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · exact hT m hm
  have h2 : f - g ∈ RingHom.ker W.π := by rw [RingHom.mem_ker, map_sub, hf, sub_self]
  rw [← hf]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [h1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := W.homog _ h2 j
  rwa [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero] at this

end

theorem UpperTheory.V.Alg.ker_pow :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (n : ℕ),
      (RingHom.ker (W.origin h) ^ n).comap W.A.val = RingHom.ker (W.originA h) ^ n ∧ ∀ x : R, ∃ y : W.A, x - y ∈ RingHom.ker (W.origin h) ^ n := by
  intro O R _ _ _ X _ _ _ _ W h n
  classical
  refine ⟨le_antisymm (fun x hx => ?_) ?_, fun x => ?_⟩
  · obtain ⟨g, hg, hgn⟩ := exists_order W h n _ hx
    have hg' : W.π g = (x : R) := hg
    obtain ⟨T, hT⟩ := A_sum W g (hg' ▸ x.2)
    have hx' : x = ∑ j ∈ T, (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) := by
      apply Subtype.ext
      rw [← hg', hT]
      simp
    rw [hx']
    refine Ideal.sum_mem _ fun j _ => ?_
    obtain ⟨μ, hμ, hs⟩ := part_span O R X W {m | Finsupp.weight W.wt m = j ∧ n ≤ m.degree} j (fun _ hm => hm.1)
    obtain ⟨b, hb, hbs⟩ := hs (wcomp O W.wt j g) (fun m hm => by
      rw [coeff_wcomp]
      split_ifs with h1
      · refine coeff_of_lt_order (lt_of_lt_of_le ?_ hgn)
        have : ¬ n ≤ m.degree := fun h2 => hm ⟨h1, h2⟩
        exact_mod_cast not_le.1 this
      · rfl)
    have h3 : (⟨W.π (wcomp O W.wt j g), W.part_le_A ⟨_, wcomp_mem O W.wt j g, rfl⟩⟩ : W.A) =
        ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A ⟨_, hb m, rfl⟩⟩ : W.A) * m.prod fun i k => W.zA i ^ k := by
      apply Subtype.ext
      show W.π (wcomp O W.wt j g) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hbs, map_sum]
      simp [π_monomial, Finsupp.prod, WPres.zA]
    rw [h3]
    exact Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _
      (prod_pow_mem (RingHom.ker (W.originA h)) W.zA (fun i => z_mem_ker W h i) m (hμ hm).2)
  · exact Ideal.le_comap_pow (K := RingHom.ker (W.origin h)) W.A.val n
  · obtain ⟨f, rfl⟩ := W.surj x
    have hfin : {m : W.σ →₀ ℕ | m.degree < n}.Finite :=
      (Finsupp.finite_of_degree_le n).subset fun m (hm : m.degree < n) => hm.le
    set t : MvPowerSeries W.σ O := ∑ m ∈ hfin.toFinset, monomial m (coeff m f) with ht
    have htA : W.π t ∈ W.A := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ht, map_sum]
      exact Subalgebra.sum_mem _ fun m _ => W.part_le_A ⟨_, monomial_mem W.wt m _, rfl⟩
    refine ⟨⟨_, htA⟩, ?_⟩
    have key : ∃ μ : Finset (W.σ →₀ ℕ), (μ : Set _) ⊆ {m : W.σ →₀ ℕ | n ≤ m.degree} ∧
        ∀ f : MvPowerSeries W.σ O, (∀ m, m ∉ {m : W.σ →₀ ℕ | n ≤ m.degree} → coeff m f = 0) →
        ∃ b : (W.σ →₀ ℕ) → MvPowerSeries W.σ O, (∀ m, b m ∈ wtPart O (fun _ : W.σ => (0 : X)) 0) ∧
          f = ∑ m ∈ μ, b m * monomial m 1 :=
      part_span O (MvPowerSeries W.σ O) X (WPres.free O fun _ : W.σ => (0 : X))
        {m : W.σ →₀ ℕ | n ≤ m.degree} 0 (fun (m : W.σ →₀ ℕ) _ => by
          show Finsupp.weight (fun _ : W.σ => (0 : X)) m = 0
          simp [Finsupp.weight_apply, Finsupp.sum])
    obtain ⟨μ, hμ, hs⟩ := key
    obtain ⟨b, -, hbs'⟩ := hs (f - t) (fun m hm => by
      have hm0 : m.degree < n := not_le.1 hm
      have hm' : m ∈ hfin.toFinset := hfin.mem_toFinset.2 hm0
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, ht, map_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq, if_pos hm', sub_self])
    show W.π f - W.π t ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sub, hbs', map_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, π_monomial]
    exact Ideal.mul_mem_left _ _ (prod_pow_mem _ _ (fun i => z_mem_ker W h i) m (hμ hm))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem coprod_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : rename u g ∈ wtPart O wt j := fun n hn => by
  rw [coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem coprod_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem coprod_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] {σ : Type} [Finite σ]
    (F G : MvPowerSeries σ O →ₐ[O] R') (hF : ∀ s, F (X s) ∈ maximalIdeal R') (h : ∀ s, G (X s) = F (X s)) :
    G = F :=
  (co_ev O O R' σ (Algebra.ofId O R') _ hF).unique ⟨fun x => G.commutes x, h⟩
    ⟨fun x => F.commutes x, fun _ => rfl⟩

theorem UpperTheory.V.Alg.coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (T : Type) [Fintype T] (B : T → Type) [∀ v, CommRing (B v)] [∀ v, Algebra O (B v)] [∀ v, IsCO O (B v)] (WB : ∀ v, WPres O X (B v)), (∀ v s, (WB v).z s ∈ maximalIdeal (B v)) →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : ∀ v, B v →ₐ[O] R) (W : WPres O X R) (e : (Σ v, (WB v).σ) ≃ W.σ),
        (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ v, B v →ₐ[O] R'), ∃! F : R →ₐ[O] R', ∀ v, F.comp (i v) = f v) ∧
        (∀ v s, W.wt (e ⟨v, s⟩) = (WB v).wt s ∧ W.z (e ⟨v, s⟩) = i v ((WB v).z s)) ∧ (∀ v j, ∀ x ∈ (WB v).part j, i v x ∈ W.part j) ∧
        RingHom.ker W.π = ⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename fun s => e ⟨v, s⟩) := by
  intro O _ _ _ _ X _ T _ B _ _ _ WB hz
  classical
  let σ : Type := Σ v, (WB v).σ
  let wt : σ → X := fun p => (WB p.1).wt p.2
  let r : ∀ v, MvPowerSeries (WB v).σ O →ₐ[O] MvPowerSeries σ O :=
    fun v => rename fun s => (⟨v, s⟩ : σ)
  have hr : ∀ v j g, g ∈ wtPart O (WB v).wt j → r v g ∈ wtPart O wt j :=
    fun v j g hg => coprod_rename_mem _ wt _ (fun _ => rfl) hg
  have hrX : ∀ v s, r v (MvPowerSeries.X s) = MvPowerSeries.X ⟨v, s⟩ := fun v s => rename_X _ s
  let J : Ideal (MvPowerSeries σ O) := ⨆ v, (RingHom.ker (WB v).π).map (r v)
  have hJ : ∀ v g, (WB v).π g = 0 → r v g ∈ J := fun v g hg =>
    le_iSup (fun v => (RingHom.ker (WB v).π).map (r v)) v (Ideal.mem_map_of_mem _ hg)
  have hJm : J ≤ maximalIdeal _ := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg hu => by
    have h1 : IsUnit g := by
      have h2 := isUnit_constantCoeff _ hu
      rw [isUnit_iff_constantCoeff]
      rwa [show constantCoeff (r v g) = constantCoeff g from constantCoeff_rename _ g] at h2
    have h3 := h1.map (WB v).π
    rw [show (WB v).π g = 0 from hg] at h3
    exact not_isUnit_zero h3
  have hJh : IsHomog O wt J := by
    choose n g c hg hs using fun v => ker_gen O X (WB v).σ (WB v).wt _ (WB v).homog
    have : J = Ideal.span (Set.range fun p : Σ v, Fin (n v) => r p.1 (g p.1 p.2)) := by
      rw [Set.range_sigma_eq_iUnion_range, Ideal.span_iUnion]
      refine iSup_congr fun v => ?_
      rw [hs v, Ideal.map_span, ← Set.range_comp]
      rfl
    rw [this]
    exact coprod_homog wt _ (fun p => c p.1 p.2) fun p => hr _ _ _ (hg p.1 p.2)
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : Nontrivial (MvPowerSeries σ O ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJm)
  let π := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  have hk : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker O J
  haveI hR : IsCO O (MvPowerSeries σ O ⧸ J) := co_quot O (MvPowerSeries σ O) _ π hπ
  let i : ∀ v, B v →ₐ[O] MvPowerSeries σ O ⧸ J := fun v =>
    (Ideal.Quotient.liftₐ (RingHom.ker (WB v).π) (π.comp (r v)) fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hJ v g hg)).comp
      (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm.toAlgHom
  have hi : ∀ v g, i v ((WB v).π g) = π (r v g) := fun v g => by
    have : (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm ((WB v).π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [i, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨_, inferInstance, inferInstance, hR, i, ⟨σ, wt, π, hπ, by rw [hk]; exact hJh⟩, Equiv.refl _, ?_,
    fun v s => ⟨rfl, ?_⟩, ?_, hk⟩
  · intro R' _ _ _ f
    have ha : ∀ v s, f v ((WB v).z s) ∈ maximalIdeal R' := fun v s => by
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hz v s
    obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R' σ (Algebra.ofId O R') (fun p => f p.1 ((WB p.1).z p.2))
      fun p => ha p.1 p.2
    have hFr : ∀ v, F.comp (r v) = (f v).comp (WB v).π := fun v =>
      coprod_ext _ _ (ha v) fun s => by rw [AlgHom.comp_apply, hrX, hF]; rfl
    have hFJ : ∀ g ∈ J, F g = 0 := by
      have : J ≤ RingHom.ker F := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg => by
        show F.comp (r v) g = 0
        rw [hFr, AlgHom.comp_apply, show (WB v).π g = 0 from hg, map_zero]
      exact this
    refine ⟨Ideal.Quotient.liftₐ J F hFJ, fun v => ?_, fun G hG => ?_⟩
    · ext x
      obtain ⟨g, rfl⟩ := (WB v).surj x
      rw [AlgHom.comp_apply, hi]
      exact DFunLike.congr_fun (hFr v) g
    · have : G.comp π = F := coprod_ext _ _ (fun p => by rw [hF]; exact ha _ _) fun p => by
        rw [hF, ← hG, AlgHom.comp_apply, AlgHom.comp_apply, WPres.z, hi, hrX]
      ext x
      obtain ⟨g, rfl⟩ := hπ x
      exact DFunLike.congr_fun this g
  · show π _ = i v ((WB v).π _)
    rw [hi, hrX]
    rfl
  · rintro v j _ ⟨g, hg, rfl⟩
    exact ⟨r v g, hr v j g hg, (hi v g).symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PreservedCoefficient
private theorem coeff_mem_of_mem_maximalIdeal {O σ : Type} [CommRing O] [IsLocalRing O]
    {g : MvPowerSeries σ O} (hg : g ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O))
    (b : σ →₀ ℕ) :
    MvPowerSeries.coeff b g ∈ IsLocalRing.maximalIdeal O ^ (1 - Finsupp.degree b) := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← MvPowerSeries.isUnit_iff_constantCoeff]
    exact hg
  · have h1 : Finsupp.degree b ≠ 0 := fun h => hb ((Finsupp.degree_eq_zero_iff b).1 h)
    have h2 : 1 - Finsupp.degree b = 0 := by omega
    rw [h2, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    (N : ℕ),
    ∀ h ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N,
      ∀ (a : σ →₀ ℕ),
        (MvPowerSeries.coeff a : MvPowerSeries σ O → O) h ∈
          IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (σ →₀ ℕ) → ℕ) a) := by
  intro O σ _ _ N
  classical
  induction N with
  | zero =>
    intro h _ a
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    intro h hh
    rw [pow_succ] at hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro f hf g hg a
      rw [MvPowerSeries.coeff_mul]
      refine Submodule.sum_mem _ fun p hp => ?_
      have hsum : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree a := by
        rw [← map_add (f := _), Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
      have hmul := Ideal.mul_mem_mul (ih f hf p.1) (coeff_mem_of_mem_maximalIdeal hg p.2)
      rw [← pow_add] at hmul
      exact Ideal.pow_le_pow_right (by omega) hmul
    · intro f g hf hg a
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (hf a) (hg a)
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pres_new_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R) :
    F g - F (truncTotal n g : MvPolynomial σ R) ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have h := key (e (g - (truncTotal n g : MvPolynomial σ R))) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n (g - ((truncTotal n g : MvPolynomial σ R) : MvPowerSeries σ R)) = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply, map_sub] at h

private theorem pres_new_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (N : ℕ) :
    ∀ h ∈ maximalIdeal (MvPowerSeries σ O) ^ N, ∀ a : σ →₀ ℕ,
      coeff a h ∈ maximalIdeal O ^ (N - a.degree) :=
  _root_.UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff N

private theorem pres_new_wcomp {O σ X : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] (wt : σ → X)
    {i : X} (j : X) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt i) :
    wcomp O wt j h = if i = j then h else 0 := by
  ext a
  rw [coeff_wcomp]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    split_ifs with h1
    · rfl
    · exact (hh a h1).symm
  · rw [if_neg hij]
    split_ifs with h1
    · rw [map_zero]
      exact hh a (h1 ▸ Ne.symm hij)
    · simp

private theorem pres_new_mono {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (u : τ →₀ ℕ) : Φ (monomial u 1) ∈ wtPart O w (Finsupp.weight wt u) := by
  induction u using Finsupp.induction_linear with
  | zero => simpa using one_mem_wtPart O w
  | add u v hu hv =>
    have : (monomial (u + v) 1 : MvPowerSeries τ O) = monomial u 1 * monomial v 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_mul, map_add (f := _)]
    exact mul_mem_wtPart O w hu hv
  | single s n =>
    rw [← X_pow_eq, map_pow, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hΦ s)

private theorem pres_new_poly {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s)) (j : Y)
    (p : MvPolynomial τ O) : Φ (wcomp O wt j p) = wcomp O w j (Φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    have : ((MvPolynomial.monomial u c : MvPolynomial τ O) : MvPowerSeries τ O) = c • monomial u 1 := by
      rw [MvPolynomial.coe_monomial, ← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, map_smul, pres_new_wcomp w j (pres_new_mono wt w Φ hΦ u),
      pres_new_wcomp wt j (h := monomial u 1) (pres_new_mono wt wt (AlgHom.id O _) (X_mem_wtPart O wt) u)]
    split_ifs <;> simp
  | add p q hp hq => simp only [MvPolynomial.coe_add, map_add (f := _), hp, hq]

private theorem pres_new_comm {O σ τ Y : Type} [CommRing O] [IsLocalRing O] [IsHausdorff (maximalIdeal O) O]
    [Finite τ] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (hm : ∀ s, Φ (X s) ∈ maximalIdeal (MvPowerSeries σ O)) (j : Y)
    (g : MvPowerSeries τ O) : Φ (wcomp O wt j g) = wcomp O w j (Φ g) := by
  have hl := pres_new_low (maximalIdeal (MvPowerSeries σ O)) (Φ : MvPowerSeries τ O →+* MvPowerSeries σ O) hm
  ext a
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal O) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have h1 := pres_new_coeff _ _ (hl (k + a.degree) g) a
  have h2 := pres_new_coeff _ _ (hl (k + a.degree) (wcomp O wt j g)) a
  have h3 : ((truncTotal (k + a.degree) (wcomp O wt j g) : MvPolynomial τ O) : MvPowerSeries τ O) =
      wcomp O wt j (truncTotal (k + a.degree) g : MvPolynomial τ O) := by
    ext b
    simp only [coeff_wcomp, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]
    split_ifs <;> rfl
  rw [h3] at h2
  simp only [RingHom.coe_coe, Nat.add_sub_cancel, map_sub] at h1 h2
  rw [pres_new_poly wt w Φ hΦ] at h2
  rw [coeff_wcomp] at h2 ⊢
  split_ifs at h2 ⊢
  · simpa using sub_mem h2 h1
  · exact h2

theorem UpperTheory.V.Alg.pres_new :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (τ : Type) [Fintype τ] (wt : τ → X) (z : τ → R), (∀ s, z s ∈ maximalIdeal R ∧ z s ∈ W.part (wt s)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 →
      ∃ (W' : WPres O X R) (e : τ ≃ W'.σ), ∀ s, W'.z (e s) = z s ∧ W'.wt (e s) = wt s := by
  intro O _ _ _ _ Y _ _ _ _ R _ _ _ W _ τ _ wt z hz hgen
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries τ O) := co_mvps O O τ
  choose f hf hfz using fun s => (hz s).2
  have hfz' : ∀ s, W.π (f s) = z s := hfz
  have hfm : ∀ s, f s ∈ maximalIdeal (MvPowerSeries W.σ O) := fun s hu =>
    (hz s).1 (hfz' s ▸ hu.map W.π)
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := co_ev O O (MvPowerSeries W.σ O) τ (Algebra.ofId _ _) f hfm
  have hF : ∀ s, (W.π.comp Φ) (X s) = z s := fun s => by rw [AlgHom.comp_apply, hΦ, hfz']
  refine ⟨⟨τ, wt, W.π.comp Φ, ?_, ?_⟩, Equiv.refl _, fun s => ⟨hF s, rfl⟩⟩
  · refine co_surj O _ R _ (hgen.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hF s]
      refine Ideal.mem_map_of_mem _ fun hu => ?_
      simpa using isUnit_constantCoeff _ hu
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← (W.π.comp Φ).commutes]
      refine Ideal.mem_map_of_mem _ fun hu => hc ?_
      simpa [MvPowerSeries.algebraMap_apply] using isUnit_constantCoeff _ hu
  · intro g hg j
    show W.π (Φ _) = 0
    rw [pres_new_comm wt W.wt Φ (fun s => hΦ s ▸ hf s) (fun s => hΦ s ▸ hfm s)]
    exact W.homog _ hg j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartRank
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section

variable {O A X τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X]
  {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

private noncomputable def crLin (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) :
    A →ₗ[O] FractionRing O :=
  ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap

private theorem crLin_apply (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (f : A) :
    crLin φ i f = MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := rfl

private theorem crLin_sat (h : IsChart 𝒜 x wt φ) (i : τ) : ∀ f ∈ satSq x, crLin φ i f = 0 := by
  classical
  have h2 : ∀ f ∈ RingHom.ker x ^ 2, crLin φ i f = 0 := by
    intro f hf
    rw [sq] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
    have ha' : MvPowerSeries.coeff 0 (φ a) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x a = 0 from ha, map_zero]
    have hb' : MvPowerSeries.coeff 0 (φ b) = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const, show x b = 0 from hb, map_zero]
    rw [crLin_apply, map_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
    simp [Finset.Nat.antidiagonal_succ, ha', hb']
  rintro f ⟨c, hc, hf⟩
  have := h2 _ hf
  rw [map_smul] at this
  exact (smul_eq_zero.1 this).resolve_left hc

private theorem crLin_wt (h : IsChart 𝒜 x wt φ) (i : τ) {j : X} (hij : wt i ≠ j)
    {f : A} (hf : f ∈ 𝒜 j) : crLin φ i f = 0 :=
  h.graded j f hf _ (by simpa [Finsupp.weight_single] using hij)

private theorem crLin_const (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (i : τ) (c : O) :
    crLin φ i (algebraMap O A c) = 0 := by
  classical
  rw [crLin_apply, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp)]

private theorem cr_fixed (h : IsChart 𝒜 x wt φ) {j : X} (hj : j ≠ 0) {f : A} (hf : f ∈ 𝒜 j) : x f = 0 := by
  have h1 := h.graded j f hf 0 (by simpa using hj.symm)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.const] at h1
  exact IsFractionRing.injective O (FractionRing O) (by rw [h1, map_zero])

private theorem crLin_proj [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (i : τ) {j : X}
    (hij : wt i = j) (f : A) : crLin φ i (DirectSum.decompose 𝒜 f j) = crLin φ i f := by
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous k f =>
    by_cases hk : k = j
    · subst hk
      rw [DirectSum.decompose_of_mem_same 𝒜 f.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 f.2 hk, map_zero, crLin_wt h i (fun h' => hk (h'.symm.trans hij)) f.2]
  | add f g hf hg => simp [hf, hg]

private theorem cr_comp [DecidableEq X] [GradedAlgebra 𝒜] (h : IsChart 𝒜 x wt φ) (j : X) (f : A) :
    ∃ g : A, g ∈ 𝒜 j ∧ x g = 0 ∧ ∀ i, wt i = j → crLin φ i g = crLin φ i f := by
  have hm : (DirectSum.decompose 𝒜 f j : A) ∈ 𝒜 j := (DirectSum.decompose 𝒜 f j).2
  by_cases hj : j = 0
  · subst hj
    refine ⟨(DirectSum.decompose 𝒜 f 0 : A) - algebraMap O A (x (DirectSum.decompose 𝒜 f 0 : A)),
      sub_mem hm (SetLike.algebraMap_mem_graded 𝒜 _), by simp, fun i hi => ?_⟩
    rw [map_sub, crLin_const, sub_zero, crLin_proj h i hi]
  · exact ⟨_, hm, cr_fixed h hj hm, fun i hi => crLin_proj h i hi f⟩

end

theorem UpperTheory.V.Alg.chart_rank :
    ∀ (O A X : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X] (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (τ : Type) [Fintype τ] (wt : τ → X) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart 𝒜 x wt φ →
      ∀ j, Module.finrank O (cotLat x 𝒜 j) = Nat.card {i // wt i = j} := by
  intro O A X _ _ _ _ _ _ 𝒜 _ x τ _ wt φ h j
  classical
  rw [Nat.card_eq_fintype_card]
  let ψ : cotLat x 𝒜 j →ₗ[O] ({i // wt i = j} → FractionRing O) :=
    LinearMap.pi fun i => ((satSq x).liftQ (crLin φ i.1) (crLin_sat h i.1)) ∘ₗ (cotLat x 𝒜 j).subtype
  have hψ : ∀ (f : A) (hf : (satSq x).mkQ f ∈ cotLat x 𝒜 j) i, ψ ⟨_, hf⟩ i = crLin φ i.1 f := fun f hf i => rfl
  apply Module.finrank_eq_of_rank_eq
  apply le_antisymm
  · have hinj : Function.Injective ψ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      rintro ⟨_, f, hf, rfl⟩ h0
      apply Subtype.ext
      refine (Submodule.Quotient.mk_eq_zero _).2 (h.inj f hf.2 fun i => ?_)
      by_cases hi : wt i = j
      · exact congrFun h0 ⟨i, hi⟩
      · exact crLin_wt h i hi hf.1
    have h1 := LinearMap.rank_le_of_injective ψ hinj
    rwa [← IsLocalization.rank_eq (FractionRing O) (nonZeroDivisors O) le_rfl (N := {i // wt i = j} → FractionRing O),
      rank_fun'] at h1
  · choose g hg hg' using h.onto
    choose p hp hpx hpl using cr_comp h j
    have hm : ∀ i, (satSq x).mkQ (p (g i)) ∈ cotLat x 𝒜 j := fun i => ⟨_, ⟨hp _, hpx _⟩, rfl⟩
    have hli : LinearIndependent O fun i : {i // wt i = j} => (⟨_, hm i.1⟩ : cotLat x 𝒜 j) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h1 := congrFun (congrArg ψ hc) i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i, map_zero, map_smul, Pi.smul_apply, hψ,
        hpl _ _ i.2] at h1
      · exact (smul_eq_zero.1 h1).resolve_right (hg i.1)
      · intro k _ hk
        rw [map_smul, Pi.smul_apply, hψ, hpl _ _ i.2, crLin_apply,
          hg' k.1 i.1 (fun h' => hk (Subtype.ext h').symm), smul_zero]
      · simp
    have h2 := hli.cardinal_le_rank
    rwa [Cardinal.mk_fintype] at h2
end
