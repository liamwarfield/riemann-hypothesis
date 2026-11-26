module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem co_span_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

theorem UpperTheory.V.Alg.co_span :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (i : B →ₐ[O] R) (S : Set R), S ⊆ maximalIdeal R →
      (∀ f f' : R →ₐ[O] DualNumber (ResidueField O), f.comp i = f'.comp i → (∀ s ∈ S, f s = f' s) → f = f') →
      maximalIdeal R ≤ Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
  intro O _ _ R _ _ _ B _ _ _ i S hS H x hx
  set I : Ideal R := Ideal.span S ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R := by
    refine sup_le (sup_le (Ideal.span_le.2 hS) (Ideal.map_le_iff_le_comap.2 fun b hb => ?_))
      (Ideal.pow_le_self two_ne_zero)
    show i b ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hb
  have hB : ∀ b ∈ maximalIdeal B, i b ∈ I := fun b hb =>
    Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hb))
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha => by
    have := hB (algebraMap O B a) (fun h => ha (IsLocalHom.map_nonunit a h))
    rwa [AlgHom.commutes] at this
  let N : Submodule O R := I.restrictScalars O ⊔ Submodule.span O {1}
  have hIN : ∀ y ∈ I, y ∈ N := fun y hy => Submodule.mem_sup_left hy
  have hON : ∀ a : O, algebraMap O R a ∈ N := fun a =>
    Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨a, (Algebra.algebraMap_eq_smul_one a).symm⟩)
  have hxN : N.mkQ x ≠ 0 := by
    intro h
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.mk_eq_zero N).1 h)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [← Algebra.algebraMap_eq_smul_one] at hyz
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hx (hIm hy)
      rwa [← hyz, add_sub_cancel_left] at this
    have h2 : a ∈ maximalIdeal O := fun h => h1 (h.map _)
    exact hxI (hyz ▸ I.add_mem hy (hO a h2))
  have htor : Module.IsTorsionBySet O (R ⧸ N) (maximalIdeal O) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective y
    show a • N.mkQ y = 0
    rw [← map_smul]
    refine (Submodule.Quotient.mk_eq_zero N).2 (hIN _ ?_)
    rw [Algebra.smul_def]
    exact I.mul_mem_right _ (hO a ha)
  obtain ⟨φ, hφ⟩ := co_span_dual O _ htor _ hxN
  let D : R →ₗ[O] ResidueField O := φ ∘ₗ N.mkQ
  have hD : ∀ y ∈ N, D y = 0 := fun y hy => by
    show φ (N.mkQ y) = 0
    rw [show N.mkQ y = 0 from (Submodule.Quotient.mk_eq_zero N).2 hy, map_zero]
  have hres : ∀ (y : R) (a : O), y - algebraMap O R a ∈ maximalIdeal R → res O R y = algebraMap O _ a :=
    fun y a ha => by
      have := (res_eq_zero_iff O R _).2 ha
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  have hmul : ∀ y z, D (y * z) = res O R y * D z + D y * res O R z := fun y z => by
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
    obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) z
    have h1 : D ((y - algebraMap O R a) * (z - algebraMap O R b)) = 0 :=
      hD _ (hIN _ (Ideal.mem_sup_right (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)))
    have h2 : y * z = (y - algebraMap O R a) * (z - algebraMap O R b) + a • z + b • y
        - algebraMap O R (a * b) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [h2, map_sub, map_add (f := _), map_add (f := _), h1, hD _ (hON _), map_smul, map_smul, hres y a ha, hres z b hb]
    simp only [Algebra.smul_def]; ring
  let f : R →ₐ[O] DualNumber (ResidueField O) :=
    { toFun := fun y => (res O R y, D y)
      map_one' := by
        ext
        · exact map_one (res O R)
        · exact hD _ (by simpa using hON 1)
      map_mul' := fun y z => by
        ext
        · exact map_mul (res O R) y z
        · exact hmul y z
      map_zero' := by
        ext
        · exact map_zero (res O R)
        · exact map_zero D
      map_add' := fun y z => by
        ext
        · exact map_add (res O R) y z
        · exact map_add D y z
      commutes' := fun a => by
        ext
        · exact (res O R).commutes a
        · exact hD _ (hON a) }
  let f' : R →ₐ[O] DualNumber (ResidueField O) :=
    (TrivSqZeroExt.inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
  have key : ∀ y, D y = 0 → f y = f' y := fun y hy => by
    ext
    · rfl
    · exact hy
  have hff : f = f' := by
    refine H f f' (AlgHom.ext fun b => key _ ?_) fun s hs => key _ (hD _ (hIN _ ?_))
    · obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) b
      have := hD _ (hIN _ (hB _ ha))
      rwa [map_sub, AlgHom.commutes, map_sub, hD _ (hON a), sub_zero] at this
    · exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span hs))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_fin_min {σ : Type} [Fintype σ] (P : (σ →₀ ℕ) → Prop) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m ∈ T, P m) ∧ ∀ n, P n → ∃ m ∈ T, m ≤ n := by
  classical
  have hfin : {m : σ →₀ ℕ | Minimal P m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, ?_⟩
  intro n hn
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | P x}).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

private theorem exists_decomp {O σ X : Type} [CommRing O] [Fintype σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) :
    ∃ (T : Finset (σ →₀ ℕ)) (g : (σ →₀ ℕ) → MvPowerSeries σ O), (∀ m ∈ T, g m ∈ wtPart O wt 0) ∧
      f = ∑ m ∈ T, monomial m (1 : O) * g m := by
  classical
  obtain ⟨T, hTP, hT⟩ := exists_fin_min (fun n => coeff n f ≠ 0)
  choose! c hcT hcle using hT
  obtain ⟨g, hg⟩ : ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, ∀ m k,
      coeff k (g m) = if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0 :=
    ⟨fun m k => if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
  have hwt : ∀ n, coeff n f ≠ 0 → Finsupp.weight wt n = j := by
    intro n hn
    by_contra h
    exact hn (hf n h)
  refine ⟨T, g, ?_, ?_⟩
  · intro m hmT k hk
    rw [hg, if_neg]
    rintro ⟨h1, h2⟩
    apply hk
    have hm : Finsupp.weight wt m = j := hwt m (hTP m hmT)
    have hkm := hwt _ h1
    rw [map_add (f := _), hm] at hkm
    simpa using hkm
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl
      (g := fun m => if c n = m then (if coeff n f ≠ 0 then coeff n f else 0) else 0),
      Finset.sum_ite_eq]
    · by_cases hn : coeff n f ≠ 0
      · rw [if_pos (hcT n hn), if_pos hn]
      · push_neg at hn
        rw [hn]
        simp
    · intro m _
      rw [MvPowerSeries.coeff_monomial_mul, one_mul]
      by_cases hmn : m ≤ n
      · rw [if_pos hmn, hg, tsub_add_cancel_of_le hmn]
        by_cases h1 : coeff n f ≠ 0 <;> by_cases h2 : c n = m <;> simp [h1, h2]
      · rw [if_neg hmn]
        by_cases h1 : coeff n f ≠ 0
        · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
          simp [h3]
        · push_neg at h1
          simp [h1]

private theorem monomial_eq_prod {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  have key : ∀ s : Finset σ, ∏ i ∈ s, (MvPowerSeries.X i : MvPowerSeries σ O) ^ (m i) =
      monomial (∑ i ∈ s, Finsupp.single i (m i)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [MvPowerSeries.monomial_zero_one]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, MvPowerSeries.X_pow_eq,
        MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [key, Finsupp.univ_sum_single]

theorem UpperTheory.V.Alg.gr_gen :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R), Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) = ⊤ := by
  intro O R _ _ _ X _ _ _ W
  classical
  haveI := W.fin
  rw [Algebra.eq_top_iff]
  rintro ⟨x, hx⟩
  refine Submodule.iSup_induction' (p := W.part)
    (motive := fun x h => (⟨x, h⟩ : W.A) ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA))
    ?_ ?_ ?_ hx
  · intro j y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨T, g, hg, hfe⟩ := exists_decomp W.wt j f hf
    have hg' : ∀ m, (if m ∈ T then g m else 0) ∈ wtPart O W.wt 0 := by
      intro m
      split_ifs with h
      · exact hg m h
      · exact zero_mem _
    let e : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (if m ∈ T then g m else 0), W.part_le_A (Submodule.mem_map_of_mem (hg' m))⟩
    have he : ∀ m, e m ∈ W.gr 0 := fun m => Submodule.mem_map_of_mem (hg' m)
    have hmem : (∑ m ∈ T, (∏ i, W.zA i ^ m i) * e m) ∈
        Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
      · refine Subalgebra.prod_mem _ fun i _ => pow_mem ?_ _
        exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (he m))
    convert hmem using 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, e, WPres.zA, WPres.z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AlgHom.toLinearMap_apply, hfe, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [if_pos hm, map_mul, monomial_eq_prod, map_prod]
    simp only [map_pow]
  · exact Subalgebra.zero_mem _
  · intro x y _ _ ihx ihy
    exact Subalgebra.add_mem _ ihx ihy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartClosed
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem wcomp_mul_homog {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_pos]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, if_neg, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add (f := _), h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem homog_of_span {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) :
    IsHomog O wt (Ideal.span S) := by
  intro f hf j
  have key : ∀ b : MvPowerSeries σ O, ∀ j, wcomp O wt j (b * f) ∈ Ideal.span S := by
    induction hf using Submodule.span_induction with
    | mem a ha =>
      intro b j
      obtain ⟨c, hc⟩ := hS a ha
      rw [wcomp_mul_homog wt hc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ha)
    | zero => intro b j; simp
    | add x y _ _ hx hy =>
      intro b j
      rw [mul_add, map_add (f := _)]
      exact add_mem (hx b j) (hy b j)
    | smul r x _ hx =>
      intro b j
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _ j
  simpa using key 1 j

private theorem homog_span_pow {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (S : Set (MvPowerSeries σ O)) (hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O wt c) (N : ℕ) :
    IsHomog O wt (Ideal.span S ^ N) := by
  have key : ∃ T : Set (MvPowerSeries σ O), (∀ a ∈ T, ∃ c, a ∈ wtPart O wt c) ∧
      Ideal.span S ^ N = Ideal.span T := by
    induction N with
    | zero =>
      refine ⟨{1}, ?_, by simp⟩
      rintro a rfl
      exact ⟨0, one_mem_wtPart O wt⟩
    | succ n ih =>
      obtain ⟨T, hT, hT'⟩ := ih
      refine ⟨_, ?_, by rw [pow_succ, hT', Ideal.span_mul_span']⟩
      rintro _ ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, hc⟩ := hT a ha
      obtain ⟨d, hd⟩ := hS b hb
      exact ⟨c + d, mul_mem_wtPart O wt hc hd⟩
  obtain ⟨T, hT, hT'⟩ := key
  rw [hT']
  exact homog_of_span wt T hT

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

theorem UpperTheory.V.Alg.part_closed :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (x : R), (∀ N : ℕ, ∃ y ∈ W.part j, x - y ∈ maximalIdeal R ^ N) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ hR W hz j x hx
  classical
  have hl : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hn : IsNoetherianRing R := hR.toIsNoetherian
  let S : Set (MvPowerSeries W.σ O) :=
    Set.range MvPowerSeries.X ∪ algebraMap O _ '' (maximalIdeal O : Set O)
  have hS : ∀ a ∈ S, ∃ c, a ∈ wtPart O W.wt c := by
    rintro _ (⟨i, rfl⟩ | ⟨a, -, rfl⟩)
    · exact ⟨_, X_mem_wtPart O W.wt i⟩
    · refine ⟨0, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart O W.wt)
  have hle : (Ideal.span S).map W.π ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact hz i
    · show W.π (algebraMap O _ a) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact fun h => ha (IsLocalHom.map_nonunit a h)
  have hmap : (Ideal.span S).map W.π = maximalIdeal R := by
    refine le_antisymm hle fun r hr => ?_
    obtain ⟨f, rfl⟩ := W.surj r
    have h1 : f - algebraMap O _ (constantCoeff f) ∈ Ideal.span S := by
      refine Ideal.span_mono Set.subset_union_left (mem_span_X _ ?_)
      simp [MvPowerSeries.algebraMap_apply]
    have h2 : constantCoeff f ∈ maximalIdeal O := fun hu =>
      hr ((MvPowerSeries.isUnit_iff_constantCoeff.2 hu).map W.π)
    have h3 : algebraMap O _ (constantCoeff f) ∈ Ideal.span S :=
      Ideal.subset_span (Or.inr ⟨_, h2, rfl⟩)
    exact Ideal.mem_map_of_mem _ (by simpa using add_mem h1 h3)
  obtain ⟨f, rfl⟩ := W.surj x
  have key : ∀ N : ℕ, W.π (f - wcomp O W.wt j f) ∈ maximalIdeal R ^ N := by
    intro N
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx N
    rw [← hmap, ← Ideal.map_pow] at hxy ⊢
    obtain ⟨g, hg, hgxy⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hxy
    have h1 : f - y - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, map_sub, hgxy]
      exact sub_self _
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j y = y := by
      ext n
      rw [coeff_wcomp]
      split_ifs with h
      · rfl
      · exact (hy n h).symm
    have h4 : g - wcomp O W.wt j g ∈ Ideal.span S ^ N :=
      sub_mem hg (homog_span_pow W.wt S hS N g hg j)
    have h5 : f - wcomp O W.wt j f =
        (f - y - g) - wcomp O W.wt j (f - y - g) + (g - wcomp O W.wt j g) := by
      rw [map_sub, map_sub, h3]; ring
    rw [h5, map_add (f := _), (RingHom.mem_ker).1 (sub_mem h1 h2), zero_add]
    exact Ideal.mem_map_of_mem _ h4
  have h0 : W.π (f - wcomp O W.wt j f) = 0 := by
    have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
    rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
    exact key
  rw [map_sub, sub_eq_zero] at h0
  exact ⟨_, wcomp_mem O W.wt j f, h0.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Gordan
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.gordan_dickson (σ : Type) [Finite σ] (S : Set (σ →₀ ℕ)) :
    ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, m ∈ S) ∧ ∀ n ∈ S, ∃ m ∈ μ, m ≤ n := by
  classical
  haveI := Fintype.ofFinite σ
  have hfin : {m : σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, fun n hn => ?_⟩
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

theorem UpperTheory.V.Alg.gordan :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X), ∃ g : Finset (σ →₀ ℕ), (∀ n ∈ g, n ≠ 0 ∧ Finsupp.weight wt n = 0) ∧
      (∀ n, Finsupp.weight wt n = 0 → n ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ))) ∧
      ∀ j, ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, Finsupp.weight wt m = j) ∧ ∀ n, Finsupp.weight wt n = j → ∃ m ∈ μ, m ≤ n := by
  intro σ _ X _ _ _ wt
  classical
  obtain ⟨g, hgS, hg⟩ := gordan_dickson σ {n | n ≠ 0 ∧ Finsupp.weight wt n = 0}
  refine ⟨g, hgS, ?_, fun j => ?_⟩
  · intro n
    induction n using WellFoundedLT.induction with
    | _ n ih =>
      intro hn
      by_cases h0 : n = 0
      · rw [h0]
        exact zero_mem _
      · obtain ⟨m, hm, hmn⟩ := hg n ⟨h0, hn⟩
        have hm' := hgS m hm
        have hsplit : n = m + (n - m) := (add_tsub_cancel_of_le hmn).symm
        have hw : Finsupp.weight wt (n - m) = 0 := by
          have h1 := hn
          rw [hsplit, map_add (f := _), hm'.2, zero_add] at h1
          exact h1
        have hlt : n - m < n := by
          refine lt_of_le_of_ne tsub_le_self fun h => hm'.1 ?_
          have h2 : m + (n - m) = n := add_tsub_cancel_of_le hmn
          rw [h] at h2
          simpa using h2
        rw [hsplit]
        exact add_mem (AddSubmonoid.subset_closure hm) (ih _ hlt hw)
  · obtain ⟨μ, hμS, hμ⟩ := gordan_dickson σ {n | Finsupp.weight wt n = j}
    exact ⟨μ, hμS, hμ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrInternal
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_internal :
    ∀ (O X R : Type) [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R), DirectSum.IsInternal W.gr := by
  intro O X R _ _ _ _ _ W
  have hhom := W.homog
  unfold IsHomog at hhom
  have hK : ∀ (j : X) (f g : MvPowerSeries W.σ O), W.π f = W.π g →
      W.π (wcomp O W.wt j f) = W.π (wcomp O W.wt j g) := by
    intro j f g hfg
    have hker : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker]
      simp [hfg]
    have h2 := hhom (f - g) hker j
    rw [RingHom.mem_ker] at h2
    simp only [map_sub] at h2
    exact sub_eq_zero.mp (by simpa using h2)
  have hself : ∀ (j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt j →
      wcomp O W.wt j f = f := by
    intro j f hf
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  have hoff : ∀ (i j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt i → i ≠ j →
      wcomp O W.wt j f = 0 := by
    intro i j f hf hij
    ext n
    rw [coeff_wcomp, map_zero]
    split_ifs with h
    · exact hf n (fun h' => hij (h'.symm.trans h))
    · rfl
  have hgr : ∀ (i : X) (y : W.A), y ∈ W.gr i ↔ y.1 ∈ W.part i := fun i y => Iff.rfl
  have hpart : ∀ (i : X) (x : R), x ∈ W.part i ↔ ∃ f ∈ wtPart O W.wt i, W.π f = x := by
    intro i x
    exact Submodule.mem_map
  let T : X → Submodule O W.A := fun j =>
    { carrier := {y | ∀ f, W.π f = y.1 → W.π (wcomp O W.wt j f) = 0}
      add_mem' := by
        intro a b ha hb f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        obtain ⟨fb, hfb⟩ := W.surj b.1
        have e : W.π f = W.π (fa + fb) := by
          rw [hf, map_add (f := _), hfa, hfb]
          rfl
        rw [hK j f (fa + fb) e, map_add (f := _), map_add (f := _), ha fa hfa, hb fb hfb, add_zero]
      zero_mem' := by
        intro f hf
        have e : W.π f = W.π 0 := by
          rw [hf, map_zero]
          rfl
        rw [hK j f 0 e, map_zero, map_zero]
      smul_mem' := by
        intro c a ha f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        have e : W.π f = W.π (c • fa) := by
          rw [hf, map_smul, hfa]
          rfl
        rw [hK j f (c • fa) e, map_smul, map_smul, ha fa hfa, smul_zero] }
  have hT : ∀ (i j : X), i ≠ j → W.gr i ≤ T j := by
    intro i j hij y hy f hf
    obtain ⟨g, hg, hgy⟩ := (hpart i y.1).mp ((hgr i y).mp hy)
    rw [hK j f g (hf.trans hgy.symm), hoff i j g hg hij, map_zero]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ i, ⨆ (_ : i ≠ j), W.gr i) ≤ T j := iSup₂_le fun i hij => hT i j hij
    have hxT := hle hx'
    obtain ⟨g, hg, hgx⟩ := (hpart j x.1).mp ((hgr j x).mp hx)
    have h0 := hxT g hgx
    rw [hself j g hg, hgx] at h0
    exact Subtype.ext h0
  · rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    have hle : ∀ i, W.part i ≤ LinearMap.range W.A.val.toLinearMap := by
      intro i x hx
      exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    have hmap : Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) = ⨆ i, W.part i := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun i => Submodule.map_comap_eq_self (hle i)
    have hmem : a ∈ Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) := by
      rw [hmap]
      exact ha
    obtain ⟨b, hb, hba⟩ := hmem
    have : b = ⟨a, ha⟩ := Subtype.ext hba
    rw [← this]
    exact hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private noncomputable def tchU (n : ℕ) (O : Type) [CommRing O] (i : Fin n) : (MvPowerSeries (Fin n) O)ˣ :=
  (show IsUnit (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) O) from
    MvPowerSeries.isUnit_iff_constantCoeff.2 (by simp)).unit

private lemma tchU_val (n : ℕ) (O : Type) [CommRing O] (i : Fin n) :
    (tchU n O i : MvPowerSeries (Fin n) O) = 1 + MvPowerSeries.X i := IsUnit.unit_spec _

private lemma tch_poly (n : ℕ) (R : Type) [CommRing R] {X : Type} (s : Finset X) (x : X → R)
    (e : X → Fin n →₀ ℕ) (he : Set.InjOn e s)
    (h : ∑ j ∈ s, (∏ i, (1 + MvPowerSeries.X i : MvPowerSeries (Fin n) R) ^ (e j i)) * C (x j) = 0) :
    ∀ j ∈ s, x j = 0 := by
  classical
  have h1 : (∑ j ∈ s, (∏ i, (1 + MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (e j i)) *
      MvPolynomial.C (x j)) = 0 := by
    apply MvPolynomial.coe_injective (Fin n) R
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.coe_zero, ← h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_prod]
    simp
  have h2 := congrArg (MvPolynomial.aeval (R := R)
    (fun i : Fin n => (MvPolynomial.X i - 1 : MvPolynomial (Fin n) R))) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h2
  have h3 : ∑ j ∈ s, MvPolynomial.monomial (e j) (x j) = 0 := by
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp [map_prod, mul_comm]
  intro j hj
  have h4 := congrArg (AddMonoidAlgebra.coeff · (e j)) h3
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single j] at h4
  · simpa using h4
  · intro k hk hkj
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hh
    exact hkj (he hk hj hh)
  · intro h; exact absurd hj h

theorem UpperTheory.V.Alg.tchar :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (n : ℕ) (t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ), (∀ j, constantCoeff (t j : MvPowerSeries (Fin n) O) = 1) ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (s : Finset X) (x : X → R),
        ∑ j ∈ s, MvPowerSeries.map (algebraMap O R) (t (Multiplicative.ofAdd j) : MvPowerSeries (Fin n) O) * C (x j) = 0 → ∀ j ∈ s, x j = 0 := by
  intro O _ _ X _ _ _
  classical
  let n := Module.finrank ℤ X
  let b : Module.Basis (Fin n) ℤ X := Module.finBasis ℤ X
  let t : Multiplicative X →* (MvPowerSeries (Fin n) O)ˣ :=
    { toFun := fun j => ∏ i, tchU n O i ^ (b.repr j.toAdd i)
      map_one' := by simp
      map_mul' := by
        intro a c
        simp [zpow_add, Finset.prod_mul_distrib] }
  have ht : ∀ j : X, t (Multiplicative.ofAdd j) = ∏ i, tchU n O i ^ (b.repr j i) := fun j => rfl
  refine ⟨n, t, ?_, ?_⟩
  · intro j
    have h1 : ∀ i, Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (tchU n O i) = 1 := by
      intro i
      ext
      simp [tchU_val]
    have h2 : Units.map (constantCoeff : MvPowerSeries (Fin n) O →+* O).toMonoidHom (t j) = 1 := by
      have := ht j.toAdd
      rw [ofAdd_toAdd] at this
      rw [this, map_prod]
      simp only [map_zpow, h1, one_zpow, Finset.prod_const_one]
    simpa using congrArg Units.val h2
  · intro R _ _ s x h
    let N : ℕ := ∑ j ∈ s, ∑ i, (b.repr j i).natAbs
    have hN : ∀ j ∈ s, ∀ i, 0 ≤ b.repr j i + N := by
      intro j hj i
      have h1 : (b.repr j i).natAbs ≤ ∑ i, (b.repr j i).natAbs :=
        Finset.single_le_sum (f := fun i => (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have h2 : ∑ i, (b.repr j i).natAbs ≤ N :=
        Finset.single_le_sum (f := fun j => ∑ i, (b.repr j i).natAbs) (fun _ _ => Nat.zero_le _) hj
      omega
    let e : X → Fin n →₀ ℕ := fun j => Finsupp.equivFunOnFinite.symm fun i => (b.repr j i + N).toNat
    have he : ∀ j i, e j i = (b.repr j i + N).toNat := fun j i => rfl
    refine tch_poly n R s x e ?_ ?_
    · intro j hj k hk hjk
      apply b.repr.injective
      ext i
      have h1 := he j i
      rw [hjk, he] at h1
      have := hN j hj i
      have := hN k hk i
      omega
    · have h1 := congrArg (fun y => MvPowerSeries.map (algebraMap O R)
        ((∏ i, tchU n O i ^ (N : ℤ) : (MvPowerSeries (Fin n) O)ˣ) : MvPowerSeries (Fin n) O) * y) h
      simp only [mul_zero] at h1
      rw [Finset.mul_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, ht, ← Finset.prod_mul_distrib]
      congr 1
      have h2 : ∀ i, tchU n O i ^ (N : ℤ) * tchU n O i ^ (b.repr j i) = tchU n O i ^ (e j i) := by
        intro i
        rw [← zpow_add, ← zpow_natCast, he, Int.toNat_of_nonneg (hN j hj i), add_comm]
      simp only [h2]
      simp [map_prod, tchU_val]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Carver
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem between_fin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b)
    (A B : Set ℝ) (hA : A.Finite) (hB : B.Finite) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x ∈ D, (∀ a ∈ A, a < x) ∧ ∀ b ∈ B, x < b := by
  obtain ⟨a0, h1, h2⟩ : ∃ a0 : ℝ, (∀ a ∈ A, a ≤ a0) ∧ ∀ b ∈ B, a0 < b := by
    rcases A.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨m, hm⟩ := hB.bddBelow
      exact ⟨m - 1, by simp, fun b hb => by linarith [hm hb]⟩
    · obtain ⟨a0, ha0, hmax⟩ := Set.exists_max_image A id hA hne
      exact ⟨a0, hmax, h a0 ha0⟩
  obtain ⟨b0, h3, h4⟩ : ∃ b0 : ℝ, a0 < b0 ∧ ∀ b ∈ B, b0 ≤ b := by
    rcases B.eq_empty_or_nonempty with rfl | hne
    · exact ⟨a0 + 1, by linarith, by simp⟩
    · obtain ⟨b0, hb0, hmin⟩ := Set.exists_min_image B id hB hne
      exact ⟨b0, h2 b0 hb0, hmin⟩
  obtain ⟨x, hx, h5, h6⟩ := hD a0 b0 h3
  exact ⟨x, hx, fun a ha => lt_of_le_of_lt (h1 a ha) h5, fun b hb => lt_of_lt_of_le h6 (h4 b hb)⟩

private theorem zsmul_mem_pos {M : Type} [AddCommGroup M] (H : Set M)
    (hH : ∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) (v : M) (hv : v ∈ H) (k : ℤ) (hk : 0 < k) : k • v ∈ H := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
  clear hk
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    have : (((n + 1 : ℕ) : ℤ) + 1) • v = ((n : ℤ) + 1) • v + v := by
      push_cast; rw [add_smul ((n : ℤ) + 1) 1 v, one_smul]
    rw [this]; exact hH _ ih _ hv

private theorem fourier_motzkin (D : Set ℝ) (hD : ∀ a b : ℝ, a < b → ∃ x ∈ D, a < x ∧ x < b) :
    ∀ (d : ℕ) (F H : Set ((Fin d → ℤ) × ℝ)), F.Finite → F ⊆ H → (∀ u ∈ H, ∀ v ∈ H, u + v ∈ H) →
      (∀ v ∈ H, v.1 = 0 → v.2 < 0) →
      ∃ φ : Fin d → ℝ, (∀ i, φ i ∈ D) ∧ ∀ v ∈ F, ∑ i, (v.1 i : ℝ) * φ i + v.2 < 0 := by
  intro d
  induction d with
  | zero =>
    intro F H _ hFH _ h0
    refine ⟨Fin.elim0, fun i => i.elim0, fun v hv => ?_⟩
    simpa using h0 v (hFH hv) (Subsingleton.elim _ _)
  | succ d ih =>
    intro F H hF hFH hadd h0
    let π : (Fin (d + 1) → ℤ) × ℝ → (Fin d → ℤ) × ℝ := fun v => (fun i => v.1 i.succ, v.2)
    let cmb : ((Fin (d + 1) → ℤ) × ℝ) × ((Fin (d + 1) → ℤ) × ℝ) → (Fin (d + 1) → ℤ) × ℝ :=
      fun p => (-p.2.1 0) • p.1 + (p.1.1 0) • p.2
    let G : Set ((Fin (d + 1) → ℤ) × ℝ) :=
      {v ∈ F | v.1 0 = 0} ∪ cmb '' ({v ∈ F | 0 < v.1 0} ×ˢ {v ∈ F | v.1 0 < 0})
    have hG : G.Finite :=
      (hF.subset (Set.sep_subset _ _)).union
        (((hF.subset (Set.sep_subset _ _)).prod (hF.subset (Set.sep_subset _ _))).image _)
    have hGH : G ⊆ {v ∈ H | v.1 0 = 0} := by
      rintro v (⟨hv, hv0⟩ | ⟨⟨s, t⟩, ⟨⟨hs, hs0⟩, ht, ht0⟩, rfl⟩)
      · exact ⟨hFH hv, hv0⟩
      · refine ⟨hadd _ (zsmul_mem_pos H hadd _ (hFH hs) _ (neg_pos.2 ht0)) _
          (zsmul_mem_pos H hadd _ (hFH ht) _ hs0), ?_⟩
        simp only [cmb, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
    obtain ⟨φ, hφD, hφ⟩ := ih (π '' G) (π '' {v ∈ H | v.1 0 = 0}) (hG.image _)
      (Set.image_mono hGH)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ _ ⟨v, ⟨hv, hv0⟩, rfl⟩
        exact ⟨u + v, ⟨hadd u hu v hv, by simp [hu0, hv0]⟩, rfl⟩)
      (by
        rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩ h
        refine h0 u hu (funext fun i => ?_)
        refine Fin.cases hu0 (fun j => ?_) i
        exact congrFun h j)
    let r : (Fin (d + 1) → ℤ) × ℝ → ℝ := fun v => ∑ i : Fin d, (v.1 i.succ : ℝ) * φ i + v.2
    have hr : ∀ v ∈ G, r v < 0 := fun v hv => hφ (π v) ⟨v, hv, rfl⟩
    have hrc : ∀ s t, r (cmb (s, t)) = (-(t.1 0 : ℝ)) * r s + (s.1 0 : ℝ) * r t := by
      intro s t
      simp only [r, cmb, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
      simp only [zsmul_eq_mul]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc]
      ring
    obtain ⟨x, hxD, hlo, hhi⟩ := between_fin D hD
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | v.1 0 < 0})
      ((fun v => -r v / (v.1 0 : ℝ)) '' {v ∈ F | 0 < v.1 0})
      ((hF.subset (Set.sep_subset _ _)).image _) ((hF.subset (Set.sep_subset _ _)).image _)
      (by
        rintro _ ⟨t, ht, rfl⟩ _ ⟨s, hs, rfl⟩
        have h1 := hr _ (Or.inr ⟨(s, t), ⟨hs, ht⟩, rfl⟩)
        rw [hrc] at h1
        have hs0 : (0 : ℝ) < s.1 0 := by exact_mod_cast hs.2
        have ht0 : (t.1 0 : ℝ) < 0 := by exact_mod_cast ht.2
        show -r t / (t.1 0 : ℝ) < -r s / (s.1 0 : ℝ)
        rw [← neg_div_neg_eq, div_lt_div_iff₀ (neg_pos.2 ht0) hs0]
        linarith)
    refine ⟨Fin.cons x φ, fun i => Fin.cases hxD hφD i, fun v hv => ?_⟩
    have hsum : ∑ i, (v.1 i : ℝ) * (Fin.cons x φ : Fin (d + 1) → ℝ) i + v.2 = (v.1 0 : ℝ) * x + r v := by
      simp only [r, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_assoc]
    rw [hsum]
    rcases lt_trichotomy (v.1 0) 0 with h | h | h
    · have h1 := hlo _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (v.1 0 : ℝ) < 0 := by exact_mod_cast h
      rw [div_lt_iff_of_neg h2] at h1
      linarith
    · have h1 := hr v (Or.inl ⟨hv, h⟩)
      rw [h]; simpa using h1
    · have h1 := hhi _ ⟨v, ⟨hv, h⟩, rfl⟩
      have h2 : (0 : ℝ) < v.1 0 := by exact_mod_cast h
      rw [lt_div_iff₀ h2] at h1
      linarith

private theorem log_norm_dense (K : Type) [NormedField K] [IsAlgClosed K] (p : K) (hp : p ≠ 0)
    (hp1 : ‖p‖ ≠ 1) (a b : ℝ) (hab : a < b) :
    ∃ x ∈ Set.range (fun u : Kˣ => Real.log ‖(u : K)‖), a < x ∧ x < b := by
  have hL : Real.log ‖p‖ ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 hp) hp1
  obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ, a < q * Real.log ‖p‖ ∧ q * Real.log ‖p‖ < b := by
    rcases lt_or_gt_of_ne hL with h | h
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn ((div_lt_div_right_of_neg h).2 hab)
      rw [div_lt_iff_of_neg h] at h1
      rw [lt_div_iff_of_neg h] at h2
      exact ⟨q, h2, h1⟩
    · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (div_lt_div_of_pos_right hab h)
      rw [div_lt_iff₀ h] at h1
      rw [lt_div_iff₀ h] at h2
      exact ⟨q, h1, h2⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq p q.den_pos
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_nz] at hr
    exact hp hr.symm
  refine ⟨_, ⟨Units.mk0 r hr0 ^ q.num, ?_⟩, hq1, hq2⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, Real.log_zpow]
  rw [← hr, norm_pow, Real.log_pow, Rat.cast_def]
  field_simp

theorem UpperTheory.V.Alg.carver :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X) (K : Type) [NormedField K] [IsAlgClosed K] (z : σ → K), (∃ p : K, p ≠ 0 ∧ ‖p‖ ≠ 1) →
      (∀ n : σ →₀ ℕ, n ≠ 0 → Finsupp.weight wt n = 0 → ‖n.prod fun s k => z s ^ k‖ < 1) →
      ∃ t : Multiplicative X →* Kˣ, ∀ s, ‖(t (Multiplicative.ofAdd (wt s)) : K) * z s‖ < 1 := by
  intro σ _ X _ _ _ wt K _ _ z ⟨p, hp, hp1⟩ hz
  let e := (Module.finBasis ℤ X).equivFun
  let g : (σ →₀ ℕ) → K := fun n => n.prod fun s k => z s ^ k
  have hg : ∀ m n, g (m + n) = g m * g n := fun m n =>
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  have hg1 : ∀ s, g (Finsupp.single s 1) = z s := fun s => by
    simp [g, Finsupp.prod_single_index]
  obtain ⟨φ, hφD, hφ⟩ := fourier_motzkin _ (log_norm_dense K p hp hp1) (Module.finrank ℤ X)
    ((fun s => (e (wt s), Real.log ‖z s‖)) '' {s | z s ≠ 0})
    ((fun n => (e (Finsupp.weight wt n), Real.log ‖g n‖)) '' {n | n ≠ 0 ∧ g n ≠ 0})
    ((Set.toFinite _).image _)
    (by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨Finsupp.single s 1, ⟨by simp, by rw [hg1]; exact hs⟩, ?_⟩
      simp [hg1, Finsupp.weight_single])
    (by
      rintro _ ⟨m, ⟨hm, hm'⟩, rfl⟩ _ ⟨n, ⟨hn, hn'⟩, rfl⟩
      refine ⟨m + n, ⟨fun h => hm (add_eq_zero.1 h).1, by rw [hg]; exact mul_ne_zero hm' hn'⟩, ?_⟩
      simp only [hg, map_add (f := _), norm_mul, Prod.mk_add_mk,
        Real.log_mul (norm_ne_zero_iff.2 hm') (norm_ne_zero_iff.2 hn')])
    (by
      rintro _ ⟨n, ⟨hn, hn'⟩, rfl⟩ h
      exact Real.log_neg (norm_pos_iff.2 hn') (hz n hn (e.map_eq_zero_iff.1 h)))
  choose u hu using hφD
  let t : Multiplicative X →* Kˣ :=
    { toFun := fun x => ∏ i, u i ^ (e x.toAdd i)
      map_one' := by simp
      map_mul' := fun x y => by simp [zpow_add, Finset.prod_mul_distrib] }
  refine ⟨t, fun s => ?_⟩
  by_cases hs : z s = 0
  · simp [hs]
  have h1 := hφ _ ⟨s, hs, rfl⟩
  have h2 : Real.log ‖(t (Multiplicative.ofAdd (wt s)) : K)‖ = ∑ i, (e (wt s) i : ℝ) * φ i := by
    show Real.log ‖((∏ i, u i ^ (e (wt s) i) : Kˣ) : K)‖ = _
    rw [Units.coe_prod, norm_prod, Real.log_prod (fun i _ => norm_ne_zero_iff.2 (Units.ne_zero _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, Real.log_zpow, ← hu i]
  rw [← Real.log_neg_iff (norm_pos_iff.2 (mul_ne_zero (Units.ne_zero _) hs)), norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (norm_ne_zero_iff.2 hs), h2]
  exact h1
end
