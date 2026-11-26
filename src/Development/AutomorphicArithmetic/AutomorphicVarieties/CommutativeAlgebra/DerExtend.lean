module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem der_algebraMap {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (c : O) : D (algebraMap O A c) = 0 := by
  have h1 : D 1 = 0 := by
    have h : D (1 * 1) = x 1 • D 1 + x 1 • D 1 := hD 1 1
    rw [mul_one, map_one x, one_smul] at h
    simpa using h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_sq {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (f : A) (hf : f ∈ RingHom.ker x ^ 2) :
    D f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero])
  have h : D (a * b) = x a • D b + x b • D a := hD a b
  rw [h, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_smul, zero_smul, add_zero]

theorem UpperTheory.V.Alg.der_extend :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (Q : Type) [AddCommGroup Q] [Module O Q],
      (∀ D ∈ PtDer (W.originA h) Q, ∃! D' : R →ₗ[O] Q, D' ∈ PtDer (W.origin h) Q ∧ D' ∘ₗ W.A.val.toLinearMap = D) ∧
      ∀ D ∈ PtDer (W.origin h) Q, (∀ s, D (W.z s) = 0) → D = 0 := by
  intro O R _ _ _ X _ _ _ _ W h Q _ _
  obtain ⟨hk, hy⟩ := UpperTheory.V.Alg.ker_pow O R X W h 2
  choose y hy using hy
  refine ⟨fun D hD => ?_, fun D hD hz => ?_⟩
  · have key : ∀ (x : R) (a : W.A), x - a ∈ RingHom.ker (W.origin h) ^ 2 → D (y x) = D a := fun x a ha => by
      rw [← sub_eq_zero, ← map_sub]
      refine der_sq _ D hD _ ?_
      rw [← hk, Ideal.mem_comap]
      have := sub_mem ha (hy x)
      convert this using 1
      simp
    have horig : ∀ x : R, W.origin h x = W.originA h (y x) := fun x => by
      have h1 : x - y x ∈ RingHom.ker (W.origin h) := Ideal.pow_le_self two_ne_zero (hy x)
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
      exact h1
    let D' : R →ₗ[O] Q :=
      { toFun := fun x => D (y x)
        map_add' := fun a b => by
          rw [← map_add (f := _)]
          refine key _ _ ?_
          have := add_mem (hy a) (hy b)
          convert this using 1
          push_cast
          ring
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul]
          refine key _ _ ?_
          have := Submodule.smul_of_tower_mem _ c (hy a)
          convert this using 1
          rw [smul_sub]
          rfl }
    refine ⟨D', ⟨fun a b => ?_, ?_⟩, ?_⟩
    · have h1 : D (y a * y b) = W.originA h (y a) • D (y b) + W.originA h (y b) • D (y a) := hD _ _
      show D (y (a * b)) = W.origin h a • D (y b) + W.origin h b • D (y a)
      rw [horig a, horig b, ← h1]
      refine key _ _ ?_
      have := add_mem (Ideal.mul_mem_right b _ (hy a)) (Ideal.mul_mem_left _ (y a : R) (hy b))
      convert this using 1
      push_cast
      ring
    · ext a
      exact key _ a (by simp)
    · rintro E ⟨hE, rfl⟩
      ext x
      have := der_sq _ E hE _ (hy x)
      rw [map_sub, sub_eq_zero] at this
      exact this
  · ext x
    obtain ⟨f, rfl⟩ := W.surj x
    have hspan : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)),
        D (W.π g) = 0 := fun g hg => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : D (W.π (c i) * W.z i) = W.origin h (W.π (c i)) • D (W.z i) + W.origin h (W.z i) • D (W.π (c i)) :=
        hD _ _
      have h2 : W.origin h (W.z i) = 0 := by
        rw [WPres.z, W.origin_π]
        simp
      rw [map_mul]
      rw [hz i, h2, smul_zero, zero_smul, add_zero] at h1
      exact h1
    have h1 := hspan (f - algebraMap O _ (constantCoeff f))
      (mem_span_X _ (by simp [MvPowerSeries.algebraMap_apply]))
    rw [map_sub, AlgHom.commutes, map_sub, der_algebraMap _ D hD, sub_zero] at h1
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LiftGrading
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.lift_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Γ ι : Type) [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (w : ι → X) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R) (c : Γ → ι → ι → O),
      (∀ g a b, residue O (c g a b) = rbar g a b) → (∀ g a b, w a ≠ w b → c g a b = 0) → r.Generates → r.TStable w →
      ∃ W : WPres O X R, (∀ g a b, r.hom g a b ∈ W.part (w a - w b)) ∧
        ∀ i, ∃ g a b, W.z i = r.hom g a b - algebraMap O R (c g a b) ∧ W.wt i = w a - w b := by
  intro O _ _ _ _ X _ _ _ Γ ι _ _ _ _ rbar w R _ _ _ r c hc hc0 hgen hst
  obtain ⟨W, u, hu, he⟩ := UpperTheory.V.Alg.coord_grading O X R (Γ × ι × ι)
    (fun s => r.hom s.1 s.2.1 s.2.2 - algebraMap O R (c s.1 s.2.1 s.2.2)) (fun s => w s.2.1 - w s.2.2)
    (fun s => by
      rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, ← hc, sub_eq_zero]
      rfl)
    (fun R' _ _ _ f f' h => hgen R' f f' (by
      ext g a b
      have := h (g, a, b)
      simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
      exact this))
    (fun R' _ _ _ f t ht => by
      obtain ⟨f', hf'⟩ := hst R' f t ht
      refine ⟨f', fun ⟨g, a, b⟩ => ?_⟩
      have h1 : f' (r.hom g a b) = t (Multiplicative.ofAdd (w a - w b)) * f (r.hom g a b) := hf' g a b
      show f' (r.hom g a b - algebraMap O R (c g a b)) =
        t (Multiplicative.ofAdd (w a - w b)) * f (r.hom g a b - algebraMap O R (c g a b))
      rw [map_sub f', map_sub f, AlgHom.commutes, AlgHom.commutes, h1, mul_sub]
      by_cases hab : w a = w b
      · simp [hab]
      · simp [hc0 g a b hab])
  refine ⟨W, fun g a b => ?_, fun i => ⟨(u i).1, (u i).2.1, (u i).2.2, (hu i).1, (hu i).2⟩⟩
  have h1 : r.hom g a b - algebraMap O R (c g a b) ∈ W.part (w a - w b) := he (g, a, b)
  have h2 : algebraMap O R (c g a b) ∈ W.part (w a - w b) := by
    by_cases hab : w a = w b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    · rw [hc0 g a b hab, map_zero]
      exact zero_mem _
  simpa using add_mem h1 h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private lemma lin_coeff_sq {O R K τ : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing K] [Algebra O K]
    (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries τ K)
    (hc : ∀ f, constantCoeff (φ f) = algebraMap O K (x f)) (i : τ) :
    ∀ g ∈ RingHom.ker x ^ 2, coeff (Finsupp.single i 1) (φ g) = 0 := by
  intro g hg
  rw [pow_two] at hg
  have hone : ∀ a ∈ RingHom.ker x, 1 ≤ (φ a).order := by
    intro a ha
    have hxa : x a = 0 := ha
    exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (by rw [hc, hxa, map_zero])
  have hord : ((2 : ℕ) : ℕ∞) ≤ (φ g).order := by
    refine Submodule.mul_induction_on (C := fun g => ((2 : ℕ) : ℕ∞) ≤ (φ g).order) hg ?_ ?_
    · intro a ha b hb
      rw [map_mul]
      calc ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
        _ ≤ (φ a).order + (φ b).order := add_le_add (hone a ha) (hone b hb)
        _ ≤ (φ a * φ b).order := MvPowerSeries.le_order_mul
    · intro a b ha hb
      rw [map_add (f := _)]
      exact le_trans (le_min ha hb) MvPowerSeries.min_order_le_add
  apply MvPowerSeries.coeff_of_lt_order
  rw [Finsupp.degree_single]
  exact lt_of_lt_of_le (by norm_num) hord

theorem UpperTheory.V.Alg.chart_gr :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) [Module.Free ℤ X] [Module.Finite ℤ X] (τ : Type) (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ → IsChart W.gr (W.originA h) wt (φ.comp W.A.val) := by
  intro O X R _ _ _ _ _ _ W h _ _ τ wt φ hφ
  obtain ⟨hk, hsurj⟩ := ker_pow O R X W h 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf
    exact hφ.graded j f.val hf
  · intro f
    exact hφ.const f.val
  · intro i
    obtain ⟨g, hg1, hg2⟩ := hφ.onto i
    obtain ⟨y, hy⟩ := hsurj g
    have hd : ∀ i', coeff (Finsupp.single i' 1) (φ (g - y)) = 0 :=
      fun i' => lin_coeff_sq (W.origin h) φ hφ.const i' _ hy
    have he : ∀ i', coeff (Finsupp.single i' 1) ((φ.comp W.A.val) y) =
        coeff (Finsupp.single i' 1) (φ g) := by
      intro i'
      have := hd i'
      rw [map_sub, map_sub, sub_eq_zero] at this
      exact this.symm
    refine ⟨y, ?_, ?_⟩
    · rw [he]
      exact hg1
    · intro i' hi'
      rw [he]
      exact hg2 i' hi'
  · intro f hf hco
    obtain ⟨c, hc0, hcf⟩ := hφ.inj f.val hf hco
    refine ⟨c, hc0, ?_⟩
    rw [← hk, Ideal.mem_comap]
    exact hcf
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrNoeth
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_noeth :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsNoetherianRing W.A ∧ Algebra.FiniteType (W.gr 0) W.A ∧ ∀ j, ∃ s : Finset W.A, (∀ a ∈ s, a ∈ W.gr j) ∧ W.gr j = W.gr 0 * Submodule.span O (s : Set W.A) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz
  classical
  haveI := W.fin
  haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O
  have hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · have e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x := rfl
        rw [← e]
        exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r =>
      have hr : algebraMap O W.A r ∈ W.gr 0 := SetLike.algebraMap_mem_graded W.gr r
      have e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r := rfl
      rw [← e]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  haveI hft : Algebra.FiniteType (W.gr 0) W.A :=
    ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  refine ⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩
  intro j
  have hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m) := by
    intro m n hn
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hn rfl
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
  let mA : (W.σ →₀ ℕ) → W.A := fun m =>
    ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩
  have hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hw : Finsupp.weight W.wt m = j := hμS hm
    show (W.π (monomial m 1) : R) ∈ W.part j
    rw [← hw]
    exact Submodule.mem_map_of_mem (hmono m)
  refine ⟨μ.image mA, hsj, ?_⟩
  apply le_antisymm
  · intro a ha
    have ha' : (a : R) ∈ W.part j := ha
    obtain ⟨f, hf, hfa⟩ := Submodule.mem_map.mp ha'
    obtain ⟨b, hb, hfb⟩ := hμ f (fun n hn => hf n hn)
    let bA : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩
    have hsum : a = ∑ m ∈ μ, bA m * mA m := by
      apply Subtype.ext
      rw [← hfa]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hfb, map_sum, map_mul, bA, mA]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_
    · show (W.π (b m) : R) ∈ W.part 0
      exact Submodule.mem_map_of_mem (hb m)
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))
  · rw [Submodule.mul_le]
    intro x hx y hy
    have hy' : y ∈ W.gr j := (Submodule.span_le.mpr fun z hz => hsj z hz) hy
    simpa using SetLike.GradedMul.mul_mem hx hy'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.IsWRing
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.isWRing :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin), (∀ s, -2 ≤ W.wt s ∧ W.wt s ≤ 2) → IsWRing W.gr (W.originA h) := by
  classical
  intro O _ _ _ _ R _ _ _ W h hw
  haveI := W.fin
  have hz : ∀ s, W.z s ∈ maximalIdeal R := by
    intro s
    by_contra hs
    have hu : IsUnit (W.z s) := by
      by_contra hn
      exact hs ((IsLocalRing.mem_maximalIdeal _).2 hn)
    have h0 : W.origin h (W.z s) = 0 := by
      simp only [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have hu' := hu.map (W.origin h)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  refine ⟨wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz, ?_, ?_⟩
  · refine ⟨(Finset.univ.filter (fun i => W.wt i ≠ 0)).image W.zA, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have hi' : W.wt i ≠ 0 := (Finset.mem_filter.1 hi).2
      have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
      obtain ⟨h1, h2⟩ := hw i
      rcases (show W.wt i = -2 ∨ W.wt i = -1 ∨ W.wt i = 1 ∨ W.wt i = 2 by omega) with e | e | e | e
      · exact Or.inl (e ▸ hm)
      · exact Or.inr (Or.inl (e ▸ hm))
      · exact Or.inr (Or.inr (Or.inl (e ▸ hm)))
      · exact Or.inr (Or.inr (Or.inr (e ▸ hm)))
    · refine top_unique ?_
      rw [← gr_gen O R ℤ W]
      apply Algebra.adjoin_mono
      rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inl hx
      · by_cases hi : W.wt i = 0
        · left
          have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
          rw [hi] at hm
          exact hm
        · right
          simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, rfl⟩
  · intro j hj f hf
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 hf
    have hc : MvPowerSeries.constantCoeff g = 0 := by
      have := hg 0 (by simpa using hj.symm)
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using this
    have hfg : (f : R) = W.π g := hgf.symm
    change W.origin h f.1 = 0
    rw [hfg, WPres.origin_π, hc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartAdd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartFree
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_intertwiner_decomp_of_kernel_intertwines {σ O : Type} [Fintype σ] [CommRing O] (g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    ∃ h : σ → MvPowerSeries σ O, g = ∑ i, monomial (Finsupp.single i 1) 1 * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) g := by
  classical
  let sel : (σ →₀ ℕ) → Option σ := fun n =>
    if hn : n.support.Nonempty then some hn.choose else none
  let H : σ → MvPowerSeries σ O := fun i k =>
    if sel (k + Finsupp.single i 1) = some i then coeff (k + Finsupp.single i 1) g else 0
  have hc : ∀ i m, coeff m (H i) =
      if sel (m + Finsupp.single i 1) = some i then coeff (m + Finsupp.single i 1) g else 0 :=
    fun _ _ => rfl
  refine ⟨H, ?_, ?_⟩
  · ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hn : n.support.Nonempty
    · have hi0 : hn.choose ∈ n.support := hn.choose_spec
      have hsel : sel n = some hn.choose := dif_pos hn
      have hle0 : Finsupp.single hn.choose 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi0)
      rw [Finset.sum_eq_single hn.choose]
      · rw [if_pos hle0, hc, tsub_add_cancel_of_le hle0, if_pos hsel]
      · intro i _ hi
        by_cases hle : Finsupp.single i 1 ≤ n
        · rw [if_pos hle, hc, tsub_add_cancel_of_le hle, if_neg]
          rw [hsel]
          intro heq
          exact hi (Option.some_injective _ heq).symm
        · rw [if_neg hle]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    · have hn0 : n = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hn
        exact hn
      subst hn0
      rw [Finset.sum_eq_zero]
      · rw [coeff_zero_eq_constantCoeff_apply]
        exact hg
      · intro i _
        rw [if_neg]
        intro hle
        have h1 := Finsupp.single_le_iff.1 hle
        simp at h1
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hc, zero_add, if_pos]
    have hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty := ⟨i, by simp⟩
    show (if hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty then some hn.choose else none) = some i
    rw [dif_pos hn]
    have hs : hn.choose ∈ ({i} : Finset σ) := by
      rw [← Finsupp.support_single_ne_zero i (one_ne_zero : (1 : ℕ) ≠ 0)]
      exact hn.choose_spec
    rw [Finset.mem_singleton.1 hs]

private lemma π_mem_sq {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (h : W.HasOrigin) (f : MvPowerSeries W.σ O) (h0 : constantCoeff f = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) f = 0) : W.π f ∈ RingHom.ker (W.origin h) ^ 2 := by
  classical
  obtain ⟨g, hf, hg⟩ := exists_intertwiner_decomp_of_kernel_intertwines f h0
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i => (hg i).trans (h1 i)
  choose k hk _ using fun i => exists_intertwiner_decomp_of_kernel_intertwines (g i) (hg0 i)
  have hz : ∀ i, W.π (monomial (Finsupp.single i 1) 1) ∈ RingHom.ker (W.origin h) := by
    intro i
    rw [RingHom.mem_ker]
    erw [WPres.origin_π]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hk i, Finset.mul_sum, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hz i) (hz j))

theorem UpperTheory.V.Alg.chart_free :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin), Function.Injective W.π → ∃ φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O), IsChart W.part (W.origin h) W.wt φ ∧ ∀ s, φ (W.z s) = MvPowerSeries.X s := by
  intro O X R _ _ _ _ _ _ W h hinj
  classical
  let e : MvPowerSeries W.σ O ≃ₐ[O] R := AlgEquiv.ofBijective W.π ⟨hinj, W.surj⟩
  let μ : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ (FractionRing O) :=
    { MvPowerSeries.map (algebraMap O (FractionRing O)) with
      commutes' := fun r => by
        ext n
        simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C] }
  let φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O) := μ.comp e.symm.toAlgHom
  have hφ : ∀ g, φ (W.π g) = MvPowerSeries.map (algebraMap O (FractionRing O)) g := by
    intro g
    show μ (e.symm (e g)) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨φ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j f hf
    have hf' : f ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hf
    obtain ⟨g, hg, rfl⟩ := hf'
    have hg' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n g = 0 := hg
    show ∀ n, Finsupp.weight W.wt n ≠ j → coeff n (φ (W.π g)) = 0
    intro n hn
    rw [hφ, MvPowerSeries.coeff_map, hg' n hn, map_zero]
  · intro f
    obtain ⟨g, rfl⟩ := W.surj f
    rw [hφ, WPres.origin_π, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
  · intro i
    refine ⟨W.π (MvPowerSeries.X i), ?_, ?_⟩
    · rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_pos rfl]
      exact one_ne_zero
    · intro i' hi'
      rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_neg]
      intro heq
      exact hi' (Finsupp.single_left_injective one_ne_zero heq)
  · intro f hf0 hlin
    obtain ⟨g, rfl⟩ := W.surj f
    unfold satSq
    show ∃ c : O, c ≠ 0 ∧ c • W.π g ∈ RingHom.ker (W.origin h) ^ 2
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    apply π_mem_sq W h g
    · rw [← WPres.origin_π W h]
      exact hf0
    · intro i
      have hi := hlin i
      rw [hφ, MvPowerSeries.coeff_map] at hi
      exact IsFractionRing.injective O (FractionRing O) (hi.trans (map_zero _).symm)
  · intro s
    show φ (W.π (MvPowerSeries.X s)) = MvPowerSeries.X s
    rw [hφ, MvPowerSeries.map_X]
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chart_add_coeff {K τ τ' : Type} [CommRing K] (ε : τ ≃ τ') (p : MvPowerSeries τ K) (n : τ' →₀ ℕ) :
    coeff n (rename ε p) = coeff (Finsupp.mapDomain ε.symm n) p := by
  have h := coeff_embDomain_rename ε.toEmbedding p (Finsupp.mapDomain ε.symm n)
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp] at h
  have h2 : (ε.toEmbedding : τ → τ') ∘ ε.symm = id := funext fun x => ε.apply_symm_apply x
  rw [h2, Finsupp.mapDomain_id] at h
  exact h

private theorem chart_add_weight {τ τ' X : Type} [AddCommGroup X] (g : τ' → τ) (wt : τ → X) (n : τ' →₀ ℕ) :
    Finsupp.weight wt (Finsupp.mapDomain g n) = Finsupp.weight (fun s => wt (g s)) n := by
  induction n using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a b => simp [Finsupp.weight_single]

private theorem chart_add_rename {O A X τ τ' : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    [AddCommGroup X] {𝒜 : X → Submodule O A} {x : A →ₐ[O] O} {wt : τ → X}
    {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)} (h : IsChart 𝒜 x wt φ) (ε : τ ≃ τ') (wt' : τ' → X)
    (hw : ∀ s, wt' s = wt (ε.symm s)) :
    IsChart 𝒜 x wt' (((rename ε).restrictScalars O).comp φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j f hf n hn
    show coeff n (rename ε (φ f)) = 0
    rw [chart_add_coeff]
    refine h.graded j f hf _ ?_
    rwa [chart_add_weight, ← funext hw]
  · intro f
    show constantCoeff (rename ε (φ f)) = _
    rw [constantCoeff_rename, h.const]
  · intro i
    obtain ⟨f, h1, h2⟩ := h.onto (ε.symm i)
    refine ⟨f, ?_, fun i' hi' => ?_⟩
    · show coeff _ (rename ε (φ f)) ≠ 0
      rwa [chart_add_coeff, Finsupp.mapDomain_single]
    · show coeff _ (rename ε (φ f)) = 0
      rw [chart_add_coeff, Finsupp.mapDomain_single]
      exact h2 _ fun h3 => hi' (ε.symm.injective h3)
  · intro f hx hf
    refine h.inj f hx fun i => ?_
    have h1 : coeff _ (rename ε (φ f)) = 0 := hf (ε i)
    rwa [chart_add_coeff, Finsupp.mapDomain_single, ε.symm_apply_apply] at h1

private def chart_add_equiv (F : Bool → Type) : (Σ v, F v) ≃ F true ⊕ F false where
  toFun
    | ⟨true, s⟩ => .inl s
    | ⟨false, s⟩ => .inr s
  invFun
    | .inl s => ⟨true, s⟩
    | .inr s => ⟨false, s⟩
  left_inv
    | ⟨true, _⟩ => rfl
    | ⟨false, _⟩ => rfl
  right_inv
    | .inl _ => rfl
    | .inr _ => rfl

private def chart_add_fam (A B : Type) : Bool → Type := fun v => Bool.rec B A v

theorem UpperTheory.V.Alg.chart_add :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin) (τ : Type) [Fintype τ] (wt : τ → X) (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart W.part (W.origin h) wt φ →
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (W' : WPres O X R') (τ' : Type) [Fintype τ'] (e : W.σ ⊕ τ' ≃ W'.σ), (∀ s, W'.wt (e (.inl s)) = W.wt s) →
      RingHom.ker W'.π = (RingHom.ker W.π).map (MvPowerSeries.rename fun s => e (.inl s)) →
      ∃ (h' : W'.HasOrigin) (ψ : R' →ₐ[O] MvPowerSeries (τ ⊕ τ') (FractionRing O)), IsChart W'.part (W'.origin h') (Sum.elim wt fun s => W'.wt (e (.inr s))) ψ ∧
        (∀ s, ψ (W'.z (e (.inl s))) = MvPowerSeries.rename Sum.inl (φ (W.z s))) ∧ ∀ s, ψ (W'.z (e (.inr s))) = MvPowerSeries.X (.inr s) := by
  intro O X R _ _ _ _ iR aR W h τ fτ wt φ hφ R' _ _ W' τ' fτ' e hwt hker
  let W0 : WPres O X (MvPowerSeries τ' O) := WPres.free O fun s : τ' => W'.wt (e (.inr s))
  have h0 : W0.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  obtain ⟨φ0, hφ0, hz0⟩ := chart_free O X (MvPowerSeries τ' O) W0 h0 Function.injective_id
  let B : Bool → Type := chart_add_fam R (MvPowerSeries τ' O)
  letI iB : ∀ v : Bool, CommRing (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => CommRing (B v)) (inferInstance : CommRing (MvPowerSeries τ' O)) iR v
  letI aB : ∀ v : Bool, Algebra O (B v) := fun v =>
    Bool.rec (motive := fun v : Bool => @Algebra O (B v) _ (iB v).toCommSemiring.toSemiring) (inferInstance : Algebra O (MvPowerSeries τ' O)) aR v
  let WB : ∀ v : Bool, WPres O X (B v) := fun v => Bool.rec (motive := fun v : Bool => WPres O X (B v)) W0 W v
  have hB : ∀ v : Bool, (WB v).HasOrigin := fun v => Bool.rec (motive := fun v : Bool => (WB v).HasOrigin) h0 h v
  let F : Bool → Type := chart_add_fam τ τ'
  letI fF : ∀ v : Bool, Fintype (F v) := fun v => Bool.rec (motive := fun v : Bool => Fintype (F v)) fτ' fτ v
  let wF : ∀ v : Bool, F v → X := fun v => Bool.rec (motive := fun v : Bool => F v → X) W0.wt wt v
  let φF : ∀ v : Bool, B v →ₐ[O] MvPowerSeries (F v) (FractionRing O) := fun v =>
    Bool.rec (motive := fun v : Bool => B v →ₐ[O] MvPowerSeries (F v) (FractionRing O)) φ0 φ v
  have hF : ∀ v : Bool, IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v) := fun v =>
    Bool.rec (motive := fun v : Bool => IsChart (WB v).part ((WB v).origin (hB v)) (wF v) (φF v)) hφ0 hφ v
  let e' : (Σ v, (WB v).σ) ≃ W'.σ := (chart_add_equiv fun v => (WB v).σ).trans e
  obtain ⟨h', ψ, hψ, hz⟩ := chart_sum O X Bool B WB hB F wF φF hF R' W' e'
    (fun v => Bool.rec (motive := fun v : Bool => ∀ s, W'.wt (e' ⟨v, s⟩) = (WB v).wt s) (fun _ => rfl) hwt v) (by
      rw [iSup_bool_eq, hker]
      have h1 : RingHom.ker (WB false).π = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id
      rw [h1, Ideal.map_bot, sup_bot_eq]
      rfl)
  let ε : (Σ v, F v) ≃ τ ⊕ τ' := chart_add_equiv F
  refine ⟨h', ((rename ε).restrictScalars O).comp ψ, chart_add_rename hψ ε _ ?_, fun s => ?_, fun s => ?_⟩
  · rintro (s | s) <;> rfl
  · have h1 := congrArg (rename ε) (hz true s)
    rw [rename_rename] at h1
    exact h1
  · have h1 := congrArg (rename ε) (hz false s)
    rw [rename_rename] at h1
    refine h1.trans ?_
    have h2 : φF false ((WB false).z s) = MvPowerSeries.X s := hz0 s
    rw [h2]
    exact rename_X _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private def tc {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) : Matrix ι ι R →* Matrix ι ι R where
  toFun h := Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b
  map_one' := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  map_mul' h h' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : w a - w b = (w a - w c) + (w c - w b) := by abel
    rw [this, ofAdd_add, map_mul, Units.val_mul]
    ring

private theorem tc_apply {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (a b : ι) :
    tc w t h a b = (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b := rfl

private theorem tc_fix {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (hh : ∀ a b, w a ≠ w b → h a b = 0) : tc w t h = h := by
  ext a b
  rw [tc_apply]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hh a b hab]

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

section

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X]
  {w : ι → X} {Φ : FormData O w} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* Matrix ι ι (ResidueField O)} {r0 : Γ →* Matrix ι ι O}
  {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private def tl (w : ι → X) (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1) (r : Lift O rbar R) :
    Lift O rbar R where
  hom := (tc w t).comp r.hom
  cont a b N := by
    have := (r.cont a b N).comp
      (fun x => Ideal.Quotient.mk (maximalIdeal R ^ N) (t (Multiplicative.ofAdd (w a - w b)) : R) * x)
    exact this
  red g a b := by
    show res O R ((t (Multiplicative.ofAdd (w a - w b)) : R) * r.hom g a b) = _
    rw [map_mul, ht, one_mul, r.red]

private theorem inH_comap {r : Lift O rbar R} (h : Φ.InH r0 R r) {H : Type} [Group H] [TopologicalSpace H]
    (φ : H →* Γ) (hφ : Continuous φ) : Φ.InH (r0.comp φ) R (r.comap φ hφ) := fun s => by
  have := h (φ s)
  rw [← map_inv] at this
  exact this

variable {F : Frame Γ} {L : ∀ q, Cond O (rbar.comp (F.ψ q))}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B}

private theorem framed_map (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q)) {i : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') :
    IsFramed Φ r0 F L ρ (f.comp i) (r.map f) (fun v => (α v).map f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm := (hh_group O ι X w Φ R).2.2.2.1 R' f
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    have e : ((r0 s⁻¹).map (algebraMap O R)).map f = (r0 s⁻¹).map (algebraMap O R') := by
      ext a b
      simp
    rw [map_mul_alg, e] at this
    exact this
  · obtain ⟨I, hI⟩ := (hL q).closed R _ (inH_comap h1 (F.ψ q) (F.hψ q))
    have h0 := (hI R (AlgHom.id O R)).1 (h2 q)
    exact (hI R' f).2 fun x hx => by rw [show x = 0 from h0 x hx, map_zero]
  · simp [h4]
  · have := congrArg (fun A : Matrix ι ι R => A.map f) (h5 v s)
    simp only [map_mul_alg] at this
    exact this

private theorem framed_torus (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q))
    (h0 : ∀ g a b, w a ≠ w b → r0 g a b = 0) {i i' : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1)
    (hi : ∀ v s a b, i' ((ρ v).hom s a b) = t (Multiplicative.ofAdd (w a - w b)) * i ((ρ v).hom s a b)) :
    IsFramed Φ r0 F L ρ i' (tl w t ht r) (fun v => tc w t (α v)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm : ∀ h, Φ.HH h → Φ.HH (tc w t h) := (hh_group O ι X w Φ R).2.2.2.2.2 t
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    rw [map_mul, tc_fix w t ((r0 s⁻¹).map _) fun a b hab => by simp [h0 _ a b hab]] at this
    exact this
  · exact (hL q).torus R _ _ t (inH_comap h1 (F.ψ q) (F.hψ q)) ht (fun g a b => rfl) (h2 q)
  · simp [h4]
  · have := congrArg (tc w t) (h5 v s)
    simp only [map_mul] at this
    have e : ((ρ v).hom s).map i' = tc w t (((ρ v).hom s).map i) := by
      ext a b
      exact hi v s a b
    rw [e]
    exact this

end

private theorem algHom_ext_on_generators {O X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
    (W : WPres O X B) (hz : ∀ s, W.z s ∈ maximalIdeal B) {R' : Type} [CommRing R'] [Algebra O R']
    [IsCO O R'] (f g : B →ₐ[O] R') (h : ∀ s, f (W.z s) = g (W.z s)) : f = g := by
  have hC : ∀ (H : MvPowerSeries W.σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hm : ∀ s, f (W.z s) ∈ maximalIdeal R' := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz s
  have key : f.comp W.π = g.comp W.π :=
    (co_ev O O R' W.σ (Algebra.ofId O R') (fun s => f (W.z s)) hm).unique ⟨hC _, fun _ => rfl⟩
      ⟨hC _, fun s => (h s).symm⟩
  ext x
  obtain ⟨y, rfl⟩ := W.surj x
  exact DFunLike.congr_fun key y

private theorem const_mem {O X R ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : x - algebraMap O R c ∈ W.part (w a - w b)) : x ∈ W.part (w a - w b) := by
  have h2 : algebraMap O R c ∈ W.part (w a - w b) := by
    by_cases hab : w a = w b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    · rw [hc hab, map_zero]
      exact zero_mem _
  simpa using add_mem hx h2

private theorem const_eig {O X R R' ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ)
    (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : f' x = t (Multiplicative.ofAdd (w a - w b)) * f x) :
    f' (x - algebraMap O R c) = t (Multiplicative.ofAdd (w a - w b)) * f (x - algebraMap O R c) := by
  rw [map_sub f', map_sub f, AlgHom.commutes, AlgHom.commutes, hx, mul_sub]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hc hab]

theorem UpperTheory.V.Alg.framed_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ v s a b, (ρ v).hom s a b ∈ WB.part (w a - w b)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ W : WPres O X R, (∀ s, W.z s ∈ maximalIdeal R) ∧ (∀ s, i (WB.z s) ∈ W.part (WB.wt s)) ∧ (∀ s a b, r.hom s a b ∈ W.part (w a - w b)) ∧ ∀ v a b, α v a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ _ Γ _ _ _ rbar r0 _ hn0 F L _ hL _ B _ _ _ ρ _ WB hzB hρ R _ _ _ i r α ⟨hfr, hu⟩
  have h0 := hn0.2.2
  have h1 : ∀ a b, w a ≠ w b → (1 : Matrix ι ι O) a b = 0 := fun a b hab =>
    Matrix.one_apply_ne fun e => hab (by rw [e])
  let e : WB.σ ⊕ (Γ × ι × ι) ⊕ (F.T × ι × ι) → R := Sum.elim (fun s => i (WB.z s))
    (Sum.elim (fun s => r.hom s.1 s.2.1 s.2.2 - algebraMap O R (r0.hom s.1 s.2.1 s.2.2))
      fun s => α s.1 s.2.1 s.2.2 - algebraMap O R ((1 : Matrix ι ι O) s.2.1 s.2.2))
  have hem : ∀ s, e s ∈ maximalIdeal R := by
    rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
    · show i (WB.z s) ∈ _
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hzB s
    · show r.hom g a b - algebraMap O R (r0.hom g a b) ∈ _
      rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, ← r0.red g a b, sub_eq_zero]
      exact (res O O).commutes _
    · show α v a b - algebraMap O R ((1 : Matrix ι ι O) a b) ∈ _
      have k : res O R (α v a b) = (1 : Matrix ι ι (ResidueField O)) a b :=
        congrFun (congrFun (hfr.2.2.1 v).2.2 a) b
      rw [← res_eq_zero_iff O, map_sub, k, AlgHom.commutes, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  obtain ⟨W, u, hW, he⟩ := coord_grading O X R _ e
    (Sum.elim WB.wt (Sum.elim (fun s => w s.2.1 - w s.2.2) fun s => w s.2.1 - w s.2.2)) hem
    (fun R' _ _ _ f f' h => by
      refine (hu R' _ _ _ (framed_map hL hfr f)).unique ⟨rfl, rfl, fun _ => rfl⟩ ⟨?_, ?_, fun v => ?_⟩
      · exact algHom_ext_on_generators WB hzB _ _ fun s => (h (.inl s)).symm
      · ext g a b
        have : f (r.hom g a b - algebraMap O R _) = f' (r.hom g a b - algebraMap O R _) :=
          h (.inr (.inl (g, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm
      · ext a b
        have : f (α v a b - algebraMap O R _) = f' (α v a b - algebraMap O R _) :=
          h (.inr (.inr (v, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm)
    (fun R' _ _ _ f t ht => by
      obtain ⟨i', hi', -⟩ := tact O X B WB hzB R' (f.comp i) t
      obtain ⟨f', ⟨k1, k2, k3⟩, -⟩ := hu R' _ _ _
        (framed_torus hL h0 (framed_map hL hfr f) t ht fun v s a b => hi' _ _ (hρ v s a b))
      refine ⟨f', ?_⟩
      rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
      · exact (DFunLike.congr_fun k1 _).trans (hi' _ _ (WB.z_mem s))
      · exact const_eig f f' t w (h0 g a b) (congrArg (fun x => x.hom g a b) k2)
      · exact const_eig f f' t w (h1 a b) (congrFun (congrFun (k3 v) a) b))
  exact ⟨W, fun s => by rw [(hW s).1]; exact hem _, fun s => he (.inl s),
    fun g a b => const_mem W w (h0 g a b) (he (.inr (.inl (g, a, b)))),
    fun v a b => const_mem W w (h1 a b) (he (.inr (.inr (v, a, b))))⟩
end
