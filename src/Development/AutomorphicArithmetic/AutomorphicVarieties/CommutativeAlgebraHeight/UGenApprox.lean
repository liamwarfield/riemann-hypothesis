module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem u_gen_approx {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (m : Ideal R)
    (A : Subalgebra O R) (T : Set R) (h0 : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ m)
    (hT : ∀ t ∈ T, t ∈ A ∧ t ∈ m) (hm : m ≤ Ideal.span T ⊔ m ^ 2) (N : ℕ) (x : R) :
    ∃ a ∈ A, x - a ∈ m ^ N :=
  _root_.UpperTheory.Reformulated.B.LayerApproximation.co_ext_approx m A T h0 hT hm N x

private theorem u_gen_dual (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.IsTorsionBySet O M (maximalIdeal O)) (x : M) (hx : x ≠ 0) :
    ∃ D : M →ₗ[O] ResidueField O, D x ≠ 0 := by
  letI : Module (ResidueField O) M := h.module
  haveI : IsScalarTower O (ResidueField O) M := h.isScalarTower
  have := (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).not.2 hx
  push Not at this
  obtain ⟨φ, hφ⟩ := this
  exact ⟨φ.restrictScalars O, hφ⟩

private theorem u_gen_span (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R]
    [IsCO O R] (S : Set R) (hS : S ⊆ maximalIdeal R)
    (hO' : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ S)
    (H : ∀ f f' : R →ₐ[O] DualNumber (ResidueField O), (∀ s ∈ S, f s = f' s) → f = f') :
    maximalIdeal R ≤ Ideal.span S ⊔ maximalIdeal R ^ 2 := by
  intro x hx
  set I : Ideal R := Ideal.span S ⊔ maximalIdeal R ^ 2 with hI
  by_contra hxI
  have hIm : I ≤ maximalIdeal R :=
    sup_le (Ideal.span_le.2 hS) (Ideal.pow_le_self two_ne_zero)
  have hO : ∀ a ∈ maximalIdeal O, algebraMap O R a ∈ I := fun a ha =>
    Ideal.mem_sup_left (Ideal.subset_span (hO' a ha))
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
  obtain ⟨φ, hφ⟩ := u_gen_dual O _ htor _ hxN
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
  have hff : f = f' :=
    H f f' fun s hs => key _ (hD _ (hIN _ (Ideal.mem_sup_left (Ideal.subset_span hs))))
  exact hφ (congrArg (fun g : R →ₐ[O] DualNumber (ResidueField O) => (g x).snd) hff)

theorem UpperTheory.V.CA.u_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (T : Set R), (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R'), (∀ t ∈ T, f t = f' t) → f = f') → ∀ (N : ℕ) (x : R), ∃ y ∈ Algebra.adjoin O T, x - y ∈ maximalIdeal R ^ N := by
  intro O _ _ R _ _ _ T H N x
  refine u_gen_approx (maximalIdeal R) (Algebra.adjoin O T)
    {y | y ∈ Algebra.adjoin O T ∧ y ∈ maximalIdeal R} (IsCO.res_surj (O := O)) (fun _ h => h) ?_ N x
  refine u_gen_span O R _ (fun _ h => h.2)
    (fun a ha => ⟨Subalgebra.algebraMap_mem _ a, fun h => ha (IsLocalHom.map_nonunit a h)⟩) ?_
  intro f f' h
  haveI := (co_res O).2
  refine H _ f f' fun t ht => ?_
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) t
  have := h _ ⟨sub_mem (Algebra.subset_adjoin ht) (Subalgebra.algebraMap_mem _ a), ha⟩
  rwa [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cl_mvps_fin {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : Module.Finite A (S ⧸ I)) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  classical
  have toP : ∀ K : Ideal S, Module.Finite A (S ⧸ K) →
      ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K := by
    intro K hK
    obtain ⟨T, hT⟩ := hK.fg_top
    choose l hl using fun q : S ⧸ K => Ideal.Quotient.mk_surjective q
    refine ⟨T.image l, fun s => ?_⟩
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' ((T.image l : Finset S) : Set S) = (T : Set (S ⧸ K)) := by
      ext q
      simp [hl]
    have hs : Ideal.Quotient.mk K s ∈ Submodule.map (Ideal.Quotient.mkₐ A K).toLinearMap
        (Submodule.span A ((T.image l : Finset S) : Set S)) := by
      rw [Submodule.map_span, himg, hT]
      exact Submodule.mem_top
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← Ideal.Quotient.eq]
    simpa using hts.symm
  have ofP : ∀ K : Ideal S, (∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K) →
      Module.Finite A (S ⧸ K) := by
    rintro K ⟨F, hF⟩
    refine ⟨⟨F.image (Ideal.Quotient.mk K), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨t, ht, hst⟩ := hF s
    have h1 : Ideal.Quotient.mk K s = (Ideal.Quotient.mkₐ A K).toLinearMap t := by
      simpa [Ideal.Quotient.eq] using hst
    have h2 := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ A K).toLinearMap) ht
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' (F : Set S) = ((F.image (Ideal.Quotient.mk K) : Finset (S ⧸ K)) : Set (S ⧸ K)) := by
      ext q
      simp
    rw [Submodule.map_span, himg] at h2
    rw [h1]
    exact h2
  obtain ⟨F1, hF1⟩ := toP I h
  have hpow : ∀ n : ℕ, ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact ⟨∅, fun s => ⟨0, Submodule.zero_mem _, by simp⟩⟩
    | succ n ih =>
      obtain ⟨Fn, hFn⟩ := ih
      obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
      refine ⟨Fn ∪ (F1 ×ˢ G).image (fun p => p.1 * p.2), fun s => ?_⟩
      obtain ⟨t, ht, hst⟩ := hFn s
      rw [← hG, Submodule.mem_span_finset] at hst
      obtain ⟨c, -, hc⟩ := hst
      choose u hu hcu using fun g => hF1 (c g)
      refine ⟨t + ∑ g ∈ G, u g * g, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.span_mono ?_ ht) (Submodule.sum_mem _ fun g hg => ?_)
        · exact Finset.coe_subset.mpr Finset.subset_union_left
        · have h3 := Submodule.mem_map_of_mem (f := LinearMap.mulRight A g) (hu g)
          rw [Submodule.map_span] at h3
          refine Submodule.span_mono ?_ h3
          rintro _ ⟨f, hf, rfl⟩
          rw [Finset.coe_union, Finset.coe_image]
          right
          exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, by simp⟩
      · have hct : s - t = ∑ g ∈ G, c g * g := by
          rw [← hc]
          simp [smul_eq_mul]
        have he : s - (t + ∑ g ∈ G, u g * g) = ∑ g ∈ G, (c g - u g) * g := by
          calc s - (t + ∑ g ∈ G, u g * g) = (s - t) - ∑ g ∈ G, u g * g := by ring
            _ = ∑ g ∈ G, c g * g - ∑ g ∈ G, u g * g := by rw [hct]
            _ = ∑ g ∈ G, (c g - u g) * g := by
              rw [← Finset.sum_sub_distrib]
              simp [sub_mul]
        rw [he, pow_succ']
        refine Ideal.sum_mem _ fun g hg => Ideal.mul_mem_mul (hcu g) ?_
        rw [← hG]
        exact Submodule.subset_span hg
  obtain ⟨F, hF⟩ := hpow N
  exact ofP J ⟨F, fun s => (hF s).imp fun t ⟨ht, hst⟩ => ⟨ht, hN hst⟩⟩

private theorem cl_mvps_max {O σ : Type} [CommRing O] [IsLocalRing O] (g : MvPowerSeries σ O) :
    g ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff g ∈ maximalIdeal O := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

theorem UpperTheory.V.CA.cl_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → ∀ (σ : Type) [Finite σ] (a : σ → R), (∀ s, a s ∈ maximalIdeal R) → maximalIdeal R ≤ (Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R)).radical → ∃ φ : MvPowerSeries σ O →ₐ[O] R, (∀ s, φ (MvPowerSeries.X s) = a s) ∧ φ.toRingHom.Finite ∧ IsLocalHom φ := by
  intro O _ _ _ _ R _ _ _ hR σ _ a ha hrad
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR.isLocalHom
  let φ : MvPowerSeries σ O →ₐ[O] R := GlobalTheory.mvEvalAdic O (maximalIdeal R) a ha
  have hX : ∀ s, φ (MvPowerSeries.X s) = a s := GlobalTheory.mvEvalAdic_X _ a ha
  have hXm : ∀ s, φ (MvPowerSeries.X s) ∈ maximalIdeal R := fun s => (hX s).symm ▸ ha s
  refine ⟨φ, hX, ?_, ?_⟩
  · letI : Algebra (MvPowerSeries σ O) R := φ.toRingHom.toAlgebra
    show Module.Finite (MvPowerSeries σ O) R
    haveI hOO : IsCO O O := ⟨inferInstance, ⟨fun x hx => by simpa using hx⟩, fun x => ⟨x, by simp⟩⟩
    haveI hCO := co_mvps O O σ
    haveI := hCO.complete
    haveI : IsScalarTower O (MvPowerSeries σ O) R :=
      IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    have hJ : Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R) ≤
        (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        rw [← hX s]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max]
        simp
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, ← φ.commutes c]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max, MvPowerSeries.algebraMap_apply]
        simpa using hc
    have hJm : (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap]
      rw [cl_mvps_max] at hg
      have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hg) (isUnit_of_map_unit (algebraMap O R) _ hu)
      have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
      have h3 := Ideal.add_mem _ h2 h1
      have h4 : φ g ∈ maximalIdeal R := by simpa using h3
      exact h4
    haveI : IsHausdorff ((maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) R :=
      IsHausdorff.of_isLocalRing _ R (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (hrad.trans (Ideal.radical_mono hJ)) (IsNoetherian.noetherian (maximalIdeal R))
    haveI : Module.Finite O (R ⧸ maximalIdeal R) := hR.res_fin
    haveI : Module.Finite (MvPowerSeries σ O) (R ⧸ maximalIdeal R) :=
      Module.Finite.of_restrictScalars_finite O _ _
    haveI : Module.Finite (MvPowerSeries σ O)
        (R ⧸ (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) :=
      cl_mvps_fin (A := MvPowerSeries σ O) inferInstance hN
    exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal (MvPowerSeries σ O))
  · constructor
    intro g hg
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    by_contra hc
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hc (isUnit_of_map_unit (algebraMap O R) _ hu)
    have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
    have h3 : φ g ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h2 h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) hg
end
