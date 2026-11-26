module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.SymExp
namespace ReciprocityTheory.ChartRestriction.G.AI

theorem symm_piecewise_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I)
    (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by
  classical
  have e : ∀ c : Bool, {a // decide (a ∈ t) = c} ≃ {b // decide (b ∈ s) = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      cases c
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = false) = tᶜ := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = false) = sᶜ := by ext; simp
        rw [h1, h2, Finset.card_compl, Finset.card_compl, hst]
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = true) = t := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = true) = s := by ext; simp
        rw [h1, h2, hst])
  have hσ : ∀ i, (Equiv.ofFiberEquiv e i ∈ s ↔ i ∈ t) := fun i => by
    have := Equiv.ofFiberEquiv_map e i
    rw [← decide_eq_decide]
    exact this
  have hfun : (s.piecewise (fun _ => x) fun _ => y) ∘ (Equiv.ofFiberEquiv e) =
      t.piecewise (fun _ => x) fun _ => y := by
    funext i
    rw [Function.comp_apply]
    by_cases hi : i ∈ t
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ ((hσ i).2 hi)]
    · have hi' : Equiv.ofFiberEquiv e i ∉ s := fun h => hi ((hσ i).1 h)
      rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi']
  rw [← hfun, hI]

theorem symm_piecewise_eq_mix {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I)
    (x y : V) (s : Finset (Fin n)) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (mix s.card x y) := by
  classical
  set t : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < s.card with ht_def
  have ht : t.card = s.card := by
    have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
    have hmap : t.map Fin.valEmbedding = Finset.range s.card := by
      ext m
      simp only [ht_def, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hm
        exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]
  rw [symm_piecewise_eq I hI x y s t ht.symm]
  congr 1
  funext i
  simp [ht_def, mix, Finset.piecewise]

theorem symm_expand {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I)
    (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by
  classical
  have h1 : (fun _ : Fin n => y + c • x) = (fun _ => c • x) + (fun _ => y) := by
    funext i
    simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  have h2 : ∀ s : Finset (Fin n),
      I (s.piecewise (fun _ => c • x) fun _ => y) = c ^ s.card * I (mix s.card x y) := by
    intro s
    have h3 : (s.piecewise (fun _ => c • x) fun _ => y) =
        s.piecewise (fun i => c • (s.piecewise (fun _ => x) (fun _ => y)) i)
          (s.piecewise (fun _ => x) fun _ => y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [h3, MultilinearMap.map_piecewise_smul, symm_piecewise_eq_mix I hI, Finset.prod_const,
      RingHom.id_apply, smul_eq_mul]
  simp only [h2]
  have h4 := Finset.sum_powerset_apply_card (f := fun k => c ^ k * I (mix k x y))
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  simp only [nsmul_eq_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaA
open MeasureTheory Set
open scoped Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI

theorem cone_preimage (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩
    · convert hm using 1
      ext
      simp
    · apply L.injective
      rw [← hx]
      simp

theorem measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable

theorem toSphere_measurePreserving (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  refine ⟨measurable_sphereMap L, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]
  congr 1
  have hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume :=
    L.measurePreserving
  exact hmp.measure_preimage_equiv _

theorem sphereInv_thm : SphereInvStatement := by
  refine ⟨?_, fun L => ?_⟩
  · have h1 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero (by simp) ?_
      exact (Metric.measure_ball_pos _ _ one_pos).ne'
    have h2 : (volume : Measure E3).toSphere Set.univ ≠ ⊤ := measure_ne_top _ _
    constructor
    rw [sphereMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h1 h2]
  · have hL := toSphere_measurePreserving L
    refine ⟨hL.measurable, ?_⟩
    rw [sphereMeasure, Measure.map_smul _ hL.measurable.aemeasurable, hL.map_eq]

end ReciprocityTheory.ChartRestriction.G.AI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CardQuotEqNatAbsNorm
namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem card_quot_eq_natAbs_norm {S : Type*} [CommRing S] [IsDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (f : S) (hf : f ≠ 0) :
    Nat.card (S ⧸ Ideal.span {f}) = (Algebra.norm ℤ f).natAbs := by
  classical
  let N : Submodule ℤ S := (Ideal.span {f}).restrictScalars ℤ
  have hmem : ∀ x : S, f * x ∈ N := fun x => Ideal.mul_mem_right x _ (Ideal.subset_span rfl)
  let g : S →+ N :=
    { toFun := fun x => ⟨f * x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      have h1 : f * x = f * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ hf h1
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, by ext; simp [g, mul_comm]⟩
  let e : S ≃+ N := AddEquiv.ofBijective g hbij
  have h := Submodule.natAbs_det_equiv N e
  have hlin : N.subtype ∘ₗ (e : S →+ N).toIntLinearMap = Algebra.lmul ℤ S f := by
    ext x
    rfl
  rw [hlin, ← Algebra.norm_apply] at h
  rw [h]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {f})).toEquiv.symm

theorem norm_int_eq_norm_rat {K : Type*} [Field K] [NumberField K] (O : Subring K)
    [Module.Free ℤ O] [Module.Finite ℤ O] (h : Module.finrank ℤ O = Module.finrank ℚ K)
    (f : O) : ((Algebra.norm ℤ f : ℤ) : ℚ) = Algebra.norm ℚ (f : K) := by
  classical
  let b := Module.Free.chooseBasis ℤ O
  have hli : LinearIndependent ℚ (fun i => ((b i : O) : K)) := by
    have h1 : LinearIndependent ℤ (fun i => ((b i : O) : K)) :=
      b.linearIndependent.map' (O.subtype.toIntAlgHom.toLinearMap)
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℚ K := by
    rw [← h, Module.finrank_eq_card_chooseBasisIndex]
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ O) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact Module.finrank_pos
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb' : ∀ i, b' i = ((b i : O) : K) := fun i => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [Algebra.norm_eq_matrix_det b f, Algebra.norm_eq_matrix_det b' (f : K)]
  have hm := RingHom.map_det (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f)
  rw [show ((Algebra.leftMulMatrix b f).det : ℚ) = (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f).det from rfl, hm]
  congr 1
  ext i j
  have hx : (f : K) * b' j = ∑ k, ((b.repr (f * b j) k : ℤ) : ℚ) • b' k := by
    have e1 := congrArg (O.subtype.toIntAlgHom.toLinearMap) (b.sum_repr (f * b j))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e1
    simp only [map_zsmul] at e1
    simp only [hb', Int.cast_smul_eq_zsmul]
    exact e1.symm
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, eq_intCast]
  rw [hx, b'.repr_sum_self]

theorem abs_norm_eq_prod {K : Type*} [Field K] [NumberField K] (x : K) :
    |(Algebra.norm ℚ x : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast, Complex.norm_ratCast] at h2
  exact h2.trans (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)).symm

theorem index_thm : IndexStatement := by
  intro K _ _ O hfree hfin hrank f hf
  haveI := hfree
  haveI := hfin
  have hc := card_quot_eq_natAbs_norm f hf
  have hn := norm_int_eq_norm_rat O hrank f
  have hprod := abs_norm_eq_prod (f : K)
  have h1 : (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| := by
    rw [hc, ← hn]
    simp [Nat.cast_natAbs, Int.cast_abs, Rat.cast_intCast]
  refine ⟨h1, ?_⟩
  rw [h1, hprod, Real.log_prod (fun σ _ => ?_)]
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (fun h0 => hf (Subtype.ext h0)))

end ReciprocityTheory.ChartRestriction.G.AI
end
