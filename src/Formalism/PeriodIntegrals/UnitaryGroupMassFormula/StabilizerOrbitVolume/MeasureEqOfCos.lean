module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasureEqOfCos
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical
  have hC : ∀ y, IsOpen {z : X | z - y ∈ Λ} := fun y =>
    hΛ.preimage (continuous_id.sub continuous_const)
  have hfin : ∀ t : Finset X,
      m1 (⋃ s ∈ t, {z | z - s ∈ Λ}) = m2 (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert s0 t hs0 ih =>
      rw [Finset.set_biUnion_insert]
      by_cases hex : ∃ s ∈ t, s0 - s ∈ Λ
      · obtain ⟨s, hs, hss⟩ := hex
        have hsub : {z : X | z - s0 ∈ Λ} ⊆ ⋃ s ∈ t, {z | z - s ∈ Λ} := by
          intro z hz
          simp only [Set.mem_iUnion, Set.mem_setOf_eq]
          exact ⟨s, hs, by simpa [sub_add_sub_cancel] using Λ.add_mem hz hss⟩
        rw [Set.union_eq_right.2 hsub, ih]
      · push_neg at hex
        have hdisj : Disjoint {z : X | z - s0 ∈ Λ} (⋃ s ∈ t, {z | z - s ∈ Λ}) := by
          rw [Set.disjoint_left]
          intro z hz hz'
          simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hz'
          obtain ⟨s, hs, hzs⟩ := hz'
          apply hex s hs
          simpa [sub_sub_sub_cancel_left] using Λ.sub_mem hzs hz
        have hmeas : MeasurableSet (⋃ s ∈ t, {z : X | z - s ∈ Λ}) :=
          (isOpen_biUnion fun s _ => hC s).measurableSet
        rw [measure_union hdisj hmeas, measure_union hdisj hmeas, h, ih]
  obtain ⟨t, htS, hcov⟩ := hS.elim_nhds_subcover (fun x => {z : X | z - x ∈ Λ})
    (fun x _ => (hC x).mem_nhds (by simp [Λ.zero_mem]))
  have heq : thick S Λ = ⋃ s ∈ t, {z : X | z - s ∈ Λ} := by
    ext x
    simp only [thick, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 (hcov hs)
      exact ⟨u, hu, by simpa [sub_add_sub_cancel] using Λ.add_mem hxs hsu⟩
    · rintro ⟨u, hu, hxu⟩
      exact ⟨u, htS u hu, hxu⟩
  rw [heq]
  exact hfin t


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [Set.mem_iInter, thick, Set.mem_setOf_eq]
  constructor
  · intro hx
    by_contra hxS
    have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
    have hN : (fun d : X => x - d) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) :=
      hc.continuousAt.preimage_mem_nhds (hSc.isOpen_compl.mem_nhds (by simpa using hxS))
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have h1 := hn hxs
    simp only [Set.mem_preimage, sub_sub_cancel, Set.mem_compl_iff] at h1
    exact h1 hs
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro i j hij x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hij hxs⟩
  have hmeas : ∀ n, MeasurableSet (thick S (Λ n)) := fun n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (fun n => (hmeas n).nullMeasurableSet)
      ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp_rw [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ hν H hHo hHc hanti hb c0 κ hm0 hcos S hS
  have hC : ∀ (n : ℕ) (y : X), IsOpen {z : X | z - y ∈ H n} := fun n y =>
    (hHo n).preimage (continuous_id.sub continuous_const)
  have hC0 : MeasurableSet {z : X | z - c0 ∈ H 0} := (hC 0 c0).measurableSet
  have hback : ∀ n y z, y - c0 ∉ H 0 → z - y ∈ H n → z - c0 ∉ H 0 := by
    intro n y z hy hz hz0
    apply hy
    have hz' : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
    simpa [sub_sub_sub_cancel_left] using (H 0).sub_mem hz0 hz'
  have key := measure_eq_of_cos m (κ • ν.restrict {z : X | z - c0 ∈ H 0}) H hHo hanti hb ?_
    S hS hS.isClosed
  · rw [key, Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
  · intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hC0, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ⊆ {z : X | z - c0 ∈ H 0} := by
        intro z hz
        have hz0 : z - y ∈ H 0 := hanti (Nat.zero_le n) hz
        simpa [sub_add_sub_cancel] using (H 0).add_mem hz0 hy
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdisj : {z : X | z - y ∈ H n} ∩ {z : X | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact hback n y z hy
      rw [hdisj, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hback n y z hy hz) hm0

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS
noncomputable section

namespace PI.VolStabSW

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h v hv
    funext j
    refine h v ?_ j
    funext i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · intro h g hg i
    have hPg : P *ᵥ g = 0 := by
      funext r
      have := congrFun hg r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cols, Pi.zero_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    exact congrFun (h g hPg) i

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.toLin'_apply] at hv
    exact (linInd_cols_iff P).1 hP v hv
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' P) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  rw [linInd_cols_iff]
  intro v hv
  calc v = (W * P) *ᵥ v := by rw [h, Matrix.one_mulVec]
    _ = W *ᵥ (P *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hv, Matrix.mulVec_zero]

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun D => D * P
      map_add' := fun D E => Matrix.add_mul D E P
      map_smul' := fun c D => Matrix.smul_mul c D P }
  have hf : ∀ D, f D = D * P := fun D => rfl
  have hsurj : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro E
    exact ⟨E * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * M - a * a := by omega
  have e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W => ⟨W.1 - L, by rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun D => ⟨D.1 + L, by
        have hD := D.2
        rw [LinearMap.mem_ker, hf] at hD
        rw [Matrix.add_mul, hD, hL, zero_add]⟩
      left_inv := fun W => by ext1; simp
      right_inv := fun D => by ext1; simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker, Nat.mul_sub_left_distrib]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  unfold ffH
  simp [Prod.fst_sum, swapR]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  unfold ffH
  simp [Prod.snd_sum, swapR]

private theorem ffGram_apply (J : Matrix (Fin M) (Fin M) (k × k))
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    ffGram (swapR k) J X r s = ffH (swapR k) J (X r) (X s) := by
  first
  | rfl
  | simp [ffGram]
  | (unfold ffGram; simp)

private theorem fst_ffGram_eq_V1_mul_map_fst (J : Matrix (Fin M) (Fin M) (k × k)) (X : Fin a → Fin M → k × k)
    (r s : Fin a) :
    (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s = (ffGram (swapR k) J X r s).1 := by
  rw [ffGram_apply, ffH_fst]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, V1, U1, Finset.sum_mul]
  exact Finset.sum_comm

private theorem snd_ffGram_eq_fst_ffGram_swap (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (X : Fin a → Fin M → k × k) (r s : Fin a) :
    (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
  rw [ffGram_apply, ffGram_apply, ffH_fst, ffH_snd]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h := congrArg Prod.fst (hJ x y)
  rw [Prod.fst_swap] at h
  rw [h]
  ring

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  constructor
  · rintro rfl
    refine Matrix.ext fun r s => ?_
    rw [fst_ffGram_eq_V1_mul_map_fst]
    rfl
  · intro h
    have hf : ∀ r s, (ffGram (swapR k) J X r s).1 = (T r s).1 := fun r s => by
      rw [← fst_ffGram_eq_V1_mul_map_fst]
      exact congrFun (congrFun h r) s
    refine Matrix.ext fun r s => Prod.ext (hf r s) ?_
    rw [snd_ffGram_eq_fst_ffGram_swap J hJ X, hf s r]
    have h2 := congrArg Prod.snd (hT r s)
    rw [Prod.snd_swap] at h2
    exact h2

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  unfold FFSplit
  intro k _ _ M a ha J hJ hJd T hT hTd
  have h := FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd
  simp only [FiniteFieldSplitting.swapR] at h
  rw [h, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have h1 : 1 ≤ Nat.card k := Nat.card_pos
  have hi : (i : ℕ) ≤ M := by have := i.isLt; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right h1 hi), Nat.cast_pow, Nat.cast_pow]

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAInt
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabSW

private theorem addHom_eq_zero_of_integralBasis_mul {F : Type} [Field F] [NumberField F] (g : F →+ ℂ)
    {y : F} (hy : y ≠ 0) (h0 : ∀ i, g (integralBasis F i * y) = 0) (w : F) : g w = 0 := by
  have hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y := by
    rw [(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hw, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, map_rat_smul, h0 i, smul_zero]

private theorem exists_mul_integers_of_fg {F : Type} [Field F] [NumberField F]
    (Λ : Submodule (𝓞 F) F) (hfg : (Λ.restrictScalars ℤ).FG) :
    ∃ c : F, c ≠ 0 ∧ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s
  have hB0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let T : Submodule ℤ F :=
    { carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r}
      add_mem' := by
        rintro a a' ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [mul_add, hr, hr', map_add (f := _)]⟩
      zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩
      smul_mem' := by
        rintro n a ⟨r, hr⟩
        exact ⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }
  have hsT : Submodule.span ℤ (s : Set F) ≤ T := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨r, hr⟩ := hb a ha
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩
  have has : a ∈ Submodule.span ℤ (s : Set F) := by rw [hs]; exact ha
  obtain ⟨r, hr⟩ := hsT has
  refine ⟨r, ?_⟩
  have hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r := by
    rfl
  rw [hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]

private theorem fg_of_addHom_intValued {F : Type} [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F)
    (g : F →+ ℂ) (hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n) (hne : ∃ w, g w ≠ 0) :
    (Λ.restrictScalars ℤ).FG := by
  classical
  let φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun y i => g (integralBasis F i * y)
      map_add' := fun y y' => by funext i; simp only [mul_add, map_add (f := _), Pi.add_apply]
      map_smul' := fun n y => by
        funext i; simp only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }
  let ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun z i => (z i : ℂ)
      map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add]
      map_smul' := fun n z => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨w, hw⟩ := hne
    exact hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)
  have hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : ∀ i, integralBasis F i * y ∈ Λ := fun i => by
      have h := Λ.smul_mem (RingOfIntegers.basis F i) hy
      rwa [Algebra.smul_def, ← integralBasis_apply] at h
    choose n hn using fun i => hg _ (hmem i)
    exact ⟨n, funext fun i => (hn i).symm⟩
  have hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG := IsNoetherian.noetherian _
  have hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, rfl⟩ := hrange hx
      exact ⟨z, hx, rfl⟩
  have hfg := hQ.map ψ
  rw [hmap] at hfg
  exact Submodule.fg_of_fg_map_injective φ hφ hfg

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ _ hnp g hg
  by_contra hall
  obtain ⟨c, hc0, hc⟩ := exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))
  exact hnp c hc0 hc

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift
noncomputable section

open NumberField Complex

namespace PI.VolStabSW

namespace ChLiftW

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := by
    intro x h
    have h1 := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (k : ℕ) (y : W), χ ((k : ℝ) • y) = χ y ^ k := by
    intro k y
    induction k with
    | zero => simp [h0]
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y : W, ‖y‖ ≤ δ → ‖χ y - 1‖ < 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
    have h2 := h (x := y) (by rw [dist_zero_right]; linarith)
    rwa [h0, dist_eq_norm] at h2
  have hre : ∀ y : W, ‖y‖ ≤ δ → 0 < (χ y).re := by
    intro y hy
    have h1 := hball y hy
    have h2 : |(χ y - 1).re| ≤ ‖χ y - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (h2.trans h1.le)).1
    linarith
  have harg : ∀ y : W, ‖y‖ ≤ δ → |Complex.arg (χ y)| < Real.pi / 2 := fun y hy =>
    Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (hre y hy))
  set L : W → ℂ := fun y => Complex.log (χ y) with hL
  have hL0 : L 0 = 0 := by simp [hL, h0]
  have hLadd : ∀ y z : W, ‖y‖ ≤ δ → ‖z‖ ≤ δ → L (y + z) = L y + L z := by
    intro y z hy hz
    simp only [hL]
    have h1 := abs_lt.1 (harg y hy)
    have h2 := abs_lt.1 (harg z hz)
    rw [hadd, Complex.log_mul (hne y) (hne z)]
    constructor <;> linarith [Real.pi_pos]
  have hLsmul : ∀ (k : ℕ) (y : W), (k : ℝ) * ‖y‖ ≤ δ → L ((k : ℝ) • y) = k * L y := by
    intro k y
    induction k with
    | zero => intro _; simp [hL0]
    | succ k ih =>
      intro hk
      have hy0 := norm_nonneg y
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      push_cast at hk
      have h1 : (k : ℝ) * ‖y‖ ≤ δ := by nlinarith
      have h2 : ‖y‖ ≤ δ := by nlinarith
      have h3 : ‖(k : ℝ) • y‖ ≤ δ := by rw [norm_smul, Real.norm_natCast]; exact h1
      rw [Nat.cast_succ, add_smul, one_smul, hLadd _ _ h3 h2, ih h1]
      push_cast
      ring
  have hkey : ∀ (a b : ℕ) (x : W), 0 < a → 0 < b → ‖x‖ ≤ a * δ → ‖x‖ ≤ b * δ →
      (a : ℂ) * L ((a : ℝ)⁻¹ • x) = (b : ℂ) * L ((b : ℝ)⁻¹ • x) := by
    intro a b x ha hb hxa hxb
    have ha' : (0 : ℝ) < a := Nat.cast_pos.2 ha
    have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
    have e1 : (b : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (a : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have e2 : (a : ℝ) • (((a : ℝ) * b)⁻¹ • x) = (b : ℝ)⁻¹ • x := by
      rw [smul_smul]
      congr 1
      field_simp
    have ny : ‖((a : ℝ) * b)⁻¹ • x‖ = ‖x‖ / (a * b) := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
      ring
    have hb1 : (b : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (b : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / a by field_simp, div_le_iff₀ ha']
      linarith
    have ha1 : (a : ℝ) * ‖((a : ℝ) * b)⁻¹ • x‖ ≤ δ := by
      rw [ny, show (a : ℝ) * (‖x‖ / (a * b)) = ‖x‖ / b by field_simp, div_le_iff₀ hb']
      linarith
    rw [← e1, ← e2, hLsmul b _ hb1, hLsmul a _ ha1]
    ring
  set N : W → ℕ := fun x => ⌈‖x‖ / δ⌉₊ + 1 with hN
  have hNpos : ∀ x, 0 < N x := fun x => Nat.succ_pos _
  have hNle : ∀ x, ‖x‖ ≤ (N x : ℝ) * δ := by
    intro x
    have h1 : ‖x‖ / δ ≤ ⌈‖x‖ / δ⌉₊ := Nat.le_ceil _
    have h2 : ‖x‖ ≤ (⌈‖x‖ / δ⌉₊ : ℝ) * δ := by rwa [div_le_iff₀ hδ] at h1
    simp only [hN]
    push_cast
    nlinarith
  set f : W → ℂ := fun x => (N x : ℂ) * L ((N x : ℝ)⁻¹ • x) with hf
  have hfM : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → f x = M * L ((M : ℝ)⁻¹ • x) :=
    fun M x hM hx => hkey (N x) M x (hNpos x) hM (hNle x) hx
  have hsmall : ∀ (M : ℕ) (x : W), 0 < M → ‖x‖ ≤ M * δ → ‖(M : ℝ)⁻¹ • x‖ ≤ δ := by
    intro M x hM hx
    have hM' : (0 : ℝ) < M := Nat.cast_pos.2 hM
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hM'.le, inv_mul_le_iff₀ hM']
    linarith
  have fadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    have hMpos : 0 < N x + N y := by have := hNpos x; omega
    have hcx : (N x : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N x ≤ N x + N y)
    have hcy : (N y : ℝ) * δ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast (by omega : N y ≤ N x + N y)
    have hx : ‖x‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle x).trans hcx
    have hy : ‖y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := (hNle y).trans hcy
    have hxy : ‖x + y‖ ≤ ((N x + N y : ℕ) : ℝ) * δ := by
      have h1 := norm_add_le x y
      have h2 := hNle x
      have h3 := hNle y
      push_cast
      linarith
    rw [hfM _ (x + y) hMpos hxy, hfM _ x hMpos hx, hfM _ y hMpos hy, smul_add,
      hLadd _ _ (hsmall _ x hMpos hx) (hsmall _ y hMpos hy), mul_add]
  have fexp : ∀ x, χ x = Complex.exp (f x) := by
    intro x
    show χ x = Complex.exp ((N x : ℂ) * Complex.log (χ ((N x : ℝ)⁻¹ • x)))
    rw [Complex.exp_nat_mul, Complex.exp_log (hne _), ← hpow, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast (hNpos x).ne'), one_smul]
  have fcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x0
    have hMpos : 0 < N x0 + 1 := Nat.succ_pos _
    have hMr : ((N x0 + 1 : ℕ) : ℝ) = N x0 + 1 := by push_cast; ring
    have hx0 : ‖x0‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
      rw [hMr]
      nlinarith [hNle x0]
    have heq : (fun x => ((N x0 + 1 : ℕ) : ℂ) * L (((N x0 + 1 : ℕ) : ℝ)⁻¹ • x)) =ᶠ[nhds x0] f := by
      filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x‖ ≤ ((N x0 + 1 : ℕ) : ℝ) * δ := by
        have h2 := norm_sub_norm_le x x0
        rw [hMr]
        nlinarith [hNle x0]
      exact (hfM _ x hMpos h1).symm
    refine ContinuousAt.congr ?_ heq
    apply ContinuousAt.mul continuousAt_const
    simp only [hL]
    apply ContinuousAt.clog
    · exact (hc.comp (continuous_const_smul _)).continuousAt
    · exact Complex.mem_slitPlane_iff.2 (Or.inl (hre _ (hsmall _ x0 hMpos hx0)))
  exact ⟨AddMonoidHom.mk' f fadd, fcont, fexp⟩

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have he0 : e 0 = 0 := by simpa using he 0 0
  have hs0 : e.symm 0 = 0 := by rw [← he0, Homeomorph.symm_apply_apply]
  have hsadd : ∀ w w' : W, e.symm (w + w') = e.symm w + e.symm w' := by
    intro w w'
    apply e.injective
    rw [he, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (fun w => χ (e.symm w)) (hc.comp e.symm.continuous)
    (fun w w' => by simp only [hsadd, hadd]) (by simp only [hs0, h0])
  refine ⟨AddMonoidHom.mk' (fun x => ℓ' (e x)) (fun x y => by simp only [he, map_add (f := _)]),
    hℓc.comp e.continuous, fun x => ?_⟩
  have h1 := hℓ (e x)
  simp only [Homeomorph.symm_apply_apply] at h1
  exact h1

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  rcases v.isReal_or_isComplex with hv | hv
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv) x y) χ hc hadd h0
  · exact lift_homeo (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).toHomeomorph
      (fun x y => map_add (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  refine Finset.induction_on s (by simp [AddChar.map_zero_eq_one]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW


open Classical in
def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x := by
  simp only [sgl]
  exact Finset.univ_sum_single x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have key : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := by
    intro v
    exact lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul]) (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓ hℓc hℓ using key
  refine ⟨AddMonoidHom.mk' (fun x => ∑ v, ℓ v (x v)) (fun x y => ?_), ?_, fun x => ?_⟩
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_add (f := _)]
    rfl
  · exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · show χ x = Complex.exp (∑ v, ℓ v (x v))
    conv_lhs => rw [← sum_sgl x]
    rw [ChLiftW.addChar_sum, Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabSW
end
end
