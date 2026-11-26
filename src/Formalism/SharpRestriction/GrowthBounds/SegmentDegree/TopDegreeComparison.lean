module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NegDminusLeMu

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantMultihomogeneous
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentProductDegreeDetermined
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Img

variable {ι ι' : Type} {n : ℕ}

theorem multideg_imgMon [DecidableEq ι'] (ga : ι → ι') (ep : ι → ℕ) (m : ι × Fin n →₀ ℕ) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      m.sum fun v k => (if ga v.1 = t then ep v.1 else 0) * k := by
  classical
  unfold multideg imgMon
  simp only [Finsupp.sum_apply]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : ga v.1 = t
  · simp [h]
  · simp [h]

theorem sum_eq_multideg (h : ι → ℕ) (m : ι × Fin n →₀ ℕ) (T : Finset ι) (hT : ∀ v ∈ m.support, v.1 ∈ T) :
    (m.sum fun v k => h v.1 * k) = ∑ x ∈ T, h x * multideg m x := by
  classical
  have hsub : m.support ⊆ T ×ˢ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨hT v hv, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (fun _ _ => mul_zero _), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold multideg
  rw [Finset.mul_sum]

theorem multideg_imgMon_congr (ga : ι → ι') (ep : ι → ℕ) (m m' : ι × Fin n →₀ ℕ)
    (h : ∀ x, multideg m x = multideg m' x) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m') t := by
  classical
  rw [multideg_imgMon, multideg_imgMon]
  let T : Finset ι := m.support.image Prod.fst ∪ m'.support.image Prod.fst
  rw [sum_eq_multideg (fun x => if ga x = t then ep x else 0) m T
      (fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
    sum_eq_multideg (fun x => if ga x = t then ep x else 0) m' T
      (fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))]
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

theorem degAt_aeval {R : Type} [CommRing R] (ga : ι → ι') (ep : ι → ℕ) {β : ι → ℕ}
    {P Q : MvPolynomial (ι × Fin n) R} (hP : P ∈ Pol R n β) (hQ : Q ∈ Pol R n β) (hQ0 : Q ≠ 0) :
    ∃ δ : ι' → ℕ, (∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) P)) ∧
      ∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) Q) := by
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hQ0
  have hm0' : m0 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm0
  refine ⟨fun t => multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m0) t,
    fun t m' hm' => ?_, fun t m' hm' => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) P hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hP m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) Q hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hQ m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t

end Img

theorem degAt_monomial {R : Type} [CommRing R] {ι : Type} {n : ℕ} (l : ι × Fin n →₀ ℕ) (c : R) (t : ι) :
    DegAt t (multideg l t) (monomial l c : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_of_degAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) R}
    (h : ∀ t, DegAt t (d t) P) : P ∈ Pol R n d := mem_Pol_iff.mpr fun m hm t => h t m hm

theorem segment_product_degree_determined : SegmentProductDegreeDetermined := by
  intro p n' r K _ F O _ x z β l0 d hx hz hdeg hne
  classical
  have hz0 : ∀ j ∈ Finset.range F.J, z (j : ℤ) ≠ 0 := by
    intro j hj h0
    apply hne
    rw [Finset.prod_eq_zero hj (by rw [h0, map_zero]), zero_mul]
  have key : ∀ j : ℕ, ∃ δ : Fin n' → ℕ, j ∈ Finset.range F.J →
      (∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (x j))) ∧ ∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (z j)) := by
    intro j
    by_cases hj : j ∈ Finset.range F.J
    · obtain ⟨δ, h1, h2⟩ := degAt_aeval (R := O) (n := r + K) (fun y : ℤ => posOf n' y)
        (fun y : ℤ => p ^ F.dist (j : ℤ) y) (hx j) (hz j) (hz0 j hj)
      exact ⟨δ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose δ hδ using key
  have hX : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).1 t) (degAt_monomial l0 1 t)
  have hZ : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).2 t) (degAt_monomial l0 1 t)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg ⊢
  refine mem_Pol_of_degAt fun t => ?_
  have e : d t = ∑ j ∈ Finset.range F.J, δ j t + multideg l0 t :=
    (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hZ t m0 hm0')
  rw [e]
  exact hX t

theorem degAt_sum {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) R) (h : ∀ i ∈ s, DegAt x d (f i)) : DegAt x d (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h i hi m hmi

theorem degAt_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} (c : R)
    {P : MvPolynomial (ι × Fin n) R} (h : DegAt x d P) : DegAt x d (C c * P) := by
  intro m hm
  refine h m ?_
  rw [mem_support_iff] at hm ⊢
  intro h0
  exact hm (by rw [coeff_C_mul, h0, mul_zero])

theorem degAt_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x t : ℤ) :
    DegAt t (∑ a : Fin r, if X.row j x a = t then 1 else 0) (X.detPl R j x) := by
  classical
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin r) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin r => (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) R)) (σ i) i)
    (fun i => if X.row j x (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (X.row j x (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if X.row j x a = t then 1 else 0)] at h2
  exact h2

theorem segment_image_multihomogeneous : SegmentImageMultihomogeneous := by
  intro p n' r K _ _ _ X O _ j b y e hy
  classical
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0]; simp [Dat.zSeg]⟩
  have hexp : ∀ P : SegRing O r K, expand (p ^ X.Rj p K j) P =
      aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^
        (fun _ : ℤ => p ^ X.Rj p K j) v.1) P := by
    intro P
    have : expand (p ^ X.Rj p K j) = aeval (fun v : ℤ × Fin (r + K) =>
        (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp
    rw [this]
  obtain ⟨δ, h1, -⟩ := degAt_aeval (R := O) (n := r + K) (fun z : ℤ => z) (fun _ : ℤ => p ^ X.Rj p K j) hy hy hy0
  have hD : X.DlSeg p K O j ∈ Pol O r (fun t => ∑ x ∈ X.toLate j, X.sg p K j x *
      ∑ a : Fin r, if X.row j x a = t then 1 else 0) := by
    refine mem_Pol_of_degAt fun t => ?_
    unfold Dat.DlSeg
    exact degAt_prod _ _ _ fun x _ => degAt_pow (degAt_detPl X j x t) _
  have h := hom_Pol_mul O (hom_Pol_mul O (plEmb_Pol r K hD) (mem_Pol_of_degAt h1))
    (mem_Pol_of_degAt fun t => degAt_monomial e (1 : O) t)
  unfold Dat.zSeg
  rw [hexp]
  exact ⟨_, h⟩

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem degAt_ph_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j x : ℤ) (t : Fin n') :
    DegAt t (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) := by
  have key : ∀ σ : Equiv.Perm (Fin r), DegAt t
      (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (∏ i : Fin r, phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x (σ i), i)))) := by
    intro σ
    rw [← Equiv.sum_comp σ (fun a => if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)]
    apply degAt_prod
    intro i _
    simp only [plEmb, phSeg, rename_X, aeval_X]
    have h := degAt_pow (R := R) (degAt_X (x := t) (posOf n' (X.row j x (σ i)), Fin.castAdd K i))
      (p ^ X.F.dist j (X.row j x (σ i)))
    convert h using 2
    split_ifs <;> simp
  unfold Dat.detPl
  rw [Matrix.det_apply']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, Matrix.of_apply, map_intCast]
  apply degAt_sum
  intro σ _
  have e : ((Equiv.Perm.sign σ : ℤ) : RRing R n' (r + K)) = C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [e]
  exact degAt_C_mul _ (key σ)

theorem discriminant_multihomogeneous : DiscriminantMultihomogeneous := by
  intro p n' r K _ _ _ X O _
  rw [RRdeg, mem_restrictSupport_iff]
  intro m hm t
  have hdeg : DegAt t (X.Et p K t) (X.Dl p K O) := by
    unfold Dat.Dl Dat.DlSeg Dat.Et
    simp only [map_prod, map_pow]
    apply degAt_prod
    intro j _
    apply degAt_prod
    intro x _
    exact degAt_pow (degAt_ph_detPl X p K j x t) _
  exact hdeg m hm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopOccursInAtMostTwoSegments
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TopCountLowerBoundsOfOccurrence
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace


open Classical in
def LeadingLetterInAtMostTwoSegments : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ t : Fin n',
    ∑ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤ 2

section locP_coef_Lsh

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem oldest_le_row (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.F.oldest j x ≤ X.row j x i := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hi := i.isLt
  rw [oldest_eq, row_eq]
  have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  exact evL_mono X.F j x (by omega) h2

theorem sg_mul_le (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    (X.sg p K j x : ℝ) * (p : ℝ) ^ X.F.dist j (X.row j x i) ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hold : X.F.oldest j x ∈ X.F.letters j := by
    rw [oldest_eq]
    have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
    rw [List.getD_eq_getElem _ _ h1]
    exact ((mem_evL X.F j x _).1 (List.getElem_mem h1)).1
  have hle := oldest_le_row hX j x hx i
  have hdist : X.F.dist j (X.row j x i) ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  obtain ⟨-, -, hpos⟩ := mem_letters_bounds hold
  have hdeg := (hX.degs _ hpos).2
  have hp1 : 1 ≤ p := le_trans (by norm_num) hX.p13
  have hp : (1:ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0:ℝ) < p := by linarith
  have hK0 : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hkpos : (0:ℝ) < Dat.k (r := r) K := by
    unfold Dat.k
    exact_mod_cast (by omega : 0 < r + K)
  have hY := hX.Y1
  have hk : 0 < Dat.k (r := r) K ^ 2 * X.Y := by positivity
  have hpd : (0:ℝ) < (p:ℝ) ^ X.F.dist j (X.F.oldest j x) := pow_pos hp0 _
  have hBo : 0 ≤ X.Bo p j x := by
    unfold Dat.Bo
    exact div_nonneg (Nat.cast_nonneg _) hpd.le
  have hsg : (X.sg p K j x : ℝ) ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) := by
    unfold Dat.sg
    exact Nat.floor_le (div_nonneg hBo hk.le)
  have hpow : (p:ℝ) ^ X.F.dist j (X.row j x i) ≤ (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
    pow_le_pow_right₀ hp hdist
  calc (X.sg p K j x : ℝ) * (p:ℝ) ^ X.F.dist j (X.row j x i)
      ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) * (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
        mul_le_mul hsg hpow (by positivity) (div_nonneg hBo hk.le)
    _ = (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (Dat.k (r := r) K ^ 2 * X.Y) := by
        unfold Dat.Bo
        field_simp
    _ ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        gcongr

private theorem late_index_map_mem_letters (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.row j x i ∈ X.F.letters j := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  have hi := i.isLt
  rw [row_eq]
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2]
  exact ((mem_evL X.F j x _).1 (List.getElem_mem h2)).1

private theorem late_index_map_injective (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) :
    Function.Injective (X.row j x) := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.1 hmem.2
  intro i i' h
  have hi := i.isLt
  have hi' := i'.isLt
  rw [row_eq, row_eq] at h
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  have h2' : (evL X.F j x).length - r + (i' : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h2'] at h
  have h3 := (evL_nodup X.F j x).getElem_inj_iff.1 h
  ext
  omega

open Classical in
theorem Et_le (hOcc : LeadingLetterInAtMostTwoSegments) (hX : X.Hyp p K) (t : Fin n') :
    (X.Et p K t : ℝ) ≤ 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have B := basics hX
  have hY0 : 0 ≤ X.Y := by linarith [B.Y1]
  have hlhs : 0 ≤ (32:ℝ) * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) hY0) (sq_nonneg _)) (Nat.cast_nonneg _)) (sq_nonneg _)) (by positivity)
  have ha0 : 0 ≤ X.a := le_trans hlhs hX.P3
  have hk5 := B.k5
  have hden : 0 < Dat.k (r := r) K ^ 2 * X.Y := by
    have : (0:ℝ) < Dat.k (r := r) K := by linarith
    have : (0:ℝ) < X.Y := by linarith [B.Y1]
    positivity
  set c : ℝ := 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hden.le
  have hcnt : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card ≤
        ((X.F.letters j).filter fun y => posOf n' y = t).card := by
    intro j x hx
    apply Finset.card_le_card_of_injOn (fun i => X.row j x i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        Finset.mem_coe, Finset.mem_filter] at hi ⊢
      exact ⟨late_index_map_mem_letters hX j x hx i, hi⟩
    · intro i _ i' _ h
      exact late_index_map_injective hX j x hx h
  have hterm : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (((X.sg p K j x * ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0 : ℕ)) : ℝ)
        ≤ c * (((X.F.letters j).filter fun y => posOf n' y = t).card : ℝ) := by
    intro j x hx
    push_cast
    rw [Finset.mul_sum]
    calc ∑ i : Fin r, (X.sg p K j x : ℝ) *
          (if posOf n' (X.row j x i) = t then (p : ℝ) ^ X.F.dist j (X.row j x i) else 0)
        ≤ ∑ i : Fin r, (if posOf n' (X.row j x i) = t then c else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact sg_mul_le hX j x hx i
          · simp
      _ = c * ((Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
          gcongr
          exact_mod_cast hcnt j x hx
  have hOcc' := hOcc p n' r K X hX t
  have hOccR : (∑ j ∈ Finset.range X.F.J,
      (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) ≤ 2 := by
    exact_mod_cast hOcc'
  unfold Dat.Et
  rw [Nat.cast_sum]
  calc _ ≤ ∑ j ∈ Finset.range X.F.J,
        (X.Ns : ℝ) * (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Nat.cast_sum]
        calc _ ≤ ∑ x ∈ X.toLate (j : ℤ),
              c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ) :=
              Finset.sum_le_sum fun x hx => hterm _ x hx
          _ = ((X.toLate (j : ℤ)).card : ℝ) *
              (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by
              have hl : (X.toLate (j : ℤ)).card ≤ X.Ns := (Finset.card_filter_le _ _).trans (hX.card _)
              gcongr
    _ = (X.Ns : ℝ) * (c * ∑ j ∈ Finset.range X.F.J,
          (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (X.Ns : ℝ) * (c * 2) := by gcongr
    _ = 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        rw [hc]
        ring

theorem a_ge (hX : X.Hyp p K) : 32 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a := by
  have B := basics hX
  have hE : (0:ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by positivity
  have hrK : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h := B.k5
    unfold Dat.k at h
    linarith
  have hsq : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := one_le_pow₀ hrK
  have hq : (1:ℝ) ≤ X.Q ^ 2 := one_le_pow₀ B.Q1
  have hp : (1:ℝ) ≤ p := by linarith [B.p1]
  have hY := B.Y1
  have hNs := B.Ns1
  have h1 : (1:ℝ) ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 := by
    have e1 : (1:ℝ) ≤ (p : ℝ) * X.Y := one_le_mul_of_one_le_of_one_le hp hY
    have e2 := one_le_mul_of_one_le_of_one_le e1 hsq
    have e3 := one_le_mul_of_one_le_of_one_le e2 hNs
    exact one_le_mul_of_one_le_of_one_le e3 hq
  have h2 := mul_le_mul_of_nonneg_right h1 hE
  have h3 := hX.P3
  nlinarith

theorem k_sq_mul_Y_ge_Ns (hX : X.Hyp p K) (hC : 32 ≤ X.Ck) : 160 * (X.Ns : ℝ) ≤ Dat.k (r := r) K ^ 2 * X.Y := by
  have B := basics hX
  have ha := a_ge hX
  have hE0 : (0:ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have ha32 : (32:ℝ) ≤ X.a := by linarith
  have hlog : 1 ≤ Real.log X.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hNs := B.Ns1
  have hNs2 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    have e1 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
    have e2 : (X.Ns : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a :=
      le_mul_of_one_le_right (sq_nonneg _) hlog
    linarith
  have hCk : 32 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [mul_assoc X.Ck]
    exact mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
  have hP1 := hX.P1
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hk5 : (5:ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h := B.k5
    rw [hkdef] at h
    exact h
  have hk32 : 32 * (X.Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) := by linarith
  have hY := hX.Y1
  rw [hkdef]
  have e1 : 0 ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Y - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have e2 : 0 ≤ ((r + K : ℕ) : ℝ) * (((r + K : ℕ) : ℝ) - 5) := mul_nonneg (by linarith) (by linarith)
  nlinarith

end locP_coef_Lsh

theorem top_count_lower_bounds_of_occurrence (C₀ : ℝ) (hC : 32 ≤ C₀) (hOcc : LeadingLetterInAtMostTwoSegments) : TopCountLowerBounds C₀ := by
  intro p n' r K _ _ _ X hX _ hCk
  have hCk' : 32 ≤ X.Ck := le_trans hC hCk
  have hk := k_sq_mul_Y_ge_Ns hX hCk'
  have ha := a_ge hX
  have B := basics hX
  have hNs : (1:ℝ) ≤ X.Ns := B.Ns1
  have hE0 : (0:ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm0 : (0:ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have ha0 : 0 ≤ X.a := by linarith
  have hE0a : 32 * (X.E₀ : ℝ) ≤ X.a := by linarith
  have hEt40 : ∀ t, (X.Et p K t : ℝ) ≤ X.a / 40 := by
    intro t
    refine (Et_le hOcc hX t).trans ?_
    have hpos : 0 < Dat.k (r := r) K ^ 2 * X.Y := by linarith
    rw [div_le_div_iff₀ hpos (by norm_num)]
    have := mul_le_mul_of_nonneg_left hk ha0
    nlinarith
  have hd : ∀ t ∈ X.F.TT, (X.d t : ℝ) = X.deg t - X.E' t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have hle : X.E' t ≤ X.deg t := by
      have : (X.E' t : ℝ) ≤ X.deg t := by linarith
      exact_mod_cast this
    unfold Dat.d
    rw [if_pos ht, Nat.cast_sub hle]
  have hEtd : ∀ t ∈ X.F.TT, X.Et p K t ≤ X.d t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have h : (X.Et p K t : ℝ) ≤ X.d t := by
      rw [hd t ht]
      linarith [hEt40 t]
    exact_mod_cast h
  constructor
  · intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    unfold Dat.a'
    rw [Nat.cast_sub (hEtd t ht), hd t ht]
    linarith [hEt40 t]
  · intro t
    by_cases ht : t ∈ X.F.TT
    · exact hEtd t ht
    · have h0 : X.Et p K t = 0 := by
        unfold Dat.Et
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro x hx
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro hpos
        apply ht
        rw [← hpos]
        exact (mem_letters_bounds (late_index_map_mem_letters hX _ x hx i)).2.2
      rw [h0]
      exact Nat.zero_le _

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Occ

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

open Classical in
theorem occ_Ioc (hV : F.Valid L₁ N₁) (c : ℤ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, ((Finset.Ioc (eFr F ((j : ℤ) + c)) (eFr F (((j + 1 : ℕ) : ℤ) + c))).filter
      fun y => posOf n' y = t).card ≤ 1 := by
  have hm := eFr_strictMono hV
  have h3 := sum_card_Ioc (fun i : ℕ => eFr F ((i : ℤ) + c)) (fun a b hab => hm.monotone (by omega))
    (fun y => posOf n' y = t) F.J
  rw [h3]
  have h2 : eFr F ((F.J : ℤ) + c) = eFr F (((0 : ℕ) : ℤ) + c) + n' := by
    have := hV.2.1 c (r - 1)
    simp only [eFr]
    rw [show (F.J : ℤ) + c = c + F.J by ring, show ((0 : ℕ) : ℤ) + c = c by simp, this]
  simp only [h2]
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact posOf_injOn _ (Finset.mem_Ioc.mp ha'.1) (Finset.mem_Ioc.mp hb'.1) (ha'.2.trans hb'.2.symm)

end Occ

theorem top_occurs_in_at_most_two_segments : LeadingLetterInAtMostTwoSegments := by
  intro p n' r K _ _ _ X hX t
  classical
  have hV := hX.valid
  have h1 := occ_Ioc hV (-2) t
  have h2 := occ_Ioc hV (-1) t
  have key : ∀ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -2)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -2))).filter fun y => posOf n' y = t).card +
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -1)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -1))).filter fun y => posOf n' y = t).card := by
    intro j _
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyl, hyt⟩ := Finset.mem_filter.mp hy
    have hb := mem_letters_bounds hyl
    have e1 : ((j + 1 : ℕ) : ℤ) + -2 = (j : ℤ) - 1 := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℤ) + -1 = (j : ℤ) := by push_cast; ring
    have e3 : (j : ℤ) + -1 = (j : ℤ) - 1 := by ring
    have h4 := hV.2.2.2.1 ((j : ℤ) + -2)
    have e4 : (j : ℤ) + -2 + 1 = (j : ℤ) - 1 := by ring
    rw [e4] at h4
    rw [e1, e2, e3, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    simp only [eFr]
    by_cases hc : y ≤ X.F.fr ((j : ℤ) - 1) (r - 1)
    · exact Or.inl ⟨⟨lt_of_lt_of_le h4 hb.1, hc⟩, hyt⟩
    · exact Or.inr ⟨⟨not_le.mp hc, hb.2.1⟩, hyt⟩
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib]
  omega

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem idx_unique {e : ℤ → ℤ} (hm : StrictMono e) {a b x : ℤ} (h1 : e (a - 1) < x) (h2 : x ≤ e a)
    (h3 : e (b - 1) < x) (h4 : x ≤ e b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exfalso
    have := hm.monotone (show a ≤ b - 1 by omega)
    linarith
  · exact h
  · exfalso
    have := hm.monotone (show b ≤ a - 1 by omega)
    linarith

section U

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem LL_unique (hV : F.Valid L₁ N₁) (j0 : ℕ) (hj0 : j0 < F.J) (z : ℤ) (hz : z ∈ F.LLset (j0 : ℤ))
    (j : ℕ) (hj : j < F.J) (x : ℤ) (hx : x ∈ F.letters (j : ℤ)) (hxz : posOf n' x = posOf n' z) :
    j = j0 ∧ x = z := by
  obtain ⟨hJ, hper, hinc, hgap, -, -, -, -, -⟩ := hV

  have hperT : ∀ t : ℤ, ∀ (j' : ℤ) i, F.fr (j' + t * F.J) i = F.fr j' i + t * n' := by
    intro t
    induction t using Int.induction_on with
    | zero => intro j' i; simp
    | succ t ih =>
      intro j' i
      have e : j' + (t + 1) * F.J = (j' + t * F.J) + F.J := by ring
      rw [e, hper, ih]
      ring
    | pred t ih =>
      intro j' i
      have e1 := hper (j' + (-(t : ℤ) - 1) * F.J) i
      have e : j' + (-(t : ℤ) - 1) * F.J + F.J = j' + -(t : ℤ) * F.J := by ring
      rw [e, ih] at e1
      linarith

  have hin : ∀ (j' : ℤ) (i : ℕ), i ≤ r - 1 → F.fr j' 0 ≤ F.fr j' i := by
    intro j' i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have := hinc j' i (by omega)
      linarith [ih (by omega)]
  have hr0 : ∀ j' : ℤ, F.fr j' 0 ≤ F.fr j' (r - 1) := fun j' => hin j' (r - 1) le_rfl
  have mono0 : StrictMono (fun j' : ℤ => F.fr j' 0) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 j'; linarith)
  have monoL : StrictMono (fun j' : ℤ => F.fr j' (r - 1)) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 (j' + 1); linarith)

  have key : ∀ (g j' : ℤ) (y : ℤ), F.fr (g - 1) (r - 1) < y → y < F.fr g 0 →
      F.fr (j' - 1) 0 ≤ y → y ≤ F.fr j' (r - 1) → j' = g := by
    intro g j' y h1 h2 h3 h4
    rcases lt_trichotomy j' g with h | h | h
    · exfalso
      have := monoL.monotone (show j' ≤ g - 1 by omega)
      linarith
    · exact h
    · exfalso
      have := mono0.monotone (show g ≤ j' - 1 by omega)
      linarith

  simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hz
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
  obtain ⟨⟨hx1, hx2⟩, -⟩ := hx
  have hmod : x % (n' : ℤ) = z % (n' : ℤ) := by
    rw [← posOf_val, ← posOf_val, hxz]
  obtain ⟨t, ht⟩ := Int.ModEq.dvd hmod

  have hxt : x = z + (-t) * n' := by linarith
  have g1 := hperT (-t) ((j0 : ℤ) - 1) (r - 1)
  have g2 := hperT (-t) (j0 : ℤ) 0
  have e1 : (j0 : ℤ) - 1 + -t * F.J = ((j0 : ℤ) + -t * F.J) - 1 := by ring
  rw [e1] at g1
  have hjj := key ((j0 : ℤ) + -t * F.J) (j : ℤ) x (by rw [g1, hxt]; linarith) (by rw [g2, hxt]; linarith) hx1 hx2
  have hJ1 : (1 : ℤ) ≤ F.J := by exact_mod_cast hJ
  have ht0 : t = 0 := by
    have hj' : (j : ℤ) < F.J := by exact_mod_cast hj
    have hj0' : (j0 : ℤ) < F.J := by exact_mod_cast hj0
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have : (1 : ℤ) ≤ -t := by omega
      nlinarith
    · exact h
    · exfalso
      have : (1 : ℤ) ≤ t := by omega
      nlinarith
  subst ht0
  constructor
  · simp at hjj
    exact_mod_cast hjj
  · simpa using hxt

end U

theorem top_degree_comparison : TopDegreeComparison := by
  intro p n' r K _ _ _ X O _ _ hX b y l hy hl hdeg hne j0 hj0 z hz
  classical
  have hV := hX.valid
  have hj0' : j0 < X.F.J := Finset.mem_range.mp hj0
  have hzz := hz
  unfold Frames.LLset at hzz
  rw [Finset.mem_filter, Finset.mem_Ioo] at hzz
  obtain ⟨⟨hz1, hz2⟩, hzT⟩ := hzz
  have hzW : ¬ X.F.IsW (j0 : ℤ) z := not_le.mpr hz1
  have hzl : z ∈ X.F.letters (j0 : ℤ) := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(fr_zero_le_eFr hV _).trans hz1.le, hz2.le.trans (fr_zero_le_eFr hV _)⟩, hzT⟩
  set t := posOf n' z with ht
  set P : ℕ := p ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ)) with hP
  have hδ : ∀ j ∈ Finset.range X.F.J, DegAt t (if j = j0 then P * b j0 z else 0) (X.phc p K O (j : ℤ) (y j)) := by
    intro j hj m' hm'
    have hj' : j < X.F.J := Finset.mem_range.mp hj
    obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
      (fun v => p ^ (X.F.dist (j : ℤ) v.1 + X.Rj p K (j : ℤ))) (y j) hm'
    have hsup := XX'_supported O X.F (j : ℤ) _ _ _ (hy j).1.1
    have hT : ∀ v ∈ m.support, v.1 ∈ X.F.letters (j : ℤ) := by
      intro v hv
      have hvv : v ∈ (y j).vars := (mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩
      exact ((mem_supported.mp hsup) (Finset.mem_coe.mpr hvv)).1
    have hPol : y j ∈ Pol O (r + K) (b j) := by rw [← segDeg_eq_Pol]; exact (hy j).1.2
    rw [multideg_imgMon (fun x : ℤ => posOf n' x) (fun x : ℤ => p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ))) m t,
      sum_eq_multideg (fun x => if posOf n' x = t then p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ)) else 0) m
        (X.F.letters (j : ℤ)) hT]
    by_cases hjj : j = j0
    · subst hjj
      rw [if_pos rfl, Finset.sum_eq_single z]
      · rw [if_pos rfl, mem_Pol_iff.mp hPol m hm z]
      · intro x hx hxz
        rw [if_neg, zero_mul]
        intro h
        exact hxz (LL_unique hV j hj0' z hz j hj' x hx h).2
      · intro h; exact absurd hzl h
    · rw [if_neg hjj]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg, zero_mul]
      intro h
      exact hjj (LL_unique hV j0 hj0' z hz j hj' x hx h).1
  have hU := degAt_mul (degAt_prod _ _ _ hδ) (degAt_monomial l (1 : O) t)
  rw [Finset.sum_ite_eq' (Finset.range X.F.J) j0, if_pos hj0] at hU
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg
  have ha' : X.a' p K t = P * b j0 z + multideg l t := (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hU m0 hm0')
  have hP0 : 0 < P := Nat.pow_pos hX.prime.pos
  have hl' : multideg l t ≤ (r + K) * (P - 1) := by
    unfold multideg
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin (r + K) => l (t, c)) (P - 1)
      (fun c _ => Nat.le_sub_one_of_lt (hl (j0 : ℤ) z hzl hzW c))
    simpa using this
  have hrK : 0 < r + K := Nat.add_pos_left (NeZero.pos r) K
  have hlt : X.a' p K t < (b j0 z + (r + K)) * P := by
    rw [ha']
    have : (r + K) * (P - 1) < (r + K) * P := Nat.mul_lt_mul_of_pos_left (by omega) hrK
    nlinarith
  have hltR : (X.a' p K t : ℝ) < ((b j0 z : ℝ) + Dat.k (r := r) K) * (P : ℝ) := by
    unfold Dat.k
    exact_mod_cast hlt
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hPe : ((p : ℝ) ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ))) = (P : ℝ) := by rw [hP]; push_cast; rfl
  rw [hPe, sub_lt_iff_lt_add, div_lt_iff₀ hPR]
  exact hltR

end Formalism.MainNotions.SelectionLemmas.Pf
