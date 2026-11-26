module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem dker_poly_eq (S : Type) [CommRing S] [Algebra A S] (p q : S[X] ⊗[A] E)
    (H : ∀ (T : Type) [CommRing T] [Algebra A T] (f : S[X] →ₐ[A] T), IsNilpotent (f X) →
      D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) p) =
        D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) q)) :
    D.D S[X] p = D.D S[X] q := by
  ext k
  have h := H _ (Ideal.Quotient.mkₐ A (Ideal.span {(X : S[X]) ^ (k + 1)})) ⟨k + 1, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  rw [D.nat, D.nat] at h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h3 := X_pow_dvd_iff.1 h2 k (Nat.lt_succ_self k)
  rwa [coeff_sub, sub_eq_zero] at h3

private theorem dker_unit (T : Type) [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) (w : T ⊗[A] E) :
    IsUnit (1 + (t ⊗ₜ[A] (1 : E)) * w) := by
  apply IsNilpotent.isUnit_one_add
  obtain ⟨k, hk⟩ := ht
  have : (t ⊗ₜ[A] (1 : E)) * w = t • w := by rw [Algebra.smul_def]; rfl
  exact ⟨k, by rw [this, _root_.smul_pow, hk, zero_smul]⟩

private theorem dker_cancel (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    Det.cancel A E S S[X] (1 + X ⊗ₜ w) = 1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w := by
  rw [map_add (f := _), map_one]
  congr 1

private theorem dker_top (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    (D.D S[X] (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w)).coeff n = D.D S w := by
  obtain ⟨h1, h2, -⟩ := d_bc D S
  obtain ⟨-, -, h3, h4, -⟩ := d_chi (D.baseChange S) w
  rw [← dker_cancel, ← h1, h3, ← h2, ← h4, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

private theorem dker_of_kills {x : E} (hx : D.Kills x) : x ∈ D.ker := by
  rw [Det.mem_ker]
  intro S _ _ y u v
  rw [← dker_top, ← dker_top D S y]
  apply congrArg (fun p : S[X] => p.coeff n)
  apply dker_poly_eq
  intro T _ _ f hf
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y) = y'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) u) = u'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) v) = v'
  obtain ⟨c, hc⟩ := dker_unit T (f X) hf y'
  have e : 1 + (f X ⊗ₜ[A] (1 : E)) * (y' + u' * (1 ⊗ₜ x) * v') =
      (c : T ⊗[A] E) * (1 + ((↑c⁻¹ : T ⊗[A] E) * (f X ⊗ₜ[A] (1 : E)) * u' * (1 ⊗ₜ x)) * v') := by
    rw [mul_add, mul_add, ← add_assoc, ← hc]
    simp only [← mul_assoc, Units.mul_inv, one_mul, mul_one]
  rw [e, map_mul, d_comm, ← mul_assoc, hx, mul_one, hc]

private theorem dker_kills_of {x : E}
    (hx : ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) :
    D.Kills x := by
  intro S _ _ h
  have key : D.D S[X] (1 + (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) * (1 ⊗ₜ x)) =
      D.D S[X] 1 := by
    apply dker_poly_eq
    intro T _ _ f hf
    simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h'
    obtain ⟨c, hc⟩ := dker_unit T (f X) hf h'
    have e : 1 + (c : T ⊗[A] E) * (1 ⊗ₜ x) = (c : T ⊗[A] E) * ((↑c⁻¹ : T ⊗[A] E) + 1 ⊗ₜ x) := by
      rw [mul_add, Units.mul_inv]
    rw [← hc, e, map_mul, hx, ← map_mul, Units.mul_inv, map_one]
  let ev : S[X] →ₐ[A] S := (Polynomial.aeval (R := S) (1 : S)).restrictScalars A
  have hev : Algebra.TensorProduct.map ev (AlgHom.id A E)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h := by
    clear key
    induction h with
    | tmul b z => simp [ev]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hX : ev X = 1 := by simp [ev]
  have k2 := congrArg ev key
  rw [← D.nat, map_one, map_one] at k2
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hev, hX] at k2
  rw [← Algebra.TensorProduct.one_def, one_mul, add_mul, one_mul, add_comm (_ ⊗ₜ x), ← add_assoc, hx] at k2
  exact k2

end

theorem UpperTheory.V.CA.d_ker :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), (x ∈ D.ker ↔ D.Kills x) ∧ (x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) ∧ (x ∈ D.ker → ∀ h i, 1 ≤ i → i ≤ n → D.lam i (h * x) = 0) := by
  intro n A E _ _ _ D x
  refine ⟨⟨fun hx S _ _ h => ?_, dker_of_kills D⟩,
    ⟨fun hx S _ _ s y => ?_, fun hx => dker_of_kills D (dker_kills_of D hx)⟩, fun hx h i h1 hi => ?_⟩
  · simpa using D.mem_ker.1 hx S 1 h 1
  · simpa using D.mem_ker.1 hx S y (s ⊗ₜ 1) 1
  · obtain ⟨-, -, h3, -⟩ := d_chi D (h * x)
    have h4 : D.D A[X] (1 + X ⊗ₜ (h * x)) = 1 := by
      simpa using D.mem_ker.1 hx A[X] 1 (X ⊗ₜ h) 1
    have h5 := congrArg (fun p => p.coeff i) (h3.symm.trans h4)
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_one] at h5
    simpa [Nat.lt_succ_of_le hi, show i ≠ 0 by omega] using h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DTrCoeff
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem UpperTheory.V.CA.d_tr_coeff {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (x : E) (i : ℕ) (hi : i ≤ n) : (D.D A[X] (1 + X ⊗ₜ x)).coeff i = D.lam i x := by
  rw [(d_chi D x).2.2.1, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff, hi]

private theorem UpperTheory.V.CA.d_tr_dual {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (hn : 1 ≤ n) (x : E) :
    D.D (DualNumber A) (1 + DualNumber.eps ⊗ₜ x) = 1 + D.tr x • DualNumber.eps := by
  have h := D.nat A[X] (DualNumber A) (aeval DualNumber.eps) (1 + X ⊗ₜ x)
  rw [map_add (f := _), map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at h
  rw [h, (d_chi D x).2.2.1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', (d_chi D x).1]
  have h2 : ∀ k : ℕ, (DualNumber.eps : DualNumber A) ^ (k + 1 + 1) = 0 := fun k => by
    rw [pow_succ, pow_succ, mul_assoc, DualNumber.eps_mul_eps, mul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, aeval_X, aeval_C, h2, mul_zero, Finset.sum_const_zero]
  simp [Det.tr, Algebra.smul_def, add_comm]

theorem UpperTheory.V.CA.d_tr :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), (1 ≤ n → ∃ t : E →ₗ[A] A, ∀ x, t x = D.tr x) ∧ (∀ i x y, D.lam i (x * y) = D.lam i (y * x)) ∧ (1 ≤ n → D.tr 1 = n) := by
  intro n A E _ _ _ D
  refine ⟨fun hn => ⟨⟨⟨D.tr, fun x y => ?_⟩, fun a x => ?_⟩, fun _ => rfl⟩, fun i x y => ?_, fun hn => ?_⟩
  · have h : (1 + DualNumber.eps ⊗ₜ (x + y) : DualNumber A ⊗[A] E) =
        (1 + DualNumber.eps ⊗ₜ x) * (1 + DualNumber.eps ⊗ₜ y) := by
      rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, DualNumber.eps_mul_eps, zero_tmul,
        tmul_add]
      simp only [one_mul, mul_one, add_zero]
      abel
    have h2 := congrArg (D.D (DualNumber A)) h
    rw [map_mul, d_tr_dual D hn, d_tr_dual D hn, d_tr_dual D hn] at h2
    have h3 := congrArg TrivSqZeroExt.snd h2
    simpa [add_comm] using h3
  · simpa [Det.tr] using (d_chi D x).2.2.2.2.2.2 a 1 hn
  · have h : ∀ j ≤ n, D.lam j (x * y) = D.lam j (y * x) := fun j hj => by
      have := d_comm D A[X] (X ⊗ₜ x) (1 ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      rw [← d_tr_coeff D _ j hj, ← d_tr_coeff D _ j hj, this]
    have h2 : D.chi (x * y) = D.chi (y * x) := by
      rw [(d_chi D (x * y)).2.1, (d_chi D (y * x)).2.1]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
    rw [Det.lam, Det.lam, h2]
  · rw [Det.tr, ← d_tr_coeff D 1 1 hn]
    have h : (1 + X ⊗ₜ 1 : A[X] ⊗[A] E) = (1 + X : A[X]) • 1 := by
      rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one, add_tmul]
    simp only [h, D.homog, map_one, mul_one, coeff_one_add_X_pow, Nat.choose_one_right]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem mem_iff {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] [Algebra A B] (D : GDet n A G)
    (x : MonoidAlgebra B G) :
    x ∈ TwoSidedIdeal.span (D.map (algebraMap A B)).CH ↔ toT A G B x ∈
      Submodule.span B ((fun z : MonoidAlgebra A G => (1 : B) ⊗ₜ[A] z) ''
        (TwoSidedIdeal.span D.CH : Set (MonoidAlgebra A G))) := by
  rw [← d_toDet_CH, ← d_toDet_CH, d_toDet_map, ← SetLike.mem_coe (p := Submodule.span B _),
    ← (d_chS D.toDet B).2.1, SetLike.mem_coe]
  obtain ⟨-, -, h1, h2⟩ := d_pull (D.toDet.baseChange B) (toT A G B)
  refine ⟨h1 x, fun h => ?_⟩
  obtain ⟨y, hy, e⟩ := (h2 fun z => ⟨_, toT_ofT z⟩).2 _ h
  have : y = x := by rw [← ofT_toT (A := A) y, e, ofT_toT]
  exact this ▸ hy

private theorem map_mem {A B : Type} [Ring A] [Ring B] (f : A →+* B) (S : Set A) (z : A)
    (hz : z ∈ TwoSidedIdeal.span S) : f z ∈ TwoSidedIdeal.span (f '' S) := by
  induction hz using TwoSidedIdeal.span_induction with
  | mem x hx => exact TwoSidedIdeal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  | right_absorb b x _ hx => rw [map_mul]; exact TwoSidedIdeal.mul_mem_right _ _ _ hx

theorem UpperTheory.V.CA.g_chmap :
    ∀ {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B), TwoSidedIdeal.span (D.map f).CH = TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G f '' D.CH) := by
  intro n A B G _ _ _ D f
  letI : Algebra A B := f.toAlgebra
  change TwoSidedIdeal.span (D.map (algebraMap A B)).CH =
    TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (algebraMap A B) '' D.CH)
  have e : ∀ z : MonoidAlgebra A G, ofT A G B (1 ⊗ₜ z) = MonoidAlgebra.mapRingHom G (algebraMap A B) z :=
    fun z => by rw [ofT_tmul, one_smul]
  apply le_antisymm
  · intro x hx
    rw [mem_iff] at hx
    rw [← ofT_toT (A := A) x]
    generalize toT A G B x = w at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [e]
      exact map_mem _ _ z hz
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx
  · rw [TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_iff, ← e, toT_ofT]
    exact Submodule.subset_span ⟨z, TwoSidedIdeal.subset_span hz, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DUnit
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_unit :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → (∀ x, IsUnit x ↔ IsUnit (D.val x)) ∧ Algebra.IsIntegral A E := by
  intro n A E _ _ _ D hD
  have h0 : ∀ x : E, Polynomial.aeval x (D.chi x) = 0 := ((d_chS D A).2.2 hD).2
  refine ⟨fun x => ⟨fun h => h.map D.val, fun h => ?_⟩, ⟨fun x => ?_⟩⟩
  · have h1 : D.lam n x = D.val x := (d_chi D x).2.2.2.1
    rw [← h1, Det.lam, Nat.sub_self] at h
    have hc : IsUnit ((D.chi x).coeff 0) := isUnit_of_mul_isUnit_right h
    have h2 := h0 x
    rw [← Polynomial.X_mul_divX_add (D.chi x), map_add (f := _), map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C] at h2
    have h3 : IsUnit (x * Polynomial.aeval x (D.chi x).divX) := by
      rw [eq_neg_of_add_eq_zero_left h2]
      exact (hc.map (algebraMap A E)).neg
    have h4 : Commute x (Polynomial.aeval x (D.chi x).divX) := by
      have := (Commute.all (X : A[X]) (D.chi x).divX).map (Polynomial.aeval x)
      rwa [Polynomial.aeval_X] at this
    exact (h4.isUnit_mul_iff.1 h3).1
  · exact ⟨D.chi x, (d_chi D x).2.2.2.2.1, h0 x⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem dim_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have hl : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      (by rw [← hm]; exact Ideal.le_comap_map)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self] at h
  simp at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, h]

private theorem dim_quot_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (J : Ideal A) :
    ringKrullDim (B ⧸ J.map (algebraMap A B)) = ringKrullDim (A ⧸ J) := by
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Ideal.map_top]
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  have hJm : J ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hJ
  have hIm : J.map (algebraMap A B) ≤ maximalIdeal B := hm ▸ Ideal.map_mono hJm
  have hI : J.map (algebraMap A B) ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hIm
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : Nontrivial (B ⧸ J.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J.map (algebraMap A B)) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) := by
    have e : (B ⧸ J.map (algebraMap A B)) ≃ₗ[A] TensorProduct A (A ⧸ J) B :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.restrictScalars A).trans
        (TensorProduct.comm A B (A ⧸ J))
    haveI := Module.Flat.baseChange A (A ⧸ J) B
    exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e)
  apply dim_eq_of_flat
  have hmA : maximalIdeal (A ⧸ J) = (maximalIdeal A).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJm))).symm
  have hmB : maximalIdeal (B ⧸ J.map (algebraMap A B)) =
      (maximalIdeal B).map (Ideal.Quotient.mk (J.map (algebraMap A B))) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm))).symm
  rw [hmA, hmB, Ideal.map_map, ← hm, Ideal.map_map]
  congr 1

theorem UpperTheory.V.CA.c3c :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I) ∧ ∀ (I : Ideal C) (q : Ideal R), I ≤ q.comap (algebraMap C R) → ringKrullDim (R ⧸ q) ≤ dimAt x I := by
  intro C R _ _ _ _ _ x _ hR
  obtain ⟨_, ⟨e⟩, hmap⟩ := cpl_uniq x hR
  haveI := hR.noeth
  haveI : IsNoetherianRing (Cpl x) := isNoetherianRing_of_ringEquiv R e.toRingEquiv
  have hmapI : ∀ I : Ideal C,
      I.map (algebraMap C (Cpl x)) = (I.map (algebraMap C R)).map (e.toRingEquiv : R →+* Cpl x) := by
    intro I
    rw [Ideal.map_map]
    congr 1
    ext c
    simp
  have h1 : x.map (algebraMap C (Cpl x)) =
      (maximalIdeal (Localization.AtPrime x)).map (algebraMap (Localization.AtPrime x) (Cpl x)) := by
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hm : (maximalIdeal (Localization.AtPrime x)).map
      (algebraMap (Localization.AtPrime x) (Cpl x)) = maximalIdeal (Cpl x) := by
    rw [← h1, hmapI, hmap]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.toRingEquiv)
  have key : ∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I := by
    intro I
    unfold dimAt
    rw [← dim_quot_eq_of_flat hm (I.map (algebraMap C (Localization.AtPrime x))), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e.toRingEquiv (hmapI I))
  refine ⟨key, fun I q hq => ?_⟩
  rw [← key I]
  have hle : I.map (algebraMap C R) ≤ q := Ideal.map_le_iff_le_comap.mpr hq
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DAmitsur
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

namespace UpperTheory.V.CA

section Fac

variable {k : ℕ} {F : Type} [Ring F]

private def amJ (x : Fin k → F) (N : ℕ) : AddSubmonoid F :=
  AddSubmonoid.closure {z | ∃ (c : ℤ) (w : FreeMonoid (Fin k)), N ≤ w.length ∧ z = c • FreeMonoid.lift x w}

private def amP (x : Fin k → F) (L : List (ℤ × FreeMonoid (Fin k))) : F :=
  (L.map fun p => 1 + p.1 • FreeMonoid.lift x p.2).prod

private theorem amJ_mono (x : Fin k → F) {a b : ℕ} (h : a ≤ b) : amJ x b ≤ amJ x a :=
  AddSubmonoid.closure_mono fun _ ⟨c, w, hw, e⟩ => ⟨c, w, h.trans hw, e⟩

private theorem amJ_mul (x : Fin k → F) {a b : ℕ} {y z : F} (hy : y ∈ amJ x a) (hz : z ∈ amJ x b) :
    y * z ∈ amJ x (a + b) := by
  induction hy using AddSubmonoid.closure_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | mem u hu =>
    induction hz using AddSubmonoid.closure_induction with
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | mem v hv =>
      obtain ⟨c, w, hw, rfl⟩ := hu
      obtain ⟨c', w', hw', rfl⟩ := hv
      refine AddSubmonoid.subset_closure ⟨c * c', w * w', ?_, ?_⟩
      · rw [FreeMonoid.length_mul]; omega
      · rw [map_mul, smul_mul_smul_comm]

private theorem amJ_neg (x : Fin k → F) {a : ℕ} {y : F} (hy : y ∈ amJ x a) : -y ∈ amJ x a := by
  induction hy using AddSubmonoid.closure_induction with
  | zero => simp
  | add u v _ _ hu hv => rw [neg_add]; exact add_mem hu hv
  | mem u hu =>
    obtain ⟨c, w, hw, rfl⟩ := hu
    exact AddSubmonoid.subset_closure ⟨-c, w, hw, (neg_smul _ _).symm⟩

private theorem amJ_step (x : Fin k → F) {N : ℕ} {d : F} (hd : d ∈ amJ x (N + 1)) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ ∃ e ∈ amJ x (N + 2), amP x L = 1 + d + e := by
  induction hd using AddSubmonoid.closure_induction with
  | zero => exact ⟨[], by simp, 0, zero_mem _, by simp [amP]⟩
  | mem u hu =>
    obtain ⟨c, w, hw, rfl⟩ := hu
    refine ⟨[(c, w)], ?_, 0, zero_mem _, by simp [amP]⟩
    intro p hp h
    rw [List.mem_singleton] at hp
    subst hp
    simp only at h
    rw [h] at hw
    simp [FreeMonoid.length_one] at hw
  | add u v hu hv ihu ihv =>
    obtain ⟨L, hL, e, he, h⟩ := ihu
    obtain ⟨L', hL', e', he', h'⟩ := ihv
    refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p), e + e' + (u + e) * (v + e'), ?_, ?_⟩
    · refine add_mem (add_mem he he') (amJ_mono x (by omega)
        (amJ_mul x (add_mem hu (amJ_mono x (by omega) he)) (add_mem hv (amJ_mono x (by omega) he'))))
    · have : amP x (L ++ L') = amP x L * amP x L' := by simp [amP]
      rw [this, h, h']; noncomm_ring

private theorem amJ_fac (x : Fin k → F) (N : ℕ) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ (∃ q ∈ amJ x 1, amP x L = 1 + q) ∧
      ∃ d ∈ amJ x (N + 1), 1 + ∑ a, x a = amP x L + d := by
  induction N with
  | zero =>
    refine ⟨[], by simp, ⟨0, zero_mem _, by simp [amP]⟩, ∑ a, x a, ?_, by simp [amP]⟩
    exact sum_mem fun a _ => AddSubmonoid.subset_closure ⟨1, FreeMonoid.of a, by simp [FreeMonoid.length_of], by simp⟩
  | succ N ih =>
    obtain ⟨L, hL, ⟨q, hq, h1⟩, d, hd, h2⟩ := ih
    obtain ⟨L', hL', e, he, h3⟩ := amJ_step x hd
    have h4 : amP x (L ++ L') = amP x L * amP x L' := by simp [amP]
    have hde : d + e ∈ amJ x (N + 1) := add_mem hd (amJ_mono x (by omega) he)
    refine ⟨L ++ L', fun p hp => (List.mem_append.1 hp).elim (hL p) (hL' p),
      ⟨q + (d + e) + q * (d + e), ?_, ?_⟩, -(e + q * (d + e)), ?_, ?_⟩
    · exact add_mem (add_mem hq (amJ_mono x (by omega) hde)) (amJ_mono x (by omega) (amJ_mul x hq hde))
    · rw [h4, h1, h3]; noncomm_ring
    · exact amJ_neg x (add_mem he (amJ_mono x (by omega) (amJ_mul x hq hde)))
    · rw [h2, h4, h1, h3]; noncomm_ring

private theorem am_univ (k N : ℕ) :
    ∃ L : List (ℤ × FreeMonoid (Fin k)), (∀ p ∈ L, p.2 ≠ 1) ∧ ∀ (F : Type) [Ring F] (x : Fin k → F),
      (∀ w : FreeMonoid (Fin k), N < w.length → FreeMonoid.lift x w = 0) → 1 + ∑ a, x a = amP x L := by
  obtain ⟨L, hL, -, d, hd, h⟩ := amJ_fac (FreeAlgebra.ι ℤ : Fin k → FreeAlgebra ℤ (Fin k)) N
  refine ⟨L, hL, fun F _ x hx => ?_⟩
  have hw : ∀ w : FreeMonoid (Fin k), FreeAlgebra.lift ℤ x (FreeMonoid.lift (FreeAlgebra.ι ℤ) w) =
      FreeMonoid.lift x w := by
    intro w
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih => simp [ih]
  have h0 : FreeAlgebra.lift ℤ x d = 0 := by
    clear h
    induction hd using AddSubmonoid.closure_induction with
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), hu, hv, add_zero]
    | mem u hu =>
      obtain ⟨c, w, hw', rfl⟩ := hu
      rw [map_zsmul, hw, hx w (by omega), smul_zero]
  have := congrArg (FreeAlgebra.lift ℤ x) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), h0, add_zero, map_one, map_sum, amP, map_list_prod, List.map_map] at this
  simp only [FreeAlgebra.lift_ι_apply] at this
  rw [this, amP]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp, map_add (f := _), map_one, map_zsmul, hw]

end Fac

section Pol

variable {k : ℕ}

private noncomputable def amWt (w : FreeMonoid (Fin k)) : Fin k →₀ ℕ := Multiset.toFinsupp (w.toList : Multiset (Fin k))

private def amGood (n : ℕ) (Q : MvPolynomial (Fin k) (MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ)) : Prop :=
  ∀ β, AddMonoidAlgebra.coeff Q β ∈ MvPolynomial.supported ℤ {v : ℕ × FreeMonoid (Fin k) | 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1} ∧
    (AddMonoidAlgebra.coeff Q β).IsWeightedHomogeneous (fun v => v.1 • amWt v.2) β

private theorem amGood_mon (n : ℕ) (γ : Fin k →₀ ℕ) (P : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ)
    (h1 : P ∈ MvPolynomial.supported ℤ {v : ℕ × FreeMonoid (Fin k) | 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1})
    (h2 : P.IsWeightedHomogeneous (fun v => v.1 • amWt v.2) γ) : amGood n (MvPolynomial.monomial γ P) := by
  intro β
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · exact ⟨h1, h ▸ h2⟩
  · exact ⟨zero_mem _, MvPolynomial.isWeightedHomogeneous_zero _ _ _⟩

private theorem amGood_one (n : ℕ) : amGood (k := k) n 1 :=
  amGood_mon n 0 1 (one_mem _) (MvPolynomial.isWeightedHomogeneous_one _ _)

private theorem amGood_add {n : ℕ} {Q Q'} (h : amGood (k := k) n Q) (h' : amGood n Q') : amGood n (Q + Q') := by
  intro β
  rw [MvPolynomial.coeff_add]
  exact ⟨add_mem (h β).1 (h' β).1, (h β).2.add (h' β).2⟩

private theorem amGood_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → _) (h : ∀ i ∈ s, amGood (k := k) n (f i)) :
    amGood n (∑ i ∈ s, f i) := by
  intro β
  rw [MvPolynomial.coeff_sum]
  exact ⟨sum_mem fun i hi => (h i hi β).1, MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => (h i hi β).2⟩

private theorem amGood_mul {n : ℕ} {Q Q'} (h : amGood (k := k) n Q) (h' : amGood n Q') : amGood n (Q * Q') := by
  intro β
  rw [MvPolynomial.coeff_mul]
  refine ⟨sum_mem fun i hi => mul_mem (h _).1 (h' _).1, MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_⟩
  have hi' : i.1 + i.2 = β := by simpa using hi
  rw [← hi']
  exact (h _).2.mul (h' _).2

private noncomputable def amF (n : ℕ) (p : ℤ × FreeMonoid (Fin k)) :
    MvPolynomial (Fin k) (MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ) :=
  1 + ∑ i ∈ Finset.range n, MvPolynomial.monomial ((i + 1) • amWt p.2)
    (MvPolynomial.C (p.1 ^ (i + 1)) * MvPolynomial.X (i + 1, p.2))

private theorem amGood_F (n : ℕ) (p : ℤ × FreeMonoid (Fin k)) (hp : p.2 ≠ 1) : amGood n (amF n p) := by
  refine amGood_add (amGood_one n) (amGood_sum _ _ fun i hi => amGood_mon n _ _ ?_ ?_)
  · refine mul_mem (Subalgebra.algebraMap_mem _ _) (MvPolynomial.X_mem_supported.2 ⟨by simp, ?_, hp⟩)
    exact Finset.mem_range.1 hi
  · exact (MvPolynomial.isWeightedHomogeneous_X ℤ (fun v : ℕ × FreeMonoid (Fin k) => v.1 • amWt v.2)
      (i + 1, p.2)).C_mul _

private theorem amGood_prod (n : ℕ) (L : List (ℤ × FreeMonoid (Fin k))) (hL : ∀ p ∈ L, p.2 ≠ 1) :
    amGood n (L.map (amF n)).prod := by
  induction L with
  | nil => exact amGood_one n
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons]
    exact amGood_mul (amGood_F n p (hL p (by simp))) (ih fun q hq => hL q (by simp [hq]))

private theorem amWt_degree (w : FreeMonoid (Fin k)) : (amWt w).degree = w.length := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [amWt, FreeMonoid.length_one]
  | of_mul a w ih =>
    have : amWt (FreeMonoid.of a * w) = Finsupp.single a 1 + amWt w := by
      simp only [amWt, FreeMonoid.toList_of_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, map_add (f := _),
        Multiset.toFinsupp_singleton]
    rw [this, map_add (f := _), ih]; simp [FreeMonoid.length_mul, FreeMonoid.length_of]

private theorem am_lift {A E B : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B]
    (π : MvPolynomial (Fin k) A →ₐ[A] B) (x : Fin k → E) (w : FreeMonoid (Fin k)) :
    FreeMonoid.lift (fun a => π (MvPolynomial.X a) ⊗ₜ[A] x a) w =
      π (MvPolynomial.monomial (amWt w) 1) ⊗ₜ[A] FreeMonoid.lift x w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [amWt, Algebra.TensorProduct.one_def]
  | of_mul a w ih =>
    have : amWt (FreeMonoid.of a * w) = Finsupp.single a 1 + amWt w := by
      simp only [amWt, FreeMonoid.toList_of_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, map_add (f := _),
        Multiset.toFinsupp_singleton]
    rw [this, map_mul, map_mul, ih, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of,
      Algebra.TensorProduct.tmul_mul_tmul, ← map_mul, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

private theorem am_one {n : ℕ} {A E B : Type} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B]
    (D : Det n A E) (b : B) (y : E) :
    D.D B (1 + b ⊗ₜ y) = 1 + ∑ i ∈ Finset.range n, algebraMap A B (D.lam (i + 1) y) * b ^ (i + 1) := by
  obtain ⟨h0, -, h, -⟩ := d_chi D y
  have := D.nat A[X] B (Polynomial.aeval b) (1 + X ⊗ₜ y)
  rw [h, map_add (f := _), map_one, Algebra.TensorProduct.map_tmul, aeval_X, AlgHom.id_apply] at this
  rw [this, Finset.sum_range_succ', h0, add_comm]
  simp

end Pol

end UpperTheory.V.CA

theorem UpperTheory.V.CA.d_amitsur :
    ∀ (n k : ℕ) (α : Fin k →₀ ℕ), ∃ P : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ, (∀ v ∈ P.vars, 1 ≤ v.1 ∧ v.1 ≤ n ∧ v.2 ≠ 1) ∧ P.IsWeightedHomogeneous (fun v => v.1 • Multiset.toFinsupp (v.2.toList : Multiset (Fin k))) α ∧ ∀ {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : Fin k → E), AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) α = MvPolynomial.aeval (fun v => D.lam v.1 (FreeMonoid.lift x v.2)) P := by
  intro n k α
  obtain ⟨L, hL, hu⟩ := am_univ k α.degree
  have hg := amGood_prod n L hL α
  refine ⟨_, fun v hv => MvPolynomial.mem_supported.1 hg.1 hv, hg.2, ?_⟩
  intro A E _ _ _ D x
  let I : Ideal (MvPolynomial (Fin k) A) :=
    Ideal.span ((fun s => MvPolynomial.monomial s 1) '' {β : Fin k →₀ ℕ | α.degree < β.degree})
  let π := Ideal.Quotient.mkₐ A I
  let φ : MvPolynomial (ℕ × FreeMonoid (Fin k)) ℤ →+* A :=
    (MvPolynomial.aeval (R := ℤ) (fun v : ℕ × FreeMonoid (Fin k) => D.lam v.1 (FreeMonoid.lift x v.2))).toRingHom
  have h1 := hu ((MvPolynomial (Fin k) A ⧸ I) ⊗[A] E) (fun a => π (MvPolynomial.X a) ⊗ₜ[A] x a) fun w hw => by
    have : π (MvPolynomial.monomial (amWt w) 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨amWt w, by simpa [amWt_degree] using hw, rfl⟩)
    rw [am_lift, this, zero_tmul]
  have h2 : π (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) = π (MvPolynomial.map φ (L.map (amF n)).prod) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← D.nat, map_add (f := _), map_one, Det.gen, map_sum]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [h1, amP, map_list_prod, map_list_prod, map_list_prod, List.map_map, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [am_lift, smul_tmul', am_one, amF, map_add (f := _), map_add (f := _), map_one (MvPolynomial.map φ), map_one π, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_zsmul, ← map_pow, ← π.commutes, ← map_mul]
    congr 1
    rw [MvPolynomial.map_monomial, _root_.smul_pow, MvPolynomial.monomial_pow, MvPolynomial.smul_monomial,
      MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial]
    congr 1
    simp [φ, mul_comm]
  have h3 := MvPolynomial.mem_ideal_span_monomial_image.1 (Ideal.Quotient.eq.1 h2)
  have h4 : AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x) -
      MvPolynomial.map φ (L.map (amF n)).prod) α = 0 := by
    by_contra h
    obtain ⟨β, hβ, hle⟩ := h3 α (MvPolynomial.mem_support_iff.2 h)
    exact absurd (Finsupp.degree_mono hle) (not_le.2 hβ)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, MvPolynomial.coeff_map] at h4
  exact h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightSpaceFinite
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.c3a :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → Module.Flat C R ∧ (∀ p : Ideal C, p.IsPrime → p ≤ x → ∃ q : Ideal R, q.IsPrime ∧ q.comap (algebraMap C R) = p) ∧ (∀ q : Ideal R, q.IsPrime → q.comap (algebraMap C R) ≤ x) ∧ (∀ q ∈ minimalPrimes R, q.comap (algebraMap C R) ∈ minimalPrimes C) ∧ ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes, q.comap (algebraMap C R) ∈ I.minimalPrimes := by
  intro C R _ _ _ _ _ x _ h
  obtain ⟨-, ⟨e⟩, -⟩ := UpperTheory.V.CA.cpl_uniq x h
  have hflat : Module.Flat C R := by
    have h1 : Module.Flat (Localization.AtPrime x) (Cpl x) := inferInstance
    have h2 : Module.Flat C (Localization.AtPrime x) := IsLocalization.flat _ x.primeCompl
    have h3 : Module.Flat C (Cpl x) := Module.Flat.trans C (Localization.AtPrime x) (Cpl x)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hx : (maximalIdeal R).comap (algebraMap C R) = x := by simpa using h.comap_pow 1
  have gd : ∀ (p : Ideal C) (q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q.comap (algebraMap C R) →
      ∃ Q : Ideal R, Q ≤ q ∧ Q.IsPrime ∧ Q.comap (algebraMap C R) = p := by
    intro p q hp hq hle
    haveI : q.LiesOver (q.comap (algebraMap C R)) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le q hle
    exact ⟨Q, hQ, hQp, hQo.over.symm⟩
  have hmin : ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes,
      q.comap (algebraMap C R) ∈ I.minimalPrimes := by
    intro I q hq
    haveI : q.IsPrime := hq.1.1
    refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hq.1.2⟩, ?_⟩
    rintro p ⟨hp, hIp⟩ hle
    obtain ⟨Q, hQ, hQp, hQo⟩ := gd p q hp this hle
    have : q ≤ Q := hq.2 ⟨hQp, Ideal.map_le_iff_le_comap.2 (hQo ▸ hIp)⟩ hQ
    rw [← hQo]
    exact Ideal.comap_mono this
  refine ⟨hflat, ?_, ?_, ?_, hmin⟩
  · intro p hp hle
    obtain ⟨Q, -, hQp, hQo⟩ := gd p (maximalIdeal R) hp inferInstance (hx.symm ▸ hle)
    exact ⟨Q, hQp, hQo⟩
  · intro q hq
    rw [← hx]
    exact Ideal.comap_mono (le_maximalIdeal hq.ne_top)
  · intro q hq
    apply hmin ⊥ q
    rw [Ideal.map_bot]
    exact hq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjDim
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.inj_dim :
    ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] (d : ℕ), ringKrullDim A = d → ringKrullDim B = d → Function.Injective (algebraMap A B) := by
  intro A B _ _ _ _ _ d hA hB
  by_contra hni
  obtain ⟨r, hr, hr0⟩ : ∃ r : A, algebraMap A B r = 0 ∧ r ≠ 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push_neg at hni
    exact hni
  have hrz : r ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hr0
  let g : (A ⧸ Ideal.span {r}) →+* B := Ideal.Quotient.lift (Ideal.span {r}) (algebraMap A B) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hr, mul_zero])
  letI : Algebra (A ⧸ Ideal.span {r}) B := g.toAlgebra
  haveI : Algebra.IsIntegral (A ⧸ Ideal.span {r}) B := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact hpb
  have h1 : ringKrullDim B ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    Order.krullDim_le_of_strictMono
      (fun P => (⟨Ideal.comap (algebraMap (A ⧸ Ideal.span {r}) B) P.asIdeal, inferInstance⟩ :
        PrimeSpectrum _))
      (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hrz
  rw [hA] at h2
  rw [hB] at h1
  have h3 : ((d : WithBot ℕ∞) + 1) ≤ d := le_trans (add_le_add_left h1 1) h2
  norm_cast at h3
  omega
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem sop_mod (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (J : Ideal S)
    (hle : J ≤ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧ ringKrullDim (S ⧸ J) = n ∧
      maximalIdeal S ≤ (Ideal.span (Set.range x) ⊔ J).radical := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ J))
  choose g hg using hsurj
  have hrad : maximalIdeal (S ⧸ J) ≤ (Ideal.span (s : Set (S ⧸ J))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro J ⟨hJ, hJ'⟩
    exact hs.2 ⟨hJ', hJ⟩ (le_maximalIdeal hJ'.ne_top)
  refine ⟨s.card, fun i => g (s.equivFin.symm i), fun i => ?_, ?_, ?_⟩
  · have h1 : π (g (s.equivFin.symm i)) ∈ maximalIdeal (S ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (s.equivFin.symm i).2)
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro y hy
    obtain ⟨N, hN⟩ := hrad (map_nonunit π y hy)
    have h2 : Ideal.span (s : Set (S ⧸ J)) ≤
        (Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π := by
      rw [Ideal.span_le]
      intro y hy
      rw [← hg y]
      refine Ideal.mem_map_of_mem π (Ideal.subset_span ⟨s.equivFin ⟨y, hy⟩, ?_⟩)
      simp
    refine ⟨N, ?_⟩
    have h3 : y ^ N ∈ ((Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π).comap π := by
      rw [Ideal.mem_comap, map_pow]
      exact h2 hN
    rwa [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker] at h3

private theorem inj_of_finite {A B : Type} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CommRing B] (φ : A →+* B)
    (h : φ.Finite) (d : ℕ) (hA : ringKrullDim A = d) (hB : ringKrullDim B = d) :
    Function.Injective φ := by
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h
  exact inj_dim A B d hA hB

private theorem nn_field (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] [IsLocalRing R]
    (h : IsCL k R) : ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d := by
  haveI := h.noeth
  obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R ⊥ bot_le
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]; infer_instance
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps k R h (Fin d) x hx
    (hrad.trans (Ideal.radical_mono (sup_le_sup_left bot_le _)))
  have hR : ringKrullDim R = d := by
    rw [← hd]; exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm
  exact ⟨d, φ, inj_of_finite φ.toRingHom hfin d (cl_cm.2 k d).2 hR, hfin, hloc, hR⟩

private theorem isCL_field (O k R : Type) [CommRing O] [Field k] [CommRing R] [IsLocalRing R]
    [Algebra O k] [Algebra O R] [Algebra k R] [IsScalarTower O k R] (h : IsCL O R) : IsCL k R := by
  have := h.res_fin
  exact ⟨h.noeth, h.complete, inferInstance,
    Module.Finite.of_restrictScalars_finite O k (ResidueField R)⟩

theorem UpperTheory.V.CA.cl_nn :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] [IsDomain R], IsCL O R → (Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) O →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = (d + 1 : ℕ)) ∧ (¬ Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) (ResidueField O) →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d) := by
  intro O _ _ _ _ R _ _ _ _ h
  haveI := h.noeth
  haveI := h.isLocalHom
  refine ⟨fun hinj => ?_, fun hninj => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have ha : algebraMap O R ϖ ∈ maximalIdeal R := map_nonunit _ _ hϖ.not_isUnit
    have ha0 : algebraMap O R ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R (Ideal.span {algebraMap O R ϖ})
      ((Ideal.span_singleton_le_iff_mem _).2 ha)
    obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R h (Fin d) x hx
      (by rwa [hm, Ideal.map_span, Set.image_singleton])
    have hR : ringKrullDim R = (d + 1 : ℕ) := by
      rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ha0) ha, hd]
      rfl
    exact ⟨d, φ, inj_of_finite φ.toRingHom hfin (d + 1) (cl_cm.1 O d).2 hR, hfin, hloc, hR⟩
  · have hk0 : RingHom.ker (algebraMap O R) ≠ ⊥ := fun e =>
      hninj ((RingHom.injective_iff_ker_eq_bot _).2 e)
    have hk : RingHom.ker (algebraMap O R) = maximalIdeal O :=
      eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hk0)
    let ψ : ResidueField O →+* R := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R)
      (fun a ha => by rwa [← hk] at ha)
    letI : Algebra (ResidueField O) R := ψ.toAlgebra
    haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h' : IsCL (ResidueField O) R := isCL_field O (ResidueField O) R h
    obtain ⟨d, φ, h1, h2, h3, h4⟩ := nn_field (ResidueField O) R h'
    exact ⟨d, φ.restrictScalars O, h1, h2, ⟨fun a ha => h3.1 a ha⟩, h4⟩
end
