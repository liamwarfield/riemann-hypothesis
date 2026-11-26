module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardProperSubfieldElementsLt
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.SubfieldCount

theorem sum_bound {g : ℕ} (hg : 5 ≤ g) (m : ℕ) :
    4 * (∑ e ∈ Finset.range m, (g ^ (e + 1) - 1)) + 4 * m + 5 ≤ 5 * g ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < g ^ (m + 1) := pow_pos (by omega) _
    have h2 : 5 * g ^ m ≤ g ^ (m + 1) := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ hg
    omega

theorem five_mul_le {g : ℕ} (hg : 5 ≤ g) (m : ℕ) : 5 * (m + 1) ≤ g ^ (m + 1) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    have h2 : g ^ (m + 1) * 5 ≤ g ^ (m + 1 + 1) := by
      rw [pow_succ g (m + 1)]; exact Nat.mul_le_mul_left _ hg
    omega

theorem num_bound {g : ℕ} (hg : 5 ≤ g) {d : ℕ} (hd : 0 < d) :
    2 * d * (∑ e ∈ Finset.range (d / 2), (g ^ (e + 1) - 1)) < g ^ d - 1 := by
  have key : ∀ m : ℕ, 4 * (m + 1) * (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) + 1
      < g ^ (2 * (m + 1)) := by
    intro m
    have h1 := sum_bound hg (m + 1)
    have h2 := five_mul_le hg m
    rw [two_mul (m + 1), pow_add]
    generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
    generalize g ^ (m + 1) = x at *
    have h3 := Nat.mul_le_mul_left (m + 1) h1
    have h4 := Nat.mul_le_mul_right x h2
    nlinarith
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
  · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h := key m
    rw [show 2 * (m + 1) / 2 = m + 1 by omega, show 2 * (2 * (m + 1)) = 4 * (m + 1) by ring]
    omega
  · rcases m with _ | m
    · simp; omega
    · have h := key m
      rw [show (2 * (m + 1) + 1) / 2 = m + 1 by omega, pow_succ g (2 * (m + 1))]
      generalize (∑ e ∈ Finset.range (m + 1), (g ^ (e + 1) - 1)) = T at *
      generalize g ^ (2 * (m + 1)) = x at *
      have h4 := Nat.mul_le_mul_left x hg
      apply Nat.lt_sub_of_add_lt
      nlinarith [Nat.zero_le (m * T), Nat.zero_le T]

theorem natDegree_dvd_iff {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (n : ℕ) :
    (minpoly (ZMod g) z).natDegree ∣ n ↔ z ^ (g ^ n) = z := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  rw [(minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff,
    Nat.card_zmod]
  simp [sub_eq_zero]

end GlobalTheory.GLm.SubfieldCount

namespace GlobalTheory.GLm
open SubfieldCount

theorem card_proper_subfield_elements_lt : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 5 ≤ g → 0 < d →
    2 * d * Nat.card {z : Formalism.CyclotomicNorms.Fbar g // z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} < g ^ d - 1 := by
  intro g _ d hg hd
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) (num_bound hg hd)
  let F : Finset (Formalism.CyclotomicNorms.Fbar g) := (Finset.range (d / 2)).biUnion fun e =>
    (nthRoots (g ^ (e + 1) - 1) (1 : Formalism.CyclotomicNorms.Fbar g)).toFinset
  have hsub : {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} ⊆ (F : Set _) := by
    rintro z ⟨h0, hz, hne⟩
    have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
    have hpos := minpoly.natDegree_pos hx
    have h1 := (natDegree_dvd_iff z _).1 dvd_rfl
    obtain ⟨k, hk⟩ := (natDegree_dvd_iff z d).2 hz
    obtain ⟨e, he⟩ : ∃ e, (minpoly (ZMod g) z).natDegree = e + 1 :=
      ⟨(minpoly (ZMod g) z).natDegree - 1, by omega⟩
    rw [he] at hk h1 hne
    have hk2 : 2 ≤ k := by
      rcases k with _ | _ | k
      · omega
      · omega
      · omega
    have hle : (e + 1) * 2 ≤ d := hk ▸ Nat.mul_le_mul_left _ hk2
    have hp : 1 < g ^ (e + 1) := Nat.one_lt_pow (by omega) (by omega)
    simp only [F, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.mem_coe,
      Multiset.mem_toFinset]
    refine ⟨e, by simp only [Set.mem_Iio]; omega, ?_⟩
    rw [mem_nthRoots (by omega)]
    apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel hp.le, h1]
  calc _ = Set.ncard {z : Formalism.CyclotomicNorms.Fbar g | z ≠ 0 ∧ z ^ (g ^ d) = z ∧
      (minpoly (ZMod g) z).natDegree ≠ d} := rfl
    _ ≤ (F : Set _).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ _ := Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ =>
        (Multiset.toFinset_card_le _).trans (card_nthRoots _ _))

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIrreducibleCharpolyMemRootsBar
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem exists_irreducible_charpoly_mem_rootsBar (g : ℕ) [Fact g.Prime] (d : ℕ)
    (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ≠ 0) (hd : (minpoly (ZMod g) z).natDegree = d) :
    ∃ y : Gn g d, Irreducible (y : Mt g d).charpoly ∧
      z ∈ Formalism.CyclotomicNorms.rootsBar (y : Mt g d).charpoly := by
  subst hd
  have hi : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  let pb := IntermediateField.adjoin.powerBasis hi
  let M : Mt g (minpoly (ZMod g) z).natDegree := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = minpoly (ZMod g) z := by
    have h := charpoly_leftMulMatrix pb
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h
    exact h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (minpoly.coeff_zero_ne_zero hi hz)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, ?_, ?_⟩
  · change Irreducible M.charpoly
    rw [hM]
    exact minpoly.irreducible hi
  · change z ∈ Formalism.CyclotomicNorms.rootsBar M.charpoly
    rw [hM, Formalism.CyclotomicNorms.rootsBar, mem_roots_map (minpoly.ne_zero hi), ← aeval_def]
    exact minpoly.aeval _ _

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeCardMulCardSupport
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem norm_unitsChar_apply {C : Type} [CommGroup C] [Fintype C] (θ : C →* ℂˣ) (z : C) :
    ‖(θ z : ℂ)‖ = 1 := by
  have h : (θ z : ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

theorem sum_unitsChar_mul_inv {C : Type} [CommGroup C] [Fintype C] (θ η : C →* ℂˣ) :
    ∑ z : C, (θ z : ℂ) * (η z⁻¹ : ℂ) = if θ = η then (Fintype.card C : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have : ∀ z : C, (θ z : ℂ) * (θ z⁻¹ : ℂ) = 1 := by
      intro z
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    simp only [this]
    simp
  · have hne : (Units.coeHom ℂ).comp (θ * η⁻¹) ≠ 1 := by
      intro h1
      apply h
      ext z
      have h2 := DFunLike.congr_fun h1 z
      have h3 : θ z * (η z)⁻¹ = 1 := by
        apply Units.ext
        simpa using h2
      rw [mul_inv_eq_one] at h3
      rw [h3]
    have := sum_hom_units_eq_zero _ hne
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp

theorem card_le_card_mul_card_support :
    ∀ (C : Type) [CommGroup C] [Fintype C] (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ), (∃ z : C, ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0) → Fintype.card C ≤ S.card * (Finset.univ.filter fun z : C => ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card := by
  intro C _ _ S c hz
  obtain ⟨z₁, hz₁⟩ := hz
  set f : C → ℂ := fun z => ∑ θ ∈ S, c θ * (θ z : ℂ) with hf
  set T : Finset C := Finset.univ.filter fun z : C => f z ≠ 0 with hT
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_max_image Finset.univ (fun z => ‖f z‖) ⟨z₁, Finset.mem_univ _⟩
  have hM : 0 < ‖f z₀‖ := lt_of_lt_of_le (norm_pos_iff.mpr hz₁) (hz₀ z₁ (Finset.mem_univ _))
  have hinv : ∀ η ∈ S, (Fintype.card C : ℂ) * c η = ∑ z ∈ T, f z * (η z⁻¹ : ℂ) := by
    intro η hη
    have h1 : ∑ z ∈ T, f z * (η z⁻¹ : ℂ) = ∑ z : C, f z * (η z⁻¹ : ℂ) := by
      rw [hT]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => ?_
      have : f z = 0 := by simpa using hz
      rw [this, zero_mul]
    rw [h1]
    simp only [hf, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_unitsChar_mul_inv, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' S η, if_pos hη, mul_comm]
  have hc : ∀ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ ≤ T.card * ‖f z₀‖ := by
    intro η hη
    have h1 : ‖(Fintype.card C : ℂ) * c η‖ = (Fintype.card C : ℝ) * ‖c η‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h1, hinv η hη]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
    exact hz₀ z (Finset.mem_univ _)
  have hf0 : ‖f z₀‖ ≤ ∑ η ∈ S, ‖c η‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
  have hfin : (Fintype.card C : ℝ) * ‖f z₀‖ ≤ ((S.card : ℝ) * T.card) * ‖f z₀‖ := by
    calc (Fintype.card C : ℝ) * ‖f z₀‖ ≤ (Fintype.card C : ℝ) * ∑ η ∈ S, ‖c η‖ :=
          mul_le_mul_of_nonneg_left hf0 (Nat.cast_nonneg _)
      _ = ∑ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ := Finset.mul_sum _ _ _
      _ ≤ S.card • ((T.card : ℝ) * ‖f z₀‖) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = _ := by rw [nsmul_eq_mul, mul_assoc]
  have := le_of_mul_le_mul_right hfin hM
  exact_mod_cast this

end GlobalTheory.GLm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLn
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.LabelUnique

theorem pow_mod_eq {M : Type*} [Monoid M] {u : M} {m : ℕ} (hu : u ^ m = 1) (n : ℕ) :
    u ^ (n % m) = u ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hu, one_pow, mul_one]

def chr (m : ℕ) [NeZero m] (u : ℂˣ) (hu : u ^ m = 1) : Multiplicative (ZMod m) →* ℂˣ where
  toFun k := u ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, pow_mod_eq hu, pow_add]

theorem ne_zero_of_pow {ζ : ℂ} {m : ℕ} (hm : m ≠ 0) (h : ζ ^ m = 1) : ζ ≠ 0 := by
  rintro rfl; rw [zero_pow hm] at h; exact zero_ne_one h

theorem exists_eq_of_sum_eq {m d : ℕ} [NeZero m] (hm : 1 < m) (ζ ζ' : ℕ → ℂ)
    (hu : ∀ i, ζ i ^ m = 1) (hu' : ∀ i, ζ' i ^ m = 1) (hd : 0 < d) (B : Finset (ZMod m))
    (hB : 2 * d * B.card < m)
    (h : ∀ k : ZMod m, k ∉ B → ∑ i ∈ Finset.range d, ζ i ^ k.val = ∑ i ∈ Finset.range d, ζ' i ^ k.val) :
    ∃ i < d, ζ' 0 = ζ i := by
  have hm0 : m ≠ 0 := by omega
  haveI : Fact (1 < m) := ⟨hm⟩
  let u : ℕ → ℂˣ := fun i => Units.mk0 (ζ i) (ne_zero_of_pow hm0 (hu i))
  let u' : ℕ → ℂˣ := fun i => Units.mk0 (ζ' i) (ne_zero_of_pow hm0 (hu' i))
  have huu : ∀ i, u i ^ m = 1 := fun i => Units.ext (by simp [u, hu i])
  have huu' : ∀ i, u' i ^ m = 1 := fun i => Units.ext (by simp [u', hu' i])
  let θ : ℕ → (Multiplicative (ZMod m) →* ℂˣ) := fun i => chr m (u i) (huu i)
  let θ' : ℕ → (Multiplicative (ZMod m) →* ℂˣ) := fun i => chr m (u' i) (huu' i)
  have hθ : ∀ i z, ((θ i z : ℂˣ) : ℂ) = ζ i ^ (Multiplicative.toAdd z).val := fun i z => by
    simp [θ, chr, u]
  have hθ' : ∀ i z, ((θ' i z : ℂˣ) : ℂ) = ζ' i ^ (Multiplicative.toAdd z).val := fun i z => by
    simp [θ', chr, u']
  let S := (Finset.range d).image θ ∪ (Finset.range d).image θ'
  let c : (Multiplicative (ZMod m) →* ℂˣ) → ℂ := fun φ =>
    (((Finset.range d).filter (fun i => θ i = φ)).card : ℂ) -
      (((Finset.range d).filter (fun i => θ' i = φ)).card : ℂ)
  have fib : ∀ (t : ℕ → (Multiplicative (ZMod m) →* ℂˣ)), (∀ i ∈ Finset.range d, t i ∈ S) → ∀ z,
      ∑ φ ∈ S, (((Finset.range d).filter (fun i => t i = φ)).card : ℂ) * (φ z : ℂ) =
        ∑ i ∈ Finset.range d, ((t i z : ℂˣ) : ℂ) := by
    intro t ht z
    rw [← Finset.sum_fiberwise_of_maps_to ht]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const,
      nsmul_eq_mul]
  have hsum : ∀ z, ∑ φ ∈ S, c φ * (φ z : ℂ) =
      ∑ i ∈ Finset.range d, ζ i ^ (Multiplicative.toAdd z).val -
        ∑ i ∈ Finset.range d, ζ' i ^ (Multiplicative.toAdd z).val := by
    intro z
    simp only [c, sub_mul, Finset.sum_sub_distrib]
    rw [fib θ (fun i hi => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)) z,
      fib θ' (fun i hi => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)) z]
    simp only [hθ, hθ']
  have hS : S.card ≤ 2 * d := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := (Finset.card_image_le (s := Finset.range d) (f := θ))
    have h2 := (Finset.card_image_le (s := Finset.range d) (f := θ'))
    simp only [Finset.card_range] at h1 h2
    omega
  have hzero : ∀ z, ∑ φ ∈ S, c φ * (φ z : ℂ) = 0 := by
    by_contra hne
    push_neg at hne
    have key := GlobalTheory.GLm.card_le_card_mul_card_support (Multiplicative (ZMod m)) S c hne
    have hcard : Fintype.card (Multiplicative (ZMod m)) = m := by
      simp [ZMod.card]
    have hsupp : (Finset.univ.filter fun z : Multiplicative (ZMod m) =>
        ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card ≤ B.card := by
      refine Finset.card_le_card_of_injOn (fun z => Multiplicative.toAdd z) ?_ ?_
      · intro z hz
        have hz' := (Finset.mem_filter.1 hz).2
        by_contra hB'
        apply hz'
        rw [hsum z, h _ hB', sub_self]
      · intro a _ b _ hab; exact hab
    rw [hcard] at key
    have : S.card * (Finset.univ.filter fun z : Multiplicative (ZMod m) =>
        ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card ≤ 2 * d * B.card := Nat.mul_le_mul hS hsupp
    omega
  have hinj : Function.Injective (fun φ : Multiplicative (ZMod m) →* ℂˣ => (Units.coeHom ℂ).comp φ) := by
    intro φ ψ hφψ
    exact MonoidHom.ext fun z => Units.ext (DFunLike.congr_fun hφψ z)
  have hli := (linearIndependent_monoidHom (Multiplicative (ZMod m)) ℂ).comp _ hinj
  rw [linearIndependent_iff'] at hli
  have hmem : θ' 0 ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simpa using hd))
  have hc0 := hli S c (by
    funext z
    rw [Finset.sum_apply]
    simpa [smul_eq_mul] using hzero z) (θ' 0) hmem
  simp only [c, sub_eq_zero, Nat.cast_inj] at hc0
  have hpos : 0 < ((Finset.range d).filter (fun i => θ' i = θ' 0)).card :=
    Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨by simpa using hd, rfl⟩⟩
  rw [← hc0] at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.1 hpos
  obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
  refine ⟨i, by simpa using hi1, ?_⟩
  have := congrArg (fun φ : Multiplicative (ZMod m) →* ℂˣ => ((φ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ)) hi2
  simp only [hθ, hθ', toAdd_ofAdd, ZMod.val_one, pow_one] at this
  exact this.symm

end GlobalTheory.GLq.LabelUnique

namespace GlobalTheory.GLq.LabelUnique

variable {g : ℕ} [Fact g.Prime]

theorem aeval_eq_zero_of_mem {P : (ZMod g)[X]} (hP : P ≠ 0) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) : aeval x P = 0 := by
  unfold Formalism.CyclotomicNorms.rootsBar at hx
  rw [mem_roots (Polynomial.map_ne_zero hP), IsRoot, eval_map] at hx
  rw [aeval_def]; exact hx

theorem minpoly_eq_of_mem {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) : minpoly (ZMod g) x = P :=
  (minpoly.eq_of_irreducible_of_monic hP.2.1 (aeval_eq_zero_of_mem hP.1.ne_zero hx) hP.1).symm

theorem ne_zero_of_mem {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) : x ≠ 0 := by
  rintro rfl
  have h := minpoly_eq_of_mem hP hx
  rw [minpoly.zero] at h
  exact hP.2.2.1 (by rw [← h]; simp)

theorem exists_mem {d : ℕ} (hd : 0 < d) {P : (ZMod g)[X]} (hP : IsPrimeLab d P) :
    ∃ x, x ∈ Formalism.CyclotomicNorms.rootsBar P := by
  have hdeg : (P.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g))).degree ≠ 0 := by
    rw [degree_map]
    exact (natDegree_pos_iff_degree_pos.mp (by rw [hP.2.2.2]; exact hd)).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨x, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  exact (mem_roots (Polynomial.map_ne_zero hP.1.ne_zero)).2 hx

theorem pow_sub_one_eq_one {d : ℕ} {P : (ZMod g)[X]} (hP : IsPrimeLab d P) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : x ∈ Formalism.CyclotomicNorms.rootsBar P) : x ^ (g ^ d - 1) = 1 := by
  have h0 := ne_zero_of_mem hP hx
  have hfix : x ^ (g ^ d) = x :=
    (GlobalTheory.GLm.SubfieldCount.natDegree_dvd_iff x d).1 (by rw [minpoly_eq_of_mem hP hx, hP.2.2.2])
  have hpos : 0 < g ^ d := pow_pos (Fact.out : g.Prime).pos d
  apply mul_right_cancel₀ h0
  rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul, hfix]

theorem aeval_pow_eq_zero {P : (ZMod g)[X]} {x : Formalism.CyclotomicNorms.Fbar g} (hx : aeval x P = 0) (i : ℕ) :
    aeval (x ^ (g ^ i)) P = 0 := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ, pow_mul, ← expand_aeval, ZMod.expand_card, map_pow, ih, zero_pow]
    exact (Fact.out : g.Prime).ne_zero

theorem thetaOf_gen_pow (L : LabelDatum g) (d : ℕ) (hd : 0 < d) (w : Formalism.CyclotomicNorms.Fbar g)
    (hw : L.teich w ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d w (L.gen d ^ n) = L.teich w ^ n := by
  have hex : ∃ n' : ℕ, L.gen d ^ n = L.gen d ^ n' := ⟨n, rfl⟩
  unfold thetaOf
  rw [dite_eq_left hex]
  have hs := hex.choose_spec
  have h1 : 1 < g ^ d := Nat.one_lt_pow hd.ne' (Fact.out : g.Prime).one_lt
  have hfo : IsOfFinOrder (L.gen d) := orderOf_pos_iff.mp (by rw [L.gen_order d hd]; omega)
  rw [hfo.pow_eq_pow_iff_modEq, L.gen_order d hd] at hs
  rw [← pow_mod_eq hw n, ← pow_mod_eq hw hex.choose]
  exact congrArg _ hs.symm

theorem label_eq (L : LabelDatum g) (hg : 5 ≤ g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : Gn g d → ℂ)
    (h : IsCuspOf L P χ) (h' : IsCuspOf L P' χ) : P = P' := by
  obtain ⟨hPl, hc, hval⟩ := h
  obtain ⟨hPl', -, hval'⟩ := h'
  have hd : 0 < d := hc.1
  set m := g ^ d - 1 with hmdef
  have hgd : 5 ≤ g ^ d := le_trans hg (Nat.le_self_pow hd.ne' g)
  have hm : 1 < m := by omega
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨x, hx⟩ := exists_mem hd hPl
  obtain ⟨x', hx'⟩ := exists_mem hd hPl'
  have hx1 := pow_sub_one_eq_one hPl hx
  have hx1' := pow_sub_one_eq_one hPl' hx'
  let γ := L.gen d
  have hord : orderOf γ = m := L.gen_order d hd
  have hγm : γ ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hfo : IsOfFinOrder γ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hγ0 : γ ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at hγm; exact zero_ne_one hγm
  have hteich : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ m = 1 → ∀ i, L.teich (w ^ (g ^ i)) ^ m = 1 := by
    intro w hw i
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hw, one_pow, map_one]

  let B : Finset (ZMod m) := Finset.univ.filter fun k => (minpoly (ZMod g) (γ ^ k.val)).natDegree ≠ d
  have hB : 2 * d * B.card < m := by
    refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) (GlobalTheory.GLm.card_proper_subfield_elements_lt g d hg hd)
    let S0 : Set (Formalism.CyclotomicNorms.Fbar g) := {z | z ≠ 0 ∧ z ^ (g ^ d) = z ∧ (minpoly (ZMod g) z).natDegree ≠ d}
    have hfin : S0.Finite := by
      refine (nthRoots m (1 : Formalism.CyclotomicNorms.Fbar g)).toFinset.finite_toSet.subset ?_
      rintro z ⟨hz0, hz, -⟩
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_nthRoots (by omega)]
      apply mul_right_cancel₀ hz0
      rw [← pow_succ, one_mul, hmdef, Nat.sub_add_cancel (by omega), hz]
    have hinj : Set.InjOn (fun k : ZMod m => γ ^ k.val) B := by
      intro a _ b _ hab
      have hab' : γ ^ a.val = γ ^ b.val := hab
      have := (hfo.pow_eq_pow_iff_modEq.1 hab')
      rw [hord] at this
      apply ZMod.val_injective
      have ha := ZMod.val_lt a
      have hb := ZMod.val_lt b
      unfold Nat.ModEq at this
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    calc B.card = (B.image fun k : ZMod m => γ ^ k.val).card := (Finset.card_image_of_injOn hinj).symm
      _ = Set.ncard ((B.image fun k : ZMod m => γ ^ k.val : Finset _) : Set (Formalism.CyclotomicNorms.Fbar g)) :=
          (Set.ncard_coe_finset _).symm
      _ ≤ S0.ncard := by
          refine Set.ncard_le_ncard ?_ hfin
          intro z hz
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
          obtain ⟨k, hk, rfl⟩ := hz
          refine ⟨pow_ne_zero _ hγ0, ?_, (Finset.mem_filter.1 hk).2⟩
          rw [← pow_mul, mul_comm, pow_mul, show g ^ d = m + 1 by omega, pow_succ, hγm, one_mul]
      _ = _ := rfl
  have hsums : ∀ k : ZMod m, k ∉ B →
      ∑ i ∈ Finset.range d, L.teich (x ^ (g ^ i)) ^ k.val =
        ∑ i ∈ Finset.range d, L.teich (x' ^ (g ^ i)) ^ k.val := by
    intro k hk
    have hdeg : (minpoly (ZMod g) (γ ^ k.val)).natDegree = d := by
      by_contra hne; exact hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
    obtain ⟨y, hy, hz⟩ := GlobalTheory.GLm.exists_irreducible_charpoly_mem_rootsBar g d (γ ^ k.val)
      (pow_ne_zero _ hγ0) hdeg
    have e1 := hval x hx y hy _ hz
    have e2 := hval' x' hx' y hy _ hz
    rw [e1] at e2
    have hsgn : ((-1 : ℂ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have e3 := mul_left_cancel₀ hsgn e2
    have conv : ∀ w : Formalism.CyclotomicNorms.Fbar g, w ^ m = 1 → ∀ i,
        thetaOf L d w ((γ ^ k.val) ^ (g ^ i)) = L.teich (w ^ (g ^ i)) ^ k.val := by
      intro w hw i
      have hw' : L.teich w ^ m = 1 := by simpa using hteich w hw 0
      rw [← pow_mul, thetaOf_gen_pow L d hd w hw', map_pow, ← pow_mul, mul_comm]
    simp only [conv x hx1, conv x' hx1'] at e3
    exact e3
  obtain ⟨i, hi, hieq⟩ := exists_eq_of_sum_eq hm (fun i => L.teich (x ^ (g ^ i)))
    (fun i => L.teich (x' ^ (g ^ i))) (hteich x hx1) (hteich x' hx1') hd B hB hsums
  simp only [pow_zero, pow_one] at hieq
  have hxe : x' = x ^ (g ^ i) :=
    L.teich_inj _ _ (ne_zero_of_mem hPl' hx') (pow_ne_zero _ (ne_zero_of_mem hPl hx)) hieq
  have h1 : aeval x' P = 0 := by
    rw [hxe]; exact aeval_pow_eq_zero (aeval_eq_zero_of_mem hPl.1.ne_zero hx) i
  have h2 := minpoly.eq_of_irreducible_of_monic hPl.2.1 h1 hPl.1
  rw [h2, minpoly_eq_of_mem hPl' hx']

end GlobalTheory.GLq.LabelUnique

namespace GlobalTheory.GLq

theorem isCuspOf_label_unique : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → ∀ (d : ℕ)
    (P P' : (ZMod g)[X]) (χ χ' : Gn g d → ℂ), IsCuspOf L P χ →
      (IsCuspOf L P' χ → P = P') ∧ (Green → IsCuspOf L P χ' → χ = χ') := by
  intro g _ L hg d P P' χ χ' h
  refine ⟨fun h' => LabelUnique.label_eq L hg d P P' χ h h', fun hG h' => ?_⟩
  obtain ⟨τ, hτ, -, hall⟩ := hG g L d h.2.1.1
  obtain ⟨Q, hQ, rfl⟩ := hall χ h.2.1
  obtain ⟨Q', hQ', rfl⟩ := hall χ' h'.2.1
  have e1 := LabelUnique.label_eq L hg d P Q _ h (hτ Q hQ).1
  have e2 := LabelUnique.label_eq L hg d P Q' _ h' (hτ Q' hQ').1
  rw [← e1, ← e2]

end GlobalTheory.GLq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharacterLabelUniqueGLnStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacter_label_unique_GLn : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → ∀ (d : ℕ) (P P' : (ZMod g)[X]) (χ χ' : Gn g d → ℂ), IsCuspOf L P χ → (IsCuspOf L P' χ → P = P') ∧ (Green → IsCuspOf L P χ' → χ = χ') := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique | exact GlobalTheory.GLq.isCuspOf_label_unique | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique <;> assumption)
end
