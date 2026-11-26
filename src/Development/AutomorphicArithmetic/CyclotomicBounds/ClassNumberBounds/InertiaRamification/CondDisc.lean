module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Filtration
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private lemma filt_gcd_eq {t : ℕ} (ht : t ≤ N.factorization l) :
    Nat.gcd N (ordCompl[l] N * l ^ t) = ordCompl[l] N * l ^ t := by
  apply Nat.gcd_eq_right
  calc ordCompl[l] N * l ^ t ∣ ordCompl[l] N * l ^ N.factorization l :=
        Nat.mul_dvd_mul_left _ (pow_dvd_pow _ ht)
    _ = N := by rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self N l

private lemma filt_mem_ker_iff {d e : ℕ} (hd : d ∣ N) (he : N = e * d) (g : (ZMod N)ˣ) :
    g ∈ (ZMod.unitsMap hd).ker ↔ addOrderOf ((g : ZMod N) - 1) ∣ e := by
  have he0 : e ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by simpa using he)
  have h1 : g ∈ (ZMod.unitsMap hd).ker ↔ ZMod.castHom hd (ZMod d) ((g : ZMod N) - 1) = 0 := by
    rw [MonoidHom.mem_ker, Units.ext_iff, map_sub, map_one, sub_eq_zero]
    rfl
  rw [h1, addOrderOf_dvd_iff_nsmul_eq_zero]
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective ((g : ZMod N) - 1)
  rw [← hn, map_natCast, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff,
    ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [he]
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero he0)).symm

private lemma filt_mem_higher {t : ℕ} (ht : t ≤ N.factorization l) (g : (ZMod N)ˣ) :
    g ∈ higherUnits N l t ↔ addOrderOf ((g : ZMod N) - 1) ∣ l ^ (N.factorization l - t) := by
  apply filt_mem_ker_iff
  rw [filt_gcd_eq l ht, mul_left_comm, ← pow_add, Nat.sub_add_cancel ht, mul_comm]
  exact (Nat.ordProj_mul_ordCompl_eq_self N l).symm

private lemma filt_card_ker {d : ℕ} (hd : d ∣ N) :
    Nat.card (ZMod.unitsMap hd).ker * Nat.totient d = Nat.totient N := by
  haveI : NeZero d := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hd⟩
  have h := Subgroup.card_mul_index (ZMod.unitsMap hd).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective hd),
    Subgroup.card_top] at h
  simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using h

private lemma filt_card_higher {t : ℕ} (ht : t ≤ N.factorization l) :
    Nat.card (higherUnits N l t) * Nat.totient (l ^ t) =
      Nat.totient (l ^ N.factorization l) := by
  have hl : l.Prime := Fact.out
  have h := filt_card_ker (Nat.gcd_dvd_left N (ordCompl[l] N * l ^ t))
  have hc : Nat.Coprime l (ordCompl[l] N) := Nat.coprime_ordCompl hl (NeZero.ne N)
  have hN : Nat.totient N = Nat.totient (l ^ N.factorization l) * Nat.totient (ordCompl[l] N) := by
    rw [← Nat.totient_mul (hc.pow_left _), Nat.ordProj_mul_ordCompl_eq_self]
  have hpos : 0 < Nat.totient (ordCompl[l] N) :=
    Nat.totient_pos.mpr (Nat.ordCompl_pos l (NeZero.ne N))
  change Nat.card (higherUnits N l t) * _ = _ at h
  rw [filt_gcd_eq l ht, Nat.totient_mul (hc.pow_left t).symm, hN] at h
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h]; ring

private lemma filt_telescope {v k : ℕ} (hk : k < v) :
    ∑ t ∈ Finset.range (k + 1), (Nat.totient (l ^ t) : ℚ) / (Nat.totient (l ^ v) : ℚ) =
      1 / (Nat.totient (l ^ (v - k)) : ℚ) := by
  have hl : l.Prime := Fact.out
  rw [← Finset.sum_div, ← Nat.cast_sum]
  have h1 : ∑ t ∈ Finset.range (k + 1), Nat.totient (l ^ t) = l ^ k := by
    rw [← Nat.sum_divisors_prime_pow hl, Nat.sum_totient]
  rw [h1]
  obtain ⟨j, rfl⟩ : ∃ j, v = k + j + 1 := ⟨v - k - 1, by omega⟩
  have : k + j + 1 - k = j + 1 := by omega
  rw [this, Nat.totient_prime_pow_succ hl, Nat.totient_prime_pow_succ hl]
  have h2 : ((l - 1 : ℕ) : ℚ) ≠ 0 := by
    have := hl.two_le
    exact Nat.cast_ne_zero.mpr (by omega)
  have h3 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  push_cast
  field_simp
  ring

private lemma filt_mem_ann {t : ℕ} (ht : t ≤ N.factorization l) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) ↔ condExp l ψ ≤ t := by
  have hl : l.Prime := Fact.out
  have h1 : ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) ↔
      ψ.conductor ∣ Nat.gcd N (ordCompl[l] N * l ^ t) := by
    rw [← mem_conductorSet_iff_conductor_dvd _ (Nat.gcd_dvd_left _ _), mem_conductorSet_iff,
      factorsThrough_iff_ker_unitsMap (Nat.gcd_dvd_left _ _), mem_annihilator_iff]
    refine forall_congr' fun a => imp_congr Iff.rfl ?_
    rw [MonoidHom.mem_ker, Units.ext_iff]
    simp
  rw [h1, filt_gcd_eq l ht, condExp]
  have hc := ψ.conductor_ne_zero
  have hN' : ordCompl[l] N ≠ 0 := (Nat.ordCompl_pos l (NeZero.ne N)).ne'
  have hp : l ^ t ≠ 0 := pow_ne_zero _ hl.ne_zero
  constructor
  · intro h
    have := (Nat.factorization_le_iff_dvd hc (mul_ne_zero hN' hp)).mpr h l
    rw [Nat.factorization_mul hN' hp] at this
    simpa [Nat.factorization_ordCompl, hl.factorization_pow] using this
  · intro h
    rw [← Nat.ordProj_mul_ordCompl_eq_self ψ.conductor l, mul_comm]
    exact Nat.mul_dvd_mul (Nat.ordCompl_dvd_ordCompl_of_dvd ψ.conductor_dvd_level l)
      (pow_dvd_pow _ h)

private lemma filt_card_ann (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  have : annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
    ext ψ
    rw [mem_annihilator_iff, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
    rfl
  rw [this, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

private lemma filt_ann_sup (U H : Subgroup (ZMod N)ˣ) (ψ : DirichletCharacter ℂ N) :
    ψ ∈ annihilator ℂ ((U ⊔ H : Subgroup (ZMod N)ˣ) : Set (ZMod N)ˣ) ↔
      ψ ∈ annihilator ℂ (H : Set (ZMod N)ˣ) ∧ ψ ∈ annihilator ℂ (U : Set (ZMod N)ˣ) := by
  simp only [mem_annihilator_iff, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨fun a ha => h a (Subgroup.mem_sup_right ha), fun a ha => h a (Subgroup.mem_sup_left ha)⟩
  · rintro ⟨h1, h2⟩ a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp ha
    rw [Units.val_mul, map_mul, h2 x hx, h1 y hy, mul_one]

private lemma filt_index {G : Type*} [CommGroup G] [Finite G] (U H : Subgroup G) :
    ((U ⊔ H).index : ℚ) / (H.index : ℚ) = (Nat.card ↥(U ⊓ H) : ℚ) / (Nat.card U : ℚ) := by
  have h1 : H.relIndex U * (U ⊔ H).index = H.index := by
    rw [← Subgroup.relIndex_sup_right U H]
    exact Subgroup.relIndex_mul_index le_sup_right
  have h2 : H.relIndex U * Nat.card ↥(U ⊓ H) = Nat.card U := by
    have h3 : Nat.card ↥(U ⊓ H) = Nat.card ((U ⊓ H).subgroupOf U) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    rw [h3, Subgroup.inf_subgroupOf_left]
    exact Subgroup.index_mul_card _
  have h4 : (H.relIndex U : ℚ) ≠ 0 := by
    have : Nat.card U ≠ 0 := Nat.card_pos.ne'
    rw [← h2] at this
    exact Nat.cast_ne_zero.mpr (left_ne_zero_of_mul this)
  have h5 : ((U ⊔ H).index : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have h6 : (Nat.card ↥(U ⊓ H) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← h1, ← h2]
  push_cast
  field_simp

theorem avgCondExp_annihilator (H : Subgroup (ZMod N)ˣ) :
    avgCondExp l (annihilator ℂ (H : Set (ZMod N)ˣ)) =
      ∑ t ∈ Finset.range (N.factorization l),
        (1 - (Nat.card ↥(higherUnits N l t ⊓ H) : ℚ) / (Nat.card (higherUnits N l t) : ℚ)) := by
  classical
  set X := annihilator ℂ (H : Set (ZMod N)ˣ) with hX
  haveI : Fintype X := Fintype.ofFinite X
  have hX0 : (Nat.card X : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc : ∀ ψ : DirichletCharacter ℂ N, (condExp l ψ : ℚ) =
      ∑ t ∈ Finset.range (N.factorization l),
        (1 - if ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) then (1 : ℚ) else 0) := by
    intro ψ
    have hle : condExp l ψ ≤ N.factorization l :=
      (Nat.factorization_le_iff_dvd ψ.conductor_ne_zero (NeZero.ne N)).mpr ψ.conductor_dvd_level l
    have h1 : ∀ t ∈ Finset.range (N.factorization l),
        (1 - if ψ ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ) then (1 : ℚ) else 0) =
          if t < condExp l ψ then 1 else 0 := by
      intro t ht
      have := filt_mem_ann l (Finset.mem_range.mp ht).le ψ
      by_cases h : t < condExp l ψ
      · rw [if_neg (by rw [this]; omega), if_pos h, sub_zero]
      · rw [if_pos (by rw [this]; omega), if_neg h, sub_self]
    rw [Finset.sum_congr rfl h1, Finset.sum_boole]
    have : (Finset.range (N.factorization l)).filter (fun t => t < condExp l ψ) =
        Finset.range (condExp l ψ) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  rw [avgCondExp, finsum_eq_sum_of_fintype]
  simp only [hc]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← filt_index, ← filt_card_ann, ← filt_card_ann H, ← hX, Finset.sum_sub_distrib,
    Finset.sum_boole, sub_div]
  congr 1
  · rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one,
      div_self hX0]
  · congr 2
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ X)
      (· ∈ annihilator ℂ (higherUnits N l t : Set (ZMod N)ˣ))).trans
        (Equiv.subtypeEquivRight fun ψ => (filt_ann_sup _ _ ψ).symm))

theorem rootWeight_eq_sum (g : (ZMod N)ˣ) (hg : g ≠ 1) :
    rootWeight l (addOrderOf ((g : ZMod N) - 1)) =
      ∑ t ∈ Finset.range (N.factorization l),
        Set.indicator (higherUnits N l t : Set (ZMod N)ˣ)
          (fun _ => 1 / (Nat.card (higherUnits N l t) : ℚ)) g := by
  classical
  have hl : l.Prime := Fact.out
  have hm1 : addOrderOf ((g : ZMod N) - 1) ≠ 1 := by
    rw [Ne, AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero]
    exact fun h => hg (Units.ext h)
  have hmN : addOrderOf ((g : ZMod N) - 1) ∣ N := by
    simpa using addOrderOf_dvd_card (x := (g : ZMod N) - 1)
  unfold rootWeight
  split_ifs with h
  · obtain ⟨-, s, hs⟩ := h
    have hs1 : s ≠ 0 := by rintro rfl; exact hm1 (by simpa using hs)
    have hsv : s ≤ N.factorization l := by
      rw [hs] at hmN
      exact (hl.pow_dvd_iff_le_factorization (NeZero.ne N)).mp hmN
    have h1 : ∀ t ∈ Finset.range (N.factorization l),
        Set.indicator (higherUnits N l t : Set (ZMod N)ˣ)
          (fun _ => 1 / (Nat.card (higherUnits N l t) : ℚ)) g =
        if t < N.factorization l - s + 1 then
          (Nat.totient (l ^ t) : ℚ) / (Nat.totient (l ^ N.factorization l) : ℚ) else 0 := by
      intro t ht
      have ht' := (Finset.mem_range.mp ht).le
      have h2 := filt_mem_higher l ht' g
      rw [hs, Nat.pow_dvd_pow_iff_le_right hl.one_lt] at h2
      rw [Set.indicator_apply]
      refine if_congr (h2.trans (by omega)) ?_ rfl
      rw [← filt_card_higher l ht']
      have h3 : (Nat.totient (l ^ t) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (pow_pos hl.pos _)).ne'
      have h4 : (Nat.card (higherUnits N l t) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      push_cast
      field_simp
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have : (Finset.range (N.factorization l)).filter (fun t => t < N.factorization l - s + 1) =
        Finset.range (N.factorization l - s + 1) := by
      ext t; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, filt_telescope l (by omega), hs, Nat.sub_sub_self hsv]
  · symm
    refine Finset.sum_eq_zero fun t ht => Set.indicator_of_notMem (fun hm => h ⟨hm1, ?_⟩) _
    have h2 := (filt_mem_higher l (Finset.mem_range.mp ht).le g).mp hm
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow hl).mp h2
    exact ⟨s, hs⟩


open scoped Classical in
open Classical in
theorem sum_rootWeight_eq_avgCondExp (H : Subgroup (ZMod N)ˣ) :
    ∑ g ∈ Finset.univ.filter (fun g : (ZMod N)ˣ => g ∉ H),
        rootWeight l (addOrderOf ((g : ZMod N) - 1)) =
      avgCondExp l (annihilator ℂ (H : Set (ZMod N)ˣ)) := by
  rw [avgCondExp_annihilator, Finset.sum_congr rfl (fun g hg => rootWeight_eq_sum l g
    (by rintro rfl; exact (Finset.mem_filter.mp hg).2 H.one_mem)), Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  generalize higherUnits N l t = U
  have h4 : (Nat.card U : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simp only [Set.indicator_apply, SetLike.mem_coe]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_comm]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)) (fun g => g ∈ H)
  have h2 : (Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)).card = Nat.card U := by
    rw [← Fintype.card_subtype, Nat.card_eq_fintype_card]
  have h3 : ((Finset.univ.filter (fun g : (ZMod N)ˣ => g ∈ U)).filter (fun g => g ∈ H)).card =
      Nat.card ↥(U ⊓ H) := by
    rw [Finset.filter_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  rw [h2, h3] at h1
  have h5 := congrArg (Nat.cast : ℕ → ℚ) h1
  push_cast at h5
  field_simp
  linarith

end KStar.Ram
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.RootNorm
namespace KStar.Ram

open NumberField

private theorem rootNorm_powerBasis {F : Type*} [Field F] [Algebra ℚ F] (pb : PowerBasis ℚ F) :
    Algebra.norm ℚ (1 - pb.gen) = (minpoly ℚ pb.gen).eval 1 := by
  classical
  rw [← charpoly_leftMulMatrix, Matrix.eval_charpoly, Algebra.norm_eq_matrix_det pb.basis,
    map_sub, map_one, map_one]

private theorem rootNorm_field {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ k : ℕ, Module.finrank ℚ K = (minpoly ℚ x).natDegree * k ∧
      Algebra.norm ℚ (1 - x) = ((minpoly ℚ x).eval 1) ^ k := by
  have hx : IsIntegral ℚ x := .of_finite ℚ x
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) K, ?_, ?_⟩
  · rw [← IntermediateField.adjoin.finrank hx, Module.finrank_mul_finrank]
  · have h1 : (1 - x : K) = algebraMap (IntermediateField.adjoin ℚ {x}) K
        (1 - IntermediateField.AdjoinSimple.gen ℚ x) := by
      simp
    have h2 := rootNorm_powerBasis (IntermediateField.adjoin.powerBasis hx)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen] at h2
    rw [h1, ← Algebra.norm_norm (S := IntermediateField.adjoin ℚ {x}), Algebra.norm_algebraMap, map_pow]
    exact congrArg (· ^ Module.finrank (IntermediateField.adjoin ℚ {x}) K) h2

theorem padicValNat_absNorm_one_sub {K : Type*} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime]
    {m : ℕ} (hm : 2 ≤ m) {η : 𝓞 K} (hη : IsPrimitiveRoot η m) :
    (padicValNat l (Ideal.absNorm (Ideal.span {1 - η})) : ℚ) =
      Module.finrank ℚ K * rootWeight l m := by
  haveI : NeZero m := ⟨by omega⟩
  have hηK : IsPrimitiveRoot (η : K) m :=
    hη.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  obtain ⟨k, hk, hnorm⟩ := rootNorm_field (η : K)
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega), Polynomial.natDegree_cyclotomic] at hk
  rw [← Polynomial.cyclotomic_eq_minpoly_rat hηK (by omega)] at hnorm
  have hcQ : (Polynomial.cyclotomic m ℚ).eval 1 = (((Polynomial.cyclotomic m ℤ).eval 1 : ℤ) : ℚ) := by
    rw [← Polynomial.map_cyclotomic_int, ← Int.cast_one, Polynomial.eval_intCast_map, eq_intCast,
      Int.cast_one]
  have hnormZ : Algebra.norm ℤ (1 - η) = ((Polynomial.cyclotomic m ℤ).eval 1) ^ k := by
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_norm_int, Int.cast_pow, ← hcQ, ← hnorm]
    push_cast
    rfl
  have hv : (padicValNat l ((Polynomial.cyclotomic m ℤ).eval 1).natAbs : ℚ) =
      m.totient * rootWeight l m := by
    by_cases hpp : ∃ p j, p.Prime ∧ m = p ^ (j + 1)
    · obtain ⟨p, j, hp, rfl⟩ := hpp
      haveI := Fact.mk hp
      rw [Polynomial.eval_one_cyclotomic_prime_pow, Int.natAbs_natCast]
      have hne : p ^ (j + 1) ≠ 1 := fun h => by rw [h] at hm; norm_num at hm
      by_cases hpl : p = l
      · subst hpl
        rw [Nat.padicValNat_def, Nat.Prime.multiplicity_self, rootWeight,
          if_pos ⟨hne, j + 1, rfl⟩]
        have ht : ((p ^ (j + 1)).totient : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr (by positivity)).ne'
        rw [Nat.cast_one, mul_one_div, div_self ht]
      · rw [Nat.padicValNat_def, multiplicity_primes (Ne.symm hpl), rootWeight, if_neg]
        · simp
        · rintro ⟨-, s, hs⟩
          apply hpl
          rcases s with _ | s
          · rw [pow_zero] at hs
            exact absurd hs hne
          · have hd : p ∣ l ^ (s + 1) := by
              rw [← hs]
              exact dvd_pow_self p (Nat.succ_ne_zero j)
            exact (Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp (hp.dvd_of_dvd_pow hd)
    · have h1 : Polynomial.eval 1 (Polynomial.cyclotomic m ℤ) = 1 := by
        apply Polynomial.eval_one_cyclotomic_not_prime_pow
        intro p hp j hj
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · exact hpp ⟨p, j, hp, hj.symm⟩
      rw [h1, rootWeight, if_neg]
      · simp [_root_.Nat.padicValNat_def (n := 1)]
      · rintro ⟨-, s, hs⟩
        rcases s with _ | s
        · rw [pow_zero] at hs
          omega
        · exact hpp ⟨l, s, Fact.out, hs⟩
  rw [Nat.padicValNat_def] at hv
  rw [Ideal.absNorm_span_singleton, hnormZ, Int.natAbs_pow, Nat.padicValNat_def,
    Nat.multiplicity_pow, hk, Nat.cast_mul, Nat.cast_mul, hv]
  ring

end KStar.Ram
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycDifferent
namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

open Polynomial in
private theorem minpoly_map_eq_prod_gal {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (x : L) (hx : Algebra.adjoin F {x} = ⊤) :
    (minpoly F x).map (algebraMap F L) = ∏ σ : Gal(L/F), (X - C (σ x)) := by
  classical
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hinj : Function.Injective (fun σ : Gal(L/F) => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hx
    rintro y rfl
    exact h
  have hm : (∏ σ : Gal(L/F), (X - C (σ x))).Monic :=
    monic_prod_of_monic _ _ fun σ _ => monic_X_sub_C _
  have hdvd : (∏ σ : Gal(L/F), (X - C (σ x))) ∣ (minpoly F x).map (algebraMap F L) := by
    apply Finset.prod_dvd_of_coprime
    · intro σ _ τ _ hne
      exact pairwise_coprime_X_sub_C hinj hne
    · intro σ _
      rw [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap, aeval_algEquiv]
      simp
  refine eq_of_monic_of_dvd_of_natDegree_le hm ((minpoly.monic hint).map _) hdvd ?_
  rw [natDegree_map, natDegree_prod_of_monic _ _ (fun σ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  exact minpoly.natDegree_le x

open Polynomial Classical in
private theorem aeval_derivative_minpoly_eq_prod_gal {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L] (x : L)
    (hx : Algebra.adjoin F {x} = ⊤) :
    aeval x (derivative (minpoly F x)) = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1, (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map, minpoly_map_eq_prod_gal x hx,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : Gal(L/F))), derivative_mul]
  simp [eval_prod]

open Polynomial Classical in
private theorem differentIdeal_eq_span_of_prod (A F : Type*) {L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F] [Field L] [NumberField L] [Algebra A F] [IsFractionRing A F]
    [Algebra F L] [Algebra A L] [Algebra A (𝓞 L)] [IsScalarTower A F L] [IsScalarTower A (𝓞 L) L]
    [IsIntegralClosure (𝓞 L) A L] [Module.IsTorsionFree A (𝓞 L)]
    [FiniteDimensional F L] [IsGalois F L] (x y : 𝓞 L)
    (hx : Algebra.adjoin A {x} = ⊤) (hx' : Algebra.adjoin F {algebraMap (𝓞 L) L x} = ⊤)
    (hy : algebraMap (𝓞 L) L y = ∏ σ ∈ (Finset.univ : Finset Gal(L/F)).erase 1,
      (algebraMap (𝓞 L) L x - σ (algebraMap (𝓞 L) L x))) :
    differentIdeal A (𝓞 L) = Ideal.span {y} := by
  have h := conductor_mul_differentIdeal A F L x hx'
  rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul] at h
  rw [h]
  congr 2
  apply IsFractionRing.injective (𝓞 L) L
  have hint : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  rw [hy, ← aeval_derivative_minpoly_eq_prod_gal _ hx',
    minpoly.isIntegrallyClosed_eq_field_fractions F L hint, derivative_map, aeval_map_algebraMap,
    aeval_algebraMap_apply]

private theorem adjoin_root_eq_top (E : Type*) [Field E] [Algebra ℚ E] [Algebra E K]
    [IsScalarTower ℚ E K] {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin E {ζ} = ⊤ := by
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℚ {ζ} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℚ {ζ} ≤ (Algebra.adjoin E {ζ}).restrictScalars ℚ :=
    Algebra.adjoin_le (by simp)
  exact this hy

private theorem adjoin_toInteger_eq_top (A : Type*) [CommRing A] [Algebra A (𝓞 K)]
    {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    Algebra.adjoin A {hζ.toInteger} = ⊤ := by
  have h := adjoin_singleton_eq_top hζ
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Algebra.adjoin ℤ {hζ.toInteger} := h ▸ Algebra.mem_top
  have : Algebra.adjoin ℤ {hζ.toInteger} ≤ (Algebra.adjoin A {hζ.toInteger}).restrictScalars ℤ :=
    Algebra.adjoin_le (by simp)
  exact this hy


open scoped Classical in
open Classical in
theorem relDifferent_eq_span_prod (E : IntermediateField ℚ K) {ζ : K} (hζ : IsPrimitiveRoot ζ N) :
    differentIdeal (𝓞 E) (𝓞 K) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup ∧ σ ≠ 1),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  refine differentIdeal_eq_span_of_prod (𝓞 E) E hζ.toInteger _
    (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top E hζ) ?_
  rw [map_prod]
  symm
  refine Finset.prod_bij (fun σ _ => σ.restrictScalars ℚ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    · intro h
      apply (Finset.mem_erase.mp hσ).1
      ext x
      exact DFunLike.congr_fun h x
  · intro σ _ τ _ h
    ext x
    exact DFunLike.congr_fun h x
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨E.fixingSubgroupEquiv ⟨σ, hσ.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      apply hσ.2
      ext x
      exact DFunLike.congr_fun h x
    · rfl
  · intro σ _
    rfl


open scoped Classical in
open Classical in
theorem map_differentIdeal_eq_span_prod (E : IntermediateField ℚ K) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    (differentIdeal ℤ (𝓞 E)).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span
      {∏ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
        (hζ.toInteger - σ • hζ.toInteger)} := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  have h1 : differentIdeal ℤ (𝓞 K) = Ideal.span
      {∏ σ ∈ (Finset.univ : Finset Gal(K/ℚ)).erase 1, (hζ.toInteger - σ • hζ.toInteger)} := by
    refine differentIdeal_eq_span_of_prod ℤ ℚ hζ.toInteger _
      (adjoin_toInteger_eq_top _ hζ) (adjoin_root_eq_top ℚ hζ) ?_
    rw [map_prod]
    rfl
  have h2 := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 K)
  have h3 : differentIdeal (𝓞 E) (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
  apply mul_left_cancel₀ h3
  rw [← h2, h1, relDifferent_eq_span_prod E hζ, Ideal.span_singleton_mul_span_singleton,
    ← Finset.prod_filter_mul_prod_filter_not _ (fun σ : Gal(K/ℚ) => σ ∈ E.fixingSubgroup)]
  congr 4
  · ext σ
    simp [and_comm]
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and,
      and_iff_right_iff_imp]
    rintro h rfl
    exact h (one_mem _)

end KStar.Ram
end

namespace KStar.Ram

open NumberField DirichletCharacter IsCyclotomicExtension.Rat
open scoped Pointwise

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

private theorem isPrimitiveRoot_pow_val {R : Type*} [CommRing R] {z : R}
    (hz : IsPrimitiveRoot z N) (a : ZMod N) : IsPrimitiveRoot (z ^ a.val) (addOrderOf a) := by
  have h1 : addOrderOf a = orderOf (z ^ a.val) := by
    have hfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨N, NeZero.pos N, hz.pow_eq_one⟩
    rw [hfin.orderOf_pow, ← hz.eq_orderOf, ← ZMod.addOrderOf_coe _ (NeZero.ne N),
      ZMod.natCast_zmod_val]
  rw [h1]
  exact IsPrimitiveRoot.orderOf _

private theorem span_sub_smul {z : 𝓞 K} (hz : IsPrimitiveRoot z N) (σ : Gal(K/ℚ)) :
    Ideal.span {z - σ • z} =
      Ideal.span {1 - z ^ ((galEquivZMod N K σ : ZMod N) - 1).val} := by
  rw [galEquivZMod_smul_of_pow_eq N K σ hz.pow_eq_one]
  have h : z ^ (galEquivZMod N K σ).val.val =
      z ^ (1 + ((galEquivZMod N K σ : ZMod N) - 1).val) := by
    refine pow_eq_pow_of_modEq ?_ hz.pow_eq_one
    rw [← ZMod.natCast_eq_natCast_iff]
    simp
  rw [h, pow_add, pow_one, ← mul_one_sub]
  exact Ideal.span_singleton_mul_left_unit (hz.isUnit (NeZero.ne N)) _

private theorem padicValNat_prod {ι : Type*} (l : ℕ) [Fact l.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValNat l (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat l (f i) := by
  have hl : l.Prime := Fact.out
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ hl]
  rw [Nat.factorization_prod hf, Finsupp.finsetSum_apply]

private theorem vdField_eq_avg (E : IntermediateField ℚ K) (l : ℕ) [Fact l.Prime] :
    vdField E l = avgCondExp l (fieldChars N E) := by
  classical
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have hz := hζ.toInteger_isPrimitiveRoot
  have h := congrArg Ideal.absNorm (map_differentIdeal_eq_span_prod E hζ)
  rw [Ideal.absNorm_algebraMap, absNorm_differentIdeal E,
    ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K, ← Ideal.prod_span_singleton, map_prod] at h
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hne' := h ▸ pow_ne_zero (Module.finrank E K) hne
  have h2 := congrArg (padicValNat l) h
  rw [Nat.padicValNat_def, Nat.multiplicity_pow, ← Nat.padicValNat_def,
    padicValNat_prod l _ _ (Finset.prod_ne_zero_iff.1 hne')] at h2
  have h3 := congrArg (Nat.cast : ℕ → ℚ) h2
  push_cast at h3
  have h4 : ∀ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      (padicValNat l (Ideal.absNorm (Ideal.span {hζ.toInteger - σ • hζ.toInteger})) : ℚ) =
        Module.finrank ℚ K * rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) := by
    intro σ hσ
    rw [span_sub_smul hz σ]
    refine padicValNat_absNorm_one_sub l ?_ (isPrimitiveRoot_pow_val hz _)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact (Finset.mem_filter.1 hσ).2 (one_mem _)
    have hpos := addOrderOf_pos ((galEquivZMod N K σ : ZMod N) - 1)
    have hne1 : addOrderOf ((galEquivZMod N K σ : ZMod N) - 1) ≠ 1 := by
      rw [Ne, AddMonoid.addOrderOf_eq_one_iff, sub_eq_zero, Units.val_eq_one,
        map_eq_one_iff _ (galEquivZMod N K).injective]
      exact hσ1
    omega
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum] at h3
  have h5 : ∑ σ ∈ Finset.univ.filter (fun σ : Gal(K/ℚ) => σ ∉ E.fixingSubgroup),
      rootWeight l (addOrderOf ((galEquivZMod N K σ : ZMod N) - 1)) =
      avgCondExp l (fieldChars N E) := by
    rw [fieldChars, ← sum_rootWeight_eq_avgCondExp]
    refine Finset.sum_equiv (galEquivZMod N K).toEquiv ?_ (fun _ _ => rfl)
    intro σ
    rw [Finset.mem_filter_univ, Finset.mem_filter_univ, fieldUnits]
    exact not_congr (Subgroup.mem_map_iff_mem (f := (galEquivZMod N K).toMonoidHom)
      (galEquivZMod N K).injective).symm
  rw [h5, ← Module.finrank_mul_finrank ℚ E K] at h3
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have p2 : (Module.finrank E K : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [vdField, padicValInt, div_eq_iff p1]
  push_cast at h3
  apply mul_left_cancel₀ p2
  rw [← Nat.padicValNat_def, h3]; ring

theorem natAbs_discr_eq_finprod_conductor (E : IntermediateField ℚ K) :
    (discr E).natAbs = ∏ᶠ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor ∧
      Real.log (rootDiscr E) = logRootDiscChar (fieldChars N E) ∧
      (discr E).natAbs.primeFactors = (fieldCond (fieldChars N E)).primeFactors := by
  classical
  have := Fintype.ofFinite (fieldChars N E)
  have hne : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hc : ∀ ψ : DirichletCharacter ℂ N, ψ.conductor ≠ 0 := fun ψ => conductor_ne_zero ψ
  have p1 : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hcard := (card_fieldChars (N := N) E).1
  have h1 : (discr E).natAbs = ∏ ψ : fieldChars N E, (ψ : DirichletCharacter ℂ N).conductor := by
    refine Nat.eq_of_factorization_eq hne (Finset.prod_ne_zero_iff.2 fun ψ _ => hc _) fun l => ?_
    by_cases hl : l.Prime
    · have : Fact l.Prime := ⟨hl⟩
      have h := vdField_eq_avg (N := N) E l
      rw [vdField, avgCondExp, hcard, div_left_inj' p1, finsum_eq_sum_of_fintype, padicValInt] at h
      rw [Nat.factorization_prod fun ψ _ => hc _, Finsupp.finsetSum_apply,
        Nat.factorization_def _ hl]
      exact_mod_cast h
    · simp [Nat.factorization_eq_zero_of_not_prime _ hl]
  refine ⟨by rw [finprod_eq_prod_of_fintype, h1], ?_, ?_⟩
  · have habs : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := by
      rw [← Int.natCast_natAbs, Int.cast_natCast]
    rw [rootDiscr_def, logRootDiscChar, hcard, finsum_eq_sum_of_fintype, habs,
      Real.log_rpow (by exact_mod_cast Nat.pos_of_ne_zero hne), h1, Nat.cast_prod,
      Real.log_prod (fun ψ _ => by exact_mod_cast hc _), div_eq_inv_mul]
  · have hf : fieldCond (fieldChars N E) ≠ 0 := by
      rw [fieldCond, Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨ψ, -, h⟩
      exact hc ψ h
    ext l
    rw [Nat.mem_primeFactors_of_ne_zero hne, Nat.mem_primeFactors_of_ne_zero hf]
    refine and_congr_right fun hl => ?_
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨a, b, -⟩ := ramIdx_eq_one_iff l (fieldChars N E)
    rw [h1, hl.prime.dvd_finsetProd_iff, ← not_iff_not, ← b, a]
    simp

end KStar.Ram
