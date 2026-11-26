module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelGroupSupLevelInertia

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFinite
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nf_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nf_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nf_mem_princ {a s : ℕ} (h : s ≤ a) {u : ℤ_[l]ˣ}
    (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) : u ∈ princ l s := by
  rw [mem_princ, hu]
  exact pow_dvd_pow _ h

private theorem nf_emult {a : ℕ} {u : ℤ_[l]ˣ} (hu : (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a) :
    emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
  rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := nf_exists_unit (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (nf_mem_princ (by omega) hu)
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by
    rw [hu]
    exact pow_dvd_pow _ (by omega)
  have := nf_nu_le hm tr
  rw [emultiplicity_pow_sub_one_sq h1, nf_emult hu,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at this
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) this

end KStar.TotallyRealRoots
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDegree
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem mem_fixingSubgroup_adjoinRoots (m : ℕ) (g : Gal(AlgebraicClosure E/E)) :
    g ∈ (adjoinRoots E m).fixingSubgroup ↔ ∀ ζ : AlgebraicClosure E, ζ ^ m = 1 → g ζ = ζ := by
  constructor
  · intro hg ζ hζ
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg ζ
      (IntermediateField.subset_adjoin E _ hζ)
  · intro h
    have hle : adjoinRoots E m ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro ζ hζ
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      have : Subgroup.zpowers g ≤ MulAction.stabilizer Gal(AlgebraicClosure E/E) ζ := by
        rw [Subgroup.zpowers_le]
        exact h ζ hζ
      exact fun f hf => this hf
    exact (IntermediateField.le_iff_le _ _).1 hle (Subgroup.mem_zpowers g)

private theorem comap_princ_eq [CharZero E] (n : ℕ) :
    (princ l n).comap (eps l E) = (adjoinRoots E (l ^ n)).fixingSubgroup := by
  ext g
  rw [Subgroup.mem_comap, eps_mem_princ_iff, mem_fixingSubgroup_adjoinRoots]

theorem card_map_redPow_galImage [CharZero E] (n : ℕ) :
    Nat.card ((galImage l E).map (redPow l n)) = Module.finrank E (adjoinRoots E (l ^ n)) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← comap_princ_eq, princ,
    MonoidHom.comap_ker, Subgroup.index_ker, galImage, MonoidHom.map_range]

end KStar.TotallyRealRoots
end

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem go_finiteDimensional_adjoinRoots {m : ℕ} (hm : 0 < m) :
    FiniteDimensional E (adjoinRoots E m) := by
  classical
  have hfin : {ζ : AlgebraicClosure E | ζ ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : AlgebraicClosure E)).toFinset.finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hm] using hζ
  have : Finite {ζ : AlgebraicClosure E | ζ ^ m = 1} := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem totient_le_finrank_mul [NumberField E] (n : ℕ) :
    (l ^ n).totient ≤ Module.finrank ℚ E * Module.finrank E (adjoinRoots E (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have : NeZero ((l ^ n : ℕ) : AlgebraicClosure E) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  have := go_finiteDimensional_adjoinRoots (E := E) hpos
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) (l ^ n)
  have hmem : ζ ∈ adjoinRoots E (l ^ n) := IntermediateField.subset_adjoin E _ hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : adjoinRoots E (l ^ n)) (l ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := (adjoinRoots E (l ^ n)).val) hζ Subtype.val_injective
  have : FiniteDimensional ℚ (adjoinRoots E (l ^ n)) := Module.Finite.trans E _
  rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic (l ^ n) ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hζ' hpos]
  exact minpoly.natDegree_le _

theorem finiteIndex_of_index_map_le {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {B : ℕ}
    (h : ∀ n, (U.map (redPow l n)).index ≤ B) : U.FiniteIndex := by
  have hl : l.Prime := Fact.out
  have hidx : ∀ n, (U ⊔ princ l n).index = (U.map (redPow l n)).index := by
    intro n
    show (U ⊔ (redPow l n).ker).index = _
    rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr (redPow_surjective n), Subgroup.index_top,
      mul_one]
  have hne : ∀ n, (U ⊔ princ l n).index ≠ 0 := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [hidx]
    exact Subgroup.index_ne_zero_of_finite
  have hbdd : BddAbove (Set.range fun n => (U ⊔ princ l n).index) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    show (U ⊔ princ l n).index ≤ B
    rw [hidx]
    exact h n
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ n, (U ⊔ princ l n).index ≤ (U ⊔ princ l n₀).index := by
    intro n
    have hc := le_csSup hbdd ⟨n, rfl⟩
    rw [← hn₀] at hc
    exact hc
  have hstab : ∀ n, n₀ ≤ n → U ⊔ princ l n₀ ≤ U ⊔ princ l n := by
    intro n hn
    have hle : U ⊔ princ l n ≤ U ⊔ princ l n₀ := sup_le_sup_left (princ_anti hn) U
    have hmul := Subgroup.relIndex_mul_index hle
    have h1 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) = 1 := by
      have hpos : 0 < (U ⊔ princ l n₀).index := Nat.pos_of_ne_zero (hne n₀)
      have hm : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) * (U ⊔ princ l n₀).index
          ≤ 1 * (U ⊔ princ l n₀).index := by
        rw [hmul, one_mul]
        exact hmax n
      have h' := Nat.le_of_mul_le_mul_right hm hpos
      have h0 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        exact hne n hmul.symm
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hsub : U ⊔ princ l n₀ ≤ U := by
    intro x hx
    apply mem_of_isClosed hU
    intro b
    have hxm : x ∈ U ⊔ princ l (max b n₀) := hstab _ (le_max_right _ _) hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxm
    refine ⟨u, hu, ?_⟩
    have hz' : z ∈ princ l b := princ_anti (le_max_left b n₀) hz
    have hz1 : redPow l b z = 1 := MonoidHom.mem_ker.mp hz'
    rw [map_mul, hz1, mul_one]
  have hEq : U ⊔ princ l n₀ = U := le_antisymm hsub le_sup_left
  rw [← hEq]
  exact ⟨hne n₀⟩

theorem isOpen_galImage [NumberField E] : IsOpen (galImage l E : Set ℤ_[l]ˣ) := by
  rw [isOpen_iff_isClosed_finiteIndex]
  refine ⟨isClosed_galImage,
    finiteIndex_of_index_map_le isClosed_galImage (B := Module.finrank ℚ E) fun n => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hN : 0 < l ^ n := pow_pos hl.pos n
  haveI : FiniteDimensional E (adjoinRoots E (l ^ n)) := go_finiteDimensional_adjoinRoots hN
  have hcard := Subgroup.index_mul_card ((galImage l E).map (redPow l n))
  rw [card_map_redPow_galImage, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  have htot := totient_le_finrank_mul (l := l) (E := E) n
  have hpos : 0 < Module.finrank E (adjoinRoots E (l ^ n)) := Module.finrank_pos
  rw [← hcard] at htot
  exact Nat.le_of_mul_le_mul_right htot hpos

end KStar.TotallyRealRoots
end
