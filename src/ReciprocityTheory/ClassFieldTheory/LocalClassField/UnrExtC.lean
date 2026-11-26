module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
public import Lemmata.GeneralBFactUpperTerForm.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtB
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

namespace UnramifiedExtensions

variable {p}

theorem norm_sum_le_of_le {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  first | exact Bl.general_b_fact_upper_ter_form.goal1 .. | (apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption)

theorem norm_sum_eq_one {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (b : ι → Obar p)
    (hb : ∀ j, (b j : PadicAlgCl p) ∈ K) (i : ι) (hi : b i = 1) :
    ‖∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ = 1 := by
  have hs : ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) = ((∑ j, b j * ω j : Obar p) : PadicAlgCl p) := by
    push_cast; rfl
  rw [hs]
  refine le_antisymm (norm_le_one _) (not_lt.1 fun hlt => ?_)
  have h0 := (res_eq_zero_iff _).2 hlt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h0
  let c : ι → resK p K := fun j => ⟨res (b j), (mem_resK_iff K _).2 ⟨b j, hb j, rfl⟩⟩
  have h1 : ∑ j, c j • IsLocalRing.residue (Obar p) (ω j) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subfield.smul_def, smul_eq_mul, map_mul]
  have h2 := Fintype.linearIndependent_iff.1 hω c h1 i
  have h3 : res (b i) = 0 := congrArg Subtype.val h2
  rw [hi, map_one] at h3
  exact one_ne_zero h3

end UnramifiedExtensions

theorem norm_le_norm_sum {ι : Type} [Fintype ι] (ω : ι → Obar p)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) (a : ι → K) (i : ι) :
    ‖(a i : PadicAlgCl p)‖ ≤ ‖∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)‖ := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖) ⟨i, Finset.mem_univ i⟩
  refine (hm i (Finset.mem_univ i)).trans ?_
  by_cases h0 : (a m : PadicAlgCl p) = 0
  · rw [h0, norm_zero]; exact norm_nonneg _
  have hpos : 0 < ‖(a m : PadicAlgCl p)‖ := norm_pos_iff.2 h0
  have hle : ∀ j, ‖(a j : PadicAlgCl p) / (a m : PadicAlgCl p)‖ ≤ 1 := by
    intro j
    rw [norm_div, div_le_one hpos]
    exact hm j (Finset.mem_univ j)
  let b : ι → Obar p := fun j => ⟨(a j : PadicAlgCl p) / (a m : PadicAlgCl p), mem_Obar_iff.2 (hle j)⟩
  have h1 := UnramifiedExtensions.norm_sum_eq_one (K := K) ω hω b (fun j => K.div_mem (a j).2 (a m).2) m
    (Subtype.ext (div_self h0))
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p)
      = (a m : PadicAlgCl p) * ∑ j, (b j : PadicAlgCl p) * (ω j : PadicAlgCl p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = (a m : PadicAlgCl p) * ((a j : PadicAlgCl p) / (a m : PadicAlgCl p) * (ω j : PadicAlgCl p))
    field_simp
  rw [h2, norm_mul, h1, mul_one]

namespace UnramifiedExtensions

variable {p} {K}

noncomputable def comb {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L) : (ι → K) →ₗ[ℚ_[p]] L where
  toFun a := ⟨∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p),
    L.sum_mem fun j _ => L.mul_mem (hKL (a j).2) (hL j)⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_assoc, Finset.mul_sum]

theorem comb_injective {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) {ι : Type} [Fintype ι]
    (ω : ι → Obar p) (hL : ∀ j, (ω j : PadicAlgCl p) ∈ L)
    (hω : LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i))) :
    Function.Injective (comb hKL ω hL) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  have h1 := norm_le_norm_sum p K ω hω a i
  have h2 : ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) = 0 := congrArg Subtype.val ha
  rw [h2, norm_zero] at h1
  exact Subtype.ext (norm_le_zero_iff.1 h1)

noncomputable def resMod {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Submodule (resK p K) (kbar p) where
  carrier := (resK p L : Set (kbar p))
  add_mem' := fun ha hb => (resK p L).add_mem ha hb
  zero_mem' := (resK p L).zero_mem
  smul_mem' := fun c x hx => by
    rw [Subfield.smul_def, smul_eq_mul]
    exact (resK p L).mul_mem (resK_mono hKL c.2) hx

set_option synthInstance.maxHeartbeats 100000 in
theorem exists_lifts {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ ∃ ω : Fin f → Obar p, (∀ j, (ω j : PadicAlgCl p) ∈ L) ∧
      LinearIndependent (resK p K) (fun i => IsLocalRing.residue (Obar p) (ω i)) := by
  have hfL : Finite (resK p L) := finite_resK L hL
  have hfW : Finite (resMod hKL) := hfL
  letI : Module.Finite (resK p K) (resMod hKL) := Module.Finite.of_finite
  have hcard : Nat.card (resMod hKL) = Nat.card (resK p K) ^ Module.finrank (resK p K) (resMod hKL) :=
    Module.natCard_eq_pow_finrank
  have hnt : Nontrivial (resMod hKL) :=
    ⟨⟨⟨1, (resK p L).one_mem⟩, 0, fun h => one_ne_zero (congrArg Subtype.val h)⟩⟩
  refine ⟨Module.finrank (resK p K) (resMod hKL), Module.finrank_pos, hcard, ?_⟩
  let B := Module.finBasis (resK p K) (resMod hKL)
  have hex : ∀ i, ∃ x : Obar p, (x : PadicAlgCl p) ∈ L ∧ res x = (B i : kbar p) :=
    fun i => (mem_resK_iff L _).1 (B i).2
  choose ω h1 h2 using hex
  refine ⟨ω, h1, ?_⟩
  have h3 : (fun i => IsLocalRing.residue (Obar p) (ω i)) = (resMod hKL).subtype ∘ B := by
    funext i; exact h2 i
  rw [h3]
  exact B.linearIndependent.map' _ (Submodule.ker_subtype _)

theorem finrank_fun (hK : FiniteDimensional ℚ_[p] K) (f : ℕ) : Module.finrank ℚ_[p] (Fin f → K) = f * Module.finrank ℚ_[p] K := by
  rw [Module.finrank_pi_fintype]
  simp

end UnramifiedExtensions

theorem qK_le_pow_finrank (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ f * Module.finrank ℚ_[p] K ≤ Module.finrank ℚ_[p] L := by
  obtain ⟨f, hf, hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  refine ⟨f, hf, hq, ?_⟩
  rw [← UnramifiedExtensions.finrank_fun hK]
  exact LinearMap.finrank_le_finrank_of_injective (UnramifiedExtensions.comb_injective hKL ω h1 h2)

theorem exists_norm_eq_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hKL : K ≤ L) {f : ℕ} (hf : 0 < f) (hdeg : Module.finrank ℚ_[p] L = f * Module.finrank ℚ_[p] K)
    (h : qK p L = qK p K ^ f) {x : PadicAlgCl p} (hx : x ∈ L) : ∃ y ∈ K, ‖x‖ = ‖y‖ := by
  classical
  have hL : FiniteDimensional ℚ_[p] L := by
    apply Module.finite_of_finrank_pos
    rw [hdeg]
    exact Nat.mul_pos hf Module.finrank_pos
  obtain ⟨f', hf', hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  have hff : f' = f := Nat.pow_right_injective (one_lt_qK p K hK) (hq.symm.trans h)
  subst hff
  have hsurj : Function.Surjective (UnramifiedExtensions.comb hKL ω h1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((UnramifiedExtensions.finrank_fun hK f').trans hdeg.symm)).1 (UnramifiedExtensions.comb_injective hKL ω h1 h2)
  obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
  have hxa : x = ∑ j, (a j : PadicAlgCl p) * (ω j : PadicAlgCl p) := (congrArg Subtype.val ha).symm
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => ‖(a j : PadicAlgCl p)‖)
    ⟨⟨0, hf⟩, Finset.mem_univ _⟩
  refine ⟨a m, (a m).2, le_antisymm ?_ ?_⟩
  · rw [hxa]
    refine UnramifiedExtensions.norm_sum_le_of_le _ _ (norm_nonneg _) fun j _ => ?_
    rw [norm_mul]
    calc ‖(a j : PadicAlgCl p)‖ * ‖(ω j : PadicAlgCl p)‖ ≤ ‖(a j : PadicAlgCl p)‖ * 1 :=
          mul_le_mul_of_nonneg_left (UnramifiedExtensions.norm_le_one _) (norm_nonneg _)
      _ ≤ ‖(a m : PadicAlgCl p)‖ := by rw [mul_one]; exact hm j (Finset.mem_univ j)
  · rw [hxa]
    exact norm_le_norm_sum p K ω h2 a m

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Polynomial

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem finiteDimensional_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    FiniteDimensional ℚ_[p] (Kn p K n) := by
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : 0 < qK p K ^ n - 1 := Nat.pos_of_ne_zero (by rintro h; exact hnd (h ▸ dvd_zero p))
  have hfin : Finite {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} := by
    have : {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1} =
        (nthRootsFinset (qK p K ^ n - 1) (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
      ext ζ
      simp [mem_nthRootsFinset hm0]
    rw [this]
    exact Finset.finite_toSet _
  have h2 : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (qK p K ^ n - 1) = 1}) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact IntermediateField.finiteDimensional_sup _ _

theorem extendScalars_Kn_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (qK p K ^ n - 1))
    (hm : qK p K ^ n - 1 ≠ 0) :
    IntermediateField.extendScalars (le_Kn p K n) = IntermediateField.adjoin K {ζ} := by
  apply le_antisymm
  · have h : Kn p K n ≤ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[p] := by
      apply UnramifiedExtensions.Kn_le
      · intro y hy
        exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨y, hy⟩
      · intro ξ hξ
        have : NeZero (qK p K ^ n - 1) := ⟨hm⟩
        obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
        exact pow_mem (IntermediateField.mem_adjoin_simple_self K ζ) i
    exact h
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact mem_Kn_of_pow p K hζ.pow_eq_one

theorem natDegree_minpoly_le (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K ^ n - 1) = 1) : (minpoly K ζ).natDegree ≤ n := by
  classical
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hsep : (minpoly K ζ).Separable := (minpoly.irreducible hint).separable
  have hcard := card_rootSet_eq_natDegree (K := PadicAlgCl p) hsep (IsAlgClosed.splits _)
  calc (minpoly K ζ).natDegree = Fintype.card ((minpoly K ζ).rootSet (PadicAlgCl p)) := hcard.symm
    _ = ((minpoly K ζ).rootSet (PadicAlgCl p)).toFinset.card := (Set.toFinset_card _).symm
    _ ≤ ((Finset.range n).image (fun i => ζ ^ (qK p K ^ i))).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Set.mem_toFinset] at hy
        obtain ⟨σ, hσ⟩ := ((isConjRoot_iff_mem_minpoly_rootSet hint).2 hy).symm.exists_algEquiv
        obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, by rw [← h, hσ]⟩
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

theorem finrank_unramified_extension (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n ∧ qK p (Kn p K n) = qK p K ^ n := by
  have hq := one_lt_qK p K hK
  have hnd := UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn
  have hm0 : qK p K ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  obtain ⟨ζ, hζ⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hfd := finiteDimensional_Kn p K hK hn
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hup : Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) ≤ n := by
    rw [extendScalars_Kn_eq_adjoin p K hζ hm0, IntermediateField.adjoin.finrank hint]
    exact natDegree_minpoly_le p K hK hn hζ.pow_eq_one
  obtain ⟨f, hf, hqf, hle⟩ := qK_le_pow_finrank p K hK hfd (le_Kn p K n)
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n)] at hmul
  have hd : 0 < Module.finrank ℚ_[p] K := Module.finrank_pos
  have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ.pow_eq_one

  have hnf : n ≤ f := by
    have hmem : UnramifiedExtensions.red ζ ∈ resK p (Kn p K n) :=
      (UnramifiedExtensions.mem_resK_iff _ _).2 ⟨⟨ζ, mem_Obar_iff.2 h1.le⟩, mem_Kn_of_pow p K hζ.pow_eq_one,
        (UnramifiedExtensions.red_of_le h1.le).symm⟩
    have h2 := UnramifiedExtensions.pow_qK_eq (Kn p K n) hfd hmem
    rw [hqf, ← UnramifiedExtensions.red_pow h1.le] at h2
    have hζf : (ζ ^ (qK p K ^ f)) ^ (qK p K ^ n - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h3 : ζ ^ (qK p K ^ f) = ζ := by
      by_contra hne
      have h4 := UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hnd hζf hζ.pow_eq_one hne
      have h5 := (UnramifiedExtensions.red_eq_iff (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζf).le h1.le).1 h2
      exact absurd h4 (ne_of_lt h5)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [norm_zero] at h1; exact zero_ne_one h1
    have hf1 : 1 ≤ qK p K ^ f := Nat.one_le_pow _ _ (by omega)
    have h6 : ζ ^ (qK p K ^ f - 1) = 1 := by
      have h7 : qK p K ^ f = (qK p K ^ f - 1) + 1 := by omega
      rw [h7, pow_succ] at h3
      exact mul_right_cancel₀ hζ0 (by rw [h3, one_mul])
    have h8 := (hζ.pow_eq_one_iff_dvd _).1 h6
    have h9 : 1 < qK p K ^ f := Nat.one_lt_pow hf.ne' hq
    have h10 := Nat.le_of_dvd (by omega) h8
    have h11 : qK p K ^ n ≤ qK p K ^ f := by
      have : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).1 h11
  have hkey : f * Module.finrank ℚ_[p] K ≤
      Module.finrank ℚ_[p] K * Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [hmul]; exact hle
  have hfle : f ≤ Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [mul_comm] at hkey
    exact Nat.le_of_mul_le_mul_left hkey hd
  have hfn : f = n := by omega
  exact ⟨by omega, by rw [hqf, hfn]⟩

theorem finrank_extendScalars_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank K (IntermediateField.extendScalars (le_Kn p K n)) = n :=
  (finrank_unramified_extension p K hK hn).1

theorem finrank_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    Module.finrank ℚ_[p] (Kn p K n) = n * Module.finrank ℚ_[p] K := by
  have hmul := IntermediateField.finrank_bot_mul_relfinrank (le_Kn p K n)
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_Kn p K n), finrank_extendScalars_Kn p K hK hn] at hmul
  rw [← hmul, mul_comm]

theorem qK_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p (Kn p K n) = qK p K ^ n :=
  (finrank_unramified_extension p K hK hn).2

theorem norm_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : ∃ y ∈ K, ‖x‖ = ‖y‖ :=
  exists_norm_eq_of_qK p K hK (le_Kn p K n) hn (finrank_Kn p K hK hn) (qK_Kn p K hK hn) hx

theorem isGalois_Kn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsGalois K (IntermediateField.extendScalars (le_Kn p K n)) := by
  have hnorm : Normal K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact map_mem_Kn p K n σ hx
  exact ⟨⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
