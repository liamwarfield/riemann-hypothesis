module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrDefs
public import Lemmata.PadicNatCastNorm.NormNatCastOfNotDvd
public import Lemmata.FirstBlockLemmaC.Imports
public import Lemmata.FirstBlockLemmaD.Imports

@[expose] public section

section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.PowPowSuccSub
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.MemOfPowQKSubOne
section -- merged from ReciprocityTheory.ClassFieldTheory.LocalClassField.NormSubEqOneOfPowEqOne
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField

variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev res : Obar p →+* kbar p := IsLocalRing.residue (Obar p)

theorem norm_le_one (x : Obar p) : ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff.1 x.2

theorem norm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  first | exact Bl.FirstBlockLemmaD.goal1 .. | (apply Bl.FirstBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaD.goal1 <;> assumption)

theorem isUnit_iff (x : Obar p) : IsUnit x ↔ ‖(x : PadicAlgCl p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : Obar p) : PadicAlgCl p) * (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = 1 := by
      have h2 : (((u : Obar p) * ((u⁻¹ : (Obar p)ˣ) : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
        rw [u.mul_inv]; rfl
      exact h2
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have ha := norm_le_one (u : Obar p)
    have hb := norm_le_one ((u⁻¹ : (Obar p)ˣ) : Obar p)
    have hb0 := norm_nonneg ((u : Obar p) : PadicAlgCl p)
    nlinarith
  · intro h
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hi : ‖(x : PadicAlgCl p)⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(x : PadicAlgCl p)⁻¹, mem_Obar_iff.2 hi⟩ : Obar p) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0

theorem res_eq_zero_iff (x : Obar p) : res x = 0 ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  constructor
  · intro h
    by_contra hc
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm (norm_le_one x) (not_lt.1 hc)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit x).2 ((isUnit_iff x).2 h1) h
  · intro h
    by_contra hc
    have := (isUnit_iff x).1 ((IsLocalRing.residue_ne_zero_iff_isUnit x).1 hc)
    exact absurd this (ne_of_lt h)

theorem res_eq_iff (x y : Obar p) : res x = res y ↔ ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  rfl

theorem mem_resK_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ res x = c := Iff.rfl

theorem resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  exact (mem_resK_iff L _).2 ⟨x, h hx, rfl⟩

theorem norm_GK {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem norm_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

scoped instance charP_kbar : CharP (kbar p) p := by
  obtain ⟨r, hr⟩ := CharP.exists (kbar p)
  have h0 : ((p : ℕ) : kbar p) = 0 := by
    have h1 : res ((p : ℕ) : Obar p) = 0 := by
      rw [res_eq_zero_iff]
      have : (((p : ℕ) : Obar p) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
      rw [this]; exact norm_p_lt_one
    simpa using h1
  have h2 : r ∣ p := (CharP.cast_eq_zero_iff (kbar p) r p).1 h0
  have h3 : r = p := ((Nat.dvd_prime Fact.out).1 h2).resolve_left (CharP.char_ne_one (kbar p) r)
  exact h3 ▸ hr

theorem finite_resK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    Finite (resK p K) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hc : IsCompact (Metric.closedBall (0 : K) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := 1) one_pos
  classical
  let g : K → kbar p := fun x => if h : ‖(x : PadicAlgCl p)‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0
  have hsub : (resK p K : Set (kbar p)) ⊆ g '' t := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
    have hxb : (⟨x, hx⟩ : K) ∈ Metric.closedBall (0 : K) 1 := by
      rw [mem_closedBall_zero_iff]; exact norm_le_one x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxb)
    rw [Metric.mem_ball, dist_eq_norm] at hxy
    have hxy' : ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := hxy
    have hy1 : ‖(y : PadicAlgCl p)‖ ≤ 1 := by
      have h1 : (y : PadicAlgCl p) = (x : PadicAlgCl p) - ((x : PadicAlgCl p) - (y : PadicAlgCl p)) := by ring
      rw [h1]
      exact (norm_sub_le_max' _ _).trans (max_le (norm_le_one x) hxy'.le)
    refine ⟨y, hy, ?_⟩
    have hg : g y = res ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩ := dif_pos hy1
    rw [hg]
    exact ((res_eq_iff x ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩).2 hxy').symm
  exact (htf.image g).subset hsub

theorem qK_eq_pow (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f := by
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hch : CharP (resK p K) p :=
    ((resK p K).subtype.charP_iff Subtype.val_injective p).2 inferInstance
  obtain ⟨n, -, hn⟩ := FiniteField.card (resK p K) p
  exact ⟨n, n.pos, by rw [qK, Nat.card_eq_fintype_card, hn]⟩

theorem one_lt_qK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    1 < qK p K := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  rw [h]
  exact Nat.one_lt_pow hf.ne' (Fact.out : p.Prime).one_lt

theorem not_dvd_qK_pow_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {n : ℕ} (hn : 0 < n) : ¬ p ∣ qK p K ^ n - 1 := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  intro hd
  have h1 : p ∣ qK p K ^ n := by
    rw [h, ← pow_mul]; exact dvd_pow_self p (Nat.mul_pos hf hn).ne'
  have h2 : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by have := one_lt_qK K hK; omega)
  have h3 : p ∣ 1 := by
    have := (Nat.dvd_sub h1 hd)
    rwa [Nat.sub_sub_self h2] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

theorem norm_eq_one_of_pow {m : ℕ} (hm : m ≠ 0) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : ‖ζ‖ = 1 := by
  first | exact Bl.FirstBlockLemmaC.goal1 .. | (apply Bl.FirstBlockLemmaC.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaC.goal1 <;> assumption)

theorem norm_sub_one_of_pow {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by
  first | exact Bl.PadicNatCastNorm.goal1 .. | (apply Bl.PadicNatCastNorm.goal1 <;> assumption) | (intros; apply Bl.PadicNatCastNorm.goal1 <;> assumption)

theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0] at hξ; exact zero_ne_one hξ
  have h1 : ζ - ξ = ξ * (ζ / ξ - 1) := by field_simp
  rw [h1, norm_mul, norm_eq_one_of_pow hm0 hξ, one_mul]
  apply norm_sub_one_of_pow hm
  · rw [div_pow, hζ, hξ, div_one]
  · intro h2; exact h ((div_eq_one_iff_eq hξ0).1 h2)

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial

variable {p : ℕ} [Fact p.Prime]

noncomputable def red (x : PadicAlgCl p) : kbar p :=
  open Classical in if h : ‖x‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0

theorem red_coe (x : Obar p) : red (x : PadicAlgCl p) = res x := dif_pos (norm_le_one x)

theorem red_of_le {x : PadicAlgCl p} (h : ‖x‖ ≤ 1) : red x = res ⟨x, mem_Obar_iff.2 h⟩ := dif_pos h

theorem red_eq_iff {x y : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : red x = red y ↔ ‖x - y‖ < 1 := by
  rw [red_of_le hx, red_of_le hy, res_eq_iff]

theorem red_pow {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (k : ℕ) : red (x ^ k) = red x ^ k := by
  rw [red_of_le hx, ← map_pow, ← red_coe]
  rfl

theorem pow_qK_eq (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {c : kbar p} (hc : c ∈ resK p K) : c ^ qK p K = c := by
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have h := FiniteField.pow_card (⟨c, hc⟩ : resK p K)
  rw [← Nat.card_eq_fintype_card] at h
  exact congrArg Subtype.val h

theorem mem_resK_of_pow (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {c : kbar p} (h : c ^ qK p K = c) : c ∈ resK p K := by
  classical
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hq := one_lt_qK K hK
  set P : (kbar p)[X] := X ^ qK p K - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero hq
  have hdeg : P.natDegree = qK p K := Polynomial.natDegree_X_pow_sub_X (R := (kbar p)) hq
  let T : Finset (kbar p) := (Finset.univ : Finset (resK p K)).image Subtype.val
  have hT : T.card = qK p K := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, qK,
      Nat.card_eq_fintype_card]
  have hsub : T ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [pow_qK_eq K hK y.2]
  have hle : P.roots.toFinset.card ≤ T.card := by
    rw [hT, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc : c ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [h]
  rw [← heq] at hc
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hc
  exact y.2

theorem exists_primitiveRoot {m : ℕ} (hm : m ≠ 0) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ m := by
  have : NeZero m := ⟨hm⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) m

theorem exists_lift_root {m : ℕ} (hm : ¬ p ∣ m) {c : kbar p} (hc : c ^ m = 1) :
    ∃ ζ : PadicAlgCl p, ζ ^ m = 1 ∧ red ζ = c := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hmp : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨ζ0, hζ0⟩ := exists_primitiveRoot (p := p) hm0
  let T : Finset (kbar p) := (nthRootsFinset m (1 : PadicAlgCl p)).image red
  have hinj : Set.InjOn red (nthRootsFinset m (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
    intro x hx y hy hxy
    have hx' := (mem_nthRootsFinset hmp 1).1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    by_contra hne
    have h1 := norm_sub_eq_one_of_pow_eq_one hm hx' hy' hne
    have h2 := (red_eq_iff (norm_eq_one_of_pow hm0 hx').le (norm_eq_one_of_pow hm0 hy').le).1 hxy
    exact absurd h1 (ne_of_lt h2)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injOn hinj, hζ0.card_nthRootsFinset]
  have hsub : T ⊆ nthRootsFinset m (1 : kbar p) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    rw [mem_nthRootsFinset hmp, ← red_pow (norm_eq_one_of_pow hm0 hy').le, hy']
    have : red (1 : PadicAlgCl p) = res 1 := red_coe 1
    rw [this, map_one]
  have hle : (nthRootsFinset m (1 : kbar p)).card ≤ T.card := by
    rw [hT]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots m 1)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc' : c ∈ nthRootsFinset m (1 : kbar p) := (mem_nthRootsFinset hmp 1).2 hc
  rw [← heq] at hc'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc'
  exact ⟨y, (mem_nthRootsFinset hmp 1).1 hy, rfl⟩

theorem mem_of_fixed (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : PadicAlgCl p}
    (h : ∀ σ : GK p K, σ x = x) : x ∈ K := by
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := PadicAlgCl p) x).2 h
  rw [← hy]
  exact y.2

theorem mem_of_pow_qK_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K := by
  have hq := one_lt_qK K hK
  have hnd : ¬ p ∣ qK p K - 1 := by simpa using not_dvd_qK_pow_sub_one K hK (n := 1) one_pos
  have hm0 : qK p K - 1 ≠ 0 := by omega
  have h1 := norm_eq_one_of_pow hm0 hζ
  have hc : red ζ ∈ resK p K := by
    apply mem_resK_of_pow K hK
    rw [← red_pow h1.le]
    congr 1
    have : qK p K = (qK p K - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  obtain ⟨x, hx, hxc⟩ := (mem_resK_iff K _).1 hc
  rw [← red_coe, red_eq_iff (norm_le_one x) h1.le] at hxc
  apply mem_of_fixed K
  intro σ
  by_contra hne
  have hσζ : (σ ζ) ^ (qK p K - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have h2 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζ hne
  have hσx : σ (x : PadicAlgCl p) = x := σ.commutes ⟨x, hx⟩
  have h3 : σ ζ - ζ = ((x : PadicAlgCl p) - ζ) - σ ((x : PadicAlgCl p) - ζ) := by
    rw [map_sub, hσx]; ring
  have h4 : ‖σ ζ - ζ‖ < 1 := by
    rw [h3]
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt hxc ?_)
    rw [norm_GK]; exact hxc
  exact absurd h2 (ne_of_lt h4)

theorem exists_teichmuller (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {x : PadicAlgCl p} (hx : x ∈ K) (h1 : ‖x‖ = 1) :
    ∃ ζ ∈ K, ζ ^ (qK p K - 1) = 1 ∧ ‖x - ζ‖ < 1 := by
  have hq := one_lt_qK K hK
  have hnd : ¬ p ∣ qK p K - 1 := by simpa using not_dvd_qK_pow_sub_one K hK (n := 1) one_pos
  have hm0 : qK p K - 1 ≠ 0 := by omega
  have hmem : red x ∈ resK p K := (mem_resK_iff K _).2 ⟨⟨x, mem_Obar_iff.2 h1.le⟩, hx, (red_of_le h1.le).symm⟩
  have hne : red x ≠ 0 := by
    rw [red_of_le h1.le, Ne, res_eq_zero_iff]
    exact not_lt.2 h1.ge
  have hpow : red x ^ (qK p K - 1) = 1 := by
    have h2 := pow_qK_eq K hK hmem
    have : qK p K = (qK p K - 1) + 1 := by omega
    rw [this, pow_succ] at h2
    exact mul_right_cancel₀ hne (by rw [h2, one_mul])
  obtain ⟨ζ, hζ, hr⟩ := exists_lift_root hnd hpow
  refine ⟨ζ, mem_of_pow_qK_sub_one K hK hζ, hζ, ?_⟩
  exact (red_eq_iff h1.le (norm_eq_one_of_pow hm0 hζ).le).1 hr.symm

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

noncomputable def sigO (σ : GK p K) : Obar p →+* Obar p :=
  ((σ : PadicAlgCl p →+* PadicAlgCl p).comp (Obar p).subtype).codRestrict (Obar p)
    (fun x => mem_Obar_iff.2 (by
      change ‖σ (x : PadicAlgCl p)‖ ≤ 1
      rw [norm_GK]; exact norm_le_one x))

theorem coe_sigO (σ : GK p K) (x : Obar p) : ((sigO σ x : Obar p) : PadicAlgCl p) = σ x := rfl

noncomputable def sigBar (σ : GK p K) : kbar p →+* kbar p :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Obar p)) (res.comp (sigO σ)) (by
    intro a ha
    have h1 : res a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [res_eq_zero_iff] at h1
    change res (sigO σ a) = 0
    rw [res_eq_zero_iff, coe_sigO, norm_GK]
    exact h1)

theorem sigBar_res (σ : GK p K) (x : Obar p) : sigBar σ (res x) = res (sigO σ x) := rfl

theorem sigBar_red (σ : GK p K) {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : sigBar σ (red x) = red (σ x) := by
  rw [red_of_le hx, sigBar_res, ← red_coe, coe_sigO]

theorem sigBar_of_mem (σ : GK p K) {c : kbar p} (hc : c ∈ resK p K) : sigBar σ c = c := by
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  rw [sigBar_res]
  congr 1
  apply Subtype.ext
  rw [coe_sigO]
  exact σ.commutes ⟨x, hx⟩

theorem pow_pow_succ_sub {R : Type*} [Monoid R] {q n : ℕ} (hq : 0 < q) {c : R} (h : c ^ (q ^ n - 1) = 1) :
    c ^ (q ^ n) = c := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  have : q ^ n = (q ^ n - 1) + 1 := by omega
  rw [this, pow_succ, h, one_mul]

theorem exists_pow_of_GK (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (σ : GK p K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ∃ i < n, σ ζ = ζ ^ (qK p K ^ i) := by
  obtain ⟨f, hf, hqf⟩ := qK_eq_pow K hK
  have hq := one_lt_qK K hK
  set q := qK p K with hqdef
  have hnd : ¬ p ∣ q ^ n - 1 := not_dvd_qK_pow_sub_one K hK hn
  have hm0 : q ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  have h1 := norm_eq_one_of_pow hm0 hζ
  set c := red ζ with hc
  have hcn : c ^ (q ^ n) = c := by
    rw [hc, ← red_pow h1.le, pow_pow_succ_sub (by omega) hζ]
  have : ExpChar (kbar p) p := ExpChar.prime Fact.out
  let φ : kbar p →+* kbar p := iterateFrobenius (kbar p) p f
  have hφ : ∀ x, φ x = x ^ q := fun x => by rw [hqf]; rfl
  let g : ℕ → (kbar p)[X] := fun i => X - C (c ^ (q ^ i))
  set h : (kbar p)[X] := ∏ i ∈ Finset.range n, g i with hh
  have hg : ∀ i, (g i).map φ = g (i + 1) := by
    intro i
    simp only [g, Polynomial.map_sub, map_X, map_C, hφ]
    rw [← pow_mul, ← pow_succ]
  have hmap : h.map φ = h := by
    rw [hh, Polynomial.map_prod]
    simp only [hg]
    have e1 := Finset.prod_range_succ g n
    have e2 := Finset.prod_range_succ' g n
    have e3 : g n = g 0 := by simp only [g, hcn, pow_zero, pow_one]
    have e4 : g 0 ≠ 0 := X_sub_C_ne_zero _
    rw [e1, e3] at e2
    exact (mul_right_cancel₀ e4 e2).symm
  have hcoef : ∀ k, h.coeff k ∈ resK p K := by
    intro k
    apply mem_resK_of_pow K hK
    rw [← hφ, ← coeff_map, hmap]
  have hmapσ : h.map (sigBar σ) = h := by
    ext k
    rw [coeff_map, sigBar_of_mem σ (hcoef k)]
  have h0 : h.eval c = 0 := by
    rw [hh, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hn)
    simp [g]
  have h2 : h.eval (sigBar σ c) = 0 := by
    conv_lhs => rw [← hmapσ]
    rw [eval_map, eval₂_at_apply, h0, map_zero]
  rw [hh, eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, hi, h3⟩ := h2
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  simp only [g, eval_sub, eval_X, eval_C, sub_eq_zero] at h3
  rw [hc, sigBar_red σ h1.le, ← red_pow h1.le] at h3
  by_contra hne
  have hσζ : (σ ζ) ^ (q ^ n - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hζi : (ζ ^ (q ^ i)) ^ (q ^ n - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h4 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζi hne
  have h5 := (red_eq_iff (norm_eq_one_of_pow hm0 hσζ).le (norm_eq_one_of_pow hm0 hζi).le).1 h3
  exact absurd h4 (ne_of_lt h5)

variable (K)

theorem le_Kn (n : ℕ) : K ≤ Kn p K n := le_sup_left

theorem mem_Kn_of_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ hζ)

theorem Kn_le {n : ℕ} {S : IntermediateField ℚ_[p] (PadicAlgCl p)} (h1 : K ≤ S)
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → ζ ∈ S) : Kn p K n ≤ S :=
  sup_le h1 (IntermediateField.adjoin_le_iff.2 h2)

theorem map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    apply Kn_le
    · intro y hy
      change σ y ∈ Kn p K n
      have : σ y = y := σ.commutes ⟨y, hy⟩
      rw [this]; exact le_Kn K n hy
    · intro ζ hζ
      change σ ζ ∈ Kn p K n
      apply mem_Kn_of_pow
      rw [← map_pow, hζ, map_one]
  exact h hx

noncomputable def eqField (σ τ : GK p K) : IntermediateField ℚ_[p] (PadicAlgCl p) where
  toSubalgebra := AlgHom.equalizer
    ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
    ((τ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
  inv_mem' := by
    intro x hx
    have hx' : σ x = τ x := hx
    change σ x⁻¹ = τ x⁻¹
    rw [map_inv₀, map_inv₀, hx']

theorem eqOn_Kn {n : ℕ} {σ τ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → σ ζ = τ ζ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    σ x = τ x := by
  have h1 : Kn p K n ≤ eqField K σ τ := by
    apply Kn_le
    · intro y hy
      change σ y = τ y
      exact (σ.commutes ⟨y, hy⟩).trans (τ.commutes ⟨y, hy⟩).symm
    · exact h
  exact h1 hx

theorem Kn_mono {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n := by
  apply Kn_le K (le_Kn K n)
  intro ζ hζ
  apply mem_Kn_of_pow
  obtain ⟨k, rfl⟩ := h
  obtain ⟨d, hd⟩ : qK p K ^ m - 1 ∣ qK p K ^ (m * k) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ m) 1 k
  rw [hd, pow_mul, hζ, one_pow]

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
end

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem mem_resK_iff (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ IsLocalRing.residue (Obar p) x = c :=
  UnramifiedExtensions.mem_resK_iff K c

theorem residue_eq_iff (x y : Obar p) :
    IsLocalRing.residue (Obar p) x = IsLocalRing.residue (Obar p) y ↔
      ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 :=
  UnramifiedExtensions.res_eq_iff x y

theorem resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L :=
  UnramifiedExtensions.resK_mono h

theorem norm_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  UnramifiedExtensions.norm_GK σ x

theorem finite_resK (hK : FiniteDimensional ℚ_[p] K) : Finite (resK p K) :=
  UnramifiedExtensions.finite_resK K hK

theorem qK_eq_pow (hK : FiniteDimensional ℚ_[p] K) : ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f :=
  UnramifiedExtensions.qK_eq_pow K hK

theorem one_lt_qK (hK : FiniteDimensional ℚ_[p] K) : 1 < qK p K :=
  UnramifiedExtensions.one_lt_qK K hK

theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 :=
  UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hm hζ hξ h

theorem exists_teichmuller (hK : FiniteDimensional ℚ_[p] K) {x : PadicAlgCl p} (hx : x ∈ K) (h1 : ‖x‖ = 1) :
    ∃ ζ ∈ K, ζ ^ (qK p K - 1) = 1 ∧ ‖x - ζ‖ < 1 :=
  UnramifiedExtensions.exists_teichmuller K hK hx h1

theorem mem_of_pow_qK_sub_one (hK : FiniteDimensional ℚ_[p] K) {ζ : PadicAlgCl p}
    (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K :=
  UnramifiedExtensions.mem_of_pow_qK_sub_one K hK hζ

theorem le_Kn (n : ℕ) : K ≤ Kn p K n :=
  UnramifiedExtensions.le_Kn K n

theorem mem_Kn_of_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  UnramifiedExtensions.mem_Kn_of_pow K hζ

theorem map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n :=
  UnramifiedExtensions.map_mem_Kn K n σ hx

theorem Kn_mono (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n :=
  UnramifiedExtensions.Kn_mono K h

theorem Kn_le_of_qK (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) {n m : ℕ} (h : qK p L = qK p K ^ (n * m)) :
    Kn p K n ≤ L := by
  apply UnramifiedExtensions.Kn_le K hKL
  intro ζ hζ
  apply UnramifiedExtensions.mem_of_pow_qK_sub_one L hL
  obtain ⟨d, hd⟩ : qK p K ^ n - 1 ∣ qK p K ^ (n * m) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ n) 1 m
  rw [h, hd, pow_mul, hζ, one_pow]

end ReciprocityTheory.DiscreteGroups.LocalClassField
