module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtension
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitDP

open Finset

theorem conv_mul_choose {R : Type} [CommRing R] (f g : ℕ → R)
    (hf : ∀ a c, f a * f c = ((a + c).choose a : R) * f (a + c))
    (hg : ∀ b d, g b * g d = ((b + d).choose b : R) * g (b + d)) (m n : ℕ) :
    (∑ p ∈ antidiagonal m, f p.1 * g p.2) * (∑ q ∈ antidiagonal n, f q.1 * g q.2) =
      ((m + n).choose m : R) * ∑ r ∈ antidiagonal (m + n), f r.1 * g r.2 := by
  have inner : ∀ p ∈ antidiagonal m,
      ∑ q ∈ antidiagonal n, ((p.1 + q.1).choose p.1 : R) * ((p.2 + q.2).choose p.2 : R) *
          (f (p.1 + q.1) * g (p.2 + q.2)) =
        ∑ r ∈ antidiagonal (m + n), ((r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := by
    intro p hp
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have hsub : (antidiagonal n).image (fun q : ℕ × ℕ ↦ (p.1 + q.1, p.2 + q.2)) ⊆ antidiagonal (m + n) := by
      intro r hr
      simp only [mem_image, HasAntidiagonal.mem_antidiagonal] at hr ⊢
      obtain ⟨q, hq, rfl⟩ := hr
      simp only
      omega
    rw [← sum_subset hsub, sum_image]
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    · intro r hr hn
      rw [HasAntidiagonal.mem_antidiagonal] at hr
      by_cases h1 : p.1 ≤ r.1
      · by_cases h2 : p.2 ≤ r.2
        · exfalso
          apply hn
          rw [mem_image]
          exact ⟨(r.1 - p.1, r.2 - p.2), by rw [HasAntidiagonal.mem_antidiagonal]; omega,
            Prod.ext (by simp only; omega) (by simp only; omega)⟩
        · rw [Nat.choose_eq_zero_of_lt (by omega : r.2 < p.2)]
          simp
      · rw [Nat.choose_eq_zero_of_lt (by omega : r.1 < p.1)]
        simp
  calc (∑ p ∈ antidiagonal m, f p.1 * g p.2) * (∑ q ∈ antidiagonal n, f q.1 * g q.2)
      = ∑ p ∈ antidiagonal m, ∑ q ∈ antidiagonal n, ((p.1 + q.1).choose p.1 : R) *
          ((p.2 + q.2).choose p.2 : R) * (f (p.1 + q.1) * g (p.2 + q.2)) := by
        rw [sum_mul_sum]
        refine sum_congr rfl fun p _ ↦ sum_congr rfl fun q _ ↦ ?_
        calc f p.1 * g p.2 * (f q.1 * g q.2) = (f p.1 * f q.1) * (g p.2 * g q.2) := by ring
          _ = _ := by rw [hf, hg]; ring
    _ = ∑ p ∈ antidiagonal m, ∑ r ∈ antidiagonal (m + n),
          ((r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := sum_congr rfl inner
    _ = ∑ r ∈ antidiagonal (m + n),
          (∑ p ∈ antidiagonal m, (r.1.choose p.1 : R) * (r.2.choose p.2 : R)) * (f r.1 * g r.2) := by
        rw [sum_comm]
        simp only [sum_mul]
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun r hr ↦ ?_
        rw [HasAntidiagonal.mem_antidiagonal] at hr
        rw [← hr, Nat.add_choose_eq]
        push_cast
        rfl

variable {B : Type} [CommRing B] {J : Ideal B} {P : Type} [CommRing P] [Algebra B P]
  {𝔞 : Ideal P}

def th (δ : DividedPowers J) (ε : P →ₐ[B] B) (η : DividedPowers 𝔞) (n : ℕ) (x : P) : P :=
  ∑ p ∈ antidiagonal n, algebraMap B P (δ.dpow p.1 (ε x)) * η.dpow p.2 (x - algebraMap B P (ε x))

variable {δ : DividedPowers J} {ε : P →ₐ[B] B} {η : DividedPowers 𝔞}

theorem sub_mem_aug (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) : x - algebraMap B P (ε x) ∈ 𝔞 :=
  (h𝔞 _).2 (by simp)

theorem mem_ext_iff (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) :
    x ∈ J.map (algebraMap B P) ⊔ 𝔞 ↔ ε x ∈ J := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hy' : y ∈ J.comap ε := by
      refine Ideal.map_le_iff_le_comap.2 ?_ hy
      intro a ha
      simp [Ideal.mem_comap, ha]
    rw [map_add (f := _), (h𝔞 z).1 hz, add_zero]
    exact hy'
  · intro h
    have hx : x = algebraMap B P (ε x) + (x - algebraMap B P (ε x)) := by ring
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h) (sub_mem_aug h𝔞 x)

theorem th_of_mem (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) {y : P} (hy : y ∈ 𝔞) (n : ℕ) :
    th δ ε η n y = η.dpow n y := by
  simp only [th, (h𝔞 y).1 hy, map_zero, sub_zero]
  rw [sum_eq_single (0, n)]
  · rw [δ.dpow_zero J.zero_mem, map_one, one_mul]
  · intro p hp hne
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have : p.1 ≠ 0 := fun h ↦ hne (Prod.ext h (by simp only; omega))
    rw [δ.dpow_eval_zero this, map_zero, zero_mul]
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.2 (zero_add n)) h

theorem th_algebraMap (j : B) (n : ℕ) : th δ ε η n (algebraMap B P j) = algebraMap B P (δ.dpow n j) := by
  simp only [th, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [sum_eq_single (n, 0)]
  · rw [η.dpow_zero 𝔞.zero_mem, mul_one]
  · intro p hp hne
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    have : p.2 ≠ 0 := fun h ↦ hne (Prod.ext (by simp only; omega) h)
    rw [η.dpow_eval_zero this, mul_zero]
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.2 (add_zero n)) h

theorem th_null (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (x : P) (hx : x ∉ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n x = 0 := by
  rw [mem_ext_iff h𝔞] at hx
  refine sum_eq_zero fun p _ ↦ ?_
  rw [δ.dpow_null hx, map_zero, zero_mul]

theorem th_zero (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η 0 x = 1 := by
  rw [mem_ext_iff h𝔞] at hx
  simp [th, δ.dpow_zero hx, η.dpow_zero (sub_mem_aug h𝔞 x)]

theorem th_one (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η 1 x = x := by
  rw [mem_ext_iff h𝔞] at hx
  simp [th, Finset.Nat.antidiagonal_succ, δ.dpow_zero hx, δ.dpow_one hx, η.dpow_zero (sub_mem_aug h𝔞 x),
    η.dpow_one (sub_mem_aug h𝔞 x)]

theorem th_mem (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (hn : n ≠ 0) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) : th δ ε η n x ∈ J.map (algebraMap B P) ⊔ 𝔞 := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  refine Ideal.sum_mem _ fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  by_cases h1 : p.1 = 0
  · exact Ideal.mul_mem_left _ _
      (Ideal.mem_sup_right (η.dpow_mem (by omega) (sub_mem_aug h𝔞 x)))
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (δ.dpow_mem h1 hu)))

theorem mk_th (x : P) :
    PowerSeries.mk (fun k ↦ th δ ε η k x) =
      PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε x))) *
        PowerSeries.mk (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) := by
  ext k
  simp [PowerSeries.coeff_mul, th]

theorem th_add (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞)
    (y : P) (hy : y ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (x + y) = ∑ k ∈ antidiagonal n, th δ ε η k.1 x * th δ ε η k.2 y := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have hv := (mem_ext_iff h𝔞 y).1 hy
  have hA : PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε (x + y)))) =
      PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε x))) *
        PowerSeries.mk (fun k ↦ algebraMap B P (δ.dpow k (ε y))) := by
    ext k
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, map_add (f := _)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [δ.dpow_add hu hv, map_sum]
    simp only [map_mul]
  have hE : PowerSeries.mk (fun k ↦ η.dpow k (x + y - algebraMap B P (ε (x + y)))) =
      PowerSeries.mk (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) *
        PowerSeries.mk (fun k ↦ η.dpow k (y - algebraMap B P (ε y))) := by
    ext k
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    have e : x + y - algebraMap B P (ε (x + y)) =
        (x - algebraMap B P (ε x)) + (y - algebraMap B P (ε y)) := by
      rw [map_add (f := _), map_add (f := _)]; ring
    rw [e, η.dpow_add (sub_mem_aug h𝔞 x) (sub_mem_aug h𝔞 y)]
  have key : PowerSeries.mk (fun k ↦ th δ ε η k (x + y)) =
      PowerSeries.mk (fun k ↦ th δ ε η k x) * PowerSeries.mk (fun k ↦ th δ ε η k y) := by
    rw [mk_th, mk_th, mk_th, hA, hE]
    ring
  have := congrArg (PowerSeries.coeff n) key
  simpa [PowerSeries.coeff_mul] using this

theorem th_mul_dpow (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (m n : ℕ) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η m x * th δ ε η n x = ((m + n).choose m : P) * th δ ε η (m + n) x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  refine conv_mul_choose (fun k ↦ algebraMap B P (δ.dpow k (ε x)))
    (fun k ↦ η.dpow k (x - algebraMap B P (ε x))) (fun a c ↦ ?_) (fun b d ↦ ?_) m n
  · beta_reduce
    rw [← map_mul, δ.mul_dpow hu, map_mul, map_natCast]
  · exact η.mul_dpow (sub_mem_aug h𝔞 x)

theorem th_mul_alg (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (β : B) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (algebraMap B P β * x) = algebraMap B P β ^ n * th δ ε η n x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have e1 : ε (algebraMap B P β * x) = β * ε x := by simp
  have e2 : algebraMap B P β * x - algebraMap B P (ε (algebraMap B P β * x)) =
      algebraMap B P β * (x - algebraMap B P (ε x)) := by
    rw [e1, map_mul]; ring
  rw [th, th, e2, e1, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [δ.dpow_mul hu, η.dpow_mul (sub_mem_aug h𝔞 x), map_mul, map_pow, ← hp, pow_add]
  ring

theorem th_mul_aug (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) {q : P} (hq : q ∈ 𝔞) (x : P)
    (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (q * x) = q ^ n * th δ ε η n x := by
  have hu := (mem_ext_iff h𝔞 x).1 hx
  have hr := sub_mem_aug h𝔞 x
  rw [th_of_mem h𝔞 (Ideal.mul_mem_right x 𝔞 hq)]
  have e : q * x = algebraMap B P (ε x) * q + q * (x - algebraMap B P (ε x)) := by ring
  rw [e, η.dpow_add (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hr), th, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  have hk : algebraMap B P (ε x) ^ p.1 * η.dpow p.1 q = algebraMap B P (δ.dpow p.1 (ε x)) * q ^ p.1 := by
    rw [← η.factorial_mul_dpow_eq_pow hq, ← map_pow, ← δ.factorial_mul_dpow_eq_pow hu, map_mul, map_natCast]
    ring
  rw [η.dpow_mul hq, η.dpow_mul hr, ← mul_assoc, hk, ← hp, pow_add]
  ring

theorem th_mul (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) (n : ℕ) (c x : P) (hx : x ∈ J.map (algebraMap B P) ⊔ 𝔞) :
    th δ ε η n (c * x) = c ^ n * th δ ε η n x := by
  obtain ⟨β, q, hq, rfl⟩ : ∃ β q, q ∈ 𝔞 ∧ c = algebraMap B P β + q :=
    ⟨ε c, _, sub_mem_aug h𝔞 c, by ring⟩
  have h1 : algebraMap B P β * x ∈ J.map (algebraMap B P) ⊔ 𝔞 := Ideal.mul_mem_left _ _ hx
  have h2 : q * x ∈ J.map (algebraMap B P) ⊔ 𝔞 := Ideal.mul_mem_left _ _ hx
  rw [add_mul, th_add h𝔞 n _ h1 _ h2, (Commute.all _ _).add_pow', sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [th_mul_alg h𝔞 _ _ _ hx, th_mul_aug h𝔞 _ hq _ hx, nsmul_eq_mul]
  calc algebraMap B P β ^ p.1 * th δ ε η p.1 x * (q ^ p.2 * th δ ε η p.2 x)
      = algebraMap B P β ^ p.1 * q ^ p.2 * (th δ ε η p.1 x * th δ ε η p.2 x) := by ring
    _ = _ := by rw [th_mul_dpow h𝔞 _ _ _ hx, hp]; ring

theorem isPreDividedPowers_th (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) :
    IsPreDP (J.map (algebraMap B P) ⊔ 𝔞) (th δ ε η) := by
  exact
    { null := th_null h𝔞
      zero := th_zero h𝔞
      one := th_one h𝔞
      mem := th_mem h𝔞
      add := th_add h𝔞
      mul := th_mul h𝔞
      mul_dpow := th_mul_dpow h𝔞 }

theorem ext_eq_span : J.map (algebraMap B P) ⊔ 𝔞 = Ideal.span (algebraMap B P '' (J : Set B) ∪ (𝔞 : Set P)) := by
  rw [Ideal.span_union, Ideal.span_eq]
  rfl

theorem th_comp (h𝔞 : ∀ p, p ∈ 𝔞 ↔ ε p = 0) :
    ∀ x ∈ algebraMap B P '' (J : Set B) ∪ (𝔞 : Set P), ∀ m n : ℕ, n ≠ 0 →
      th δ ε η m (th δ ε η n x) = (m.uniformBell n : P) * th δ ε η (m * n) x := by
  rintro x (⟨j, hj, rfl⟩ | hx) m n hn
  · rw [th_algebraMap, th_algebraMap, th_algebraMap, δ.dpow_comp hn hj, map_mul, map_natCast]
  · rw [th_of_mem h𝔞 hx n, th_of_mem h𝔞 (η.dpow_mem hn hx), th_of_mem h𝔞 hx, η.dpow_comp hn hx]

theorem exists_dp_ext : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P]
    [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) →
    ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧
      ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  intro B _ J δ P _ _ ε 𝔞 η h𝔞
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators P (J.map (algebraMap B P) ⊔ 𝔞) (th δ ε η) _ (isPreDividedPowers_th h𝔞)
    ext_eq_span (th_comp h𝔞)
  refine ⟨θ, ⟨le_sup_left, fun {n} a _ ↦ ?_⟩, fun n p hp ↦ ?_⟩
  · rw [hθ, th_algebraMap]
  · rw [hθ, th_of_mem h𝔞 hp]

end GlobalTheory.SplitDP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersSplitAugmentationExtensionStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_split_augmentation_extension : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  first | exact @GlobalTheory.SplitDP.exists_dp_ext | exact GlobalTheory.SplitDP.exists_dp_ext | (intros; apply GlobalTheory.SplitDP.exists_dp_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdeal
set_option autoImplicit false

noncomputable section

open DividedPowers

namespace GlobalTheory.PDA

def IsExpSer {R : Type} [CommRing R] (f : PowerSeries R) : Prop :=
  PowerSeries.coeff 0 f = 1 ∧ ∀ m n, PowerSeries.coeff m f * PowerSeries.coeff n f =
    ((m + n).choose m : R) * PowerSeries.coeff (m + n) f

variable {B : Type} [CommRing B]

def PDPoly.expTerm (Q : PDPoly B) (k : ℕ) (b : B) : PowerSeries Q.P :=
  if k = 0 then 1 else
    PowerSeries.mk fun n ↦ algebraMap B Q.P (b ^ n) * ((n.uniformBell k : Q.P) * Q.e (n * k))

def PDPoly.augExp (Q : PDPoly B) (p : Q.P) : PowerSeries Q.P := (Q.e.repr p).prod Q.expTerm


open Classical in
def PDPoly.augDP (Q : PDPoly B) (n : ℕ) (p : Q.P) : Q.P :=
  if p ∈ Q.aug then PowerSeries.coeff n (Q.augExp p) else 0

open PowerSeries Finset

theorem IsExpSer.mul {R : Type} [CommRing R] {f g : PowerSeries R} (hf : IsExpSer f) (hg : IsExpSer g) :
    IsExpSer (f * g) := by
  refine ⟨by simp [PowerSeries.coeff_mul, hf.1, hg.1], fun m n ↦ ?_⟩
  simp only [PowerSeries.coeff_mul, Finset.sum_mul_sum]
  have key : ∀ x ∈ antidiagonal m, ∑ y ∈ antidiagonal n, coeff x.1 f * coeff x.2 g * (coeff y.1 f * coeff y.2 g) =
      ∑ z ∈ antidiagonal (m + n), ((z.1.choose x.1 * z.2.choose x.2 : ℕ) : R) * (coeff z.1 f * coeff z.2 g) := by
    rintro ⟨i, j⟩ hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    dsimp only at hx
    have e1 : ∀ y ∈ antidiagonal n, coeff i f * coeff j g * (coeff y.1 f * coeff y.2 g) =
        (fun z : ℕ × ℕ ↦ ((z.1.choose i * z.2.choose j : ℕ) : R) * (coeff z.1 f * coeff z.2 g))
          (i + y.1, j + y.2) := by
      intro y _
      simp only
      rw [show coeff i f * coeff j g * (coeff y.1 f * coeff y.2 g) =
        (coeff i f * coeff y.1 f) * (coeff j g * coeff y.2 g) by ring, hf.2, hg.2]
      push_cast; ring
    let F : ℕ × ℕ → R := fun z ↦ ((z.1.choose i * z.2.choose j : ℕ) : R) * (coeff z.1 f * coeff z.2 g)
    let G : ℕ × ℕ → ℕ × ℕ := fun y ↦ (i + y.1, j + y.2)
    have inj : ∀ a ∈ antidiagonal n, ∀ b ∈ antidiagonal n, G a = G b → a = b := by
      intro a _ b _ h; simp only [G, Prod.mk.injEq] at h; ext <;> omega
    refine ((Finset.sum_congr rfl e1).trans (Finset.sum_image (f := F) inj).symm).trans ?_
    refine Finset.sum_subset ?_ ?_
    · intro z hz
      simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal] at hz ⊢
      obtain ⟨y, hy, rfl⟩ := hz
      show i + y.1 + (j + y.2) = m + n
      omega
    · rintro ⟨a, b⟩ hz hn
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hz
      simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal, not_exists, not_and, G, Prod.mk.injEq] at hn
      by_cases ha : i ≤ a
      · by_cases hb : j ≤ b
        · exfalso; refine hn (a - i, b - j) ?_ ?_ ?_ <;> dsimp only <;> omega
        · simp only [F]; rw [Nat.choose_eq_zero_of_lt (by omega : b < j)]; simp
      · simp only [F]; rw [Nat.choose_eq_zero_of_lt (by omega : a < i)]; simp
  rw [Finset.sum_congr rfl key, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
  rw [← Finset.sum_mul, ← Nat.cast_sum, ← Nat.add_choose_eq, hz]

theorem isExpSer_one {R : Type} [CommRing R] : IsExpSer (1 : PowerSeries R) := by
  refine ⟨by simp, fun m n ↦ ?_⟩
  simp only [PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : m + n ≠ 0 := by omega
    simp [hm.ne', this]

theorem mk_exp_add {R : Type} [CommRing R] (u : ℕ → R)
    (hu : ∀ m n, u m * u n = ((m + n).choose m : R) * u (m + n)) (a b : R) :
    PowerSeries.mk (fun n ↦ (a + b) ^ n * u n) =
      PowerSeries.mk (fun n ↦ a ^ n * u n) * PowerSeries.mk (fun n ↦ b ^ n * u n) := by
  ext n
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  simp only [PowerSeries.coeff_mk]
  rw [show a ^ x.1 * u x.1 * (b ^ x.2 * u x.2) = a ^ x.1 * b ^ x.2 * (u x.1 * u x.2) by ring, hu, hx, nsmul_eq_mul]
  ring

theorem uniformBell_mul_uniformBell (m n k : ℕ) (hk : k ≠ 0) :
    m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k) = (m + n).choose m * (m + n).uniformBell k := by
  have q : ∀ a : ℕ, (a.uniformBell k : ℚ) = (a * k).factorial / ((k.factorial : ℚ) ^ a * a.factorial) := by
    intro a
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [← mul_assoc]; exact Nat.uniformBell_mul_eq a hk)
  have : ((m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k) : ℕ) : ℚ) =
      (((m + n).choose m * (m + n).uniformBell k : ℕ) : ℚ) := by
    push_cast
    rw [q, q, q, Nat.cast_add_choose, Nat.cast_add_choose, add_mul, pow_add]
    field_simp
  exact_mod_cast this

theorem choose_pow_mul_uniformBell (m K n : ℕ) (hm : m ≠ 0) (hK : K ≠ 0) :
    (m + K).choose m ^ n * n.uniformBell (m + K) =
      n.factorial * n.uniformBell m * n.uniformBell K * (n * m + n * K).choose (n * m) := by
  have q : ∀ k : ℕ, k ≠ 0 → (n.uniformBell k : ℚ) = (n * k).factorial / ((k.factorial : ℚ) ^ n * n.factorial) := by
    intro k hk
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by rw [← mul_assoc]; exact Nat.uniformBell_mul_eq n hk)
  have : ((((m + K).choose m ^ n * n.uniformBell (m + K)) : ℕ) : ℚ) =
      ((n.factorial * n.uniformBell m * n.uniformBell K * (n * m + n * K).choose (n * m) : ℕ) : ℚ) := by
    push_cast
    rw [q _ hm, q _ hK, q _ (by omega), Nat.cast_add_choose, Nat.cast_add_choose, mul_add, div_pow]
    field_simp
    ring
  exact_mod_cast this

theorem PDPoly.expTerm_of_ne (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (b : B) :
    Q.expTerm k b = PowerSeries.mk fun n ↦ algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k)) := by
  simp [PDPoly.expTerm, hk, map_pow]

theorem PDPoly.coeff_expTerm (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (b : B) (n : ℕ) :
    coeff n (Q.expTerm k b) = algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k)) := by
  rw [Q.expTerm_of_ne hk, coeff_mk]

theorem PDPoly.expSeq_mul (Q : PDPoly B) {k : ℕ} (hk : k ≠ 0) (m n : ℕ) :
    (m.uniformBell k : Q.P) * Q.e (m * k) * ((n.uniformBell k : Q.P) * Q.e (n * k)) =
      ((m + n).choose m : Q.P) * ((m + n).uniformBell k * Q.e ((m + n) * k)) := by
  have h := uniformBell_mul_uniformBell m n k hk
  calc _ = ((m.uniformBell k * n.uniformBell k : ℕ) : Q.P) * (Q.e (m * k) * Q.e (n * k)) := by push_cast; ring
    _ = (((m.uniformBell k * n.uniformBell k * (m * k + n * k).choose (m * k)) : ℕ) : Q.P) * Q.e (m * k + n * k) := by
        rw [Q.e_mul]; push_cast; ring
    _ = _ := by rw [h, add_mul]; push_cast; ring

theorem PDPoly.expTerm_zero (Q : PDPoly B) (k : ℕ) : Q.expTerm k 0 = 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [PDPoly.expTerm]
  · ext n
    rw [Q.coeff_expTerm hk, coeff_one]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Q.e_zero, Nat.uniformBell_zero_left]
    · simp [hn]

theorem PDPoly.expTerm_add (Q : PDPoly B) (k : ℕ) (a b : B) :
    Q.expTerm k (a + b) = Q.expTerm k a * Q.expTerm k b := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [PDPoly.expTerm]
  · rw [Q.expTerm_of_ne hk, Q.expTerm_of_ne hk, Q.expTerm_of_ne hk, map_add (f := _)]
    exact mk_exp_add _ (fun m n ↦ Q.expSeq_mul hk m n) _ _

theorem PDPoly.isExpSer_expTerm (Q : PDPoly B) (k : ℕ) (b : B) : IsExpSer (Q.expTerm k b) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simpa [PDPoly.expTerm] using isExpSer_one
  · refine ⟨by simp [Q.coeff_expTerm hk, Q.e_zero, Nat.uniformBell_zero_left], fun m n ↦ ?_⟩
    rw [Q.coeff_expTerm hk, Q.coeff_expTerm hk, Q.coeff_expTerm hk,
      show algebraMap B Q.P b ^ m * ((m.uniformBell k : Q.P) * Q.e (m * k)) *
        (algebraMap B Q.P b ^ n * ((n.uniformBell k : Q.P) * Q.e (n * k))) =
        algebraMap B Q.P b ^ (m + n) * ((m.uniformBell k : Q.P) * Q.e (m * k) * ((n.uniformBell k : Q.P) * Q.e (n * k)))
        by ring, Q.expSeq_mul hk]
    ring

theorem PDPoly.isExpSer_prod (Q : PDPoly B) (c : ℕ →₀ B) : IsExpSer (c.prod Q.expTerm) :=
  Finset.prod_induction _ IsExpSer (fun _ _ ↦ IsExpSer.mul) isExpSer_one fun k _ ↦ Q.isExpSer_expTerm k (c k)

theorem PDPoly.isExpSer_augExp (Q : PDPoly B) (p : Q.P) : IsExpSer (Q.augExp p) := Q.isExpSer_prod _

theorem PDPoly.augExp_add (Q : PDPoly B) (p q : Q.P) : Q.augExp (p + q) = Q.augExp p * Q.augExp q := by
  rw [PDPoly.augExp, map_add (f := _), Finsupp.prod_add_index' Q.expTerm_zero Q.expTerm_add]; rfl

theorem PDPoly.augExp_zero (Q : PDPoly B) : Q.augExp 0 = 1 := by
  simp [PDPoly.augExp]

theorem PDPoly.augExp_smul_e (Q : PDPoly B) (b : B) (k : ℕ) : Q.augExp (b • Q.e k) = Q.expTerm k b := by
  rw [PDPoly.augExp, map_smul, Q.e.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.prod_single_index (Q.expTerm_zero k)]

theorem PDPoly.mem_aug_iff (Q : PDPoly B) (p : Q.P) : p ∈ Q.aug ↔ Q.e.repr p 0 = 0 := by
  have hms : ∀ (q : Q.P) (n : ℕ), Q.e.repr (q * Q.e (n + 1)) 0 = 0 := by
    intro q n
    have : (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0 := by
      refine Q.e.ext fun m ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
        LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finsupp.single_eq_of_ne (by omega), smul_zero]
    exact LinearMap.congr_fun this q
  constructor
  · intro h
    have h2 : ∀ q, Q.e.repr (q * p) 0 = 0 := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ h
      · rintro _ ⟨j, rfl⟩ q; exact hms q j
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add (f := _), Finsupp.add_apply, hx, hy, add_zero]
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    simpa using h2 1
  · intro h
    rw [← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Ideal.sum_mem _ fun n hn ↦ ?_
    rcases n with _ | n
    · exact absurd h (Finsupp.mem_support_iff.1 hn)
    · rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (Q.e_succ_mem_aug n)

theorem PDPoly.coeff_one_prod (Q : PDPoly B) (c : ℕ →₀ B) :
    coeff 1 (c.prod Q.expTerm) = c.sum fun k b ↦ if k = 0 then 0 else b • Q.e k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' Q.expTerm_zero Q.expTerm_add, Finsupp.sum_add_index' (by simp)
      (fun k a b ↦ by split_ifs <;> simp [add_smul]), ← hf, ← hg, coeff_mul,
      Finset.Nat.sum_antidiagonal_succ]
    simp [(Q.isExpSer_prod f).1, (Q.isExpSer_prod g).1, add_comm]
  | single k b =>
    rw [Finsupp.prod_single_index (Q.expTerm_zero k), Finsupp.sum_single_index (by simp)]
    rcases eq_or_ne k 0 with rfl | hk
    · simp [PDPoly.expTerm]
    · rw [Q.coeff_expTerm hk]; simp [hk, Algebra.smul_def, Nat.uniformBell_one_left]

theorem PDPoly.e_pow (Q : PDPoly B) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    Q.e m ^ n = ((n.factorial * n.uniformBell m : ℕ) : Q.P) * Q.e (n * m) := by
  induction n with
  | zero => simp [Q.e_zero, Nat.uniformBell_zero_left]
  | succ n ih =>
    have h := uniformBell_mul_uniformBell n 1 m hm
    simp only [Nat.uniformBell_one_left, one_mul, mul_one, Nat.choose_succ_self_right] at h
    rw [pow_succ, ih, mul_assoc, Q.e_mul, ← mul_assoc, ← Nat.cast_mul, Nat.succ_mul]
    congr 2
    rw [Nat.factorial_succ, mul_assoc, h]; ring

theorem PDPoly.augExp_e (Q : PDPoly B) (k : ℕ) : Q.augExp (Q.e k) = Q.expTerm k 1 := by
  simpa using Q.augExp_smul_e 1 k

theorem PDPoly.coeff_prod_mem_aug (Q : PDPoly B) (c : ℕ →₀ B) (n : ℕ) (hn : n ≠ 0) :
    coeff n (c.prod Q.expTerm) ∈ Q.aug := by
  revert n
  refine Finset.prod_induction _ (fun f : PowerSeries Q.P ↦ ∀ n, n ≠ 0 → coeff n f ∈ Q.aug) ?_ ?_ ?_
  · intro f g hf hg n hn
    rw [coeff_mul]
    refine Ideal.sum_mem _ fun x hx ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rcases eq_or_ne x.1 0 with h0 | h0
    · exact Ideal.mul_mem_left _ _ (hg _ (by omega))
    · exact Ideal.mul_mem_right _ _ (hf _ h0)
  · intro n hn; simp [coeff_one, hn]
  · intro k _ n hn
    rcases eq_or_ne k 0 with rfl | hk
    · simp [PDPoly.expTerm, coeff_one, hn]
    · rw [Q.coeff_expTerm hk]
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (mul_ne_zero hn hk)
      rw [hj]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Q.e_succ_mem_aug j))

theorem PDPoly.coeff_augExp_smul_e_mul_e (Q : PDPoly B) (b : B) (m : ℕ) {K : ℕ} (hK : K ≠ 0) (n : ℕ) :
    coeff n (Q.augExp ((b • Q.e m) * Q.e K)) = (b • Q.e m) ^ n * coeff n (Q.augExp (Q.e K)) := by
  rw [smul_mul_assoc, Q.e_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul B, smul_smul, Q.augExp_smul_e,
    Q.coeff_expTerm (by omega), Q.augExp_e, Q.coeff_expTerm hK, smul_pow, Algebra.smul_def, map_pow, map_one,
    one_pow, one_mul, map_mul, map_natCast]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Q.e_zero]
  · rw [Q.e_pow hm, show n * (m + K) = n * m + n * K from mul_add _ _ _]
    have h := choose_pow_mul_uniformBell m K n hm hK
    calc (algebraMap B Q.P b * ((m + K).choose m : Q.P)) ^ n * ((n.uniformBell (m + K) : Q.P) * Q.e (n * m + n * K))
        = algebraMap B Q.P b ^ n * (((m + K).choose m ^ n * n.uniformBell (m + K) : ℕ) : Q.P) *
            Q.e (n * m + n * K) := by push_cast; ring
      _ = algebraMap B Q.P b ^ n * ((n.factorial * n.uniformBell m * n.uniformBell K : ℕ) : Q.P) *
            (((n * m + n * K).choose (n * m) : Q.P) * Q.e (n * m + n * K)) := by rw [h]; push_cast; ring
      _ = _ := by rw [← Q.e_mul]; push_cast; ring

theorem PDPoly.coeff_augExp_mul (Q : PDPoly B) (a : Q.P) {x : Q.P} (hx : x ∈ Q.aug) (n : ℕ) :
    coeff n (Q.augExp (a * x)) = a ^ n * coeff n (Q.augExp x) := by

  have hsum : ∀ y : Q.P, ∀ s : Finset ℕ, ∀ f : ℕ → Q.P,
      (∀ i ∈ s, ∀ n, coeff n (Q.augExp (f i * y)) = f i ^ n * coeff n (Q.augExp y)) →
      ∀ n, coeff n (Q.augExp ((∑ i ∈ s, f i) * y)) = (∑ i ∈ s, f i) ^ n * coeff n (Q.augExp y) := by
    intro y s f hf
    refine Finset.sum_induction _ (fun a ↦ ∀ n, coeff n (Q.augExp (a * y)) = a ^ n * coeff n (Q.augExp y))
      ?_ ?_ hf
    · intro a a' ha ha' n
      rw [add_mul, Q.augExp_add, coeff_mul, (Commute.all a a').add_pow', Finset.sum_mul]
      refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
      rw [ha, ha', nsmul_eq_mul,
        show a ^ z.1 * coeff z.1 (Q.augExp y) * (a' ^ z.2 * coeff z.2 (Q.augExp y)) =
          a ^ z.1 * a' ^ z.2 * (coeff z.1 (Q.augExp y) * coeff z.2 (Q.augExp y)) by ring,
        (Q.isExpSer_augExp y).2, hz]
      ring
    · intro n
      rw [zero_mul, Q.augExp_zero, coeff_one]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [(Q.isExpSer_augExp y).1]
      · simp [hn]

  have hgen : ∀ k a n, coeff n (Q.augExp (a * Q.e (k + 1))) = a ^ n * coeff n (Q.augExp (Q.e (k + 1))) := by
    intro k a
    rw [← Q.e.linearCombination_repr a, Finsupp.linearCombination_apply, Finsupp.sum]
    exact hsum _ _ _ fun m _ n ↦ Q.coeff_augExp_smul_e_mul_e _ m (by omega) n
  revert a n
  refine Submodule.span_induction (p := fun x _ ↦ ∀ a n, coeff n (Q.augExp (a * x)) = a ^ n * coeff n (Q.augExp x))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨k, rfl⟩; exact hgen k
  · intro a n
    rw [mul_zero, Q.augExp_zero, coeff_one]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn]
  · intro x y _ _ hx hy a n
    rw [mul_add, Q.augExp_add, Q.augExp_add, coeff_mul, coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
    rw [hx, hy, ← hz, pow_add]; ring
  · intro r x _ hx a n
    rw [smul_eq_mul, ← mul_assoc, hx (a * r) n, hx r n, mul_pow, mul_assoc]

theorem PDPoly.augDP_of_mem (Q : PDPoly B) {x : Q.P} (hx : x ∈ Q.aug) (n : ℕ) :
    Q.augDP n x = coeff n (Q.augExp x) := by
  simp [PDPoly.augDP, hx]

theorem exists_isPreDividedPowers_augmentation : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  intro B _ Q
  refine ⟨Q.augDP, ⟨fun n x hx ↦ by simp [PDPoly.augDP, hx], fun x hx ↦ ?_, fun x hx ↦ ?_, fun n hn x hx ↦ ?_,
    fun n x hx y hy ↦ ?_, fun n a x hx ↦ ?_, fun m n x hx ↦ ?_⟩, fun n k ↦ ?_⟩
  · rw [Q.augDP_of_mem hx]; exact (Q.isExpSer_augExp x).1
  · rw [Q.augDP_of_mem hx, PDPoly.augExp, Q.coeff_one_prod]
    have h0 := (Q.mem_aug_iff x).1 hx
    calc _ = (Q.e.repr x).sum fun k b ↦ b • Q.e k := Finsupp.sum_congr fun k hk ↦ by
            split_ifs with h
            · subst h; exact absurd h0 (Finsupp.mem_support_iff.1 hk)
            · rfl
      _ = x := by rw [← Finsupp.linearCombination_apply, Q.e.linearCombination_repr]
  · rw [Q.augDP_of_mem hx]; exact Q.coeff_prod_mem_aug _ n hn
  · rw [Q.augDP_of_mem (add_mem hx hy), Q.augExp_add, coeff_mul]
    simp only [Q.augDP_of_mem hx, Q.augDP_of_mem hy]
  · rw [Q.augDP_of_mem (Ideal.mul_mem_left _ a hx), Q.augDP_of_mem hx, Q.coeff_augExp_mul a hx]
  · rw [Q.augDP_of_mem hx, Q.augDP_of_mem hx, Q.augDP_of_mem hx]; exact (Q.isExpSer_augExp x).2 m n
  · rw [Q.augDP_of_mem (Q.e_succ_mem_aug k), Q.augExp_e, Q.coeff_expTerm (by omega), map_one, one_pow, one_mul]

end GlobalTheory.PDA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdealStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧ ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | exact GlobalTheory.PDA.exists_isPreDividedPowers_augmentation | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_augmentation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIde
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc n.uniformBell N ^ m * m.uniformBell (n * N) * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n))
      = m.uniformBell (n * N) * (n.uniformBell N * N.factorial ^ n * n.factorial) ^ m * m.factorial := by ring
    _ = (m * (n * N)).factorial := by rw [h1, h2]
    _ = ((m * n) * N).factorial := by rw [Nat.mul_assoc]
    _ = (m * n).uniformBell N * N.factorial ^ (m * n) * (m.uniformBell n * n.factorial ^ m * m.factorial) := by
      rw [h3, h4]
    _ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨γ, hγ, he⟩ := GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal B Q
  have hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 →
      γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x := by
    rintro _ ⟨k, rfl⟩ m n hn
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 := ⟨n * (k + 1) - 1, by
      have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
      omega⟩
    have hmem : Q.e (n * (k + 1)) ∈ Q.aug := hj ▸ Q.e_succ_mem_aug j
    have key := congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)
    push_cast at key
    rw [he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]
    linear_combination key * Q.e (m * n * (k + 1))
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp
  refine ⟨δ, fun n ↦ ?_⟩
  rw [hδ]
  have := he n 0
  simpa [Nat.uniformBell_one_right] using this

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersDividedPowerPolyAlgebraAugIdeStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal : ∀ (B : Type) [CommRing B] (Q : PDPoly B), ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  first | exact @GlobalTheory.PDA.exists_dividedPowers_aug | exact GlobalTheory.PDA.exists_dividedPowers_aug | (intros; apply GlobalTheory.PDA.exists_dividedPowers_aug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal B Q
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_lift_and_augmentation_map B Q).2
  obtain ⟨θ, hθ, hθη⟩ := GlobalTheory.T.exists_dividedPowers_split_augmentation_extension B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdStatement
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dividedPowers_ext_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B), ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_isStd | exact GlobalTheory.PDA.PDPoly.exists_isStd | (intros; apply GlobalTheory.PDA.PDPoly.exists_isStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilIsSubDPIdeal
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_isSubDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (N : ℕ), 1 ≤ N →
    δ.IsSubDPIdeal (fil δ N) := by
  intro B _ J δ N hN
  refine ⟨GlobalTheory.Cris.ExpBij.dpFil_le δ hN, fun n hn j hj ↦ ?_⟩
  have h := GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hN hj n
  exact GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hn)) h

end GlobalTheory.PDA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdPoly
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevel
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeThick

theorem ringHom_eq_of_basis {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

end GlobalTheory.PDForm.FreeThick

namespace GlobalTheory.PDForm


open GlobalTheory.PDForm.FreeThick in
theorem exists_isFree_one_qAt : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Unit → F.B),
      IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n T hT
  obtain ⟨Q⟩ := GlobalTheory.exists_pdPoly T.B
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_ext_isStd T.B T.J T.δ Q
  obtain ⟨hlift, ε, hε⟩ := GlobalTheory.PDA.PDPoly.exists_lift_and_aug T.B Q
  have hfil := GlobalTheory.PDA.fil_properties Q.P (Q.ext T.J) η
  obtain ⟨K, hK⟩ : ∃ K : Ideal Q.P, K = fil η (n + 1) := ⟨_, rfl⟩
  have hsub : η.IsSubDPIdeal K := by rw [hK]; exact GlobalTheory.PDA.fil_isSubDPIdeal Q.P (Q.ext T.J) η (n + 1) (by omega)
  obtain ⟨δ', hδ', huniv⟩ := (GlobalTheory.DPQuot.quotient_subDPIdeal Q.P (Q.ext T.J) η).1 K hsub
  have hKle : K ≤ Q.ext T.J := by rw [hK]; exact (hfil.2.2.1 1 (n + 1) (by omega)).trans hfil.2.1.le
  letI : Algebra R Q.P := ((algebraMap T.B Q.P).comp (algebraMap R T.B)).toAlgebra
  haveI : IsScalarTower R T.B Q.P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hε1 : ∀ b, ε (algebraMap T.B Q.P b) = b := fun b ↦ by simp
  have hεJ : ∀ p : Q.P, ε p ∈ T.J ↔ p ∈ Q.ext T.J := by
    intro p
    constructor
    · intro hp
      have : p = algebraMap T.B Q.P (ε p) + (p - algebraMap T.B Q.P (ε p)) := by ring
      rw [this]
      refine add_mem (Q.algebraMap_mem_ext hp) (Ideal.mem_sup_right ((hε _).2 ?_))
      rw [map_sub, hε1, sub_self]
    · intro hp
      have hle : Q.ext T.J ≤ T.J.comap (ε : Q.P →+* T.B) := by
        refine sup_le (Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_) fun q hq ↦ ?_
        · rw [Ideal.mem_comap]; change ε (algebraMap T.B Q.P b) ∈ T.J; rw [hε1]; exact hb
        · rw [Ideal.mem_comap]; change ε q ∈ T.J; rw [(hε q).1 hq]; exact T.J.zero_mem
      exact hle hp
  let π₀ : Q.P →+* T.B₀ := T.π.comp (ε : Q.P →+* T.B)
  have hπ₀ : ∀ p, π₀ p = 0 ↔ p ∈ Q.ext T.J := fun p ↦ (T.ker _).trans (hεJ p)
  let πF : Q.P ⧸ K →+* T.B₀ := Ideal.Quotient.lift K π₀ fun p hp ↦ (hπ₀ p).2 (hKle hp)
  have hπF : ∀ p, πF (Ideal.Quotient.mk K p) = T.π (ε p) := fun p ↦ rfl
  have hlev : IsLev δ' (n + 1) := by
    have h := GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism Q.P (Q.ext T.J) η (Q.P ⧸ K) _ δ' (Ideal.Quotient.mk K) hδ' rfl (n + 1)
    rw [← hK, Ideal.map_quotient_self] at h
    exact le_bot_iff.1 h
  have halg : algebraMap R (Q.P ⧸ K) = (Ideal.Quotient.mk K).comp ((algebraMap T.B Q.P).comp (algebraMap R T.B)) :=
    rfl
  let F : Thick κ t :=
    { B := Q.P ⧸ K
      J := (Q.ext T.J).map (Ideal.Quotient.mk K)
      δ := δ'
      nil := (isDPNilpotent_iff_exists_isLevel δ').2 ⟨_, hlev⟩
      dp := by rw [halg]; exact IsDPMorphism.comp _ hδ' (IsDPMorphism.comp _ hη.dp T.dp)
      B₀ := T.B₀
      π := πF
      surj := fun b₀ ↦ by
        obtain ⟨b, rfl⟩ := T.surj b₀
        exact ⟨Ideal.Quotient.mk K (algebraMap T.B Q.P b), by rw [hπF, hε1]⟩
      ker := fun y ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Ideal.mem_quotient_iff_mem hKle]
        exact hπ₀ p
      x := T.x
      w := by
        rw [T.w]
        congr 1
        refine RingHom.ext fun r ↦ ?_
        change T.π (algebraMap R T.B r) = T.π (ε (algebraMap T.B Q.P (algebraMap R T.B r)))
        rw [hε1] }
  let φ : T.B →ₐ[R] F.B :=
    { (Ideal.Quotient.mk K).comp (algebraMap T.B Q.P) with commutes' := fun _ ↦ rfl }
  let u : T ⟶ F :=
    ⟨φ, RingHom.id T.B₀, fun b ↦ by
      change T.π b = T.π (ε (algebraMap T.B Q.P b)); rw [hε1],
     IsDPMorphism.comp _ hδ' hη.dp, by rw [spMap_id, Category.id_comp]⟩
  refine ⟨F, u, fun _ ↦ Ideal.Quotient.mk K (Q.e 1), ⟨hlev, fun _ ↦ Ideal.mem_map_of_mem _ (Q.e_one_mem_ext T.J), ?_⟩, ?_⟩
  · intro S hS a c hc
    have hS' : fil S.δ (n + 1) = ⊥ := hS
    obtain ⟨G, hG1, hG2⟩ := hlift S.B (a.φ : T.B →+* S.B) (fun k ↦ S.δ.dpow k (c ())) (S.δ.dpow_zero (hc ()))
      fun m k ↦ S.δ.mul_dpow (hc ())
    have hGa : G.comp (algebraMap T.B Q.P) = (a.φ : T.B →+* S.B) := RingHom.ext hG1
    have hGdp : IsDPMorphism η S.δ G :=
      GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd T.B T.J T.δ Q η hη S.B S.J S.δ G (c ()) (hc ()) (by rw [hGa]; exact a.dp)
        hG2
    have hGK : ∀ p ∈ K, G p = 0 := fun p hp ↦ by
      have h := hfil.2.2.2.2.2.2 S.B S.J S.δ G hGdp (n + 1)
      rw [hS', ← hK] at h
      exact (Ideal.mem_bot).1 (h (Ideal.mem_map_of_mem G hp))
    let Gb : Q.P ⧸ K →+* S.B := Ideal.Quotient.lift K G hGK
    have hGb : ∀ p, Gb (Ideal.Quotient.mk K p) = G p := fun p ↦ rfl
    let gφ : F.B →ₐ[R] S.B :=
      { Gb with
        commutes' := fun r ↦ by
          change G (algebraMap T.B Q.P (algebraMap R T.B r)) = _
          rw [hG1]; exact a.φ.commutes r }
    have hgdp : IsDPMorphism F.δ S.δ (gφ : F.B →+* S.B) := by
      refine huniv S.B S.J S.δ Gb ?_
      have : Gb.comp (Ideal.Quotient.mk K) = G := RingHom.ext hGb
      rw [this]; exact hGdp
    let g : F ⟶ S :=
      ⟨gφ, a.φ₀, fun b' ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
        change a.φ₀ (T.π (ε p)) = S.π (G p)
        rw [a.comm, show a.φ (ε p) = G (algebraMap T.B Q.P (ε p)) from (hG1 _).symm]
        have hm : p - algebraMap T.B Q.P (ε p) ∈ Q.ext T.J :=
          Ideal.mem_sup_right ((hε _).2 (by rw [map_sub, hε1, sub_self]))
        have h2 := hGdp.1 (Ideal.mem_map_of_mem G hm)
        rw [← S.ker, map_sub, map_sub, sub_eq_zero] at h2
        exact h2.symm,
       hgdp, a.pt⟩
    refine ⟨g, ⟨Thick.Hom.ext' (AlgHom.ext fun b ↦ hG1 b), fun _ ↦ ?_⟩, ?_⟩
    · change G (Q.e 1) = c ()
      rw [hG2 1, S.δ.dpow_one (hc ())]
    · rintro g' ⟨h1, h2⟩
      refine Thick.Hom.ext' (AlgHom.ext fun b' ↦ ?_)
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
      change ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) p = G p
      have hHdp : IsDPMorphism η S.δ ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) :=
        IsDPMorphism.comp _ g'.dp hδ'
      refine congrArg (fun f : Q.P →+* S.B ↦ f p) (ringHom_eq_of_basis Q (fun b ↦ ?_) fun k ↦ ?_)
      · change (u ≫ g').φ b = G (algebraMap T.B Q.P b)
        rw [h1]; exact (hG1 b).symm
      · rw [hG2 k, ← hη.var k, hHdp.map_dpow (Q.e_one_mem_ext T.J)]
        change S.δ.dpow k (g'.φ (Ideal.Quotient.mk K (Q.e 1))) = _
        rw [show g'.φ (Ideal.Quotient.mk K (Q.e 1)) = c () from h2 ()]
  · have hsemi : SemiHom (RingHom.id R) (Ideal.Quotient.mk K) := fun r p ↦ map_smul (Ideal.Quotient.mkₐ R K) r p
    exact GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable R T.B T.J T.δ Q η (Q.P ⧸ K) F.J δ' (Ideal.Quotient.mk K) n hη hT hsemi hδ'
      Ideal.Quotient.mk_surjective rfl (fun b ↦ by rw [Ideal.Quotient.eq_zero_iff_mem, hK]) φ
      (SemiHom.of_algHom u.φ) u.dp fun _ ↦ rfl

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeCrystallineThickeningOneElementLevelStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeCrystallineThickening_oneElement_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (n : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Unit → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  first | exact @GlobalTheory.PDForm.exists_isFree_one_qAt | exact GlobalTheory.PDForm.exists_isFree_one_qAt | (intros; apply GlobalTheory.PDForm.exists_isFree_one_qAt <;> assumption)
end
