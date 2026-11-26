module

public import ReciprocityTheory.GroupCohomology.ConnNatHolds

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.IsSuccSubset
namespace ReciprocityTheory.Coh

noncomputable section

universe u

open Cx

namespace InflationTower

variable {R : Type u} [CommRing R]

lemma H_mk {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

lemma lift_cocycle {A B : Cx R} (φ : Hom A B) (hs : ∀ n, Function.Surjective (φ.f n)) (n : ℕ)
    (z : A.Z n) (w : B.Z n) (h : φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk w) :
    ∃ z' : A.Z n, (Submodule.Quotient.mk z' : A.H n) = Submodule.Quotient.mk z ∧ φ.Z n z' = w := by
  rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap] at h
  cases n with
  | zero =>
    refine ⟨z, rfl, ?_⟩
    have h' : ((φ.Z 0 z - w : B.Z 0) : B.X 0) = 0 := h
    exact sub_eq_zero.mp (Subtype.ext h')
  | succ k =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', rfl⟩ := hs k c
    have hdc : A.d (k+1) (A.d k c') = 0 := A.dd k c'
    refine ⟨z - ⟨A.d k c', hdc⟩, ?_, ?_⟩
    · rw [Submodule.Quotient.eq, Submodule.mem_comap]
      refine ⟨-c', ?_⟩
      show A.d k (-c') = (z : A.X (k+1)) - A.d k c' - z
      rw [map_neg]; abel
    · apply Subtype.ext
      have hc' : B.d k (φ.f k c') = φ.f (k+1) z - w := hc
      show φ.f (k+1) ((z : A.X (k+1)) - A.d k c') = w
      rw [map_sub, φ.comm, hc']; abel

theorem surj_part (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (n : ℕ) (y : ∀ m, (A m).H n) (hy : ∀ m, (τ m).H n (y (m + 1)) = y m) :
    ∃ x, ∀ m, (π m).H n x = y m := by
  have step : ∀ m (z : (A m).Z n), (Submodule.Quotient.mk z : (A m).H n) = y m →
      ∃ z' : (A (m+1)).Z n, (Submodule.Quotient.mk z' : (A (m+1)).H n) = y (m+1) ∧ (τ m).Z n z' = z := by
    intro m z hz
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (y (m+1))
    obtain ⟨z', h1, h2⟩ := lift_cocycle (τ m) (hT.surj m) n w z (by rw [hw, hy, hz])
    exact ⟨z', h1.trans hw, h2⟩
  let seq : ∀ m, {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m} := fun m =>
    Nat.rec (motive := fun m => {z : (A m).Z n // (Submodule.Quotient.mk z : (A m).H n) = y m})
      ⟨Classical.choose (Submodule.Quotient.mk_surjective _ (y 0)),
        Classical.choose_spec (Submodule.Quotient.mk_surjective _ (y 0))⟩
      (fun m s => ⟨Classical.choose (step m s.1 s.2), (Classical.choose_spec (step m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).Z n (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (step m (seq m).1 (seq m).2)).2
  obtain ⟨x, hx⟩ := hT.lift n (fun m => ((seq m).1 : (A m).X n)) (fun m => congrArg Subtype.val (hseq m))
  have hdx : L.d n x = 0 := by
    apply hT.ext
    intro m
    rw [(π m).comm, hx]; exact (seq m).1.2
  refine ⟨Submodule.Quotient.mk ⟨x, hdx⟩, fun m => ?_⟩
  rw [H_mk, ← (seq m).2]
  congr 1; exact Subtype.ext (hx m)

def Hs (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) : ℕ → ∀ m, Submodule R ((A m).H k)
  | 0 => fun _ => ⊤
  | j + 1 => fun m => (Hs A τ k j (m + 1)).map ((τ m).H k)

def Is (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1)) :
    ℕ → ∀ m, Set ((A m).X k)
  | 0 => fun m => {b | (A m).d k b = c m}
  | j + 1 => fun m => (τ m).f k '' Is A τ k c j (m + 1)

section Inj

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

lemma Is_torsor (hs : ∀ m n, Function.Surjective ((τ m).f n)) :
    ∀ j m p, p ∈ Is A τ k c j m → ∀ q, q ∈ Is A τ k c j m ↔
      ∃ hx : (A m).d k (q - p) = 0, (Submodule.Quotient.mk ⟨q - p, hx⟩ : (A m).H k) ∈ Hs A τ k j m := by
  intro j
  induction j with
  | zero =>
    intro m p hp q
    have hp' : (A m).d k p = c m := hp
    show (A m).d k q = c m ↔ _
    simp only [Hs, Submodule.mem_top, exists_prop, and_true, map_sub, hp', sub_eq_zero]
  | succ j ih =>
    intro m p hp q
    obtain ⟨p', hp', rfl⟩ := hp
    constructor
    · rintro ⟨q', hq', rfl⟩
      obtain ⟨hx, hmem⟩ := (ih (m+1) p' hp' q').1 hq'
      have hx' : (A m).d k ((τ m).f k q' - (τ m).f k p') = 0 := by
        rw [← map_sub, ← (τ m).comm, hx, map_zero]
      refine ⟨hx', ?_⟩
      have he : (Submodule.Quotient.mk ⟨(τ m).f k q' - (τ m).f k p', hx'⟩ : (A m).H k) =
          (τ m).H k (Submodule.Quotient.mk ⟨q' - p', hx⟩) := by
        rw [H_mk]; congr 1; exact Subtype.ext (map_sub _ _ _).symm
      rw [he]
      exact Submodule.mem_map_of_mem hmem
    · rintro ⟨hx, hmem⟩
      obtain ⟨h, hh, he⟩ := hmem
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
      obtain ⟨y', h1, h2⟩ := lift_cocycle (τ m) (hs m) k y ⟨_, hx⟩ he
      have h2' : (τ m).f k y' = q - (τ m).f k p' := congrArg Subtype.val h2
      refine ⟨p' + y', ?_, ?_⟩
      · rw [ih (m+1) p' hp']
        have hy0 : (A (m+1)).d k (p' + y' - p') = 0 := by rw [add_sub_cancel_left]; exact y'.2
        refine ⟨hy0, ?_⟩
        have : (⟨p' + y' - p', hy0⟩ : (A (m+1)).Z k) = y' := Subtype.ext (add_sub_cancel_left _ _)
        rw [this, h1]; exact hh
      · rw [map_add (f := _), h2']; abel

lemma Is_nonempty (hP : ∀ m, ∃ b, (A m).d k b = c m) : ∀ j m, (Is A τ k c j m).Nonempty := by
  intro j
  induction j with
  | zero => exact hP
  | succ j ih => intro m; exact (ih (m+1)).image _

lemma Is_succ_subset (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) :
    ∀ j m, Is A τ k c (j+1) m ⊆ Is A τ k c j m := by
  intro j
  induction j with
  | zero =>
    rintro m _ ⟨b, hb, rfl⟩
    have hb' : (A (m+1)).d k b = c (m+1) := hb
    show (A m).d k ((τ m).f k b) = c m
    rw [← (τ m).comm, hb', hc]
  | succ j ih => intro m; exact Set.image_mono (ih (m+1))

lemma Hs_succ_le : ∀ j m, Hs A τ k (j+1) m ≤ Hs A τ k j m := by
  intro j
  induction j with
  | zero => intro m; exact le_top
  | succ j ih => intro m; exact Submodule.map_mono (ih (m+1))

end Inj

section Inj2

variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))

lemma Is_anti (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) (m : ℕ) :
    Antitone fun j => Is A τ k c j m :=
  antitone_nat_of_succ_le fun j => Is_succ_subset A τ k c hc j m

lemma Hs_anti (m : ℕ) : Antitone fun j => Hs A τ k j m :=
  antitone_nat_of_succ_le fun j => Hs_succ_le A τ k j m

lemma Hs_stab (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Hs A τ k j m = Hs A τ k J m := by
  obtain ⟨J, hJ⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (Hs A τ k j m), fun _ _ h => Hs_anti A τ k m h⟩ :
      ℕ →o (Submodule R ((A m).H k))ᵒᵈ)
  exact ⟨J, fun j hj => (congrArg OrderDual.ofDual (hJ j hj)).symm⟩

lemma Is_stab (hs : ∀ m n, Function.Surjective ((τ m).f n)) (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m)
    (hP : ∀ m, ∃ b, (A m).d k b = c m) (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m := by
  obtain ⟨J, hJ⟩ := Hs_stab A τ k hA m
  refine ⟨J, fun j hj => ?_⟩
  apply le_antisymm (Is_anti A τ k c hc m hj)
  obtain ⟨p, hp⟩ := Is_nonempty A τ k c hP j m
  have hpJ := Is_anti A τ k c hc m hj hp
  intro q hq
  rw [Is_torsor A τ k c hs j m p hp, hJ j hj]
  exact (Is_torsor A τ k c hs J m p hpJ q).1 hq

theorem inj_part (L : Cx R) (π : ∀ m, Hom L (A m)) (hT : IsTowerLim A τ L π)
    (hA : ∀ m, IsArtinian R ((A m).H k)) (x : L.H (k + 1)) (hx : ∀ m, (π m).H (k + 1) x = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ∀ m, ∃ b, (A m).d k b = (π m).f (k+1) z := by
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, hb⟩
  let c : ∀ m, (A m).X (k + 1) := fun m => (π m).f (k+1) z
  have hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m := fun m => hT.compat m (k+1) z
  have hstab : ∀ m, ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m :=
    Is_stab A τ k c hT.surj hc hP hA
  let J : ℕ → ℕ := fun m => Classical.choose (hstab m)
  have hJ : ∀ m j, J m ≤ j → Is A τ k c j m = Is A τ k c (J m) m := fun m => Classical.choose_spec (hstab m)
  let S : ∀ m, Set ((A m).X k) := fun m => Is A τ k c (J m) m
  have hS : ∀ m j, S m ⊆ Is A τ k c j m := by
    intro m j
    rcases le_total j (J m) with h | h
    · exact Is_anti A τ k c hc m h
    · rw [hJ m j h]
  have hSsurj : ∀ m, ∀ s ∈ S m, ∃ t ∈ S (m+1), (τ m).f k t = s := fun m s hs =>
    hS m (J (m+1) + 1) hs
  have hS0 : (S 0).Nonempty := Is_nonempty A τ k c hP _ _
  let seq : ∀ m, {b : (A m).X k // b ∈ S m} := fun m =>
    Nat.rec (motive := fun m => {b : (A m).X k // b ∈ S m}) ⟨hS0.some, hS0.some_mem⟩
      (fun m s => ⟨Classical.choose (hSsurj m s.1 s.2), (Classical.choose_spec (hSsurj m s.1 s.2)).1⟩) m
  have hseq : ∀ m, (τ m).f k (seq (m+1)).1 = (seq m).1 := fun m =>
    (Classical.choose_spec (hSsurj m (seq m).1 (seq m).2)).2
  obtain ⟨b, hb⟩ := hT.lift k (fun m => (seq m).1) hseq
  have hdb : L.d k b = z := by
    rw [← sub_eq_zero]
    apply hT.ext
    intro m
    have h0 : (A m).d k (seq m).1 = c m := hS m 0 (seq m).2
    rw [map_sub, (π m).comm, hb, h0, sub_self]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact ⟨b, hdb⟩

end Inj2

theorem inj_zero (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (x : L.H 0) (hx : ∀ m, (π m).H 0 x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : L.X 0) = 0 := by
    apply hT.ext
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    exact h
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hz]
  exact Submodule.zero_mem _

end InflationTower

end

universe u

open InflationTower in
theorem tower_holds : TowerStatement.{u} := by
  intro R _ A τ L π hT n
  refine ⟨surj_part A τ L π hT n, fun hA x hx => ?_⟩
  cases n with
  | zero => exact inj_zero A τ L π hT x hx
  | succ k => exact inj_part A τ k L π hT (hA k rfl) x hx

end ReciprocityTheory.Coh
end

namespace ReciprocityTheory.Coh

open Cx Function

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem hom_H_smul {A : Cx R} (i : Hom A A) (t : R) (hi : ∀ n x, i.f n x = t • x) (n : ℕ)
    (x : A.H n) : i.H n x = t • x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    show Submodule.Quotient.mk (i.Z n z) = t • Submodule.Quotient.mk z
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hi n z.1)

end SlopeTestRemainingChoices

section Aux2

theorem tower_family {X : ℕ → Type*} (f : ∀ k, X (k + 1) → X k) (hf : ∀ k, Surjective (f k)) :
    ∀ (m : ℕ) (y : X m), ∃ z : ∀ k, X k, (∀ k, f k (z (k + 1)) = z k) ∧ z m = y := by
  intro m
  induction m generalizing X with
  | zero =>
    intro y
    let z : ∀ k, X k := fun k => Nat.rec (motive := fun k => X k) y
      (fun k zk => Classical.choose (hf k zk)) k
    exact ⟨z, fun k => Classical.choose_spec (hf k (z k)), rfl⟩
  | succ m ih =>
    intro y
    obtain ⟨z', hz', hm⟩ := ih (X := fun k => X (k + 1)) (fun k => f (k + 1)) (fun k => hf (k + 1)) y
    refine ⟨fun k => match k with | 0 => f 0 (z' 0) | k + 1 => z' k, fun k => ?_, hm⟩
    cases k with
    | zero => rfl
    | succ k => exact hz' k

variable {R : Type u} [CommRing R] {M P Q : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

noncomputable def descend (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) : P →ₗ[R] Q :=
  (LinearMap.ker p).liftQ g h ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap

theorem descend_apply (p : M →ₗ[R] P) (hp : Surjective p) (g : M →ₗ[R] Q)
    (h : LinearMap.ker p ≤ LinearMap.ker g) (x : M) : descend p hp g h (p x) = g x := by
  have : (p.quotKerEquivOfSurjective hp).symm (p x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [descend, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, this,
    Submodule.liftQ_apply]

theorem isFiniteLength_of_exact {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Exact f g)
    (hM : IsFiniteLength R M) (hP : IsFiniteLength R P) : IsFiniteLength R N := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at *
  obtain ⟨_, _⟩ := hM
  obtain ⟨_, _⟩ := hP
  have e : LinearMap.range f = LinearMap.ker g := h.linearMap_ker_eq.symm
  exact ⟨isNoetherian_of_range_eq_ker f g e, isArtinian_of_range_eq_ker f g e⟩

theorem mem_smul_top_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ J) hx ?_ ?_
    · intro a ha m _ i; exact J.mul_mem_right _ ha
    · intro a b ha hb i; exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [show x = ∑ i, x i • Pi.single i (1 : R) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

theorem isPrecomplete_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  have key : ∀ k (x : ι → R), x ∈ I ^ k • (⊤ : Submodule R (ι → R)) ↔
      ∀ i, x i ∈ I ^ k • (⊤ : Submodule R R) := by
    intro k x
    rw [mem_smul_top_pi]
    simp only [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ l : R, ∀ n, f n i ≡ l [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => f n i) fun {m n} hmn => ?_
    have := (hf hmn)
    rw [SModEq.sub_mem] at this ⊢
    exact (key m _).1 this i
  choose l hl using hc
  refine ⟨l, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hl i n)

end Aux2

section Tower

variable {R : Type u} [CommRing R] (t : R) {A : ℕ → Cx R} {τ : ∀ m, Hom (A (m + 1)) (A m)}
  {L : Cx R} {π : ∀ m, Hom L (A m)}

theorem tower_pi_surj (hT : IsTowerLim A τ L π) (m n : ℕ) : Surjective ((π m).f n) := by
  intro y
  obtain ⟨z, hz, hm⟩ := tower_family (X := fun k => (A k).X n) (fun k => (τ k).f n)
    (fun k => hT.surj k n) m y
  obtain ⟨x, hx⟩ := hT.lift n z hz
  exact ⟨x, (hx m).trans hm⟩

def smulHom (L : Cx R) (t : R) : Hom L L := ⟨fun _ => t • LinearMap.id, fun n x => by simp⟩

theorem smulHom_f (L : Cx R) (t : R) (n : ℕ) (x : L.X n) : (smulHom L t).f n x = t • x := rfl

theorem pow_torsionfree (htf : ∀ n (x : L.X n), t • x = 0 → x = 0) (n : ℕ) :
    ∀ k (x : L.X n), t ^ k • x = 0 → x = 0 := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih => intro x hx; exact htf n x (ih _ (by rw [smul_smul, ← pow_succ]; exact hx))

variable (hT : IsTowerLim A τ L π) (htf : ∀ n (x : L.X n), t • x = 0 → x = 0)
  (hk : ∀ m n (x : L.X n), (π m).f n x = 0 ↔ ∃ y, x = t ^ (m + 1) • y)

include hT htf hk

theorem ses_smul : SES (smulHom L t) (π 0) := by
  refine ⟨fun n => (injective_iff_map_eq_zero _).2 fun x hx => htf n x hx,
    ?_, tower_pi_surj hT 0⟩
  intro n y
  rw [hk 0 n y]
  simp only [zero_add, pow_one, Set.mem_range, smulHom_f]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

theorem ker_le_ker_smul (m n : ℕ) : LinearMap.ker ((π 0).f n) ≤
    LinearMap.ker ((π (m + 1)).f n ∘ₗ (t ^ (m + 1) • LinearMap.id)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := (hk 0 n x).1 hx
  show (π (m + 1)).f n (t ^ (m + 1) • t ^ (0 + 1) • y) = 0
  rw [hk, smul_smul, ← pow_add]
  exact ⟨y, by ring_nf⟩

noncomputable def jf (m n : ℕ) : (A 0).X n →ₗ[R] (A (m + 1)).X n :=
  descend ((π 0).f n) (tower_pi_surj hT 0 n) _ (ker_le_ker_smul t hT htf hk m n)

theorem jf_apply (m n : ℕ) (x : L.X n) :
    jf t hT htf hk m n ((π 0).f n x) = (π (m + 1)).f n (t ^ (m + 1) • x) :=
  descend_apply _ _ _ _ x

noncomputable def jHom (m : ℕ) : Hom (A 0) (A (m + 1)) where
  f n := jf t hT htf hk m n
  comm n a := by
    obtain ⟨x, rfl⟩ := tower_pi_surj hT 0 n a
    rw [← (π 0).comm, jf_apply, jf_apply, ← (π (m + 1)).comm]
    simp only [map_smul]

theorem ses_j (m : ℕ) : SES (jHom t hT htf hk m) (τ m) := by
  refine ⟨?_, ?_, hT.surj m⟩
  · intro n
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨x, rfl⟩ := tower_pi_surj hT 0 n a
    change jf t hT htf hk m n _ = 0 at ha
    rw [jf_apply, hk] at ha
    obtain ⟨y, hy⟩ := ha
    have : x = t • y := by
      refine sub_eq_zero.1 (pow_torsionfree t htf n (m + 1) _ ?_)
      rw [smul_sub, hy, smul_smul, ← pow_succ, sub_self]
    rw [hk 0 n]
    exact ⟨y, by simpa using this⟩
  · intro n z
    obtain ⟨x, rfl⟩ := tower_pi_surj hT (m + 1) n z
    rw [hT.compat, hk]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(π 0).f n y, jf_apply t hT htf hk m n y⟩
    · rintro ⟨a, ha⟩
      obtain ⟨y, rfl⟩ := tower_pi_surj hT 0 n a
      change jf t hT htf hk m n _ = _ at ha
      rw [jf_apply] at ha
      have h2 : (π (m + 1)).f n (x - t ^ (m + 1) • y) = 0 := by rw [map_sub, ha, sub_self]
      obtain ⟨w, hw⟩ := (hk (m + 1) n _).1 h2
      refine ⟨y + t • w, ?_⟩
      rw [smul_add, smul_smul, ← pow_succ, ← hw]
      abel

end Tower

theorem modT_holds : ModTStatement.{u} := by
  intro R _ A C i p t δ hi hs hc n
  obtain ⟨⟨δ0, hc0, hl⟩, huniq⟩ := lES_holds R A A C i p hs
  obtain rfl : δ = δ0 := huniq δ δ0 hc hc0
  refine ⟨fun x => ?_, hl.exC n, fun x => ?_⟩
  · rw [hl.exB n x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, hom_H_smul i t hi n y⟩
  · rw [LinearMap.mem_range, ← hom_H_smul i t hi (n + 1) x]
    exact (hl.exA n x).symm

theorem finGen_holds : FinGenStatement.{u} := by
  intro R _ t _ A τ L π hT htf hk h0
  have hfl : ∀ m n, IsFiniteLength R ((A m).H n) := by
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      intro n
      obtain ⟨⟨δ, _, hl⟩, _⟩ := lES_holds R (A 0) (A (m + 1)) (A m) (jHom t hT htf hk m) (τ m)
        (ses_j t hT htf hk m)
      exact isFiniteLength_of_exact _ _ (hl.exB n) (h0 n) (ih n)
  intro n
  refine ⟨?_, fun m => hfl m n⟩
  have hkill : ∀ m (z : (A m).H n), t ^ (m + 1) • z = 0 := by
    intro m z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [← Submodule.Quotient.mk_smul]
      have : t ^ (m + 1) • w = 0 := by
        apply Subtype.ext
        obtain ⟨l, hl⟩ := tower_pi_surj hT m n w.1
        show t ^ (m + 1) • w.1 = 0
        rw [← hl, ← map_smul, hk]
        exact ⟨l, rfl⟩
      rw [this, Submodule.Quotient.mk_zero]
  have hmem : ∀ k (x : L.H n), x ∈ Ideal.span {t} ^ k • (⊤ : Submodule R (L.H n)) ↔
      ∃ y, x = t ^ k • y := by
    intro k x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [eq_comm]
  have : IsHausdorff (Ideal.span {t}) (L.H n) := by
    refine ⟨fun x hx => ?_⟩
    refine (tower_holds R A τ L π hT n).2 (fun k _ m => ?_) x (fun m => ?_)
    · exact (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl m k)).2
    · have h1 := SModEq.sub_mem.1 (hx (m + 1))
      rw [sub_zero] at h1
      obtain ⟨y, rfl⟩ := (hmem (m + 1) x).1 h1
      rw [map_smul, hkill]
  obtain ⟨⟨δ, hc, _⟩, _⟩ := lES_holds R L L (A 0) (smulHom L t) (π 0) (ses_smul t hT htf hk)
  have hmt := (modT_holds R L (A 0) (smulHom L t) (π 0) t δ (fun _ _ => rfl)
    (ses_smul t hT htf hk) hc n).1
  have hmem1 : ∀ x : L.H n, x ∈ Ideal.span {t} • (⊤ : Submodule R (L.H n)) ↔ ∃ y, x = t • y := by
    intro x
    simpa using hmem 1 x
  have hle : Ideal.span {t} • (⊤ : Submodule R (L.H n)) ≤ LinearMap.ker ((π 0).H n) := by
    intro x hx
    exact (hmt x).2 ((hmem1 x).1 hx)
  let q := (Ideal.span {t} • (⊤ : Submodule R (L.H n))).liftQ ((π 0).H n) hle
  have hq : Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero, hmem1]
      exact (hmt x).1 hz
  have : IsNoetherian R ((A 0).H n) := (isFiniteLength_iff_isNoetherian_isArtinian.1 (h0 n)).1
  have : Module.Finite R (L.H n ⧸ Ideal.span {t} • (⊤ : Submodule R (L.H n))) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R)
    (M := L.H n ⧸ Ideal.span {t} • (⊤ : Submodule R (L.H n)))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {t}) (Fin r → R) := isPrecomplete_pi _
  have hsurj : Surjective ((Ideal.span {t} • (⊤ : Submodule R (L.H n))).mkQ ∘ₗ
      Fintype.linearCombination R s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end ReciprocityTheory.Coh
