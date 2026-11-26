module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV

namespace GlobalTheory.LevNorm

def edgeVal {k : Type} [CommRing k] {n : ℕ} (ρ κ : ℕ) (a : Fin n → Fin n → k) (M : GL (Fin n) k) : k :=
  ∑ i, ∑ j, if symEdge ρ κ i j then a i j * (M : Matrix (Fin n) (Fin n) k) i j else 0

def midDiag {k : Type} [CommRing k] (n ρ κ : ℕ) (s c : k) : Matrix (Fin n) (Fin n) k :=
  Matrix.diagonal fun i => if ρ ≤ i.val ∧ i.val < ρ + κ then c else s

def IsScal {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) : Prop :=
  ∃ (c : Kˣ) (x : GL (Fin n) O), (m : Matrix (Fin n) (Fin n) K) = (c : K) • ((bc O.subtype x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem edgeVal_one {k : Type} [CommRing k] {n : ℕ} (ρ κ : ℕ) (a : Fin n → Fin n → k) : edgeVal ρ κ a 1 = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := fun e => by unfold symEdge at h; rw [e] at h; omega
    simp [Matrix.one_apply_ne this]
  · rfl

structure PlaceSys (A : Type) [CommRing A] (S : Subring A) (P : Type) (k : P → Type) [∀ Q, Field (k Q)]
    (r : ∀ Q, S →+* k Q) : Type 1 where

  K : P → Type
  [fK : ∀ Q, Field (K Q)]

  O : ∀ Q, ValuationSubring (K Q)

  p : ∀ Q, A →+* K Q

  e : P → A
  surj : ∀ Q, Function.Surjective (p Q)
  e_self : ∀ Q, p Q (e Q) = 1
  e_ne : ∀ Q Q', Q' ≠ Q → p Q' (e Q) = 0
  ext : ∀ a, (∀ Q, p Q a = 0) → a = 0
  int : ∀ a, a ∈ S ↔ ∀ Q, p Q a ∈ O Q
  fin : ∀ a, {Q | p Q a ∉ O Q}.Finite
  r_surj : ∀ Q, Function.Surjective (r Q)
  r_ker : ∀ Q (s : S), r Q s = 0 ↔ (O Q).valuation (p Q s) < 1

attribute [instance] PlaceSys.fK

namespace PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r)

theorem ext' {a b : A} (h : ∀ Q, Z.p Q a = Z.p Q b) : a = b :=
  sub_eq_zero.1 (Z.ext _ fun Q => by rw [map_sub, h Q, sub_self])

theorem e_mem (Q : P) : Z.e Q ∈ S := (Z.int _).2 fun Q' => by
  by_cases h : Q' = Q
  · subst h; rw [Z.e_self]; exact one_mem _
  · rw [Z.e_ne Q Q' h]; exact zero_mem _

theorem e_mul_eq_iff (Q : P) (a b : A) : Z.e Q * a = Z.e Q * b ↔ Z.p Q a = Z.p Q b := by
  refine ⟨fun h => by simpa [Z.e_self] using congrArg (Z.p Q) h, fun h => Z.ext' fun Q' => ?_⟩
  by_cases h' : Q' = Q
  · subst h'; rw [map_mul, map_mul, h]
  · rw [map_mul, map_mul, Z.e_ne Q Q' h', zero_mul, zero_mul]

theorem e_idem (Q : P) : Z.e Q * Z.e Q = Z.e Q := by
  have := (Z.e_mul_eq_iff Q (Z.e Q) 1).2 (by rw [Z.e_self, map_one])
  rwa [mul_one] at this

theorem e_mul_mem_iff (Q : P) (a : A) : Z.e Q * a ∈ S ↔ Z.p Q a ∈ Z.O Q := by
  refine ⟨fun h => by simpa [Z.e_self] using (Z.int _).1 h Q, fun h => (Z.int _).2 fun Q' => ?_⟩
  by_cases h' : Q' = Q
  · subst h'; rwa [map_mul, Z.e_self, one_mul]
  · rw [map_mul, Z.e_ne Q Q' h', zero_mul]; exact zero_mem _

theorem e_injective : Function.Injective Z.e := fun Q Q' h => by
  by_contra hne
  have h1 := Z.e_self Q
  rw [h, Z.e_ne Q' Q hne] at h1
  exact zero_ne_one h1

theorem exists_single (Q : P) (x : Z.K Q) : ∃ a : A, Z.p Q a = x ∧ ∀ Q', Q' ≠ Q → Z.p Q' a = 0 := by
  obtain ⟨b, hb⟩ := Z.surj Q x
  exact ⟨Z.e Q * b, by rw [map_mul, Z.e_self, one_mul, hb], fun Q' h => by rw [map_mul, Z.e_ne Q Q' h, zero_mul]⟩

def pO (Q : P) : S →+* Z.O Q :=
  ((Z.p Q).comp S.subtype).codRestrict (Z.O Q) fun s => (Z.int _).1 s.2 Q

theorem pO_coe (Q : P) (s : S) : (Z.pO Q s : Z.K Q) = Z.p Q s := rfl

theorem pO_surj (Q : P) : Function.Surjective (Z.pO Q) := fun x => by
  obtain ⟨a, h1, h2⟩ := Z.exists_single Q x
  refine ⟨⟨a, (Z.int _).2 fun Q' => ?_⟩, Subtype.ext h1⟩
  by_cases h' : Q' = Q
  · subst h'; rw [h1]; exact x.2
  · rw [h2 Q' h']; exact zero_mem _

theorem exists_res (Q : P) : ∃ ρ : Z.O Q →+* k Q, Function.Surjective ρ ∧ ∀ s, ρ (Z.pO Q s) = r Q s := by
  have hk : RingHom.ker (Z.pO Q) ≤ RingHom.ker (r Q) := fun s hs => by
    have h0 : Z.p Q s = 0 := congrArg Subtype.val (RingHom.mem_ker.1 hs)
    rw [RingHom.mem_ker, Z.r_ker, h0, map_zero]
    exact zero_lt_one
  refine ⟨(Z.pO Q).liftOfSurjective (Z.pO_surj Q) ⟨r Q, hk⟩, fun y => ?_, fun s => RingHom.liftOfSurjective_comp_apply _ _ _ _⟩
  obtain ⟨s, rfl⟩ := Z.r_surj Q y
  exact ⟨Z.pO Q s, RingHom.liftOfSurjective_comp_apply _ _ _ _⟩

theorem r_congr (Q : P) {s t : S} (h : Z.p Q s = Z.p Q t) : r Q s = r Q t := by
  obtain ⟨ρ, -, hρ⟩ := Z.exists_res Q
  rw [← hρ, ← hρ, show Z.pO Q s = Z.pO Q t from Subtype.ext h]

theorem gl_int {n : ℕ} {x : GL (Fin n) A} (h : ∀ Q, ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) x) :
    ∃ y : GL (Fin n) S, bc S.subtype y = x := by
  have key : ∀ {x : GL (Fin n) A}, (∀ Q, ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) x) →
      ∀ i j, (x : Matrix (Fin n) (Fin n) A) i j ∈ S := fun {x} h i j => (Z.int _).2 fun Q => by
    obtain ⟨y, hy⟩ := h Q
    have := congrArg (fun g : GL (Fin n) (Z.K Q) => (g : Matrix (Fin n) (Fin n) (Z.K Q)) i j) hy
    exact (show _ = Z.p Q _ from this) ▸ ((y : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have h1 := key h
  have h2 := key (x := x⁻¹) fun Q => by
    obtain ⟨y, hy⟩ := h Q
    exact ⟨y⁻¹, by rw [map_inv, map_inv, hy]⟩
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype := Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem gl_single {n : ℕ} (Q : P) (y : GL (Fin n) (Z.K Q)) :
    ∃ x : GL (Fin n) A, bc (Z.p Q) x = y ∧ ∀ Q', Q' ≠ Q → bc (Z.p Q') x = 1 := by
  choose j hj hj' using Z.exists_single Q
  let g : Matrix (Fin n) (Fin n) (Z.K Q) → Matrix (Fin n) (Fin n) A := fun M => 1 + (M - 1).map j
  have g1 : ∀ M, (Z.p Q).mapMatrix (g M) = M := fun M => by
    rw [map_add (f := _), map_one]
    have : (Z.p Q).mapMatrix ((M - 1).map j) = M - 1 := by ext a b; exact hj _
    rw [this, add_sub_cancel]
  have g2 : ∀ M Q', Q' ≠ Q → (Z.p Q').mapMatrix (g M) = 1 := fun M Q' h => by
    rw [map_add (f := _), map_one]
    have : (Z.p Q').mapMatrix ((M - 1).map j) = 0 := by ext a b; exact hj' _ Q' h
    rw [this, add_zero]
  have gm : ∀ M N, M * N = 1 → g M * g N = 1 := fun M N h => Matrix.ext fun a b => Z.ext' fun Q' => by
    have : (Z.p Q').mapMatrix (g M * g N) = (Z.p Q').mapMatrix 1 := by
      rw [map_mul, map_one]
      by_cases h' : Q' = Q
      · subst h'; rw [g1, g1, h]
      · rw [g2 _ _ h', g2 _ _ h', one_mul]
    exact congrFun (congrFun this a) b
  exact ⟨⟨g y.1, g (y⁻¹).1, gm _ _ y.mul_inv, gm _ _ y.inv_mul⟩, Units.ext (g1 _), fun Q' h => Units.ext (g2 _ Q' h)⟩

variable {σ : A →+* A}

theorem exists_bar (hσ : ∀ a, σ (σ a) = a) (Q : P) : ∃ Q', σ (Z.e Q) = Z.e Q' := by
  have h0 : ∀ Q, σ (Z.e Q) ≠ 0 := fun Q h => by
    have h1 := Z.e_self Q
    rw [← hσ (Z.e Q), h, map_zero, map_zero] at h1
    exact zero_ne_one h1
  have h01 : ∀ Q Q', Z.p Q' (σ (Z.e Q)) ≠ 0 → Z.p Q' (σ (Z.e Q)) = 1 := fun Q Q' h =>
    mul_left_cancel₀ h (by rw [← map_mul, ← map_mul, Z.e_idem, mul_one])
  obtain ⟨Q', hQ'⟩ : ∃ Q', Z.p Q' (σ (Z.e Q)) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 Q (Z.ext _ hc)
  have e1 : Z.e Q' * σ (Z.e Q) = Z.e Q' * 1 := (Z.e_mul_eq_iff _ _ _).2 (by rw [h01 _ _ hQ', map_one])
  have e2 : σ (Z.e Q') * Z.e Q = σ (Z.e Q') := by simpa [hσ] using congrArg σ e1
  have e3 : ∀ Q'', Q'' ≠ Q → Z.p Q'' (σ (Z.e Q')) = 0 := fun Q'' h => by
    rw [← e2, map_mul, Z.e_ne Q Q'' h, mul_zero]
  have e4 : Z.p Q (σ (Z.e Q')) = 1 := h01 _ _ fun h => h0 Q' (Z.ext _ fun Q'' => by
    by_cases h' : Q'' = Q
    · subst h'; exact h
    · exact e3 _ h')
  refine ⟨Q', ?_⟩
  rw [← hσ (Z.e Q')]
  congr 1
  refine Z.ext' fun Q'' => ?_
  by_cases h' : Q'' = Q
  · subst h'; rw [e4, Z.e_self]
  · rw [e3 _ h', Z.e_ne Q Q'' h']

theorem exists_conj (hS : ∀ a ∈ S, σ a ∈ S) {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') :
    ∃ s : Z.K Q →+* Z.K Q', (∀ a, s (Z.p Q a) = Z.p Q' (σ a)) ∧ ∀ x ∈ Z.O Q, s x ∈ Z.O Q' := by
  have hk : RingHom.ker (Z.p Q) ≤ RingHom.ker ((Z.p Q').comp σ) := fun a ha => by
    have h1 : Z.e Q * a = Z.e Q * 0 := (Z.e_mul_eq_iff _ _ _).2 (by rw [RingHom.mem_ker.1 ha, map_zero])
    have h2 : Z.e Q' * σ a = Z.e Q' * 0 := by simpa [h] using congrArg σ h1
    simpa using (Z.e_mul_eq_iff _ _ _).1 h2
  have hs : ∀ a, (Z.p Q).liftOfSurjective (Z.surj Q) ⟨(Z.p Q').comp σ, hk⟩ (Z.p Q a) = Z.p Q' (σ a) :=
    fun a => RingHom.liftOfSurjective_comp_apply _ _ _ _
  refine ⟨_, hs, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Z.surj Q x
  rw [hs, ← Z.e_mul_mem_iff, ← h, ← map_mul]
  exact hS _ ((Z.e_mul_mem_iff _ _).2 hx)

theorem r_conj (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') (s : S) (hs : r Q s = 0) :
    r Q' ⟨σ s, hS _ s.2⟩ = 0 := by
  obtain ⟨t, ht, htO⟩ := Z.exists_conj hS (Q := Q') (Q' := Q) (by rw [← h, hσ])
  rw [Z.r_ker] at hs ⊢
  by_contra hc
  have hm : Z.p Q' (σ s) ∈ Z.O Q' := (Z.int _).1 (hS _ s.2) Q'
  have h1 : (Z.O Q').valuation (Z.p Q' (σ s)) = 1 := le_antisymm (((Z.O Q').valuation_le_one_iff _).2 hm) (not_lt.1 hc)
  have h0 : Z.p Q' (σ s) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have h2 : (Z.p Q' (σ s))⁻¹ ∈ Z.O Q' := by rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have h3 := htO _ h2
  rw [map_inv₀, ht, hσ, ← ValuationSubring.valuation_le_one_iff, map_inv₀] at h3
  have h4 : Z.p Q s ≠ 0 := by rw [← hσ s, ← ht]; exact (map_ne_zero t).2 h0
  have h5 : 0 < (Z.O Q).valuation (Z.p Q s) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h4)
  exact absurd hs (not_lt.2 ((inv_le_one₀ h5).1 h3))

end PlaceSys

end GlobalTheory.LevNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
namespace GlobalTheory.SymResCount

open Formalism.L2.DIV

theorem mem_unipSym_iff {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) :
    g ∈ unipSym K r ρ κ ↔ ∀ a b : Fin r, ¬ (a.val < b.val ∧ ¬ (ρ ≤ a.val ∧ a.val < ρ + κ ∧ b.val = ρ + κ)) →
      (g : Matrix (Fin r) (Fin r) K) a b = (1 : Matrix (Fin r) (Fin r) K) a b := by
  constructor
  · rintro ⟨⟨hl, hd⟩, hc⟩ a b hab
    by_cases e : a = b
    · subst e; rw [hd a, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne e]
      have hne : a.val ≠ b.val := fun h => e (Fin.ext h)
      by_cases h1 : b.val < a.val
      · exact hl (show b.val < a.val from h1)
      · exact hc a b (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (by omega), Matrix.one_apply_eq]
    · rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

def permFn (ρ κ i : ℕ) : ℕ := if i < κ then ρ + i else if i < κ + ρ then i - κ else i

def permInv (ρ κ a : ℕ) : ℕ := if a < ρ then κ + a else if a < ρ + κ then a - ρ else a

def perm (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : Fin r ≃ Fin r where
  toFun i := ⟨permFn ρ κ i.val, by unfold permFn; split_ifs <;> omega⟩
  invFun a := ⟨permInv ρ κ a.val, by unfold permInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega
  right_inv a := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega

theorem perm_val {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (i : Fin r) : (perm r ρ κ hr i).val = permFn ρ κ i.val := rfl

theorem freePos_iff (ρ κ i j : ℕ) :
    GlobalTheory.SymRes.FreePos ρ κ i j ↔ (permFn ρ κ i < permFn ρ κ j ∧
      ¬ (ρ ≤ permFn ρ κ i ∧ permFn ρ κ i < ρ + κ ∧ permFn ρ κ j = ρ + κ)) := by
  unfold GlobalTheory.SymRes.FreePos permFn; split_ifs <;> omega

def reidx {K : Type} [CommRing K] (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : GL (Fin r) K ≃* GL (Fin r) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (perm r ρ κ hr)).toMulEquiv

theorem reidx_apply {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) (i j : Fin r) :
    ((reidx r ρ κ hr g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) (perm r ρ κ hr i) (perm r ρ κ hr j) =
      (g : Matrix (Fin r) (Fin r) K) i j := by
  simp [reidx, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem reidx_mem_iff {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) :
    reidx r ρ κ hr g ∈ unipSym K r ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ g := by
  rw [mem_unipSym_iff]
  constructor
  · intro h i j hf
    have := h (perm r ρ κ hr i) (perm r ρ κ hr j) (by rw [perm_val, perm_val, ← freePos_iff]; exact hf)
    rw [reidx_apply] at this
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (perm r ρ κ hr).surjective a
    obtain ⟨j, rfl⟩ := (perm r ρ κ hr).surjective b
    rw [reidx_apply, h i j (by rw [freePos_iff, ← perm_val hr, ← perm_val hr]; exact hab)]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]

end GlobalTheory.SymResCount

namespace GlobalTheory.SymResCount
open Formalism.L2.DIV

theorem conj_pat_onto : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) →
    ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) →
    ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  intro K _ _ r ρ κ hr m hm g hg
  have hr' : κ + ρ ≤ r := by omega
  haveI : Finite (GL (Fin r) K) := Finite.of_injective (fun u : GL (Fin r) K => (u : Matrix (Fin r) (Fin r) K)) Units.val_injective
  set S : Set (GL (Fin r) K) := {g | GlobalTheory.SymRes.IsPat ρ κ g} with hS
  set U : Set (GL (Fin r) K) := (unipSym K r ρ κ : Set (GL (Fin r) K)) with hU
  have hSU : (reidx (K := K) r ρ κ hr') '' S = U := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (reidx_mem_iff hr' x).2 hx
    · intro hh
      refine ⟨(reidx r ρ κ hr').symm h, (reidx_mem_iff hr' _).1 (by rw [MulEquiv.apply_symm_apply]; exact hh), by simp⟩
  have hinj : Function.Injective (fun x : GL (Fin r) K => m * x * m⁻¹) := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hc : (fun x : GL (Fin r) K => m * x * m⁻¹) '' S = U := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact hm x hx
    · rw [Set.ncard_image_of_injective S hinj, ← hSU, Set.ncard_image_of_injective S (reidx r ρ κ hr').injective]
    · exact Set.toFinite U
  have hg' : m * g * m⁻¹ ∈ U := hg
  rw [← hc] at hg'
  obtain ⟨x, hx, he⟩ := hg'
  have : x = g := hinj he
  rw [← this]; exact hx

end GlobalTheory.SymResCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinctStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  first | exact @GlobalTheory.CosetDistinct.coset_uniq | exact GlobalTheory.CosetDistinct.coset_uniq | (intros; apply GlobalTheory.CosetDistinct.coset_uniq <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRep
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke GlobalTheory.ParHeckeSource GlobalTheory.ParahoricConjBlocks

noncomputable section

namespace GlobalTheory.LowerHecke

theorem lowU_conj_blocks {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (M W : Matrix D D k) (ν : Matrix D A k) (a : Matrix A A k) (b : Matrix A D k) (c : Matrix D A k) (e : Matrix D D k) :
    fromBlocks 1 0 0 M * fromBlocks 1 0 (-ν) 1 * fromBlocks a b c e * fromBlocks 1 0 0 W =
      fromBlocks a (b * W) (M * (c - ν * a)) (M * (e - ν * b) * W) := by
  simp only [fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel

end GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem exists_lowU_diag_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj
  set w := torusElt k D ϖ (indic s) with hw
  have hjI : IsIntM j.1 := isIntM_of_mem_parahoric hj
  have hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1 := (mem_parahoric.1 hj).2
  have hjd : valuation k j.1.det = 1 := val_det_of_mem_KO (mem_parahoric.1 hj).1
  obtain ⟨ha, he⟩ := (val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd
  obtain ⟨haI, hbI, hcI, heI⟩ := isIntM_toBlocks hjI
  set a := j.1.toBlocks₁₁ with ha_def
  set b := j.1.toBlocks₁₂ with hb_def
  set c := j.1.toBlocks₂₁ with hc_def
  set e := j.1.toBlocks₂₂ with he_def
  have hcM : ∀ i l, valuation k (c i l) < 1 := fun i l => hjl i l
  have ha0 : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at ha; exact zero_ne_one ha
  have hainvI : IsIntM a⁻¹ := isIntM_inv haI ha
  have hinva : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha0
  letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0
  set E := e - c * a⁻¹ * b with hE_def
  have hjE : j.1.det = a.det * E.det := by
    rw [← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hEd : valuation k E.det = 1 := by
    rw [hjE, map_mul, ha, one_mul] at hjd; exact hjd
  have hEI : IsIntM E := isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).2
    (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)
  set E' : GL D k := hEu.unit with hE'_def
  have hE'v : E'.1 = E := hEu.unit_spec
  have hE'K : E' ∈ KO k D := mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)
  obtain ⟨g, ⟨hgR, hgK⟩, -⟩ := hR.2 E' hE'K
  obtain ⟨hκg, hκ'g, hgeq⟩ := hκ g hgR

  refine ⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩
  rintro ν ⟨μ, hμ, hνμ⟩
  have hν : ν = c * a⁻¹ - g.1 * μ := by rw [← hνμ]; abel
  set K1 := κ g with hK1
  set K2 := κ' g with hK2
  have hm : (w⁻¹ * K1⁻¹) * g = K2 := by rw [hgeq]; group
  have hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹ := by rw [← hm]; group
  have hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w) := by
    rw [mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk,
      inv_one, ← emb_mul_emb]
    simp only [mul_assoc, hw]
  rw [hX]
  set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM
  have hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 =
      fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]
    exact lowU_conj_blocks _ _ _ _ _ _ _
  have h21 : M * (c - ν * a) = K2.1 * (μ * a) := by
    rw [hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]
  have he' : e - ν * b = E + g.1 * μ * b := by rw [hν, hE_def, Matrix.sub_mul]; abel
  have h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1) := by
    rw [he', Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [hM, ← hm', ← hE'v]; simp only [Units.val_mul, Matrix.mul_assoc]
    · rw [← hm, hM]; simp only [Units.val_mul, Matrix.mul_assoc]
  have hwI : IsIntM w.1 := by
    have h := inv_torusElt_int (D := D) hϖ s
    rw [val_inv_torusElt] at h
    rw [hw, val_torusElt]; simpa using h
  have hμa : ∀ i l, valuation k ((μ * a) i l) < 1 := GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)
  have hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1 := val_lt_mul (isIntM_of_mem_KO hκ'g) hμa
  have hwdet : (w⁻¹).1.det * w.1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hXv, h21, h22]
    refine isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩
    intro i l
    exact add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l)
      (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)
  · have hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det =
        (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one,
        val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul,
        Matrix.det_mul]
      simp only [Matrix.det_one]; ring
    rw [hdet, hwdet, mul_one, map_mul, hjd, mul_one]
    exact val_det_of_mem_KO (inv_mem hκg)
  · intro i l
    rw [hXv, fromBlocks_apply₂₁, h21]
    exact hll i l

end GlobalTheory.LowerHecke

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRepStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  first | exact @GlobalTheory.LowerHecke.exists_lowU_diag_coset | exact GlobalTheory.LowerHecke.exists_lowU_diag_coset | (intros; apply GlobalTheory.LowerHecke.exists_lowU_diag_coset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentatives
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem repsBuild : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ N hN
  classical
  set t : GL (A ⊕ D) k := mtor ϖ (indic s) with ht
  let f : (Σ _ : GL D k, Matrix D A k) → GL (A ⊕ D) k :=
    fun x => lowU x.2 * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ x.1)

  have key : ∀ g₁ ∈ R, ∀ ν₁ ∈ N g₁, ∀ g₂ ∈ R, ∀ ν₂ ∈ N g₂,
      (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D → g₁ = g₂ ∧ ν₁ = ν₂ := by
    intro g₁ hg₁ ν₁ hν₁ g₂ hg₂ ν₂ hν₂ h
    obtain ⟨rfl, μ, hμ, hdiff⟩ := GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct k A D ϖ hϖ s R hR κ κ' hκ g₁ hg₁ g₂ hg₂ ν₁ ν₂ h
    refine ⟨rfl, ?_⟩
    obtain ⟨hsmall, huniq⟩ := hN g₁ hg₁
    obtain ⟨ν', _, hν'⟩ := huniq ν₂ (hsmall ν₂ hν₂)
    have e2 : ν₂ = ν' := hν' ν₂ ⟨hν₂, 0, fun i a => by simp, by simp⟩
    have e1 : ν₁ = ν' := hν' ν₁ ⟨hν₁, μ, hμ, hdiff⟩
    rw [e1, e2]
  refine ⟨(R.sigma N).image f, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨⟨g, ν⟩, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_sigma] at hx
    obtain ⟨hg, hν⟩ := hx
    refine ⟨Subgroup.mul_mem _ (lowU_mem ((hN g hg).1 ν hν)) (emb_mem (hκ g hg).1), ?_⟩
    have h22 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)).1.toBlocks₂₂ = (κ g).1 := by
      rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
    show ((blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) : kˣ) : k) = _
    rw [blockDet_lowU_emb, h22, GeneralLinearGroup.val_det_apply]
  · intro j hj
    obtain ⟨g, hg, ν₀, hν₀, hall⟩ := GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep k A D ϖ hϖ s R hR κ κ' hκ j hj
    obtain ⟨ν', ⟨hν'N, μ, hμ, hdiff⟩, -⟩ := (hN g hg).2 ν₀ hν₀
    refine ⟨f ⟨g, ν'⟩, ⟨Finset.mem_image.2 ⟨(⟨g, ν'⟩ : Σ _ : GL D k, Matrix D A k), Finset.mem_sigma.2 ⟨hg, hν'N⟩, rfl⟩,
      hall ν' ⟨μ, hμ, hdiff⟩⟩, ?_⟩
    rintro j' ⟨hj', hmem⟩
    obtain ⟨⟨g₂, ν₂⟩, hx, rfl⟩ := Finset.mem_image.1 hj'
    rw [Finset.mem_sigma] at hx
    have hmem' : (f ⟨g, ν'⟩ * t)⁻¹ * (j * t) ∈ parahoric k A D := hall ν' ⟨μ, hμ, hdiff⟩
    have hc : (f ⟨g₂, ν₂⟩ * t)⁻¹ * (f ⟨g, ν'⟩ * t) ∈ parahoric k A D := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hmem')
      simpa [mul_assoc] using this
    obtain ⟨rfl, rfl⟩ := key g₂ hx.1 ν₂ hx.2 g hg ν' hν'N hc
    rfl
  · intro F
    rw [Finset.sum_image, Finset.sum_sigma]
    rintro ⟨g₁, ν₁⟩ h₁ ⟨g₂, ν₂⟩ h₂ heq
    rw [Finset.coe_sigma, Set.mem_sigma_iff] at h₁ h₂
    have hc : (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D := by
      rw [show f ⟨g₁, ν₁⟩ = f ⟨g₂, ν₂⟩ from heq, inv_mul_cancel]; exact Subgroup.one_mem _
    obtain ⟨rfl, rfl⟩ := key g₁ h₁.1 ν₁ h₁.2 g₂ h₂.1 ν₂ h₂.2 hc
    rfl

end GlobalTheory.LowerHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentativesStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_diag_doubleCoset_representatives : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  first | exact @GlobalTheory.LowerHecke.repsBuild | exact GlobalTheory.LowerHecke.repsBuild | (intros; apply GlobalTheory.LowerHecke.repsBuild <;> assumption)
end
end
