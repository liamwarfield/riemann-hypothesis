module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosDef

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosOf
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.LetterRowOperator
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FRSmulRight
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.MemHdIff
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def TE (K : Type) [CommRing K] (k : ℕ) (vec : Bool) (d : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k) K) : MvPolynomial (Fin k) K :=
  if vec then X a * pderiv b f else (if a = b then (d : K) • f else 0) - X b * pderiv a f

def RestAdj : Prop :=
  ∀ (K : Type) [Field K] (k : ℕ) (a b : Fin k) (P Q : MvPolynomial (Fin k × Fin k) K),
    fockR (RE K k a b P) Q = fockR P (RE K k b a Q)

def RestStab : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (ν : Fin k → ℕ) (a b : Fin k), ∀ P ∈ dualWeyl K k k ν, RE K k a b P ∈ dualWeyl K k k ν

def RestTheta : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)), ∀ P ∈ Hd K (m + 1) d,
    RE K (m + 1) a b (theta K m vec P) = theta K m vec (TE K (m + 1) vec d a b P)

def RestWt : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0

def RestRep : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d : ℕ),
    (∀ P ∈ Hd K (m + 1) d, (∀ Q ∈ Hd K (m + 1) d, fockR (theta K m vec P) (theta K m vec Q) = 0) → P = 0)

theorem RE_mul (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  unfold RE
  simp only [MvPolynomial.pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun t _ => ?_ <;> ring

theorem RE_add (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f + g) = RE K k a b f + RE K k a b g := by
  unfold RE
  simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem mem_Hd_iff {K : Type} [CommRing K] {k d : ℕ} (P : MvPolynomial (Fin k) K) :
    P ∈ Hd K k d ↔ P ∈ homogeneousSubmodule (Fin k) K d := by
  rw [Formalism.L2.G.Model.mem_Hd, mem_homogeneousSubmodule]
  constructor
  · intro h μ hμ
    have := h μ (mem_support_iff.2 hμ)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  · intro h μ hμ
    have := h (mem_support_iff.1 hμ)
    rw [← this]
    simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem EdWord_coe (K : Type) [Field K] (k d : ℕ) (l : List (Fin k × Fin k)) (P : ↥(homogeneousSubmodule (Fin k) K d)) :
    ((EdWord K k d l P : ↥(homogeneousSubmodule (Fin k) K d)) : MvPolynomial (Fin k) K) =
      word1 l (P : MvPolynomial (Fin k) K) := by
  induction l with
  | nil => simp [EdWord, word1]
  | cons y l ih =>
    have : EdWord K k d (y :: l) = Ed K k d y.1 y.2 * EdWord K k d l := by simp [EdWord]
    rw [this, Module.End.mul_apply]
    show X y.1 * pderiv y.2 ((EdWord K k d l P : ↥(homogeneousSubmodule (Fin k) K d)) : MvPolynomial (Fin k) K) = _
    rw [ih]
    rfl

end Formalism.MainNotions.TestSideCounting
end
end

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

section F

variable {τ K : Type} [CommRing K]

theorem fR_symm (f g : MvPolynomial τ K) : fockR f g = fockR g f := (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g 0).2.2
theorem fR_add_left (f f' g : MvPolynomial τ K) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f f' g 0).1
theorem fR_smul_left (a : K) (f g : MvPolynomial τ K) : fockR (a • f) g = a * fockR f g :=
  (Formalism.L2.G.Model.TS.Top.fockRBilin τ K f 0 g a).2.1
theorem fR_add_right (f g g' : MvPolynomial τ K) : fockR f (g + g') = fockR f g + fockR f g' := by
  rw [fR_symm, fR_add_left, fR_symm g, fR_symm g']
theorem fR_smul_right (a : K) (f g : MvPolynomial τ K) : fockR f (a • g) = a * fockR f g := by
  rw [fR_symm, fR_smul_left, fR_symm g]
theorem fR_neg_left (f g : MvPolynomial τ K) : fockR (-f) g = -fockR f g := by
  have := fR_smul_left (-1 : K) f g
  simpa using this
theorem fR_sub_left (f f' g : MvPolynomial τ K) : fockR (f - f') g = fockR f g - fockR f' g := by
  rw [sub_eq_add_neg, fR_add_left, fR_neg_left, ← sub_eq_add_neg]
theorem fR_sub_right (f g g' : MvPolynomial τ K) : fockR f (g - g') = fockR f g - fockR f g' := by
  rw [fR_symm, fR_sub_left, fR_symm g, fR_symm g']

end F

abbrev VV (K : Type) [Field K] (m d : ℕ) := ↥(homogeneousSubmodule (Fin (m + 1)) K d)

def thV (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) : VV K m d →ₗ[K] MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (theta K m vec).toLinearMap ∘ₗ (homogeneousSubmodule (Fin (m + 1)) K d).subtype

def RestRep2 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (m : ℕ), 1 ≤ m → ∀ (vec : Bool) (d : ℕ) (f : Module.Dual K (VV K m d)),
    ∃ P : VV K m d, ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = f Q

def cForm (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    VV K m d →ₗ[K] Module.Dual K (VV K m d) :=
  LinearMap.mk₂ K (fun P Q => fockR (thV K m vec d P * s) (thV K m vec d Q * β))
    (fun P P' Q => by rw [map_add (f := _), add_mul, fR_add_left])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_left, smul_eq_mul])
    (fun P Q Q' => by rw [map_add (f := _), add_mul, fR_add_right])
    (fun t P Q => by rw [map_smul, smul_mul_assoc, fR_smul_right, smul_eq_mul])

theorem cForm_apply (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
    (P Q : VV K m d) : cForm K m vec d β s P Q = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := rfl

theorem uniqV (hR : RestRep) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : VV K m d)
    (h : ∀ Q, fockR (thV K m vec d P) (thV K m vec d Q) = 0) : P = 0 := by
  apply Subtype.ext
  exact hR K m hm vec d P.1 ((mem_Hd_iff _).2 P.2) fun Q hQ => h ⟨Q, (mem_Hd_iff _).1 hQ⟩

theorem exists_A (hR : RestRep) (hR2 : RestRep2) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) (vec : Bool) (d : ℕ) :
    ∃ A : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → Module.End K (VV K m d),
      ∀ β s P Q, fockR (thV K m vec d (A β s P)) (thV K m vec d Q) = fockR (thV K m vec d P * s) (thV K m vec d Q * β) := by
  have hb : Function.Bijective (cForm K m vec d 1 1) := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro P hP
      apply uniqV hR hm vec d P
      intro Q
      have := congrArg (fun f => f Q) hP
      simpa [cForm] using this
    · intro f
      obtain ⟨P, hP⟩ := hR2 K m hm vec d f
      refine ⟨P, LinearMap.ext fun Q => ?_⟩
      simpa [cForm] using hP Q
  let e := LinearEquiv.ofBijective (cForm K m vec d 1 1) hb
  refine ⟨fun β s => e.symm.toLinearMap ∘ₗ cForm K m vec d β s, fun β s P Q => ?_⟩
  have h1 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) = cForm K m vec d β s P := e.apply_symm_apply _
  have h2 : cForm K m vec d 1 1 (e.symm (cForm K m vec d β s P)) Q = cForm K m vec d β s P Q := by rw [h1]
  rw [cForm_apply, cForm_apply, mul_one, mul_one] at h2
  exact h2

end Formalism.MainNotions.TestSideCounting
end
end

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

def letterRowOperator (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) : Module.End K (VV K m d) :=
  if vec then Ed K (m + 1) d a b else (if a = b then (d : K) • (1 : Module.End K (VV K m d)) else 0) - Ed K (m + 1) d b a

theorem letter_operator_matches_row_operator (hT : RestTheta) (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) (P : VV K m d) :
    thV K m vec d (letterRowOperator K m vec d a b P) = RE K (m + 1) a b (thV K m vec d P) := by
  have h := hT K m vec d a b P.1 ((mem_Hd_iff _).2 P.2)
  show theta K m vec ((letterRowOperator K m vec d a b P : VV K m d) : MvPolynomial (Fin (m + 1)) K) = RE K (m + 1) a b (theta K m vec P.1)
  rw [h]
  congr 1
  unfold letterRowOperator TE
  cases vec
  · by_cases hab : a = b
    · simp [hab, Ed]
    · simp [hab, Ed]
  · simp [Ed]

set_option maxHeartbeats 1000000 in
theorem comm_A (hAdj : RestAdj) (hT : RestTheta) (hR : RestRep) {K : Type} [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m)
    (vec : Bool) (d : ℕ)
    (A : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K → Module.End K (VV K m d))
    (hA : ∀ β s P Q, fockR (thV K m vec d (A β s P)) (thV K m vec d Q) = fockR (thV K m vec d P * s) (thV K m vec d Q * β))
    (a b : Fin (m + 1)) (β s : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :
    letterRowOperator K m vec d a b * A β s - A β s * letterRowOperator K m vec d a b = A β (RE K (m + 1) a b s) - A (RE K (m + 1) b a β) s := by
  apply LinearMap.ext
  intro P
  rw [← sub_eq_zero]
  apply uniqV hR hm vec d
  intro Q
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, fR_sub_left, hA]
  rw [letter_operator_matches_row_operator hT, hAdj, ← letter_operator_matches_row_operator hT, hA, letter_operator_matches_row_operator hT, letter_operator_matches_row_operator hT]
  have e1 : RE K (m + 1) b a (thV K m vec d Q) * β =
      RE K (m + 1) b a (thV K m vec d Q * β) - thV K m vec d Q * RE K (m + 1) b a β := by
    rw [RE_mul]; ring
  rw [e1, fR_sub_right, ← hAdj, RE_mul, fR_add_left]
  ring

end Formalism.MainNotions.TestSideCounting
end
end

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL)
open Formalism.L2.G.Model.TS (fockR)

theorem Ed_comm_eq (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ) (a b : Fin (m + 1)) (X : Module.End K (VV K m d)) :
    Ed K (m + 1) d a b * X - X * Ed K (m + 1) d a b =
      if vec = true then letterRowOperator K m vec d a b * X - X * letterRowOperator K m vec d a b
      else -(letterRowOperator K m vec d b a * X - X * letterRowOperator K m vec d b a) := by
  cases vec
  · simp only [Bool.false_eq_true, if_false, letterRowOperator]
    split_ifs
    · rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
      abel
    · rw [zero_sub, neg_mul, mul_neg]
      abel
  · simp [letterRowOperator]


set_option maxHeartbeats 2000000 in
theorem onePos_of (hOB : OpBound) (hAdj : RestAdj) (hSt : RestStab) (hT : RestTheta) (hW : RestWt) (hR : RestRep)
    (hR2 : RestRep2) : OnePos := by
  intro K _ _ m hm vec d c ν hν hνc β hβ s hs
  obtain ⟨A, hA⟩ := exists_A (K := K) hR hR2 hm vec d
  have huniq : ∀ T T' : Module.End K (VV K m d),
      (∀ P Q, fockR (thV K m vec d (T P)) (thV K m vec d Q) =
        fockR (thV K m vec d (T' P)) (thV K m vec d Q)) → T = T' := by
    intro T T' h
    refine LinearMap.ext fun P => ?_
    have h0 := uniqV hR hm vec d (T P - T' P) (fun Q => by rw [map_sub, fR_sub_left, h P Q, sub_self])
    exact sub_eq_zero.1 h0
  have hadd1 : ∀ x x' y, A (x + x') y = A x y + A x' y := by
    intro x x' y
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add (f := _), fR_add_left, hA, hA, hA, mul_add, fR_add_right]
  have hsmul1 : ∀ (t : K) x y, A (t • x) y = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_right]
  have hadd2 : ∀ x y y', A x (y + y') = A x y + A x y' := by
    intro x y y'
    apply huniq
    intro P Q
    rw [LinearMap.add_apply, map_add (f := _), fR_add_left, hA, hA, hA, mul_add, fR_add_left]
  have hsmul2 : ∀ (t : K) x y, A x (t • y) = t • A x y := by
    intro t x y
    apply huniq
    intro P Q
    rw [LinearMap.smul_apply, map_smul, fR_smul_left, hA, hA, mul_smul_comm, fR_smul_left]
  let Aₗ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) K →ₗ[K] Module.End K (VV K m d) :=
    LinearMap.mk₂ K A hadd1 hsmul1 hadd2 hsmul2
  obtain ⟨J, bs, μ, hspan, hRE, hμ⟩ := hW K m ν hν
  let WW := Submodule.map₂ Aₗ (dualWeyl K (m + 1) (m + 1) ν) (dualWeyl K (m + 1) (m + 1) ν)
  let Sg := Set.image2 (fun x y => Aₗ x y) (Set.range bs) (Set.range bs)
  have hWWspan : WW = Submodule.span K Sg := by
    show Submodule.map₂ Aₗ _ _ = _
    rw [← hspan, Submodule.map₂_span_span]
  have hbmem : ∀ i, bs i ∈ dualWeyl K (m + 1) (m + 1) ν := fun i => by
    rw [← hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hAmem : ∀ x y, x ∈ dualWeyl K (m + 1) (m + 1) ν → y ∈ dualWeyl K (m + 1) (m + 1) ν →
      A x y ∈ WW := fun x y hx hy => Submodule.apply_mem_map₂ Aₗ hx hy
  have hcomm : ∀ x y (a a' : Fin (m + 1)), x ∈ dualWeyl K (m + 1) (m + 1) ν →
      y ∈ dualWeyl K (m + 1) (m + 1) ν →
      Ed K (m + 1) d a a' * A x y - A x y * Ed K (m + 1) d a a' ∈ WW := by
    intro x y a a' hx hy
    rw [Ed_comm_eq K m vec d a a' (A x y)]
    split_ifs
    · rw [comm_A hAdj hT hR hm vec d A hA a a' x y]
      exact WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a a' y hy)) (hAmem _ _ (hSt K (m + 1) ν a' a x hx) hy)
    · rw [comm_A hAdj hT hR hm vec d A hA a' a x y]
      exact WW.neg_mem (WW.sub_mem (hAmem _ _ hx (hSt K (m + 1) ν a' a y hy))
        (hAmem _ _ (hSt K (m + 1) ν a a' x hx) hy))
  have hstab : ∀ A' ∈ WW, ∀ a a' : Fin (m + 1),
      Ed K (m + 1) d a a' * A' - A' * Ed K (m + 1) d a a' ∈ WW := by
    intro A' hA' a a'
    rw [hWWspan] at hA'
    induction hA' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ := hx
      exact hcomm _ _ a a' (hbmem i) (hbmem j)
    | zero => simp
    | add x y _ _ hx hy =>
      have e : Ed K (m + 1) d a a' * (x + y) - (x + y) * Ed K (m + 1) d a a' =
          (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') +
            (Ed K (m + 1) d a a' * y - y * Ed K (m + 1) d a a') := by
        rw [mul_add, add_mul]
        abel
      rw [e]
      exact WW.add_mem hx hy
    | smul t x _ hx =>
      have e : Ed K (m + 1) d a a' * (t • x) - (t • x) * Ed K (m + 1) d a a' =
          t • (Ed K (m + 1) d a a' * x - x * Ed K (m + 1) d a a') := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]
      exact WW.smul_mem t hx
  have hwt : ∀ A' ∈ Sg, ∃ ω : Fin (m + 1) → ℤ,
      (∀ a, Ed K (m + 1) d a a * A' - A' * Ed K (m + 1) d a a = (ω a : K) • A') ∧ ∀ a, ω a ≤ c := by
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    refine ⟨fun a => if vec then (μ j a : ℤ) - μ i a else (μ i a : ℤ) - μ j a, fun a => ?_, fun a => ?_⟩
    · show Ed K (m + 1) d a a * A (bs i) (bs j) - A (bs i) (bs j) * Ed K (m + 1) d a a = _
      rw [Ed_comm_eq K m vec d a a (A (bs i) (bs j)), comm_A hAdj hT hR hm vec d A hA a a (bs i) (bs j),
        hRE j a, hRE i a, hsmul1, hsmul2]
      dsimp only
      rw [show (Aₗ (bs i)) (bs j) = A (bs i) (bs j) from rfl]
      split_ifs <;> push_cast <;> rw [sub_smul] <;> abel
    · dsimp only
      have h1 := hμ j a
      have h2 := hμ i a
      split_ifs <;> omega
  have hmain := hOB K (m + 1) d c WW Sg hstab hWWspan hwt (A β s) (hAmem β s hβ hs)
  have hset : {B | ∃ l : List (Fin (m + 1) × Fin (m + 1)), l.length ≤ c ∧ B = EdWord K (m + 1) d l} =
      EdWord K (m + 1) d '' {l | l.length ≤ c} := by
    ext B
    simp [eq_comm]
  rw [hset, Finsupp.mem_span_image_iff_linearCombination] at hmain
  obtain ⟨f, hf, hfA⟩ := hmain
  refine ⟨f.support, f, fun l hl => (Finsupp.mem_supported K f).1 hf hl, ?_⟩
  intro P hP Q hQ
  have hP' : P ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff P).1 hP
  have hQ' : Q ∈ homogeneousSubmodule (Fin (m + 1)) K d := (mem_Hd_iff Q).1 hQ
  have h1 := hA β s ⟨P, hP'⟩ ⟨Q, hQ'⟩
  have hcoe : ((A β s ⟨P, hP'⟩ : VV K m d) : MvPolynomial (Fin (m + 1)) K) =
      ∑ l ∈ f.support, f l • word1 l P := by
    rw [← hfA, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, EdWord_coe]
  calc fockR (theta K m vec P * s) (theta K m vec Q * β)
      = fockR (thV K m vec d ⟨P, hP'⟩ * s) (thV K m vec d ⟨Q, hQ'⟩ * β) := rfl
    _ = fockR (thV K m vec d (A β s ⟨P, hP'⟩)) (thV K m vec d ⟨Q, hQ'⟩) := h1.symm
    _ = fockR (theta K m vec (∑ l ∈ f.support, f l • word1 l P)) (theta K m vec Q) := by
      rw [← hcoe]
      rfl

end Formalism.MainNotions.TestSideCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RowGenCoeffZero
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model.TS (fockR)

theorem RE_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (v : Fin k × Fin k) :
    RE K k a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  unfold RE
  simp only [pderiv_X]
  by_cases h : v.1 = b
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have : ((b, v.2) : Fin k × Fin k) = v := Prod.ext h.symm rfl
      rw [this, Pi.single_eq_same, mul_one]
    · intro t _ ht
      rw [Pi.single_eq_of_ne, mul_zero]
      intro hv
      apply ht
      rw [hv]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hv
    apply h
    rw [hv]

theorem RE_C (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  unfold RE
  simp

theorem rowGen_coeff_zero (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    (rowGen K a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

theorem RE_eq_rowDiv (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b f = rowDiv K a b 1 f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C r => rw [RE_C]; simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]
  | add p q hp hq => rw [RE_add, map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [RE_mul, map_mul, Polynomial.mul_coeff_one, rowGen_coeff_zero, rowGen_coeff_zero, hp, RE_X]
    have : (rowGen K a b (X v)).coeff 1 = if v.1 = b then X (a, v.2) else 0 := by
      simp only [rowGen, aeval_X]
      split_ifs <;> simp [Polynomial.coeff_C]
    rw [this]
    ring

theorem restAdj : RestAdj := by
  intro K _ k a b P Q
  rw [RE_eq_rowDiv, RE_eq_rowDiv]
  exact Formalism.L2.G.Model.TS.Top.fockRRowDivAdj K k k a b 1 P Q

theorem restStab : RestStab := by
  intro K _ _ k ν a b P hP
  rw [RE_eq_rowDiv]
  exact rowDivStable K k k ν a b 1 P hP

end Formalism.MainNotions.TestSideCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThetaInjHd
open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (theta Hd nuL psi qf)
open Formalism.L2.G.Model.TS (fockR)

theorem nuL_anti (m d : ℕ) (vec : Bool) : Antitone (nuL m d vec) := by
  intro a b hab
  cases vec
  · simp only [nuL, Bool.false_eq_true, if_false]
    by_cases ha : a = Fin.last m
    · have hb : b = Fin.last m := le_antisymm (Fin.le_last _) (ha ▸ hab)
      simp [ha, hb]
    · split_ifs <;> omega
  · simp only [nuL, if_true]
    by_cases hb : b = 0
    · have ha : a = 0 := le_antisymm (hb ▸ hab) (Fin.zero_le _)
      simp [ha, hb]
    · split_ifs <;> omega

theorem theta_inj_Hd (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : MvPolynomial (Fin (m + 1)) K)
    (hP : P ∈ Hd K (m + 1) d) (h : theta K m vec P = 0) : P = 0 := by
  have h1 : (psi K m vec).comp (theta K m vec) = aeval (fun c => qf K m vec * X c) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply, theta, aeval_X]
    exact Formalism.L2.G.Model.psi_Nv K m hm vec c
  have h2 := congrArg (fun f => f P) h1
  simp only [AlgHom.comp_apply, h, map_zero] at h2
  rw [Formalism.L2.G.Model.scaleHd _ P hP] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact absurd h3 (pow_ne_zero _ (Formalism.L2.G.Model.qf_ne K m vec))
  · exact h3

theorem theta_mem (K : Type) [Field K] (m : ℕ) (hm : 1 ≤ m) (vec : Bool) (d : ℕ) (P : MvPolynomial (Fin (m + 1)) K)
    (hP : P ∈ Hd K (m + 1) d) : theta K m vec P ∈ dualWeyl K (m + 1) (m + 1) (nuL m d vec) := by
  rw [← Formalism.L2.G.Model.theta_Hd K m hm d vec]
  exact ⟨P, hP, rfl⟩

theorem restRep : RestRep := by
  intro K _ _ m hm vec d P hP h
  apply theta_inj_Hd K m hm vec d P hP
  apply Formalism.L2.G.Model.TS.Top.nondegK K (m + 1) (m + 1) le_rfl (nuL m d vec) (nuL_anti m d vec) _ (theta_mem K m hm vec d P hP)
  intro P' hP'
  rw [← Formalism.L2.G.Model.theta_Hd K m hm d vec] at hP'
  obtain ⟨Q, hQ, rfl⟩ := hP'
  rw [fR_symm]
  exact h Q hQ

theorem restRep2 : RestRep2 := by
  intro K _ _ m hm vec d f
  have hfinW : FiniteDimensional K ↥(dualWeyl K (m + 1) (m + 1) (nuL m d vec)) := by
    obtain ⟨b, hb, -⟩ := sSBasis K (m + 1) (m + 1) (nuL m d vec)
    have : Finite ↥(ssIdx (m + 1) (m + 1) (nuL m d vec)) := (sSIdxFinite (m + 1) (m + 1) (nuL m d vec)).to_subtype
    rw [← hb.2.1]
    exact FiniteDimensional.span_of_finite K (Set.finite_range b)
  let φ : VV K m d →ₗ[K] ↥(dualWeyl K (m + 1) (m + 1) (nuL m d vec)) :=
    LinearMap.codRestrict _ (thV K m vec d) (fun P => theta_mem K m hm vec d P.1 ((mem_Hd_iff _).2 P.2))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply Subtype.ext
    apply theta_inj_Hd K m hm vec d P.1 ((mem_Hd_iff _).2 P.2)
    exact congrArg Subtype.val hP
  have hfinV : FiniteDimensional K (VV K m d) := FiniteDimensional.of_injective φ hφ
  have hinj : Function.Injective (cForm K m vec d 1 1) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro P hP
    apply uniqV restRep hm vec d P
    intro Q
    have h2 : cForm K m vec d 1 1 P Q = 0 := by rw [hP]; rfl
    rw [cForm_apply, mul_one, mul_one] at h2
    exact h2
  have hsurj : Function.Surjective (cForm K m vec d 1 1) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨P, hP⟩ := hsurj f
  refine ⟨P, fun Q => ?_⟩
  rw [← hP, cForm_apply, mul_one, mul_one]

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

theorem onePos_of_opBound (hOB : OpBound) (hT : RestTheta) (hW : RestWt) : OnePos :=
  onePos_of hOB restAdj restStab hT hW restRep restRep2

end Formalism.MainNotions.TestSideCounting
