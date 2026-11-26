module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnitCongruentToInteger

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.Development
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Defs

variable {E K : Type} [Field E] [NumberField E] [Field K]

def RS (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ℕ) (H : (ι → E) → K) : K :=
  (((qOf P : K) ^ B)⁻¹) ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => valsQ E (qOf P) A B), H t

def Good (P : HeightOneSpectrum (𝓞 E)) {ι : Type} (a b : ℕ) (H : (ι → E) → K) : Prop :=
  (∀ t, H t ≠ 0 → ∀ l, IntAt P ((qOf P : E) ^ a * t l)) ∧
  (∀ t δ : ι → E, (∀ l, IntAt P (δ l / (qOf P : E) ^ b)) → H (t + δ) = H t)

end Defs

section Defs2

variable {E : Type} [Field E]

def resX {n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : (Fin n → E) →ₗ[E] (Fin n → E) :=
  Matrix.toLin' (Matrix.of fun (l p : Fin n) => ρ (eN E (n + c) p.1) (Fin.castAdd c l))

def Tr {n' c' n c : ℕ} (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (t : FC n' c' n c → E) : FC n' c' n c → E :=
  fun f => (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) t) (eN E (n' + c') f.1.2.1) f.1.1

end Defs2

def StabP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ((qOf P : ℕ) : K) ≠ 0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a b : ℕ) (H : (ι → E) → K), Good P a b H →
      ∀ A B : ℕ, a ≤ A → b ≤ B → RS P A B H = RS P a b H

def CoVP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ((qOf P : ℕ) : K) ≠ 0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : (ι → E) ≃ₗ[E] (ι → E)) (τ : ι → E),
      ∃ c : K, c ≠ 0 ∧ ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
        Good P a' b' (fun t => H (L t + τ)) ∧ RS P a' b' (fun t => H (L t + τ)) = c * RS P a b H

def JLawP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n kj : ℕ), r = kj + c → k₀ ≤ kj → kj ≤ n → r ≤ n' + c' → k₀ ≤ n' →
    ∀ κ ∈ JQ P (qOf P) kj n c, ∃ lam : K, lam ≠ 0 ∧ ∀ y : HomE E (n' + c') (n + c),
      PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n (κ.symm.toLinearMap ∘ₗ y) = lam * PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n y

def MuNeP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), cq ≠ 0 → ∀ a : E, a ≠ 0 → locChar (P := P) (q := qOf P) cq χ a ≠ 0

def OmStepP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (sq cq : K), sq ≠ 0 → cq ≠ 0 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n kj : ℕ), r = kj + c → k₀ ≤ kj → kj ≤ n → r ≤ n' + c' → k₀ ≤ n' →
    ∀ (g₀ : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)) (h ρ κ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)),
      κ ∈ JQ P (qOf P) kj n c → ∃ C : K, C ≠ 0 ∧ ∀ x : HomE E (n' + c') (n + c),
        om (locChar (P := P) (q := qOf P) cq ξ⁻¹) (vP P (qOf P)) sq g₀ (ρ * h * κ) (PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n) x =
          C * om (locChar (P := P) (q := qOf P) cq ξ⁻¹) (vP P (qOf P)) sq g₀ h (PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n)
            ((ρ⁻¹).toLinearMap ∘ₗ x)

def PhiSuppP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n → k₀ ≤ n' →
    ∀ y : HomE E (n' + c') (n + c), PhiQ (q := q) (ξ := ξ) k₀ r c' n' c n y ≠ 0 →
      ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (y (eN E (n' + c') s) l)

def PhiPerP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (y ε : HomE E (n' + c') (n + c)),
      (∀ (s : ℕ) (l : Fin (n + c)), IntAt P (ε (eN E (n' + c') s) l / (qOf P : E))) →
      PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n (y + ε) = PhiQ (q := qOf P) (ξ := ξ) k₀ r c' n' c n y

def BddEntP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (R : Ranks) (j : ℕ)
    (h : AutYL E R j), BddL R P j h →
      (∀ (s : ℕ) (l : Fin (R.N j + cOf R j)), IntAt P ((qOf P : E) ^ j * h (eN E _ s) l)) ∧
      (∀ (s : ℕ) (l : Fin (R.N j + cOf R j)), IntAt P (h.symm (eN E _ s) l))

def GSuppP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (a b : ℕ) (mu : E → K) (v : E → ℤ) (sq : K) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) (Φ : SF E K a b) (j : ℕ),
    (∀ y, Φ y ≠ 0 → ∀ (s : ℕ) (l : Fin b), IntAt P (y (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin a), IntAt P (g₀.symm (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin b), IntAt P ((qOf P : E) ^ j * h (eN E b s) l)) →
    ∀ x, om mu v sq g₀ h Φ x ≠ 0 → ∀ (s : ℕ) (l : Fin b), IntAt P ((qOf P : E) ^ j * x (eN E a s) l)

def GPerP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (a b : ℕ) (mu : E → K) (v : E → ℤ) (sq : K) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E))
    (h : (Fin b → E) ≃ₗ[E] (Fin b → E)) (Φ : SF E K a b) (e : ℕ),
    (∀ y ε : (Fin a → E) →ₗ[E] (Fin b → E),
      (∀ (s : ℕ) (l : Fin b), IntAt P (ε (eN E a s) l / (qOf P : E))) → Φ (y + ε) = Φ y) →
    (∀ (s : ℕ) (l : Fin a), IntAt P ((qOf P : E) ^ e * g₀ (eN E a s) l)) →
    (∀ (s : ℕ) (l : Fin b), IntAt P (h.symm (eN E b s) l)) →
    ∀ x δ : (Fin a → E) →ₗ[E] (Fin b → E),
      (∀ (s : ℕ) (l : Fin b), IntAt P (δ (eN E a s) l / (qOf P : E) ^ (e + 1))) →
      om mu v sq g₀ h Φ (x + δ) = om mu v sq g₀ h Φ x

def HGoodP : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)),
    (Ideal.absNorm P.asIdeal).Prime →
    ∀ (n' c' n c D j : ℕ), j ≤ D → ∀ psi : E → K, PsiOk D P psi →
    ∀ G : SF E K (n' + c') (n + c),
    (∀ x, G x ≠ 0 → ∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l)) →
    (∀ x δ : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E),
      (∀ (s : ℕ) (l : Fin (n + c)), IntAt P (δ (eN E (n' + c') s) l / (qOf P : E) ^ j)) → G (x + δ) = G x) →
    ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E),
      Good P j j (fun t : FC n' c' n c → E => G (xx1 y t) * psi (-chArg (xx1 y t)))

def ChArgBddP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c j : ℕ)
    (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)),
    (∀ (s : ℕ) (l : Fin (n + c)), IntAt P ((qOf P : E) ^ j * x (eN E (n' + c') s) l)) →
      IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) x)

def XXP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      ρ.toLinearMap ∘ₗ xx1 xj t = xx1 (resX ρ ∘ₗ xj) (Tr ρ t)

def TrAffP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∃ L : (FC n' c' n c → E) ≃ₗ[E] (FC n' c' n c → E), ∀ t, Tr ρ t = L t + Tr ρ 0

def ResXSurjP : Prop :=
  ∀ (E : Type) [Field E] (n' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ y : (Fin n' → E) →ₗ[E] (Fin n → E), ∃ xj, resX ρ ∘ₗ xj = y

def ChArgP : Prop :=
  ∀ (E : Type) [Field E] (n' c' n c : ℕ) (ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)), ρ ∈ R1 E n c →
    ∀ (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E),
      chArg (ρ.toLinearMap ∘ₗ xx1 xj t) = chArg (xx1 xj t) +
        chArg (ρ.toLinearMap ∘ₗ xx1 (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) (0 : FC n' c' n c → E))

end PI.TwistedEisensteinNonvanishing.W
end
end

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

def NTAll : Prop := IntegerIntegralIffDvd ∧ IntegralApproximationByInteger ∧ ElementEqPrimePowerMulUnit ∧ ValuationExponentUnique ∧ UnitCongruentToInteger

section IntAtLem

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem ia_mul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  obtain ⟨r', s', hs', h2⟩ := hb
  refine ⟨r * r', s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_mul, map_mul, ← h1, ← h2]
  ring

theorem ia_nat (k : ℕ) : IntAt P (k : E) :=
  ⟨k, 1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩

theorem ia_zero : IntAt P (0 : E) := by simpa using ia_nat P 0

theorem ia_one : IntAt P (1 : E) := by simpa using ia_nat P 1

theorem ia_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  exact ⟨-r, s, hs, by rw [map_neg, ← h1]; ring⟩

theorem ia_add {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r, s, hs, h1⟩ := ha
  obtain ⟨r', s', hs', h2⟩ := hb
  refine ⟨r * s' + r' * s, s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← h1, ← h2]
  ring

theorem ia_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  rw [sub_eq_add_neg]
  exact ia_add P ha (ia_neg P hb)

theorem ia_qpow (k : ℕ) : IntAt P ((qOf P : E) ^ k) := by
  have := ia_nat P (qOf P ^ k)
  push_cast at this
  exact this

theorem ia_sum {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ia_zero P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ia_add P (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ia_up {j D : ℕ} (hjD : j ≤ D) {z : E} (hz : IntAt P ((qOf P : E) ^ j * z)) :
    IntAt P ((qOf P : E) ^ D * z) := by
  have e : (qOf P : E) ^ D * z = (qOf P : E) ^ (D - j) * ((qOf P : E) ^ j * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hjD]
  rw [e]
  exact ia_mul P (ia_qpow P _) hz

theorem qE_ne (hp : (Ideal.absNorm P.asIdeal).Prime) : (qOf P : E) ≠ 0 :=
  Nat.cast_ne_zero.2 hp.ne_zero

theorem ia_div_down (hp : (Ideal.absNorm P.asIdeal).Prime) {b b' : ℕ} (hb : b' ≤ b) {x : E}
    (hx : IntAt P (x / (qOf P : E) ^ b)) : IntAt P (x / (qOf P : E) ^ b') := by
  have e : x / (qOf P : E) ^ b' = (qOf P : E) ^ (b - b') * (x / (qOf P : E) ^ b) := by
    have hq := qE_ne P hp
    field_simp
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hb]
  rw [e]
  exact ia_mul P (ia_qpow P _) hx

theorem ia_bound (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) :
    ∃ g : ℕ, IntAt P ((qOf P : E) ^ g * a) := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, mul_zero]; exact ia_zero P⟩
  obtain ⟨e, w, rfl, -, hw, -⟩ := hN.2.2.1 E P hp hq a ha
  refine ⟨(-e).toNat, ?_⟩
  have hq0 := qE_ne P hp
  have : (qOf P : E) ^ (-e).toNat * ((qOf P : E) ^ e * w) =
      (qOf P : E) ^ (((-e).toNat : ℤ) + e).toNat * w := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ hq0, ← zpow_natCast]
    congr 2
    omega
  rw [this]
  exact ia_mul P (ia_qpow P _) hw

end IntAtLem

section Val

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def UnitAt (w : E) : Prop := w ≠ 0 ∧ IntAt P w ∧ IntAt P w⁻¹


open Classical in
def vq (a : E) : ℤ := by
  classical
  exact if h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w then h.choose else 0

variable {P}

theorem unitAt_mul {w w' : E} (h : UnitAt P w) (h' : UnitAt P w') : UnitAt P (w * w') :=
  ⟨mul_ne_zero h.1 h'.1, ia_mul P h.2.1 h'.2.1, by rw [mul_inv]; exact ia_mul P h.2.2 h'.2.2⟩

theorem unitAt_one : UnitAt P (1 : E) := ⟨one_ne_zero, ia_one P, by rw [inv_one]; exact ia_one P⟩

variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
include hN hp hq

theorem vq_spec {a : E} (ha : a ≠ 0) : ∃ w : E, a = (qOf P : E) ^ vq (P := P) a * w ∧ UnitAt P w := by
  have h : ∃ e : ℤ, ∃ w : E, a = (qOf P : E) ^ e * w ∧ UnitAt P w := by
    obtain ⟨e, w, h1, h2, h3, h4⟩ := hN.2.2.1 E P hp hq a ha
    exact ⟨e, w, h1, h2, h3, h4⟩
  unfold vq
  rw [dite_eq_left h]
  exact h.choose_spec

theorem vq_eq {a w : E} {e : ℤ} (h : a = (qOf P : E) ^ e * w) (hw : UnitAt P w) : vq (P := P) a = e := by
  have ha : a ≠ 0 := by
    rw [h]
    exact mul_ne_zero (zpow_ne_zero _ (qE_ne P hp)) hw.1
  obtain ⟨w1, h1, hw1⟩ := vq_spec hN hp hq ha
  exact hN.2.2.2.1 E P hp hq _ _ w1 w hw1.1 hw1.2.1 hw1.2.2 hw.2.1 hw.2.2 (h1.symm.trans h)

theorem vq_mul {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) : vq (P := P) (a * b) = vq (P := P) a + vq (P := P) b := by
  obtain ⟨w, h1, hw⟩ := vq_spec hN hp hq ha
  obtain ⟨w', h2, hw'⟩ := vq_spec hN hp hq hb
  apply vq_eq hN hp hq _ (unitAt_mul hw hw')
  rw [zpow_add₀ (qE_ne P hp)]
  conv_lhs => rw [h1, h2]
  ring

theorem vq_one : vq (P := P) (1 : E) = 0 := vq_eq hN hp hq (by simp) unitAt_one

theorem vq_prod {ι : Type*} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ≠ 0) :
    vq (P := P) (∏ i ∈ s, f i) = ∑ i ∈ s, vq (P := P) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vq_one hN hp hq
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      vq_mul hN hp hq (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Val

end PI.TwistedEisensteinNonvanishing.W
