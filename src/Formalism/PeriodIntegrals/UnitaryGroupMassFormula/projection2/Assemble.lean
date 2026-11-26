module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.KappaZero
section -- merged from Formalism.PeriodIntegrals.OneCosetSharp
open NumberField IsDedekindDomain Module MvPolynomial

noncomputable section

namespace PI.OneCosetSharp

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 := hr.1 i _ (hs.2.2 i)
    have h2 := hr.2.2 i
    have key : (r * s) (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        r (s (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) +
          (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      show r (s _) - _ = _
      rw [map_sub]
      abel
    rw [key]
    exact Submodule.add_mem _ h1 h2

theorem R1cond_one : R1cond k n c 1 := by
  refine ⟨fun i v hv => hv, rfl, fun i => ?_⟩
  show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
  rw [sub_self]
  exact Submodule.zero_mem _

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

end Groups

section Data

variable {k K : Type} [CommRing k] [Field K]

abbrev SF (k K : Type) [CommRing k] (a b : ℕ) : Type := ((Fin a → k) →ₗ[k] (Fin b → k)) → K

def om {a b : ℕ} (mu : k → K) (v : k → ℤ) (sq : K) (g₀ : (Fin a → k) ≃ₗ[k] (Fin a → k))
    (h : (Fin b → k) ≃ₗ[k] (Fin b → k)) (Φ : SF k K a b) : SF k K a b := fun x =>
  mu (LinearEquiv.det g₀ : kˣ) * (mu (LinearEquiv.det h : kˣ))⁻¹ * sq ^ (-(v (LinearEquiv.det g₀ : kˣ)) * b) *
    sq ^ (v (LinearEquiv.det h : kˣ) * a) * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap)

variable (n' c' n c : ℕ)

def IsFree (l s : ℕ) : Prop := n' ≤ s ∧ (s - n' = c ∨ (1 ≤ s - n' ∧ (l < n ∨ l - n < s - n')))

instance (l s : ℕ) : Decidable (IsFree n' n c l s) := by unfold IsFree; infer_instance

abbrev FC : Type := {p : Fin (n + c) × Fin (n' + c') // IsFree n' n c p.1.1 p.2.1}

variable {n' c' n c}

def xx1 (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' c' n c → k) : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hf : IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
    else if hs : s.1 < n' then (if hl : l.1 < n then LinearMap.toMatrix' xj ⟨l.1, hl⟩ ⟨s.1, hs⟩ else 0)
    else if l.1 = n + (s.1 - n') then 1 else 0)

def chArg (x : (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k)) : k :=
  ∑ i ∈ Finset.range c, atN (x (eN k (n' + c') (n' + i + 1))) (n + i)

def E1 (psi : k → K) (vals : Finset k) (wt : K) (Φ : SF k K (n' + c') (n + c)) : SF k K n' n := fun xj =>
  wt ^ Fintype.card (FC n' c' n c) *
    ∑ t ∈ Fintype.piFinset fun _ : FC n' c' n c => vals, Φ (xx1 xj t) * psi (-chArg (xx1 xj t))

end Data

end Loc

namespace LocE

def fIdx (k₀ c n s : ℕ) : ℕ := if s < k₀ then s else if s < k₀ + c then n + (s - k₀) else s - c

end LocE

open Loc LocE

def chiV {k : Type} [Field k] [DecidableEq k] (χ : kˣ →* ℂˣ) (x : k) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)

def ent {k : Type} [Field k] {A B : ℕ} (k₀ cA nA cB nB : ℕ) (x : (Fin A → k) →ₗ[k] (Fin B → k)) (p p' : ℕ) : k :=
  atN (x (eN k A (fIdx k₀ cA nA p'))) (fIdx k₀ cB nB p)

def Allow (k₀ m t N p p' : ℕ) : Prop :=
  if p' < k₀ then p < p' ∨ (k₀ ≤ p ∧ p < k₀ + (m / 2 - 1))
  else if p' < k₀ + m - 1 then (k₀ ≤ p ∧ p < p') ∨ (m / 2 < p' + 1 - k₀ ∧ p < k₀)
  else p < k₀ + m - 1 ∨ (p < N ∧ (p - (k₀ + m - 1)) / t ≤ (p' - (k₀ + m - 1)) / t)


open Classical in
def PhiS {k : Type} [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ) : SF k ℂ (n' + (c + 1)) (n + c) := by
  classical
  exact fun x =>
    let M := ent k₀ (c + 1) n' c n x
    let r := k₀ + m - 1
    let a := r + (j - 1) * t
    if (∀ p', p' < r → M p' p' = 1) ∧ (∀ p p', p < n + c → p' < a → p ≠ p' → M p p' ≠ 0 → Allow k₀ m t a p p')
    then ψ₀ (∑ i ∈ Finset.range (r - 1), M i (i + 1)) *
        (∏ i ∈ Finset.range (j - 1),
          chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)))) *
        (chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin a => M s.1 s'.1)))⁻¹
    else 0

def InJS {k : Type} [Field k] (k₀ m t c n : ℕ) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ p', p' < k₀ + m - 1 → ent k₀ c n c n κ.toLinearMap p' p' = 1) ∧
    ∀ p p', p < n + c → p' < n + c → p ≠ p' → ent k₀ c n c n κ.toLinearMap p p' ≠ 0 → Allow k₀ m t (n + c) p p'

def OneCosetSharp : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    1 ≤ k₀ → Even m → 4 ≤ m → 1 ≤ j → j ≤ m - 2 → c = m - 1 - j →
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t → n + c = k₀ + m - 1 + j * t →
    (∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ) ∧
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0

end PI.OneCosetSharp

end
end

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

def Nums (k₀ m t j n' c n : ℕ) : Prop :=
  1 ≤ k₀ ∧ Even m ∧ 4 ≤ m ∧ 1 ≤ j ∧ j ≤ m - 2 ∧ c = m - 1 - j ∧
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = k₀ + m - 1 + j * t

def Claim1 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ

def Claim2 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0

def PatClosed : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ₁ → InJS k₀ m t c n κ₂ →
      InJS k₀ m t c n (κ₁ * κ₂) ∧ InJS k₀ m t c n κ₁⁻¹

def KappaZero : Prop :=
  ∀ (k : Type) [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k), PhiS ψ₀ χ k₀ m t j n' c n y ≠ 0 →
      ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ ∧
        ∀ p < n' + (c + 1), κ (eN k (n + c) (fIdx k₀ c n p)) = y (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p))

def NElem : Prop :=
  ∀ (k : Type) [Field k] (n' c n : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k),
    ∃ ν ∈ R1 k n c, (∀ v, ν (inX k n c v) = inX k n c v) ∧
      ∀ i < c, ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i))

def GaStep : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) →
      (∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) → ∃ v, g (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v) →
      ∃ γ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ g = γ * κ

end PI.OneCosetSharp.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

theorem eN_eq_single {k : Type} [Field k] {N : ℕ} (i : ℕ) (hi : i < N) :
    eN k N i = Pi.single (⟨i, hi⟩ : Fin N) 1 := by
  ext l
  simp only [eN, Pi.single_apply, Fin.ext_iff]

theorem inX_apply {k : Type} [Field k] {n c : ℕ} (v : Fin n → k) (l : Fin (n + c)) :
    inX k n c v l = if h : l.1 < n then v ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs <;> rfl

theorem inX_of_zero {k : Type} [Field k] {n c : ℕ} (w : Fin (n + c) → k) (hw : ∀ l : Fin (n + c), n ≤ l.1 → w l = 0) :
    ∃ v, inX k n c v = w := by
  refine ⟨fun i => w ⟨i.1, by omega⟩, ?_⟩
  ext l
  rw [inX_apply]
  split_ifs with h
  · rfl
  · exact (hw l (not_lt.mp h)).symm

theorem embedMatrix_basisVec_apply_of_le {k : Type} [Field k] {n' c n : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (tt : FC n' (c + 1) n c → k) (s : ℕ) (hs : s < n') (l : Fin (n + c)) (hl : n ≤ l.1) :
    xx1 xj tt (eN k (n' + (c + 1)) s) l = 0 := by
  have hl' : ¬ l.1 < n := not_lt.mpr hl
  rw [eN_eq_single s (by omega)]
  simp [xx1, Matrix.mulVec_single, IsFree, hs, hl', not_le.mpr hs]

theorem sum_step {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ)
    (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k))
    (hE : E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) :
    ∃ tt, PhiS ψ₀ χ k₀ m t j n' c n (h.symm.toLinearMap ∘ₗ xx1 xj tt) ≠ 0 := by
  by_contra H
  simp only [not_exists, not_not] at H
  apply hE
  simp [E1, om, H]

theorem fIdx_add_of_lt (k₀ c n i : ℕ) (hi : i < c) : fIdx k₀ c n (k₀ + i) = n + i := by
  unfold fIdx
  rw [if_neg (by omega), if_pos (by omega)]
  omega

theorem Nums.n'_ge {k₀ m t j n' c n : ℕ} (hn : Nums k₀ m t j n' c n) : k₀ ≤ n' := by
  obtain ⟨-, -, h4, hj1, hj2, hc, h7, -⟩ := hn
  generalize (j - 1) * t = X at h7
  omega

theorem claim1_of (hP : PatClosed) (hK : KappaZero) (hN : NElem) (hG : GaStep) : Claim1 := by
  intro k _ _ ψ₀ χ k₀ m t j n' c n hnum h ⟨xj, hE⟩
  obtain ⟨tt, htt⟩ := sum_step ψ₀ χ k₀ m t j n' c n h xj hE
  obtain ⟨κ, hκ, hκe⟩ := hK k ψ₀ χ k₀ m t j n' c n hnum _ htt
  obtain ⟨ν, hνR, hνX, hνe⟩ := hN k n' c n xj tt
  have hk₀ := Nums.n'_ge hnum
  have hνinv : ∀ y z, ν z = y → ν⁻¹ y = z := by
    intro y z hz
    rw [← hz]
    show (ν⁻¹ * ν) z = z
    rw [inv_mul_cancel]
    rfl
  have g1 : ∀ i < c, (ν⁻¹ * h * κ) (eN k (n + c) (n + i)) = eN k (n + c) (n + i) := by
    intro i hi
    have e1 := hκe (k₀ + i) (by omega)
    rw [fIdx_add_of_lt k₀ c n i hi, fIdx_add_of_lt k₀ (c + 1) n' i (by omega)] at e1
    show ν⁻¹ (h (κ (eN k (n + c) (n + i)))) = eN k (n + c) (n + i)
    rw [e1]
    apply hνinv
    rw [hνe i hi]
    simp
  have g2 : ∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) →
      ∃ v, (ν⁻¹ * h * κ) (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v := by
    intro p hp hcase
    have hs : fIdx k₀ (c + 1) n' p < n' := by
      unfold fIdx
      split_ifs <;> omega
    obtain ⟨v, hv⟩ := inX_of_zero (xx1 xj tt (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p)))
      (fun l hl => embedMatrix_basisVec_apply_of_le xj tt _ hs l hl)
    refine ⟨v, ?_⟩
    show ν⁻¹ (h (κ (eN k (n + c) (fIdx k₀ c n p)))) = inX k n c v
    rw [hκe p hp]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← hv]
    exact hνinv _ _ (hνX v)
  obtain ⟨γ, hγ, κ', hκ', hg⟩ := hG k k₀ m t j n' c n hnum (ν⁻¹ * h * κ) g1 g2
  have hκinv := (hP k k₀ m t j n' c n hnum κ κ hκ hκ).2
  refine ⟨ν * γ, mul_mem hνR hγ, κ' * κ⁻¹,
    (hP k k₀ m t j n' c n hnum κ' κ⁻¹ hκ' hκinv).1, ?_⟩
  calc h = ν * (ν⁻¹ * h * κ) * κ⁻¹ := by group
    _ = ν * γ * (κ' * κ⁻¹) := by rw [hg]; group

end PI.OneCosetSharp.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.AllowColLt
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE

noncomputable section

namespace PI.OneCosetSharp.W.P2

def S (k₀ m t N p q : ℕ) : Prop := p = q ∨ Allow k₀ m t N p q

theorem allow_col_lt {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : p < k₀ + m - 1 := by
  unfold Allow at h
  split_ifs at h <;> omega

theorem S_trans {k₀ m t N p q s : ℕ} (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q s) : S k₀ m t N p s := by
  rcases h1 with rfl | h1
  · exact h2
  rcases h2 with rfl | h2
  · exact Or.inr h1
  by_cases hps : p = s
  · exact Or.inl hps
  right
  unfold Allow at h1 h2 ⊢
  generalize (p - (k₀ + m - 1)) / t = bp at *
  generalize (q - (k₀ + m - 1)) / t = bq at *
  generalize (s - (k₀ + m - 1)) / t = bs at *
  split_ifs at h1 h2 ⊢ <;> omega

def φ (k₀ m p : ℕ) : ℕ := if p < k₀ then m + p else if p < k₀ + (m / 2 - 1) then p - k₀ else p + 2 * m + k₀

theorem allow_lt_φ {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : φ k₀ m p < φ k₀ m q := by
  unfold Allow at h
  unfold φ
  split_ifs at h ⊢ <;> omega

theorem S_antisymm {k₀ m t N p q : ℕ} (hp : p < k₀ + m - 1) (h1 : S k₀ m t N p q) (h2 : S k₀ m t N q p) : p = q := by
  rcases h1 with h1 | h1
  · exact h1
  rcases h2 with h2 | h2
  · exact h2.symm
  have hq := allow_col_lt hp h2
  have a := allow_lt_φ hq h1
  have b := allow_lt_φ hp h2
  omega

variable {k : Type} [Field k]

def alg (k₀ m t b : ℕ) : Submodule k (Matrix (Fin b) (Fin b) k) where
  carrier := {A | ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1}
  add_mem' := by
    intro A B hA hB p q h
    by_contra hs
    apply h
    simp only [Matrix.add_apply]
    rw [not_imp_comm.1 (hA p q) hs, not_imp_comm.1 (hB p q) hs, add_zero]
  zero_mem' := fun _ _ h => absurd rfl h
  smul_mem' := by
    intro a A hA p q h
    by_contra hs
    apply h
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [not_imp_comm.1 (hA p q) hs, mul_zero]

variable {k₀ m t b : ℕ}

theorem mem_alg {A : Matrix (Fin b) (Fin b) k} : A ∈ alg (k := k) k₀ m t b ↔ ∀ p q, A p q ≠ 0 → S k₀ m t b p.1 q.1 :=
  Iff.rfl

theorem alg_one : (1 : Matrix (Fin b) (Fin b) k) ∈ alg (k := k) k₀ m t b := by
  intro p q h
  left
  rw [Matrix.one_apply] at h
  split_ifs at h with hpq
  · exact congrArg Fin.val hpq
  · exact absurd rfl h

theorem alg_mul {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b) :
    A * B ∈ alg (k := k) k₀ m t b := by
  intro p q h
  rw [Matrix.mul_apply] at h
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact S_trans (hA p s (left_ne_zero_of_mul hs)) (hB s q (right_ne_zero_of_mul hs))

theorem alg_inv {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hBA : B * A = 1) :
    B ∈ alg (k := k) k₀ m t b := by
  let f : alg (k := k) k₀ m t b →ₗ[k] alg (k := k) k₀ m t b :=
    (LinearMap.mulLeft k A).restrict (fun X hX => alg_mul hA hX)
  have hf : ∀ X : alg (k := k) k₀ m t b, (f X).1 = A * X.1 := fun X => rfl
  have hinj : Function.Injective f := by
    intro X Y hXY
    have h1 : A * X.1 = A * Y.1 := by rw [← hf, ← hf, hXY]
    apply Subtype.ext
    have h2 := congrArg (B * ·) h1
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using h2
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨1, alg_one⟩
  have hAX : A * X.1 = 1 := by rw [← hf, hX]
  have : B = X.1 := by
    calc B = B * (A * X.1) := by rw [hAX, Matrix.mul_one]
      _ = X.1 := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [this]
  exact X.2

theorem alg_diag {A B : Matrix (Fin b) (Fin b) k} (hA : A ∈ alg (k := k) k₀ m t b) (hB : B ∈ alg (k := k) k₀ m t b)
    (p : Fin b) (hp : p.1 < k₀ + m - 1) : (A * B) p p = A p p * B p p := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · intro s _ hs
    by_contra h
    exact hs (Fin.ext (S_antisymm hp (hA p s (left_ne_zero_of_mul h)) (hB s p (right_ne_zero_of_mul h)))).symm
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p q : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hq : q < n + c)
    (h : fIdx k₀ c n p = fIdx k₀ c n q) : p = q := by
  unfold fIdx at h
  split_ifs at h <;> omega

def fe (k₀ c n : ℕ) (hk : k₀ ≤ n) : Fin (n + c) ≃ Fin (n + c) :=
  Equiv.ofBijective (fun p => ⟨fIdx k₀ c n p.1, fIdx_lt hk p.2⟩)
    (Finite.injective_iff_bijective.1 fun p q h => Fin.ext (fIdx_inj hk p.2 q.2 (congrArg Fin.val h)))

def Pm {c n : ℕ} (k₀ : ℕ) (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Matrix (Fin (n + c)) (Fin (n + c)) k :=
  (LinearMap.toMatrix' κ.toLinearMap).submatrix (fe k₀ c n hk) (fe k₀ c n hk)

theorem ent_eq {c n : ℕ} (hk : k₀ ≤ n) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) (p q : Fin (n + c)) :
    ent k₀ c n c n κ.toLinearMap p.1 q.1 = Pm k₀ hk κ p q := by
  have e : eN k (n + c) (fIdx k₀ c n q.1) = Pi.single (fe k₀ c n hk q) (1 : k) := by
    funext j'
    simp only [eN, Pi.single_apply, fe, Equiv.ofBijective_apply, Fin.ext_iff]
  simp only [Pm, Matrix.submatrix_apply, LinearMap.toMatrix'_apply, ent, atN, dif_pos (fIdx_lt hk p.2), e]
  rfl

theorem Pm_mul {c n : ℕ} (hk : k₀ ≤ n) (κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Pm k₀ hk (κ₁ * κ₂) = Pm k₀ hk κ₁ * Pm k₀ hk κ₂ := by
  have e : (κ₁ * κ₂).toLinearMap = κ₁.toLinearMap ∘ₗ κ₂.toLinearMap := LinearMap.ext fun _ => rfl
  rw [Pm, Pm, Pm, e, LinearMap.toMatrix'_comp, Matrix.submatrix_mul_equiv]

theorem Pm_one {c n : ℕ} (hk : k₀ ≤ n) : Pm (k := k) (c := c) (n := n) k₀ hk 1 = 1 := by
  have e : (1 : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)).toLinearMap = LinearMap.id := LinearMap.ext fun _ => rfl
  rw [Pm, e, LinearMap.toMatrix'_id, Matrix.submatrix_one_equiv]

theorem injs_iff {c n : ℕ} (hk : k₀ ≤ n) (hr : k₀ + m - 1 ≤ n + c) (κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    InJS k₀ m t c n κ ↔ Pm k₀ hk κ ∈ alg (k := k) k₀ m t (n + c) ∧ ∀ p : Fin (n + c), p.1 < k₀ + m - 1 → Pm k₀ hk κ p p = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p q h => ?_, fun p hp => ?_⟩
    · by_cases hpq : p = q
      · exact Or.inl (congrArg Fin.val hpq)
      · right
        refine h2 p.1 q.1 p.2 q.2 (fun e => hpq (Fin.ext e)) ?_
        rwa [ent_eq hk]
    · rw [← ent_eq hk]
      exact h1 p.1 hp
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => ?_, fun p q hp hq hpq h => ?_⟩
    · have := h2 ⟨p, by omega⟩ hp
      rwa [← ent_eq hk] at this
    · rw [show p = (⟨p, hp⟩ : Fin (n + c)).1 from rfl, show q = (⟨q, hq⟩ : Fin (n + c)).1 from rfl, ent_eq hk] at h
      rcases h1 _ _ h with h | h
      · exact absurd h hpq
      · exact h

theorem nums_le {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) : k₀ ≤ n ∧ k₀ + m - 1 ≤ n + c := by
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8⟩ := h
  generalize j * t = J at h8
  omega

end PI.OneCosetSharp.W.P2

namespace PI.OneCosetSharp.W

open P2 in
theorem patClosed : PatClosed := by
  intro k _ k₀ m t j n' c n hN κ₁ κ₂ h₁ h₂
  obtain ⟨hk, hr⟩ := nums_le hN
  rw [injs_iff hk hr] at h₁ h₂
  refine ⟨?_, ?_⟩
  · rw [injs_iff hk hr, Pm_mul]
    refine ⟨alg_mul h₁.1 h₂.1, fun p hp => ?_⟩
    rw [alg_diag h₁.1 h₂.1 p hp, h₁.2 p hp, h₂.2 p hp, mul_one]
  · have hBA : Pm k₀ hk κ₁⁻¹ * Pm k₀ hk κ₁ = 1 := by rw [← Pm_mul, inv_mul_cancel, Pm_one]
    have hB := alg_inv h₁.1 hBA
    rw [injs_iff hk hr]
    refine ⟨hB, fun p hp => ?_⟩
    have := congrFun (congrFun hBA p) p
    rw [alg_diag hB h₁.1 p hp, h₁.2 p hp, mul_one, Matrix.one_apply_eq] at this
    exact this

end PI.OneCosetSharp.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EntryEmbedMatrix
noncomputable section

namespace PI.OneCosetSharp.W.C2

open Loc LocE

variable {k : Type} [Field k]

theorem toLin'_eN {A B : ℕ} (X : Matrix (Fin B) (Fin A) k) (i : ℕ) (hi : i < A) :
    Matrix.toLin' X (eN k A i) = fun l => X l ⟨i, hi⟩ := by
  funext l
  rw [Matrix.toLin'_apply]
  show ∑ j, X l j * PI.OneCosetSharp.Loc.eN k A i j = X l ⟨i, hi⟩
  rw [Finset.sum_eq_single ⟨i, hi⟩]
  · simp [PI.OneCosetSharp.Loc.eN]
  · intro b _ hb
    have hb' : (b : ℕ) ≠ i := fun h => hb (Fin.ext h)
    simp [PI.OneCosetSharp.Loc.eN, hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

def xj0 (k₀ n' n : ℕ) : (Fin n' → k) →ₗ[k] (Fin n → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') =>
    if l.1 = (if s.1 < k₀ then s.1 else s.1 + 1) then (1 : k) else 0)

def τ0 (k₀ n' c n : ℕ) : FC n' (c + 1) n c → k := fun q =>
  if q.1.2.1 = n' + c ∧ q.1.1.1 = k₀ then 1 else 0

private theorem atN_of_lt' {N : ℕ} (v : Fin N → k) {i : ℕ} (h : i < N) : PI.OneCosetSharp.Loc.atN v i = v ⟨i, h⟩ := by
  unfold PI.OneCosetSharp.Loc.atN
  simp [h]

theorem entry_embedMatrix {n' c n : ℕ} (k₀ : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (τ : FC n' (c + 1) n c → k)
    (p p' : ℕ) (hp : fIdx k₀ c n p < n + c) (hp' : fIdx k₀ (c + 1) n' p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 xj τ) p p' =
      (if hf : IsFree n' n c (fIdx k₀ c n p) (fIdx k₀ (c + 1) n' p') then τ ⟨(⟨_, hp⟩, ⟨_, hp'⟩), hf⟩
       else if hs : fIdx k₀ (c + 1) n' p' < n' then
          (if hl : fIdx k₀ c n p < n then LinearMap.toMatrix' xj ⟨_, hl⟩ ⟨_, hs⟩ else 0)
       else if fIdx k₀ c n p = n + (fIdx k₀ (c + 1) n' p' - n') then 1 else 0) := by
  unfold PI.OneCosetSharp.ent PI.OneCosetSharp.Loc.xx1
  rw [toLin'_eN _ _ hp', atN_of_lt' _ hp]
  rfl

theorem facts {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) :
    k₀ ≤ n' ∧ 1 ≤ c ∧ k₀ + c < k₀ + m - 1 ∧ k₀ + m - 1 ≤ n' + (c + 1) ∧ n' + (c + 1) ≤ n + c ∧
      n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = n' + (c + 1) + t := by
  obtain ⟨h1, -, h4, hj1, hjm, hc, he1, he2⟩ := h
  have hjt : j * t = (j - 1) * t + t := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp [add_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, he1, ?_⟩ <;> omega

theorem fIdx_lt {k₀ c n p : ℕ} (_hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

private theorem fIdx_eq_cases (k₀ c n p : ℕ) :
    (p < k₀ ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p) ∨ (k₀ ≤ p ∧ p < k₀ + c ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = n + (p - k₀)) ∨
      (k₀ + c ≤ p ∧ PI.OneCosetSharp.LocE.fIdx k₀ c n p = p - c) := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

theorem ent_unit {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) (hcol : p' ≤ k₀ ∨ k₀ + c < p') :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' = if p = p' then 1 else 0 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hR := fIdx_eq_cases k₀ c n p
  have hS := fIdx_eq_cases k₀ (c + 1) n' p'
  have hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := fIdx_lt (by omega) hp
  have hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1) := fIdx_lt hk hp'
  rw [entry_embedMatrix k₀ _ _ p p' hrl hsl]
  generalize PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢
  generalize PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢
  simp only [xj0, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)

theorem ent_τ0 {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) (τ0 (k := k) k₀ n' c n)) p p' = if p = p' then 1 else 0 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hR := fIdx_eq_cases k₀ c n p
  have hS := fIdx_eq_cases k₀ (c + 1) n' p'
  have hrl : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := fIdx_lt (by omega) hp
  have hsl : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' < n' + (c + 1) := fIdx_lt hk hp'
  rw [entry_embedMatrix k₀ _ _ p p' hrl hsl]
  generalize PI.OneCosetSharp.LocE.fIdx k₀ c n p = r at hR hrl ⊢
  generalize PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' p' = s at hS hsl ⊢
  simp only [xj0, τ0, LinearMap.toMatrix'_toLin', Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; (try simp only [PI.OneCosetSharp.Loc.IsFree] at *); omega)

theorem chiV_one [DecidableEq k] (χ : kˣ →* ℂˣ) : chiV χ (1 : k) = 1 := by
  simp [PI.OneCosetSharp.chiV]

theorem sum_eq_chArg {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (τ : FC n' (c + 1) n c → k) :
    ∑ i ∈ Finset.range (k₀ + m - 1 - 1), ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) i (i + 1) =
      chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ) := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hsplit : k₀ + m - 1 - 1 = k₀ + (c + (k₀ + m - 1 - 1 - k₀ - c)) := by omega
  rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
  have hz : ∀ i, i + 1 < n' + (c + 1) → (i + 1 ≤ k₀ ∨ k₀ + c < i + 1) →
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 := by
    intro i hi hcol
    rw [ent_unit hN τ (by omega) hi hcol, if_neg (by omega)]
  have h1 : ∑ i ∈ Finset.range k₀, PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) i (i + 1) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      exact hz i (by omega) (by omega)
  have h3 : ∑ x ∈ Finset.range (k₀ + m - 1 - 1 - k₀ - c),
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + (c + x)) (k₀ + (c + x) + 1) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      rw [Finset.mem_range] at hx
      exact hz _ (by omega) (by omega)
  simp only [h1, h3, zero_add, add_zero]
  unfold PI.OneCosetSharp.Loc.chArg
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.mem_range] at he
  unfold PI.OneCosetSharp.ent
  have e1 : PI.OneCosetSharp.LocE.fIdx k₀ (c + 1) n' (k₀ + e + 1) = n' + e + 1 := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  have e2 : PI.OneCosetSharp.LocE.fIdx k₀ c n (k₀ + e) = n + e := by
    unfold PI.OneCosetSharp.LocE.fIdx
    split_ifs <;> omega
  rw [e1, e2]


open Classical in
theorem prod_blocks [DecidableEq k] {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    ∏ i ∈ Finset.range (j - 1), chiV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1) (k₀ + m - 1 + i * t + s'.1))) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_range] at hi
  have hit : i * t + t ≤ (j - 1) * t := by
    have h := Nat.mul_le_mul (show i + 1 ≤ j - 1 by omega) (le_refl t)
    rwa [add_mul, one_mul] at h
  have hM : (Matrix.of fun s s' : Fin t =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) (k₀ + m - 1 + i * t + s.1)
        (k₀ + m - 1 + i * t + s'.1)) = 1 := by
    ext s s'
    have hs1 := s.isLt
    have hs2 := s'.isLt
    rw [Matrix.of_apply, ent_unit hN τ (by omega) (by omega) (by omega), Matrix.one_apply]
    by_cases h : s = s'
    · subst h
      simp
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Fin.ext (by omega))
  rw [hM, Matrix.det_one, chiV_one]


open Classical in
theorem top_block [DecidableEq k] {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k)
    (hC : (∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
        ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p')) :
    chiV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) s.1 s'.1)) = 1 := by
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  have hdet : Matrix.det (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
      PI.OneCosetSharp.ent k₀ (c + 1) n' c n (PI.OneCosetSharp.Loc.xx1 (xj0 k₀ n' n) τ) s.1 s'.1) = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · apply Finset.prod_eq_one
      intro s _
      have hs1 := s.isLt
      rw [Matrix.of_apply]
      by_cases hs : s.1 < k₀ + m - 1
      · exact hC.1 s.1 hs
      · rw [ent_unit hN τ (by omega) (by omega) (by omega), if_pos rfl]
    · intro s s' hss
      have hss' : s'.1 < s.1 := hss
      have hs1 := s.isLt
      have hs2 := s'.isLt
      rw [Matrix.of_apply]
      by_cases hcol : s'.1 ≤ k₀ ∨ k₀ + c < s'.1
      · rw [ent_unit hN τ (by omega) (by omega) hcol, if_neg (by omega)]
      · by_contra hne
        have hA := hC.2 s.1 s'.1 (by omega) hs2 (by omega) hne
        unfold PI.OneCosetSharp.Allow at hA
        split_ifs at hA <;> omega
  rw [hdet, chiV_one]


local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Classical in
theorem term_eq [DecidableEq k] {k₀ m t j n' c n : ℕ} (hN : Nums k₀ m t j n' c n) (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ)
    (τ : FC n' (c + 1) n c → k) :
    PhiS ψ₀ χ k₀ m t j n' c n (xx1 (xj0 k₀ n' n) τ) *
        ψ₀ (-chArg (n' := n') (c' := c + 1) (n := n) (c := c) (xx1 (xj0 k₀ n' n) τ)) =
      if ((∀ p', p' < k₀ + m - 1 → ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p' p' = 1) ∧
        (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' →
          ent k₀ (c + 1) n' c n (xx1 (xj0 k₀ n' n) τ) p p' ≠ 0 → Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p'))
      then 1 else 0 := by
  unfold PI.OneCosetSharp.PhiS
  dsimp only
  split_ifs with h
  · letI : DecidableEq k := fun a b => Classical.propDecidable (a = b)
    rw [prod_blocks hN χ τ, top_block hN χ τ h, sum_eq_chArg hN τ]
    rw [inv_one, mul_one, mul_one, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · rw [zero_mul]

theorem claim2 : Claim2 := by
  unfold PI.OneCosetSharp.W.Claim2
  intro k _ _ ψ₀ χ k₀ m t j n' c n hN
  classical
  obtain ⟨hk, hc1, hlt, hle, hle2, heq1, heq2⟩ := facts hN
  refine ⟨xj0 k₀ n' n, ?_⟩
  unfold PI.OneCosetSharp.Loc.E1
  simp only [one_pow, one_mul, term_eq hN ψ₀ χ]
  rw [Finset.sum_boole, Nat.cast_ne_zero, Finset.card_ne_zero]
  refine ⟨τ0 k₀ n' c n, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_⟩⟩
  refine ⟨fun p' hp' => ?_, fun p p' hp hp' hne h0 => ?_⟩
  · rw [ent_τ0 hN (by omega) (by omega), if_pos rfl]
  · exact absurd (by rw [ent_τ0 hN hp (by omega), if_neg hne]) h0

end PI.OneCosetSharp.W.C2
end
end
