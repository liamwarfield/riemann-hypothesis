module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CanonicalAnticommutationRelationsConsequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChains
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChains

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundary
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open Formalism.REAL (GlRel)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvComm

section RingId

variable {R : Type} [Ring R]

theorem anti_comm {u v x : R} (hu : u * x + x * u = 0) (hv : v * x + x * v = 0) :
    Commute (u * v) x := by
  have e1 : u * x = -(x * u) := eq_neg_of_add_eq_zero_left hu
  have e2 : v * x = -(x * v) := eq_neg_of_add_eq_zero_left hv
  show u * v * x = x * (u * v)
  rw [mul_assoc, e2, mul_neg, ← mul_assoc, e1, neg_mul, neg_neg, mul_assoc]

theorem cross {n : ℕ} {c d c' d' L L' : Fin n → Fin n → R} (p q : Fin n)
    (hcc : ∀ a b a' b', c a b * c' a' b' + c' a' b' * c a b = 0)
    (hcd : ∀ a b a' b', c a b * d' a' b' + d' a' b' * c a b = 0)
    (hdc : ∀ a b a' b', d a b * c' a' b' + c' a' b' * d a b = 0)
    (hdd : ∀ a b a' b', d a b * d' a' b' + d' a' b' * d a b = 0)
    (hLL : ∀ a b a' b', Commute (L a b) (L' a' b'))
    (hLc : ∀ a b a' b', Commute (L a b) (c' a' b'))
    (hLd : ∀ a b a' b', Commute (L a b) (d' a' b'))
    (hMc : ∀ a b a' b', Commute (L' a b) (c a' b'))
    (hMd : ∀ a b a' b', Commute (L' a b) (d a' b')) :
    Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p))
      ((∑ a, ∑ b, L' a b * c' a b) + ∑ a, ∑ b, ∑ e, d' a e * c' b e * c' a b) := by
  have hXc : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (c' a b) :=
    fun a b => (hLc p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _))
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdc _ _ _ _) (hcc _ _ _ _)))
  have hXd : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (d' a b) :=
    fun a b => (hLd p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _))
      (Commute.sum_left _ _ _ fun r _ => anti_comm (hdd _ _ _ _) (hcd _ _ _ _)))
  have hXL : ∀ a b, Commute (L p q + (∑ r, d p r * c q r - ∑ r, d r q * c r p)) (L' a b) :=
    fun a b => (hLL p q a b).add_left (Commute.sub_left
      (Commute.sum_left _ _ _ fun r _ => ((hMd a b p r).symm).mul_left (hMc a b q r).symm)
      (Commute.sum_left _ _ _ fun r _ => ((hMd a b r q).symm).mul_left (hMc a b r p).symm))
  exact Commute.add_right
    (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      (hXL a b).mul_right (hXc a b))
    (Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ =>
      Commute.sum_right _ _ _ fun e _ => ((hXd a e).mul_right (hXc b e)).mul_right (hXc a b))

variable [Algebra ℂ R]

theorem anti_comb (x0 x1 y0 y1 : R) (σ ρ : ℂ) :
    (x0 + σ • x1) * (y0 + ρ • y1) + (y0 + ρ • y1) * (x0 + σ • x1)
      = (x0 * y0 + y0 * x0) + ρ • (x0 * y1 + y1 * x0) + σ • (x1 * y0 + y0 * x1)
        + (σ * ρ) • (x1 * y1 + y1 * x1) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  module

theorem half_three (z0 z1 y0 y1 x0 x1 : R) :
    ((1 / 2 : ℂ) • (z0 + (1 : ℂ) • z1)) * (y0 + (1 : ℂ) • y1) * (x0 + (1 : ℂ) • x1)
      + ((1 / 2 : ℂ) • (z0 + (-1 : ℂ) • z1)) * (y0 + (-1 : ℂ) • y1) * (x0 + (-1 : ℂ) • x1)
      = z0 * y1 * x1 + z1 * y0 * x1 + (z1 * y1 * x0 + z0 * y0 * x0) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]
  module

theorem half_two (z0 z1 y0 y1 : R) :
    ((1 / 2 : ℂ) • (z0 + (1 : ℂ) • z1)) * (y0 + (1 : ℂ) • y1)
      + ((1 / 2 : ℂ) • (z0 + (-1 : ℂ) • z1)) * (y0 + (-1 : ℂ) • y1)
      = z1 * y1 + z0 * y0 := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_assoc]
  module

end RingId

theorem sum_pos' {n : ℕ} {M : Type*} [AddCommMonoid M] (g : Fin n → Fin n → M) (h : ∀ a b, ¬a < b → g a b = 0) :
    ∑ a, ∑ b, g a b = ∑ i : Pos n, g i.1.1 i.1.2 := by
  rw [← Fintype.sum_prod_type' (f := g),
    ← Finset.sum_filter_of_ne (s := univ) (f := fun y : Fin n × Fin n => g y.1 y.2) (p := fun y => y.1 < y.2)
      (fun y _ hy => by_contra fun t => hy (h _ _ t))]
  exact Finset.sum_subtype _ (by simp) _

theorem sum_lt {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Bool → Fin n → Fin n → M)
    (h : ∀ s a b, ¬a < b → F s a b = 0) :
    ∑ l : Lt n, F l.1 l.2.1.1 l.2.1.2 = ∑ s, ∑ a, ∑ b, F s a b := by
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun s _ => (sum_pos' (F s) (h s)).symm

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev tau (lev : Fin n → ℕ) (a b : Fin n) : Prop := a < b ∧ lev a < lev b

def cT (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : tau lev a b then annL (s, ⟨(a, b), h.1⟩) else 0

def dT (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : tau lev a b then creL (s, ⟨(a, b), h.1⟩) else 0

def cE (lev : Fin n → ℕ) (σ : ℂ) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  cT lev false a b + σ • cT lev true a b

def dE (lev : Fin n → ℕ) (σ : ℂ) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  (1 / 2 : ℂ) • (dT lev false a b + σ • dT lev true a b)

abbrev LT (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) : Module.End ℂ (Cq n V) := liftL n (E a b)

def Dd (lev : Fin n → ℕ) (σ : ℂ) (E : Fin n → Fin n → Module.End ℂ V) : Module.End ℂ (Cq n V) :=
  (∑ a, ∑ b, LT E a b * cE lev σ a b) + ∑ a, ∑ b, ∑ e, dE lev σ a e * cE lev σ b e * cE lev σ a b

def Aa (lev : Fin n → ℕ) (σ : ℂ) (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  LT E p q + (∑ r, dE lev σ p r * cE lev σ q r - ∑ r, dE lev σ r q * cE lev σ r p)

variable {lev : Fin n → ℕ}

theorem cT_pos {s : Bool} {a b : Fin n} (h : tau lev a b) :
    (cT lev s a b : Module.End ℂ (Cq n V)) = annL (s, ⟨(a, b), h.1⟩) := dif_pos h

theorem dT_pos {s : Bool} {a b : Fin n} (h : tau lev a b) :
    (dT lev s a b : Module.End ℂ (Cq n V)) = creL (s, ⟨(a, b), h.1⟩) := dif_pos h

theorem cT_neg {s : Bool} {a b : Fin n} (h : ¬tau lev a b) :
    (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := dif_neg h

theorem dT_neg {s : Bool} {a b : Fin n} (h : ¬tau lev a b) :
    (dT lev s a b : Module.End ℂ (Cq n V)) = 0 := dif_neg h

theorem cT_cT (s t : Bool) (a b a' b' : Fin n) :
    (cT lev s a b * cT lev t a' b' + cT lev t a' b' * cT lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [cT_pos h, cT_pos h']; exact annL_annL _ _
    · rw [cT_neg h']; simp
  · rw [cT_neg h]; simp

theorem dT_dT (s t : Bool) (a b a' b' : Fin n) :
    (dT lev s a b * dT lev t a' b' + dT lev t a' b' * dT lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [dT_pos h, dT_pos h']; exact creL_creL _ _
    · rw [dT_neg h']; simp
  · rw [dT_neg h]; simp

theorem cT_dT (s t : Bool) (a b a' b' : Fin n) :
    (cT lev s a b * dT lev t a' b' + dT lev t a' b' * cT lev s a b : Module.End ℂ (Cq n V))
      = if s = t ∧ a = a' ∧ b = b' ∧ tau lev a b then 1 else 0 := by
  by_cases h : tau lev a b
  · by_cases h' : tau lev a' b'
    · rw [cT_pos h, dT_pos h', annL_creL]
      by_cases e : s = t ∧ a = a' ∧ b = b'
      · obtain ⟨rfl, rfl, rfl⟩ := e
        simp [h]
      · rw [if_neg, if_neg]
        · exact fun t => e ⟨t.1, t.2.1, t.2.2.1⟩
        · intro t
          simp only [Prod.mk.injEq, Subtype.mk.injEq] at t
          exact e t
    · rw [dT_neg h', if_neg]
      · simp
      · rintro ⟨-, rfl, rfl, t⟩
        exact h' t
  · rw [cT_neg h, if_neg (fun t => h t.2.2.2)]; simp

theorem cE_cE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (cE lev σ a b * cE lev ρ a' b' + cE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [cE]
  rw [anti_comb, cT_cT, cT_cT, cT_cT, cT_cT]
  simp

theorem dE_dE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (dE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * dE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [dE, smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [anti_comb, dT_dT, dT_dT, dT_dT, dT_dT]
  simp

theorem cE_dE (σ ρ : ℂ) (a b a' b' : Fin n) :
    (cE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V))
      = ((1 + σ * ρ) / 2) • (if a = a' ∧ b = b' ∧ tau lev a b then 1 else 0) := by
  simp only [cE, dE, smul_mul_assoc, mul_smul_comm, ← smul_add]
  rw [anti_comb, cT_dT, cT_dT, cT_dT, cT_dT]
  simp only [Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, if_false, smul_zero, add_zero,
    ite_false]
  module

theorem LT_cT (E : Fin n → Fin n → Module.End ℂ V) (a b a' b' : Fin n) (s : Bool) :
    Commute (LT E a b) (cT lev s a' b') := by
  by_cases h : tau lev a' b'
  · rw [cT_pos h]; exact liftL_annL _ _
  · rw [cT_neg h]; exact Commute.zero_right _

theorem LT_dT (E : Fin n → Fin n → Module.End ℂ V) (a b a' b' : Fin n) (s : Bool) :
    Commute (LT E a b) (dT lev s a' b') := by
  by_cases h : tau lev a' b'
  · rw [dT_pos h]; exact liftL_creL _ _
  · rw [dT_neg h]; exact Commute.zero_right _

theorem LT_cE (E : Fin n → Fin n → Module.End ℂ V) (σ : ℂ) (a b a' b' : Fin n) :
    Commute (LT E a b) (cE lev σ a' b') :=
  (LT_cT E a b a' b' false).add_right ((LT_cT E a b a' b' true).smul_right σ)

theorem LT_dE (E : Fin n → Fin n → Module.End ℂ V) (σ : ℂ) (a b a' b' : Fin n) :
    Commute (LT E a b) (dE lev σ a' b') :=
  ((LT_dT E a b a' b' false).add_right ((LT_dT E a b a' b' true).smul_right σ)).smul_right _

theorem glRel_LT {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (p q a b : Fin n) :
    LT E p q * LT E a b - LT E a b * LT E p q =
      (if q = a then LT E p b else 0) - (if b = p then LT E a q else 0) := by
  refine LinearMap.ext fun y => funext fun A => ?_
  have e := LinearMap.congr_fun (hE p q a b) (y A)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, liftL_apply]
  rw [e]
  split_ifs <;> rfl

theorem LT_LT {E E' : Fin n → Fin n → Module.End ℂ V} (h : ∀ a b c d, E a b * E' c d = E' c d * E a b)
    (a b c d : Fin n) : Commute (LT E a b) (LT E' c d) := by
  refine LinearMap.ext fun y => funext fun A => ?_
  exact LinearMap.congr_fun (h a b c d) (y A)

theorem tau_left (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (b : Fin n) :
    tau lev p b ↔ tau lev q b :=
  ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩,
    fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩

theorem tau_right (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (a : Fin n) :
    tau lev a p ↔ tau lev a q :=
  ⟨fun h => ⟨hm.reflect_lt (by rw [← hpq]; exact h.2), by rw [← hpq]; exact h.2⟩,
    fun h => ⟨hm.reflect_lt (by rw [hpq]; exact h.2), by rw [hpq]; exact h.2⟩⟩

theorem comm_same (hm : Monotone lev) {σ : ℂ} (hσ : σ * σ = 1) {E : Fin n → Fin n → Module.End ℂ V}
    (hE : GlRel E) {p q : Fin n} (hpq : lev p = lev q) :
    Commute (Aa lev σ E p q) (Dd lev σ E) :=
  GlobalTheory.CompanionTheory.CliffordCoeff.commute_shifted_dirac n (Module.End ℂ (Cq n V)) (tau lev)
    (cE lev σ) (dE lev σ) (LT E) p q
    (fun a b a' b' => cE_cE σ σ a b a' b') (fun a b a' b' => dE_dE σ σ a b a' b')
    (fun a b a' b' => by
      rw [cE_dE, hσ]
      have : ((1 + 1) / 2 : ℂ) = 1 := by norm_num
      rw [this, one_smul])
    (fun a b h => by simp only [cE, cT_neg h, smul_zero, add_zero])
    (fun a b h => by simp only [dE, dT_neg h, smul_zero, add_zero])
    (tau_left hm hpq) (tau_right hm hpq)
    (fun a b a' b' => LT_cE E σ a b a' b') (fun a b a' b' => LT_dE E σ a b a' b')
    (fun a b => glRel_LT hE p q a b)

theorem comm_cross {σ ρ : ℂ} (hσ : σ * ρ = -1) {E E' : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ a b c d, E a b * E' c d = E' c d * E a b) (p q : Fin n) :
    Commute (Aa lev σ E p q) (Dd lev ρ E') := by
  have hz : ∀ {σ ρ : ℂ}, σ * ρ = -1 → ∀ a b a' b',
      (cE lev σ a b * dE lev ρ a' b' + dE lev ρ a' b' * cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
    intro σ ρ hs a b a' b'
    rw [cE_dE, hs]
    simp
  have hz' : σ * ρ = -1 → ρ * σ = -1 := fun e => by rw [mul_comm]; exact e
  exact cross p q (fun a b a' b' => cE_cE σ ρ a b a' b') (hz hσ)
    (fun a b a' b' => by rw [add_comm]; exact hz (hz' hσ) a' b' a b)
    (fun a b a' b' => dE_dE σ ρ a b a' b') (LT_LT h)
    (fun a b a' b' => LT_cE E ρ a b a' b') (fun a b a' b' => LT_dE E ρ a b a' b')
    (fun a b a' b' => LT_cE E' σ a b a' b') (fun a b a' b' => LT_dE E' σ a b a' b')

theorem lift_k (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (liftL n (kA E1 E2 a b) : Module.End ℂ (Cq n V)) = LT E1 a b + LT E2 a b :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem lift_p (E1 E2 : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    (liftL n (pA E1 E2 a b) : Module.End ℂ (Cq n V)) = LT E1 a b - LT E2 a b :=
  LinearMap.ext fun _ => funext fun _ => rfl

theorem cE_zero (σ : ℂ) {a b : Fin n} (h : ¬a < b) : (cE lev σ a b : Module.End ℂ (Cq n V)) = 0 := by
  simp only [cE, cT_neg (fun u : tau lev a b => h u.1), smul_zero, add_zero]

theorem bd_one (E1 E2 : Fin n → Fin n → Module.End ℂ V) {dec : ∀ l : Lt n, Decidable (inUU lev l)} :
    (∑ l : Lt n, @ite _ (inUU lev l) (dec l) ((liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l) 0)
      = (∑ a, ∑ b, LT E1 a b * cE lev 1 a b) + ∑ a, ∑ b, LT E2 a b * cE lev (-1) a b := by
  rw [sum_pos' (fun a b => LT E1 a b * cE lev 1 a b) (fun a b h => by rw [cE_zero _ h, mul_zero]),
    sum_pos' (fun a b => LT E2 a b * cE lev (-1) a b) (fun a b h => by rw [cE_zero _ h, mul_zero]),
    ← sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have x1 : xL E1 E2 (true, ⟨(a, b), hab⟩) = pA E1 E2 a b := by simp [xL]
  have x0 : xL E1 E2 (false, ⟨(a, b), hab⟩) = kA E1 E2 a b := by simp [xL]
  by_cases hi : lev a < lev b
  · have ht : tau lev a b := ⟨hab, hi⟩
    have e1 : inUU lev ((true, ⟨(a, b), hab⟩) : Lt n) := hi
    have e0 : inUU lev ((false, ⟨(a, b), hab⟩) : Lt n) := hi
    rw [if_pos e1, if_pos e0, x1, x0, lift_p, lift_k]
    simp only [cE, cT_pos ht, one_smul, neg_smul]
    noncomm_ring
  · have e1 : ¬inUU lev ((true, ⟨(a, b), hab⟩) : Lt n) := hi
    have e0 : ¬inUU lev ((false, ⟨(a, b), hab⟩) : Lt n) := hi
    have ht : ¬tau lev a b := fun u => hi u.2
    rw [if_neg e1, if_neg e0]
    simp only [cE, cT_neg ht, smul_zero, add_zero, mul_zero]

theorem tri_sum (l m : Lt n)
    {dec : ∀ k : Lt n, Decidable (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)} :
    (∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec k) (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = if l.2.1.2 = m.2.1.1 then
          dT lev (xor l.1 m.1) l.2.1.1 m.2.1.2 * cT lev m.1 m.2.1.1 m.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2
        else 0 := by
  obtain ⟨s, ⟨a, b⟩, hab⟩ := l
  obtain ⟨t, ⟨b', e⟩, hbe⟩ := m
  dsimp only at *
  by_cases h : b = b'
  swap
  · rw [if_neg h]
    exact sum_eq_zero fun k _ => if_neg (fun u => h u.2.2.1)
  subst h
  rw [if_pos rfl]
  by_cases hl : lev a < lev b
  swap
  · rw [cT_neg (lev := lev) (a := a) (b := b) (fun u => hl u.2), mul_zero]
    exact sum_eq_zero fun k _ => if_neg (fun u => hl u.1)
  by_cases hr : lev b < lev e
  swap
  · rw [cT_neg (lev := lev) (a := b) (b := e) (fun u => hr u.2), mul_zero, zero_mul]
    exact sum_eq_zero fun k _ => if_neg (fun u => hr u.2.1)
  have hlt : a < e := hab.trans hbe
  have hlv : lev a < lev e := hl.trans hr
  rw [dT_pos (lev := lev) ⟨hlt, hlv⟩, cT_pos (lev := lev) (a := b) (b := e) ⟨hbe, hr⟩,
    cT_pos (lev := lev) (a := a) (b := b) ⟨hab, hl⟩, sum_eq_single (xor s t, ⟨(a, e), hlt⟩)]
  · rw [if_pos ⟨hl, hr, rfl, rfl, rfl, rfl⟩]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨-, -, -, e1, e2, e3⟩
    exact hk (Prod.ext e1 (Subtype.ext (Prod.ext e2 e3)))
  · simp

theorem bd_two
    {dec : ∀ l m k : Lt n, Decidable (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧
      k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)} :
    (∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧
      k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec l m k)
        (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = (∑ a, ∑ b, ∑ e, dE lev 1 a e * cE lev 1 b e * cE lev 1 a b)
        + ∑ a, ∑ b, ∑ e, dE lev (-1) a e * cE lev (-1) b e * cE lev (-1) a b := by
  have h1 : ∀ l : Lt n, (∑ m : Lt n, ∑ k : Lt n, @ite _ (inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧
      k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2) (dec l m k)
        (creL k * annL m * annL l : Module.End ℂ (Cq n V)) 0)
      = ∑ t, ∑ e, dT lev (xor l.1 t) l.2.1.1 e * cT lev t l.2.1.2 e * cT lev l.1 l.2.1.1 l.2.1.2 := by
    intro l
    rw [sum_congr rfl fun m _ => tri_sum l m]
    refine (sum_lt (fun t b' e => if l.2.1.2 = b' then
      dT lev (xor l.1 t) l.2.1.1 e * cT lev t b' e * cT lev l.1 l.2.1.1 l.2.1.2 else 0) ?_).trans ?_
    · intro t b' e h
      have hc : (cT lev t b' e : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun t _ => ?_
      rw [sum_eq_single l.2.1.2 (fun b _ hb => sum_eq_zero fun e _ => if_neg (Ne.symm hb)) (by simp)]
      exact sum_congr rfl fun e _ => if_pos rfl
  rw [sum_congr rfl fun l _ => h1 l]
  refine (sum_lt (fun s a b => ∑ t, ∑ e, dT lev (xor s t) a e * cT lev t b e * cT lev s a b) ?_).trans ?_
  · intro s a b h
    have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
    simp [hc]
  · simp only [Fintype.sum_bool, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun e _ => ?_
    simp only [dE, cE]
    rw [half_three]
    rfl

theorem bdL_eq (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    bdL (inUU lev) E1 E2 = Dd lev 1 E1 + Dd lev (-1) E2 := by
  unfold bdL
  refine (congrArg₂ (· + ·)
    (bd_one (lev := lev) (dec := fun _ => Classical.propDecidable _) E1 E2)
    (bd_two (lev := lev) (dec := fun _ _ _ =>
      @instDecidableAnd _ _ (Classical.propDecidable _)
        (@instDecidableAnd _ _ (Classical.propDecidable _) inferInstance)))).trans ?_
  simp only [Dd]
  abel

theorem adLL_term (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (l : Lt n) :
    (∑ k : Lt n, if inUU lev l then adCL false p q l k • (creL k * annL l : Module.End ℂ (Cq n V)) else 0)
      = (if q = l.2.1.1 then dT lev l.1 p l.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2 else 0)
        - (if l.2.1.2 = p then dT lev l.1 l.2.1.1 q * cT lev l.1 l.2.1.1 l.2.1.2 else 0) := by
  obtain ⟨s, ⟨a, b⟩, hab⟩ := l
  by_cases hl : lev a < lev b
  swap
  · have hS : ¬inUU lev ((s, ⟨(a, b), hab⟩) : Lt n) := hl
    have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => hl u.2)
    rw [sum_eq_zero fun k _ => if_neg hS]
    dsimp only
    rw [hc]
    simp
  have hS : inUU lev ((s, ⟨(a, b), hab⟩) : Lt n) := hl
  rw [sum_congr rfl fun k _ => if_pos hS]
  simp only [adCL, sub_smul, sum_sub_distrib]
  rw [cT_pos (lev := lev) (s := s) (a := a) (b := b) ⟨hab, hl⟩]
  congr 1
  · by_cases h : q = a
    · have hlv : lev p < lev b := by rw [hpq, h]; exact hl
      have hlt : p < b := hm.reflect_lt hlv
      rw [if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(p, b), hlt⟩)]
      · rw [if_pos ⟨h, by simp, rfl⟩, one_smul]
      · intro k _ hk
        rw [if_neg, zero_smul]
        rintro ⟨-, e1, e2⟩
        exact hk (Prod.ext (by simpa using e1) (Subtype.ext e2))
      · simp
    · rw [if_neg h]
      exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]
  · by_cases h : b = p
    · have hlv : lev a < lev q := by rw [← hpq, ← h]; exact hl
      have hlt : a < q := hm.reflect_lt hlv
      rw [if_pos h, dT_pos (lev := lev) ⟨hlt, hlv⟩, sum_eq_single (s, ⟨(a, q), hlt⟩)]
      · rw [if_pos ⟨h, by simp, rfl⟩, one_smul]
      · intro k _ hk
        rw [if_neg, zero_smul]
        rintro ⟨-, e1, e2⟩
        exact hk (Prod.ext (by simpa using e1) (Subtype.ext e2))
      · simp
    · rw [if_neg h]
      exact sum_eq_zero fun k _ => by rw [if_neg (fun t => h t.1), zero_smul]

theorem adLL_eq (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) :
    (adLL lev false p q : Module.End ℂ (Cq n V))
      = ∑ s, (∑ r, dT lev s p r * cT lev s q r - ∑ r, dT lev s r q * cT lev s r p) := by
  have e1 : (∑ l : Lt n, if q = l.2.1.1 then
      (dT lev l.1 p l.2.1.2 * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0)
      = ∑ s, ∑ r, dT lev s p r * cT lev s q r := by
    refine (sum_lt (fun s a b => if q = a then dT lev s p b * cT lev s a b else 0) ?_).trans ?_
    · intro s a b h
      have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun s _ => ?_
      rw [sum_eq_single q (fun a _ ha => sum_eq_zero fun b _ => if_neg (Ne.symm ha)) (by simp)]
      exact sum_congr rfl fun r _ => if_pos rfl
  have e2 : (∑ l : Lt n, if l.2.1.2 = p then
      (dT lev l.1 l.2.1.1 q * cT lev l.1 l.2.1.1 l.2.1.2 : Module.End ℂ (Cq n V)) else 0)
      = ∑ s, ∑ r, dT lev s r q * cT lev s r p := by
    refine (sum_lt (fun s a b => if b = p then dT lev s a q * cT lev s a b else 0) ?_).trans ?_
    · intro s a b h
      have hc : (cT lev s a b : Module.End ℂ (Cq n V)) = 0 := cT_neg (fun u => h u.1)
      simp [hc]
    · refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => ?_
      rw [sum_eq_single p (fun b _ hb => if_neg hb) (by simp)]
      exact if_pos rfl
  unfold adLL
  rw [sum_congr rfl fun l _ => adLL_term hm hpq l, sum_sub_distrib, e1, e2, sum_sub_distrib]

theorem Lv_eq (hm : Monotone lev) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n}
    (hpq : lev p = lev q) :
    Lv lev E1 E2 p q = Aa lev 1 E1 p q + Aa lev (-1) E2 p q := by
  have s1 : (∑ r, dE lev 1 p r * cE lev 1 q r + ∑ r, dE lev (-1) p r * cE lev (-1) q r
      : Module.End ℂ (Cq n V))
      = ∑ r, dT lev true p r * cT lev true q r + ∑ r, dT lev false p r * cT lev false q r := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    simp only [dE, cE]
    exact half_two _ _ _ _
  have s2 : (∑ r, dE lev 1 r q * cE lev 1 r p + ∑ r, dE lev (-1) r q * cE lev (-1) r p
      : Module.End ℂ (Cq n V))
      = ∑ r, dT lev true r q * cT lev true r p + ∑ r, dT lev false r q * cT lev false r p := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    simp only [dE, cE]
    exact half_two _ _ _ _
  unfold Lv Aa
  rw [adLL_eq hm hpq, lift_k, Fintype.sum_bool]
  have e : ∀ L1 L2 X1 X2 Y1 Y2 : Module.End ℂ (Cq n V),
      L1 + (X1 - Y1) + (L2 + (X2 - Y2)) = L1 + L2 + ((X1 + X2) - (Y1 + Y2)) := by
    intros; abel
  rw [e, s1, s2]
  abel

theorem lv_bd_comm : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → IsPairA E1 E2 → ∀ p q : Fin n, lev p = lev q →
      (Lv lev E1 E2 p q * bdL (inUU lev) E1 E2 : Module.End ℂ (Cq n V)) = bdL (inUU lev) E1 E2 * Lv lev E1 E2 p q := by
  intro n lev V _ _ E1 E2 hm hE p q hpq
  obtain ⟨h1, h2, h12⟩ := hE
  have hs : ((1 : ℂ) * 1 = 1) ∧ ((-1 : ℂ) * -1 = 1) ∧ ((1 : ℂ) * -1 = -1) ∧ ((-1 : ℂ) * 1 = -1) := by
    norm_num
  rw [Lv_eq hm E1 E2 hpq, bdL_eq]
  exact (Commute.add_left
    (Commute.add_right (comm_same hm hs.1 h1 hpq) (comm_cross hs.2.2.1 h12 p q))
    (Commute.add_right (comm_cross hs.2.2.2 (fun a b c d => (h12 c d a b).symm) p q)
      (comm_same hm hs.2.1 h2 hpq))).eq

end GlobalTheory.CompanionTheory.LvComm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundaryStatement
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_commute_unipotent_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → IsPairA E1 E2 → ∀ p q : Fin n, lev p = lev q →
      (Lv lev E1 E2 p q * bdL (inUU lev) E1 E2 : Module.End ℂ (Cq n V)) = bdL (inUU lev) E1 E2 * Lv lev E1 E2 p q := by
  first | exact @GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | exact GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LvComm.lv_bd_comm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChains
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChains
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppL (inUU lev) x ∧ DegL d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsInL lev d S) := by
  let L : chainsInL lev d S →ₗ[ℂ] (Finset (Lt n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsInL lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem Lv_apply (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cq n V)
    (A : Finset (Lt n)) :
    Lv lev E1 E2 p q x A = kA E1 E2 p q (x A) +
      ∑ l : Lt n, ∑ k : Lt n, if inUU lev l then adCL false p q l k • creL k (annL l x) A else 0 := by
  simp only [Lv, adLL, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, liftL_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Module.End.mul_apply]

theorem creL_annL_mem {S : Submodule ℂ V} {x : Cq n V} (hx : ∀ A, x A ∈ S) (l k : Lt n) (A : Finset (Lt n)) :
    creL k (annL l x) A ∈ S := by
  rw [creL_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [annL_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inUU_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {l k : Lt n}
    (h : adCL false p q l k ≠ 0) (hl : inUU lev l) : inUU lev k := by
  by_cases c1 : q = l.2.1.1 ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (p, l.2.1.2)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c1.2.2]
    show lev p < lev l.2.1.2
    rw [hpq, c1.1]
    exact hl
  by_cases c2 : l.2.1.2 = p ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (l.2.1.1, q)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c2.2.2]
    show lev l.2.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hl
  · exact absurd (by rw [adCL, if_neg c1, if_neg c2, sub_zero]) h

theorem Lv_ne {lev : Fin n → ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cq n V}
    {A : Finset (Lt n)} (h : Lv lev E1 E2 p q x A ≠ 0) :
    kA E1 E2 p q (x A) ≠ 0 ∨ ∃ l k, inUU lev l ∧ adCL false p q l k ≠ 0 ∧ creL k (annL l x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [Lv_apply, hc.1, zero_add]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hl
  · by_cases h0 : adCL false p q l k = 0
    · rw [h0, zero_smul]
    · rw [hc.2 l k hl h0, smul_zero]
  · rfl

theorem term_suppL {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cq n V}
    (hx : SuppL (inUU lev) x) (hd : DegL d x) {A : Finset (Lt n)} {l k : Lt n} (h0 : adCL false p q l k ≠ 0)
    (h : creL k (annL l x) A ≠ 0) : (∀ j ∈ A, inUU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := creL_ne h
  obtain ⟨h2, h3⟩ := annL_ne h1
  have hs := hx _ h3
  have hi : inUU lev l := hs l (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inUU_of_adCL hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem Lv_mem_chainsInL {lev : Fin n → ℕ} {d : ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) {p q : Fin n} (hpq : lev p = lev q)
    {x : Cq n V} (hx : x ∈ chainsInL lev d S) : Lv lev E1 E2 p q x ∈ chainsInL lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hk : ∀ A, kA E1 E2 p q (x A) ≠ 0 → x A ≠ 0 := fun A h h0 => h (by rw [h0, map_zero])
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx1 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').1
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx2 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').2
  · rw [Lv_apply]
    refine S.add_mem (hS p q _ (hx3 A)) (S.sum_mem fun l _ => S.sum_mem fun k _ => ?_)
    split_ifs
    · exact S.smul_mem _ (creL_annL_mem hx3 l k A)
    · exact S.zero_mem

theorem exists_stable : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  intro n lev V _ _ E1 E2 d y hF hy hd
  choose Sf hfd hmem hSt using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  have : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S := fun a b v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b z hz) : S ≤ S.comap (kA E1 E2 a b)) hv
  refine ⟨chainsInL lev d S, finiteDimensional_chainsInL lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hpq x hx => Lv_mem_chainsInL hSs hpq hx⟩

end GlobalTheory.CompanionTheory.LvStableChains
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChainsStatement
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_levi_stable_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  first | exact @GlobalTheory.CompanionTheory.LvStableChains.exists_stable | exact GlobalTheory.CompanionTheory.LvStableChains.exists_stable | (intros; apply GlobalTheory.CompanionTheory.LvStableChains.exists_stable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestriction
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem bdL_inRR_eq {n : ℕ} {lev : Fin n → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) {x : Cq n V} (hx : SuppL (inUU lev) x) :
    bdL (inRR lev) E1 E2 x = bdL (inUU lev) E1 E2 x := by
  classical
  have h1 : ∀ l : Lt n, ¬inUU lev l → annL l x = 0 := fun l hl => by
    funext A
    by_contra h
    exact hl (hx _ (annL_ne h).2 l (mem_insert_self _ _))
  have h2 : ∀ l m : Lt n, ¬inUU lev m → annL m (annL l x) = 0 := fun l m hm => by
    funext A
    by_contra h
    obtain ⟨-, h3⟩ := annL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    exact hm (hx _ h4 m (mem_insert_of_mem (mem_insert_self _ _)))
  simp only [bdL, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · refine sum_congr rfl fun l _ => ?_
    by_cases hl : inUU lev l
    · rw [if_pos (Or.inr hl : inRR lev l), if_pos hl]
    · rw [if_neg hl]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl
  · refine sum_congr rfl fun l _ => sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_
    by_cases hl : inUU lev l
    · by_cases hm : inUU lev m
      · by_cases hc : l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2
        · rw [if_pos ⟨Or.inr hl, Or.inr hm, hc⟩, if_pos ⟨hl, hm, hc⟩]
        · rw [if_neg fun t => hc t.2.2, if_neg fun t => hc t.2.2]
      · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
            k.2.1.2 = m.2.1.2) := fun t => hm t.2.1
        rw [if_neg hn]
        split_ifs
        · simp [Module.End.mul_apply, h2 l m hm]
        · rfl
    · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
          k.2.1.2 = m.2.1.2) := fun t => hl t.1
      rw [if_neg hn]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem creL_single (f : Lt n) (S : Finset (Lt n)) (w : V) (h : f ∉ S) :
    (creL f : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) =
      sgL f (insert f S) • (Pi.single (insert f S) w : Cq n V) := by
  funext A
  rw [creL_apply, Pi.smul_apply]
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (mem_insert_self f S), erase_insert h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hA, smul_zero]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun e => hA (by rw [← e, insert_erase hf])
      rw [Pi.single_eq_of_ne hne, smul_zero]
    · rfl

theorem prod_creL_single (l : List (Lt n)) (S : Finset (Lt n)) (w : V) (hl : l.Nodup) (hS : ∀ i ∈ l, i ∉ S) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((l.map creL).prod : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) = c • (Pi.single (S ∪ l.toFinset) w : Cq n V) := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons f t ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨c, hc, e⟩ := ih hl.2 fun i hi => hS i (List.mem_cons_of_mem f hi)
    have hf : f ∉ S ∪ t.toFinset := by
      rw [mem_union, not_or]
      exact ⟨hS f List.mem_cons_self, fun h => hl.1 (List.mem_toFinset.1 h)⟩
    have hU : S ∪ (f :: t).toFinset = insert f (S ∪ t.toFinset) := by
      rw [List.toFinset_cons, union_insert]
    refine ⟨c * sgL f (insert f (S ∪ t.toFinset)), mul_ne_zero hc (sgL_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, map_smul, creL_single f _ w hf, hU, smul_smul]

theorem suppL_degL_prod (P : Lt n → Prop) (l : List (Lt n)) (x : Cq n V) (j : ℕ) (hl : ∀ i ∈ l, P i)
    (hx : SuppL P x) (hd : DegL j x) :
    SuppL P (((l.map creL).prod : Module.End ℂ (Cq n V)) x) ∧
      DegL (j + l.length) (((l.map creL).prod : Module.End ℂ (Cq n V)) x) := by
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := creL_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := creL_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.LvChain

namespace GlobalTheory.CompanionTheory.LvChain


open GlobalTheory.CompanionTheory.FarReg in
theorem highest_preimage {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    (T : Submodule ℂ (Cq n V)) (a b : ι → Module.End ℂ (Cq n V)) (D : Module.End ℂ (Cq n V)) (y : Cq n V)
    (hT : FiniteDimensional ℂ T) (hadj : ∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) : ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  let e : Cq n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Lt n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Lt n) → V)).symm
  let c : Module.End ℂ (Cq n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Lt n) => V)) := fun f =>
    (e : Cq n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cq n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

theorem injUU_of_injRL : InjRL → InjUU := by
  intro hR n lam hlam lev hlev V _ _ E1 E2 hA u y hu hy hd hb
  have hm : Monotone lev := hlev.1
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hup : ∀ a b : Fin n, a < b → kA E1 E2 a b u = 0 := fun a b hab => hu.2 a b hab rfl
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := GlobalTheory.T.exists_finite_levi_stable_chains n lev V E1 E2 _ y hA.locFin hy hd
  have hC := GlobalTheory.T.levi_commute_unipotent_boundary n lev V E1 E2 hm hP
  have hone := GlobalTheory.T.levi_raising_kills_top_chain n lev V E1 E2 u hup
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := highest_preimage
    (ι := {pq : Fin n × Fin n // pq.1 < pq.2 ∧ lev pq.1 = lev pq.2}) T
    (fun i => Lv lev E1 E2 i.1.1 i.1.2) (fun i => Lv lev E1 E2 i.1.2 i.1.1) (bdL (inUU lev) E1 E2) y hTf
    (fun i x z => GlobalTheory.T.levi_adjoint_on_chains n lev V E1 E2 hA.unitK _ _ i.2.2 x z)
    (fun i t ht => hTs _ _ i.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.symm t ht)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2) t).symm ▸ rfl)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2.symm) t).symm ▸ rfl) hyT
    (fun i => by rw [hb]; exact hone _ _ i.2.1 i.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order n (fun _ => true) lev hm
  have hlc : ∀ e ∈ l, lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨-, h2⟩ := (hmem e).1 he
    refine le_antisymm (hm e.2.le) ?_
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, not_le.1 h3⟩)
  have hbd := GlobalTheory.T.boundary_prod_creation_levi_chains n lev V E1 E2 l y' hlc hcl hy's
    (fun e he => hy'0 ⟨e.1, e.2, hlc e he⟩)
  rw [bdL_inRR_eq E1 E2 hy's, hy'b, hb] at hbd
  set l' : List (Lt n) := l.map fun i => (false, i) with hl'
  have hmap : (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))) = l'.map creL := by
    rw [hl', List.map_map]; rfl
  have hnd' : l'.Nodup := hnd.map fun a b h => (Prod.ext_iff.1 h).2
  have hout : ∀ i ∈ l', i ∉ omU lev := by
    intro i hi h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    have := (Finset.mem_filter.1 h).2.2
    have h2 := hlc e he
    simp only at this
    omega
  obtain ⟨c, hc0, hcw⟩ := prod_creL_single (V := V) l' (omU lev) u hnd' hout
  have hun : omU lev ∪ l'.toFinset = omN n := by
    ext ⟨t, i⟩
    simp only [Finset.mem_union, List.mem_toFinset, hl', List.mem_map, omU, omN, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | ⟨e, -, h⟩)
      · exact h.1
      · exact (Prod.ext_iff.1 h).1.symm
    · rintro rfl
      by_cases h2 : lev i.1.1 < lev i.1.2
      · exact Or.inl ⟨rfl, h2⟩
      · refine Or.inr ⟨i, (hmem i).2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, fun h => h2 (Finset.mem_filter.1 h).2.2⟩, rfl⟩
  have hcard : (omN n).card = (omU lev).card + l'.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd']
    exact Finset.disjoint_left.2 fun i h1 h2 => hout i (List.mem_toFinset.1 h2) h1
  obtain ⟨hs1, hs2⟩ := suppL_degL_prod (V := V) (inRR lev) l' y' _
    (fun i hi => by obtain ⟨e, -, rfl⟩ := List.mem_map.1 hi; exact Or.inl rfl)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cq n V := ((l'.map creL).prod : Module.End ℂ (Cq n V)) y' with hCd
  have hsm : ∀ (s : ℂ) (x : Cq n V) (A : Finset (Lt n)), (s • x) A ≠ 0 → x A ≠ 0 :=
    fun s x A h h0 => h (by simp [h0])
  refine hR n lam hlam lev hlev V E1 E2 hA u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu ?_ ?_ ?_
  · exact fun A hA' => hs1 A (hsm _ C A hA')
  · intro A hA'
    have h3 := hs2 A (hsm _ C A hA')
    rw [h3, hcard]
    have : l'.length = l.length := by rw [hl', List.length_map]
    omega
  · rw [map_smul, hCd]
    rw [hmap] at hbd
    rw [hbd, hcw, hun, smul_smul, smul_smul]
    have hlen : l'.length = l.length := by rw [hl', List.length_map]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.LvChain
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveUnipotentOfRestrictionStatement
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_unipotent_of_restriction : PositivityTheory.RgBcC.RealD.InjRL → PositivityTheory.RgBcC.RealD.InjUU := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | exact GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL | (intros; apply GlobalTheory.CompanionTheory.LvChain.injUU_of_injRL <;> assumption)
end
