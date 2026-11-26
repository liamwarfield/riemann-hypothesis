module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def seqN (N : ℕ) (j : Ω →+* Qbar l) (φ : HahnSeries ℚ Ω) : ℕ → Qbar l := fun s => j (φ.coeff ((s : ℚ) / N))

def FinSupp (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, (∀ s ∈ S, f s = 0) → lam f = 0

def IsLamOf (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)


def IsLamOfL (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ), c ≤ n → ∀ (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN N j φ)) (per n * pr b 1)


theorem norm_l_pow (n : ℕ) : ‖((l : ℕ) : Qbar l) ^ n‖ = ((l : ℝ)⁻¹) ^ n := by
  have : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [norm_pow, this, norm_algebraMap', Padic.norm_p]

theorem cg_mono {m n : ℕ} (h : m ≤ n) {x y : Qbar l} (hxy : Cg n x y) : Cg m x y := by
  unfold Cg at *
  refine hxy.trans ?_
  rw [norm_l_pow, norm_l_pow]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h1) h

theorem exists_le_l_pow (l : ℕ) [Fact l.Prime] (t : ℝ) : ∃ k : ℕ, t ≤ (l : ℝ) ^ k := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt t h1
  exact ⟨k, hk.le⟩

theorem l_pow_mul_norm {k m : ℕ} (h : k ≤ m) :
    (l : ℝ) ^ k * ‖((l : ℕ) : Qbar l) ^ m‖ = ‖((l : ℕ) : Qbar l) ^ (m - k)‖ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h0 : (l : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [norm_l_pow, norm_l_pow, Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

theorem cg_sub_iff {c n : ℕ} (h : c ≤ n) (x y : Qbar l) :
    Cg (n - c) x y ↔ ‖x - y‖ ≤ (l : ℝ) ^ c * ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [l_pow_mul_norm h]; rfl

theorem cg_mul_left {k m : ℕ} (h : k ≤ m) {a x y : Qbar l} (ha : ‖a‖ ≤ (l : ℝ) ^ k) (hxy : Cg m x y) :
    Cg (m - k) (a * x) (a * y) := by
  rw [cg_sub_iff h, ← mul_sub, norm_mul]
  exact mul_le_mul ha hxy (norm_nonneg _) (by positivity)

theorem seqN_single {N : ℕ} (hN : N ≠ 0) (j : Ω →+* Qbar l) (s : ℕ) (a : Ω) :
    seqN N j (HahnSeries.single ((s : ℚ) / N) a) = Pi.single s (j a) := by
  funext t
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  by_cases h : t = s
  · subst h; simp [seqN]
  · have : (t : ℚ) / N ≠ (s : ℚ) / N := fun e => h (by exact_mod_cast (div_left_inj' hN').1 e)
    simp [seqN, HahnSeries.coeff_single_of_ne this, h]

theorem finSupp_proj (s : ℕ) : FinSupp (LinearMap.proj (R := Qbar l) (φ := fun _ : ℕ => Qbar l) s) :=
  ⟨{s}, fun f hf => hf s (Finset.mem_singleton_self s)⟩

theorem FinSupp.smul {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (a : Qbar l) : FinSupp (a • lam) := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun f hf => by simp [hS f hf]⟩

theorem FinSupp.add {lam lam' : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) (h' : FinSupp lam') :
    FinSupp (lam + lam') := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, hT⟩ := h'
  exact ⟨S ∪ T, fun f hf => by
    simp [hS f fun s hs => hf s (Finset.mem_union_left _ hs), hT f fun s hs => hf s (Finset.mem_union_right _ hs)]⟩

theorem FinSupp.exists_sum {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ S : Finset ℕ, ∀ f : ℕ → Qbar l, lam f = ∑ s ∈ S, lam (Pi.single s 1) * f s := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun f => ?_⟩
  have h0 := hS (f - ∑ s ∈ S, f s • (Pi.single s 1 : ℕ → Qbar l)) (fun t ht => by
    simp [Finset.sum_apply, Pi.single_apply, ht])
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum, sub_eq_zero] at h0
  rw [h0]
  exact Finset.sum_congr rfl fun s _ => by rw [map_smul, smul_eq_mul, mul_comm]

theorem FinSupp.exists_loss {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l} (h : FinSupp lam) :
    ∃ c : ℕ, ∀ n, c ≤ n → ∀ f g : ℕ → Qbar l, (∀ s, Cg n (f s) (g s)) → Cg (n - c) (lam f) (lam g) := by
  obtain ⟨S, hS⟩ := h.exists_sum
  obtain ⟨c, hc⟩ := exists_le_l_pow l (∑ s ∈ S, ‖lam (Pi.single s 1)‖)
  refine ⟨c, fun n hn f g hfg => ?_⟩
  rw [cg_sub_iff hn, hS f, hS g, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hfg s) (norm_nonneg _)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {j : Ω →+* Qbar l} {pr : X.Fn l → Fin 2 → Qbar l}
  {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

end Induced

end GlobalTheory.KummerEisensteinGalois

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTPresNuOfPolys (A : ValuationSubring Ω) (c : Coef l) (m c₀ : ℕ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (ζ : Ω)
    {ι : Type} [Fintype ι] (P : ι → Polynomial Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ m) ∧ (∀ i, ∀ x ∈ (P i).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ (∀ i, o i ∈ c.O) ∧
    (∀ i, (P i).eval ζ ≠ 0) ∧ GlobalTheory.Col.KumPres A (m - c₀) m (ζ ^ l ^ c₀) (Z m) (fun i => (P i).eval ζ) o

def HTLawCsOfCoef (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (j : Ω →+* Qbar l)
    (m₀ c₀ : ℕ) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l) : Prop :=
  ∃ ζ : ℕ → Ω, (∀ m, IsPrimitiveRoot (ζ m) (l ^ m) ∧ ζ (m + 1) ^ l = ζ m) ∧
    ∀ m, m₀ ≤ m → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
      HTPresNuOfPolys A c m c₀ Z (ζ m) P o ∧ ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive →
        Cg (m - c₀) (∑ b : (ZMod (l ^ m))ˣ, ψ b * htv j (ζ m) P o (b : ZMod (l ^ m)).val) (Rhs m ψ (j (ζ m)))

def Pin7 (e : ℕ) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (ν : G ℚ Ω → (Qbar l)ˣ)
    (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (a a' κ : Qbar l) (v : ℕ → Qbar l) (j : Ω →+* Qbar l) (Rhs : ∀ m : ℕ, DirichletCharacter (Qbar l) (l ^ m) → Qbar l → Qbar l)
    (L : PowerSeries (Qbar l)) (φ : DirichletCharacter (Qbar l) l) (m₀ c₀ n₀ : ℕ),
    (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧ (∃ σ ∈ Dec (F := ℚ) A, IsFrob A l σ ∧ (ν σ : Qbar l) = a) ∧
    ‖a‖ = 1 ∧ ‖a'‖ = 1 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧ κ ≠ 0 ∧ (∀ x ∈ A, ‖j x‖ ≤ 1) ∧
    (∀ n, L.coeff n ∈ c.O) ∧ HTLawCsOfCoef A c Z j m₀ c₀ Rhs ∧
    (∀ m, m₀ ≤ m → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), ψ.IsPrimitive → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) →
      Cg (m - c₀) (Rhs m ψ z) (v m * κ * a' ^ m * ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval L (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val))) ∧
    (∀ r, 1 ≤ r → ∀ x : (ZMod (l ^ r))ˣ, χ r x = (φ ((x : ZMod (l ^ r)).val : ZMod l))⁻¹) ∧
    ∃ r₁ : ℕ, ∀ r, r₁ ≤ r → 1 ≤ r → ∀ ξ : Qbar l, IsPrimitiveRoot ξ (l ^ r) →
      ¬ Cg (n₀ + r) (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass L r ξ x) 0

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def HTCoL (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ FixIc c (o i) ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg m ((l : Qbar l) ^ c₀ * Z m s y) ((l : Qbar l) ^ c₀ * h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

theorem htCoL_of_eq (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) (hZ : ∀ s, Z m s y = h * lamv l m s) : HTCoL A c j Z m c₀ y h :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun s _ _ => by simp [Cg, hZ, mul_assoc]⟩

end GlobalTheory.LambdaValuationPowers
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CycMOfNot
noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def cycM (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : (ZMod M)ˣ :=
  open Classical in
  if h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val then h.choose else 1

def repM (M : ℕ) (y : (ZMod M)ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val

def topM (l n r N : ℕ) : ℕ := l ^ (r + n) * N

instance topM.neZero (l n r N : ℕ) [Fact l.Prime] [NeZero N] : NeZero (topM l n r N) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (NeZero.ne N)⟩

def redM (l n r N : ℕ) (y : (ZMod (topM l n r N))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom y

def redL (l r : ℕ) (y : (ZMod (l ^ (r + 1)))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom y

theorem cycM_spec (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω)
    (h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := by
  classical
  unfold cycM
  rw [dite_eq_left h]
  exact h.choose_spec

theorem repM_spec (M : ℕ) (y : (ZMod M)ˣ)
    (h : ∃ s : Ω ≃ₐ[ℚ] Ω, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → (repM M y : Ω ≃ₐ[ℚ] Ω) z = z ^ (y : ZMod M).val :=
  Classical.epsilon_spec h

end GlobalTheory.K4
end
end
