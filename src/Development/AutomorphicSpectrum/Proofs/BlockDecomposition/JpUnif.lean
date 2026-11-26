module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerLeftBlock
noncomputable section

open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

variable {n : ℕ}

section Ring

variable {R : Type} [CommRing R]

def nU (y : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks 1 y 0 1
  inv := fromBlocks 1 (-y) 0 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

def pM (a d : GL (Fin n) R) (b : Matrix (Fin n) (Fin n) R) : GL (Ix n) R where
  val := fromBlocks a.1 b 0 d.1
  inv := fromBlocks (a⁻¹).1 (-((a⁻¹).1 * b * (d⁻¹).1)) 0 (d⁻¹).1
  val_inv := by
    simp [fromBlocks_multiply, ← fromBlocks_one, ← Matrix.mul_assoc]
  inv_val := by
    simp [fromBlocks_multiply, ← fromBlocks_one, Matrix.mul_assoc]

def lowerLeftBlock (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₁

def dBlk (g : GL (Ix n) R) : Matrix (Fin n) (Fin n) R := g.1.toBlocks₂₂

end Ring

def iD {k : Type} [Field k] (g : GL (Ix n) k) : ℕ := n - (dBlk g).rank

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {L : Type} [Field L] [Algebra O L]

abbrev inL : GL (Ix n) O →* GL (Ix n) L := Matrix.GeneralLinearGroup.map (algebraMap O L)

abbrev resK : GL (Ix n) O →* GL (Ix n) (IsLocalRing.ResidueField O) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue O)

def scM (w : Lˣ) : GL (Fin n) L := Units.map (Matrix.scalar (Fin n) : L →+* Matrix (Fin n) (Fin n) L).toMonoidHom w

def tauM (w : Lˣ) : GL (Ix n) L := pM 1 (scM w) 0

def IsHgt (nv : Lˣ →* ℝ≥0) (h : GL (Ix n) L → ℝ≥0) : Prop :=
  ∀ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
    h (pM a d b * inL κ) = nv (Matrix.GeneralLinearGroup.det a) / nv (Matrix.GeneralLinearGroup.det d)

def NvOK [Fintype (IsLocalRing.ResidueField O)] (nv : Lˣ →* ℝ≥0) (w : Lˣ) : Prop :=
  (∀ u : Oˣ, nv (Units.map (algebraMap O L).toMonoidHom u) = 1) ∧
    nv w = ((Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0))⁻¹

def IsRed (w : Lˣ) (κ : GL (Ix n) O) (hb : GL (Ix n) (IsLocalRing.ResidueField O)) : Prop :=
  ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ' : GL (Ix n) O),
    inL κ * tauM w = pM a d b * inL κ' ∧ resK κ' = hb

def Gam2 (ϖ : O) : Subgroup (GL (Ix n) O) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}))).ker

instance (ϖ : O) : (Gam2 (n := n) ϖ).Normal := by unfold Gam2; infer_instance

def avgK (ϖ : O) (φ : GL (Ix n) O → ℂ) : ℂ :=
  (Nat.card (GL (Ix n) O ⧸ Gam2 (n := n) ϖ) : ℂ)⁻¹ * ∑ᶠ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ, φ (Quotient.out u)

def liftM (ℓ : IsLocalRing.ResidueField O → O) (Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)) :
    Matrix (Fin n) (Fin n) L := (Y.map ℓ).map (algebraMap O L)

end Local

def coY {k : Type} [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (β Y : Matrix (Fin n) (Fin n) k) : ℂ :=
  ((Fintype.card k : ℂ) ^ (n * n))⁻¹ * (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β)))

end GlobalTheory.CompanionTheory.Jp

end
end

noncomputable section

open Matrix MeasureTheory
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp

def sumG {k : Type} [Field k] {n : ℕ} (f : GL (Ix n) k → ℂ) : ℂ := ∑ᶠ g, f g

def JpIw : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (g : GL (Ix n) L), ∃ (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ : GL (Ix n) O),
      g = pM a d b * inL κ

def JpHgt : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h → ∀ κ : GL (Ix n) O,
      h (inL κ * (tauM w)⁻¹) = (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ (2 * iD (resK κ)) /
        (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) ^ n

def JpUnif : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O),
    Irreducible ϖ → ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
    MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ φ : GL (Ix n) O → ℂ,
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∫ x, φ (ρ x) ∂ν = avgK ϖ φ

def JpCmp : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ Ψ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ, (∀ a d b g, Ψ (pM a d b * g) = Ψ g) →
    ∀ T : GL (Ix n) O → GL (Ix n) (IsLocalRing.ResidueField O), (∀ κ, IsRed (O := O) w κ (T κ)) →
      avgK ϖ (fun κ => Ψ (T κ)) =
        sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) /
          sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) =>
            (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g))

def JpPos : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (n r m : ℕ) (ψ₀ : AddChar k ℂ), ψ₀ ≠ 1 → ∀ β : Matrix (Fin n) (Fin n) k, β.rank = r →
    r ≤ m → ∃ x : ℝ, 0 < x ∧
      sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) = x

def JpCondition : Prop :=
  ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    [Fintype (IsLocalRing.ResidueField O)] (n r t : ℕ), r + t = n → 1 ≤ r →
    ∀ ψ₀ : AddChar (IsLocalRing.ResidueField O) ℂ, ψ₀ ≠ 1 →
    ∀ β : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), β.rank = r →
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
      ∀ ℓ : IsLocalRing.ResidueField O → O, (∀ a, IsLocalRing.residue O (ℓ a) = a) →
      ∀ nv : Lˣ →* ℝ≥0, NvOK (O := O) nv w → ∀ h : GL (Ix n) L → ℝ≥0, IsHgt (O := O) nv h →
      ∀ (X : Type) [Group X] [MeasurableSpace X] [MeasurableMul X] (ν : Measure X) [IsProbabilityMeasure ν]
        [ν.IsMulLeftInvariant] (ρ : X →* GL (Ix n) O), Function.Surjective ρ →
        MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) O))) → ∀ z : ℂ,
        ∫ x, ∑ Y : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O), coY ψ₀ β Y *
          (((h (inL (ρ x) * nU ((w⁻¹ : Lˣ).1 • liftM (L := L) ℓ Y)) : ℝ≥0) : ℝ) : ℂ) ^ (z + (n : ℂ) / 2) ∂ν = c z

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

open MeasureTheory
open scoped Matrix ComplexConjugate

def hermC (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) ℂ) := selfAdjoint _

theorem mem_hermC {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} : b ∈ hermC n ↔ b.IsHermitian := by
  unfold hermC
  rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  exact Iff.rfl

theorem isClosed_hermC (n : ℕ) : IsClosed (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hset : (hermC n : Set (Matrix (Fin n) (Fin n) ℂ)) = {b | star b = b} := rfl
  rw [hset]
  exact isClosed_eq continuous_star continuous_id

instance measHermC (n : ℕ) : MeasurableSpace (hermC n) := borel _

instance borelHermC (n : ℕ) : BorelSpace (hermC n) := ⟨rfl⟩

instance locCompactHermC (n : ℕ) : LocallyCompactSpace (hermC n) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isClosed_hermC n).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableHermC (n : ℕ) : SecondCountableTopology (hermC n) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  TopologicalSpace.Subtype.secondCountableTopology _

def detW {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : ℝ := (Matrix.det (1 + b * b)).re

def gramC {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a c => ∑ i, ∑ j, conj (X a i) * J i j * X c j

def phaseM {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (B : W → Matrix (Fin n) (Fin n) ℂ) (X : W → Fin n → Fin M → ℂ) : ℝ :=
  ∑ w, (Matrix.trace (B w * gramC (J w) (X w))).re

def coreC {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (g : (W → Fin n → Fin M → ℂ) → ℂ) (b : W → hermC n) : ℂ :=
  ∫ X, g X * Complex.exp (2 * Real.pi * Complex.I *
    ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X : ℝ) : ℂ)) ∂μ

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.UnfoldAbs

theorem hasSum_integral_of_norm_bound {A Z : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] [Countable Z] (G : Z → A → ℂ)
    (hm : ∀ q, AEStronglyMeasurable (G q) μ) (M : ℝ)
    (hb : ∀ b, Summable (fun q => ‖G q b‖) ∧ ∑' q, ‖G q b‖ ≤ M) :
    HasSum (fun q => ∫ b, G q b ∂μ) (∫ b, ∑' q, G q b ∂μ) := by
  have hbd : ∀ q b, ‖G q b‖ ≤ M := fun q b =>
    ((hb b).1.le_tsum q (fun _ _ => norm_nonneg _)).trans (hb b).2
  have hint : ∀ q, Integrable (G q) μ := fun q =>
    Integrable.of_bound (hm q) M (ae_of_all _ (hbd q))
  refine hasSum_integral_of_summable_integral_norm hint ?_
  refine summable_of_sum_le (c := ∫ _, M ∂μ)
    (fun q => integral_nonneg fun _ => norm_nonneg _) ?_
  intro s
  rw [← MeasureTheory.integral_finsetSum s (fun q _ => (hint q).norm)]
  exact integral_mono (MeasureTheory.integrable_finsetSum _ fun q _ => (hint q).norm) (integrable_const _)
    (fun b => ((hb b).1.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans (hb b).2)

theorem setIntegral_eq_zero_of_translate {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (Ψ : A → ℂ) (ν : A) (z : ℂ)
    (hz : z ≠ 1) (hΛ : ∀ (l : Λ) b, Ψ ((l : A) + b) = Ψ b) (hν : ∀ b, Ψ (ν + b) = z * Ψ b) :
    ∫ b in 𝓖, Ψ b ∂lam = 0 := by
  have h2 : IsAddFundamentalDomain Λ (ν +ᵥ 𝓖) lam := h𝓖.vadd_of_comm ν
  have e1 : ∫ b in 𝓖, Ψ b ∂lam = ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam :=
    h𝓖.setIntegral_eq h2 (fun g x => hΛ g x)
  have hpre : (fun x => ν + x) ⁻¹' (ν +ᵥ 𝓖) = 𝓖 := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e2 : ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam = ∫ b in 𝓖, Ψ (ν + b) ∂lam := by
    have := (measurePreserving_add_left lam ν).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft ν).measurableEmbedding Ψ (ν +ᵥ 𝓖)
    rw [hpre] at this
    exact this.symm
  have e3 : ∫ b in 𝓖, Ψ (ν + b) ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by
    simp_rw [hν]
    exact integral_const_mul _ _
  have e4 : (1 - z) * ∫ b in 𝓖, Ψ b ∂lam = 0 := by
    have : ∫ b in 𝓖, Ψ b ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by rw [← e3, ← e2, ← e1]
    linear_combination this
  exact (mul_eq_zero.mp e4).resolve_left (sub_ne_zero.mpr (Ne.symm hz))

theorem integrable_of_lattice_bound {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (F0 : A → ℂ) (hm : AEStronglyMeasurable F0 lam) (M : ℝ)
    (hb : ∀ b, Summable (fun l : Λ => ‖F0 ((l : A) + b)‖) ∧ ∑' l : Λ, ‖F0 ((l : A) + b)‖ ≤ M) :
    Integrable F0 lam := by
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have e : ∫⁻ b, ‖F0 b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 ((l : A) + b)‖ₑ ∂lam :=
    h𝓖.lintegral_eq_tsum'' _
  have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 ((l : A) + b)‖ₑ) (lam.restrict 𝓖) := fun l =>
    ((hm.comp_measurePreserving (measurePreserving_add_left lam (l : A))).enorm).restrict
  rw [e, ← lintegral_tsum hmeas]
  calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 ((l : A) + b)‖ₑ ∂lam
      ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal M ∂lam := by
        refine lintegral_mono (fun b => ?_)
        simp_rw [← ofReal_norm_eq_enorm]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb b).1]
        exact ENNReal.ofReal_le_ofReal (hb b).2
    _ < ⊤ := by simp [h1]

theorem unfold_abs : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ)
    (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  intro A X Y _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ c y0 F F0 ch hF hch hnorm hmul hΛ M hb τ hτ hcτ e he hfib
    hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ M := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) M (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have hF0e : F0 = F (e 0) := by
    funext b
    have := hF0 0 b
    simpa using this.symm
  have hint0 : Integrable F0 lam := by
    refine integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 F0 (hF0e ▸ hF (e 0)) M (fun b => ?_)
    simpa only [hF0] using hsub e he b
  refine ⟨hint0, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ ≃ {x // c x = y0} := Equiv.ofBijective
    (fun l => ⟨e l, (hfib _).2 ⟨l, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨l, hl⟩ := (hfib q).1 q.2
      exact ⟨l, Subtype.ext hl⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' l : Λ, F (e l) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  rw [← (key e he).tsum_eq]
  have hint1 : Integrable (fun b => F0 b * ch b) lam :=
    hint0.mono (hint0.aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  rw [h𝓖.integral_eq_tsum'' _ hint1]
  refine tsum_congr fun l => ?_
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  change F (e l) b * ch b = F0 ((l : A) + b) * ch ((l : A) + b)
  rw [hF0, hmul, hΛ, one_mul]

end GlobalTheory.CompanionTheory.UnfoldAbs
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfoldingStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_fourier_unfolding : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A) (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y) (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam) (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1) (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ) (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X) (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q) (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e) (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b)) (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b), Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | exact GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | (intros; apply GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
open scoped Matrix
open MeasureTheory

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

def PosOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, w ≠ 0 → 0 < ε * (star w ⬝ᵥ Z.mulVec w).re

def NonnegOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, 0 ≤ ε * (star w ⬝ᵥ Z.mulVec w).re

theorem integrable_of_mul_unimodular {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by
  have hfun : a = fun x => (a x * b x) * star (b x) := by
    funext x
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    simp
  have hmeas : AEStronglyMeasurable a μ := by
    rw [hfun]
    exact hi.1.mul hb.star
  refine hi.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hb1, mul_one]

theorem vanish_abs {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by
  have hbd : ∀ z, ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v‖ ∂μ := by
    intro z
    calc ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v * e v z‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ v, ‖J v‖ ∂μ := by
        congr 1
        ext v
        rw [norm_mul, hen, mul_one]
  have hFc : Continuous fun z => ∫ v, J v * e v z ∂μ := by
    refine continuous_of_dominated (F := fun z v => J v * e v z) (bound := fun v => ‖J v‖)
      (fun z => hJ.1.mul (he z).aestronglyMeasurable) (fun z => Filter.Eventually.of_forall
        fun v => by rw [norm_mul, hen, mul_one]) hJ.norm
      (Filter.Eventually.of_forall fun v => continuous_const.mul (he' v))
  set F : X → ℂ := fun z => ∫ v, J v * e v z ∂μ with hFdef
  have hzero : ∀ z₁ ∈ N, F z₁ = 0 := by
    intro z₁ hz₁
    by_contra hc
    set c := F z₁ with hcdef
    let G : X → ℝ := fun z => (starRingEnd ℂ c * F z).re
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_const.mul hFc)
    have hG1 : 0 < G z₁ := by
      show 0 < (starRingEnd ℂ c * c).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hc
    have hN'o : IsOpen (N ∩ {z | 0 < G z}) := hN.inter (isOpen_lt continuous_const hGc)
    obtain ⟨Φ, hΦc, hΦi, hΦpos, hΦsupp, hΦ1, hint⟩ :=
      hb _ hN'o Set.inter_subset_left z₁ ⟨hz₁, hG1⟩
    have hint' : ∫ z, F z * Φ z ∂μ = 0 := hint
    have hFΦi : Integrable (fun z => F z * Φ z) μ := by
      refine Integrable.mono (hΦi.norm.const_mul (∫ v, ‖J v‖ ∂μ))
        (hFc.aestronglyMeasurable.mul hΦi.1) (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_norm,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hbd z) (norm_nonneg _)
    let H : X → ℝ := fun z => (starRingEnd ℂ c * (F z * Φ z)).re
    have hHeq : ∀ z, H z = G z * (Φ z).re := by
      intro z
      simp only [H, G]
      rw [← mul_assoc, Complex.mul_re, (hΦpos z).2, mul_zero, sub_zero]
    have hHnn : ∀ z, 0 ≤ H z := by
      intro z
      rw [hHeq]
      by_cases hz : z ∈ N ∩ {z | 0 < G z}
      · exact mul_nonneg hz.2.le (hΦpos z).1
      · rw [hΦsupp z hz]
        simp
    have hHc : Continuous H := Complex.continuous_re.comp (continuous_const.mul (hFc.mul hΦc))
    have hHi : Integrable H μ := (hFΦi.const_mul (starRingEnd ℂ c)).re
    have hHpos : 0 < ∫ z, H z ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hHnn z) hHi]
      apply hHc.isOpen_support.measure_pos μ
      refine ⟨z₁, ?_⟩
      rw [Function.mem_support, hHeq]
      exact (mul_pos hG1 hΦ1).ne'
    have hHzero : ∫ z, H z ∂μ = 0 := by
      have h : ∫ z, H z ∂μ = (∫ z, starRingEnd ℂ c * (F z * Φ z) ∂μ).re :=
        integral_re (hFΦi.const_mul _)
      rw [h, integral_const_mul, hint', mul_zero, Complex.zero_re]
    linarith
  exact closure_minimal (s := N) (t := {z | F z = 0})
    (fun z hz => hzero z hz) (isClosed_eq hFc continuous_const) hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

variable {A : Type} [CommRing A]

structure IsFieldIdem (f : A) : Prop where
  idem : f * f = f
  ne : f ≠ 0
  inv : ∀ x, f * x ≠ 0 → ∃ y, f * x * y = f

structure IsFieldDec {ι : Type} [Fintype ι] (e : A) (f : ι → A) : Prop where
  field : ∀ i, IsFieldIdem (f i)
  orth : ∀ i j, i ≠ j → f i * f j = 0
  sum : ∑ i, f i = e

def NonDiscreteAt [TopologicalSpace A] (f : A) : Prop := ∀ V ∈ 𝓝 (0 : A), ∃ x ∈ V, x ≠ 0 ∧ f * x = x

def IsHaarMod [TopologicalSpace A] [MeasurableSpace A] (md : Aˣ →* ℝ≥0) : Prop :=
  ∀ h : Measure A, h.IsAddHaarMeasure → ∀ u : Aˣ, h.map (fun x => (u : A) * x) = ((md u : ℝ≥0∞))⁻¹ • h

abbrev Fx (A : Type) (m n : ℕ) : Type := Matrix (Fin m) (Fin n) A

variable {a r t : ℕ}

def yc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A r t := P z.1 * z.2

def vc (P : Fx A a r → Fx A r a) (z : Fx A a r × Fx A a t) : Fx A a t := z.2 - z.1 * yc P z

def admitted (e : A) (P : Fx A a r → Fx A r a) : Set (Fx A a r × Fx A a t) :=
  {z | e • z.1 = z.1 ∧ e • z.2 = z.2 ∧ P z.1 * z.1 = e • (1 : Fx A r r)}

def Piece (e f : A) (P : Fx A a r → Fx A r a) (i : Fin t) (C : Set A) : Set (Fx A a r × Fx A a t) :=
  {z | z ∈ admitted e P ∧ (∀ p q, z.1 p q ∈ C) ∧ (∀ l k, f * yc P z l k ∈ C ∧ (1 - f) * yc P z l k ∈ C) ∧
    (∀ p k, k ≠ i → vc P z p k ∈ C) ∧ (∀ p, (1 - f) * vc P z p i ∈ C) ∧
    ∃ c : Fin t → A, c i = 0 ∧ (∀ k, f * c k = c k ∧ c k ∈ C) ∧ ∀ p, f * vc P z p i = ∑ k, c k * vc P z p k}

def gU (i : Fin t) (c₀ : Fin t → A) : Fx A t t := 1 + Matrix.of fun k j => if j = i then c₀ k else 0

def gD (i : Fin t) (u : A) : Fx A t t := Matrix.diagonal (Function.update 1 i u)

def yU (i : Fin t) (y₀ : Fin r → A) : Fx A r t := Matrix.of fun l j => if j = i then y₀ l else 0

end GlobalTheory.CompanionTheory.NullFr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

open scoped Matrix

variable {P ι : Type}

def qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : P → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (A w *ᵥ x w))

def gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))

def boxR [Fintype ι] (t : P → ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, ‖x w‖ ≤ t w}

def coreR [Fintype ι] (δ R : ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegBump
open Topology

namespace GlobalTheory.CompanionTheory.Bump

theorem exists_nonneg_bump :
    ∀ {X : Type} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (x : X) (N : Set X),
      N ∈ 𝓝 x → ∃ φ : X → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ 0 ≤ φ ∧ φ x ≠ 0 ∧
        Function.support φ ⊆ N := by
  intro X _ _ _ x N hN
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.mpr hN
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (s := {x}) (t := (interior N)ᶜ) isCompact_singleton isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h hx))
  refine ⟨f, f.continuous, hfc, fun y => (hfI y).1, ?_, ?_⟩
  · have h1 : f x = 1 := hf1 (Set.mem_singleton x)
    rw [h1]
    exact one_ne_zero
  · intro y hy
    by_contra hyN
    exact hy (hf0 (fun hi => hyN (interior_subset hi)))

end GlobalTheory.CompanionTheory.Bump
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGlLastRowEq
open Matrix

namespace GlobalTheory.CompanionTheory.LinAlg

theorem exists_GL_lastRow_eq : ∀ (K : Type) [Field K] (n : ℕ) (a : Fin (n + 1) → K), a ≠ 0 →
    ∃ m : GL (Fin (n + 1)) K, vecMul (Pi.single (Fin.last n) 1) (m : Matrix (Fin (n + 1)) (Fin (n + 1)) K) = a := by
  intro K _ n a ha
  classical
  set e : Fin (n + 1) → K := Pi.single (Fin.last n) 1 with he_def
  have he : e ≠ 0 := by simp [e]
  let f : (K ∙ e) ≃ₗ[K] (K ∙ a) :=
    (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton K _ a ha
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : (LinearEquiv.toSpanNonzeroSingleton K _ e he).symm
      ⟨e, Submodule.mem_span_singleton_self e⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hga : g e = a := by
    have hx := hg ⟨e, Submodule.mem_span_singleton_self e⟩
    rw [← hx]
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.toSpanNonzeroSingleton_one]
  have hdet : IsUnit (LinearMap.toMatrix' (g : (Fin (n + 1) → K) →ₗ[K] Fin (n + 1) → K))ᵀ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' g
  refine ⟨hdet.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  simpa using hga

end GlobalTheory.CompanionTheory.LinAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjection
namespace GlobalTheory.CompanionTheory.EigenLift

theorem exists_eigenvector_of_surjective_intertwiner
    (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hfT : f ∘ₗ T = S ∘ₗ f)
    (c : ℂ) (w' : W') (hw' : w' ≠ 0) (hS : S w' = c • w') :
    ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  by_contra hne
  push_neg at hne
  haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf
  set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA
  set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra h0
    apply hne w h0
    simpa [hA, sub_eq_zero] using hw
  have hsurjT : Function.Surjective A := LinearMap.injective_iff_surjective.1 hinj
  have hcomm : ∀ z, f (A z) = B (f z) := by
    intro z
    have h1 := LinearMap.congr_fun hfT z
    simp only [LinearMap.comp_apply] at h1
    simp [hA, hB, map_sub, map_smul, h1]
  have hsurjS : Function.Surjective B := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hsurjT x
    exact ⟨f z, (hcomm z).symm⟩
  have hinjS := LinearMap.injective_iff_surjective.2 hsurjS
  apply hw'
  apply hinjS
  simp [hB, hS]

theorem nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS

end GlobalTheory.CompanionTheory.EigenLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjectionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_lift_of_surjection : ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'), Function.Surjective f → f ∘ₗ T = S ∘ₗ f → ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  first | exact @GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | exact GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts | (intros; apply GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnIteratedDerivFamily
open Filter Topology

namespace GlobalTheory.CompanionTheory.HolFamily

theorem continuousOn_deriv_family (P : Type) [TopologicalSpace P] (U : Set ℂ) (hU : IsOpen U)
    (H : P → ℂ → ℂ) (hc : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U))
    (hd : ∀ p, DifferentiableOn ℂ (H p) U) :
    ContinuousOn (fun q : P × ℂ => deriv (H q.1) q.2) (Set.univ ×ˢ U) := by
  rintro ⟨p0, z0⟩ ⟨-, hz0⟩
  simp only at hz0
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hU z0 hz0
  have hR : 0 < e / 3 := by positivity
  set R := e / 3 with hRdef
  have hKU : Metric.closedBall z0 (2 * R) ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball
    rw [hRdef]; linarith
  let K : Set ℂ := Metric.closedBall z0 (2 * R)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall z0 (2 * R))
  have hFc : Continuous (fun x : P × K => H x.1 x.2) := by
    have : Continuous (fun x : P × K => ((x.1, (x.2 : ℂ)) : P × ℂ)) := by fun_prop
    exact hc.comp_continuous this (fun x => ⟨Set.mem_univ _, hKU x.2.2⟩)
  let F : C(P × K, ℂ) := ⟨fun x => H x.1 x.2, hFc⟩
  let G : C(P, C(K, ℂ)) := F.curry
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  have hGc : Tendsto G (𝓝 p0) (𝓝 (G p0)) := G.continuous.tendsto p0
  have h1 : ∀ᶠ p in 𝓝 p0, dist (G p) (G p0) < ε / 2 * R / 2 :=
    (Metric.tendsto_nhds.1 hGc) _ (by positivity)
  have hdc : ContinuousAt (deriv (H p0)) z0 :=
    ((hd p0).deriv hU).continuousOn.continuousAt (hU.mem_nhds hz0)
  have h2 : ∀ᶠ z in 𝓝 z0, dist (deriv (H p0) z) (deriv (H p0) z0) < ε / 2 :=
    (Metric.tendsto_nhds.1 hdc) _ (by positivity)
  have h3 : ∀ᶠ z in 𝓝 z0, z ∈ Metric.ball z0 R := Metric.ball_mem_nhds z0 hR
  have h4 := h1.prod_nhds (h2.and h3)
  filter_upwards [nhdsWithin_le_nhds h4]
  rintro ⟨p, z⟩ ⟨hp, hz, hzR⟩
  simp only at hp hz hzR ⊢
  have hsub : Metric.closedBall z R ⊆ K := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    rw [Metric.mem_ball] at hzR
    have := dist_triangle w z z0
    linarith
  have hfd : DifferentiableOn ℂ (fun w => H p w - H p0 w) U := (hd p).sub (hd p0)
  have hzU : z ∈ U := hKU (hsub (Metric.mem_closedBall_self hR.le))
  have hnh : U ∈ 𝓝 z := hU.mem_nhds hzU
  have hderiv : deriv (fun w => H p w - H p0 w) z = deriv (H p) z - deriv (H p0) z :=
    deriv_fun_sub ((hd p).differentiableAt hnh) ((hd p0).differentiableAt hnh)
  have hbound : ∀ w ∈ Metric.sphere z R, ‖H p w - H p0 w‖ ≤ ε / 2 * R / 2 := by
    intro w hw
    have hwK : w ∈ K := hsub (Metric.sphere_subset_closedBall hw)
    have := ContinuousMap.dist_apply_le_dist (f := G p) (g := G p0) (⟨w, hwK⟩ : K)
    have h5 : dist (G p ⟨w, hwK⟩) (G p0 ⟨w, hwK⟩) = ‖H p w - H p0 w‖ := by
      rw [dist_eq_norm]; rfl
    rw [← h5]
    exact this.trans hp.le
  have hcauchy : ‖deriv (fun w => H p w - H p0 w) z‖ ≤ ε / 2 * R / 2 / R :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      (hfd.diffContOnCl_ball (hsub.trans hKU)) hbound
  have hval : ε / 2 * R / 2 / R = ε / 4 := by field_simp; ring
  rw [hval, hderiv] at hcauchy
  calc dist (deriv (H p) z) (deriv (H p0) z0)
      ≤ dist (deriv (H p) z) (deriv (H p0) z) + dist (deriv (H p0) z) (deriv (H p0) z0) :=
        dist_triangle _ _ _
    _ < ε := by
        rw [dist_eq_norm (deriv (H p) z)]
        linarith

theorem continuousOn_iteratedDeriv_family :
    ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
      ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) →
      (∀ p, DifferentiableOn ℂ (H p) U) →
        ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U) := by
  intro P _ U hU H hc hd r
  have hdiff : ∀ (r : ℕ) (p : P), DifferentiableOn ℂ (iteratedDeriv r (H p)) U := by
    intro r p
    induction r with
    | zero => simpa [iteratedDeriv_zero] using hd p
    | succ r ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hU
  induction r with
  | zero => simpa [iteratedDeriv_zero] using hc
  | succ r ih =>
    simp only [iteratedDeriv_succ]
    exact continuousOn_deriv_family P U hU (fun p => iteratedDeriv r (H p)) ih (hdiff r)

end GlobalTheory.CompanionTheory.HolFamily
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.CoefId

variable {n : ℕ}

def mon (e : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ a, z a ^ e a

def dl (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def prs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

def score (T : Finset (Fin n × Fin n)) : Fin n → ℤ := fun c =>
  ((T.filter fun p => p.1 = c).card : ℤ) + (((prs n \ T).filter fun p => p.2 = c).card : ℤ)

def tZero (lev : Fin n → ℕ) : Finset (Fin n × Fin n) := (prs n).filter fun p => lev p.1 < lev p.2

end GlobalTheory.CompanionTheory.CoefId
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangular
open Matrix

namespace GlobalTheory.CompanionTheory.QR

theorem exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

end GlobalTheory.CompanionTheory.QR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic
open Filter Topology

namespace GlobalTheory.CompanionTheory.Entire

theorem local_factorisation :
    ∀ A : ℂ → ℂ, Differentiable ℂ A → (∃ z, A z ≠ 0) → ∀ s₀ : ℂ,
      ∃ (k : ℕ) (U : Set ℂ) (u : ℂ → ℂ), IsOpen U ∧ s₀ ∈ U ∧ DifferentiableOn ℂ u U ∧
        ∀ s ∈ U, u s ≠ 0 ∧ A s = (s - s₀) ^ k * u s := by
  intro A hA hne s₀
  have han : AnalyticAt ℂ A s₀ := hA.analyticAt s₀
  have hnz : ¬ ∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨z, hz⟩ := hne
    exact hz (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w _ => hA.analyticAt w) isPreconnected_univ (Set.mem_univ s₀) hev (Set.mem_univ z))
  obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hall : ∀ᶠ z in 𝓝 s₀, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ A z = (z - s₀) ^ n * g z :=
    hg.eventually_analyticAt.and ((hg.continuousAt.eventually_ne hg0).and
      (hev.mono fun z hz => by simpa [smul_eq_mul] using hz))
  obtain ⟨U, hU, hUo, hsU⟩ := eventually_nhds_iff.mp hall
  exact ⟨n, U, g, hUo, hsU, fun z hz => (hU z hz).1.differentiableAt.differentiableWithinAt,
    fun z hz => ⟨(hU z hz).2.1, (hU z hz).2.2⟩⟩

end GlobalTheory.CompanionTheory.Entire
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZero
open Matrix

namespace GlobalTheory.CompanionTheory.RelIndex

theorem relIndex_ne_zero_of_isCompact_of_isOpen :
    ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  intro X _ _ _ A H hA hH _
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) :=
    AddSubgroup.quotient_finite_of_isOpen _ hopen
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.CompanionTheory.RelIndex
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexOpenCompactNeZeroStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_open_compact_ne_zero : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A → H.relIndex A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | exact GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen | (intros; apply GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen <;> assumption)
end
end
