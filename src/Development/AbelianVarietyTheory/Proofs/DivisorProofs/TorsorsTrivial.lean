module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

abbrev GenFib (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Type :=
  Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))

def TorsorsTrivial (B : Type) [CommRing B] (q : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
    Module.FaithfullyFlat B D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[B] B)

def AbsIntClosed (T : Type) [CommRing T] : Prop :=
  ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0

def KeyAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocalWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocal : Prop := KeyLocalWith (fun _ _ _ _ => True)

def KeyGeneric : Prop :=
  KeyLocalWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyClosedPts : Prop :=
  KeyLocalWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyOrigin : Prop :=
  KeyLocalWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

end GlobalTheory.LocAcyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
noncomputable section

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable {F : Type} [Field F] [NumberField F]

def NZ (I : FractionalIdeal (𝓞 F)⁰ F) : Type := {b : F // b ∈ I ∧ b ≠ 0}

def unitRel (I : FractionalIdeal (𝓞 F)⁰ F) : Setoid (NZ I) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def phi (σ w : ℂ) : ℂ := w⁻¹ ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ (-2 * σ)

def hTrans (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def cConst (σ : ℂ) : ℂ := hTrans σ 0 1


variable (F) in
def kFac (σ : ℂ) : ℂ :=
  ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))

def fTerm (σ : ℂ) (z : Emb F → ℂ) (b ν : F) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * (z τ).im))

def aPart (𝔞 : Frac F) (σ : ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 (c.out.1, 0)

def bOne (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1

def bZero (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  if σ = 0 then 0 else
    kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * (((nrm (F := F) 𝔟) : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) *
      ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))

def gFun (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  aPart 𝔞 σ + bZero Zb 𝔞 𝔟 σ z + kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * bOne 𝔞 𝔟 σ z

def IsGood (P : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (P σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (P σ) z) halfPlane)

theorem kFac_differentiable : Differentiable ℂ (kFac (F := F)) := by
  intro σ
  unfold kFac
  rw [show (fun σ : ℂ => ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))) =
      fun σ => ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ)) ^ Fintype.card (Emb F) from
    funext fun σ => Finset.prod_const _]
  refine DifferentiableAt.pow (DifferentiableAt.const_mul ?_ _) _
  refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
  exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'

end GlobalTheory.HeckeTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma Matrix

def stdH (K : UQ) (n : ℕ) (y z : Fin n → K.E) : K.E := ∑ k, y k * K.c (z k)

def IsModel {K : UQ} (B : InvAlg K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) : Prop :=
  B.σ (x : B.A) = x ∧ (∀ y, ψ (B.g * y) = γ *ᵥ ψ y) ∧ ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z

end GlobalTheory.InertUnitOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem HasQ.coeff_unique {N : ℕ} {f : ℍ → ℂ} {a b : ℕ → ℂ} (hN : 0 < N) (ha : HasQ N f a)
    (hb : HasQ N f b) : a = b := by
  have toSeries : ∀ c : ℕ → ℂ, HasQ N f c → GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk c) := by
    intro c hc τ
    have hs := (hasQ_iff N f c).1 hc τ
    simpa [PowerSeries.coeff_mk, Function.Periodic.qParam] using hs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab := GlobalTheory.HasQExpansion.unique hN' (toSeries a ha) (toSeries b hb)
  funext n
  simpa using congrArg (PowerSeries.coeff n) hab

theorem HasQ.fun_unique {N : ℕ} {f g : ℍ → ℂ} {a : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g a) :
    f = g := by
  funext τ
  exact (hf τ).unique (hg τ)

theorem hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) :=
  ⟨fun _ _ _ _ hN ha hb => HasQ.coeff_unique hN ha hb, fun _ _ _ _ hf hg => HasQ.fun_unique hf hg⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique : (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧ (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by
  first | exact @GlobalTheory.QFam.hasQ_unique_both | exact GlobalTheory.QFam.hasQ_unique_both | (intros; apply GlobalTheory.QFam.hasQ_unique_both <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam.QAllSubring

variable {R : Subring ℂ} {N : ℕ}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.add {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [add_mul] using (ha τ).add (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [sub_mul] using (ha τ).sub (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.mul {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.pow {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.prod {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩

end GlobalTheory.QFam.QAllSubring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  first | exact @GlobalTheory.QFam.QAllSubring.ring_closed | exact GlobalTheory.QFam.QAllSubring.ring_closed | (intros; apply GlobalTheory.QFam.QAllSubring.ring_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.LipschitzTR

variable (F : Type) [Field F] [NumberField F]

abbrev RSp := EuclideanSpace ℝ (F →+* ℝ)

def remb : F →+ RSp F where
  toFun a := WithLp.toLp 2 (fun τ : F →+* ℝ => τ a)
  map_zero' := by ext τ; simp
  map_add' a b := by ext τ; simp

variable {F}

@[simp] theorem remb_apply (a : F) (τ : F →+* ℝ) : remb F a τ = τ a := rfl

def latOf (N : FractionalIdeal (𝓞 F)⁰ F) : Submodule ℤ (RSp F) :=
  Submodule.map (remb F).toIntLinearMap ((N : Submodule (𝓞 F) F).restrictScalars ℤ)

theorem mem_latOf (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by
  simp [latOf]

def phi1 (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w)
  else 0

def Phi (k : ℕ) (z : (F →+* ℝ) → ℂ) (ξ : RSp F) : ℂ :=
  ∏ τ : F →+* ℝ, phi1 k (z τ) (ξ τ)

end GlobalTheory.LipschitzTR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
open IsLocalRing

namespace GlobalTheory.StrictHensUnion


open CategoryTheory Limits in
theorem indEtale_of_directed_union : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (D : ι → Subalgebra R S), Monotone D → (∀ s : S, ∃ i, s ∈ D i) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R (D i))) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) := by
  intro R S _ _ _ ι _ _ _ D hmono hcov hD
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  haveI : IsFiltered ι := inferInstance
  let F : ι ⥤ CommRingCat.{0} :=
    { obj := fun i => CommRingCat.of (D i)
      map := fun {i j} h => CommRingCat.ofHom
        (Subalgebra.inclusion (hmono (leOfHom h))).toRingHom
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  let t : (Functor.const ι).obj (CommRingCat.of R) ⟶ F :=
    { app := fun i => CommRingCat.ofHom (algebraMap R (D i)), naturality := fun _ _ _ => rfl }
  let s : F ⟶ (Functor.const ι).obj (CommRingCat.of S) :=
    { app := fun i => CommRingCat.ofHom (D i).val.toRingHom, naturality := fun _ _ _ => rfl }
  refine ⟨ι, inferInstance, inferInstance, F, t, s, ?_, fun i => ⟨hD i, rfl⟩⟩
  haveI : ReflectsColimit F (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

def DivIdx {A : Type} [CommRing A] (M : Submonoid A) : Type := M

def DivIdx.el {A : Type} [CommRing A] {M : Submonoid A} (x : DivIdx M) : A := ((show M from x) : A)

theorem DivIdx.el_mem {A : Type} [CommRing A] {M : Submonoid A} (x : DivIdx M) : x.el ∈ M :=
  (show M from x).2

instance DivIdx.instPreorder {A : Type} [CommRing A] (M : Submonoid A) : Preorder (DivIdx M) where
  le x y := x.el ∣ y.el
  le_refl x := dvd_refl _
  le_trans _ _ _ h₁ h₂ := dvd_trans h₁ h₂

instance DivIdx.instIsDirected {A : Type} [CommRing A] (M : Submonoid A) :
    IsDirected (DivIdx M) (· ≤ ·) :=
  ⟨fun x y => ⟨(show M from ((show M from x) * (show M from y))), dvd_mul_right x.el y.el, dvd_mul_left y.el x.el⟩⟩

instance DivIdx.instNonempty {A : Type} [CommRing A] (M : Submonoid A) : Nonempty (DivIdx M) :=
  ⟨(1 : M)⟩


open CategoryTheory Limits in
theorem indEtale_localization_of_etale : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A] (M : Submonoid A), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R (Localization M)) := by
  intro R A _ _ _ _ M
  haveI : IsFiltered (DivIdx M) := inferInstance
  have hunit : ∀ {x y : DivIdx M}, x ≤ y →
      IsUnit (algebraMap A (Localization.Away y.el) x.el) := by
    intro x y h
    obtain ⟨c, hc⟩ := h
    have hy := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away y.el) y.el
    have he : algebraMap A (Localization.Away y.el) y.el =
        algebraMap A (Localization.Away y.el) x.el * algebraMap A (Localization.Away y.el) c := by
      rw [← map_mul, ← hc]
    exact isUnit_of_mul_isUnit_left (he ▸ hy)
  have hM : ∀ x : DivIdx M, IsUnit (algebraMap A (Localization M) x.el) :=
    fun x => IsLocalization.map_units (Localization M) (⟨x.el, x.el_mem⟩ : M)
  let F : DivIdx M ⥤ CommRingCat.{0} :=
    { obj := fun x => CommRingCat.of (Localization.Away x.el)
      map := fun {x y} h => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hunit (leOfHom h)))
      map_id := fun x => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [IsLocalization.Away.lift_comp]
      map_comp := fun {x y z} f g => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [IsLocalization.Away.lift, IsLocalization.lift_eq] }
  let t : (Functor.const (DivIdx M)).obj (CommRingCat.of R) ⟶ F :=
    { app := fun x => CommRingCat.ofHom (algebraMap R (Localization.Away x.el))
      naturality := fun x y h => by
        ext r
        simp [F, IsScalarTower.algebraMap_apply R A (Localization.Away x.el),
          IsScalarTower.algebraMap_apply R A (Localization.Away y.el),
          IsLocalization.Away.lift, IsLocalization.lift_eq] }
  let s : F ⟶ (Functor.const (DivIdx M)).obj (CommRingCat.of (Localization M)) :=
    { app := fun x => CommRingCat.ofHom (IsLocalization.Away.lift x.el (hM x))
      naturality := fun x y h => by
        ext1
        apply IsLocalization.ringHom_ext (Submonoid.powers x.el)
        ext a
        simp [F, IsLocalization.Away.lift, IsLocalization.lift_eq] }
  refine ⟨DivIdx M, inferInstance, inferInstance, F, t, s, ?_, fun x => ⟨?_, ?_⟩⟩
  · haveI : ReflectsColimit F (forget CommRingCat.{0}) :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    refine isColimitOfReflects (forget CommRingCat.{0}) ?_
    refine Types.FilteredColimit.isColimitOf' _ _ (fun z => ?_) (fun x u v huv => ?_)
    · obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.mk'_surjective M (show Localization M from z)
      let mi : DivIdx M := (show DivIdx M from m)
      have hmi : mi.el = (m : A) := rfl
      refine ⟨mi, (algebraMap A (Localization.Away mi.el) a *
        IsLocalization.Away.invSelf (S := Localization.Away mi.el) mi.el : Localization.Away mi.el), ?_⟩
      change (show Localization M from z) = IsLocalization.Away.lift mi.el (hM mi)
        (algebraMap A (Localization.Away mi.el) a * IsLocalization.Away.invSelf mi.el)
      have h1 : ∀ b : A, IsLocalization.Away.lift mi.el (hM mi)
          (algebraMap A (Localization.Away mi.el) b) = algebraMap A (Localization M) b := by
        intro b
        simp [IsLocalization.Away.lift, IsLocalization.lift_eq]
      rw [← hz, IsLocalization.mk'_eq_iff_eq_mul, ← hmi, ← h1 mi.el, ← h1 a, ← map_mul, mul_assoc,
        mul_comm (IsLocalization.Away.invSelf mi.el), IsLocalization.Away.mul_invSelf, mul_one]
    · let u' : Localization.Away x.el := u
      let v' : Localization.Away x.el := v
      let φx : Localization.Away x.el →+* Localization M := IsLocalization.Away.lift x.el (hM x)
      have huv' : φx (u' - v') = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 huv
      obtain ⟨⟨a, p⟩, hw0⟩ := IsLocalization.mk'_surjective (Submonoid.powers x.el) (u' - v')
      have hw : IsLocalization.mk' (Localization.Away x.el) a p = u' - v' := hw0
      have ha : algebraMap A (Localization M) a = 0 := by
        have h2 := IsLocalization.mk'_spec (Localization.Away x.el) a p
        have h3 := congrArg φx h2
        rw [map_mul, hw, huv', zero_mul] at h3
        rw [h3]
        simp [φx, IsLocalization.Away.lift, IsLocalization.lift_eq]
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M (Localization M) a).1 ha
      let k : DivIdx M := (show DivIdx M from ((show M from x) * m))
      have hk : k.el = x.el * (m : A) := rfl
      have hxk : x ≤ k := ⟨(m : A), hk⟩
      refine ⟨k, homOfLE hxk, ?_⟩
      change IsLocalization.Away.lift x.el (hunit hxk) u' = IsLocalization.Away.lift x.el (hunit hxk) v'
      rw [← sub_eq_zero, ← map_sub, ← hw]
      have hmk : IsUnit (algebraMap A (Localization.Away k.el) (m : A)) := by
        have hy := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away k.el) k.el
        rw [hk, map_mul] at hy
        exact isUnit_of_mul_isUnit_right hy
      have hak : algebraMap A (Localization.Away k.el) a = 0 := by
        apply (hmk.mul_right_eq_zero).1
        rw [← map_mul, hm, map_zero]
      have hpk : IsUnit (IsLocalization.Away.lift x.el (hunit hxk)
          (algebraMap A (Localization.Away x.el) (p : A))) := by
        obtain ⟨n, hn⟩ := p.2
        rw [← hn, map_pow, map_pow]
        exact ((IsLocalization.Away.algebraMap_isUnit x.el).map _).pow n
      apply (hpk.mul_left_eq_zero).1
      rw [← map_mul, IsLocalization.mk'_spec]
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hak]
  · haveI : Algebra.Etale A (Localization.Away x.el) :=
      Algebra.Etale.of_isLocalizationAway x.el
    haveI : Algebra.Etale R (Localization.Away x.el) :=
      Algebra.Etale.comp R A _
    change RingHom.Etale (algebraMap R (Localization.Away x.el))
    exact RingHom.etale_algebraMap.2 inferInstance
  · ext r
    simp [t, s, IsScalarTower.algebraMap_apply R A (Localization.Away x.el),
      IsScalarTower.algebraMap_apply R A (Localization M), IsLocalization.Away.lift]
    exact IsLocalization.lift_eq _ _


open CategoryTheory in
theorem indEtale_over_localization : ∀ (R L S : Type) [CommRing R] [CommRing L] [CommRing S] [Algebra R L] [Algebra R S] [Algebra L S] [IsScalarTower R L S] (N : Submonoid R) [IsLocalization N L], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R S) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap L S) := by
  intro R L S _ _ _ _ _ _ _ N _ hR
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S N) S := by
    refine IsLocalization.self ?_
    rintro _ ⟨n, hn, rfl⟩
    rw [IsScalarTower.algebraMap_apply R L S]
    exact (IsLocalization.map_units L (⟨n, hn⟩ : N)).map (algebraMap L S)
  haveI : Algebra.IsPushout R S L S := Algebra.isPushout_of_isLocalization N L S S
  haveI : Algebra.IsPushout R L S S := this.symm
  have sq := CommRingCat.isPushout_of_isPushout R L S S
  have : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale)) sq hR

theorem indEtale_of_algEquiv {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R A)) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap R B) := by
  have : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
  have h2 := CategoryTheory.MorphismProperty.RespectsIso.postcomp
    (CategoryTheory.MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale))
    (e.toRingEquiv.toCommRingCatIso.hom) (CommRingCat.ofHom (algebraMap R A)) h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  convert h2 using 1
  ext x
  simp

theorem isStrictHenselisation_of_directed_union : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O]
    [IsSepClosed (IsLocalRing.ResidueField O)],
    (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
      (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧
      ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A)
        (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) →
    ∃ (P : Ideal (Polynomial T)) (_ : P.IsPrime) (φ : Localization.AtPrime P →+* O),
      φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  intro T O _ _ _ _ _ _ _ _ _ hS
  obtain ⟨ι, _, _, _, Si, hmono, hcov, hA⟩ := hS
  set P : Ideal (Polynomial T) := (maximalIdeal O).comap (algebraMap (Polynomial T) O) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap (Polynomial T) O y) := by
    intro y
    have := y.2
    by_contra hy
    exact this ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let φ : Localization.AtPrime P →+* O := IsLocalization.lift hu
  have hφ : φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O :=
    IsLocalization.lift_comp hu
  refine ⟨P, hPp, φ, hφ, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro ha
    have h1 : algebraMap (Polynomial T) O a =
        algebraMap (Polynomial T) O s * φ (IsLocalization.mk' _ a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).1 rfl
    have h2 : IsUnit (algebraMap (Polynomial T) O a) := by
      rw [h1]; exact (hu s).mul hx
    exact (IsLocalRing.mem_maximalIdeal _).1 ha h2
  · letI : Algebra (Localization.AtPrime P) O := φ.toAlgebra
    haveI : IsScalarTower (Polynomial T) (Localization.AtPrime P) O :=
      IsScalarTower.of_algebraMap_eq fun x => (congrArg (fun f => f x) hφ).symm
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) O) := by
      refine indEtale_of_directed_union (Polynomial T) O ι Si hmono hcov fun i => ?_
      obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hA i
      exact indEtale_of_algEquiv e (indEtale_localization_of_etale (Polynomial T) A q.primeCompl)
    exact indEtale_over_localization (Polynomial T) (Localization.AtPrime P) O P.primeCompl hR

end GlobalTheory.StrictHensUnion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

theorem hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr

theorem sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by
  intro V _ _ _ B _ _ _ om ρ h X l h1 h2 h3 Θ hd hc
  have sep : ∀ b b' : B, (∀ x, l x b = l x b') → b = b' := fun b b' hb => by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact h2 _ 0 le_rfl fun x => by rw [map_sub, hb, sub_self, norm_zero]
  have lsm : ∀ x (r : ℝ) (b : B), l x (r • b) = r • l x b := fun x r b => ((l x).restrictScalars ℝ).map_smul r b
  have key : ∀ f ∈ Θ, ∃ D : V →L[ℝ] B, (∀ z, D z ∈ Θ) ∧
      ∀ v, HasFDerivAt (fun w => ρ w f) (((ρ v).restrictScalars ℝ).comp D -
        (om v).smulRight (((π : ℂ) * I) • ρ v f)) v := by
    intro f hf
    choose g hg hg' using hc f hf
    have hgd : ∀ x z, l x (g z) = fderiv ℝ (fun v => l x (ρ v f)) 0 z := by
      intro x z
      refine (hg' z x).unique ?_
      have a1 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
      have a2 : HasFDerivAt (fun v => l x (ρ v f)) (fderiv ℝ (fun v => l x (ρ v f)) 0) ((0 : ℝ) • z) := by
        rw [zero_smul]; exact (hd f hf x 0).hasFDerivAt
      exact a2.comp_hasDerivAt (0 : ℝ) a1
    let D0 : V →ₗ[ℝ] B :=
      { toFun := g
        map_add' := fun z z' => sep _ _ fun x => by rw [map_add (f := _), hgd, hgd, hgd, map_add (f := _)]
        map_smul' := fun r z => sep _ _ fun x => by rw [RingHom.id_apply, lsm, hgd, hgd, map_smul] }
    let D : V →L[ℝ] B := LinearMap.toContinuousLinearMap D0
    have hD : ∀ z, D z = g z := fun z => rfl
    refine ⟨D, fun z => hg z, hasFDerivAt_of_norming l h1 h2 _ _ ?_ ?_⟩
    · refine continuous_clm_apply.2 fun z => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      have a1 := h.2.2.2 (D z)
      have a2 := h.2.2.2 f
      exact a1.sub ((om.continuous.clm_apply continuous_const).smul (a2.const_smul _))
    · intro x v
      obtain ⟨a, x', hx⟩ := h3 x v
      have e : (fun w => l x (ρ w f)) =
          fun w => cexp (-(π * I) * (om v (w - v) : ℝ)) * (a * l x' (ρ (w - v) f)) := by
        funext w
        rw [← hx, h.2.1, add_sub_cancel, map_smul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        simp
      have b0 : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v := (hasFDerivAt_id v).sub_const v
      have b1 : HasFDerivAt (fun w => l x' (ρ (w - v) f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) v := by
        have a2 : HasFDerivAt (fun v => l x' (ρ v f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) (v - v) := by
          rw [sub_self]; exact (hd f hf x' 0).hasFDerivAt
        simpa [Function.comp_def] using HasFDerivAt.comp (f := fun w : V => w - v) v a2 b0
      have b2 : HasFDerivAt (fun w : V => ((om v (w - v) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om v)) v := by
        simpa [Function.comp_def] using (Complex.ofRealCLM.comp (om v)).hasFDerivAt.comp v b0
      have b3 := ((b2.const_mul (-(π * I) : ℂ)).cexp).mul (b1.const_mul a)
      rw [e]
      refine b3.congr_fderiv ?_
      ext z
      simp [← hgd, h.1, hD, lsm, hx]
      ring
  have ind : ∀ n : ℕ, ∀ f ∈ Θ, ContDiff ℝ n fun v => ρ v f := by
    intro n
    induction n with
    | zero => intro f _; exact contDiff_zero.2 (h.2.2.2 f)
    | succ n ih =>
      intro f hf
      obtain ⟨D, hD, hF⟩ := key f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun v => (hF v).differentiableAt, by simp, fun z => ?_⟩
      simp only [(hF _).fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      exact (ih _ (hD z)).sub ((om.contDiff.clm_apply contDiff_const).smul ((ih f hf).const_smul _))
  intro f hf
  exact contDiff_infty.2 fun n => ind n f hf

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSetStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_smooth_of_weak_derivative_closed_set : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) → (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) → (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B, (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) → (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) → ∀ f ∈ Θ, Sm ρ f := by
  first | exact @GlobalTheory.RealWeil.sm_of_weak_deriv_closed | exact GlobalTheory.RealWeil.sm_of_weak_deriv_closed | (intros; apply GlobalTheory.RealWeil.sm_of_weak_deriv_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

noncomputable section
namespace GlobalTheory.HermitianPreEigenvalues
variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

def mulR (a : S → O) (N : ℕ) (r : RS a) : (Fin N → RS a) →ₗ[O] (Fin N → RS a) :=
  (LinearMap.lsmul (RS a) (Fin N → RS a) r).restrictScalars O

def preEig (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  (Fil.restrictScalars O).comap (mulR a N (lin a τ))

def filKer (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  Fil.restrictScalars O ⊓ LinearMap.ker (mulR a N (cofac a τ))

end GlobalTheory.HermitianPreEigenvalues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperations
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.add {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ + g τ) (fun n => a n + b n) := by
  intro τ
  simpa only [add_mul] using (hf τ).add (hg τ)

theorem HasQ.sub {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ - g τ) (fun n => a n - b n) := by
  intro τ
  simpa only [sub_mul] using (hf τ).sub (hg τ)

theorem HasQ.const_mul {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (c : ℂ) (hf : HasQ N f a) :
    HasQ N (fun τ => c * f τ) (fun n => c * a n) := by
  intro τ
  simpa only [mul_assoc] using (hf τ).mul_left c

theorem HasQ.const (N : ℕ) (c : ℂ) :
    HasQ N (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro τ
  have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0
    (fun m hm => by simp [hm])
  simpa using h

theorem HasQ.sum {N : ℕ} {κ : Type*} (s : Finset κ) {f : κ → ℍ → ℂ} {a : κ → ℕ → ℂ}
    (h : ∀ k ∈ s, HasQ N (f k) (a k)) :
    HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n) := by
  intro τ
  simpa only [Finset.sum_mul] using hasSum_sum fun k hk => h k hk τ

theorem hasQ_linear : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  intro N
  exact ⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg,
    fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperationsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_linear_operations : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  first | exact @GlobalTheory.QFam.hasQ_linear | exact GlobalTheory.QFam.hasQ_linear | (intros; apply GlobalTheory.QFam.hasQ_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_isDomain_isIntegrallyClosed :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A]
      [Algebra.Etale R A] (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro R A _ _ _ _ _ _ p _
  exact isDomain_and_isIntegrallyClosed_atPrime_of_etale R p (Localization.AtPrime p)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SmoothNormal

theorem isNormalScheme_of_smoothOfRelativeDimension :
    ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n π],
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y := by
  intro B Y _ π n _ hB
  have : Smooth π := SmoothOfRelativeDimension.smooth n π
  exact GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth π hB

end GlobalTheory.SmoothNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

def LiftIn {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (f : R) (V : X.left.Opens) : Prop :=
  ∃ e : Sp (Localization.Away f) ⟶ X.left,
    e ≫ X.hom = spMap (algebraMap R (Localization.Away f)) ∧
    spMap (Localization.awayMap π f) ≫ e = spMap (algebraMap R₀ (Localization.Away (π f))) ≫ g₀ ∧
    e ⁻¹ᵁ V = ⊤

end GlobalTheory.SecLift
end
