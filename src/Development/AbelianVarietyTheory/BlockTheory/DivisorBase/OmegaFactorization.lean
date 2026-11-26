module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable (F : Type) [Field F] [NumberField F]

abbrev Emb : Type := F →+* ℝ

abbrev Frac : Type := (FractionalIdeal (𝓞 F)⁰ F)ˣ

def upperHalf : Set (Emb F → ℂ) := {z | ∀ τ, 0 < (z τ).im}

def dF : ℝ := |(discr F : ℝ)|

variable {F}

def latM (𝔞 : Frac F) : FractionalIdeal (𝓞 F)⁰ F :=
  ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (↑𝔞⁻¹ : FractionalIdeal (𝓞 F)⁰ F)

def nrm (𝔞 : Frac F) : ℝ := (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℝ)


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 =
      FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv,
    Units.val_inv_eq_inv_val]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul (ε : (𝓞 F)ˣ) :
    (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((ε : 𝓞 F) : F) = 1 := by
  norm_cast; simp

def latPt (z : Emb F → ℂ) (p : F × F) : Emb F → ℂ :=
  fun τ => 2 * (Real.pi : ℂ) * I * ((τ p.1 : ℂ) + (τ p.2 : ℂ) * z τ)

def LatPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ latM 𝔞 ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ p ≠ 0}

def latRel (𝔞 𝔟 : Frac F) : Setoid (LatPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, ← mul_assoc, unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }

def eisTerm (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (∏ τ, latPt z p τ)⁻¹ ^ k * ((‖∏ τ, latPt z p τ‖ : ℝ) : ℂ) ^ (-2 * σ)

def eisClass (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (c : Quotient (latRel 𝔞 𝔟)) : ℂ :=
  eisTerm k σ z c.out.1

def eisSum (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) : ℂ := ∑' c, eisClass 𝔞 𝔟 k σ z c

def QPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧
    ∀ τ : Emb F, 0 < τ (p.1 * p.2)}

def qRel (𝔞 𝔟 : Frac F) : Setoid (QPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, inv_inv, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc, mul_inv]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }

def qPow (ξ : F) (z : Emb F → ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ ξ : ℂ) * z τ)

def qTerm (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (((|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) : ℝ) : ℂ) * qPow (p.1 * p.2) z

def qClass (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ℂ := qTerm 𝔞 k z c.out.1

def IsPartialZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)

def cK (F : Type) [Field F] [NumberField F] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ (((k : ℝ) - 1) / 2)

def omegaFactor (𝔞 : Frac F) : ℝ := dF F ^ ((1 : ℝ) / 2) * nrm 𝔞

def HasExpansion (𝔞 𝔟 : Frac F) (k : ℕ) (g : (Emb F → ℂ) → ℂ) : Prop :=
  ∃ Z : ℂ → ℂ, IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ ∀ z ∈ upperHalf F,
    Summable (qClass 𝔞 𝔟 k z) ∧
      (cK F k : ℂ) * g z / (omegaFactor 𝔞 : ℂ) ^ k =
        (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) + ∑' c, qClass 𝔞 𝔟 k z c


open Classical in
def wirt {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ := by
  classical
  exact fun z =>
    (fderiv ℝ g z (Pi.single τ 1) + (if bar then I else -I) * fderiv ℝ g z (Pi.single τ I)) / 2

def wirtWord {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ := by
  classical
  exact ws.foldr (fun w h => wirt w.1 w.2 h) g

theorem wirtWord_nil {Φ : Type} [Fintype Φ] (g : (Φ → ℂ) → ℂ) : wirtWord [] g = g := rfl

theorem wirtWord_cons {Φ : Type} [Fintype Φ] (w : Φ × Bool) (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) :
    wirtWord (w :: ws) g = wirt w.1 w.2 (wirtWord ws g) := rfl

def halfPlane : Set ℂ := {σ | -1 / 2 < σ.re}

def IsContinuation (𝔞 𝔟 : Frac F) (G : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ : ℂ, 0 < σ.re → ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 2 σ z) ∧ G σ z = eisSum 𝔞 𝔟 2 σ z) ∧
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (G σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) z) halfPlane)

def HeckeWeightTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ 𝔞 𝔟 : Frac F,
    ∃ G : ℂ → (Emb F → ℂ) → ℂ, IsContinuation 𝔞 𝔟 G ∧
      DifferentiableOn ℂ (G 0) (upperHalf F) ∧ HasExpansion 𝔞 𝔟 2 (G 0)


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb [IsTotallyReal F] (x : F) :
    ∏ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((τ x : ℝ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h1
  rw [h1]
  have h2 : ∏ σ : F →ₐ[ℚ] ℂ, σ x = ∏ φ : F →+* ℂ, φ x :=
    Fintype.prod_bijective (fun σ : F →ₐ[ℚ] ℂ => (σ : F →+* ℂ))
      (RingHom.equivRatAlgHom F ℂ).symm.bijective _ _ (fun _ => rfl)
  have h3 : ∏ τ : F →+* ℝ, ((τ x : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ x := by
    refine Fintype.prod_bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨?_, ?_⟩ _ _
      (fun _ => rfl)
    · intro a b h
      ext y
      have := congrArg (fun f : F →+* ℂ => f y) h
      simpa using this
    · intro φ
      have hφ : ComplexEmbedding.IsReal φ :=
        InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
      exact ⟨hφ.embedding, by ext y; simp [ComplexEmbedding.IsReal.coe_embedding_apply]⟩
  rw [h2, h3]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit [IsTotallyReal F] {k : ℕ} (hk : Even k)
    (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (ε : (𝓞 F)ˣ) (a b : F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z (a, b) := by
  have hprod : ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) τ =
      ((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℂ) * ∏ τ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z (a, b) τ := by
    rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt, map_mul]
    push_cast
    ring
  have hn : |Algebra.norm ℚ ((ε : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm
  rw [hprod]
  rcases (abs_eq zero_le_one).mp hn with h | h <;> rw [h] <;>
    simp [hk.neg_pow, inv_neg, norm_neg]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass_mk [IsTotallyReal F] (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F)
    {k : ℕ} (hk : Even k) (σ : ℂ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ)
    (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.LatPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 k σ z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k σ z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hp : p.1 = (((ε : 𝓞 F) : F) * q.1.1, ((ε : 𝓞 F) : F) * q.1.2) := Prod.ext h1 h2
  rw [hp, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm_unit hk]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass_mk (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ)
    (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ) (p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.QPair 𝔞 𝔟) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 k z (Quotient.mk _ p) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z p.1 := by
  have hrel := Quotient.mk_out (s := _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass
  generalize (Quotient.mk (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qRel 𝔞 𝔟) p).out = q at hrel ⊢
  obtain ⟨ε, h1, h2⟩ := hrel
  have hu : |Algebra.norm ℚ (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)| = 1 := NumberField.Units.norm F ε⁻¹
  have hmul : p.1.1 * p.1.2 = q.1.1 * q.1.2 := by
    rw [h1, h2, mul_mul_mul_comm, _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]
  have hn : |((Algebra.norm ℚ p.1.1 : ℚ) : ℝ)| = |((Algebra.norm ℚ q.1.1 : ℚ) : ℝ)| := by
    rw [h1, map_mul, Rat.cast_mul, abs_mul, ← Rat.cast_abs, hu, Rat.cast_one, one_mul]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm
  rw [hn, hmul]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt_ne_zero {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) {p : F × F} (hp : p ≠ 0) (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latPt z p τ ≠ 0 := by
  intro h
  have h2 : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rcases mul_eq_zero.mp h with h' | h'
  · exact h2 h'
  · by_cases hb : p.2 = 0
    · have ha : p.1 ≠ 0 := fun ha => hp (Prod.ext ha hb)
      rw [hb, map_zero] at h'
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_eq_zero,
        map_eq_zero] at h'
      exact ha h'
    · have him := congrArg Complex.im h'
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        zero_mul, add_zero, zero_add, Complex.zero_im] at him
      rcases mul_eq_zero.mp him with h1 | h1
      · exact hb ((map_eq_zero τ).mp h1)
      · exact (hz τ).ne' h1

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
open Polynomial Module

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

variable {C : Type} [Field C]

abbrev Int0 (v : AddValuation C (WithTop ℝ)) : Subring C :=
  (AddValuation.toValuation v).integer

theorem mem_addValuationIntegerRing_iff (v : AddValuation C (WithTop ℝ)) (x : C) : x ∈ Int0 v ↔ 0 ≤ v x := Iff.rfl

def RelLen (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M] [Module (Int0 v) M]
    (X' X : Submodule (Int0 v) M) (r : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
    (A : Matrix (Fin n) (Fin n) (Int0 v)),
    (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) ∧ v (A.det : C) = (r : WithTop ℝ)

section Ring

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

abbrev RS (a : S → O) : Type := AdjoinRoot (∏ s, (X - Polynomial.C (a s)) : O[X])

def lin (a : S → O) (s : S) : RS a := AdjoinRoot.root _ - algebraMap O (RS a) (a s)

def cofac (a : S → O) (τ : S) : RS a := ∏ s ∈ Finset.univ.erase τ, lin a s

def ev (a : S → O) (s : S) : RS a →ₐ[O] O :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id O O) (a s) (by
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp))

def comp (a : S → O) (N : ℕ) (s : S) : (Fin N → RS a) →ₗ[O] (Fin N → O) :=
  (ev a s).toLinearMap.compLeft (Fin N)

def kerMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.ker (LinearMap.lsmul (RS a) M r)).restrictScalars O

def imMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.range (LinearMap.lsmul (RS a) M r)).restrictScalars O

def eigSub (a : S → O) (τ : S) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  kerMul a (lin a τ) M

def eigQuot (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) (s : S) :
    Submodule O (Fin N → O) :=
  (X.restrictScalars O).map (comp a N s)

def incl (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) : X →ₗ[O] (Fin N → RS a) :=
  X.subtype.restrictScalars O

def proj (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) :
    (Fin N → RS a) →ₗ[O] ((Fin N → RS a) ⧸ X) :=
  X.mkQ.restrictScalars O

theorem ev_lin (a : S → O) (s t : S) : ev a s (lin a t) = a s - a t := by
  simp [ev, lin]

end Ring

variable {S : Type} [Fintype S] [DecidableEq S]

def eigRank (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (X : Submodule (RS a) (Fin N → RS a)) (s : S) : ℕ :=
  finrank C (Submodule.span C
    ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (eigQuot a X s : Set (Fin N → Int0 v))))

def vd (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) (τ : S) : WithTop ℝ :=
  v (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)))

def yExp (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : WithTop ℝ :=
  ∑ s ∈ Finset.univ.erase τ, eigRank v a Fil s • v ((a s : C) - (a τ : C))

def DetIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ p : ℕ, p + eigRank v a Fil τ = N ∧
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) ∧
    Nonempty (Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))) ∧
    Nonempty (Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ)) ∧
    ∀ (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
      (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
      (x : Fin p → (Fin N → RS a))
      (_ : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
      (f : Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ))
      (e : Fin N ≃ Fin p ⊕ Fin (eigRank v a Fil τ)),
      ∃ c : C, v c = yExp v a Fil τ ∧
        (Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
        ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
          c * ((Matrix.of fun k : Fin N =>
            Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C)

def KernelIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  (eigSub a τ (Fin N → RS a)).map (proj a Fil) ≤ eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧
  eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (proj a Fil) = (eigSub a τ Fil).map (incl a Fil)

def LengthIdentities (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ δ e₂ m : ℝ,
    RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ ∧
    RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ ∧
    RelLen v (imMul a (cofac a τ) Fil) (eigSub a τ Fil) e₂ ∧
    RelLen v ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) (eigQuot a Fil τ) m ∧
    ((m + e₂ : ℝ) : WithTop ℝ) = eigRank v a Fil τ • vd v a τ ∧
    ((∀ s, eigRank v a Fil s = eigRank v a Fil τ) →
      0 ≤ δ ∧ (δ : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ ∧
      0 ≤ m ∧ (m : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ)

def HerbrandDet : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, DetIdentity v a Fil τ ∧ KernelIdentity v a Fil τ ∧ LengthIdentities v a Fil τ

theorem v_unit (v : AddValuation C (WithTop ℝ)) {u : Int0 v} (hu : IsUnit u) : v (u : C) = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : v (u : C) + v (w : C) = 0 := by
    rw [← v.map_mul, ← Subring.coe_mul, hw]; simp
  have hu0 : 0 ≤ v (u : C) := u.2
  have hw0 : 0 ≤ v (w : C) := w.2
  refine le_antisymm ?_ hu0
  calc v (u : C) ≤ v (u : C) + v (w : C) := le_add_of_nonneg_right hw0
    _ = 0 := h1

theorem RelLen.unique (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
    [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r r' : ℝ}
    (h : RelLen v X' X r) (h' : RelLen v X' X r') : r = r' := by
  obtain ⟨n, b, b', A, hA, hr⟩ := h
  obtain ⟨m, c, c', B, hB, hr'⟩ := h'
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hnm
  have hle : X' ≤ X := by
    intro x hx
    have : (x : M) = ∑ k, b'.repr ⟨x, hx⟩ k • (b' k : M) := by
      have := congrArg X'.subtype (b'.sum_repr ⟨x, hx⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    rw [this]
    refine X.sum_mem fun k _ => X.smul_mem _ ?_
    rw [hA k]
    exact X.sum_mem fun i _ => X.smul_mem _ (b i).2
  have key : ∀ (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
      (A : Matrix (Fin n) (Fin n) (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have : v (A.det : C) = v (B.det : C) := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
      v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]
  rw [hr, hr'] at this
  exact_mod_cast this

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
open scoped NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

noncomputable section Defs

variable {C : Type} [Field C] (w : Valuation C ℝ≥0)

noncomputable def addVal (ℓ c : C) : ℝ := Real.log (w c : ℝ) / Real.log (w ℓ : ℝ)

def HasVal (ℓ c : C) (y : ℝ) : Prop := c ≠ 0 ∧ addVal w ℓ c = y

def IsLatticeBasis {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (x : Fin n → W)
    (X : Submodule w.valuationSubring W) : Prop :=
  LinearIndependent C x ∧ Submodule.span w.valuationSubring (Set.range x) = X

def HasLength (ℓ : C) {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] (X X' : Submodule w.valuationSubring W) (t : ℝ) :
    Prop :=
  X' ≤ X ∧ ∃ (n : ℕ) (x x' : Fin n → W) (M : Matrix (Fin n) (Fin n) C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w x' X' ∧ (∀ i, x' i = ∑ j, M i j • x j) ∧
      HasVal w ℓ M.det t

def DetRel (ℓ : C) {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (X : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) : Prop :=
  ∃ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C)
    (m : Fin q → Fin (p + q) → C) (c : C),
    IsLatticeBasis w x X ∧ IsLatticeBasis w (fun i => F.mkQ (u i)) L ∧ IsLatticeBasis w m M ∧
      (∀ i, m i ∈ F) ∧ HasVal w ℓ c y ∧
      (Matrix.of x).det = c * (Matrix.of (Fin.append u m)).det

variable {w}

def eigenSub {S : Type} [DecidableEq S] {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.comap (LinearMap.single w.valuationSubring W τ)

def eigenQuot {S : Type} {W : S → Type} [∀ s, AddCommGroup (W s)]
    [∀ s, Module w.valuationSubring (W s)] (X : Submodule w.valuationSubring (∀ s, W s))
    (τ : S) : Submodule w.valuationSubring (W τ) :=
  X.map (LinearMap.proj τ)

def freeLattice {S : Type} (a : S → w.valuationSubring) (r : ℕ) :
    Submodule w.valuationSubring (S → Fin r → C) where
  carrier := {x | ∀ i, ∃ f : Polynomial w.valuationSubring, ∀ s,
    x s i = ((f.eval (a s) : w.valuationSubring) : C)}
  zero_mem' := fun _ => ⟨0, fun _ => by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨f, hf⟩ := hx i
    obtain ⟨g, hg⟩ := hy i
    exact ⟨f + g, fun s => by simp [hf s, hg s]⟩
  smul_mem' := by
    intro c x hx i
    obtain ⟨f, hf⟩ := hx i
    exact ⟨Polynomial.C c * f, fun s => by simp [hf s, Algebra.smul_def]⟩

def unif {S : Type} {r : ℕ} (a : S → w.valuationSubring) (x : S → Fin r → C) :
    S → Fin r → C := fun s => (a s : C) • x s

def filSpace {S : Type} {r : ℕ} (Fil : Submodule w.valuationSubring (S → Fin r → C)) (s : S) :
    Submodule C (Fin r → C) :=
  Submodule.span C (eigenQuot (W := fun _ => Fin r → C) Fil s : Set (Fin r → C))

def quotMap {r : ℕ} (F : Submodule C (Fin r → C)) :
    (Fin r → C) →ₗ[w.valuationSubring] ((Fin r → C) ⧸ F) :=
  F.mkQ.restrictScalars w.valuationSubring

def lie {S : Type} {r : ℕ} (H Fil : Submodule w.valuationSubring (S → Fin r → C)) :
    Submodule w.valuationSubring (∀ s, (Fin r → C) ⧸ filSpace Fil s) :=
  H.map (LinearMap.pi fun s => quotMap (filSpace Fil s) ∘ₗ LinearMap.proj s)

def dualLie {S : Type} [DecidableEq S] {r : ℕ}
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil H' Fil' : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) :
    Submodule w.valuationSubring (Fin r → C) where
  carrier := {x | x ∈ filSpace Fil τ ∧ ∀ y : Fin r → C,
    (filSpace Fil' τ).mkQ y ∈ eigenSub (lie H' Fil') τ →
      β (Pi.single τ x) (Pi.single τ y) ∈ w.valuationSubring}
  zero_mem' := ⟨zero_mem _, fun y _ => by simp⟩
  add_mem' := by
    rintro x x' ⟨hx, h⟩ ⟨hx', h'⟩
    refine ⟨add_mem hx hx', fun y hy => ?_⟩
    rw [Pi.single_add, map_add (f := _), LinearMap.add_apply]
    exact add_mem (h y hy) (h' y hy)
  smul_mem' := by
    rintro c x ⟨hx, h⟩
    refine ⟨Submodule.smul_mem _ (c : C) hx, fun y hy => ?_⟩
    have : (Pi.single τ (c • x) : S → Fin r → C) = (c : C) • (Pi.single τ x : S → Fin r → C) :=
      Pi.single_smul' τ (c : C) x
    rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_mem c.2 (h y hy)

structure IsFiltration {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  le : Fil ≤ freeLattice a r
  stable : ∀ x ∈ Fil, unif a x ∈ Fil
  saturated : ∀ x ∈ freeLattice a r, ∀ c : w.valuationSubring, c ≠ 0 → c • x ∈ Fil → x ∈ Fil

structure IsDualDatum {S : Type} {r : ℕ} (a : S → w.valuationSubring)
    (β : (S → Fin r → C) →ₗ[C] (S → Fin r → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin r → C)) : Prop where
  fil : IsFiltration a Fil
  fil' : IsFiltration a Fil'
  adjoint : ∀ x y, β (unif a x) y = β x (unif a y)
  perfect_left : ∀ x, x ∈ freeLattice a r ↔
    ∀ y ∈ freeLattice a r, β x y ∈ w.valuationSubring
  perfect_right : ∀ y, y ∈ freeLattice a r ↔
    ∀ x ∈ freeLattice a r, β x y ∈ w.valuationSubring
  ann_left : ∀ x ∈ freeLattice a r, (x ∈ Fil ↔ ∀ y ∈ Fil', β x y = 0)
  ann_right : ∀ y ∈ freeLattice a r, (y ∈ Fil' ↔ ∀ x ∈ Fil, β x y = 0)

def diffGen {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (τ : S) :
    w.valuationSubring := ∏ s ∈ Finset.univ.erase τ, (a τ - a s)

def flatLattice {S : Type} {r : ℕ} (a : S → w.valuationSubring) (τ : S)
    (d : w.valuationSubring) : Submodule w.valuationSubring (Fin r → C) :=
  (eigenQuot (W := fun _ => Fin r → C) (freeLattice a r) τ).map
    (LinearMap.lsmul w.valuationSubring (Fin r → C) d)

end Defs

section Stmt

variable {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)

def TypeOne : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    Function.Injective a → IsDualDatum a β Fil Fil' →
    (∀ s, Module.finrank C (filSpace Fil s) = q) →
    let H := freeLattice a (p + q)
    let vd := addVal w ℓ (diffGen a τ : C)
    let HH := flatLattice (r := p + q) a τ (diffGen a τ)
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenSub (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      ((q : ℝ) * vd) ∧
    HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ)) = FilSub ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧
      HasLength w ℓ (eigenSub (lie H Fil) τ) (HH.map (quotMap (filSpace Fil τ)))
        ((q : ℝ) * vd - t) ∧
      0 ≤ (q : ℝ) * vd - t ∧ (q : ℝ) * vd - t ≤ (q : ℝ) * vd

def TypeTwo : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ τ' : S),
    τ ≠ τ' → (∀ s, s = τ ∨ s = τ') →
    HasVal w ℓ ((a τ : C) - (a τ' : C)) (1 / 2) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q → Module.finrank C (filSpace Fil τ') = p →
    let H := freeLattice a (p + q)
    let HH := flatLattice (r := p + q) a τ 1
    let FilSub := eigenSub (W := fun _ => Fin (p + q) → C) Fil τ
    let FilQuot := eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ
    HH = eigenQuot (W := fun _ => Fin (p + q) → C) H τ ∧
    DetRel w ℓ (filSpace Fil τ) HH (eigenSub (lie H Fil) τ) (dualLie β Fil H Fil' τ)
      (-((q : ℝ) / 2)) ∧
    HH.map (quotMap (filSpace Fil τ)) = eigenQuot (lie H Fil) τ ∧
    (∃ la : ℝ, HasLength w ℓ (eigenQuot (lie H Fil) τ) (eigenSub (lie H Fil) τ) la ∧
      0 ≤ la ∧ la ≤ (q : ℝ) / 2 ∧
      HasLength w ℓ (HH ⊓ LinearMap.ker (quotMap (filSpace Fil τ))) FilQuot
        ((q : ℝ) / 2 - la)) ∧
    ∃ t : ℝ, HasLength w ℓ FilQuot FilSub t ∧ t ≤ (q : ℝ) / 2

def Unramified : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (β : (S → Fin (p + q) → C) →ₗ[C] (S → Fin (p + q) → C) →ₗ[C] C)
    (Fil Fil' : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S),
    (∀ s, s = τ) → IsDualDatum a β Fil Fil' →
    Module.finrank C (filSpace Fil τ) = q →
    let H := freeLattice a (p + q)
    DetRel w ℓ (filSpace Fil τ) (flatLattice (r := p + q) a τ 1) (eigenSub (lie H Fil) τ)
      (dualLie β Fil H Fil' τ) 0

def ValuedFieldThreeCases : Prop := TypeOne w ℓ ∧ TypeTwo w ℓ ∧ Unramified w ℓ

end Stmt

def Stmt : Prop :=
  ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ValuedFieldThreeCases w ℓ

noncomputable section Example

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

end Example

end GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

def traceDual (M : FractionalIdeal (𝓞 F)⁰ F) : Set F :=
  {y | ∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n}

def covol (M : FractionalIdeal (𝓞 F)⁰ F) : ℝ :=
  Real.sqrt |(discr F : ℝ)| * (FractionalIdeal.absNorm M : ℝ)

def dualCone (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) : Set F :=
  {ν | ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν}

def lhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (a : F) : ℂ :=
  (∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ))) ^ (-(k : ℤ))

def rhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) : ℂ :=
  ((|∏ τ : F →+* ℝ, τ ν| ^ (k - 1) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * z τ)

def lipConst (k : ℕ) (M : FractionalIdeal (𝓞 F)⁰ F) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (k * Module.finrank ℚ F) /
    ((((k - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * (covol M : ℂ))

def Lipschitz : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
    ∀ (k : ℕ), 2 ≤ k → Even k →
    ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
      Summable (fun a : (M : Set F) => lhsTerm k z a) ∧
      Summable (fun ν : dualCone M z => rhsTerm k z ν) ∧
      ∑' a : (M : Set F), lhsTerm k z a = lipConst k M * ∑' ν : dualCone M z, rhsTerm k z ν


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by
  change (∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) ↔ _
  rw [FractionalIdeal.mem_dual hM]
  refine forall₂_congr fun a _ => ?_
  simp [Algebra.traceForm_apply, eq_comm]


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by
  refine mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))) ?_
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg M)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.2 hM))


open scoped Classical in
variable {F : Type} [Field F] [NumberField F] in
open Classical in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (E := mixedEmbedding.mixedSpace F)
        (mixedEmbedding.idealLattice F M) MeasureTheory.volume := by
  rw [mixedEmbedding.covolume_idealLattice, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
    mul_one, mul_comm]
  rfl


theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  classical
  rw [IsTotallyReal.finrank, ← InfinitePlace.card_real_embeddings]
  convert Fintype.card_congr
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, ?_⟩
      invFun := fun φ => φ.2.embedding
      left_inv := ?_
      right_inv := ?_ : (F →+* ℝ) ≃ { φ : F →+* ℂ // ComplexEmbedding.IsReal φ } }
  · rw [ComplexEmbedding.isReal_iff]; ext x; simp [ComplexEmbedding.conjugate]
  · intro φ; ext x
    simpa using ComplexEmbedding.IsReal.coe_embedding_apply (φ := Complex.ofRealHom.comp φ) _ x
  · intro φ; ext x; simp [ComplexEmbedding.IsReal.coe_embedding_apply]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end
end
