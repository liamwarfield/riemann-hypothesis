module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DpDual

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure HD (m n : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ)
    (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ) : Prop where
  ιc : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 m 0 e y'
  hU : IsOpen U
  hR : GlobalTheory.Cont.IsRightDomain U
  hs : s₀ ∈ U
  hol : ∀ g, DifferentiableOn ℂ (Ê · g) U
  cont : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)
  far : ∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
      ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
    ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g

def ιK (n : ℕ) : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)

def resG {G : Type} [Group G] (ι : GR n →* G) (F : G → ℂ) (g : G) : M2 n → ℂ := lift fun y => F (g * ι y)

def FarId : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → SecFz →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (Q : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ρ : Fin N → KR n → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ)
      (a b : Fin N → M2 n) (D : ℂ → ℂ) (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) → (∀ l, IsSingTest (ψ l)) →
      (∀ l, InG (a l) ∧ InG (b l)) → Differentiable ℂ D → (∀ l, Differentiable ℂ (M l)) →
      (∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (fz m e z) x) →
      (∃ t' : ℝ, ∀ z : ℂ, t' < z.re → ∀ (g : G) (y : GR n),
        D (z - s₀) * rC (lowQ Q) (resG ι (Ê z) g) (mR y) =
          ∑ l, M l (z - s₀) * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y)) ∧
      ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k

def SmoothX : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → ∀ g : G,
    ∃ (Φ : ℂ → M2 n → ℂ) (Ω : Set (M2 n)) (c : ℂ → ℂ), IsOpen Ω ∧ GSet n ⊆ Ω ∧ DifferentiableOn ℂ c U ∧ c s₀ ≠ 0 ∧
      (∀ z ∈ U, ∀ y : GR n, Φ z (mR y) = c z * Ê z (g * ι y)) ∧
      (∀ z ∈ U, ContDiffOn ℝ ∞ (Φ z) Ω) ∧
      (∀ r : ℕ, ContDiffOn ℝ ∞ (fun x => iteratedDeriv r (Φ · x) s₀) Ω) ∧
      (∀ x ∈ Ω, DifferentiableOn ℂ (Φ · x) U) ∧
      ∀ (Q : Matrix (Fin n) (Fin n) ℂ) (y : GR n),
        DifferentiableOn ℂ (fun z => rC (lowQ Q) (Φ z) (mR y)) U ∧
        ∀ r : ℕ, iteratedDeriv r (fun z => rC (lowQ Q) (Φ z) (mR y)) s₀ =
          rC (lowQ Q) (fun x => iteratedDeriv r (Φ · x) s₀) (mR y)

def TopHol : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (ρ : KR n → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n), Continuous ρ → Continuous ψ → HasCompactSupport ψ →
      InG a → InG b → ∀ (g : G) (y : GR n),
      DifferentiableOn ℂ (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) s₀ =
        tOp μ (ιK n) ρ ψ a b (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y)

def RcCongr : Prop :=
  ∀ (n : ℕ) (F F' : M2 n → ℂ) (Z : M2 n) (x : M2 n), InG x → (∀ x', InG x' → F x' = F' x') →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) → rC Z F x = rC Z F' x

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def zOfE (x : M2 n) : Matrix (Fin n) (Fin n) ℂ := (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹

def LocSec : Prop :=
  ∀ (n : ℕ) (Z₀ : Matrix (Fin n) (Fin n) ℂ), ((-(Complex.I / 2)) • (Z₀ - Z₀ᴴ)).PosDef →
    ∃ s : Matrix (Fin n) (Fin n) ℂ → M2 n, (∀ᶠ Z in 𝓝 Z₀, InG (s Z) ∧ (s Z).det ≠ 0 ∧ zOfE (s Z) = Z) ∧
      ContDiffAt ℝ 1 s Z₀

def Fib : Prop :=
  ∀ (n : ℕ) (y y' : GR n), zOfE (mR y) = zOfE (mR y') → InK (mR (y⁻¹ * y'))

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem inverse_first_block_eq_adjoint {x : M2 n} (hx : InG x) : ub1 x = (u1 x)ᴴ := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  have hl : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by simp only [Matrix.mul_assoc]
    rw [neg_mul, e, hx', hJ, neg_neg]
  rw [ub1, Matrix.inv_eq_left_inv hl, u1]
  rw [← fromBlocks_toBlocks x]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp
  abel

theorem secFz : SecFz := by
  intro n m e w y
  have hg : InG (mR y) := y.2
  have key : ∀ r : ℝ, 0 ≤ r → ((r⁻¹ : ℝ) : ℂ) ^ w = (r : ℂ) ^ (-w) := by
    intro r hr
    rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
    rw [Complex.arg_ofReal_of_nonneg hr]
    exact Real.pi_ne_zero.symm
  simp only [fz, F0, f0, hLoc, inverse_first_block_eq_adjoint hg, det_conjTranspose]
  rw [key _ (by positivity), Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionUnipotentInvariant
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem upper_left_block_mul (M N : M2 n) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem upper_right_block_mul (M N : M2 n) : (M * N).toBlocks₁₂ = M.toBlocks₁₁ * N.toBlocks₁₂ + M.toBlocks₁₂ * N.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₂, Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type]

theorem det_mR_ne (y : GR n) : (mR y).det ≠ 0 := by
  have h : IsUnit (mR y) := (y.1).isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem isUnit_first_cayley_block (y : GR n) : IsUnit (u1 (mR y)) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (detU1 n y).1)

theorem spherical_section_ne_zero_group (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y ≠ 0 := by
  have h1 := det_mR_ne y
  obtain ⟨h2, h3⟩ := detU1 n y
  simp only [F0, f0]
  exact mul_ne_zero (zpow_ne_zero _ h1) (mul_ne_zero (zpow_ne_zero _ h2) (zpow_ne_zero _ h3))

theorem zOf_nU' (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) : zOf (x * y) = zOf y + h := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hU := isUnit_first_cayley_block y
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [nU, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.one_mul]
  have key : (Complex.I • ((mR y).toBlocks₁₁ + h * (mR y).toBlocks₂₁) + ((mR y).toBlocks₁₂ + h * (mR y).toBlocks₂₂)) =
      (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₁₂) + h * u1 (mR y) := by
    simp only [u1, Matrix.mul_add, Matrix.mul_smul, smul_add]
    abel
  rw [key, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
    Matrix.mul_one]

theorem spherical_section_unipotent_invariant (p q : ℕ) (e : ℤ) (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = nU h) :
    F0 p q e (x * y) = F0 p q e y := by
  have hm : mR (x * y) = nU h * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hu2 : u2 (mR (x * y)) = u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, nU, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.one_mul]
  have hd : (mR (x * y)).det = (mR y).det := by
    rw [hm, Matrix.det_mul, nU, Matrix.det_fromBlocks_zero₂₁]
    simp
  simp only [F0, f0, hu1, hu2, hd]

theorem levi_inv (a a' : Matrix (Fin n) (Fin n) ℂ) (x : GR n) (hx : mR x = fromBlocks a 0 0 a') : aᴴ * a' = 1 := by
  obtain ⟨-, E2, -⟩ := IwaPf.inG_blocks (mR x) x.2
  rw [hx] at E2
  simpa using E2

theorem zOf_levi' (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    zOf (x * y) = a * zOf y * aᴴ := by
  have hinv := levi_inv a a' x hx
  have ha' : a'⁻¹ = aᴴ := Matrix.inv_eq_left_inv hinv
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  unfold zOf
  rw [hu, hm, upper_left_block_mul, upper_right_block_mul]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.zero_mul, add_zero]
  rw [Matrix.mul_inv_rev, ha']
  simp only [← Matrix.mul_smul, ← Matrix.mul_add, Matrix.mul_assoc]

theorem spherical_section_levi_mul (p q : ℕ) (e : ℤ) (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n) (hx : mR x = fromBlocks a 0 0 a') :
    F0 p q e (x * y) = F0 p q e x * F0 p q e y := by
  have hm : mR (x * y) = fromBlocks a 0 0 a' * mR y := by rw [mR_mul, hx]
  have hu1 : u1 (mR (x * y)) = a' * u1 (mR y) := by
    simp only [u1, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul]
  have hu2 : u2 (mR (x * y)) = a' * u2 (mR y) := by
    simp only [u2, hm, projected_block_lower_sum, lowerDiagonalBlockAsGL, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
      Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]
  have hx1 : u1 (mR x) = a' := by simp [u1, hx]
  have hx2 : u2 (mR x) = a' := by simp [u2, hx]
  have hd : (mR (x * y)).det = (mR x).det * (mR y).det := by rw [mR_mul, Matrix.det_mul]
  simp only [F0, f0, hu1, hu2, hx1, hx2, hd, Matrix.det_mul, mul_zpow]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end
