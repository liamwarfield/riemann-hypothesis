module

public import ReciprocityTheory.AnalyticForms.MaIntEmpty

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ}

def IsPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  UpperSemicontinuousOn φ U ∧
    ∀ z w : Fin D → ℂ, (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ U) →
      CircleIntegrable (fun ζ : ℂ => φ (z + ζ • w)) 0 1 ∧
        φ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w)) 0 1

def IsLeviPsh (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ 2 φ U ∧ ∀ z ∈ U, ∀ w : Fin D → ℂ, 0 ≤ levi φ z w

def IsPsh_iff_isLeviPshStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U →
    (IsPsh U φ ↔ IsLeviPsh U φ)

def IsPsh_locallyIntegrableStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ), IsOpen U → IsPsh U φ →
    LocallyIntegrableOn φ U volume

def IsPsh_supStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → (∀ j, IsPsh U (u j)) →
    IsPsh U (fun z => Finset.univ.sup' Finset.univ_nonempty (fun j => u j z))

def SubMeanPolydiscStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ),
    IsOpen U → IsPsh U φ → 0 < t → closedBall z t ⊆ U →
    IntegrableOn φ (closedBall z t) volume ∧ φ z ≤ ⨍ x in closedBall z t, φ x

def coordDiv (S : Finset (Fin D)) : Set (Fin D → ℂ) :=
  {z | ∃ i ∈ S, z i = 0}


open Classical in
def limsupExt (U A : Set (Fin D → ℂ)) (v : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  by
    classical
    exact if z ∈ A then limsup v (𝓝[U \ A] z) else v z

def PshExtensionStatement : Prop :=
  ∀ (D : ℕ) (S : Finset (Fin D)) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (C : ℝ),
    IsOpen U → U ⊆ ball 0 1 → ContinuousOn u (U \ coordDiv S) → IsPsh (U \ coordDiv S) u →
    (∀ z ∈ U \ coordDiv S, u z ≤ C * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹)) →
    (∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → BddAbove (u '' (K \ coordDiv S))) ∧
      ∀ κ : ℝ, IsPsh U (limsupExt U (coordDiv S) (fun z => max (u z) (-κ)))

def polyMax (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' closedBall z t)

def PolyMaxLogConvexStatement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (R : ℝ),
    IsOpen U → IsPsh U φ → 0 < R → closedBall z R ⊆ U →
    ConvexOn ℝ (Set.Iic (Real.log R)) (fun s => polyMax φ z (Real.exp s)) ∧
      MonotoneOn (polyMax φ z) (Set.Ioc 0 R) ∧
      (∀ t, 0 ≤ t → t ≤ R → ∃ x ∈ closedBall z t, φ x = polyMax φ z t) ∧
      Tendsto (polyMax φ z) (𝓝[>] 0) (𝓝 (φ z))

structure Mollifier (D : ℕ) where

  toFun : (Fin D → ℂ) → ℝ
  contDiff : ContDiff ℝ ∞ toFun
  nonneg : ∀ w, 0 ≤ toFun w
  support_subset : Function.support toFun ⊆ ball 0 1
  integral_eq_one : ∫ w, toFun w = 1
  circle_inv : ∀ (c : ℂ) (w : Fin D → ℂ), ‖c‖ = 1 → toFun (c • w) = toFun w

def MollifierInhabitStatement : Prop := ∀ D : ℕ, Nonempty (Mollifier D)

def Mollifier.scaled (ρ : Mollifier D) (ε : ℝ) (w : Fin D → ℂ) : ℝ :=
  (ε ^ (2 * D))⁻¹ * ρ.toFun (ε⁻¹ • w)

def molli (ρ : Mollifier D) (ε : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  ∫ w, ρ.scaled ε w * φ (z - w)

def shrink (U : Set (Fin D → ℂ)) (ε : ℝ) : Set (Fin D → ℂ) :=
  {z | closedBall z ε ⊆ U}

def MollifyStatement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → IsPsh U φ →
    (∀ ε, 0 < ε → IsOpen (shrink U ε) ∧ ContDiffOn ℝ ∞ (molli ρ ε φ) (shrink U ε) ∧
        IsPsh (shrink U ε) (molli ρ ε φ) ∧
        ∀ z ∈ shrink U ε, φ z ≤ molli ρ ε φ z ∧ molli ρ ε φ z ≤ polyMax φ z ε) ∧
      (∀ z ∈ U, Tendsto (fun ε => molli ρ ε φ z) (𝓝[>] 0) (𝓝 (φ z)))

def MollificationSecondOrder : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (U K : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ),
    IsOpen U → ContDiffOn ℝ 3 φ U → IsCompact K → K ⊆ U →
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ z ∈ K, z ∈ shrink U ε ∧
      |molli ρ ε φ z - φ z| ≤ C * ε ∧
      ‖fderiv ℝ (molli ρ ε φ) z - fderiv ℝ φ z‖ ≤ C * ε ∧
      ‖fderiv ℝ (fderiv ℝ (molli ρ ε φ)) z - fderiv ℝ (fderiv ℝ φ) z‖ ≤ C * ε

def kθ : ℝ → ℝ :=
  (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)).normed volume

def tmax {ι : Type*} [Fintype ι] [Nonempty ι] (t : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty t

def regMax {ι : Type*} [Fintype ι] [Nonempty ι] (η : ℝ) (t : ι → ℝ) : ℝ :=
  ∫ h : ι → ℝ, tmax (fun j => t j + η * h j) * ∏ j, kθ (h j)

def RegMaxStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι],
    (∀ η : ℝ, 0 < η →
      ContDiff ℝ ∞ (regMax (ι := ι) η) ∧ ConvexOn ℝ Set.univ (regMax (ι := ι) η) ∧
      Monotone (regMax (ι := ι) η) ∧
      (∀ t : ι → ℝ, tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2) ∧
      (∀ (t : ι → ℝ) i, (∀ j, j ≠ i → t j + η ≤ t i) → regMax η t = t i) ∧
      (∀ (t : ι → ℝ) j k (s : ℝ), k ≠ j → t j + η ≤ t k → s + η ≤ t k →
        regMax η (Function.update t j s) = regMax η t) ∧
      (∀ (t : ι → ℝ) (c : ℝ), regMax η (fun j => t j + c) = regMax η t + c) ∧
      (∀ t : ι → ℝ, ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1)) ∧
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ (t : ι → ℝ) (i j : ι),
      |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t (Pi.single i 1) (Pi.single j 1)| ≤ C / η

def RegMaxLeviStatement : Prop :=
  ∀ (D : ℕ) (ι : Type) [Fintype ι] [Nonempty ι] (η : ℝ) (U : Set (Fin D → ℂ))
    (u : ι → (Fin D → ℂ) → ℝ), IsOpen U → 0 < η → (∀ j, ContDiffOn ℝ 2 (u j) U) →
    ∀ z ∈ U, ∀ (w : Fin D → ℂ) (g : ℝ), (∀ j, g ≤ levi (u j) z w) →
      g ≤ levi (fun x => regMax η (fun j => u j x)) z w

end

end ReciprocityTheory.AnForm.A
end

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
namespace ReciprocityTheory.AnForm.A

open MeasureTheory
open scoped Laplacian

noncomputable section

def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Δ u z

def ddcCoordDens {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (2 / Real.pi) * ReciprocityTheory.AnForm.levi u z (Pi.single j 1)

def GreenParamFiberStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ p : E,
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z = 2 * Real.pi * u (0, p)

def GreenParamStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
        ((volume : Measure ℂ).prod μ) ∧
      ∫ q : ℂ × E, Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1 ∂((volume : Measure ℂ).prod μ)
        = 2 * Real.pi * ∫ p : E, u (0, p) ∂μ

def GreenCoordStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z j‖ * ddcCoordDens j u z =
        ∫ w : Fin D → ℂ, u (Fin.insertNth j 0 w)

def GreenMixedStatement : Prop :=
  ∀ (D : ℕ) (j a b : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    (a, b) ≠ (j, j) →
    Integrable (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) ∧
      ∫ z : Fin (D + 1) → ℂ, (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b = 0

end

end ReciprocityTheory.AnForm.A
end

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
namespace ReciprocityTheory.AnForm.A

open MeasureTheory

open scoped ContDiff

noncomputable section

def hypIncl {n : ℕ} (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons (0 : ℂ) w

theorem hypIncl_zero {n : ℕ} (w : Fin n → ℂ) : hypIncl w 0 = 0 := rfl

def PoincareLelongData {n : ℕ} (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : Prop :=
  IsOpen U ∧ ContDiff ℝ 3 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ∀ k, ContDiffOn ℝ ∞ (φ k) U

def densV {n : ℕ} (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  maDens (D := n + 1) (Fin.cons v φ) z

def densHyp {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypIncl) w

def PoincareLelongHyperplane : Prop :=
  ∀ (n : ℕ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ), PoincareLelongData U v φ →
    Integrable (fun z => Real.log ‖z 0‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypIncl w) * densHyp φ w) volume ∧
    ∫ z, Real.log ‖z 0‖ * densV v φ z = ∫ w, v (hypIncl w) * densHyp φ w

def PoincareLelongUnitPower : Prop :=
  ∀ (n : ℕ) (m : ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖z 0 ^ m * u z‖ * densV v φ z = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp φ w

def hypInclAt {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) i 0 w

def densHypAt {n : ℕ} (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypInclAt i) w

def PoincareLelongNormalCrossing : Prop :=
  ∀ (n : ℕ) (m : Fin (n + 1) → ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z =
      ∑ i, (m i : ℝ) * ∫ w, v (hypInclAt i w) * densHypAt i φ w

theorem hypInclAt_zero {n : ℕ} (w : Fin n → ℂ) : hypInclAt 0 w = hypIncl w := by
  funext j
  simp [hypInclAt, hypIncl, Fin.insertNth_zero']

end

end ReciprocityTheory.AnForm.A
end

section -- merged from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscPos
namespace ReciprocityTheory.AnForm.A

open Matrix Finset
open scoped ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def pmGmat (w : Fin D → ι → Fin D → ℂ) (g : Fin D → Fin D × ι) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun x a => w (g a).1 (g a).2 x

def pmGram (w : Fin D → ι → Fin D → ℂ) (k : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => ∑ r, w k r a * star (w k r b)

theorem pm_sum_gram_apply (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) (a b : Fin D) :
    (∑ k ∈ S, pmGram w k) a b =
      ∑ p : Fin D × ι, (if p.1 ∈ S then (1 : ℂ) else 0) * (w p.1 p.2 a * star (w p.1 p.2 b)) := by
  simp only [Matrix.sum_apply, pmGram, Matrix.of_apply, Fintype.sum_prod_type, ite_mul, one_mul,
    zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by simp [hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]

theorem pm_det_sum_gram (w : Fin D → ι → Fin D → ℂ) (S : Finset (Fin D)) :
    (∑ k ∈ S, pmGram w k).det = ∑ g : Fin D → Fin D × ι,
      (if ∀ a, (g a).1 ∈ S then (1 : ℂ) else 0) *
        ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
  simp only [det_apply, pm_sum_gram_apply]
  simp only [Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, pmGmat, Matrix.of_apply, Finset.prod_boole,
    Finset.mem_univ, true_imp_iff, Units.smul_def, zsmul_eq_mul]
  ring

theorem pm_alt (K : Finset (Fin D)) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if K ⊆ S then 1 else 0) =
      if K = univ then 1 else 0 := by
  have hc : ∀ T : Finset (Fin D), D - (D - T.card) = T.card := fun T =>
    Nat.sub_sub_self (by simpa using Finset.card_le_univ T)
  rw [← Fintype.sum_bijective (Compl.compl : Finset (Fin D) → Finset (Fin D)) compl_involutive.bijective
    (fun T : Finset (Fin D) => (-1 : ℂ) ^ T.card * if T ⊆ Kᶜ then 1 else 0) _ fun T => by
      simp only [Finset.card_compl, Fintype.card_fin, hc, Finset.subset_compl_comm]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hf : (univ.filter fun T : Finset (Fin D) => T ⊆ Kᶜ) = Kᶜ.powerset := by ext; simp
  rw [hf]
  have h := Finset.sum_powerset_neg_one_pow_card (x := Kᶜ)
  have h2 := congrArg (Int.cast : ℤ → ℂ) h
  push_cast at h2
  rw [h2]
  simp [Finset.compl_eq_empty_iff]

def pmWt (g : Fin D → Fin D × ι) : ℝ :=
  if univ.image (fun a => (g a).1) = univ then 1 else 0

theorem pmWt_nonneg (g : Fin D → Fin D × ι) : 0 ≤ pmWt g := by
  unfold pmWt; split_ifs <;> norm_num

theorem pmWt_comp_perm (g : Fin D → Fin D × ι) (τ : Equiv.Perm (Fin D)) :
    pmWt (g ∘ τ) = pmWt g := by
  unfold pmWt
  have : univ.image (fun a => ((g ∘ τ) a).1) = univ.image (fun a => (g a).1) := by
    ext x
    simp only [mem_image, mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨a, h⟩ => ⟨τ a, h⟩, fun ⟨a, h⟩ => ⟨τ.symm a, by simpa using h⟩⟩
  rw [this]

theorem pm_sum_alt (g : Fin D → Fin D × ι) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (if ∀ a, (g a).1 ∈ S then 1 else 0) =
      (pmWt g : ℂ) := by
  have h : ∀ S : Finset (Fin D), (∀ a, (g a).1 ∈ S) ↔ univ.image (fun a => (g a).1) ⊆ S := by
    intro S; simp [Finset.image_subset_iff]
  simp only [h, pm_alt, pmWt]
  split_ifs <;> simp

theorem pm_comp_bijective (τ : Equiv.Perm (Fin D)) :
    Function.Bijective (fun g : Fin D → Fin D × ι => g ∘ τ) :=
  ⟨fun g h e => by funext a; simpa using congrFun e (τ.symm a),
    fun g => ⟨g ∘ τ.symm, by funext a; simp⟩⟩

theorem pm_sum_perm_reindex (w : Fin D → ι → Fin D → ℂ) :
    (D.factorial : ℂ) * ∑ g : Fin D → Fin D × ι,
        (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) =
      ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) := by
  have hcard : (D.factorial : ℂ) = ∑ _τ : Equiv.Perm (Fin D), (1 : ℂ) := by
    simp [Fintype.card_perm]
  rw [hcard, Finset.sum_mul]
  simp only [one_mul]
  rw [Finset.sum_congr rfl fun τ _ => (Fintype.sum_bijective _ (pm_comp_bijective (ι := ι) τ)
    (fun g => (pmWt (g ∘ τ) : ℂ) * ((pmGmat w (g ∘ τ)).det *
      ∏ a, star (w ((g ∘ τ) a).1 ((g ∘ τ) a).2 a)))
    (fun g => (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)))
    fun _ => rfl).symm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hsub : ∀ τ : Equiv.Perm (Fin D), pmGmat w (g ∘ τ) = (pmGmat w g).submatrix id τ :=
    fun τ => rfl
  have hstar : star (pmGmat w g).det = ∑ τ : Equiv.Perm (Fin D),
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ a, star (w (g (τ a)).1 (g (τ a)).2 a) := by
    rw [← det_conjTranspose, det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [conjTranspose_apply, pmGmat, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  simp only [pmWt_comp_perm, hsub, det_permute', Function.comp_apply]
  rw [hstar, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem pm_mdisc_gram (w : Fin D → ι → Fin D → ℂ) :
    mdisc (pmGram w) = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hD : (D.factorial : ℂ) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
  have h1 : (D.factorial : ℂ) * mdisc (pmGram w) = ∑ g : Fin D → Fin D × ι,
      (pmWt g : ℂ) * ((pmGmat w g).det * ∏ a, star (w (g a).1 (g a).2 a)) := by
    rw [mdisc, ← mul_assoc, mul_one_div_cancel hD, one_mul]
    simp only [pm_det_sum_gram, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← pm_sum_alt, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  have h2 := pm_sum_perm_reindex w
  rw [← h1] at h2
  have h3 : ∑ g : Fin D → Fin D × ι, (pmWt g : ℂ) * ((pmGmat w g).det * star (pmGmat w g).det) =
      ((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  push_cast
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  push_cast at h3
  rw [← h3, ← h2]
  ring

theorem pm_mdisc_gram_sum_nonneg (w : Fin D → ι → Fin D → ℂ) :
    0 ≤ ∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det :=
  Finset.sum_nonneg fun g _ => mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)

open scoped MatrixOrder in
theorem pm_exists_gram_of_posSemidef {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) :
    ∃ v : Fin D → Fin D → ℂ, ∀ a b, A a b = ∑ r, v r a * star (v r b) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  refine ⟨fun r a => star (B r a), fun a b => ?_⟩
  rw [hB, star_eq_conjTranspose, Matrix.mul_apply]
  simp [conjTranspose_apply]


theorem pm_mdisc_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ι → Fin D → ℂ)
    (h : ∀ k a b, A k a b = ∑ r, w k r a * star (w k r b)) :
    mdisc A = (((∑ g : Fin D → Fin D × ι, pmWt g * Complex.normSq (pmGmat w g).det) /
      (D.factorial : ℝ) ^ 2 : ℝ) : ℂ) := by
  have : A = pmGram w := by funext k; ext a b; simp [pmGram, h]
  rw [this, pm_mdisc_gram]

theorem mixedDiscriminant_nonneg_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  rw [pm_mdisc_of_gram A v hv]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact div_nonneg (pm_mdisc_gram_sum_nonneg _) (by positivity)

theorem mixedDiscriminant_re_mono_of_gram (A B : Fin D → Matrix (Fin D) (Fin D) ℂ) (hA : ∀ k, (A k).PosSemidef)
    (hAB : ∀ k, (B k - A k).PosSemidef) : (mdisc A).re ≤ (mdisc B).re := by
  choose v hv using fun k => pm_exists_gram_of_posSemidef (hA k)
  choose u hu using fun k => pm_exists_gram_of_posSemidef (hAB k)
  let w : Fin D → (Fin D ⊕ Fin D) → Fin D → ℂ := fun k => Sum.elim (v k) (u k)
  have hw : ∀ k a b, B k a b = ∑ s, w k s a * star (w k s b) := by
    intro k a b
    have e : B k a b = A k a b + (B k - A k) a b := by simp
    rw [e, hv, hu, Fintype.sum_sum_type]
    rfl
  rw [pm_mdisc_of_gram A v hv, pm_mdisc_of_gram B w hw, Complex.ofReal_re, Complex.ofReal_re]
  gcongr
  let φ : (Fin D → Fin D × Fin D) → (Fin D → Fin D × (Fin D ⊕ Fin D)) :=
    fun g a => ((g a).1, Sum.inl (g a).2)
  have hφ : Function.Injective φ := by
    intro g h e
    funext a
    have := congrFun e a
    simp only [φ, Prod.mk.injEq, Sum.inl.injEq] at this
    exact Prod.ext this.1 this.2
  calc ∑ g : Fin D → Fin D × Fin D, pmWt g * Complex.normSq (pmGmat v g).det
      = ∑ g : Fin D → Fin D × Fin D, pmWt (φ g) * Complex.normSq (pmGmat w (φ g)).det :=
        Finset.sum_congr rfl fun g _ => rfl
    _ = ∑ g ∈ univ.image φ, pmWt g * Complex.normSq (pmGmat w g).det :=
        (Finset.sum_image (f := fun g => pmWt g * Complex.normSq (pmGmat w g).det)
          fun x _ y _ h => hφ h).symm
    _ ≤ ∑ g, pmWt g * Complex.normSq (pmGmat w g).det :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun g _ _ =>
          mul_nonneg (pmWt_nonneg g) (Complex.normSq_nonneg _)

end ReciprocityTheory.AnForm.A
end
