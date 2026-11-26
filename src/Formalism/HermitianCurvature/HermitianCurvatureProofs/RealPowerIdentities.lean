module

public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.StatementTA
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RealPowerIdentities
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

namespace RealPowerIdentities

theorem inv_pow_triangle_mul_rpow_half {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (T ^ (m * (m + 1) / 2))⁻¹ * T ^ ((m : ℝ) / 2) = T ^ (-((m : ℝ) ^ 2) / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have hc : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_neg hT.le, ← Real.rpow_add hT]
  congr 1
  ring

theorem rpow_half_mul_pow_triangle {Z : ℝ} (hZ : 0 < Z) {m : ℕ} (hm : 1 ≤ m) :
    Z ^ ((m : ℝ) / 2) * Z ^ (m * (m - 1) / 2) = Z ^ ((m : ℝ) ^ 2 / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have hc : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast [Nat.cast_sub hm]
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_add hZ]
  congr 1
  ring

end RealPowerIdentities

open RealPowerIdentities in
theorem germExpansionOfTestFunction : Formalism.FourierDecayAlt.A6.GermPhiAssemble := by
  intro hOsc hSt hInv hMod K _ _ _ R ψ hd hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨L₁, Λ₁, hL₁, hΛ₁, V₁, hV₁, hO⟩ := hOsc K R ψ hd hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  have hQ'c : IsCompact ((fun d : K => (-1) ^ m * d) '' Q) :=
    hQc.image (continuous_const.mul continuous_id)
  have hQ'u : ∀ d ∈ (fun d : K => (-1) ^ m * d) '' Q, IsUnit d := by
    rintro _ ⟨d, hdQ, rfl⟩
    exact (isUnit_one.neg.pow m).mul (hQu d hdQ)
  obtain ⟨V₂, hV₂, hS⟩ := hSt K R ψ hd hn m hm γ hγ L₁ Λ₁ _ hL₁ hΛ₁ hQ'c hQ'u
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, ?_⟩
  intro Φ hΦ t c ht hc
  have hD : ((c * t ^ m : Kˣ) : K) ∈ Q := by simpa using hc
  obtain ⟨A, hA, hAz, hAo⟩ := hO Φ hΦ (c * t ^ m) hD
  obtain ⟨Λ, hΛ, hinv⟩ := hInv K R ψ hd hn m L₁ Λ₁ hL₁ hΛ₁ A ((t⁻¹ : Kˣ) : K)
    (((-1) ^ m * (c * t ^ m) : Kˣ) : K) hA
  have hD' : (((-1) ^ m * (c * t ^ m) : Kˣ) : K) ∈ (fun d : K => (-1) ^ m * d) '' Q :=
    ⟨_, hD, by simp⟩
  have hDeq : ((-1) ^ m * (c * t ^ m) : Kˣ) = (-t) ^ m * c := by
    rw [neg_pow t m]
    ac_rfl
  have hT : 0 < modK R (t : K) := (hMod K R ψ hd t t).1
  rw [hAo t c ht.1 rfl Λ hΛ hinv, hS t _ A ht.2 hD' hA Λ hΛ hinv]
  unfold germSum
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_pow_triangle_mul_rpow_half hT m]
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : z ^ (m + 1) = (-1) ^ m * (c * t ^ m)
  · have hZ : 0 < modK R (z : K) := (hMod K R ψ hd z z).1
    rw [if_pos hz, if_pos (hz.trans hDeq), hAz z hz]
    unfold germCoef
    rw [← rpow_half_mul_pow_triangle hZ hm]
    push_cast
    ring
  · rw [if_neg hz, if_neg (fun h => hz (h.trans hDeq.symm))]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open scoped InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

structure PKer (α : Type) where
  K : α → α → ℂ
  psd : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K

namespace PKer

variable {α : Type} (P : PKer α)

def Sp (_P : PKer α) : Type := α →₀ ℂ

instance : AddCommGroup P.Sp := inferInstanceAs (AddCommGroup (α →₀ ℂ))
instance : Module ℂ P.Sp := inferInstanceAs (Module ℂ (α →₀ ℂ))

def fm (f g : α →₀ ℂ) : ℂ := f.sum fun x a => conj a * g.sum fun y b => P.K x y * b

theorem herm (x y : α) : conj (P.K y x) = P.K x y := by
  classical
  have h := (P.psd {x, y}).1
  have hx : x ∈ ({x, y} : Finset α) := by simp
  have hy : y ∈ ({x, y} : Finset α) := by simp
  have := congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩
  simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using this

theorem fm_add_left (f₁ f₂ g : α →₀ ℂ) : P.fm (f₁ + f₂) g = P.fm f₁ g + P.fm f₂ g := by
  unfold fm
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [map_add (f := _)]; ring)

theorem fm_smul_left (f g : α →₀ ℂ) (r : ℂ) : P.fm (r • f) g = conj r * P.fm f g := by
  unfold fm
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [smul_eq_mul, map_mul]; ring

theorem fm_conj (f g : α →₀ ℂ) : conj (P.fm g f) = P.fm f g := by
  unfold fm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [P.herm y x]; ring

theorem fm_nonneg (f : α →₀ ℂ) : 0 ≤ (P.fm f f).re := by
  classical
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 (P.psd f.support)).2 (fun i => f i)
  have e : dotProduct (star (fun i : f.support => f i)) (Matrix.mulVec (Matrix.of fun x y : f.support => P.K x y) (fun i => f i)) =
      P.fm f f := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    unfold fm
    simp only [Finsupp.sum]
    rw [← Finset.sum_coe_sort f.support (fun x => (starRingEnd ℂ) (f x) * ∑ y ∈ f.support, P.K x y * f y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort f.support (fun y => P.K (↑i) y * f y)]
    simp only [Complex.star_def]
  rw [e] at h
  exact (Complex.nonneg_iff.1 h).1

instance core : PreInnerProductSpace.Core ℂ P.Sp where
  inner f g := P.fm f g
  conj_inner_symm f g := P.fm_conj f g
  re_inner_nonneg f := P.fm_nonneg f
  add_left f₁ f₂ g := P.fm_add_left f₁ f₂ g
  smul_left f g r := P.fm_smul_left f g r

instance : SeminormedAddCommGroup P.Sp := InnerProductSpace.Core.toSeminormedAddCommGroup (c := P.core)
instance : InnerProductSpace ℂ P.Sp := InnerProductSpace.ofCore P.core

abbrev H : Type := UniformSpace.Completion P.Sp

def vec (x : α) : P.H := UniformSpace.Completion.coe' (show P.Sp from Finsupp.single x (1 : ℂ))

theorem inner_vec (x y : α) : ⟪P.vec x, P.vec y⟫_ℂ = P.K x y := by
  unfold vec
  refine (UniformSpace.Completion.inner_coe (𝕜 := ℂ) _ _).trans ?_
  show P.fm (Finsupp.single x 1) (Finsupp.single y 1) = P.K x y
  unfold fm
  simp

end PKer

theorem kolmogorov {α : Type} (K : α → α → ℂ) (hK : ∀ Y : Finset α, Formalism.FourierDecayAlt.TB.PSDOn Y K) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (V : α → H),
      ∀ x y, K x y = ⟪V x, V y⟫_ℂ :=
  let P : PKer α := ⟨K, hK⟩
  ⟨P.H, inferInstance, inferInstance, inferInstance, P.vec, fun x y => (P.inner_vec x y).symm⟩

end

end Formalism.FourierDecayAlt.P.GermFibreKernels
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondPolynomialClauses
open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem third_polynomial_prime_combination : LeadingBlockSeveralPlacesBound := by
  intro ι _ _ K abelian₂ t t' Ntt Nt Nt' S1 S2 ht hLam hNt hNt' hS1 hS2 hG hA hB
  obtain ⟨m, hm⟩ : ∃ m : ι → ℝ, m = fun v => minFac (2 * abelian₂ v) (oAbs t t' v) K := ⟨_, rfl⟩
  have hm0 : ∀ v, 0 ≤ m v := by
    intro v; rw [hm]; dsimp only; unfold minFac; split_ifs with h
    · exact pow_nonneg (div_nonneg (by linarith [hLam v]) (norm_nonneg _)) _
    · exact zero_le_one
  have key : ∀ v (s : ℝ), 0 ≤ s → s * oAbs t t' v ≤ 2 → 2 * abelian₂ v < oAbs t t' v →
      (s * abelian₂ v) ^ (2 * K) ≤ m v ^ 2 := by
    intro v s hs hso hlt
    have ho : 0 < oAbs t t' v := lt_of_le_of_lt (by linarith [hLam v]) hlt
    have hmv : m v = (2 * abelian₂ v / oAbs t t' v) ^ K := by rw [hm]; dsimp only; rw [minFac, if_pos hlt]
    rw [hmv, ← pow_mul, mul_comm K 2]
    apply pow_le_pow_left₀ (mul_nonneg hs (hLam v))
    rw [le_div_iff₀ ho]; nlinarith [mul_le_mul_of_nonneg_right hso (hLam v)]
  have h1 : ∀ v, oAbs t t' v ≤ 1 / ‖t v‖ + 1 / ‖t' v‖ := by
    intro v; unfold oAbs
    calc _ ≤ ‖1 / t v‖ + ‖1 / t' v‖ := norm_sub_le _ _
      _ = _ := by rw [norm_div, norm_div, norm_one]
  have hto : ∀ v, ‖t v‖ ≤ ‖t' v‖ → ‖t v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t v‖ * oAbs t t' v ≤ ‖t v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) ha.le
      _ = 1 + ‖t v‖ / ‖t' v‖ := by rw [mul_add, mul_one_div_cancel ha.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one hb).mpr hle]
  have hto' : ∀ v, ¬ ‖t v‖ ≤ ‖t' v‖ → ‖t' v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t' v‖ * oAbs t t' v ≤ ‖t' v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) hb.le
      _ = ‖t' v‖ / ‖t v‖ + 1 := by rw [mul_add, mul_one_div_cancel hb.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one ha).mpr (le_of_lt (not_le.mp hle))]
  have hPA : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod₀ (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto v hv2) hv1)
  have hPB : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod₀ (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto' v hv2) hv1)
  have hdisj : Disjoint (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖))
      (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖)) :=
    Finset.disjoint_filter.mpr fun v _ hv1 hv2 => hv2.2 hv1.2
  have hM : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) *
      (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) =
      (∏ v, m v) ^ 2 := by
    rw [← Finset.prod_union hdisj, ← Finset.prod_pow]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    have hnot : ¬ 2 * abelian₂ v < oAbs t t' v := by
      intro hlt
      apply hv
      by_cases hle : ‖t v‖ ≤ ‖t' v‖
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
    rw [hm]; dsimp only; rw [minFac, if_neg hnot, one_pow]
  have hM0 : 0 ≤ ∏ v, m v := Finset.prod_nonneg fun v _ => hm0 v
  have hgoal : ∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K = ∏ v, m v := by rw [hm]
  rw [hgoal]
  have hsq : ‖Ntt‖ ^ 2 ≤ ((∏ v, m v) * ((S1 + S2) / 2)) ^ 2 := by
    calc ‖Ntt‖ ^ 2 ≤ Nt * Nt' := hG
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
            (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
            (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2) :=
          mul_le_mul hA hB hNt' (le_trans hNt hA)
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hPA hS1) (mul_le_mul_of_nonneg_right hPB hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _) hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => sq_nonneg _) hS1)
      _ = (∏ v, m v) ^ 2 * (S1 * S2) := by rw [← hM]; ring
      _ ≤ (∏ v, m v) ^ 2 * ((S1 + S2) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (S1 - S2)]) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (by linarith)) two_ne_zero).mp hsq

end Formalism.FourierDecayAlt.P.SecondPolynomialClauses

theorem Formalism.FourierDecayAlt.P.third_polynomial_prime_combine : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockSeveralPlacesBound := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.third_polynomial_prime_combination

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

end Blocks

end Formalism.FourierDecayAlt.P.S3x1




namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j := by ext i; simp
    rw [e, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

variable {r k : ℕ}

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Count

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count2

variable {A : Type} [CommRing A] {r k : ℕ}

theorem prod_gl (q k : ℕ) : ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) =
    q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id,
    ← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1) := by
    refine Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have : k - (k - a) = a := by omega
      rw [this]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ k := (Finset.mem_range.1 hi).le
  rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]

end Count2

end Formalism.FourierDecayAlt.P.S3x1





open Formalism.FourierDecayAlt.P.S3x1 in
theorem Formalism.FourierDecayAlt.P.gamma_factor_product : Formalism.FourierDecayAlt.S3.GammaProduct := by
  intro K _ _ k
  rw [Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveSemidefinitePullback
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

noncomputable section

open Classical

theorem sqrt_form_sum_le {n ι : Type} [Fintype n] (M : Matrix n n ℂ) (hM : M.PosSemidef)
    (I : Finset ι) (x : ι → n → ℂ) :
    √(((M *ᵥ (∑ s ∈ I, x s)) ⬝ᵥ star (∑ s ∈ I, x s)).re) ≤
      ∑ s ∈ I, √(((M *ᵥ x s) ⬝ᵥ star (x s)).re) :=
  @norm_sum_le _ _ (M.toSeminormedAddCommGroup hM) I x

def ind {α : Type} (Y A : Finset α) : Y → ℂ := fun p => if (p : α) ∈ A then 1 else 0

theorem sum_mul_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (g : α → ℂ) :
    ∑ q : Y, g q * ind Y A q = ∑ q ∈ A, g q := by
  have h := Finset.sum_coe_sort Y (fun q => g q * (if q ∈ A then (1 : ℂ) else 0))
  simp only [ind]
  rw [h]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA]

theorem star_ind {α : Type} (Y A : Finset α) : star (ind Y A) = ind Y A := by
  funext p
  simp only [Pi.star_apply, ind]
  split_ifs <;> simp

theorem form_ind {α : Type} (Y A : Finset α) (hA : A ⊆ Y) (k : α → α → ℂ) :
    ((Matrix.of fun x y : Y => k x y) *ᵥ ind Y A) ⬝ᵥ star (ind Y A) = ∑ p ∈ A, ∑ q ∈ A, k p q := by
  rw [star_ind]
  simp only [dotProduct, mulVec, of_apply]
  have h1 : ∀ p : Y, ∑ q : Y, k p q * ind Y A q = ∑ q ∈ A, k p q :=
    fun p => sum_mul_ind Y A hA (fun q => k p q)
  simp only [h1]
  exact sum_mul_ind Y A hA (fun p => ∑ q ∈ A, k p q)

theorem psd_mul {α : Type} {Y : Finset α} {k₁ k₂ : α → α → ℂ} (h₁ : PSDOn Y k₁) (h₂ : PSDOn Y k₂) :
    PSDOn Y (fun p q => k₁ p q * k₂ p q) :=
  Matrix.PosSemidef.hadamard h₁ h₂

theorem psd_pull {α β : Type} {Y : Finset α} (g : α → β) {k : β → β → ℂ}
    (h : PSDOn (Y.image g) k) : PSDOn Y (fun p q => k (g p) (g q)) :=
  Matrix.PosSemidef.submatrix h (fun p : Y => (⟨g p, Finset.mem_image_of_mem g p.2⟩ : Y.image g))

theorem psd_sum_nonneg {α : Type} {Y : Finset α} {k : α → α → ℂ} (h : PSDOn Y k) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q).re := by
  rw [← form_ind Y Y (Finset.Subset.refl Y) k, dotProduct_comm]
  exact Matrix.PosSemidef.re_dotProduct_nonneg h _

variable {E W : Type} [Field E]

theorem last_size (T : Tower E) {i : ℕ} (hi : 1 ≤ i) {p : Pt E} (hp : p ∈ T.X i) :
    ∃ s ∈ Icc 1 i, p.getLast?.map Prod.fst = some s := by
  obtain ⟨hl, hb⟩ := (T.isTower i p).1 hp
  rcases List.eq_nil_or_concat p with rfl | ⟨h, b, rfl⟩
  · simp [level] at hl; omega
  · refine ⟨b.1, ?_, by simp⟩
    have h1 : 1 ≤ b.1 := by simpa using (hb h.length (by simp)).1
    have h2 : level (h.concat b) = level h + b.1 := by simp [level]
    rw [Finset.mem_Icc]
    exact ⟨h1, by omega⟩

theorem sum_ind_Xs (T : Tower E) {i : ℕ} (hi : 1 ≤ i) :
    ∑ s ∈ Icc 1 i, ind (T.X i) (Xs T i s) = ind (T.X i) (T.X i) := by
  funext p
  obtain ⟨s, hs, hps⟩ := last_size T hi p.2
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · have hm : (p : Pt E) ∈ Xs T i s := by
      simp only [Xs, Finset.mem_filter]
      exact ⟨p.2, hps⟩
    simp [ind, hm]
  · intro s' _ hne
    have : (p : Pt E) ∉ Xs T i s' := by
      simp only [Xs, Finset.mem_filter, not_and]
      intro _ h
      rw [hps] at h
      exact hne (Option.some.inj h).symm
    simp [ind, this]
  · intro h; exact absurd hs h

theorem Nst_re (D : Data E W) (ε : ℝ) (i s : ℕ) (w : W) (Y : Finset (Pt E))
    (κ : Pt E → Pt E → ℂ) (t t' : E) :
    (D.Nst ε i s w Y κ t t').re =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * D.gram ε i w (join h s t) (join h' s t')).re / D.wt w := by
  simp only [Data.Nst, Complex.div_ofReal_re]

theorem Nst_nonneg (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ : Pt E → Pt E → ℂ} (hκ : PSDOn Y κ) (t : E) :
    0 ≤ (D.Nst ε i s w Y κ t t).re := by
  rw [Nst_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg (psd_mul hκ (psd_pull (fun h => join h s t) (hG ε hε i w _)))

theorem Nst_mono (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ₁ κ₂ : Pt E → Pt E → ℂ}
    (hκ : PSDOn Y (fun h h' => κ₂ h h' - κ₁ h h')) (t : E) :
    (D.Nst ε i s w Y κ₁ t t).re ≤ (D.Nst ε i s w Y κ₂ t t).re := by
  have h := Nst_nonneg D hG hW hε i s w Y hκ t
  have e : D.Nst ε i s w Y (fun h h' => κ₂ h h' - κ₁ h h') t t =
      D.Nst ε i s w Y κ₂ t t - D.Nst ε i s w Y κ₁ t t := by
    simp only [Data.Nst, sub_mul, Finset.sum_sub_distrib, sub_div]
  rw [e, Complex.sub_re] at h
  linarith

end

end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

namespace Formalism.FourierDecayAlt.P

open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback

open Classical in
theorem splitByLastSize : Formalism.FourierDecayAlt.TB.SplitBySize := by
  intro E W _ D hG hK T ε hε i hi w
  have hM : PSDOn (T.X i) (fun p q => D.Kr i p q * D.gram ε i w p q) :=
    psd_mul (hK.1 i _) (hG ε hε i w _)
  have h := sqrt_form_sum_le _ hM (Icc 1 i) (fun s => ind (T.X i) (Xs T i s))
  have h2 : ∀ s, Xs T i s ⊆ T.X i := fun s => Finset.filter_subset _ _
  rw [sum_ind_Xs T hi, form_ind (T.X i) (T.X i) (Finset.Subset.refl _)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  simp only [fun s => form_ind (T.X i) (Xs T i s) (h2 s)
    (fun p q => D.Kr i p q * D.gram ε i w p q)] at h
  exact h

open Classical in
theorem diagStep : Formalism.FourierDecayAlt.TB.DiagStep := by
  intro E W _ D hG hK hW hA T ε hε i s hs hsi hir w R hR
  obtain ⟨_, hdom, hper, _⟩ := hA i s hs hsi hir
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ h).1 hh).1
  have hnn : ∀ t₀ t : E, 0 ≤ (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re :=
    fun t₀ t => Nst_nonneg D hG hW hε i s w _ (hK.2 i s t₀ _) t
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold Data.Dg
  refine Finset.sum_le_sum fun t ht => ?_
  have ht0 : t ≠ 0 := fun h => T.zero_not_mem _ _ (h ▸ ht)
  obtain ⟨t₀, ht₀, hmem⟩ := hR t ht
  have h1 := Nst_mono D hG hW hε i s w (T.X (i - s)) (hdom t ht0 _ hY) t
  rw [hper t t₀ hmem] at h1
  refine h1.trans ?_
  have h2 := Finset.single_le_sum (f := fun t₀ => if t - t₀ ∈ D.La (i - s + 1) s then
      (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re else 0)
    (fun x _ => by
      split_ifs
      · exact hnn x t
      · exact le_refl 0) ht₀
  simpa only [if_pos hmem] using h2

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PosSemidefEntryBound
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.A6x2

lemma normsq_eq_inner {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) :
    ((‖w‖ : ℝ) : ℂ) ^ 2 = inner ℂ w w := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w).symm

lemma sum_addChar_norm_sq (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (G : Type)
    [AddCommGroup G] [Fintype G] (v : G → E) :
    ∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 = (Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 := by
  classical
  have key : ((∑ χ : AddChar G ℂ, ‖∑ g, χ (-g) • v g‖ ^ 2 : ℝ) : ℂ) =
      (((Fintype.card G : ℝ) * ∑ g, ‖v g‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have h1 : ∀ χ : AddChar G ℂ, ((‖∑ g, χ (-g) • v g‖ : ℂ)) ^ 2 =
        ∑ g, ∑ h, χ (g - h) * inner ℂ (v g) (v h) := by
      intro χ
      rw [normsq_eq_inner, sum_inner]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [inner_smul_left, inner_smul_right, AddChar.map_neg_eq_conj, Complex.conj_conj,
        sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ g : G, ∑ χ : AddChar G ℂ, ∑ h, χ (g - h) * inner ℂ (v g) (v h) =
        (Fintype.card G : ℂ) * (‖v g‖ : ℂ) ^ 2 := by
      intro g
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_eq_zero]
      rw [Finset.sum_eq_single g]
      · rw [if_pos rfl, normsq_eq_inner]
      · intro b _ hb
        rw [if_neg (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ g) h
    simp_rw [h2]
    rw [Finset.mul_sum]
  exact_mod_cast key

theorem parsevalGroup : ParsevalGroup := by
  intro E _ _ G _ _ v
  classical
  rw [finsum_eq_sum_of_fintype]
  have hN : (Fintype.card G : ℝ) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos_iff.2 ⟨0⟩
    positivity
  have h1 : ∀ χ : AddChar G ℂ, ‖(Fintype.card G : ℂ)⁻¹ • ∑ g, χ (-g) • v g‖ ^ 2 =
      ((Fintype.card G : ℝ)⁻¹) ^ 2 * ‖∑ g, χ (-g) • v g‖ ^ 2 := by
    intro χ
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
  simp_rw [h1]
  rw [← Finset.mul_sum, sum_addChar_norm_sq]
  field_simp

theorem pSDClosed : PSDClosed := by
  intro X F k l hk hl a
  have ht : Tendsto (fun j => ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y) atTop
      (𝓝 (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y)) :=
    tendsto_finsetSum _ fun x hx => tendsto_finsetSum _ fun y hy => (hl x hx y hy).const_mul _
  constructor
  · have h1 := (Complex.continuous_im.tendsto _).comp ht
    have h2 : (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) = fun _ => (0 : ℝ) := by
      funext j; exact (hk j a).1
    have h3 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).im) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).im)) := h1
    rw [h2] at h3
    exact (tendsto_nhds_unique h3 tendsto_const_nhds)
  · have h1 : Tendsto (fun j => (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k j x y).re) atTop
        (𝓝 ((∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * l x y).re)) :=
      (Complex.continuous_re.tendsto _).comp ht
    exact ge_of_tendsto' h1 fun j => (hk j a).2

theorem boundedSubseq : BoundedSubseq := by
  intro I _ θ C hC
  have := Fintype.ofFinite I
  have hb : ∀ j, θ j ∈ Metric.closedBall (0 : I → ℂ) (max C 0) := by
    intro j
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    exact fun i => (hC j i).trans (le_max_left _ _)
  obtain ⟨l, -, φ, hφ, hl⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hb
  exact ⟨φ, l, hφ, fun i => (tendsto_pi_nhds.1 hl) i⟩

lemma posSemidef_of_isPSD {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    (Matrix.of fun x y : F => conj (k x y)).PosSemidef := by
  classical
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.isPositive_iff_complex]
  intro v
  have hv : inner ℂ ((Matrix.of fun x y : F => conj (k x y)).toEuclideanLin v) v =
      ∑ x ∈ F, ∑ y ∈ F, (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) x *
        conj ((fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0) y) * k x y := by
    rw [← Finset.sum_coe_sort F]
    simp_rw [← Finset.sum_coe_sort F (fun y => _ * k _ y)]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hv]
  obtain ⟨h1, h2⟩ := h (fun x => if hx : x ∈ F then v ⟨x, hx⟩ else 0)
  refine ⟨?_, h2⟩
  apply Complex.ext
  · simp
  · simpa using h1.symm

open scoped MatrixOrder in
lemma exists_factor {X : Type} (F : Finset X) (k : X → X → ℂ) (h : IsPSD F k) :
    ∃ S : F → F → ℂ, ∀ x y : F, k x y = ∑ j, S j x * conj (S j y) := by
  classical
  have h0 := (posSemidef_of_isPSD F k h).nonneg
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h0
  refine ⟨fun j x => B j x, fun x y => ?_⟩
  have h1 := congrFun (congrFun hB x) y
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply] at h1
  have h2 := congrArg conj h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Complex.conj_conj, map_sum] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem gramRealiseCut : GramRealiseCut := by
  intro X F G Gc h1 h2
  classical
  obtain ⟨S1, hS1⟩ := exists_factor F Gc h1
  obtain ⟨S2, hS2⟩ := exists_factor F _ h2
  let e : (F ⊕ F) ≃ Fin (Fintype.card (F ⊕ F)) := Fintype.equivFin _
  let u : X → EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) := fun x =>
    WithLp.toLp 2 (fun i => if hx : x ∈ F then
      Sum.elim (fun j => S1 j ⟨x, hx⟩) (fun j => S2 j ⟨x, hx⟩) (e.symm i) else 0)
  let d : Fin (Fintype.card (F ⊕ F)) → ℂ := fun i => if (e.symm i).isLeft then 1 else 0
  let T : EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card (F ⊕ F))) :=
    { toFun := fun v => WithLp.toLp 2 (fun i => d i * v i)
      map_add' := by
        intro v w; ext i; simp [mul_add]
      map_smul' := by
        intro c v; ext i; simp; ring }
  refine ⟨_, u, T, ?_, ?_, ?_⟩
  · intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    show ‖d i * v i‖ ^ 2 ≤ ‖v i‖ ^ 2
    by_cases hi : (e.symm i).isLeft
    · simp [d, hi]
    · simp [d, hi]
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    have h4 := hS2 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3 h4
    simp only [u, hx, hy, dite_true, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr,
      RCLike.inner_apply, Finset.univ_eq_attach]
    rw [← h3, ← h4]
    ring
  · intro x hx y hy
    rw [PiLp.inner_apply, ← e.sum_comp, Fintype.sum_sum_type]
    have h3 := hS1 ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.univ_eq_attach] at h3
    simp [u, T, d, hx, hy]
    exact h3.symm

theorem pSDEntryBound : PSDEntryBound := by
  intro X F k M h1 h2 x hx y hy
  obtain ⟨n, u, T, hT, hG, hGc⟩ := gramRealiseCut X F M k h1 h2
  have hn : ∀ z ∈ F, ‖u z‖ ^ 2 = (M z z).re := by
    intro z hz
    rw [← hG z hz z hz]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (u z)).symm
  rw [← hGc x hx y hy, ← hn x hx, ← hn y hy, ← mul_pow]
  have h3 : ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖u x‖ * ‖u y‖ :=
    calc ‖inner ℂ (T (u y)) (T (u x))‖ ≤ ‖T (u y)‖ * ‖T (u x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u y‖ * ‖u x‖ := mul_le_mul (hT _) (hT _) (norm_nonneg _) (norm_nonneg _)
      _ = ‖u x‖ * ‖u y‖ := mul_comm _ _
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

end Formalism.FourierDecayAlt.P.A6x2

namespace Formalism.FourierDecayAlt.P

theorem parsevalGroup_statement : Formalism.FourierDecayAlt.A6.ParsevalGroup := A6x2.parsevalGroup

theorem gramRealisation : Formalism.FourierDecayAlt.A6.GramRealiseCut := A6x2.gramRealiseCut

theorem posSemidefEntryBound : Formalism.FourierDecayAlt.A6.PSDEntryBound := A6x2.pSDEntryBound

theorem posSemidefClosed : Formalism.FourierDecayAlt.A6.PSDClosed := A6x2.pSDClosed

theorem boundedSubsequence : Formalism.FourierDecayAlt.A6.BoundedSubseq := A6x2.boundedSubseq

end Formalism.FourierDecayAlt.P
end
end
