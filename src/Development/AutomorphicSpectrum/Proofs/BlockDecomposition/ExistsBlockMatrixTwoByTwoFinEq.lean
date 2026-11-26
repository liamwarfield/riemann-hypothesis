module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlockMatrixTwoByTwoFinEq
noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem submatrix_fromBlocks_mul {n : ℕ} (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {n : ℕ} : blk4 (1 : Matrix (Fin n) (Fin n) K) 0 0 1 = 1 := by
  simp [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_injective {n : ℕ} {a b c d a' b' c' d' : Matrix (Fin n) (Fin n) K}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h'
  exact Matrix.fromBlocks_inj.mp h'

theorem neg_block_matrix {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_neg]
  rfl

theorem exists_blockMatrixTwoByTwoFin_eq {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    ∃ A B C D : Matrix (Fin n) (Fin n) K, g = blk4 A B C D := by
  refine ⟨(g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (g.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id]

theorem is_siegel_parabolic_block_iff {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    IsSiegelP (blk4 a b c d) ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    have h' := h i j
    simpa only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply] using h'
  · rintro rfl i j
    simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]

theorem det_block_lower_zero {n : ℕ} (a b d : Matrix (Fin n) (Fin n) K) :
    (blk4 a b 0 d).det = a.det * d.det := by
  simp only [blk4, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

section cT
variable (σ : K →+* K)

theorem cT_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) K) (y : Matrix (Fin b) (Fin c) K) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {a : ℕ} : cT σ (1 : Matrix (Fin a) (Fin a) K) = 1 := by
  unfold cT; simp

theorem cT_zero {a b : ℕ} : cT σ (0 : Matrix (Fin a) (Fin b) K) = 0 := by
  unfold cT; simp

theorem cT_neg {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_sub {a b : ℕ} (x y : Matrix (Fin a) (Fin b) K) : cT σ (x - y) = cT σ x - cT σ y := by
  ext i j
  simp [cT]

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : ℕ} (x : Matrix (Fin a) (Fin b) K) : cT σ (cT σ x) = x := by
  ext i j
  simp [cT, hσ]

theorem det_cT {a : ℕ} (x : Matrix (Fin a) (Fin a) K) : (cT σ x).det = σ x.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem isUnit_det_cT {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : IsUnit (cT σ x).det := by
  rw [det_cT]; exact hx.map σ

theorem cT_inv {a : ℕ} {x : Matrix (Fin a) (Fin a) K} (hx : IsUnit x.det) : cT σ x⁻¹ = (cT σ x)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← cT_mul, Matrix.mul_nonsing_inv _ hx, cT_one]

theorem cT_blk4 {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) K) :
    cT σ (blk4 a b c d) = blk4 (cT σ a) (cT σ c) (cT σ b) (cT σ d) := by
  ext i j
  rcases finSumFinEquiv.surjective i with ⟨i, rfl⟩
  rcases finSumFinEquiv.surjective j with ⟨j, rfl⟩
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [cT, blk4, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

end cT

theorem Jm_mul_Jm (n : ℕ) : Jm K n * Jm K n = -1 := by
  rw [Jm, submatrix_fromBlocks_mul, ← block_matrix_one (K := K), neg_block_matrix]
  congr 1 <;> simp

theorem unitary_left_inv (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : (-(Jm K n * cT σ g * Jm K n)) * g = 1 := by
  unfold IsUnitary at hg
  rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ g), hg, Jm_mul_Jm, neg_neg]

theorem isUnit_det_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : IsUnit g.det :=
  Matrix.isUnit_det_of_left_inverse (unitary_left_inv σ hg)

theorem inv_of_unitary (σ : K →+* K) {n : ℕ} {g : Matrix (Fin (n + n)) (Fin (n + n)) K}
    (hg : IsUnitary σ (Jm K n) g) : g⁻¹ = -(Jm K n * cT σ g * Jm K n) :=
  Matrix.inv_eq_left_inv (unitary_left_inv σ hg)

theorem unitary_mul (σ : K →+* K) {N : ℕ} {J g h : Matrix (Fin N) (Fin N) K}
    (hg : IsUnitary σ J g) (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul, show cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h by
    simp only [Matrix.mul_assoc], hg, hh]

section eId

theorem eId_mul_eId (n r : ℕ) : eId K n r * eId K n r = eId K n r := by
  rw [eId, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  split_ifs <;> simp

theorem cT_eId (σ : K →+* K) (n r : ℕ) : cT σ (eId K n r) = eId K n r := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [cT, eId, Matrix.diagonal_apply, apply_ite σ]
  · simp [cT, eId, Matrix.diagonal_apply, h, Ne.symm h]

theorem eId_mul_extB {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : eId K n r * extB b = extB b := by
  ext i j
  simp only [eId, Matrix.diagonal_mul, extB]
  split_ifs <;> simp_all

theorem extB_mul_eId {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) : extB b * eId K n r = extB b := by
  ext i j
  simp only [eId, Matrix.mul_diagonal, extB]
  split_ifs <;> simp_all

theorem cT_extB (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) :
    cT σ (extB (n := n) b) = extB (cT σ b) := by
  ext i j
  simp only [cT, extB, Matrix.transpose_apply, Matrix.map_apply]
  split_ifs <;> simp_all

theorem extB_injective {n r : ℕ} (hr : r ≤ n) {b b' : Matrix (Fin r) (Fin r) K}
    (h : extB (n := n) b = extB b') : b = b' := by
  ext i j
  have h' := congrFun (congrFun h ⟨i, by omega⟩) ⟨j, by omega⟩
  simpa [extB] using h'

end eId

theorem repMat_eq (σ : K →+* K) {n r : ℕ} (b : Matrix (Fin r) (Fin r) K) (a : Matrix (Fin n) (Fin n) K) :
    repMat σ b a = blk4 ((1 - eId K n r) * a) (eId K n r * (cT σ a)⁻¹) (-(eId K n r * a))
      ((1 - eId K n r - extB b) * (cT σ a)⁻¹) := by
  rw [repMat, wr, nB, mA, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  congr 1 <;> simp [sub_mul, mul_sub, add_mul, eId_mul_extB] <;> abel

end GlobalTheory.CompanionTheory.BruhatCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBound
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {r : ℕ}

theorem cone_anti {c c' : ℝ} (hcc : c' ≤ c) {t : Fin r → ℝ} (ht : t ∈ cone r c) : t ∈ cone r c' :=
  ⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h),
    fun i h => hcc.trans (ht.2.2 i h)⟩

theorem cone_step {c : ℝ} (hc0 : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (d : ℕ) :
    ∀ a b : Fin r, b.val = a.val + d → c ^ d * t b ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have e : b = a := Fin.ext (by simpa using h)
    subst e
    simp
  | succ d ih =>
    intro a b h
    have hm : a.val + d < r := by
      have := b.2
      omega
    have h1 := ih a ⟨a.val + d, hm⟩ rfl
    have h2 := ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)
    calc c ^ (d + 1) * t b = c ^ d * (c * t b) := by ring
      _ ≤ c ^ d * t ⟨a.val + d, hm⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ t a := h1

theorem cone_pow_mul_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    {a b : Fin r} (hab : a ≤ b) : c ^ r * t b ≤ t a := by
  have hab' : a.val ≤ b.val := hab
  have h1 := cone_step hc0 ht (b.val - a.val) a b (by omega)
  have hle : c ^ r ≤ c ^ (b.val - a.val) :=
    pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)
  exact (mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1

theorem cone_pow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    (i : Fin r) : c ^ r ≤ t i := by
  have hi := i.2
  have hl : r - 1 < r := by omega
  have h1 := cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)
  have h2 := ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)
  calc c ^ r ≤ c ^ (r - 1 - i.val + 1) := pow_le_pow_of_le_one hc0.le hc1 (by omega)
    _ = c ^ (r - 1 - i.val) * c := pow_succ _ _
    _ ≤ c ^ (r - 1 - i.val) * t ⟨r - 1, hl⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ t i := h1

theorem weights_across_levels {e A T wa wb : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heA : e ≤ A) (heT : e ≤ T)
    (h : (e * A ≤ wa ∧ wb * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ wa * T ∧ e * A * wb ≤ 1) ∨ (e * A ≤ wa ∧ e * A * wb ≤ 1)) :
    wb * (e ^ 4 * A) ≤ T * wa := by
  have hA0 : 0 < A := he0.trans_le heA
  have hT0 : 0 < T := he0.trans_le heT
  have hee : e * e ^ 2 ≤ e ^ 2 := by
    have : 0 ≤ e ^ 2 := by positivity
    nlinarith
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e * (e * A) ≤ wa := by
      have : 0 ≤ e * A := by positivity
      nlinarith
    calc wb * (e ^ 4 * A) = (wb * e ^ 2) * (e * (e * A)) := by ring
      _ ≤ T * wa := mul_le_mul h2 h3 (by positivity) hT0.le
  · calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * e ^ 2 := mul_le_mul h2 hee (by positivity) zero_le_one
      _ = e ^ 2 := one_mul _
      _ ≤ wa * T := h1
      _ = T * wa := mul_comm _ _
  · have h3 : e * e ^ 2 ≤ T * wa := by
      calc e * e ^ 2 = e * (e * e) := by ring
        _ ≤ T * (e * A) := mul_le_mul heT (mul_le_mul_of_nonneg_left heA he0.le) (by positivity) hT0.le
        _ ≤ T * wa := mul_le_mul_of_nonneg_left h1 hT0.le
    calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * (e * e ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = e * e ^ 2 := one_mul _
      _ ≤ T * wa := h3

theorem frameWt_div_le_div_ratio : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c,
    ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  intro r c hc
  have hc0 : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  set c' := min c 1 with hc'
  set e := c' ^ r with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ hc0.le hc1
  refine ⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩
  have ht : t ∈ cone r c' := cone_anti (min_le_left _ _) ht0
  have hpos := ht.1
  have hge : ∀ i, e ≤ t i := cone_pow_le hc0 hc1 ht
  have hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a := fun h => cone_pow_mul_le hc0 hc1 ht h
  have hsq : e ^ 2 ≤ e := by nlinarith
  obtain ⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by
    by_cases h : s.val + 1 < r
    · refine ⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩
      have hb' : s.val < b.val := hb
      exact Fin.le_def.2 (by simp only []; omega)
    · refine ⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩
      have hb' : s.val < b.val := hb
      have := b.2
      omega
  have hT0 : 0 < T := he0.trans_le heT
  have lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simpa [frameWt] using hle ha
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
  have lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1 := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simp only [frameWt]
      rw [← div_eq_mul_inv]
      exact (div_le_one (hpos a)).2 (hle ha)
  have lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T := by
    intro γ h
    have key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T := fun b hb => by
      have h1 := hTb b hb
      have h2 := hge b
      constructor
      · rw [sq]
        exact mul_le_mul h2 heT he0.le (hpos b).le
      · have : 0 ≤ e * t b := (mul_pos he0 (hpos b)).le
        nlinarith
    rcases γ with _ | a | a
    · simp only [frameWt, one_mul]
      exact ⟨hsq.trans heT, hsq.trans heT⟩
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      simpa [frameWt] using key a ha
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      have h1 := hTb a ha
      have h2 := hge a
      simp only [frameWt]
      rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]
      constructor
      · have : 0 ≤ e * t a := (mul_pos he0 (hpos a)).le
        nlinarith
      · rw [sq]
        exact mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2 := by
    intro γ
    rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp
  have hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨
      (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨
      (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1) := by
    rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;>
      first
        | exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩
        | exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)
        | exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)
        | (exfalso; omega)
  have key := weights_across_levels he0 he1 (hge s) heT hcases
  have hwa : 0 < frameWt t α := frameWt_pos hpos α
  have hA0 : 0 < t s := hpos s
  have hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s) := by
    rw [hrat]
    field_simp
  rw [hK, div_le_div_iff₀ hwa (by positivity)]
  exact key

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBoundStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_frame_weight_ratio_bound : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c, ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | exact GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameWt_div_le_div_ratio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariant
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariantStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_preserves_equivariant : ∀ (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n), h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitary
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hk
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitaryStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_parabolic_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n, ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | exact GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOne
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOneStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | exact GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv | (intros; apply GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHom
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  change fderiv ℝ (DR Y h).1 g (g * X) = fderiv ℝ (Rd Y h.1) g (g * X)
  rw [hev.fderiv_eq]

theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simpa only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_add_left X Y h.1) g

theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : (r : ℂ) • X = r • X := by
    ext a b
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, e,
    Complex.real_smul, smul_eq_mul] using
    congrFun (GlobalTheory.CompanionTheory.RCalc.Rd_smul_left r X h.1) g

theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, mul_apply_eq_comp, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeRealLieHomStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | exact GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie | (intros; apply GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChain
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChain
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem adCL_mem_omU {n : ℕ} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hl : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) (hm : l ∈ omU lev) : k ∈ omU lev ∧ k ≠ l := by
  have hcase : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) ∨
      (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adCL, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := (mem_filter.1 hm).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev p < lev l.2.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev l.2.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem Lv_single_omU : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  intro n lev V _ _ E1 E2 u hu p q hpq hl
  have h1 : liftL n (kA E1 E2 p q) (Pi.single (omU lev) u : Cq n V) = 0 := by
    funext A
    rw [liftL_apply]
    by_cases e : A = omU lev
    · subst e
      rw [Pi.single_eq_same]
      exact hu p q hpq
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adLL lev false p q (Pi.single (omU lev) u : Cq n V) = 0 := by
    simp only [adLL, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hS
    swap
    · rfl
    by_cases hc : adCL false p q l k = 0
    · rw [hc, zero_smul]; rfl
    suffices h : creL k (annL l (Pi.single (omU lev) u : Cq n V)) = 0 by
      rw [LinearMap.smul_apply, Module.End.mul_apply, h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := creL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    have e : insert l (B.erase k) = omU lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hm : l ∈ omU lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hkl⟩ := adCL_mem_omU hpq hl hc hm
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hkl h5
    · exact notMem_erase _ _ h5
  show liftL n (kA E1 E2 p q) _ + adLL lev false p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.LvChain
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChainStatement
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_raising_kills_top_chain : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.Lv_single_omU | exact GlobalTheory.CompanionTheory.LvChain.Lv_single_omU | (intros; apply GlobalTheory.CompanionTheory.LvChain.Lv_single_omU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  delta ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  delta ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  delta ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  delta ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianFormStatement
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 :=
  @GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form
end
end
