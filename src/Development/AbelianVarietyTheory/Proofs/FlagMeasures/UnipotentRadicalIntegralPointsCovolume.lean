module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeLeProdLayersUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewOrthonormalBasisAdaptedFiltration
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetRealSandwich
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerFromCoordinatesProductLaw
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightFlagPieceTriangularFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LayerIso

variable {n m d : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {B : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}

theorem block_eq_zero (hU : Biorth r m U (fun b => (U b)ᴴ)) {t : ℕ} (ht : m ≤ t) : U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  have : U t = (∑ b ∈ range m, U b * (U b)ᴴ) * U t := by rw [h3, Matrix.one_mul]
  rw [this, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hb' : b ≠ t := by have := Finset.mem_range.1 hb; omega
  rw [Matrix.mul_assoc, h2 b t hb', Matrix.mul_zero]

theorem mem_lowers_iff (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  rw [mem_lowers]
  constructor
  · intro h s t hst
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : U t *ᵥ x ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hx) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW] at hy ⊢
    intro s hs
    have : y = (∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by rw [h3, Matrix.one_mulVec]
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc]
    by_cases ht : t ≤ s + c
    · rw [h s t ht, Matrix.zero_mul, Matrix.zero_mulVec]
    · rw [← Matrix.mulVec_mulVec, hy t (by omega), Matrix.mulVec_zero]

theorem expand (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) (S : Set (Fin d))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℂ (B '' S)) :
    Y = ∑ i, (Y * (B i)ᴴ).trace • B i ∧ ∀ i, i ∉ S → (Y * (B i)ᴴ).trace = 0 := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨by simp [hB], fun i hi => ?_⟩
    rw [hB, if_neg]
    rintro rfl
    exact hi hj
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.add_mul, trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    · rw [Matrix.add_mul, trace_add, hx.2 i hi, hy.2 i hi, add_zero]
  | smul a x _ hx =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hx.1]
    · rw [Matrix.smul_mul, trace_smul, hx.2 i hi, smul_zero]

theorem trace_self {p q : Type} [Fintype p] [Fintype q] (A : Matrix p q ℂ) :
    (A * Aᴴ).trace = ((∑ s, ∑ t, ‖A s t‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem trace_blocks (hU : Biorth r m U (fun b => (U b)ᴴ)) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (Y * Yᴴ).trace = ∑ s ∈ range m, ∑ t ∈ range m,
      (((U s)ᴴ * Y * U t) * ((U s)ᴴ * Y * U t)ᴴ).trace := by
  obtain ⟨-, -, h3⟩ := hU
  have : Y * Yᴴ = (∑ b ∈ range m, U b * (U b)ᴴ) * (Y * (∑ b ∈ range m, U b * (U b)ᴴ) * Yᴴ) := by
    rw [h3, Matrix.one_mul, Matrix.mul_one]
  rw [this, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_assoc (U s), Matrix.trace_mul_comm]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem placed_block (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t s' t' : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) (h : s' ≠ s ∨ t ≠ t') :
    (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = 0 := by
  obtain ⟨-, h2, -⟩ := hU
  have : (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = ((U s')ᴴ * U s) * Z * ((U t)ᴴ * U t') := by
    simp only [Matrix.mul_assoc]
  rw [this]
  rcases h with h | h
  · rw [h2 _ _ h]; simp
  · rw [h2 _ _ h]; simp

theorem placed_block_self (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) :
    (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = Z := by
  obtain ⟨h1, -, -⟩ := hU
  have : (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = ((U s)ᴴ * U s) * Z * ((U t)ᴴ * U t) := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, h1]; simp

noncomputable def toBlocks (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ)
    (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ) (c : ℕ) :
    ({i : Fin d // deg i = c} → ℂ) →ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ) where
  toFun z b s t := ((U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1)) s t
  map_add' z w := by
    funext b s t
    simp [add_smul, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  map_smul' a z := by
    funext b s t
    simp [mul_smul, ← Finset.smul_sum]

theorem of_toBlocks (c : ℕ) (z : {i : Fin d // deg i = c} → ℂ) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c z b) = (U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1) := rfl

theorem toBlocks_coords (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ lowers W c) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c (fun i => (Y * (B i.1)ᴴ).trace) b)
      = (U b)ᴴ * Y * U (b + c + 1) := by
  rw [of_toBlocks]
  rw [hL] at hY
  obtain ⟨h1, h2⟩ := expand hB _ hY
  conv_rhs => rw [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => deg i = c) (by simp)
    (fun i => (Y * (B i)ᴴ).trace • B i)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hi' : deg i ≠ c := by simpa using hi
  by_cases hc : c ≤ deg i
  · have : B i ∈ lowers W (c + 1) := by
      rw [hL]
      exact Submodule.subset_span ⟨i, by show c + 1 ≤ deg i; omega, rfl⟩
    rw [Matrix.mul_smul, Matrix.smul_mul,
      (mem_lowers_iff hU hW _ _).1 this b (b + c + 1) (by omega), smul_zero]
  · rw [h2 i hc]; simp

theorem toBlocks_surjective (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ) :
    Function.Surjective (toBlocks m U B deg c) := by
  intro Z
  set Y : Matrix (Fin n) (Fin n) ℂ :=
    ∑ b : Fin m, U b * Matrix.of (Z b) * (U (b + c + 1))ᴴ with hYdef
  have hY : Y ∈ lowers W c := by
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_lowers_iff hU hW]
    intro s t hst
    exact placed_block hU _ (by omega)
  refine ⟨fun i => (Y * (B i.1)ᴴ).trace, funext fun b => ?_⟩
  apply Matrix.of.injective
  rw [toBlocks_coords hU hW hB hL c Y hY b, hYdef, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_eq_single b]
  · exact placed_block_self hU _
  · intro b' _ hb
    exact placed_block hU _ (Or.inl fun h => hb (Fin.ext h.symm))
  · simp

theorem toBlocks_norm (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (z : {i : Fin d // deg i = c} → ℂ) :
    ∑ b, ∑ s, ∑ t, ‖toBlocks m U B deg c z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  set Y : Matrix (Fin n) (Fin n) ℂ := ∑ i, z i • B i.1 with hYdef
  have hY : Y ∈ lowers W c := by
    rw [hL]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i.1, i.2.ge, rfl⟩)
  have h1 : (Y * Yᴴ).trace = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    simp [hYdef, conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, trace_sum, hB,
      Subtype.val_inj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.conj_mul']
  have horth : ∀ X ∈ lowers W (c + 1), (X * Yᴴ).trace = 0 := by
    intro X hX
    rw [hL] at hX
    have h2 := (expand hB _ hX).2
    rw [hYdef, conjTranspose_sum, Matrix.mul_sum, trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [conjTranspose_smul, Matrix.mul_smul, trace_smul, h2 i.1, smul_zero]
    have := i.2
    show ¬ (c + 1 ≤ deg i.1)
    omega
  have h2 : (Y * Yᴴ).trace = ∑ s ∈ range m,
      (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace := by
    rw [trace_blocks hU]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_eq_single _ (fun t _ ht => ?_) (fun h => ?_)
    · by_cases hst : t ≤ s + c
      · rw [(mem_lowers_iff hU hW _ _).1 hY s t hst]; simp
      · have hX : U s * ((U s)ᴴ * Y * U t) * (U t)ᴴ ∈ lowers W (c + 1) := by
          rw [mem_lowers_iff hU hW]
          intro s' t' h'
          exact placed_block hU _ (by omega)
        rw [← horth _ hX, Matrix.mul_assoc (U s), Matrix.mul_assoc (U s), Matrix.trace_mul_comm (U s)]
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    · rw [block_eq_zero hU (t := s + c + 1) (by simpa using h)]; simp
  rw [h2, ← Fin.sum_univ_eq_sum_range
    (fun s => (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace)] at h1
  simp only [trace_self] at h1
  rw [← Complex.ofReal_sum] at h1
  exact Complex.ofReal_injective h1

theorem exists_layerIso : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  intro n m d W r U B deg hU hW hB hL c
  have hinj : Function.Injective (toBlocks m U B deg c) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h := toBlocks_norm hU hW hB hL c z
    rw [hz] at h
    have h0 : ∑ i, ‖z i‖ ^ 2 = 0 := by rw [← h]; simp
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h0
    funext i
    simpa using h0 i (Finset.mem_univ i)
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, toBlocks_surjective hU hW hB hL c⟩,
    toBlocks_norm hU hW hB hL c, toBlocks_coords hU hW hB hL c⟩

end GlobalTheory.LayerIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocksStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_layerCoords_to_blocks : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  first | exact @GlobalTheory.LayerIso.exists_layerIso | exact GlobalTheory.LayerIso.exists_layerIso | (intros; apply GlobalTheory.LayerIso.exists_layerIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLowering
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLowering
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadFullFlag

theorem form_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star (uMat g *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]

private theorem dotProduct_Jm_uMat_sub_one {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) =
      -(star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) -
        star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) := by
  have h := form_uMat g x y
  simp only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  linear_combination h

theorem flagN_eq_lowers : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  intro n a ε W W' hF htop hW'
  obtain ⟨hmono, -, hstab, hdual⟩ := hF
  have hmem : ∀ y, y ∈ W (2 * a + 1) := fun y => by rw [htop]; exact Submodule.mem_top

  have horth : ∀ b, b ≤ 2 * a + 1 → ∀ y,
      y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 :=
    fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩
  ext g
  have hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
    rw [sub_mulVec, one_mulVec]
  unfold GlobalTheory.FlagMeas.flagN
  simp only [Set.mem_setOf_eq, mem_lowers, add_zero]
  constructor
  · rintro ⟨h1, h2⟩

    have hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b := by
      intro b hb y hy
      have := h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)
      rw [hW'] at this
      rw [hsub]; exact this
    have hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a := by
      intro y hy
      have hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
        rw [hW']
        have e : 2 * a + 1 - a = a + 1 := by omega
        exact (horth a (by omega) y).1 (by rw [e]; exact hy)
      have := h2 y hy'
      rw [hW'] at this
      rw [hsub]; exact this

    have hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1),
        (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) := by
      intro k
      induction k with
      | zero =>
        intro _ y _
        simpa using hmem ((uMat g - 1) *ᵥ y)
      | succ k ih =>
        intro hk y hy
        rw [horth (k + 1) (by omega)]
        intro x hx
        have hx' : (uMat g - 1) *ᵥ x ∈ W k := hlow k (by omega) x hx
        have hyk : y ∈ W (2 * a + 1 - k) := by
          have e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k := by omega
          rw [e] at hy; exact hy
        have hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) :=
          ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)
        rw [dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx',
          (horth k (by omega) _).1 hgy _ hx']
        simp
    intro b y hy
    rcases lt_trichotomy b a with hb | hb | hb
    · exact hlow b hb y hy
    · subst hb; exact hmid y hy
    · by_cases hbm : 2 * a + 1 ≤ b
      · rw [hstab b hbm]; exact hmem _
      · have hk : b = 2 * a + 1 - (2 * a + 1 - b) := by omega
        have := hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)
        rw [← hk] at this; exact this
  · intro h
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · rw [hW'] at hy ⊢
      rw [← hsub]; exact h i y hy
    · rw [hW'] at hy ⊢
      have hy' : y ∈ W (a + 1) := by
        have e : 2 * a + 1 - a = a + 1 := by omega
        rw [← e]; exact (horth a (by omega) y).2 hy
      rw [← hsub]; exact h a y hy'

end GlobalTheory.RadFullFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLoweringStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_eq_lowering : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  first | exact @GlobalTheory.RadFullFlag.flagN_eq_lowers | exact GlobalTheory.RadFullFlag.flagN_eq_lowers | (intros; apply GlobalTheory.RadFullFlag.flagN_eq_lowers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowers
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowers
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private lemma linearIndependent_map_ringHom_complex {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) {ι : Type}
    [Fintype ι] {v : ι → Fin n → E} (hv : LinearIndependent E v) :
    LinearIndependent ℂ (fun i l => φ (v i l)) := by
  classical

  let f : (ι → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E v
  have hf : ∀ c, f c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply E v c
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hf] at hc
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hc i
  obtain ⟨L, hL⟩ := f.exists_leftInverse_of_injective hker
  have hB : ∀ i, LinearMap.toMatrix' L *ᵥ v i = Pi.single i 1 := by
    intro i
    rw [LinearMap.toMatrix'_mulVec]
    have h1 := LinearMap.congr_fun hL (Pi.single i 1)
    have h2 : f (Pi.single i 1) = v i := by
      rw [hf]
      simp [Pi.single_apply]
    rw [LinearMap.comp_apply, h2] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : ∀ i k, ((LinearMap.toMatrix' L).map φ *ᵥ fun l => φ (v i l)) k
      = if k = i then 1 else 0 := by
    intro i k
    have h3 := RingHom.map_mulVec φ (LinearMap.toMatrix' L) (v i) k
    rw [hB i] at h3
    rw [show (fun l => φ (v i l)) = φ ∘ v i from rfl, ← h3]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki]
  have h4 := congrArg (fun w => ((LinearMap.toMatrix' L).map φ *ᵥ w) j) hc
  simp only [Matrix.mulVec_zero, Pi.zero_apply] at h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h4, ← Matrix.mulVecLin_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Matrix.mulVecLin_apply, hcol, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma map_mem_span_image_of_mem_span {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (t : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ Submodule.span E t) :
    (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' t) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have h0 : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have h1 : (fun l => φ ((y + z) l)) = (fun l => φ (y l)) + (fun l => φ (z l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h1 : (fun l => φ ((c • y) l)) = φ c • (fun l => φ (y l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.smul_mem _ _ hy

theorem finrank_span_image_ringHom {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s))
      = Module.finrank E (Submodule.span E s) := by
  classical
  let V := Submodule.span E s
  let b := Module.finBasis E V
  let v : Fin (Module.finrank E V) → Fin n → E := fun i => (b i : Fin n → E)
  have hv : LinearIndependent E v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2
  have hspan : Submodule.span E (Set.range v) = V := by
    have hr : Set.range v = V.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have heq : Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s)
      = Submodule.span ℂ (Set.range fun i l => φ (v i l)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span E (Set.range v) := by
        rw [hspan]; exact Submodule.subset_span hx
      have h := map_mem_span_image_of_mem_span φ _ hx'
      rw [← Set.range_comp] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact map_mem_span_image_of_mem_span φ s (hvV i)
  rw [heq, finrank_span_eq_card (linearIndependent_map_ringHom_complex φ hv), Fintype.card_fin]

theorem finrank_locFlag_and_lowers (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (hP : IsUnit P) :
    (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧
      ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  refine ⟨fun b => ?_, fun c T hT => ?_⟩
  · have hinj : Function.Injective (Matrix.mulVecLin P⁻¹) := by
      intro x y hxy
      have h := congrArg (fun z => P *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, hPP] using h
    have himg : locFlag φ P F b = Submodule.map (Matrix.mulVecLin P⁻¹)
        (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' (F b : Set (Fin n → E)))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [himg, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image_ringHom]
    rfl
  · rw [GlobalTheory.RadCov.mem_lowers] at hT ⊢
    intro b y hy
    have key : locFlag φ P F (b + c + 1)
        ≤ Submodule.comap (Matrix.mulVecLin (P⁻¹ * T.map φ * P)) (locFlag φ P F b) := by
      rw [locFlag, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      refine Submodule.subset_span ⟨T *ᵥ x, hT b x hx, ?_⟩
      have h1 : (fun l => φ ((T *ᵥ x) l)) = T.map φ *ᵥ (fun l => φ (x l)) := by
        funext l; exact RingHom.map_mulVec φ T x l
      dsimp only
      rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P⁻¹ * T.map φ) P P⁻¹,
        hPP, Matrix.mul_one]
    exact key hy

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowersStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), IsUnit P → (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧ ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  first | exact @GlobalTheory.RadCov.finrank_locFlag_and_lowers | exact GlobalTheory.RadCov.finrank_locFlag_and_lowers | (intros; apply GlobalTheory.RadCov.finrank_locFlag_and_lowers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolume
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

def realMul (ι κ : Type) (c : ℂ) : (ι → κ → ℝ) →ₗ[ℤ] (ι → κ → ℂ) where
  toFun y := fun v i => c * (y v i : ℂ)
  map_add' x y := by funext v i; simp [mul_add]
  map_smul' k x := by funext v i; simp [mul_left_comm]

theorem real_domain (E : Type) [Field E] [NumberField E] [StarRing E] (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : ι → E →+* ℂ)
    (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (L : Submodule ℤ (ι → κ → ℂ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hO : ∀ x : 𝓞 E, ∀ z ∈ L, (fun v i => φ v (x : E) * z v i) ∈ L)
    (hc : ∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) :
    ∃ D : Set (ι → κ → ℝ), MeasurableSet D ∧
      (∀ x, ∃ y : ι → κ → ℝ, (fun v i => (y v i : ℂ)) ∈ L ∧ y + x ∈ D) ∧
      volume D ≤ ENNReal.ofReal
        (Real.sqrt (2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume)) := by
  classical
  have hA : ∀ y, y ∈ L.comap (realMul ι κ 1) ↔ (fun v i => (y v i : ℂ)) ∈ L := fun y => by
    simp [realMul]
  have hB : ∀ y, y ∈ L.comap (realMul ι κ Complex.I) ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L :=
    fun y => Iff.rfl
  generalize L.comap (realMul ι κ 1) = A at hA
  generalize L.comap (realMul ι κ Complex.I) = B at hB
  obtain ⟨⟨dA, lA⟩, ⟨dB, lB⟩, hle⟩ := GlobalTheory.T.conjStable_lattice_real_imag_covolume_le ι κ L hc A B hA hB
  have heq : ZLattice.covolume A volume = ZLattice.covolume B volume := by
    refine GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars ι κ A B fun p hp => ?_
    obtain ⟨δ, N, h1, h2, h3⟩ := GlobalTheory.T.exists_skew_integer_norm_coprime_prime E hE ι φ hφ p hp
    have hδ : ∀ v, φ v (δ : E) = Complex.I * ((φ v (δ : E)).im : ℂ) := by
      intro v
      have h := hE.2.1 (φ v) (δ : E)
      rw [h1, map_neg] at h
      have h4 := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.conj_re] at h4
      apply Complex.ext <;> simp
      linarith
    refine ⟨fun v => (φ v (δ : E)).im, N, h2, ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h3]
      refine Finset.prod_congr rfl fun v _ => ?_
      conv_rhs => rw [hδ v]
      simp
    · rw [hB]
      have := hO δ _ ((hA y).1 hy)
      convert this using 3 with v i
      conv_rhs => rw [hδ v]
      push_cast
      ring
    · rw [hA]
      have := neg_mem (hO δ _ ((hB y).1 hy))
      convert this using 1
      funext v i
      simp only [Pi.neg_apply]
      conv_rhs => rw [hδ v]
      push_cast
      linear_combination (((φ v (δ : E)).im : ℂ) * (y v i : ℂ)) * Complex.I_mul_I
  let b := Module.Free.chooseBasis ℤ A
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ A), ZSpan.fundamentalDomain_measurableSet _,
    fun x => ⟨-(ZSpan.floor (b.ofZLatticeBasis ℝ A) x : ι → κ → ℝ), ?_, ?_⟩, ?_⟩
  · rw [← hA]
    refine neg_mem ?_
    exact (b.ofZLatticeBasis_span ℝ).le (ZSpan.floor (b.ofZLatticeBasis ℝ A) x).2
  · rw [neg_add_eq_sub]
    exact ZSpan.fract_mem_fundamentalDomain _ x
  · have h1 := ZLattice.covolume_eq_measure_fundamentalDomain A volume
      (ZLattice.isAddFundamentalDomain b volume)
    have h2 := (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ A)).measure_lt_top (μ := volume)
    rw [← ENNReal.ofReal_toReal h2.ne]
    refine ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ?_)
    rw [← measureReal_def, ← h1, sq]
    nth_rewrite 2 [heq]
    exact hle

theorem layer_covolume (E : Type) [Field E] [NumberField E] [StarRing E] (hE : IsTotallyComplex E)
    (ι : Type) [Fintype ι] (n m d : ℕ) (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) (hX : PlaceMatch φ P X) (hP : ∀ v, IsUnit (P v))
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E))
    (hT : Biorth r m T T') (hΛ : ∀ b, Submodule.IsFullLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (U : ι → ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (hU : ∀ v, Biorth r m (U v) (fun b => (U v b)ᴴ))
    (hW : ∀ v k y, y ∈ locFlag (φ v) (P v) F k ↔ ∀ b, k ≤ b → (U v b)ᴴ *ᵥ y = 0)
    (B : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ)
    (hB : ∀ v i k, (B v i * (B v k)ᴴ).trace = if i = k then 1 else 0)
    (hs : ∀ v c, lowers (locFlag (φ v) (P v) F) c = Submodule.span ℂ (B v '' {i | c ≤ deg i})) (c : ℕ)
    (L : Submodule ℤ (ι → {i : Fin d // deg i = c} → ℂ))
    (hL : ∀ z, z ∈ L ↔ ∃ Y ∈ lowers F c, ∀ v i,
      z v i = ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace) :
    ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume =
      ∏ b ∈ Finset.range m, Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (r b * r (b + c + 1))) *
        (pieceHt X F b ^ r (b + c + 1) / pieceHt X F (b + c + 1) ^ r b) := by
  classical
  obtain ⟨hloc, hrat⟩ := GlobalTheory.T.rational_block_frame_local_split E n m F r T T' Λ hT hΛ hF
  obtain ⟨hr1, hr2⟩ := hrat c
  choose Φ hΦ1 hΦ2 using fun v => GlobalTheory.T.exists_unitary_layerCoords_to_blocks n m d _ r (U v) (B v) deg (hU v) (hW v) (hB v) (hs v) c
  set G : ι → ∀ b, Matrix (Fin (r b)) (Fin (r b)) ℂ :=
    fun v b => (U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v)) with hG
  have hblk := fun v => GlobalTheory.T.biorthogonal_block_frames_triangular n m _ r _ (U v) _ _ (hloc (φ v) (P v) (hP v)).1 (hU v)
    (hloc (φ v) (P v) (hP v)).2 (hW v)
  have hinv : ∀ v b, (G v b)⁻¹ = (T' b).map (φ v) * P v * U v b :=
    fun v b => Matrix.inv_eq_right_inv ((hblk v).1 b)
  have hdet : ∀ v b, (G v b).det ≠ 0 := fun v b =>
    (Matrix.isUnit_det_of_right_inverse ((hblk v).1 b)).ne_zero
  have hkey : ∀ Y ∈ lowers F c, ∀ v (b : Fin m),
      Matrix.of (Φ v (fun i => ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace) b) =
        G v b * (T' b * Y * T (b + c + 1)).map (φ v) * (G v (b + c + 1))⁻¹ := by
    intro Y hY v b
    have h1 := (GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers E n (φ v) (P v) F (hP v)).2 c Y hY
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hP v)
    rw [hΦ2 v _ h1, (hblk v).2 c _ h1, hinv, Matrix.map_mul, Matrix.map_mul]
    congr 2
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  let M : ∀ b : Fin m, Submodule ℤ (ι → Fin (r b) → Fin (r (b + c + 1)) → ℂ) := fun b =>
    { carrier := {z | ∃ Z : Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ y ∈ Λ (b + c + 1), Z *ᵥ y ∈ Λ b) ∧
        ∀ v, Matrix.of (z v) = G v b * Z.map (φ v) * (G v (b + c + 1))⁻¹}
      zero_mem' := ⟨0, fun y _ => by simp, fun v => by
        rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul]; rfl⟩
      add_mem' := by
        rintro z z' ⟨Z, h1, h2⟩ ⟨Z', h1', h2'⟩
        refine ⟨Z + Z', fun y hy => ?_, fun v => ?_⟩
        · rw [Matrix.add_mulVec]; exact add_mem (h1 y hy) (h1' y hy)
        · rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, ← h2, ← h2']; rfl
      smul_mem' := by
        rintro k z ⟨Z, h1, h2⟩
        refine ⟨k • Z, fun y hy => ?_, fun v => ?_⟩
        · rw [Matrix.smul_mulVec]; exact zsmul_mem (h1 y hy) k
        · have : (k • Z).map (φ v) = k • Z.map (φ v) := by ext p q; simp
          rw [this, Matrix.mul_smul, Matrix.smul_mul, ← h2]; rfl }
  have hM := fun b : Fin m => GlobalTheory.T.homLatticeCovolume_embedding_family E hE ι φ hX.1 _ _ (Λ b) (Λ (b + c + 1)) (by first | exact hΛ _ | exact (hΛ _).toIsLattice) (by first | exact hΛ _ | exact (hΛ _).toIsLattice)
    (fun v => G v b) (fun v => G v (b + c + 1)) (fun v => hdet v _) (fun v => hdet v _) (M b)
    (fun z => Iff.rfl)
  obtain ⟨dL, lL, hcov⟩ := GlobalTheory.T.covolume_pi_lattice_unitary_coordinates ι {i : Fin d // deg i = c} (Fin m) (fun b => r b)
    (fun b => r (b + c + 1)) Φ hΦ1 M (fun b => (hM b).imp fun _ h => h.1) L (fun z => by
      rw [hL]
      constructor
      · rintro ⟨Y, hY, hz⟩ b
        refine ⟨_, hr1 Y hY b, fun v => ?_⟩
        rw [← hkey Y hY v b, ← funext (hz v)]
      · intro h
        choose Z hZ1 hZ2 using h
        obtain ⟨Y, hY, hYZ⟩ := hr2 Z hZ1
        refine ⟨Y, hY, fun v i => ?_⟩
        have e : z v = fun i => ((P v)⁻¹ * Y.map (φ v) * P v * (B v i.1)ᴴ).trace := by
          refine (Φ v).injective (funext fun b => Matrix.of.injective ?_)
          rw [hkey Y hY v b, hYZ b, ← hZ2 b v]
        exact congrFun e i)
  refine ⟨dL, lL, ?_⟩
  rw [hcov, Finset.prod_range]
  refine Finset.prod_congr rfl fun b _ => ?_
  obtain ⟨_, -, h⟩ := hM b
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E := by
    have : 0 < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hp := GlobalTheory.T.height_flag_piece_triangular_frame E hE ι n m φ P X hX hP F r T T' Λ hT (by intro b; first | exact hΛ b | exact (hΛ b).toIsLattice) hF U hU hW
  rw [h, hp, hp, div_mul_cancel_left₀ (pow_pos hv _).ne', mul_pow, ← pow_mul, inv_pow, mul_assoc,
    mul_assoc, div_eq_mul_inv]

theorem exists_deg (m : ℕ) (k : ℕ → ℕ) (hk : ∀ c, m ≤ c → k c = 0) (d : ℕ)
    (hd : d = ∑ c ∈ Finset.range m, k c) :
    ∃ deg : Fin d → ℕ, ∀ c, Fintype.card {i : Fin d // deg i = c} = k c := by
  classical
  have e : Fin d ≃ (Σ c : Fin m, Fin (k c)) := Fintype.equivOfCardEq (by
    simp [hd, Finset.sum_range])
  refine ⟨fun i => (e i).1, fun c => ?_⟩
  rw [Fintype.card_congr (e.subtypeEquiv (q := fun x => (x.1 : ℕ) = c) fun _ => Iff.rfl),
    Fintype.card_subtype, Finset.card_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  have h1 : ∀ x : Fin m, (∑ _y : Fin (k x), if (x : ℕ) = c then 1 else 0) = if (x : ℕ) = c then k x else 0 := by
    intro x
    split_ifs <;> simp
  refine (Finset.sum_congr rfl fun x _ => h1 x).trans ?_
  rw [← Finset.sum_range (fun x => if x = c then k x else 0), Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (hk c (by simpa using h)).symm

theorem covol_mono_left {G : Type} [Mul G] [MeasurableSpace G] {Γ Γ' : Set G} (h : Γ' ⊆ Γ) (μ : Measure G)
    (A : Set G) : covol Γ μ A ≤ covol Γ' μ A := by
  unfold covol
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun hc => ?_
  exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le_of_le
    (fun x hx => (hc x hx).imp fun γ hγ => ⟨h hγ.1, hγ.2⟩) le_rfl))

theorem adj_frame {E : Type} [Field E] [StarRing E] {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    {φ : E →+* ℂ} (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x)) {P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) {ε : Fin n → Bool} (h : Pᴴ * J.map φ * P = Formalism.REAL.Jm ε)
    (Y : Matrix (Fin n) (Fin n) E) :
    P⁻¹ * (J⁻¹ * Yᴴ * J).map φ * P =
      Formalism.REAL.Jm ε * (P⁻¹ * Y.map φ * P)ᴴ * Formalism.REAL.Jm ε := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hu' : IsUnit (Pᴴ).det := by rw [Matrix.det_conjTranspose]; exact hu.star
  have h1 : J.map φ * (J⁻¹).map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hJ.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (Yᴴ).map φ = (Y.map φ)ᴴ := by ext i k; simp [hφ]
  have h3 : Formalism.REAL.Jm ε * (P⁻¹ * (J⁻¹ * Yᴴ * J).map φ * P) = (P⁻¹ * Y.map φ * P)ᴴ * Formalism.REAL.Jm ε := by
    rw [← h, Matrix.map_mul, Matrix.map_mul, h2, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu']
    rw [← Matrix.mul_assoc (J.map φ), h1, Matrix.one_mul]
  rw [Matrix.mul_assoc (Formalism.REAL.Jm ε), ← h3, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]

theorem radicalCovolume : RadicalCovolume := by
  classical
  intro I xf a j hj S hS ν _ hν
  obtain ⟨F, r, hF, hFm, hFS, hr, hrj, hra, hr0⟩ := GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag I xf a j S hS
  obtain ⟨hτ, hha, hh1⟩ := GlobalTheory.T.selfDualHermitianFlag_piece_heights I xf a j hj S hS F hF hFm hFS
  obtain ⟨-, hfg, hsp, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I (1, xf)
  obtain ⟨htc, hf1, hf2, -, -⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I (1, xf)
  obtain ⟨hadjL, helt⟩ := GlobalTheory.T.adjoint_mem_and_exists_integral_point I xf
  have hX := GlobalTheory.T.embeddingsMatchInfinitePlaces_autInstance I xf
  have hJ : I.Jᴴ = I.J := I.J_herm
  have hφ := fun v => I.cm.cmUnram.2.1 (I.φ v)
  set m := 2 * a + 1 with hm
  rw [← hFm] at hfg hsp hadjL helt
  set W : InfinitePlace I.F → ℕ → Submodule ℂ (Fin I.n → ℂ) := fun v => locFlag (I.φ v) (I.P v) F with hWdef
  have hW : ∀ v, IsDualFlag (Formalism.REAL.Jm (I.ε v)) (W v) m ∧ W v m = ⊤ := fun v => GlobalTheory.T.selfDual_hermitianFlag_at_complex_embedding I.E I.n m I.J (I.φ v) (I.P v) (I.ε v) F (hφ v) (I.P_unit v) (I.P_spec v) hF hsp
  have hWr := fun v => GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers I.E I.n (I.φ v) (I.P v) F (I.P_unit v)
  have hN : ∀ v, flagN (I.ε v) (flagAt I S v) = {g | uMat g - 1 ∈ lowers (W v) 0} := fun v =>
    GlobalTheory.T.isotropicFlagUnipotentRadical_eq_lowering I.n a (I.ε v) (W v) _ (hW v).1 (hW v).2 fun i => by
      simp only [hWdef, locFlag, flagAt, hFS]
  choose U hU hUW using fun v => GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag I.n m (W v) r (hW v).1.1 (hW v).1.2.1
    (fun b hb => ((hW v).1.2.2.1 b hb).trans (hW v).2) (fun b => by
      rw [hWdef, (hWr v).1, (hWr v).1, hr])
  obtain ⟨deg, hdeg⟩ := exists_deg m (fun c => ∑ b ∈ Finset.range m, r b * r (b + c + 1))
    (fun c hc => Finset.sum_eq_zero fun b _ => by rw [hr0 (b + c + 1) (by omega), mul_zero])
    (dimN I.n j) (GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs I.n a j r hrj hra hr0)
  have hbot : ∀ v, lowers (W v) m = ⊥ := fun v =>
    lowers_eq_bot (hW v).1.2.1 (hW v).1.2.2.1 (by rw [(hW v).2]; simp)
  have hadj : ∀ v c, ∀ X ∈ lowers (W v) c,
      Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ lowers (W v) c := fun v c X hX =>
    lowers_adj (Formalism.REAL.Jm_conjTranspose _) (hW v).1 hX
      (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul])
      (fun y _ => by rw [(hW v).2]; trivial)
  choose B hB hBG hBs using fun v => GlobalTheory.T.exists_skew_orthonormal_basis_adapted_filtration I.n (dimN I.n j) m (I.ε v) (lowers (W v)) deg
    (lowers_succ_le (hW v).1.1) (hbot v) (hadj v) (fun c => by
      rw [hdeg, GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add I.n m (W v) r (U v) (hU v) (hUW v) c])
  have hreal := fun v s => GlobalTheory.T.real_complex_span_orthonormal_skew_family I.n _ (I.ε v) (B v) s (hB v) (hBG v)
  have hle : ∀ b, F b ≤ F m := fun b => by
    rcases le_total b m with h | h
    · exact hF.1 h
    · exact (hF.2.2.1 b h).le
  obtain ⟨T, T', Λ, hT, hΛ, hFT⟩ := GlobalTheory.T.exists_biorthogonal_frame_of_saturated_flag I.E I.n m F r hF.1 hF.2.1 hF.2.2.1 (by
      letI : Submodule.IsLattice I.E (F m) := Submodule.IsLattice.of_fg I.E hfg
      exact ⟨hsp⟩)
    (fun b y hy hyb => by
      by_cases hb : m ≤ b
      · rwa [hF.2.2.1 b hb]
      have e : b = m - (m - b) := by omega
      rw [e, hF.2.2.2 _ (by omega)]
      refine ⟨hy, fun x hx => ?_⟩
      clear hy
      induction hyb using Submodule.span_induction with
      | mem z hz => exact ((hF.2.2.2 (m - b) (by omega) z).1 (e ▸ hz)).2 x hx
      | zero => simp
      | add z z' _ _ h1 h2 => rw [Matrix.mulVec_add, dotProduct_add, h1, h2, add_zero]
      | smul c z _ h1 => rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]) hr
  have hkeep : ∀ c, ∀ Y ∈ lowers F c, ∀ y ∈ F m, Y *ᵥ y ∈ F m := fun c Y hY y hy =>
    hY m y (by rwa [hF.2.2.1 _ (by omega)])
  have hadjF : ∀ c, ∀ Y ∈ lowers F c, I.J⁻¹ * Yᴴ * I.J ∈ lowers F c := fun c Y hY =>
    lowers_adj hJ hF hY
      (by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ I.J_det.isUnit])
      (hadjL Y (hkeep c Y hY))
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.exists_integral_points_algebra_subgroup I xf (fun v => lowers (W v) 0)
    (fun v X hX Y hY => lowers_succ_le (hW v).1.1 0 (lowers_mul_zero hX hY).1) (fun v => hadj v 0)
  have hΓ' : ∀ g, g ∈ Γ ↔ g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ lowers (W v) 0 := fun g => by
    rw [← SetLike.mem_coe, hΓ]; rfl
  obtain ⟨w, hw⟩ := GlobalTheory.TraceOnto.exists_trace_one I.E I.cm.cmUnram

  have hlayer : ∀ c : ℕ, ∃ D : Set (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℝ),
      MeasurableSet D ∧ (∀ x : InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℝ,
        ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ (lowers (W v) c).restrictScalars ℝ) ∧
        (fun v (i : {i : Fin (dimN I.n j) // deg i = c}) =>
          (((uMat (γ v) - 1) * (B v i.1)ᴴ).trace).re + x v i) ∈ D) ∧
      volume D ≤ ENNReal.ofReal (Real.sqrt (2 ^ (I.f * ∑ b ∈ Finset.range m, r b * r (b + c + 1)) *
        ∏ b ∈ Finset.range m, Formalism.HermitianLatticesTheory.vInv I.E ^ (I.f * (r b * r (b + c + 1))) *
          (pieceHt (frm I (1, xf)) F b ^ r (b + c + 1) / pieceHt (frm I (1, xf)) F (b + c + 1) ^ r b))) := by
    intro c
    let crd : Matrix (Fin I.n) (Fin I.n) I.E →+
        (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℂ) :=
      { toFun := fun Y v i => ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v * (B v i.1)ᴴ).trace
        map_zero' := by funext v i; simp
        map_add' := fun Y Y' => by
          funext v i
          simp [Matrix.map_add (f := _), Matrix.mul_add, Matrix.add_mul] }
    have c0 : ∀ Y v i, crd Y v i = ((I.P v)⁻¹ * Y.map (I.φ v) * I.P v * (B v i.1)ᴴ).trace :=
      fun _ _ _ => rfl
    have c1 : ∀ (x : 𝓞 I.E) Y v i, crd (x • Y) v i = I.φ v (x : I.E) * crd Y v i := by
      intro x Y v i
      have : (x • Y).map (I.φ v) = I.φ v (x : I.E) • Y.map (I.φ v) := by
        ext p q; simp [Algebra.smul_def]
      rw [c0, c0, this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have c2 : ∀ Y v i, crd (I.J⁻¹ * Yᴴ * I.J) v i = -starRingEnd ℂ (crd Y v i) := by
      intro Y v i
      rw [c0, c0, adj_frame I.J_det (hφ v) (I.P_unit v) (I.P_spec v), (hreal v ∅).2.2]
    have c3 : ∀ Y ∈ lowers F (c + 1), crd Y = 0 := by
      intro Y hY
      funext v i
      refine (hreal v {i | c + 1 ≤ deg i}).2.1 _ ?_ _ (by simp [i.2])
      rw [← hBs]
      exact (hWr v).2 _ Y hY
    let L : Submodule ℤ (InfinitePlace I.F → {i : Fin (dimN I.n j) // deg i = c} → ℂ) :=
      ((lowers F c).toAddSubgroup.map crd).toIntSubmodule
    have hL : ∀ z, z ∈ L ↔ ∃ Y ∈ lowers F c, crd Y = z := fun z => Iff.rfl
    obtain ⟨dL, lL, hcov⟩ := layer_covolume I.E htc _ I.n m _ I.φ I.P _ hX I.P_unit F r T T' Λ hT hΛ hFT
      U hU hUW B deg hB hBs c L (fun z => by
        rw [hL]
        refine exists_congr fun Y => and_congr_right fun _ => ?_
        exact ⟨fun h v i => by rw [← h]; rfl, fun h => funext fun v => funext fun i => (h v i).symm⟩)
    obtain ⟨D, hD1, hD2, hD3⟩ := real_domain I.E I.cm.cmUnram _ _ I.φ hX.1 L
      (fun x z hz => by
        obtain ⟨Y, hY, rfl⟩ := (hL z).1 hz
        exact (hL _).2 ⟨x • Y, Submodule.smul_mem _ _ hY, funext fun v => funext fun i => c1 x Y v i⟩)
      (fun z hz => by
        obtain ⟨Y, hY, rfl⟩ := (hL z).1 hz
        refine (hL _).2 ⟨_, neg_mem (hadjF c Y hY), funext fun v => funext fun i => ?_⟩
        rw [map_neg, Pi.neg_apply, Pi.neg_apply, c2, neg_neg])
    refine ⟨D, hD1, fun x => ?_, ?_⟩
    · obtain ⟨y, hy, hyD⟩ := hD2 x
      obtain ⟨Y, hY, hYy⟩ := (hL _).1 hy
      have hY' : w • Y ∈ lowers F c := Submodule.smul_mem _ _ hY
      have hX' := sub_mem hY' (hadjF c _ hY')
      obtain ⟨Z, hZ, hU'⟩ := GlobalTheory.T.exists_unitary_leading_term_of_skew_layer (𝓞 I.E) I.E I.n m I.J (lowers F) w hJ I.J_det hw
        (lowers_succ_le hF.1) (lowers_eq_bot hF.2.1 hF.2.2.1 hsp)
        (fun c X hX Y hY => lowers_mul_zero hX hY) hadjF c _ hX' (by
          have hu := I.J_det.isUnit
          rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_nonsing_inv, hJ, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
            Matrix.sub_mul, neg_sub]
          simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu,
            Matrix.nonsing_inv_mul _ hu, Matrix.mul_one])
      have hcX : crd (w • Y - I.J⁻¹ * (w • Y)ᴴ * I.J) = fun v i => (y v i : ℂ) := by
        funext v i
        have h1 := congrArg (I.φ v) hw
        rw [map_add (f := _), hφ, map_one] at h1
        rw [map_sub, Pi.sub_apply, Pi.sub_apply, c2, c1, hYy, map_mul, Complex.conj_ofReal]
        linear_combination (y v i : ℂ) * h1
      generalize w • Y - I.J⁻¹ * (w • Y)ᴴ * I.J = X at hX' hU' hcX
      have hXZ : X + Z ∈ lowers F c := add_mem hX' (lowers_succ_le hF.1 c hZ)
      obtain ⟨g, hg, hgm⟩ := helt _ hU' (fun y hy => by
        rw [add_assoc, Matrix.add_mulVec, Matrix.one_mulVec]
        exact add_mem hy (hkeep c _ hXZ y hy))
      have hg1 : ∀ v, uMat (g v) - 1 = (I.P v)⁻¹ * (X + Z).map (I.φ v) * I.P v := by
        intro v
        rw [hgm, add_assoc, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)), add_sub_cancel_left]
      have hg2 : ∀ v, uMat (g v) - 1 ∈ lowers (W v) c := fun v => by
        rw [hg1]; exact (hWr v).2 _ _ hXZ
      refine ⟨g, (hΓ' g).2 ⟨hg, fun v => lowers_anti (hW v).1.1 (Nat.zero_le c) (hg2 v)⟩, hg2, ?_⟩
      convert hyD using 1
      funext v i
      rw [hg1, ← c0, map_add (f := _), c3 Z hZ, add_zero, hcX]
      simp
    · rw [hcov, hf2, hdeg, show Formalism.HermitianLatticesTheory.fDeg I.E = I.f from hf1] at hD3
      exact hD3
  choose D hD1 hD2 hD3 using hlayer
  have hnil := GlobalTheory.T.covolume_le_prod_layers_unipotent _ I.n (dimN I.n j) m I.ε (fun v c => (lowers (W v) c).restrictScalars ℝ) B deg
    (fun v c => lowers_succ_le (hW v).1.1 c) (fun v => by rw [hbot]; rfl)
    (fun v c X hX Y hY => lowers_mul_zero hX hY) hadj
    (fun v i k => by rw [hB]; split_ifs <;> simp)
    (fun v c X => by
      rw [← (hreal v _).1, ← hBs]; rfl) ν (fun v => by have := hν v; rwa [hN] at this) Γ D
    (fun γ hγ => ((hΓ' γ).1 hγ).2) hD1 hD2
  simp only [hN]
  refine le_trans (le_trans (covol_mono_left (fun g hg => ?_) _ _) hnil) ?_
  · obtain ⟨⟨γ, h1, h2, h3⟩, h4⟩ := (hΓ' g).1 hg
    exact ⟨γ, h1, h2, h3, h4⟩
  refine (Finset.prod_le_prod' fun c _ => hD3 c).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_prod_of_nonneg fun c _ => Real.sqrt_nonneg _]
  congr 1
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv I.E := by
    have : 0 < |(discr I.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero I.E)
    unfold Formalism.HermitianLatticesTheory.vInv
    positivity
  have hpos : ∀ b, 0 < pieceHt (frm I (1, xf)) F b := fun b => by
    have h := fun b => (Formalism.HN.plLat _ _ _ (bas I) (frm I (1, xf))
      (GlobalTheory.PointEquivariance.frm_det I (1, xf)) (F b) (Submodule.FG.of_le hfg (hle b))).2.2
    exact div_pos (h _) (h _)
  have hlp : 0 ≤ layerProd I.n I.f j
      (fun i => Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc)) id := by
    have := fun i => (hτ i).1
    unfold layerProd
    refine mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_)
      (Finset.prod_nonneg fun i _ => ?_)
    · have h1 := this i; have h2 := this k
      simp only [id]
      positivity
    · have := this i
      simp only [id]
      positivity
  rw [← Real.sqrt_prod _ (fun c _ => by
    have := hpos
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun b _ =>
      mul_nonneg (by positivity) (div_pos (pow_pos (hpos _) _) (pow_pos (hpos _) _)).le))]
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum]
  rw [← GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs I.n a j r hrj hra hr0, GlobalTheory.T.prod_layer_height_quotients_eq_sq I.n I.f a j r _ _ hrj hra hr0 hτ hha hh1, ← mul_assoc,
    ← mul_pow, Real.sqrt_mul (by positivity), Real.sqrt_sq hlp, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

end GlobalTheory.RadCov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolumeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_integral_points_covolume : RadicalCovolume := by
  first | exact @GlobalTheory.RadCov.radicalCovolume | exact GlobalTheory.RadCov.radicalCovolume | (intros; apply GlobalTheory.RadCov.radicalCovolume <;> assumption)
end
