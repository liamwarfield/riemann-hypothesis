module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

def SpComp : Prop :=
  ∀ (E : Type) [Field E] (k m : ℕ) (P : Matrix (Fin k) (Fin m) E) (R : Matrix (Fin m) (Fin k) E), P * R = 1 →
    k ≤ m ∧ ∃ U : Matrix (Fin m) (Fin (m - k)) E, P * U = 0 ∧ Function.Injective U.mulVec ∧
      ∀ w : Fin m → E, P *ᵥ w = 0 → ∃ y, U *ᵥ y = w

def SpDen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (X : Matrix (Fin k) (Fin k) E), ∃ D : ℕ, 1 ≤ D ∧
    ∀ i j, (D : E) * X i j ∈ (algebraMap (𝓞 E) E).range

def SpLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k n d D : ℕ) (J : Matrix (Fin m) (Fin m) E)
    (M : Submodule (𝓞 E) (Fin m → E)) (V : Matrix (Fin m) (Fin k) E) (U : Matrix (Fin m) (Fin n) E),
    (J, M) ∈ Lat E m d → (∀ i, (fun r => V r i) ∈ M) → 1 ≤ D →
    (cT (starRingEnd E) V * J * V).det ≠ 0 →
    (∀ i j, (D : E) * (cT (starRingEnd E) V * J * V)⁻¹ i j ∈ (algebraMap (𝓞 E) E).range) →
    cT (starRingEnd E) V * J * U = 0 → Function.Injective U.mulVec →
    (∀ w : Fin m → E, (cT (starRingEnd E) V * J) *ᵥ w = 0 → ∃ y, U *ᵥ y = w) →
    (cT (starRingEnd E) U * J * U, M.comap ((Matrix.mulVecLin U).restrictScalars (𝓞 E))) ∈ Lat E n (d * D) ∧
    ∀ z ∈ M, ∃ c : Fin k → E, (∀ i, c i ∈ (algebraMap (𝓞 E) E).range) ∧ ∃ y : Fin n → E, U *ᵥ y ∈ M ∧
      (D : E) • z = V *ᵥ c + U *ᵥ y

def SpOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (m k : ℕ), 1 ≤ k → (∀ j < m, HL E j) →
    ∀ d : ℕ, 1 ≤ d → ∀ Γ : Matrix (Fin k) (Fin k) E, Γ.det ≠ 0 → FinCl (SplitSet E m k d {Γ})

theorem partSplit_of_one (h : SpOne) : PartSplit := by
  unfold PartSplit
  unfold SpOne at h
  intro F E _ _ _ _ _ _ _ m k hk hHL d hd G hG hdet

  have h1 : ∀ Γ ∈ G, FinCl (SplitSet E m k d {Γ}) := fun Γ hΓ => h E m k hk hHL d hd Γ (hdet Γ hΓ)
  choose T hTfin hT using h1
  refine ⟨⋃ (Γ) (hΓ : Γ ∈ G), T Γ hΓ, hG.biUnion' hTfin, ?_⟩
  rintro p ⟨hpL, v, hv, hvG⟩
  obtain ⟨q, hq, hiso⟩ := hT _ hvG p ⟨hpL, v, hv, Set.mem_singleton _⟩
  exact ⟨q, Set.mem_iUnion₂.mpr ⟨_, hvG, hq⟩, hiso⟩

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HmkFactor
noncomputable section

namespace PIW.AdelClassFin

open MeasureTheory Matrix Module
open scoped MatrixOrder

theorem hmk_factor {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.PosDef) :
    ∃ B : Matrix (Fin N) (Fin N) ℝ, G = Bᵀ * B := by
  refine ⟨CFC.sqrt G, ?_⟩
  have h0 : (0 : Matrix (Fin N) (Fin N) ℝ) ≤ G := hG.posSemidef.nonneg
  have hsa : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]

theorem hmk_int {N : ℕ} (x : Fin N → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin N)))) :
    ∃ c : Fin N → ℤ, (fun i => (c i : ℝ)) = x := by
  rw [(Pi.basisFun ℝ (Fin N)).mem_span_iff_repr_mem (R := ℤ) x] at hx
  choose c hc using hx
  refine ⟨c, funext fun i => ?_⟩
  have := hc i
  simp only [Pi.basisFun_repr, algebraMap_int_eq, Int.coe_castRingHom] at this
  exact this

theorem hmk_box {N : ℕ} (hN : 1 ≤ N) (B : Matrix (Fin N) (Fin N) ℝ) (hB : B.det ≠ 0) :
    ∃ c : Fin N → ℤ, c ≠ 0 ∧
      ∀ i, |(B *ᵥ fun j => (c j : ℝ)) i| ≤ 2 * |B.det| ^ ((1 : ℝ) / N) := by
  set d := |B.det| with hd
  have hd0 : 0 < d := abs_pos.mpr hB
  set t := 2 * d ^ ((1 : ℝ) / N) with ht
  have ht0 : 0 < t := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have htN : t ^ N = 2 ^ N * d := by
    rw [ht, mul_pow, ← Real.rpow_natCast (d ^ _), ← Real.rpow_mul hd0.le]
    rw [one_div_mul_cancel hN0, Real.rpow_one]
  let f : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := Matrix.toLin' B
  have hf : LinearMap.det f ≠ 0 := by rw [LinearMap.det_toLin']; exact hB
  let box : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-t) t
  let s : Set (Fin N → ℝ) := f ⁻¹' box
  let b := Pi.basisFun ℝ (Fin N)
  have fund := ZSpan.isAddFundamentalDomain' b (volume : Measure (Fin N → ℝ))
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp
  have hvolbox : volume box = ENNReal.ofReal (2 * t) ^ N := by
    simp only [box]
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hvols : volume s = ENNReal.ofReal (4 ^ N) := by
    simp only [s]
    rw [MeasureTheory.Measure.addHaar_preimage_linearMap _ hf, hvolbox,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [LinearMap.det_toLin', abs_inv, ← hd, mul_pow, htN]
    rw [show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N by rw [← mul_pow]; norm_num]
    field_simp
  have h_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      map_neg, Pi.neg_apply] at hx ⊢
    intro i
    obtain ⟨h1, h2⟩ := hx i
    constructor <;> linarith
  have h_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Icc (-t) t).linear_preimage f
  have h : volume (ZSpan.fundamentalDomain b) * 2 ^ finrank ℝ (Fin N → ℝ) < volume s := by
    rw [hvolF, one_mul, hvols, Module.finrank_fin_fun]
    rw [show (2 : ENNReal) ^ N = ENNReal.ofReal (2 ^ N) by
      rw [ENNReal.ofReal_pow (by norm_num)]; simp]
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range b)))
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund h_symm h_conv h
  obtain ⟨c, hc⟩ := hmk_int (x : Fin N → ℝ) x.2
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply hx0
    ext i
    have := congrFun hc i
    simp at this
    simp [← this]
  · intro i
    have := hxs
    simp only [s, box, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc] at this
    rw [hc]
    exact abs_le.mpr (this i)

theorem partMink : PartMink := by
  intro N hN
  refine ⟨4 * N, fun G hG => ?_⟩
  obtain ⟨B, rfl⟩ := hmk_factor G hG
  have hdet : (Bᵀ * B).det = B.det ^ 2 := by rw [det_mul, det_transpose, sq]
  have hpos := hG.det_pos
  have hB : B.det ≠ 0 := by
    intro h0; rw [hdet, h0] at hpos; simp at hpos
  obtain ⟨c, hc0, hc⟩ := hmk_box hN B hB
  refine ⟨c, hc0, ?_⟩
  set v : Fin N → ℝ := fun i => (c i : ℝ)
  set d := |B.det|
  have hd0 : 0 < d := abs_pos.mpr hB
  have hq : v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = ∑ i, (B *ᵥ v) i ^ 2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, sq]
  have hdetG : (Bᵀ * B).det = d ^ 2 := by rw [hdet, sq_abs]
  have hpow : (d ^ ((1 : ℝ) / N)) ^ 2 = (d ^ 2) ^ ((1 : ℝ) / N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast d, ← Real.rpow_mul hd0.le, ← Real.rpow_mul hd0.le,
      mul_comm]
  rw [hq, hdetG, ← hpow]
  calc ∑ i, (B *ᵥ v) i ^ 2 ≤ ∑ _i : Fin N, (2 * d ^ ((1 : ℝ) / N)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq' (abs_le.mp (hc i)).1 (abs_le.mp (hc i)).2
    _ = 4 * N * (d ^ ((1 : ℝ) / N)) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ]; ring

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix ComplexOrder

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gramTr {m N : ℕ} (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))

def IsMajFam {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ φ : E →+* ℂ, (H φ).PosDef ∧ (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ) ∧
    (∀ z : Fin m → ℂ, ‖star z ⬝ᵥ (J.map φ *ᵥ z)‖ ≤ (star z ⬝ᵥ (H φ *ᵥ z)).re) ∧
    H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)

end Defs

def SvCodiffAt (E : Type) [Field E] [NumberField E] (δ : ℕ) : Prop :=
  ∀ y : E, (∀ a : 𝓞 E, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * y) ∈ (algebraMap ℤ ℚ).range) →
    (δ : E) * y ∈ (algebraMap (𝓞 E) E).range

def SvCodiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ δ : ℕ, 1 ≤ δ ∧ SvCodiffAt E δ

def SvMaj : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.IsHermitian → J.det ≠ 0 →
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ H.det = ((‖J.det‖ : ℝ) : ℂ) ∧
      ∀ z : Fin n → ℂ, ‖star z ⬝ᵥ (J *ᵥ z)‖ ≤ (star z ⬝ᵥ (H *ᵥ z)).re

def SvMajE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J → J.det ≠ 0 →
      ∃ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H

def SvBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (M : Submodule (𝓞 E) (Fin m → E)),
    M.FG → Submodule.span E (M : Set (Fin m → E)) = ⊤ →
      ∃ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e ∧ (∀ i, e i ∈ M) ∧
        ∀ x ∈ M, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i

def SvGramDet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ m d δ : ℕ, 1 ≤ d → 1 ≤ δ → SvCodiffAt E δ → ∀ p ∈ Lat E m d,
      ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e → (∀ i, e i ∈ p.2) →
        (∀ x ∈ p.2, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i) →
          (gramTr p.1 e).det ≠ 0 ∧ |(gramTr p.1 e).det| ≤ ((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E)

def SvReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J →
      ∀ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H →
        ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, (gramTr J e).det ≠ 0 →
          ∃ R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ,
            R.PosDef ∧ R.det = |((gramTr J e).det : ℝ)| ∧
              ∀ c : Fin (m * Module.finrank ℚ E) → ℤ,
                ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖ ≤
                  (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ))

theorem partShort_of (hM : PartMink) (hMaj : SvMajE) (hCod : SvCodiff) (hB : SvBasis)
    (hD : SvGramDet) (hR : SvReal) : PartShort := by
  intro F E _ _ _ _ _ _ hCM m d hm hd
  obtain ⟨δ, hδ1, hδ⟩ := hCod E
  have hn1 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN1 : 1 ≤ m * Module.finrank ℚ E :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨Kc, hK⟩ := hM _ hN1
  set S : ℝ := max Kc 0 * ((d * δ : ℕ) : ℝ) with hS
  refine ⟨((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℚ), fun p hp => ?_⟩
  obtain ⟨hherm, hdet, hfg, hspan, -, -⟩ := id hp
  obtain ⟨H, hH⟩ := hMaj F E hCM m p.1 hherm hdet
  obtain ⟨e, hlin, hemem, hegen⟩ := hB E m p.2 hfg hspan
  obtain ⟨hgd, hgb⟩ := hD F E hCM m d δ hd hδ1 hδ p hp e hlin hemem hegen
  obtain ⟨R, hRpd, hRdet, hRle⟩ := hR F E hCM m p.1 hherm H hH e hgd
  obtain ⟨c, hc0, hcR⟩ := hK R hRpd
  set x : Fin m → E := ∑ i, (c i : E) • e i with hx
  have hxmem : x ∈ p.2 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul E]
    exact p.2.toAddSubgroup.zsmul_mem (hemem i) (c i)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have h0' : ∑ i, (c i : ℚ) • e i = 0 := by
      rw [← h0, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul E]
    exact_mod_cast Fintype.linearIndependent_iff.1 hlin _ h0' i
  refine ⟨x, hxmem, hx0, ?_⟩
  set a := hform (starRingEnd E) p.1 x x with ha
  have hsumle : ∑ φ : E →+* ℂ, ‖φ a‖ ≤ S := by
    have h1 := hRle c
    have hdetR : R.det ≤ ((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E) := by
      rw [hRdet]
      have h' : ((|(gramTr p.1 e).det| : ℚ) : ℝ) ≤
          ((((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E) : ℚ) : ℝ) := by exact_mod_cast hgb
      rw [Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast] at h'
      exact h'
    have hR0 : 0 ≤ R.det := hRpd.det_pos.le
    have hroot : R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) ≤ ((d * δ : ℕ) : ℝ) := by
      calc R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ))
          ≤ (((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E)) ^
              ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hR0 hdetR (by positivity)
        _ = ((d * δ : ℕ) : ℝ) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    have hroot0 : 0 ≤ R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := Real.rpow_nonneg hR0 _
    calc ∑ φ : E →+* ℂ, ‖φ a‖ ≤ _ := h1
      _ ≤ Kc * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := hcR
      _ ≤ max Kc 0 * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hroot0
      _ ≤ S := mul_le_mul_of_nonneg_left hroot (le_max_right _ _)
  have hnorm : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ S ^ Module.finrank ℚ E := by
    have h2 := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
    simp only [norm_prod] at h2
    rw [show ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ a)‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| by simp] at h2
    rw [Rat.cast_abs, h2]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ ≤ ∏ σ : E →ₐ[ℚ] ℂ, S :=
          Finset.prod_le_prod₀ (fun σ _ => norm_nonneg _) (fun σ _ =>
            (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ a‖) (fun φ _ => norm_nonneg _)
              (Finset.mem_univ (σ : E →+* ℂ))).trans hsumle)
      _ = S ^ Module.finrank ℚ E := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ E ℂ]
  have hfin : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ ((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℝ) :=
    hnorm.trans (Nat.le_ceil _)
  exact_mod_cast hfin

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors

namespace DictInter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def tau (w : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ
    TensorProduct.map ((Algebra.trace F E) ∘ₗ LinearMap.mulLeft F w) LinearMap.id

lemma tau_tmul (w e : E) (a : Af F) : tau w (e ⊗ₜ[F] a) = Algebra.trace F E (w * e) • a := by
  first
    | simp [tau]
    | rfl


variable (F E) in
def dualSet : Set E := {w | ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range}

lemma tau_mul_left (w a : E) (r : E ⊗[F] Af F) :
    tau w ((a ⊗ₜ[F] (1 : Af F)) * r) = tau (w * a) r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_assoc]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy]

lemma tau_mul_right (w : E) (b : Af F) (r : E ⊗[F] Af F) :
    tau w (((1 : E) ⊗ₜ[F] b) * r) = b * tau w r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, tau_tmul, tau_tmul, mul_smul_comm]
  | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]

lemma tau_incl (w e : E) :
    tau w (Formalism.UG.inclE (F := F) (Af F) e) = algebraMap F (Af F) (Algebra.trace F E (w * e)) := by
  show tau w (e ⊗ₜ[F] (1 : Af F)) = _
  rw [tau_tmul, Algebra.algebraMap_eq_smul_one]

lemma algebraMap_mem_intAd (x : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F x) ∈ Formalism.UG.intAd F := by
  intro v
  have h1 : Valued.v (((algebraMap (𝓞 F) F x : F)) : v.adicCompletion F) ≤ 1 := by
    first
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
      | rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
        first
          | exact v.valuation_le_one x
          | exact v.valuation_le_one F x
  first
    | exact h1
    | exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h1

lemma of_algebraMap_mem_intAd (f : F) (h : algebraMap F (Af F) f ∈ Formalism.UG.intAd F) :
    f ∈ (algebraMap (𝓞 F) F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) f ?_
  intro v
  have hv : Valued.v ((f : F) : v.adicCompletion F) ≤ 1 := h v
  first
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    | rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at hv

def tSet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Set (E ⊗[F] Af F) :=
  {r | ∀ w ∈ dualSet F E, tau w r ∈ Formalism.UG.intAd F}

lemma one_mem_tSet : (1 : E ⊗[F] Af F) ∈ tSet F E := by
  show ∀ w ∈ dualSet F E, tau w ((1 : E) ⊗ₜ[F] (1 : Af F)) ∈ Formalism.UG.intAd F
  intro w hw
  have hw1 := (show ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range from hw) 1
  obtain ⟨x, hx⟩ := hw1
  rw [tau_tmul, ← Algebra.algebraMap_eq_smul_one]
  have hx' : Algebra.trace F E (w * (1 : E)) = algebraMap (𝓞 F) F x := by
    rw [hx]
    rfl
  rw [hx']
  exact algebraMap_mem_intAd x

private theorem mul_algebraMap_mem_dualSet {w : E} (hw : w ∈ dualSet F E) (a : 𝓞 E) :
    w * algebraMap (𝓞 E) E a ∈ dualSet F E := by
  show ∀ b : 𝓞 E, Algebra.trace F E (w * algebraMap (𝓞 E) E a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
  intro b
  have h := (show ∀ b : 𝓞 E, Algebra.trace F E (w * (b : E)) ∈ (algebraMap (𝓞 F) F).range from hw) (a * b)
  rw [mul_assoc]
  exact h

lemma mem_tSet (r : E ⊗[F] Af F) (hr : r ∈ IntAf F E) : r ∈ tSet F E := by
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  suffices h : ∀ s ∈ tSet F E, r * s ∈ tSet F E by
    have h1 := h 1 one_mem_tSet
    rwa [mul_one] at h1
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
    · obtain ⟨a, rfl⟩ := he
      intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_left]
      exact (show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) _ (mul_algebraMap_mem_dualSet hw a)
    · intro s hs
      show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
      intro w hw
      rw [tau_mul_right]
      exact mul_mem hb ((show ∀ w ∈ dualSet F E, tau w s ∈ Formalism.UG.intAd F from hs) w hw)
  | zero =>
    intro s _
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w _
    rw [zero_mul, map_zero]
    exact zero_mem _
  | one =>
    intro s hs
    rwa [one_mul]
  | add x y _ _ hx hy =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [add_mul, map_add (f := _)]
    exact add_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
      ((show ∀ w ∈ dualSet F E, tau w (y * s) ∈ Formalism.UG.intAd F from hy s hs) w hw)
  | neg x _ hx =>
    intro s hs
    show ∀ w ∈ dualSet F E, tau w _ ∈ Formalism.UG.intAd F
    intro w hw
    rw [neg_mul, map_neg]
    exact neg_mem ((show ∀ w ∈ dualSet F E, tau w (x * s) ∈ Formalism.UG.intAd F from hx s hs) w hw)
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_assoc]
    exact hx _ (hy s hs)

end DictInter

open DictInter in
theorem dual_intersection : DInter := by
  intro F E _ _ _ _ _ e he
  have ht := mem_tSet (F := F) (E := E) _ he
  have key : ∀ w ∈ dualSet F E, Algebra.trace F E (w * e) ∈ (algebraMap (𝓞 F) F).range := by
    intro w hw
    apply of_algebraMap_mem_intAd
    rw [← tau_incl]
    exact (show ∀ w ∈ dualSet F E, tau w (Formalism.UG.inclE (F := F) (Af F) e) ∈ Formalism.UG.intAd F from ht) w hw
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    first
      | exact FractionalIdeal.dual_ne_zero (𝓞 F) F h1
      | exact FractionalIdeal.dual_ne_zero h1
  have hmem : e ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    rw [Algebra.traceForm_apply, mul_comm]
    apply key
    show ∀ b : 𝓞 E, Algebra.trace F E (a * (b : E)) ∈ (algebraMap (𝓞 F) F).range
    intro b
    have hb := ha (b : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨b, rfl⟩)
    rwa [Algebra.traceForm_apply] at hb
  rw [FractionalIdeal.dual_dual] at hmem
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  exact ⟨x, hx⟩

end PIW.AdelClassFin
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictGen
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix

namespace DictGen

variable (I : AutInst)

theorem lf_eq : I.Lf = Submodule.span (IntAf I.F I.E)
    (Set.range fun x : I.L => iv I (x : Fin I.n → I.E)) := rfl

theorem iv_mem {l : Fin I.n → I.E} (hl : l ∈ I.L) : iv I l ∈ I.Lf := by
  rw [lf_eq]
  exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩

theorem natSmul_mem (k : ℕ) {w : Fin I.n → I.E ⊗[I.F] Af I.F} (hw : w ∈ I.Lf) :
    (k : I.E ⊗[I.F] Af I.F) • w ∈ I.Lf := by
  first
    | rw [Nat.cast_smul_eq_nsmul (I.E ⊗[I.F] Af I.F)]
      exact nsmul_mem hw k
    | rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hw k
    | exact I.Lf.smul_mem (k : IntAf I.F I.E) hw

theorem iv_nsmul (N : ℕ) (v : Fin I.n → I.E) :
    iv I (N • v) = (N : I.E ⊗[I.F] Af I.F) • iv I v := by
  funext i
  first
    | simp [iv, nsmul_eq_mul]
    | simp only [iv, Pi.smul_apply, map_nsmul, nsmul_eq_mul, smul_eq_mul]

theorem natCast_cancel (N : ℕ) (hN : 0 < N) {a b : Fin I.n → I.E ⊗[I.F] Af I.F}
    (h : (N : I.E ⊗[I.F] Af I.F) • a = (N : I.E ⊗[I.F] Af I.F) • b) : a = b := by
  have hu : IsUnit (N : (I.E ⊗[I.F] Af I.F)) := by
    have h0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
    have h1 := (IsUnit.mk0 _ h0).map (algebraMap I.F (I.E ⊗[I.F] Af I.F))
    rwa [map_natCast] at h1
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact hu.mul_left_cancel hi

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  first
    | exact Units.mul_inv (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  first
    | exact Units.inv_mul (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    | simp

def lamM (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Submodule (𝓞 I.E) (Fin I.n → I.E) where
  carrier := {v | M *ᵥ iv I v ∈ I.Lf}
  add_mem' := fun {v w} hv hw => by
    have e : iv I (v + w) = iv I v + iv I w := by
      funext i; simp [iv]
    show M *ᵥ iv I (v + w) ∈ I.Lf
    rw [e, Matrix.mulVec_add]
    exact I.Lf.add_mem hv hw
  zero_mem' := by
    have e : iv I (0 : Fin I.n → I.E) = 0 := by
      funext i; simp [iv]
    show M *ᵥ iv I 0 ∈ I.Lf
    rw [e, Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  smul_mem' := fun a v hv => by
    have ha : Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) ∈ IntAf I.F I.E :=
      Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
    have e : iv I (a • v) = Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E) • iv I v := by
      funext i
      simp [iv, Algebra.smul_def]
    show M *ᵥ iv I (a • v) ∈ I.Lf
    rw [e, Matrix.mulVec_smul]
    exact I.Lf.smul_mem ⟨_, ha⟩ hv

theorem mulVec_mem_of_le {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (h : I.L ≤ lamM I M) :
    ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  rw [lf_eq] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    exact (show M *ᵥ iv I l ∈ I.Lf from h hl)
  | zero =>
    rw [Matrix.mulVec_zero]
    exact I.Lf.zero_mem
  | add a b _ _ ha hb =>
    rw [Matrix.mulVec_add]
    exact I.Lf.add_mem ha hb
  | smul s a _ ha =>
    have e : M *ᵥ (s • a) = s • (M *ᵥ a) := by
      show M *ᵥ ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • (M *ᵥ a)
      exact Matrix.mulVec_smul M _ a
    rw [e]
    exact I.Lf.smul_mem s ha

private theorem smul_mulVec_lemma {A : Type} [CommRing A] {n : ℕ} (c : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) : (c • M) *ᵥ y = c • (M *ᵥ y) := by
  first
    | exact Matrix.smul_mulVec c M y
    | exact Matrix.smul_mulVec_assoc c M y
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

theorem denom (hD : LDenom) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (M *ᵥ y) ∈ I.Lf := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hm using fun v : Fin I.n → I.E => hD I (M *ᵥ iv I v)
  refine ⟨∏ j ∈ s, m j, Finset.prod_pos fun j _ => hm0 j, ?_⟩
  have hle : I.L ≤ lamM I (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    show (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) *ᵥ iv I v ∈ I.Lf
    rw [smul_mulVec_lemma, ← Finset.prod_erase_mul s m hv, Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hm v)
  intro y hy
  have h2 := mulVec_mem_of_le I hle y hy
  rwa [smul_mulVec_lemma] at h2

theorem exists_denominator_fmat (hD : LDenom) (x : I.Gf) : ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf,
    (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf := by
  obtain ⟨N1, h1, hN1⟩ := denom I hD (I.fmat x)
  obtain ⟨N2, h2, hN2⟩ := denom I hD (I.fmat x⁻¹)
  refine ⟨N1 * N2, Nat.mul_pos h1 h2, fun y hy => ⟨?_, ?_⟩⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact natSmul_mem I _ (hN1 y hy)
  · rw [Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hN2 y hy)

theorem nL_sub (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {l : Fin I.n → I.E} (hl : l ∈ I.L) : N • l ∈ abelian₂ I x := by
  show I.fmat x⁻¹ *ᵥ iv I (N • l) ∈ I.Lf
  rw [iv_nsmul, Matrix.mulVec_smul]
  exact (hN _ (iv_mem I hl)).2

theorem nLam_sub (hInt : LInter) (x : I.Gf) (N : ℕ)
    (hN : ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ y) ∈ I.Lf ∧
      (N : I.E ⊗[I.F] Af I.F) • (I.fmat x⁻¹ *ᵥ y) ∈ I.Lf)
    {v : Fin I.n → I.E} (hv : v ∈ abelian₂ I x) : N • v ∈ I.L := by
  apply hInt I
  have hv' : I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf := hv
  have e : iv I v = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ iv I v) := by
    rw [Matrix.mulVec_mulVec, fmat_mul_inv, Matrix.one_mulVec]
  rw [iv_nsmul, e]
  exact (hN _ hv').1

end DictGen

theorem mLat_of (hInt : LInter) (hD : LDenom) : MLat := by
  intro I x
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · let ψ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
      (((N : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
    have hle : abelian₂ I x ≤ I.L.map ψ := by
      intro v hv
      have h1 : N • v ∈ I.L := DictGen.nLam_sub I hInt x N hN' hv
      have e : ψ (N • v) = v := by
        show (N : I.E)⁻¹ • (N • v) = v
        rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
      rw [← e]
      exact Submodule.mem_map_of_mem h1
    haveI : IsNoetherian (𝓞 I.E) (I.L.map ψ) := isNoetherian_of_fg_of_noetherian _ (I.L_fg.map ψ)
    haveI : IsNoetherian (𝓞 I.E) (abelian₂ I x) := isNoetherian_of_le hle
    first
      | exact (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
      | exact Module.Finite.iff_fg.mp inferInstance
  · rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro v hv
    have h1 : N • v ∈ abelian₂ I x := DictGen.nL_sub I x N hN' hv
    have h2 : N • v ∈ Submodule.span I.E
        ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) :=
      Submodule.subset_span h1
    have e : v = (N : I.E)⁻¹ • (N • v) := by
      rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ h2

theorem mGen_of (hD : LDenom) (hDen : LDense) : MGen := by
  intro I x y hy
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNL : ∀ u ∈ I.Lf, (N : (I.E ⊗[I.F] Af I.F)) • u ∈
      Submodule.span (IntAf I.F I.E) (Set.range fun v : abelian₂ I x => iv I (v : Fin I.n → I.E)) := by
    intro u hu
    rw [DictGen.lf_eq] at hu
    induction hu using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hz
      show (N : (I.E ⊗[I.F] Af I.F)) • iv I l ∈ _
      rw [← DictGen.iv_nsmul]
      exact Submodule.subset_span ⟨⟨N • l, DictGen.nL_sub I x N hN' hl⟩, rfl⟩
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    | smul s a _ ha =>
      have e : (N : (I.E ⊗[I.F] Af I.F)) • (s • a) = s • ((N : (I.E ⊗[I.F] Af I.F)) • a) := by
        show (N : (I.E ⊗[I.F] Af I.F)) • ((s : (I.E ⊗[I.F] Af I.F)) • a) = (s : (I.E ⊗[I.F] Af I.F)) • ((N : (I.E ⊗[I.F] Af I.F)) • a)
        rw [smul_smul, smul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ s ha
  obtain ⟨l, hl, y', hy', hw⟩ := hDen I (N * N) (Nat.mul_pos hN hN) _ (hN' y hy).1
  obtain ⟨v, hv⟩ : ∃ v : Fin I.n → I.E, v = (N : I.E)⁻¹ • l := ⟨_, rfl⟩
  have hNv : N • v = l := by
    rw [hv, ← Nat.cast_smul_eq_nsmul I.E, smul_smul, mul_inv_cancel₀ hNE, one_smul]
  have hz : I.fmat x *ᵥ y = iv I v + (N : (I.E ⊗[I.F] Af I.F)) • y' := by
    apply DictGen.natCast_cancel I N hN
    rw [smul_add, ← DictGen.iv_nsmul, hNv, hw, smul_smul, Nat.cast_mul]
  have hvL : v ∈ abelian₂ I x := by
    show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf
    have e : iv I v = I.fmat x *ᵥ y - (N : (I.E ⊗[I.F] Af I.F)) • y' := by
      first
        | rw [hz, add_sub_cancel_right]
        | (rw [hz]; abel)
    rw [e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, DictGen.fmat_inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_smul]
    exact I.Lf.sub_mem hy (hN' y' hy').2
  rw [hz]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨⟨v, hvL⟩, rfl⟩) (hNL y' hy')

end PIW.AdelClassFin
end
end
