module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameSpanCompletedEigenLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbedding
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false
namespace GlobalTheory.ConjHostChar

theorem embK_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ (H.bar a) = embK c (conjEmb τ) a := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, conjEmb, RingHom.comp_apply]
  rw [← ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  simp

theorem conj_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ a, ((t.comp (H.bar : 𝓞 E →+* 𝓞 E) a : 𝓞 K) : K) = algebraMap c.F K (embK c (conjEmb τ.1) a) := by
  intro E _ _ _ H Dw l Xo c τ K _ _ _ t ht a
  rw [RingHom.comp_apply, ht]
  exact congrArg _ (embK_bar H c τ.1 a)

end GlobalTheory.ConjHostChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostIntegerCharacterCompConjEqConjEmbeddingStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostIntegerCharacter_comp_conj_eq_conjEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ a, ((t.comp (H.bar : 𝓞 E →+* 𝓞 E) a : 𝓞 K) : K) = algebraMap c.F K (embK c (conjEmb τ.1) a) := by
  first | exact @GlobalTheory.ConjHostChar.conj_char | exact GlobalTheory.ConjHostChar.conj_char | (intros; apply GlobalTheory.ConjHostChar.conj_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionConstValuationEigenLatticeAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChange
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.FlatChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) = if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  classical
  show (wtOf Dw (flatWt Dw τ) 0).1 (σ, (i : ℕ)) = _
  have hi := i.2
  by_cases h : σ (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_big (flatWt Dw τ) 0 ⟨σ, h⟩ i hp
    refine e0.trans ?_
    have hne : σ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
    by_cases e : σ = τ.1
    · have : (⟨σ, h⟩ : Psi H) = τ := Subtype.ext e
      simp [flatWt, parWt, this, e]
    · have : (⟨σ, h⟩ : Psi H) ≠ τ := fun e' => e (congrArg Subtype.val e')
      simp [flatWt, parWt, this, e, hne]
  · have h' := conj_mem h
    have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb σ, h'⟩ i hq
    simp only [Formalism.L2.Pj.conjEmb_conjEmb] at e0
    refine e0.trans ?_
    have hne : σ ≠ τ.1 := fun e' => h (e' ▸ τ.2)
    have hiff : (⟨conjEmb σ, h'⟩ : Psi H) = τ ↔ σ = conjEmb τ.1 := by
      constructor
      · intro e'; rw [← congrArg Subtype.val e', Formalism.L2.Pj.conjEmb_conjEmb]
      · intro e'; apply Subtype.ext; show conjEmb σ = τ.1; rw [e', Formalism.L2.Pj.conjEmb_conjEmb]
    by_cases e : σ = conjEmb τ.1
    · have h2 := hiff.2 e
      rw [if_neg hne, if_pos e]
      simp only [flatWt, parWt, if_pos h2]
      norm_num
    · have : (⟨conjEmb σ, h'⟩ : Psi H) ≠ τ := fun e' => e (hiff.1 e')
      simp [flatWt, parWt, this, e, hne]

theorem flatWt_char (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ) :
    (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) =
      ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  have key : (∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i) =
      (∏ i : Fin (Dw.mult τ.1), t (some ⟨τ.1, i⟩))⁻¹ * ∏ j : Fin (Dw.mult (conjEmb τ.1)), t (some ⟨conjEmb τ.1, j⟩) := by
    rw [Fintype.prod_option, Fintype.prod_sigma]
    have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
    rw [h0, zpow_zero, one_mul]
    rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_]
    · congr 1
      · rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_pos rfl, zpow_neg_one]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_neg hne.symm, if_pos rfl, zpow_one]
    · rintro σ ⟨h1, h2⟩
      refine Finset.prod_eq_one fun i _ => ?_
      rw [exOf_flatWt_some, if_neg h1, if_neg h2, zpow_zero]
  rw [key, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  rw [mul_comm, mul_inv_cancel_left]

end GlobalTheory.FlatChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChangeStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLineWeight_character_triangular_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ), (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  first | exact @GlobalTheory.FlatChar.flatWt_char | exact GlobalTheory.FlatChar.flatWt_char | (intros; apply GlobalTheory.FlatChar.flatWt_char <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMul
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

open scoped WithZero

namespace GlobalTheory.CdvrPlaceVal

theorem mem_range_iff_valV_le_one (T : CDVR) (x : T.Fr) :
    x ∈ Set.range (algebraMap T.V T.Fr) ↔ valV T.V x ≤ 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact HeightOneSpectrum.valuation_le_one _ v
  · intro hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (IsDiscreteValuationRing.maximalIdeal T.V) x hx
    have hu : IsUnit (d : T.V) := by
      by_contra hu
      exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 hu)
    obtain ⟨u, hu⟩ := hu
    refine ⟨n * ↑u⁻¹, ?_⟩
    rw [map_mul, ← hnd, ← hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

theorem vV_eq_mul_vAdd (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR)
    (iK : K →+* T.Fr)
    (h : ∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) :
    ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  let v1 : Valuation K ℤᵐ⁰ := (valV T.V).comap iK
  have hv1 : ∀ z, v1 z = valV T.V (iK z) := fun z => rfl
  have hle : ∀ z : K, v1 z ≤ 1 ↔ 𝔓.valuation K z ≤ 1 := fun z => by
    rw [← h z, mem_range_iff_valV_le_one, hv1]
  have hunit : ∀ w : K, 𝔓.valuation K w = 1 → v1 w = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    have h0 : v1 w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    have h1 : v1 w ≤ 1 := (hle w).2 hw.le
    have h2 : v1 w⁻¹ ≤ 1 := (hle w⁻¹).2 (by rw [map_inv₀, hw, inv_one])
    rw [map_inv₀] at h2
    have h1' := (WithZero.log_le_log h0 one_ne_zero).2 h1
    have h2' := (WithZero.log_le_log (inv_ne_zero h0) one_ne_zero).2 h2
    rw [WithZero.log_inv, WithZero.log_one] at h2'
    rw [WithZero.log_one] at h1'
    rw [← WithZero.exp_log h0, show WithZero.log (v1 w) = 0 by omega]
    rfl
  obtain ⟨ϖ, hϖ⟩ := 𝔓.valuation_exists_uniformizer K
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hv1ϖ0 : v1 ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hlt : v1 ϖ < 1 := by
    have hle1 : v1 ϖ ≤ 1 := (hle ϖ).2 (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)
    refine lt_of_le_of_ne hle1 fun heq => ?_
    have h3 : v1 ϖ⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
    have h4 := (hle ϖ⁻¹).1 h3
    rw [map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg] at h4
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h4
    norm_num at h4
  have ha : 0 < vV T.V (iK ϖ) := by
    have h5 : WithZero.log (v1 ϖ) < WithZero.log 1 := (WithZero.log_lt_log hv1ϖ0 one_ne_zero).2 hlt
    rw [WithZero.log_one, hv1] at h5
    simp only [vV]
    omega
  refine ⟨(vV T.V (iK ϖ)).toNat, by omega, fun z => ?_⟩
  rw [Int.toNat_of_nonneg ha.le]
  by_cases hz : z = 0
  · subst hz; simp [vV, vAdd]
  have hz2 : 𝔓.valuation K z = WithZero.exp (-vAdd 𝔓 z) := by
    simp only [vAdd, neg_neg]; exact (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hz)).symm
  have hw : 𝔓.valuation K (z * ϖ ^ (-vAdd 𝔓 z)) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hz2, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu := hunit _ hw
  have hz' : z = (z * ϖ ^ (-vAdd 𝔓 z)) * ϖ ^ (vAdd 𝔓 z) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0]; simp
  have hv : v1 z = v1 ϖ ^ (vAdd 𝔓 z) := by
    conv_lhs => rw [hz']
    rw [map_mul, hu, one_mul, map_zpow₀]
  have e1 : vV T.V (iK z) = -WithZero.log (v1 z) := rfl
  have e2 : vV T.V (iK ϖ) = -WithZero.log (v1 ϖ) := rfl
  rw [e1, e2, hv, WithZero.log_zpow, smul_eq_mul]
  ring

end GlobalTheory.CdvrPlaceVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMulStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  first | exact @GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | exact GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | (intros; apply GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtComplet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetN
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetN
open Matrix

namespace GlobalTheory
namespace IwasawaLowerTri

variable (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F]

lemma permMatrix_map {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix V).map (algebraMap V F) = σ.permMatrix F := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

lemma permMatrix_mul_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (σ.permMatrix F * A) i j = A (σ i) j := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]

lemma isUnit_det_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsUnit (σ.permMatrix V).det := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma exists_max_val {n : ℕ} (c : Fin (n+1) → F) :
    ∃ i0, ∀ i, ValuationRing.valuation V F (c i) ≤ ValuationRing.valuation V F (c i0) := by
  obtain ⟨i0, -, h⟩ := Finset.exists_max_image Finset.univ (fun i => ValuationRing.valuation V F (c i)) Finset.univ_nonempty
  exact ⟨i0, fun i => h i (Finset.mem_univ _)⟩

lemma integral_of_val_le (x y : F) (hy : y ≠ 0)
    (h : ValuationRing.valuation V F x ≤ ValuationRing.valuation V F y) :
    ∃ q : V, algebraMap V F q = x / y := by
  rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, Valuation.map_div]
  have : ValuationRing.valuation V F y ≠ 0 := by simpa using hy
  exact (div_le_one₀ (zero_lt_iff.mpr this)).mpr h

lemma clear_last_column {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) F) :
    ∃ P : Matrix (Fin (n+1)) (Fin (n+1)) V, IsUnit P.det ∧
      ∀ i : Fin n, (P.map (algebraMap V F) * A) i.castSucc (Fin.last n) = 0 := by
  by_cases hz : ∀ i, A i (Fin.last n) = 0
  · refine ⟨1, by simp, fun i => ?_⟩
    simp [hz]
  push_neg at hz
  obtain ⟨i1, hi1⟩ := hz
  obtain ⟨i0, hmax⟩ := exists_max_val V F (fun i => A i (Fin.last n))
  have h0 : A i0 (Fin.last n) ≠ 0 := by
    intro h
    have := hmax i1
    simp only [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi1 this
  have hq : ∀ i, ∃ q : V, algebraMap V F q = A i (Fin.last n) / A i0 (Fin.last n) :=
    fun i => integral_of_val_le V F _ _ h0 (hmax i)
  choose q hq using hq
  set σ : Equiv.Perm (Fin (n+1)) := Equiv.swap i0 (Fin.last n) with hσ
  let E : Matrix (Fin (n+1)) (Fin (n+1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = Fin.last n then -q (σ i) else 0
  refine ⟨E * σ.permMatrix V, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ (isUnit_det_permMatrix V σ)
    rw [Matrix.det_of_upperTriangular]
    · simp [E]
    · intro a b hab
      have hne : a ≠ b := ne_of_gt hab
      have hb : b ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hab (Fin.le_last a))
      simp [E, hne, hb]
  · rw [Matrix.map_mul, Matrix.mul_assoc, permMatrix_map, Matrix.mul_apply,
      Fintype.sum_eq_add i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne]
    · simp only [permMatrix_mul_apply, E, Matrix.map_apply, Matrix.of_apply, if_true,
        (Fin.castSucc_lt_last i).ne, if_false, map_one, map_neg, hq]
      have : σ (Fin.last n) = i0 := by simp [hσ]
      rw [this]
      field_simp
      ring
    · intro x hx
      simp [E, Matrix.map_apply, Ne.symm hx.1, hx.2]

def blockExt {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : Matrix (Fin (n+1)) (Fin (n+1)) V :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks k 0 0 (1 : Matrix (Fin 1) (Fin 1) V))

lemma blockExt_det {n : ℕ} (k : Matrix (Fin n) (Fin n) V) : (blockExt V k).det = k.det := by
  simp [blockExt, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

lemma blockExt_cc {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a b : Fin n) :
    blockExt V k a.castSucc b.castSucc = k a b := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_cl {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (a : Fin n) :
    blockExt V k a.castSucc (Fin.last n) = 0 := by
  simp [blockExt, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma blockExt_mul_apply {n : ℕ} (k : Matrix (Fin n) (Fin n) V) (A : Matrix (Fin (n+1)) (Fin (n+1)) F)
    (a : Fin n) (j : Fin (n+1)) :
    ((blockExt V k).map (algebraMap V F) * A) a.castSucc j =
      (k.map (algebraMap V F) * A.submatrix Fin.castSucc id) a j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.map_apply, blockExt_cc, blockExt_cl,
    map_zero, zero_mul, add_zero, Matrix.submatrix_apply, id]

theorem iwasawa_lowerTriangular (n : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧
      ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  induction n with
  | zero => exact ⟨1, by simp, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨P, hP, hPA⟩ := clear_last_column V F A
    set A' := P.map (algebraMap V F) * A with hA'
    obtain ⟨k', hk', hk'A⟩ := ih (A'.submatrix Fin.castSucc Fin.castSucc)
    refine ⟨blockExt V k' * P, ?_, fun i j hij => ?_⟩
    · rw [Matrix.det_mul, blockExt_det]
      exact hk'.mul hP
    · rw [Matrix.map_mul, Matrix.mul_assoc, ← hA']
      obtain ⟨a, rfl⟩ : ∃ a : Fin n, a.castSucc = i :=
        Fin.exists_castSucc_eq.mpr (ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j)))
      rw [blockExt_mul_apply]
      induction j using Fin.lastCases with
      | last =>
        rw [Matrix.mul_apply]
        simp only [Matrix.submatrix_apply, id, hPA, mul_zero, Finset.sum_const_zero]
      | cast b =>
        have := hk'A a b (Fin.castSucc_lt_castSucc_iff.mp hij)
        simpa [Matrix.mul_apply, Matrix.submatrix_apply] using this
end IwasawaLowerTri
end GlobalTheory

theorem GlobalTheory.iwasawa_lowerTriangular_of_det :
    ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 :=
  fun V F _ _ _ _ _ _ n A _ => GlobalTheory.IwasawaLowerTri.iwasawa_lowerTriangular V F n A
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMulLowerTriangularOfDetNStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero : ∀ (V F : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F] [IsFractionRing V F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 → ∃ k : Matrix (Fin n) (Fin n) V, IsUnit k.det ∧ ∀ i j, i < j → (k.map (algebraMap V F) * A) i j = 0 := by
  first | exact @GlobalTheory.iwasawa_lowerTriangular_of_det | exact GlobalTheory.iwasawa_lowerTriangular_of_det | (intros; apply GlobalTheory.iwasawa_lowerTriangular_of_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtComplet
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDegInt

open GlobalTheory.LamT

private theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (GlobalTheory.sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

private theorem integral_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : CDVR) (io : c.F →+* T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (_ : y.x = x) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro y hx
  subst hx
  exact integral_of T io y

theorem intPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 𝔓 T iK hiK yT hyT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ρV, hρV⟩ := exists_restrict_ringHom (algebraMap (𝓞 K) K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hiK _).2 (HeightOneSpectrum.valuation_le_one 𝔓 r))
  obtain ⟨G, n, -⟩ := (GlobalTheory.LamT.pat_pullback E H _ _ ρV B).1
  obtain ⟨_, _, _, _, _, n', -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap iK) t₀
  have hx : yT.x = spMap iK ≫ y.x := hyT.1
  obtain ⟨m1', h1⟩ := sab_comp' n' m1 yT.x hx
  obtain ⟨k2, hk2⟩ := sab_comp' n' m2 _ rfl
  obtain ⟨m2', h2⟩ := sab_cancel' n k2 (spMap (algebraMap T.V T.Fr))
    (by rw [← spMap_comp', ← spMap_comp', hρV])
  obtain ⟨⟨g0, hg0u, hg0⟩, -⟩ := GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' yT rfl
  obtain ⟨a0, ha0⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G _ yT.x m1' m2' yT rfl
  choose k hk using fun σ => GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero T.V T.Fr (Dw.mult σ) (g0 σ) (hg0u σ).ne_zero
  have hkdet : ∀ σ, IsUnit (((k σ).map (algebraMap T.V T.Fr))).det := fun σ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hk σ).1.map _
  let C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr :=
    fun σ => (k σ).map (algebraMap T.V T.Fr) * g0 σ
  have hCdet : ∀ σ, IsUnit (C σ).det := fun σ => by
    simp only [C, Matrix.det_mul]
    exact (hkdet σ).mul (hg0u σ)
  have hlow : ∀ σ i j, i < j → C σ i j = 0 := fun σ i j hij => (hk σ).2 i j hij
  have hdiag : ∀ σ i, C σ i i ≠ 0 := fun σ i => by
    have hd : (C σ).det = ∏ j, C σ j j :=
      Matrix.det_of_lowerTriangular _ (fun a b hab => hlow σ a b hab)
    have hne : (C σ).det ≠ 0 := (hCdet σ).ne_zero
    rw [hd] at hne
    exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _)
  let td : Ix Dw → T.Frˣ := fun o => o.elim a0 (fun p => Units.mk0 (C p.1 p.2 p.2) (hdiag p.1 p.2))
  obtain ⟨y', hy', hyu⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT C a0 hCdet
  obtain ⟨y0, hy0, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT g0 a0 hg0u
  obtain ⟨y1, hy1, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr y0 (fun σ => (k σ).map (algebraMap T.V T.Fr)) 1 hkdet
  have hc := (frChg_refl_and_comp E H Dw l Xo c T.Fr yT y0 y1).2 g0 _ (a0 : T.Fr) _ hy0 hy1
  have h1y : y1 = y' := hyu y1 (by simpa [C] using hc)
  have hL0 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y0.u := hg0 a0 y0 hy0
  have hL1 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y1.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' y0 hy0.1).2 hL0 k _ y1
      (fun σ => (hk σ).1) hy1
  rw [h1y] at hL1
  refine ⟨ρV, hρV, G, _, n, n', m1', m2', h1, h2.trans hk2, C, td, y', hlow, fun σ i => rfl, hy', hL1, ?_⟩
  exact integral_of_eq T (iK.comp (algebraMap c.F K)) y' hy'.1 m1' m2' hL1 (ha0 C y' hy')

end GlobalTheory.PtDegInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtCompletStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frameChange_basechange_integral_at_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  first | exact @GlobalTheory.PtDegInt.intPt | exact GlobalTheory.PtDegInt.intPt | (intros; apply GlobalTheory.PtDegInt.intPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLattice
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.TwoBasesDet

theorem exists_leftInv {K : Type} [Field K] {n g : ℕ} (b : Fin n → Fin g → K)
    (hb : LinearIndependent K b) :
    ∃ A : Matrix (Fin n) (Fin g) K, ∀ i j, ∑ k, A i k * b j k = if i = j then 1 else 0 := by
  let lc : (Fin n → K) →ₗ[K] (Fin g → K) := Fintype.linearCombination K b
  have hinj : LinearMap.ker lc = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact funext (Fintype.linearIndependent_iff.1 hb c (by simpa [lc, Fintype.linearCombination_apply] using hc))
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective lc hinj
  refine ⟨LinearMap.toMatrix' f, fun i j => ?_⟩
  have h1 : f (b j) = Pi.single j 1 := by
    have : lc (Pi.single j 1) = b j := by simp [lc, Fintype.linearCombination_apply_single]
    rw [← this, ← LinearMap.comp_apply, hf, LinearMap.id_apply]
  have h3 : (Matrix.mulVec (LinearMap.toMatrix' f) (b j)) = f (b j) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h2 := congrFun (h3.trans h1) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

theorem vV_algebraMap_unit (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] {u : V} (hu : IsUnit u) :
    vV V (algebraMap V K' u) = 0 := by
  unfold vV valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2]
  · simp
  · exact fun h => (HeightOneSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

theorem valuation_div_le_one {K : Type} [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K))
    (c d : 𝓞 K) (hd : d ∉ 𝔓.asIdeal) : 𝔓.valuation K ((c : K) / d) ≤ 1 := by
  rw [map_div₀]
  have h1 : 𝔓.valuation K (d : K) = 1 := by
    rw [show (d : K) = algebraMap (𝓞 K) K d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hd
  rw [h1, div_one, show (c : K) = algebraMap (𝓞 K) K c from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem det_vV_add_eq_zero : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  intro K _ _ 𝔓 T iK hiK g n L b hb M u hu C hW hL
  set B : Fin n → Fin g → T.Fr := fun l k => iK (b l k) with hBdef
  obtain ⟨A, hA⟩ := exists_leftInv b hb.2.1

  have key : ∀ z : Fin n → T.Fr, ∀ i, z i = ∑ k, iK (A i k) * ∑ l, z l * B l k := by
    intro z i
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ k, iK (A i k) * (z l * B l k) = if i = l then z l else 0 := by
      intro l
      have h := congrArg iK (hA i l)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      simp only [map_mul] at h
      calc ∑ k, iK (A i k) * (z l * B l k) = z l * ∑ k, iK (A i k) * iK (b l k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hBdef]; ring
        _ = _ := by rw [h]; split_ifs <;> simp
    simp_rw [h]; simp
  have hinj : ∀ x y : Fin n → T.Fr, (∀ k, ∑ l, x l * B l k = ∑ l, y l * B l k) → x = y := by
    intro x y hxy
    funext i
    rw [key x i, key y i]
    exact Finset.sum_congr rfl fun k _ => by rw [hxy k]

  set P : Matrix (Fin n) (Fin n) T.Fr := C * M.map iK with hPdef
  have hWP : ∀ i k, (∑ j, C i j • fun k => iK (u j k)) k = ∑ l, P i l * B l k := by
    intro i k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hu, map_sum, map_mul, hPdef, Matrix.mul_apply,
      Matrix.map_apply, hBdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  have hint : ∀ x ∈ L, ∃ p : Fin n → T.V, ∀ k, iK (x k) = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hb.2.2 x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hdx
    have hd0 : (d : K) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      rw [this]; exact Submodule.zero_mem _
    choose p hp using fun l => (hiK ((c l : K) / d)).2 (valuation_div_le_one 𝔓 (c l) d hd)
    refine ⟨p, fun k => ?_⟩
    have hk := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def] at hk
    have hx' : x k = ∑ l, ((c l : K) / d) * b l k := by
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      rw [eq_div_iff hd0]
      convert hk.symm using 1
      · ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hp, hBdef, hx', map_sum, map_mul]
  have hspan : ∀ w ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K))),
      ∃ p : Fin n → T.V, ∀ k, w k = ∑ l, algebraMap T.V T.Fr (p l) * B l k := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact hint x hx
    | zero => exact ⟨0, fun k => by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨p, hp⟩ := h
      obtain ⟨p', hp'⟩ := h'
      exact ⟨p + p', fun k => by simp [hp, hp', add_mul, Finset.sum_add_distrib]⟩
    | smul a w _ h =>
      obtain ⟨p, hp⟩ := h
      refine ⟨a • p, fun k => ?_⟩
      simp only [Pi.smul_apply, Algebra.smul_def, hp, Finset.mul_sum, smul_eq_mul, map_mul, mul_assoc]
      exact Finset.sum_congr rfl fun _ _ => by simp only [Algebra.algebraMap_self, RingHom.id_apply]

  have hPint : ∀ i, ∃ p : Fin n → T.V, ∀ l, P i l = algebraMap T.V T.Fr (p l) := by
    intro i
    obtain ⟨p, hp⟩ := hspan _ (hW i)
    refine ⟨p, fun l => congrFun (hinj (P i) (fun l => algebraMap T.V T.Fr (p l)) fun k => ?_) l⟩
    rw [← hWP, hp]
  choose Pv hPv using hPint
  have hPeq : P = (Matrix.of Pv).map (algebraMap T.V T.Fr) := by
    ext i l; simp [hPv i l]

  have hQint : ∀ l, ∃ q : Fin n → T.V, ∀ m, ∑ i, algebraMap T.V T.Fr (q i) * P i m = if l = m then 1 else 0 := by
    intro l
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hL (b l) (hb.1 l))
    refine ⟨q, fun m => congrFun (hinj (fun m => ∑ i, algebraMap T.V T.Fr (q i) * P i m)
      (fun m => if l = m then 1 else 0) fun k => ?_) m⟩
    have hk : ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k = iK (b l k) := by
      rw [← congrFun hq k, Finset.sum_apply]
      simp only [Pi.smul_apply, Algebra.smul_def]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_comm]
    calc ∑ i, ∑ m, algebraMap T.V T.Fr (q i) * P i m * B m k
        = ∑ i, algebraMap T.V T.Fr (q i) * (∑ j, C i j • fun k => iK (u j k)) k := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hWP, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = B l k := hk
  choose Qv hQv using hQint
  have hQP : Matrix.of Qv * Matrix.of Pv = 1 := by
    apply (Matrix.map_injective (IsFractionRing.injective T.V T.Fr))
    show (Matrix.of Qv * Matrix.of Pv).map (algebraMap T.V T.Fr) = (1 : Matrix (Fin n) (Fin n) T.V).map (algebraMap T.V T.Fr)
    rw [Matrix.map_mul, ← hPeq, Matrix.map_one _ (map_zero _) (map_one _)]
    ext l m
    simpa [Matrix.mul_apply, Matrix.one_apply] using hQv l m
  have hunit : IsUnit (Matrix.of Pv).det := by
    have := congrArg Matrix.det hQP
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact ⟨⟨_, _, by rw [mul_comm]; exact this, this⟩, rfl⟩
  have hdetP : P.det = algebraMap T.V T.Fr (Matrix.of Pv).det := by
    rw [hPeq, RingHom.map_det]; rfl
  have hdetP' : P.det = C.det * iK M.det := by
    rw [hPdef, Matrix.det_mul, RingHom.map_det]; rfl
  have hP0 : P.det ≠ 0 := by
    rw [hdetP]
    exact (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 hunit.ne_zero
  have hC0 : C.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, zero_mul])
  have hM0 : iK M.det ≠ 0 := fun h => hP0 (by rw [hdetP', h, mul_zero])
  refine ⟨fun h => hM0 (by rw [h, map_zero]), hC0, ?_⟩
  rw [← vV_mul hC0 hM0, ← hdetP', hdetP]
  exact vV_algebraMap_unit T.V hunit

end GlobalTheory.TwoBasesDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetValuationsSumZeroSameLocalLatticeStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_valuations_sum_zero_same_local_lattice : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (g n : ℕ) (L : Submodule (𝓞 K) (Fin g → K)) (b : Fin n → Fin g → K), GlobalTheory.PtDeg.LocBasis 𝔓 L b → ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → Fin g → K), (∀ i, u i = ∑ j, M i j • b j) → ∀ (C : Matrix (Fin n) (Fin n) T.Fr), (∀ i, (∑ j, C i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin g → K) k => iK (v k)) '' (L : Set (Fin g → K)))) → (∀ v ∈ L, (fun k => iK (v k)) ∈ Submodule.span T.V (Set.range fun i => ∑ j, C i j • fun k => iK (u j k))) → M.det ≠ 0 ∧ C.det ≠ 0 ∧ vV T.V C.det + vV T.V (iK M.det) = 0 := by
  first | exact @GlobalTheory.TwoBasesDet.det_vV_add_eq_zero | exact GlobalTheory.TwoBasesDet.det_vV_add_eq_zero | (intros; apply GlobalTheory.TwoBasesDet.det_vV_add_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionConstValuationEigenLatticeAtPrime
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.PtDeg

theorem rho_eq_vAdd_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ (π : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 c.F)) (ε : HeightOneSpectrum (𝓞 K) → ℕ), (∀ 𝔓 (z : c.F), 𝔓.valuation K (algebraMap c.F K z) = (π 𝔓).valuation c.F z ^ ε 𝔓) → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (M : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) K) (b' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (M' : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) K), GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act t) b → (∀ i, u i = ∑ j, M i j • b j) → GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) b' → (∀ i, u' i = ∑ j, M' i j • b' j) → (ε 𝔓 : ℝ) * ρ (π 𝔓) = (vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hyZ B t₀ m1 m2 F t ht π ε hπε u u' hu hu' 𝔓 b M b' M' hb hM hb' hM'
  have hε : 0 < ε 𝔓 := by
    rcases Nat.eq_zero_or_pos (ε 𝔓) with h | h
    · have h0 := hπε 𝔓 0
      rw [h, pow_zero, map_zero, map_zero] at h0
      exact absurd h0 zero_ne_one
    · exact h
  obtain ⟨T, iK, hFin, hT⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff K 𝔓
  obtain ⟨e, he, hv⟩ := GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul K 𝔓 T iK hT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  let φ : K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.FlagTan.exists_frMap φ y
  have htri := GlobalTheory.T.triangular_frameChange_basechange_integral_at_completion E H Dw l Xo c K y B t₀ m1 m2 𝔓 T iK hT yT hyT
  rcases htri with ⟨ρV, hρV, G, t', n, n', m1', m2', h1, h2, C, td, y', hlow, hdiag, hchg, hlie, hint⟩
  have hbor : FrBor td yT y' :=
    ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c T.Fr yT y' y').1 td).2 ⟨C, hlow, hdiag, hchg⟩
  have hover : OverLa (π 𝔓) T.V (iK.comp (algebraMap c.F K)) (e * ε 𝔓) := by
    refine ⟨Nat.mul_pos he hε, fun z => ?_⟩
    rw [RingHom.comp_apply, hv, vAdd, hπε, vLa]
    by_cases hz : z = 0
    · subst hz; simp
    · have hz' : (π 𝔓).valuation c.F z ≠ 0 := by simpa using hz
      rw [WithZero.log_pow]
      push_cast; ring
  let yI : IntFr Xo c T (iK.comp (algebraMap c.F K)) := ⟨y', GlobalTheory.FlagTan.fromTest_of_isLocalRing y', hint⟩
  have hyTZ : LiesOn Z yT := GlobalTheory.FlatLine.liesOn_frMap hyT hyZ
  have hlies : LiesOn Z y' := by
    have e1 : ptF y' = ptF yT := by
      unfold ptF
      congr 1
      exact hchg.1
    intro p
    rw [e1]
    exact hyTZ p
  have hmem : (fun f => nval T.V (e * ε 𝔓) (evI yI f)) ∈ valOn Z (π 𝔓) :=
    ⟨PtV.mk (π 𝔓) hover yI ⟨hFin, hlies⟩ () trivial, rfl⟩
  have hval := hρ (π 𝔓) _ hmem
  have hev1 := GlobalTheory.FlagTan.evR_frBor s.sig_mem hbor
  have hev2 : evR Xo c s.sig yT = φ (evR Xo c s.sig y) := GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hyT
  have hS4 := GlobalTheory.T.flatLineWeight_character_triangular_frameChange E H Dw τ T.Fr td
  have hct := GlobalTheory.ConjHostChar.conj_char E H Dw l Xo c τ K t ht
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht u hu 𝔓 T iK hT ρV hρV yT hyT G t' n n'
    m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨hB1, hB2⟩ := GlobalTheory.T.integralFrame_span_completed_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) (t.comp (H.bar : 𝓞 E →+* 𝓞 E)) hct u' hu'
    𝔓 T iK hT ρV hρV yT hyT G t' n n' m1' m2' h1 h2 C (td none) y' hchg hlie
  obtain ⟨-, hCdet, hvC⟩ := GlobalTheory.T.det_valuations_sum_zero_same_local_lattice K 𝔓 T iK hT F.P₀.g _ _ b hb M u hM (C τ.1) hA1 hA2
  obtain ⟨-, -, hvC'⟩ := GlobalTheory.T.det_valuations_sum_zero_same_local_lattice K 𝔓 T iK hT F.P₀.g _ _ b' hb' M' u' hM' (C (conjEmb τ.1)) hB1 hB2
  have hdet : ∀ σ, (C σ).det = ∏ i, (td (some ⟨σ, i⟩) : T.Fr) := fun σ => by
    rw [Matrix.det_of_lowerTriangular (C σ) (fun i j hij => hlow σ i j hij)]
    exact Finset.prod_congr rfl fun i _ => hdiag σ i
  have hφ : ∀ z, φ z = iK z := fun _ => rfl
  have hprod : evR Xo c s.sig y' * (C τ.1).det = (C (conjEmb τ.1)).det * iK (evR Xo c s.sig y) := by
    rw [hev1, hev2, hdet, hdet, hφ, ← hS4]
    ring
  have hval' : nval T.V (e * ε 𝔓) (evR Xo c s.sig y') = (ρ (π 𝔓) : EReal) := hval
  have hy'0 : evR Xo c s.sig y' ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hval'
    exact EReal.coe_ne_top _ hval'.symm
  have ha0 : iK (evR Xo c s.sig y) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hC'0 : (C (conjEmb τ.1)).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact mul_ne_zero hy'0 hCdet hprod
  have hZ := congrArg (vV T.V) hprod
  rw [vV_mul hy'0 hCdet, vV_mul hC'0 ha0, hv] at hZ
  rw [hv] at hvC hvC'
  rw [nval_of_ne hy'0, EReal.coe_eq_coe_iff] at hval'
  have hvy : (vV T.V (evR Xo c s.sig y') : ℝ) = e * ((vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ)) := by
    have : vV T.V (evR Xo c s.sig y') = e * (vAdd 𝔓 (evR Xo c s.sig y) + vAdd 𝔓 M.det - vAdd 𝔓 M'.det) := by linarith
    rw [this]; push_cast; ring
  rw [← hval', hvy]
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hε' : (ε 𝔓 : ℝ) ≠ 0 := by exact_mod_cast hε.ne'
  push_cast
  field_simp

end GlobalTheory.PtDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionConstValuationEigenLatticeAtPrimeStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSection_constValuation_eigenLattice_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ (π : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 c.F)) (ε : HeightOneSpectrum (𝓞 K) → ℕ), (∀ 𝔓 (z : c.F), 𝔓.valuation K (algebraMap c.F K z) = (π 𝔓).valuation c.F z ^ ε 𝔓) → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (b : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (M : Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) K) (b' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (M' : Matrix (Fin (Dw.mult (conjEmb τ.1))) (Fin (Dw.mult (conjEmb τ.1))) K), GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act t) b → (∀ i, u i = ∑ j, M i j • b j) → GlobalTheory.PtDeg.LocBasis 𝔓 (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) b' → (∀ i, u' i = ∑ j, M' i j • b' j) → (ε 𝔓 : ℝ) * ρ (π 𝔓) = (vAdd 𝔓 (evR Xo c s.sig y) : ℝ) + (vAdd 𝔓 M.det : ℝ) - (vAdd 𝔓 M'.det : ℝ) := by
  first | exact @GlobalTheory.PtDeg.rho_eq_vAdd_at_prime | exact GlobalTheory.PtDeg.rho_eq_vAdd_at_prime | (intros; apply GlobalTheory.PtDeg.rho_eq_vAdd_at_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPoint
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

namespace GlobalTheory.FlatPointNe

theorem evR_sig_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c r U x _ Z τ s K _ _ _ y hy h0
  have ht : Tested y := GlobalTheory.FlagTan.fromTest_of_isLocalRing y
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hy ht]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

end GlobalTheory.FlatPointNe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionNeZeroAtNumberFieldPointStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatSection_ne_zero_at_numberField_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → evR Xo c s.sig y ≠ 0 := by
  first | exact @GlobalTheory.FlatPointNe.evR_sig_ne_zero | exact GlobalTheory.FlatPointNe.evR_sig_ne_zero | (intros; apply GlobalTheory.FlatPointNe.evR_sig_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtension
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine Formalism.BasicNotions

namespace GlobalTheory.FlatLine

section Descent

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']

theorem exp_ne_zero_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) : ε 𝔓 ≠ 0 := by
  intro h0
  have hmem : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k') ∈ 𝔓.asIdeal := Ideal.absNorm_mem _
  have h2 : 𝔓.valuation k' (algebraMap (𝓞 k') k' ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k')) < 1 := by
    rwa [HeightOneSpectrum.valuation_lt_one_iff_mem]
  have h1 := hv 𝔓 (Ideal.absNorm 𝔓.asIdeal : k)
  rw [h0, pow_zero, map_natCast] at h1
  rw [map_natCast, h1] at h2
  exact lt_irrefl _ h2

theorem mem_iff_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) (x : 𝓞 k) :
    x ∈ (π 𝔓).asIdeal ↔ 𝔓.valuation k' (algebraMap k k' (x : k)) < 1 := by
  rw [hv, pow_lt_one_iff (exp_ne_zero_of_valuation_pow hv 𝔓), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k)]

theorem eq_of_valuation_pow {π π' : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε ε' : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (hv' : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π' 𝔓).valuation k z ^ ε' 𝔓) :
    π = π' ∧ ε = ε' := by
  have hπ : π = π' := by
    funext 𝔓
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_iff_of_valuation_pow hv, mem_iff_of_valuation_pow hv']
  refine ⟨hπ, ?_⟩
  funext 𝔓
  obtain ⟨z, hz⟩ := (π 𝔓).valuation_exists_uniformizer k
  have h := (hv 𝔓 z).symm.trans (hv' 𝔓 z)
  rw [← hπ, hz, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

theorem lineDeg_descent : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']
    (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ),
    (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) →
    ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ),
    (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite →
    (Function.support ρ).Finite ∧
      lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  intro k k' _ _ _ _ _ π ε hv r ρ hfin
  classical
  obtain ⟨π₀, ε₀, hv₀, hsum⟩ :=
    GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm k k' (algebraMap k k')
  obtain ⟨hπ, hε'⟩ := eq_of_valuation_pow hv hv₀
  rw [← hπ, ← hε'] at hsum
  choose s hs hne hid using hsum
  have hε : ∀ 𝔓, ε 𝔓 ≠ 0 := exp_ne_zero_of_valuation_pow hv
  have hk : (0 : ℝ) < finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hk' : (0 : ℝ) < finrank ℚ k' := by exact_mod_cast Module.finrank_pos

  have hρ : (Function.support ρ).Finite := by
    refine (hfin.image π).subset ?_
    intro 𝔭 h𝔭
    obtain ⟨𝔓, h𝔓⟩ := hne 𝔭
    have he : π 𝔓 = 𝔭 := (hs 𝔭 𝔓).1 h𝔓
    refine ⟨𝔓, ?_, he⟩
    simp only [Function.mem_support, he]
    exact mul_ne_zero (by exact_mod_cast hε 𝔓) h𝔭
  refine ⟨hρ, ?_⟩

  have harch := GlobalTheory.finrank_mul_sum_embeddings_comp k k' (algebraMap k k') (fun σ => Real.log (r σ))
  have hA : (∑ σ : k' →+* ℂ, Real.log (r (σ.comp (algebraMap k k')))) / (finrank ℚ k' : ℝ)
      = (∑ σ : k →+* ℂ, Real.log (r σ)) / (finrank ℚ k : ℝ) := by
    rw [div_eq_div_iff hk'.ne' hk.ne']
    linarith [harch]

  have hdisj : ((hρ.toFinset : Finset (HeightOneSpectrum (𝓞 k))) : Set (HeightOneSpectrum (𝓞 k))).PairwiseDisjoint s := by
    intro a _ b _ hab
    exact Finset.disjoint_left.2 fun 𝔓 ha hb => hab (((hs a 𝔓).1 ha).symm.trans ((hs b 𝔓).1 hb))
  unfold lineDeg lw
  beta_reduce
  have h1 : Function.support (fun la : HeightOneSpectrum (𝓞 k) =>
      ρ la * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k : ℝ))) ⊆ ↑hρ.toFinset := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
    simp [hx]
  have h2 : Function.support (fun la : HeightOneSpectrum (𝓞 k') =>
      (ε la : ℝ) * ρ (π la) * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k' : ℝ)))
      ⊆ ↑(hρ.toFinset.biUnion s) := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    have h0 : ρ (π x) = 0 := by
      by_contra h
      apply hx
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset,
        Function.mem_support]
      exact ⟨π x, h, (hs _ _).2 rfl⟩
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, hA,
    Finset.sum_biUnion hdisj]
  congr 1
  refine Finset.sum_congr rfl fun 𝔭 _ => ?_
  have e1 : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * ρ (π 𝔓) * (Real.log (Ideal.absNorm 𝔓.asIdeal) / (finrank ℚ k' : ℝ))
      = ρ 𝔭 / (finrank ℚ k' : ℝ) * ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔓 h => ?_
    rw [(hs 𝔭 𝔓).1 h]
    ring
  have hS : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal)
      = (finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) / (finrank ℚ k : ℝ) := by
    rw [eq_div_iff hk.ne']
    linarith [hid 𝔭]
  rw [e1, hS]
  field_simp

end Descent

end GlobalTheory.FlatLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtensionStatement
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLine_degree_invariant_finite_extension : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k'] (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) → ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ), (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite → (Function.support ρ).Finite ∧ lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  first | exact @GlobalTheory.FlatLine.lineDeg_descent | exact GlobalTheory.FlatLine.lineDeg_descent | (intros; apply GlobalTheory.FlatLine.lineDeg_descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem lineDeg_eq_deg_eigLat_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hy B t₀ hm1 hm2 F h hh t ht
  obtain ⟨m1⟩ := hm1
  obtain ⟨m2⟩ := hm2
  obtain ⟨π, ε, hπ, -⟩ := GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm c.F K (algebraMap c.F K)
  have ht' := GlobalTheory.T.hostIntegerCharacter_comp_conj_eq_conjEmbedding E H Dw l Xo c τ K t ht
  obtain ⟨u, hu, hui, hus⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht
  obtain ⟨u', hu', hui', hus'⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) _ ht'
  have hfin := GlobalTheory.T.flatSection_constValuation_eigenLattice_at_prime E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy B t₀ m1 m2 F t ht π ε hπ u u' hu hu'
  have hlat := GlobalTheory.T.degree_determinant_line_two_hermitianLattices K h _ _ (GlobalTheory.CM.DegBound.eigLat_fg F _ _) (GlobalTheory.CM.DegBound.eigLat_fg F _ _) u u' hui hus hui'
    hus' _ (GlobalTheory.T.flatSection_ne_zero_at_numberField_point E H Dw l Xo c r U x hL Z τ s K y hy) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) hfin
  have harch := GlobalTheory.T.constLengthFlatSection_eq_frameNorm_complexEmbedding E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu'
  obtain ⟨hf, hd⟩ := GlobalTheory.T.adelicLine_degree_invariant_finite_extension c.F K π ε hπ s.cInf ρ hlat.1
  refine ⟨hf, hd.trans ?_⟩
  rw [← hlat.2]
  congr 1
  funext σ
  exact harch σ

end GlobalTheory.PtDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSubStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLineDegree_eq_eigenLattice_degree_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  first | exact @GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | exact GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub | (intros; apply GlobalTheory.PtDeg.lineDeg_eq_deg_eigLat_sub <;> assumption)
end
