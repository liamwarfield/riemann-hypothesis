module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import GroundTheory.AutomorphicForms.ReductionSiegel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeLoss

open IsDedekindDomain

theorem additiveValuation_mul_of_ne_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem additiveValuation_conj_place_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneIdeal_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneIdeal_iff_additiveValuation_pos _ y hy, mem_heightOneIdeal_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conj_place_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) :
    SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP
  rw [plEq_conj]
  exact Formalism.DivisionValues.ValuationRepresentative.lw_conjPl (D.plEq w)

theorem additiveValuation_residueChar_eq_ramIndex (D : D7) (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have h0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.val_eq w _ h0
  rw [D.what₂.places.val_resChar] at h1
  exact_mod_cast h1.symm

theorem exists_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset D.what₂.places.Pl, ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p := by
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩

theorem sum_half (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (y : D.what₂.LL) (hy : y * star y = (p : D.what₂.LL)) :
    ∑ w ∈ S, 2 * SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) = Real.log p := by
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  have hconj : ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) =
      ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) := by
    refine Finset.sum_nbij' D.what₂.places.conj D.what₂.places.conj ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      rw [logWeight_conj, additiveValuation_conj_place_eq_star]
  have hm := factEtaMean D p hp S hS
  rw [← hm]
  have : ∀ w ∈ S, lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ) =
      SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) + SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) := by
    intro w hw
    have h1 := additiveValuation_residueChar_eq_ramIndex D w
    rw [(hS w).1 hw, ← hy, additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)] at h1
    have h2 : (D.what₂.places.ramIdx w : ℝ) = (vAdd (D.plEq w) y : ℝ) + (vAdd (D.plEq w) (star y) : ℝ) := by
      exact_mod_cast h1.symm
    rw [h2, ← mul_add]
    rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hconj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem conj_sigmaOf {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) :
    H.conj (H.sigmaOf g x) = H.sigmaOf g (H.conj x) := by
  have h1 : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  have h2 : H.sigmaOf (R.cc * g) = H.conj * H.sigmaOf g :=
    map_mul (H.gal).symm (R.cc) g
  have h3 : H.conj * H.sigmaOf g = H.sigmaOf g * H.conj := by rw [← h1, ← h2, mul_comm]
  exact congrArg (fun s : H.E ≃ₐ[ℚ] H.E => s x) h3

theorem tauPib_norm {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    tauPib X i τ * star (tauPib X i τ) = (D.host.g i : D.what₂.LL) := by
  unfold tauPib tauLL
  rw [← D.embE_conj, conj_sigmaOf, ← map_mul, ← map_mul, ← map_mul, X.piG_norm]
  simp

theorem padic_log_le (p n : ℕ) (hp : p.Prime) : (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.padicValNat_def]
  · have h : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [← Real.log_pow]
    apply Real.log_le_log
    · have := hp.pos
      positivity
    · exact_mod_cast h

theorem arith_bound (δ v e lg f m b L N η C₁ C₂ cg CY B : ℝ) (hB : B = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hCY : 0 ≤ CY) (hδ : |δ| ≤ C₁ * f * b) (hv0 : 0 ≤ v)
    (hv : v ≤ C₂ * f * N * Real.log (f * N)) (he : e = cg * f * (N ^ 2 + m ^ 2 * η)) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ (CY + 1) * L) (hη0 : 0 ≤ η) (hNη : N ^ 2 ≤ η) (hmf : m ≤ f) (hfη : f * η ≤ b) :
    |δ * lg + 2 * v + 2 * e * lg| ≤ (|C₁| * (CY + 1) + 2 * |C₂| + 4 * |cg| * (CY + 1)) * B := by
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hηb : η ≤ b := le_trans (le_mul_of_one_le_left hη0 hf) hfη
  have hb : 0 ≤ b := hη0.trans hηb
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hB1 : f * b * L ≤ B := by
    have : B = m * (f * b * L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (mul_nonneg hfb hL0) hm
  have hB2 : f * b ≤ B := le_trans (le_mul_of_one_le_right hfb hL) hB1
  have t1 : |δ * lg| ≤ |C₁| * (CY + 1) * B := by
    rw [abs_mul, abs_of_nonneg hlg0]
    have h1 : |δ| ≤ |C₁| * (f * b) := by
      refine hδ.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hfb
    calc |δ| * lg ≤ |C₁| * (f * b) * ((CY + 1) * L) := mul_le_mul h1 hlg hlg0 (by positivity)
      _ = |C₁| * (CY + 1) * (f * b * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : v ≤ |C₂| * B := by
    have hfN : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf hN
    have l0 : 0 ≤ Real.log (f * N) := Real.log_nonneg hfN
    have l1 : Real.log (f * N) ≤ f * N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h1 : f * N * Real.log (f * N) ≤ B := by
      calc f * N * Real.log (f * N) ≤ f * N * (f * N) := mul_le_mul_of_nonneg_left l1 (by linarith)
        _ = f * (f * N ^ 2) := by ring
        _ ≤ f * b := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hNη hf0).trans hfη) hf0
        _ ≤ B := hB2
    calc v ≤ C₂ * (f * N * Real.log (f * N)) := by rw [← mul_assoc, ← mul_assoc]; exact hv
      _ ≤ |C₂| * (f * N * Real.log (f * N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (by linarith) l0)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t3 : |2 * e * lg| ≤ 4 * |cg| * (CY + 1) * B := by
    have h0 : 0 ≤ N ^ 2 + m ^ 2 * η := by positivity
    have h1 : N ^ 2 + m ^ 2 * η ≤ 2 * (m * b) := by
      have a1 : m * η ≤ b := (mul_le_mul_of_nonneg_right hmf hη0).trans hfη
      have a2 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left a1 hm0
      have a3 : b ≤ m * b := le_mul_of_one_le_left hb hm
      nlinarith
    have h2 : |2 * e * lg| = 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) := by
      rw [he, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlg0, abs_of_nonneg h0, abs_of_nonneg hf0]
      simp only [abs_two]
      ring
    rw [h2]
    calc 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) ≤ 2 * |cg| * f * (2 * (m * b) * ((CY + 1) * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hlg hlg0 (by positivity)) (by positivity)
      _ = _ := by rw [hB]; ring
  have tri : |δ * lg + 2 * v + 2 * e * lg| ≤ |δ * lg| + |2 * v| + |2 * e * lg| := abs_add_three _ _ _
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * v)] at tri
  nlinarith

end GlobalTheory.TypeLoss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
open scoped Pointwise
namespace GlobalTheory.HCF.ModGrowth
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_ringEquivComplex (w : InfinitePlace E) (hw : w.IsComplex) (x : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)) x

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_ringEquivComplex w (IsTotallyComplex.isComplex w) (x.1 w)

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq
    (by simp [nsmul_eq_mul]))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  · exact (norm_le_pi_norm (toL B k) j).trans (norm_le_pi_norm (toL B) k)

theorem height_mul_le (y z : GL (Fin a) (Cinf E)) :
    GlobalTheory.CuspRep.height (y * z) ≤ (a + 1) * (GlobalTheory.CuspRep.height y * GlobalTheory.CuspRep.height z) := by
  have h1 := norm_toL_mul_le (E := E) y.val z.val
  have h2 := norm_toL_mul_le (E := E) (z⁻¹).val (y⁻¹).val
  unfold GlobalTheory.CuspRep.height
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have p1 := norm_nonneg (toL y.val)
  have p2 := norm_nonneg (toL (y⁻¹).val)
  have q1 := norm_nonneg (toL z.val)
  have q2 := norm_nonneg (toL (z⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg p1 q1, mul_nonneg p2 q2, mul_nonneg p1 q2, mul_nonneg p2 q1, mul_nonneg ha (mul_nonneg p1 q1),
    mul_nonneg ha (mul_nonneg p2 q2), mul_nonneg ha p1, mul_nonneg ha p2, mul_nonneg ha q1, mul_nonneg ha q2,
    mul_nonneg ha (mul_nonneg p1 q2), mul_nonneg ha (mul_nonneg p2 q1)]

theorem continuous_height : Continuous (GlobalTheory.CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp continuous_inv
  exact (continuous_const.add (continuous_norm.comp h1)).add (continuous_norm.comp h2)

theorem pFin_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    Matrix.GeneralLinearGroup.map (pFin E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagUnits a fun i => posIdele (K := E) (r i) (hr i) : GA E a) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by
      change ((posIdele (K := E) (r i) (hr i) : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = _
      rw [posIdele_finite]; rfl
  · exact map_zero _

theorem height_pInf_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)))
      ≤ 1 + ∑ i, (r i + (r i)⁻¹) := by
  set d : Fin a → GroundTheory.Global.IdeleGroup E := fun i => posIdele (K := E) (r i) (hr i) with hd
  have hn : ∀ i w, ‖pInf E (d i : Ad E) w‖ = r i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (r i) (hr i) w
  have hn' : ∀ i w, ‖pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w‖ = (r i)⁻¹ := fun i w => by
    have e : pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w * pInf E (d i : Ad E) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.inv_mul, map_one, Pi.one_apply]
    have := congrArg norm e
    rw [norm_mul, hn, norm_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have key : ∀ (f : Fin a → GroundTheory.Global.IdeleGroup E) (s : Fin a → ℝ), (∀ i w, ‖pInf E (f i : Ad E) w‖ = s i) →
      (∀ i, 0 ≤ s i) → ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a f)).val‖ ≤ ∑ i, s i := by
    intro f s hf hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    change ‖pInf E ((diagUnits a f : GA E a) i j)‖ ≤ _
    rw [coe_diagUnits, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      refine (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
      rw [hf]
      exact Finset.single_le_sum (fun k _ => hs k) (Finset.mem_univ i)
    · rw [map_zero, norm_zero]; exact h0
  have h1 := key d r hn fun i => (hr i).le
  have h2 := key (fun i => (d i)⁻¹) (fun i => (r i)⁻¹) hn' fun i => (inv_pos.2 (hr i)).le
  have e : (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a d))⁻¹ =
      Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => (d i)⁻¹) := by
    rw [← map_inv, ← map_inv]; rfl
  unfold GlobalTheory.CuspRep.height
  rw [e, Finset.sum_add_distrib]
  linarith

theorem span_props {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    (∀ l ∈ L, finRep E a l φ = φ) ∧ ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    refine ⟨hx.2.1, fun g => ?_⟩
    obtain ⟨C, M, h⟩ := hx.1.growth g
    refine ⟨|C|, M, abs_nonneg _, fun y => (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) ?_)⟩
    exact pow_nonneg (zero_le_one.trans (one_le_height y)) _
  | zero => exact ⟨fun l _ => map_zero _, fun g => ⟨0, 0, le_rfl, fun y => by simp⟩⟩
  | add x y _ _ hx hy =>
    refine ⟨fun l hl => by rw [map_add (f := _), hx.1 l hl, hy.1 l hl], fun g => ?_⟩
    obtain ⟨C1, M1, h1, e1⟩ := hx.2 g
    obtain ⟨C2, M2, h2, e2⟩ := hy.2 g
    refine ⟨C1 + C2, M1 + M2, add_nonneg h1 h2, fun z => ?_⟩
    have hz := one_le_height z
    have p1 : GlobalTheory.CuspRep.height z ^ M1 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    have p2 : GlobalTheory.CuspRep.height z ^ M2 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    calc ‖(x + y).1 (g * infGL E a z)‖ = ‖x.1 (g * infGL E a z) + y.1 (g * infGL E a z)‖ := rfl
      _ ≤ ‖x.1 (g * infGL E a z)‖ + ‖y.1 (g * infGL E a z)‖ := norm_add_le _ _
      _ ≤ C1 * GlobalTheory.CuspRep.height z ^ (M1 + M2) + C2 * GlobalTheory.CuspRep.height z ^ (M1 + M2) :=
        add_le_add ((e1 z).trans (mul_le_mul_of_nonneg_left p1 h1)) ((e2 z).trans (mul_le_mul_of_nonneg_left p2 h2))
      _ = (C1 + C2) * GlobalTheory.CuspRep.height z ^ (M1 + M2) := by ring
  | smul c x _ hx =>
    refine ⟨fun l hl => by rw [map_smul, hx.1 l hl], fun g => ?_⟩
    obtain ⟨C, M, h, e⟩ := hx.2 g
    refine ⟨‖c‖ * C, M, by positivity, fun z => ?_⟩
    change ‖c * x.1 (g * infGL E a z)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (e z) (norm_nonneg c)

theorem uniform_fin {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hinv : ∀ l ∈ L, finRep E a l φ = φ)
    (hg : ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M)
    {S : Set (GL (Fin a) (Af E))} (hS : IsCompact S) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ s ∈ S, ∀ y, ‖φ.1 (finGL E a s * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : GL (Fin a) (Af E) => s • (L : Set (GL (Fin a) (Af E))))
    (fun s => hL.leftCoset s) (fun s _ => Set.mem_iUnion.2 ⟨s, Set.mem_smul_set.2 ⟨1, L.one_mem, mul_one s⟩⟩)
  choose C M hC hb using fun s : GL (Fin a) (Af E) => hg (finGL E a s)
  refine ⟨∑ s ∈ t, C s, ∑ s ∈ t, M s, Finset.sum_nonneg fun s _ => hC s, fun s' hs' y => ?_⟩
  obtain ⟨s, hst, hs⟩ := Set.mem_iUnion₂.1 (ht hs')
  obtain ⟨l, hl, rfl⟩ := Set.mem_smul_set.1 hs
  have e : φ.1 (finGL E a (s • l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y) := by
    have h := congrArg (fun ψ : Sm E a => ψ.1 (finGL E a s * infGL E a y)) (hinv l hl)
    refine Eq.trans ?_ h
    change φ.1 (finGL E a (s * l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y * finGL E a l)
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hb s y).trans (mul_le_mul (Finset.single_le_sum (fun s _ => hC s) hst)
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (M s)) hst))
    (pow_nonneg (zero_le_one.trans hy) _) (Finset.sum_nonneg fun s _ => hC s))

end GlobalTheory.HCF.ModGrowth

namespace GlobalTheory.HCF.ModGrowth

theorem modGrowth_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ))
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
    ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
    ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E),
    ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
      C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  intro E _ _ _ a L hL W X N φ hφ Ω hΩ
  obtain ⟨hinv, hgr⟩ := span_props hφ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : ∀ g : GA E 0, g = 1 := fun g => Units.ext (Matrix.ext fun i => Fin.elim0 i)
    refine ⟨‖φ.1 1‖, 0, norm_nonneg _, fun b _ r hr k _ y => ?_⟩
    rw [h1 (b * _ * k * _)]
    simp
  have hS : IsCompact ((fun p : GA E a × GA E a => Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) ''
      (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a)))) :=
    (hΩ.prod isCompact_maxCompact).image ((ContAut.continuous_map_pFin E a).comp (continuous_fst.mul continuous_snd))
  obtain ⟨C1, M, hC1, hb1⟩ := uniform_fin hL hinv hgr hS
  have hf : Continuous fun g : GA E a => GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) g) :=
    continuous_height.comp (ContAut.continuous_map_pInf E a)
  obtain ⟨Mb, hMb⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_maxCompact (K := E) (n := a)).exists_bound_of_continuousOn hf.continuousOn
  have hB : (0 : ℝ) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) := by positivity
  refine ⟨C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M, M, by positivity, fun b hb r hr k hk y => ?_⟩
  have hfin : Matrix.GeneralLinearGroup.map (pFin E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pFin E) (b * k) := by
    simp only [map_mul, pFin_diag, pFin_infGL, mul_one]
  have hinf : Matrix.GeneralLinearGroup.map (pInf E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pInf E) b *
        Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i))) *
        Matrix.GeneralLinearGroup.map (pInf E) k * y := by
    simp only [map_mul, pInf_infGL]
  have hx := infGL_mul_finGL (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)
  rw [infGL_comm, hfin, hinf] at hx
  rw [← hx]
  have hs : Matrix.GeneralLinearGroup.map (pFin E) (b * k) ∈ (fun p : GA E a × GA E a =>
      Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) '' (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a))) :=
    ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  refine (hb1 _ hs _).trans ?_

  set A := Matrix.GeneralLinearGroup.map (pInf E) b
  set D := Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)))
  set K := Matrix.GeneralLinearGroup.map (pInf E) k
  set s := ∑ i, (r i + (r i)⁻¹)
  have hs1 : 1 ≤ s := by
    have h0 : ∀ i, 0 ≤ r i + (r i)⁻¹ := fun i => add_nonneg (hr i).le (inv_pos.2 (hr i)).le
    have h1 : 1 ≤ r ⟨0, ha⟩ + (r ⟨0, ha⟩)⁻¹ := by
      rcases le_total (r ⟨0, ha⟩) 1 with h | h
      · linarith [(one_le_inv₀ (hr ⟨0, ha⟩)).2 h, hr ⟨0, ha⟩]
      · linarith [inv_pos.2 (hr ⟨0, ha⟩)]
    exact h1.trans (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ _))
  have hA : GlobalTheory.CuspRep.height A ≤ max Mb 1 :=
    ((Real.le_norm_self _).trans (hMb b hb)).trans (le_max_left _ _)
  have hK : GlobalTheory.CuspRep.height K ≤ max Mk 1 :=
    ((Real.le_norm_self _).trans (hMk k hk)).trans (le_max_left _ _)
  have hD : GlobalTheory.CuspRep.height D ≤ 2 * s := (height_pInf_diag r hr).trans (by linarith)
  have hA1 := one_le_height A
  have hD1 := one_le_height D
  have hK1 := one_le_height K
  have hy1 := one_le_height y
  have c0 : (0 : ℝ) ≤ a + 1 := by positivity
  have e3 := height_mul_le A D
  have e2 := height_mul_le (A * D) K
  have e1 := height_mul_le (A * D * K) y
  have hAD : GlobalTheory.CuspRep.height A * GlobalTheory.CuspRep.height D ≤ max Mb 1 * (2 * s) :=
    mul_le_mul hA hD (by linarith) (by positivity)
  have hADK : GlobalTheory.CuspRep.height (A * D * K) ≤ (a + 1) * ((a + 1) * (max Mb 1 * (2 * s)) * max Mk 1) :=
    e2.trans (mul_le_mul_of_nonneg_left (mul_le_mul (e3.trans (mul_le_mul_of_nonneg_left hAD c0)) hK (by linarith)
      (by positivity)) c0)
  have hz : GlobalTheory.CuspRep.height (A * D * K * y) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y := by
    refine e1.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hADK (by linarith)) c0).trans_eq ?_)
    ring
  have hz0 : 0 ≤ GlobalTheory.CuspRep.height (A * D * K * y) := zero_le_one.trans (one_le_height _)
  calc C1 * GlobalTheory.CuspRep.height (A * D * K * y) ^ M
      ≤ C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz M) hC1
    _ = C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M * s ^ M * GlobalTheory.CuspRep.height y ^ M := by
        rw [mul_pow, mul_pow]; ring

end GlobalTheory.HCF.ModGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteFormsStatement
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_span_harishChandraFiniteForms : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E), ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤ C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  first | exact @GlobalTheory.HCF.ModGrowth.modGrowth_span | exact GlobalTheory.HCF.ModGrowth.modGrowth_span | (intros; apply GlobalTheory.HCF.ModGrowth.modGrowth_span <;> assumption)
end
end
