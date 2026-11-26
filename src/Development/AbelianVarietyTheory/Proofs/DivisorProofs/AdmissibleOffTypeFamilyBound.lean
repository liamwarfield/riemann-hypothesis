module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VAddNonnegOfIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdTrace
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.LevelCoprime

open Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = starRingEnd ℂ (φ x) :=
  H.conjE_apply φ x

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem sigma_conj (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) : σ (H.conj x) = H.conj (σ x) := by
  apply H.φ₀.injective
  have h1 := phi_conj H (H.φ₀.comp (σ : H.E →+* H.E)) x
  exact h1.trans (phi_conj H H.φ₀ (σ x)).symm

theorem b_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_b : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [phi_conj, map_neg, h3]
  simp

theorem agree_on_K (σ τ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = τ H.sqrtMinusD) (x : H.E) (hx : x ∈ H.K) :
    σ x = τ x := by
  have hx' : x ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap r => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem trace_rat (x : H.E) (hx : x ∈ H.K) : ∃ r : ℚ, algebraMap ℚ H.E r = x + H.conj x := by
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  have hmem : x + H.conj x ∈ (⊥ : IntermediateField ℚ H.E) := by
    rw [← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro σ _
    have hb : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
      apply sq_eq_sq_iff_eq_or_eq_neg.1
      rw [← map_pow, b_sq, map_neg, map_natCast]
    rw [map_add (f := _), sigma_conj]
    rcases hb with hb | hb
    · have := agree_on_K H σ 1 hb x hx
      rw [this]; rfl
    · have := agree_on_K H σ H.conj (hb.trans (conj_b H).symm) x hx
      rw [this, conj_conj, add_comm]
  exact IntermediateField.mem_bot.1 hmem

theorem trace_int (x : 𝓞 H.E) (hx : (x : H.E) ∈ H.K) : ∃ a : ℤ, (a : H.E) = x + H.conj x := by
  obtain ⟨r, hr⟩ := trace_rat H x hx
  have h1 : IsIntegral ℤ (H.conj (x : H.E)) :=
    IsIntegral.map (H.conj : H.E →+* H.E).toIntAlgHom x.isIntegral_coe
  have h2 : IsIntegral ℤ (algebraMap ℚ H.E r) := hr ▸ x.isIntegral_coe.add h1
  have h3 : IsIntegral ℤ r := (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  rw [← hr, ← ha]
  simp

theorem trace_sq_le (x : H.E) (a : ℤ) (T : ℕ) (ha : (a : H.E) = x + H.conj x) (hT : x * H.conj x = T) :
    a ^ 2 ≤ 4 * T := by
  have h1 := congrArg H.φ₀ ha
  have h2 := congrArg H.φ₀ hT
  rw [map_add (f := _), phi_conj, map_intCast, Complex.add_conj] at h1
  rw [map_mul, phi_conj, map_natCast, Complex.mul_conj, Complex.normSq_apply] at h2
  have h3 : (a : ℝ) = 2 * (H.φ₀ x).re := by exact_mod_cast h1
  have h4 : (H.φ₀ x).re * (H.φ₀ x).re + (H.φ₀ x).im * (H.φ₀ x).im = (T : ℝ) := by exact_mod_cast h2
  have h5 : (a : ℝ) ^ 2 ≤ 4 * T := by
    rw [h3, ← h4]
    nlinarith [mul_self_nonneg (H.φ₀ x).im]
  exact_mod_cast h5

end Host

theorem four_dvd {E : Type} [Field E] [NumberField E] (n : ℤ) (y : E) (hy : IsIntegral ℤ y)
    (h : (n : E) = 4 * y) : (4 : ℤ) ∣ n := by
  have h1 : y = algebraMap ℚ E ((n : ℚ) / 4) := by
    rw [map_div₀, map_intCast, h]
    simp
  rw [h1] at hy
  have h3 := (isIntegral_algebraMap_iff ).1 hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h3
  refine ⟨a, ?_⟩
  have h4 : (a : ℚ) = (n : ℚ) / 4 := by simpa using ha
  have h5 : (n : ℚ) = 4 * a := by rw [h4]; ring
  exact_mod_cast h5

theorem not_dvd_trace {D : D7} (X : ErrX D) (u : D.what₂.Word) (a : ℤ)
    (ha : (a : D.host.E) = X.piT u + D.host.conj (X.piT u)) : ¬ (((D.mem u).A.T : ℤ) ∣ a) := by
  intro hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + 4 * b := by
    have h4 : (4 : ℕ) ∣ D.host.QS :=
      (show (4 : ℕ) ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h4
    refine ⟨(k * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) * c, ?_⟩
    rw [hk] at hc
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  have hle := trace_sq_le D.host _ a _ ha hn
  have hb' : ((X.piT u : 𝓞 D.host.E) : D.host.E) = 1 + 4 * (b : D.host.E) := by
    rw [hb]; simp [map_ofNat]
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe
  have hb0 := b.isIntegral_coe
  rw [hb'] at ha hn
  simp only [map_add (f := _), map_mul, map_one, map_ofNat] at ha hn
  have h1 : (4 : ℤ) ∣ a - 2 := four_dvd _ _ (hb0.add hbi) (by push_cast; linear_combination ha)
  have h4 : IsIntegral ℤ (4 : D.host.E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := 4))
  have h2 : (4 : ℤ) ∣ ((D.mem u).A.T : ℤ) - 1 :=
    four_dvd _ _ ((hb0.add hbi).add ((h4.mul hb0).mul hbi)) (by push_cast; linear_combination -hn)
  have h3 := (D.mem u).A.T_prime.two_le
  obtain ⟨k, rfl⟩ := hd
  set T : ℤ := ((D.mem u).A.T : ℤ) with hT
  have h5 : 5 ≤ T := by omega
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 1 ≤ k ^ 2 := by
    have := sq_pos_of_ne_zero hk
    omega
  nlinarith [mul_pow T k 2]

theorem coprime_conj {D : D7} (X : ErrX D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    ¬ (0 < vAdd (D.plEq w) (D.embE (X.piT u : D.host.E)) ∧
      0 < vAdd (D.plEq w) (star (D.embE (X.piT u : D.host.E)))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := trace_int D.host (X.piT u) (X.piT_K u)
  have hp := (D.mem u).A.T_prime
  have hn := X.piT_norm u
  have hT0 : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [← hn] at hT0
  rw [← D.embE_conj] at h2
  have i1 : IsIntegral ℤ (D.embE (X.piT u : D.host.E)) :=
    IsIntegral.map D.embE.toIntAlgHom (X.piT u).isIntegral_coe
  have i2 : IsIntegral ℤ (D.embE (D.host.conj (X.piT u : D.host.E))) :=
    IsIntegral.map (D.embE.comp (D.host.conj : D.host.E →+* D.host.E)).toIntAlgHom (X.piT u).isIntegral_coe
  let y : 𝓞 D.what₂.LL := ⟨_, i1⟩
  let z : 𝓞 D.what₂.LL := ⟨_, i2⟩
  have hy : y ≠ 0 := fun h => (map_ne_zero D.embE).2 (left_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have hz : z ≠ 0 := fun h => (map_ne_zero D.embE).2 (right_ne_zero_of_mul hT0) (congrArg Subtype.val h)
  have m1 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) y hy).2 h1
  have m2 := (GlobalTheory.TypeLoss.mem_heightOneIdeal_iff_additiveValuation_pos (D.plEq w) z hz).2 h2
  have e : ((a : ℤ) : 𝓞 D.what₂.LL) = y + z := by
    apply RingOfIntegers.coe_injective
    rw [map_intCast, map_add (f := _)]
    change _ = D.embE _ + D.embE _
    rw [← map_add (f := _), ← ha, map_intCast]
  have m3 : ((a : ℤ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := e ▸ Ideal.add_mem _ m1 m2
  have m4 : (((D.mem u).A.T : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := hw ▸ resChar_mem D w
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : ℤ) a :=
    (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 (not_dvd_trace X u a ha)
  obtain ⟨s, t, hst⟩ := hc
  apply (D.plEq w).isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h := congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hst
  push_cast at h
  rw [← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m4) (Ideal.mul_mem_left _ _ m3)

end GlobalTheory.LevelCoprime
end

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.SeenHalf

variable {D : D7}

theorem vAdd_add_star (D : D7) (w : D.what₂.places.Pl) (y : D.what₂.LL)
    (hy : y * star y = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)) :
    vAdd (D.plEq w) y + vAdd (D.plEq w) (star y) = (D.what₂.places.ramIdx w : ℤ) := by
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  rw [← GlobalTheory.TypeLoss.additiveValuation_residueChar_eq_ramIndex, ← hy, GlobalTheory.TypeLoss.additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)]

theorem vAdd_nonneg_of_isIntegral {K : Type} [Field K] [NumberField K]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ≠ 0) (hi : IsIntegral ℤ x) : 0 ≤ vAdd w x := by
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := K) w (⟨x, hi⟩ : 𝓞 K)
  have hx' : w.valuation K x ≠ 0 := (map_ne_zero _).2 hx
  unfold vAdd
  rw [neg_nonneg, ← WithZero.log_one, WithZero.log_le_log hx' one_ne_zero]
  exact h

theorem sigmaOf_fix {R : Ranks} (H : Host R) (g : R.Psi) {x : H.E} (hx : x ∈ H.K) : H.sigmaOf g x = x := by
  have h : H.sigmaOf g (H.sqd) = H.sqd := by
    refine (H.galE_mem_Psi_iff _).1 ?_
    have : H.galE (H.sigmaOf g) = g :=
      (H.gal).apply_symm_apply _
    rw [this]
    exact g.2
  have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.sigmaOf g)) := by
    refine IntermediateField.adjoin_simple_le_iff.2 ?_
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers (H.sigmaOf g) ≤ MulAction.stabilizer _ (H.sqd) := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) _ (Subgroup.mem_zpowers _)

theorem ETpi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi D u := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  positivity

theorem sz_ET_nonneg (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    0 ≤ SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) := by
  have h0 := ETpi_nonneg D u
  have l0 : 0 ≤ SizeData₂.lwP w := by
    unfold SizeData₂.lwP lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have h1 : 0 ≤ Formalism.MainNotions.product_first_zeroth_parts.ET D u w := by
    rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
    split_ifs
    · exact h0
    · exact le_rfl
  unfold SizeData₂.sz
  positivity

theorem sum_over_eq {X : ErrX D} (hs : SeenDef D X) (u : D.what₂.Word) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = (D.mem u).A.T) :
    ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET D u w) = Formalism.MainNotions.product_first_zeroth_parts.ETpi D u * Real.log ((D.mem u).A.T : ℝ) := by
  have hT : ((D.mem u).A.T).Prime := (D.mem u).A.T_prime
  set y : D.what₂.LL := D.embE (X.piT u : D.host.E) with hy
  have hn : y * star y = ((D.mem u).A.T : D.what₂.LL) := by
    rw [hy, ← D.embE_conj, ← map_mul, X.piT_norm]
    simp
  have hy0 : y ≠ 0 := fun h => (Nat.cast_ne_zero.2 hT.ne_zero : ((D.mem u).A.T : D.what₂.LL) ≠ 0)
    (by rw [← hn, h, zero_mul])
  have hi1 : IsIntegral ℤ y := IsIntegral.map (D.embE : D.host.E →+* D.what₂.LL).toIntAlgHom (X.piT u).isIntegral_coe
  have hi2 : IsIntegral ℤ (star y) := IsIntegral.map (starRingEnd D.what₂.LL).toIntAlgHom hi1
  rw [← GlobalTheory.TypeLoss.sum_half D _ hT S hS y hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw := (hS w).1 hw
  have a1 := vAdd_nonneg_of_isIntegral (D.plEq w) hy0 hi1
  have a2 := vAdd_nonneg_of_isIntegral (D.plEq w) (star_ne_zero.2 hy0) hi2
  have a3 := vAdd_add_star D w y (by rw [hw]; exact hn)
  have a4 := GlobalTheory.LevelCoprime.coprime_conj X u w hw
  rw [← hy] at a4
  have a5 : (D.fm u).seenP w = true ↔ 0 < vAdd (D.plEq w) y := by
    rw [hs u w hw]
    have e : ∀ τ, tauLL D τ (X.piT u : D.host.E) = y := fun τ => by
      unfold tauLL
      rw [sigmaOf_fix D.host (D.eTau τ) (X.piT_K u)]
    simp only [e, D.val_eq w y hy0]
    constructor
    · intro h
      exact_mod_cast h (D.eTau.symm 1)
    · intro h _
      exact_mod_cast h
  rw [Formalism.MainNotions.product_first_zeroth_parts.ET_eq]
  unfold SizeData₂.sz
  by_cases h : (D.fm u).seenP w = true
  · have b1 := a5.1 h
    have b2 : vAdd (D.plEq w) y = (D.what₂.places.ramIdx w : ℤ) := by
      by_contra hne
      exact a4 ⟨b1, by omega⟩
    rw [if_pos h, b2]
    push_cast
    ring
  · have b2 : vAdd (D.plEq w) y = 0 := by
      have := mt a5.2 h
      omega
    rw [if_neg h, b2]
    simp

theorem seen_half : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (S : Finset (Fm.D x i).what₂.places.Pl), (∀ w ∈ S, Formalism.MainNotions.product_first_zeroth_parts.OverT (Fm.D x i) u w) → 0 ≤ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ∧ ∑ w ∈ S, SizeData₂.sz w (Formalism.MainNotions.product_first_zeroth_parts.ET (Fm.D x i) u w) ≤ Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ) := by
  intro eps Fm x hx i u S hS
  refine ⟨Finset.sum_nonneg fun w _ => sz_ET_nonneg _ u w, ?_⟩
  obtain ⟨S', hS'⟩ := GlobalTheory.TypeLoss.exists_over (Fm.D x i) _ ((Fm.D x i).mem u).A.T_prime
  rw [← sum_over_eq (Fm.ex x hx i).err.seen u S' hS']
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => (hS' w).2 (hS w hw)) fun w _ _ => sz_ET_nonneg _ u w

end GlobalTheory.SeenHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UBoundOffTop
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelLoss

variable {D : D7} {L : SizeData₂ D}

theorem u_bound_off_top (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) (hl0 : ¬ (l.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 3 * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hb1 := GlobalTheory.HCEntries.b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hS : L.Sc ≤ L.sc.b := by linarith [GlobalTheory.HCEntries.b'_Sc_le hS, GlobalTheory.HCEntries.b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    have ha : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := fun ha =>
      hl0 ⟨rfl, by unfold topsOf; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
    have h1 := P.cloud_place_bound τ (by omega) ha
    push_cast at h1
    linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem N_le_b (h : SizesAt L) (P : ParameterChoice' D L) : 5 * (D.R.N D.R.m : ℝ) ≤ L.sc.b := by
  have h1 := (GlobalTheory.FockDegreeGap.errors_le h P).2.2
  have hk : (5 : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega : 5 ≤ D.R.k)
  have h0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  nlinarith

theorem true_entry_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (i : ℕ) (hi : i ≤ D.R.m) (a : Fin (D.R.N i)) (ha : ¬ (a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau)) :
    |((((D.fm u).lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 5 * L.sc.b := by
  have hN := N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by positivity
  have s0 : (0 : ℝ) ≤ ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have s1 : ((i * (D.R.t + 1) / 2 : ℕ) : ℝ) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by
    have : i * (D.R.t + 1) / 2 ≤ D.R.m * (D.R.t + 1) :=
      (Nat.div_le_self _ _).trans (Nat.mul_le_mul_right _ hi)
    exact_mod_cast this
  have e0 : ((((D.fm u).lam i τ).w a : ℤ) : ℝ) = (((((D.fm u).lam i τ).w a : ℤ) : ℚ) : ℝ) := by
    rw [Rat.cast_intCast]
  rw [Int.cast_sub, Int.cast_natCast, e0, (D.fm u).lam_eq i hi τ a]
  split_ifs with hk
  · have b := abs_le.1 (u_bound_off_top h P hx u τ ⟨a.1, hk⟩ ha)
    have a1 : (a.1 : ℝ) ≤ D.R.k := by exact_mod_cast hk.le
    have a0 : (0 : ℝ) ≤ a.1 := Nat.cast_nonneg _
    unfold hcToWeightQ rhoVec
    push_cast
    rw [abs_le]
    constructor <;> linarith [b.1, b.2, GlobalTheory.HCEntries.one_le_b L]
  · have hq := D.R.blk_lt hi a hk
    generalize_proofs
    obtain ⟨w0, w1⟩ := GlobalTheory.HCEntries.wj_bounds h hx ((a.1 - D.R.k) / (D.R.t + 1) + 1) (Nat.le_add_left _ _) hq τ
    rw [GlobalTheory.FockDegreeGap.wj_succ D _ hq] at w0 w1
    rw [D.hcW_e]
    have q1 : (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast hq
    have q0 : (1 : ℝ) ≤ (((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left _ _
    unfold wG
    generalize ((a.1 - D.R.k) / (D.R.t + 1) + 1 : ℕ) = q at q0 q1 ⊢
    have q2 : (q : ℝ) * (D.R.t + 1) ≤ (D.R.m : ℝ) * (D.R.t + 1) := by gcongr
    have q3 : (1 : ℝ) * (D.R.t + 1) ≤ (q : ℝ) * (D.R.t + 1) := by gcongr
    push_cast
    rw [abs_le]
    constructor <;> linarith

theorem Wtau_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (Wtau D u τ : ℝ) ≤ 5 * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  rw [← Nat.le_floor_iff (by linarith)]
  unfold Wtau
  refine Finset.sup_le fun i hi => Finset.sup_le fun a _ => ?_
  split_ifs with ha
  · exact Nat.zero_le _
  · rw [Nat.le_floor_iff (by linarith), Nat.cast_natAbs, Int.cast_abs]
    exact true_entry_le h P hx u τ i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) a ha

end GlobalTheory.LevelLoss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelBudget

variable {D : D7} {L : SizeData₂ D}

theorem ETpi_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) :
    Formalism.MainNotions.product_first_zeroth_parts.ETpi D u ≤ 12 * D.R.f * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  have hN := GlobalTheory.LevelLoss.N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have r2 := (GlobalTheory.FockDegreeGap.ranks_le D).2
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h1 : ∑ τ : D.what₂.Tau, (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ) ≤ D.R.f * (5 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ)) _
      (fun τ _ => GlobalTheory.LevelLoss.Wtau_le h P hx u τ)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have h2 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) ≤ D.R.f := by
    have := Finset.card_le_univ (Formalism.MainNotions.product_first_zeroth_parts.tops D)
    rw [D.what₂.card_Tau] at this
    exact_mod_cast this
  have h3 : ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) ≤ L.sc.b := by nlinarith
  have h4 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) * (((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1)) ≤ D.R.f * L.sc.b :=
    mul_le_mul h2 h3 (by positivity) hf0
  have h5 : (D.R.f : ℝ) * D.R.N D.R.m ≤ D.R.f * L.sc.b :=
    mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) (D.R.N D.R.m)]) hf0
  have h6 : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  nlinarith

theorem admissible_off_type_level_budget : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ ⟨x₁, h1⟩
  refine ⟨max (12 * Fm.CTu) 0, max 2 x₁, le_max_right _ _, fun x hx0 hx i u => ⟨fun S hS => GlobalTheory.SeenHalf.seen_half Fm x hx i u S hS, ?_⟩⟩
  have a := ETpi_le (Fm.sizes x hx i) (Fm.params x hx i)
    (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) u
  have b := (h1 x ((le_max_right _ _).trans hx0) i).2 u
  have hb := GlobalTheory.HCEntries.one_le_b (Fm.L x i)
  have hT : (1 : ℝ) ≤ (((Fm.D x i).mem u).A.T : ℝ) := by exact_mod_cast ((Fm.D x i).mem u).A.T_prime.one_le
  have hl : 0 ≤ Real.log (((Fm.D x i).mem u).A.T : ℝ) := Real.log_nonneg hT
  have e : (Fm.L x i).B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L := rfl
  have hB : 0 ≤ (Fm.L x i).B0 := Formalism.MainNotions.WeightDegreeSizes.loss_bound_nonneg _
  calc Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ)
      ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * Real.log (((Fm.D x i).mem u).A.T : ℝ) :=
        mul_le_mul_of_nonneg_right a hl
    _ ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * (Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_left b (by positivity)
    _ = 12 * Fm.CTu * (Fm.L x i).B0 := by rw [e]; ring
    _ ≤ max (12 * Fm.CTu) 0 * (Fm.L x i).B0 := mul_le_mul_of_nonneg_right (le_max_left _ _) hB

end GlobalTheory.LevelBudget
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_off_type_family_bound : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.LevelBudget.admissible_off_type_level_budget | exact GlobalTheory.LevelBudget.admissible_off_type_level_budget | (intros; apply GlobalTheory.LevelBudget.admissible_off_type_level_budget <;> assumption)
end
