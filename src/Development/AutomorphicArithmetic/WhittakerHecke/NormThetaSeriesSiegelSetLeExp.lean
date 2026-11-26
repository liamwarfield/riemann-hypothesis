module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsRatMulIdeleFinitePartMemCompactOfLeNorm
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm :
    ∀ c : ℝ, 0 < c → ∃ (S : Set (A ℚ)ˣ) (Bu : ℝ), IsCompact S ∧ 1 ≤ Bu ∧ ∀ a : (A ℚ)ˣ, c ≤ ab a →
        ∃ (q : ℚ) (a' u : (A ℚ)ˣ), q ≠ 0 ∧ (a' : A ℚ) = rt q * (a : A ℚ) ∧ u ∈ S ∧ (a' : A ℚ).2 = (u : A ℚ).2 ∧
          ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 ∧ Bu⁻¹ ≤ |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ∧
          |UpperTheory.ConvolutionTheory.RankTwoDescent.re (a' : A ℚ)| ≤ Bu * (ab a / c) := by
  intro c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) hc c
  have hv : Continuous fun u : IdeleGroup ℚ => ((u : IdeleGroup ℚ) : A ℚ) := Units.continuous_val
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ)) : A ℚ) := Units.continuous_coe_inv
  have hcont : Continuous fun u : IdeleGroup ℚ => ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ +
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ :=
    (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hv))).add
      (continuous_norm.comp ((continuous_apply _).comp (continuous_fst.comp hi)))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  set b := max M 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hb0 : 0 < b := one_pos.trans_le hb1
  refine ⟨S, b, hS, hb1, fun a ha => ?_⟩
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := ab a / c with hsdef
  have hs0 : 0 < s := one_pos.trans_le hx
  set p : IdeleGroup ℚ := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, Module.finrank_self, pow_one]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal ℚ t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs0 v
  have hpi2 : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    have e : (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul p)
    rwa [hp2, mul_one] at e
  have hre : |UpperTheory.ConvolutionTheory.RankTwoDescent.re (((p * u : IdeleGroup ℚ)) : A ℚ)| = s * ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := by
    rw [abs_re]
    have e1 : (((p * u : IdeleGroup ℚ)) : A ℚ).1 Rat.infinitePlace =
        ((p : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace := by
      simp only [Units.val_mul]
      rfl
    rw [e1, norm_mul, hp, norm_posIdele_infinite]
  have hbd := hM u ht
  have hn1 : 0 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (by positivity)] at hbd
  have hMb : M ≤ b := le_max_left _ _
  have hprod : ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ *
      ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace‖ = 1 := by
    rw [← norm_mul]
    have e : ((u : IdeleGroup ℚ) : A ℚ).1 * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 = 1 :=
      congrArg Prod.fst (Units.mul_inv u)
    have e' := congrFun e Rat.infinitePlace
    change ((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace * (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 Rat.infinitePlace = 1 at e'
    rw [e', norm_one]
  refine ⟨(t : ℚ), p * u, u, t.ne_zero, ?_, ht, ?_, ?_, ?_, ?_⟩
  · have h1 : ((IdeleGroup.diagonal ℚ t : IdeleGroup ℚ) : A ℚ) = rt (t : ℚ) := IdeleGroup.coe_diagonal _ _
    rw [← hau, Units.val_mul, h1]
  · change (((p * u : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [Units.val_mul]
    change (((p : IdeleGroup ℚ) : A ℚ)).2 * _ = _
    rw [hp2, one_mul]
  · change ((((p * u)⁻¹ : IdeleGroup ℚ)) : A ℚ).2 = _
    rw [_root_.mul_inv_rev, Units.val_mul]
    change _ * (((p⁻¹ : IdeleGroup ℚ) : A ℚ)).2 = _
    rw [hpi2, mul_one]
  · rw [hre, inv_le_iff_one_le_mul₀ hb0]
    have h1 : 1 ≤ ‖((u : IdeleGroup ℚ) : A ℚ).1 Rat.infinitePlace‖ * b := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left (by linarith) hn1
    nlinarith
  · rw [hre, mul_comm b]
    exact mul_le_mul_of_nonneg_left (by linarith) hs0.le
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsCommonDenomOfIsCompactUnipotentTranslates
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)


open scoped nonZeroDivisors in
private theorem den_of {Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hQ : IsCompact Q) :
    ∃ d : ℕ, 0 < d ∧ ∀ q : ℚ, algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ Q →
      ∃ l : ℤ, (d : ℚ) * q = l := by
  obtain ⟨D, hD0, hD⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set z : ℤ := Rat.ringOfIntegersEquiv D with hz
  have hz0 : z ≠ 0 := by
    intro h
    exact hD0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ D = z := (Rat.ringOfIntegersEquiv_apply_coe D).symm
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, fun q hq => ?_⟩
  have h1 := hD _ hq
  rw [← map_mul] at h1
  have h2 : algebraMap (𝓞 ℚ) ℚ D * q ∈
      ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  have hn : ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) = (z : ℚ) * q := by
    rw [← hdz, ← hr]
    exact Rat.ringOfIntegersEquiv_apply_coe r |>.symm ▸ rfl
  rcases Int.natAbs_eq z with h | h
  · refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = z := by omega
    rw [hn, show ((z.natAbs : ℕ) : ℚ) = (z : ℚ) by rw [← Int.cast_natCast, e1]]
  · refine ⟨-Rat.ringOfIntegersEquiv r, ?_⟩
    have e1 : ((z.natAbs : ℕ) : ℤ) = -z := by omega
    rw [Int.cast_neg, hn, show ((z.natAbs : ℕ) : ℚ) = -(z : ℚ) by
      rw [← Int.cast_natCast, e1, Int.cast_neg], neg_mul]

private theorem mul_int {a : ℕ} {q : ℚ} (c : ℕ) (h : ∃ l : ℤ, (a : ℚ) * q = l) :
    ∃ l : ℤ, ((c * a : ℕ) : ℚ) * q = l := by
  obtain ⟨l, hl⟩ := h
  refine ⟨c * l, ?_⟩
  push_cast
  rw [mul_assoc, hl]

theorem UpperTheory.exists_common_denom_of_isCompact_unipotent_translates :
    ∀ (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), IsCompact L → ∀ S : Set (A ℚ)ˣ, IsCompact S →
        ∃ d : ℕ, 0 < d ∧ ∀ u ∈ S, ∀ (b : FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ ξ' : Fin 2 → ℚ),
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * (u : A ℚ).2,
              (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2]) ∈ L →
          (∃ l : ℤ, (d : ℚ) * ξ 0 = l) ∧ (ξ 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ 1 = l) ∧
            (ξ 0 = ξ' 0 → ∃ l : ℤ, (d : ℚ) * (ξ 1 - ξ' 1) = l) := by
  intro L hL S hS
  have hf : Continuous fun u : (A ℚ)ˣ => (u : A ℚ).2 :=
    continuous_snd.comp Units.continuous_val
  have hi : Continuous fun u : (A ℚ)ˣ => ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hp : ∀ i : Fin 2, Continuous fun v : Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ => v i :=
    fun i => continuous_apply i
  set Q0 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      p.1 0 * ((p.2⁻¹ : (A ℚ)ˣ) : A ℚ).2) '' (L ×ˢ S) with hQ0
  set Q2 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ => p.1 1 * (p.2 : A ℚ).2) '' (L ×ˢ S)
    with hQ2
  set Q1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × (A ℚ)ˣ =>
      (p.1 1 - p.2.1 1) * (p.2.2 : A ℚ).2) '' (L ×ˢ (L ×ˢ S)) with hQ1
  have c0 : IsCompact Q0 := (hL.prod hS).image
    (((hp 0).comp continuous_fst).mul (hi.comp continuous_snd))
  have c2 : IsCompact Q2 := (hL.prod hS).image
    (((hp 1).comp continuous_fst).mul (hf.comp continuous_snd))
  have c1 : IsCompact Q1 := (hL.prod (hL.prod hS)).image
    ((((hp 1).comp continuous_fst).sub ((hp 1).comp (continuous_fst.comp continuous_snd))).mul
      (hf.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d0, hd0, H0⟩ := den_of c0
  obtain ⟨d2, hd2, H2⟩ := den_of c2
  obtain ⟨d1, hd1, H1⟩ := den_of c1
  refine ⟨d1 * d2 * d0, by positivity, fun u hu b ξ ξ' h h' => ?_⟩
  have hu1 : (u : A ℚ).2 * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = 1 := by
    have h0 : (u : A ℚ) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := Units.mul_inv u
    exact congrArg Prod.snd h0
  have hu2 : ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = 1 := by
    rw [mul_comm, hu1]
  refine ⟨mul_int _ (H0 _ ⟨(_, u), ⟨h, hu⟩, ?_⟩), fun e => ?_, fun e => ?_⟩
  · change algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2 *
      ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
    rw [mul_assoc, hu1, mul_one]
  · have := H2 (ξ 1) ⟨(_, u), ⟨h, hu⟩, by
      change (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 * (u : A ℚ).2 = _
      rw [e, map_zero, zero_mul, zero_add, mul_assoc, hu2, mul_one]⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d1 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
  · have := H1 (ξ 1 - ξ' 1) ⟨(_, _, u), ⟨h, h', hu⟩, by
      change ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2 -
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 0) * b +
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ' 1)) * ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2) * (u : A ℚ).2 = _
      rw [e, ← sub_mul, mul_assoc, hu2, mul_one, map_sub]
      ring⟩
    obtain ⟨l, hl⟩ := this
    refine ⟨d2 * l * d0, ?_⟩
    push_cast
    rw [← hl]
    ring
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SchwartzBruhatTranslateDecayBound
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem abs_re' (x : A ℚ) : |UpperTheory.ConvolutionTheory.RankTwoDescent.re x| = ‖x.1 Rat.infinitePlace‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal Rat.infinitePlace)).norm_map_of_map_zero (map_zero _) (x.1 Rat.infinitePlace)

private theorem re_mul' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a * b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a * UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_mul, Pi.mul_apply]

private theorem re_add' (a b : A ℚ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.re (a + b) = UpperTheory.ConvolutionTheory.RankTwoDescent.re a + UpperTheory.ConvolutionTheory.RankTwoDescent.re b := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, map_add (f := _), Pi.add_apply]

private theorem pInf_id' (u : (TR.Rinf ℚ)ˣ) : TR.pInf ℚ (TR.infId ℚ u).val = u.val := by
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) = _
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  simp [h]

private theorem re_iy' {s : ℝ} (hs : s ≠ 0) : UpperTheory.ConvolutionTheory.RankTwoDescent.re (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ) = s := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.re, UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs, pInf_id']

private theorem snd_iy' {s : ℝ} (hs : s ≠ 0) : (UpperTheory.ConvolutionTheory.RankTwoDescent.iy s : A ℚ).2 = 1 := by
  simp only [UpperTheory.ConvolutionTheory.RankTwoDescent.iy, dite_eq_right hs]
  change (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) - 0 + 0 = 1
  simp

theorem UpperTheory.schwartzBruhat_translate_decay_bound :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ N : ℕ,
        ∃ (B κ : ℝ) (L : Set (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ)), 0 ≤ B ∧ 0 < κ ∧ κ ≤ 1 ∧ IsCompact L ∧
          ∀ (t : ℝ), ∀ k ∈ C, ∀ y : Fin 2 → A ℚ,
            ‖Φ fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j‖ ≤
                B * ((1 + κ * Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|)) ^ N)⁻¹ ∧
              (Φ (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * (y ᵥ* k.val) j) ≠ 0 → (fun j => (y j).2) ∈ L) := by
  intro Φ hΦ C hC N
  obtain ⟨C0, hC0, L0, hL0, hmaj⟩ := GroundTheory.Automorphic.GJGlobal.exists_majorant_pi hΦ N
  have hinv : Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val :=
    Units.continuous_val.comp continuous_inv
  have hent : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) => (k⁻¹).val i j :=
    fun i j => hinv.matrix_elem i j
  have hnorm : ∀ i j, Continuous fun k : GL (Fin 2) (A ℚ) =>
      ‖((k⁻¹).val i j).1 Rat.infinitePlace‖ := fun i j =>
    (((continuous_apply Rat.infinitePlace).comp continuous_fst).comp (hent i j)).norm
  obtain ⟨B1, hB1⟩ := hC.exists_bound_of_continuousOn
    (f := fun k : GL (Fin 2) (A ℚ) => ∑ i, ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hnorm i j).continuousOn
  have hBk0 : 0 ≤ max B1 0 := le_max_right _ _
  have hBk : ∀ k ∈ C, ∀ i j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re ((k⁻¹).val i j)| ≤ max B1 0 := by
    intro k hk i j
    rw [abs_re']
    have h1 := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB1 k hk))
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖((k⁻¹).val i j).1 Rat.infinitePlace‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  generalize max B1 0 = Bk at hBk0 hBk
  have hpos : 0 < 1 + 4 * Bk := by linarith
  let f : (Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ) × GL (Fin 2) (A ℚ) → Fin 2 → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun p j => p.1 0 * ((p.2⁻¹).val 0 j).2 + p.1 1 * ((p.2⁻¹).val 1 j).2
  have hf : Continuous f := by
    refine continuous_pi fun j => ?_
    exact (((continuous_apply 0).comp continuous_fst).mul
        (continuous_snd.comp ((hent 0 j).comp continuous_snd))).add
      (((continuous_apply 1).comp continuous_fst).mul
        (continuous_snd.comp ((hent 1 j).comp continuous_snd)))
  refine ⟨C0, 1 / (1 + 4 * Bk), f '' (L0 ×ˢ C), hC0, by positivity,
    (div_le_one hpos).2 (by linarith), (hL0.prod hC).image hf, fun t k hk y => ?_⟩
  have het : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  have hyz : ∀ j, y j = (y ᵥ* k.val) 0 * (k⁻¹).val 0 j + (y ᵥ* k.val) 1 * (k⁻¹).val 1 j := by
    intro j
    have h : (y ᵥ* k.val) ᵥ* (k⁻¹).val = y := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    conv_lhs => rw [← h]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  generalize hz : y ᵥ* k.val = z at hyz ⊢
  generalize hx : (fun j => (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j) = x
  have hxj : ∀ j, x j = (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ) * z j := fun j => by rw [← hx]
  have hxT : ∀ j, Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| ≤ ‖infPartPi x‖ := by
    intro j
    have e : Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z j)| = |UpperTheory.ConvolutionTheory.RankTwoDescent.re (x j)| := by
      rw [hxj, re_mul', re_iy' het, abs_mul, abs_of_pos (Real.exp_pos t)]
    rw [e, abs_re']
    exact (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ _).trans
      (norm_le_pi_norm (infPartPi x) j)
  have hyb : ∀ j, |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y j)| ≤
      Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) := by
    intro j
    rw [hyz j, re_add', re_mul', re_mul']
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, mul_add, mul_comm Bk, mul_comm Bk]
    exact add_le_add (mul_le_mul_of_nonneg_left (hBk k hk 0 j) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hBk k hk 1 j) (abs_nonneg _))
  have hT : 0 ≤ ‖infPartPi x‖ := norm_nonneg _
  have hkey : 1 / (1 + 4 * Bk) * Real.exp t *
      (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤ ‖infPartPi x‖ := by
    have hS : Real.exp t * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) ≤
        4 * Bk * ‖infPartPi x‖ := by
      have h0 := mul_le_mul_of_nonneg_left (hyb 0) (Real.exp_pos t).le
      have h1 := mul_le_mul_of_nonneg_left (hyb 1) (Real.exp_pos t).le
      have h2 : Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) ≤
          Bk * (‖infPartPi x‖ + ‖infPartPi x‖) := by
        rw [show Real.exp t * (Bk * (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|)) =
          Bk * (Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 0)| + Real.exp t * |UpperTheory.ConvolutionTheory.RankTwoDescent.re (z 1)|) by ring]
        exact mul_le_mul_of_nonneg_left (add_le_add (hxT 0) (hxT 1)) hBk0
      nlinarith
    rw [mul_assoc, one_div, inv_mul_le_iff₀ hpos]
    nlinarith
  have hm := hmaj x
  constructor
  · by_cases hmem : finPartPi x ∈ L0
    · rw [Set.indicator_of_mem hmem, mul_one] at hm
      refine hm.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      have hb : 0 ≤ 1 / (1 + 4 * Bk) * Real.exp t *
          (|UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 0)| + |UpperTheory.ConvolutionTheory.RankTwoDescent.re (y 1)|) := by positivity
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) N)
    · rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hm.trans (by positivity)
  · intro hne
    have hmem : finPartPi x ∈ L0 := by
      by_contra hmem
      rw [Set.indicator_of_notMem hmem, mul_zero] at hm
      exact hne (norm_le_zero_iff.1 hm)
    refine ⟨(finPartPi x, k), ⟨hmem, hk⟩, ?_⟩
    have hfin : ∀ j, finPartPi x j = (z j).2 := by
      intro j
      change (x j).2 = _
      rw [hxj]
      change (UpperTheory.ConvolutionTheory.RankTwoDescent.iy (Real.exp t) : A ℚ).2 * (z j).2 = _
      rw [snd_iy' het, one_mul]
    funext j
    simp only [f, hfin]
    rw [hyz j]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.SummableTsumInvOneAddHeightPowLe
private lemma gen {ι : Type*} (R : Set ι) (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) (τ : ι → ℤ × ℤ)
    (hinj : Set.InjOn τ R) (w : ℤ × ℤ → ℝ) (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x ∈ R, f x ≤ K * w (τ x)) :
    Summable (R.indicator f) ∧ ∑' x, R.indicator f x ≤ K * ∑' x, w x := by
  classical
  have hinj' : Function.Injective (fun x : R => τ x.1) := by
    intro a b h
    exact Subtype.ext (hinj a.2 b.2 h)
  have hs : Summable (fun x : R => w (τ x.1)) := hw.comp_injective hinj'
  have hs2 : Summable (fun x : R => f x.1) :=
    Summable.of_nonneg_of_le (fun x => hf _) (fun x => hb x.1 x.2) (hs.mul_left K)
  refine ⟨summable_subtype_iff_indicator.mp hs2, ?_⟩
  rw [← tsum_subtype R f]
  calc ∑' x : R, f x.1 ≤ ∑' x : R, K * w (τ x.1) :=
        hs2.tsum_le_tsum (fun x => hb x.1 x.2) (hs.mul_left K)
    _ = K * ∑' x : R, w (τ x.1) := tsum_mul_left
    _ ≤ K * ∑' x, w x := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Summable.tsum_le_tsum_of_inj _ hinj' (fun c _ => hw0 c) (fun _ => le_rfl) hs hw

private lemma wsum1 : Summable (fun l : ℤ => ((1 + |(l : ℝ)|) ^ 2)⁻¹) := by
  have h0 : Summable (fun m : ℕ => ((1 + (m : ℝ)) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr (fun m => ?_)
    push_cast
    rw [one_div, add_comm]
  apply Summable.of_nat_of_neg
  · refine h0.congr (fun m => ?_)
    simp
  · refine h0.congr (fun m => ?_)
    simp

private lemma wsum : Summable (fun p : ℤ × ℤ => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹) :=
  Summable.mul_of_nonneg wsum1 wsum1 (fun _ => by positivity) (fun _ => by positivity)

private lemma round_bd (x : ℝ) : 1 + |((round x : ℤ) : ℝ)| ≤ 2 * (1 + |x|) := by
  have h := abs_sub_round x
  have h2 : |((round x : ℤ) : ℝ)| ≤ |x| + |x - round x| := by
    have := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at this
    linarith
  linarith [abs_nonneg x]

private lemma nu_lower (κ Bu α T d ν a b : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hBu : 1 ≤ Bu)
    (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hν : ν = a * α + b / α) :
    (κ / (Bu * d)) * (κ / (T * d)) * ((1 + d * a) * (1 + d * b)) ≤ (1 + κ * ν) ^ 2 := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hδ : κ / (Bu * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hδ' : κ / (T * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hA : (κ / (Bu * d)) * (1 + d * a) ≤ 1 + κ * (a * α) := by
    have e : (κ / (Bu * d)) * (1 + d * a) = κ / (Bu * d) + κ * (a * Bu⁻¹) := by
      field_simp
    rw [e]
    have : κ * (a * Bu⁻¹) ≤ κ * (a * α) := by gcongr
    linarith
  have hB : (κ / (T * d)) * (1 + d * b) ≤ 1 + κ * (b / α) := by
    have e : (κ / (T * d)) * (1 + d * b) = κ / (T * d) + κ * (b / T) := by
      field_simp
    rw [e]
    have : κ * (b / T) ≤ κ * (b / α) := by gcongr
    linarith
  have hA0 : 0 ≤ κ * (a * α) := by positivity
  have hB0 : 0 ≤ κ * (b / α) := by positivity
  have hprod : ((κ / (Bu * d)) * (1 + d * a)) * ((κ / (T * d)) * (1 + d * b))
      ≤ (1 + κ * (a * α)) * (1 + κ * (b / α)) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have e2 : (1 + κ * ν) = 1 + κ * (a * α) + κ * (b / α) := by rw [hν]; ring
  rw [e2]
  nlinarith [mul_nonneg hA0 hB0]

private lemma lower_bound_first_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hT : 1 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * a) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ a := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have h3 : Bu⁻¹ * T⁻¹ ≤ α := by
    have : Bu⁻¹ * T⁻¹ ≤ Bu⁻¹ * 1 := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ a * α := mul_le_mul h1 h3 (by positivity) ha
  have h4 : 0 ≤ b / α := by positivity
  linarith

private lemma lower_bound_second_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T)
    (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * b) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ b := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : Bu⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBu
  have h3 : T⁻¹ ≤ α⁻¹ := inv_anti₀ hα0 hαT
  have h5 : Bu⁻¹ * T⁻¹ ≤ α⁻¹ := by
    have : Bu⁻¹ * T⁻¹ ≤ 1 * T⁻¹ := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e, div_eq_mul_inv]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ b * α⁻¹ := mul_le_mul h1 h5 (by positivity) hb
  have h4 : 0 ≤ a * α := by positivity
  linarith

private lemma term_bd (n : ℕ) (κ Bu α T d ν a b t L M : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (hν : ν = a * α + b / α) (hν1 : 1 / (d * Bu * T) ≤ ν) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hL : 1 + L ≤ 2 * (1 + d * a)) (hM : 1 + M ≤ 2 * (1 + d * b)) :
    ((1 + κ * Real.exp t * ν) ^ (n + 4))⁻¹ ≤
      (16 * (d * Bu / κ) ^ n * ((d / κ) * (Bu * d / κ)) ^ 2) * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) *
        (((1 + L) ^ 2)⁻¹ * ((1 + M) ^ 2)⁻¹) := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hE1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  set E := Real.exp t with hE
  have hE0 : 0 < E := by linarith
  have hlow := nu_lower κ Bu α T d ν a b hd hκ hκ1 hBu hα hαT hT ha hb hν
  set X := 1 + κ * E * ν with hX
  have hX1 : κ * E * (1 / (d * Bu * T)) ≤ X := by
    have : κ * E * (1 / (d * Bu * T)) ≤ κ * E * ν := by gcongr
    have h0 : 0 ≤ κ * E * ν := by positivity
    linarith
  have hX2 : 1 + κ * ν ≤ X := by
    have : κ * ν ≤ κ * E * ν := by
      have : κ * 1 ≤ κ * E := by gcongr
      nlinarith
    linarith
  have hQ : (1 + L) * (1 + M) ≤ 4 * ((1 + d * a) * (1 + d * b)) := by
    have := mul_le_mul hL hM (by positivity) (by positivity)
    nlinarith
  set c1 := κ / (Bu * d) with hc1
  set c2 := κ / (T * d) with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  have hY : (c1 * c2 / 4) * ((1 + L) * (1 + M)) ≤ (1 + κ * ν) ^ 2 := by
    have h1 : c1 * c2 * ((1 + L) * (1 + M)) ≤ c1 * c2 * (4 * ((1 + d * a) * (1 + d * b))) := by gcongr
    nlinarith
  have hY0 : 0 < (c1 * c2 / 4) * ((1 + L) * (1 + M)) := by positivity
  have hX4 : ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ X ^ 4 := by
    calc ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ ((1 + κ * ν) ^ 2) ^ 2 := by gcongr
      _ = (1 + κ * ν) ^ 4 := by ring
      _ ≤ X ^ 4 := by
        have : 0 ≤ 1 + κ * ν := by positivity
        gcongr
  have hXn : (κ * E * (1 / (d * Bu * T))) ^ n ≤ X ^ n := by gcongr
  have hmain : (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2
      ≤ X ^ (n + 4) := by
    rw [pow_add]
    exact mul_le_mul hXn hX4 (by positivity) (by positivity)
  have hpos : 0 < (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 := by
    positivity
  refine (inv_anti₀ hpos hmain).trans (le_of_eq ?_)
  have hexp : Real.exp (-((n : ℝ) * t)) = (E ^ n)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul]
  rw [hexp, hc1, hc2, pow_add T n 2]
  have e1 : κ * E * (1 / (d * Bu * T)) = (κ / (d * Bu)) * E * T⁻¹ := by
    field_simp
  have e2 : d * Bu / κ = (κ / (d * Bu))⁻¹ := by
    rw [inv_div]
  rw [e1, e2, mul_pow, mul_pow, inv_pow, inv_pow]
  have hu : κ / (d * Bu) ≠ 0 := by positivity
  have hun : (κ / (d * Bu)) ^ n ≠ 0 := pow_ne_zero _ hu
  have hEn : E ^ n ≠ 0 := pow_ne_zero _ hE0.ne'
  have hTn : T ^ n ≠ 0 := pow_ne_zero _ hT0.ne'
  generalize (κ / (d * Bu)) ^ n = U at *
  generalize E ^ n = V at *
  generalize T ^ n = W' at *
  have hL1 : 1 + L ≠ 0 := by positivity
  have hM1 : 1 + M ≠ 0 := by positivity
  field_simp
  ring

theorem UpperTheory.summable_tsum_inv_one_add_height_pow_le :
    ∀ (n d : ℕ) (κ Bu : ℝ), 0 < d → 0 < κ → κ ≤ 1 → 1 ≤ Bu → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (R : Set {r : Fin 2 → ℚ // r ≠ 0}) (β α T t : ℝ), 0 ≤ t → Bu⁻¹ ≤ α → α ≤ T → 1 ≤ T →
          (∀ ξ ∈ R, ∃ l : ℤ, (d : ℚ) * ξ.1 0 = l) →
          (∀ ξ ∈ R, ξ.1 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ.1 1 = l) →
          (∀ ξ ∈ R, ∀ ξ' ∈ R, ξ.1 0 = ξ'.1 0 → ∃ l : ℤ, (d : ℚ) * (ξ.1 1 - ξ'.1 1) = l) →
          Summable (R.indicator fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ∧
          ∑' ξ : {r : Fin 2 → ℚ // r ≠ 0}, R.indicator (fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ξ
            ≤ B * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) := by
  intro n d κ Bu hd hκ hκ1 hBu
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hBu0 : 0 < Bu := by linarith
  set w : ℤ × ℤ → ℝ := fun p => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹ with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  set C : ℝ := 16 * ((d : ℝ) * Bu / κ) ^ n * (((d : ℝ) / κ) * (Bu * (d : ℝ) / κ)) ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C * ∑' p, w p, mul_nonneg hC0 (tsum_nonneg hw0), ?_⟩
  intro R β α T t ht hα hαT hT h1 h2 h3
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  set τ : {r : Fin 2 → ℚ // r ≠ 0} → ℤ × ℤ := fun ξ =>
    (round ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ)),
      round ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))) with hτ
  have hinj : Set.InjOn τ R := by
    intro ξ hξ ξ' hξ' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    simp only [hτ] at he1 he2
    obtain ⟨l, hl⟩ := h1 ξ hξ
    obtain ⟨l', hl'⟩ := h1 ξ' hξ'
    have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
    have hlR' : (d : ℝ) * ((ξ'.1 0 : ℚ) : ℝ) = (l' : ℝ) := by exact_mod_cast hl'
    rw [hlR, hlR', round_intCast, round_intCast] at he1
    have h0 : ξ.1 0 = ξ'.1 0 := by
      have : (d : ℚ) * ξ.1 0 = (d : ℚ) * ξ'.1 0 := by rw [hl, hl', he1]
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne') this
    obtain ⟨j, hj⟩ := h3 ξ hξ ξ' hξ' h0
    have hjR : (d : ℝ) * (((ξ.1 1 : ℚ) : ℝ) - ((ξ'.1 1 : ℚ) : ℝ)) = (j : ℝ) := by exact_mod_cast hj
    have e : (d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ))
        = (d : ℝ) * (((ξ'.1 0 : ℚ) : ℝ) * β + ((ξ'.1 1 : ℚ) : ℝ)) + (j : ℝ) := by
      rw [← hjR, h0]; ring
    rw [e, round_add_intCast] at he2
    have hj0 : j = 0 := by linarith
    have h1' : ξ.1 1 = ξ'.1 1 := by
      rw [hj0] at hj
      have : (d : ℚ) * (ξ.1 1 - ξ'.1 1) = 0 := by simpa using hj
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by exact_mod_cast hd.ne')
      · exact sub_eq_zero.mp h
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1'
  have hb : ∀ ξ ∈ R, ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
      ≤ (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) * w (τ ξ) := by
    intro ξ hξ
    have hν1 : 1 / ((d : ℝ) * Bu * T) ≤ |((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      by_cases hz : ξ.1 0 = 0
      · obtain ⟨l, hl⟩ := h2 ξ hξ hz
        have hlR : (d : ℝ) * ((ξ.1 1 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hne : ξ.1 1 ≠ 0 := by
          intro h
          apply ξ.2
          funext i
          fin_cases i
          · exact hz
          · exact h
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 1 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hne h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_second_case _ _ _ _ _ _ hd1 hBu hα hαT hT (abs_nonneg _) (abs_nonneg _)
        have hz' : ((ξ.1 0 : ℚ) : ℝ) = 0 := by rw [hz]; simp
        rw [hz', zero_mul, zero_add]
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 1 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
      · obtain ⟨l, hl⟩ := h1 ξ hξ
        have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 0 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hz h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_first_case _ _ _ _ _ _ hd1 hBu hα hT (abs_nonneg _) (abs_nonneg _)
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 0 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
    have hL := round_bd ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ))
    have hM := round_bd ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))
    rw [abs_mul, abs_of_pos hd0] at hL hM
    exact term_bd n κ Bu α T (d : ℝ) _ _ _ t _ _ hd1 hκ hκ1 hBu hα hαT hT (abs_nonneg _)
      (abs_nonneg _) ht rfl hν1 (abs_nonneg _) (abs_nonneg _) hL hM
  have hf : ∀ ξ : {r : Fin 2 → ℚ // r ≠ 0}, 0 ≤ ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹ := by
    intro ξ
    positivity
  obtain ⟨hs, hle⟩ := gen R _ hf τ hinj w wsum hw0 (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2))
    (by positivity) hb
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  ring
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

namespace UpperTheory.QuaternionSwap

private noncomputable def Yv (b : A ℚ) (a : (A ℚ)ˣ) (ξ : Fin 2 → ℚ) : Fin 2 → A ℚ :=
  ![rt (ξ 0) * (a : A ℚ), (rt (ξ 0) * b + rt (ξ 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)]

private theorem row_eq (b : A ℚ) (a : (A ℚ)ˣ) (k : GL (Fin 2) (A ℚ)) (ξ : Fin 2 → ℚ) :
    (fun i => rt (ξ i)) ᵥ* (gl (nU b * mD a) * k).val = Yv b a ξ ᵥ* k.val := by
  have h1 : (gl (nU b * mD a) * k).val = (nU b * mD a).val * k.val := rfl
  rw [h1, ← Matrix.vecMul_vecMul]
  congr 1
  have h2 : (nU b * mD a).val = !![1, b; 0, 1] * !![(a : A ℚ), 0; 0, ((a⁻¹ : (A ℚ)ˣ) : A ℚ)] := rfl
  rw [h2]
  funext j
  fin_cases j <;> simp [Yv, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply] <;> ring

private def swapQ (q : ℚ) (hq : q ≠ 0) : Rw ℚ ≃ Rw ℚ where
  toFun ξ := ⟨![q * ξ.1 0, q⁻¹ * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  invFun ξ := ⟨![q⁻¹ * ξ.1 0, q * ξ.1 1], fun h => ξ.2 (by
    funext i
    fin_cases i
    · have := congrFun h 0
      simpa [hq] using this
    · have := congrFun h 1
      simpa [hq] using this)⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]
  right_inv ξ := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [hq]

private theorem Yv_swap (q : ℚ) (hq : q ≠ 0) (b : A ℚ) (a a' : (A ℚ)ˣ) (ha : (a' : A ℚ) = rt q * (a : A ℚ))
    (ξ : Rw ℚ) : Yv b a (swapQ q hq ξ).1 = Yv (rt (q ^ 2) * b) a' ξ.1 := by
  have hqq : rt q * rt q⁻¹ = (1 : A ℚ) := by
    rw [← map_mul, mul_inv_cancel₀ hq, map_one]
  have hinv : ((a'⁻¹ : (A ℚ)ˣ) : A ℚ) = rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ha]
    calc rt q * (a : A ℚ) * (rt q⁻¹ * ((a⁻¹ : (A ℚ)ˣ) : A ℚ))
        = (rt q * rt q⁻¹) * ((a : A ℚ) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) := by ring
      _ = 1 := by rw [hqq, Units.mul_inv, one_mul]
  have rm : ∀ x y : ℚ, rt (x * y) = rt x * rt y := fun x y => map_mul (algebraMap ℚ (A ℚ)) x y
  funext j
  fin_cases j
  · change rt (q * ξ.1 0) * (a : A ℚ) = rt (ξ.1 0) * (a' : A ℚ)
    rw [ha, rm]
    ring
  · change (rt (q * ξ.1 0) * b + rt (q⁻¹ * ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) =
      (rt (ξ.1 0) * (rt (q ^ 2) * b) + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ)
    have e2 : rt (q ^ 2) = rt q * rt q := by rw [pow_two, rm]
    rw [hinv, rm, rm, e2]
    have e : rt q = rt q * rt q * rt q⁻¹ := by rw [mul_assoc, hqq, mul_one]
    calc (rt q * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ)
        = ((rt q * rt q * rt q⁻¹) * rt (ξ.1 0) * b + rt q⁻¹ * rt (ξ.1 1)) * ((a⁻¹ : (A ℚ)ˣ) : A ℚ) := by rw [← e]
      _ = _ := by ring

private theorem re_mul (x y : A ℚ) : re (x * y) = re x * re y := by
  simp [re, map_mul]
private theorem re_add (x y : A ℚ) : re (x + y) = re x + re y := by
  simp [re, map_add (f := _)]
private theorem re_rat (q : ℚ) : re (rt q) = (q : ℝ) := by
  exact eq_ratCast (((Pi.evalRingHom (fun _ : InfinitePlace ℚ => ℝ) Rat.infinitePlace).comp
    (TR.pInf ℚ)).comp (algebraMap ℚ (A ℚ))) q
private theorem re_inv (a : (A ℚ)ˣ) : re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = (re (a : A ℚ))⁻¹ := by
  have h : re (a : A ℚ) * re ((a⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
    rw [← re_mul, Units.mul_inv]
    simp [re]
  exact eq_inv_of_mul_eq_one_right h

end UpperTheory.QuaternionSwap

open UpperTheory.QuaternionSwap in
theorem UpperTheory.norm_thetaSeries_siegelSet_le_exp :
    ∀ (Φ : (Fin 2 → A ℚ) → ℂ), Φ ∈ schwartzBruhatPi (K := ℚ) (ι := Fin 2) → ∀ (C : Set (GL (Fin 2) (A ℚ))), IsCompact C → ∀ (c : ℝ), 0 < c → ∀ n : ℕ,
        ∃ (r : ℕ) (B : ℝ), ∀ t : ℝ, 0 ≤ t → ∀ (b : A ℚ) (a : (A ℚ)ˣ), ∀ k ∈ C, c ≤ ab a →
          ‖ThR Φ t (gl (nU b * mD a) * k)‖ ≤ B * Real.exp (-((n : ℝ) * t)) * ab a ^ r := by
  intro Φ hΦ C hC c hc n
  obtain ⟨B0, κ, L, hB0, hκ, hκ1, hL, hmaj⟩ := UpperTheory.schwartzBruhat_translate_decay_bound Φ hΦ C hC (n + 4)
  obtain ⟨S, Bu, hS, hBu, hred⟩ := UpperTheory.exists_rat_mul_idele_finitePart_mem_compact_of_le_norm c hc
  obtain ⟨d, hd, hden⟩ := UpperTheory.exists_common_denom_of_isCompact_unipotent_translates L hL S hS
  obtain ⟨B1, hB1, hsum⟩ := UpperTheory.summable_tsum_inv_one_add_height_pow_le n d κ Bu hd hκ hκ1 hBu
  refine ⟨n + 2, B0 * B1 * (Bu / c) ^ (n + 2), fun t ht b a k hk hca => ?_⟩
  obtain ⟨q, a', u, hq, ha', hu, hf, hfi, hlo, hhi⟩ := hred a hca
  set b' : A ℚ := rt (q ^ 2) * b with hb'
  set α : ℝ := |re (a' : A ℚ)| with hα
  set β : ℝ := re b' with hβ
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.2 (by linarith)) hlo
  have hab : 0 < ab a := lt_of_lt_of_le hc hca
  set T : ℝ := Bu * (ab a / c) with hT
  have hT1 : 1 ≤ T := by
    have : 1 ≤ ab a / c := (one_le_div hc).2 hca
    nlinarith
  let R : Set (Rw ℚ) := {ξ | (fun j => (Yv b' a' ξ.1 j).2) ∈ L}
  let Wt : Rw ℚ → ℝ := fun ξ =>
    ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
  have hfin : ∀ ξ : Fin 2 → ℚ, (fun j => (Yv b' a' ξ j).2) =
      ![algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * (u : A ℚ).2,
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 0) * b'.2 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (ξ 1)) *
          ((u⁻¹ : (A ℚ)ˣ) : A ℚ).2] := by
    intro ξ
    funext j
    fin_cases j
    · change (rt (ξ 0)).2 * (a' : A ℚ).2 = _
      rw [hf]
      rfl
    · change ((rt (ξ 0)).2 * b'.2 + (rt (ξ 1)).2) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ).2 = _
      rw [hfi]
      rfl
  have hR : ∀ ξ ∈ R, ∀ ξ' ∈ R, _ := fun ξ h ξ' h' =>
    hden u hu b'.2 ξ.1 ξ'.1 (by have := h; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
      (by have := h'; simp only [R, Set.mem_setOf_eq, hfin] at this; exact this)
  obtain ⟨hs, hle⟩ := hsum R β α T t ht hlo hhi hT1 (fun ξ h => (hR ξ h ξ h).1) (fun ξ h => (hR ξ h ξ h).2.1)
    (fun ξ h ξ' h' => (hR ξ h ξ' h').2.2)
  have hterm : ∀ ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ ≤ B0 * R.indicator Wt ξ := by
    intro ξ
    obtain ⟨h1, h2⟩ := hmaj t k hk (Yv b' a' ξ.1)
    have e0 : |re (Yv b' a' ξ.1 0)| = |((ξ.1 0 : ℚ) : ℝ)| * α := by
      change |re (rt (ξ.1 0) * (a' : A ℚ))| = _
      rw [re_mul, re_rat, abs_mul]
    have e1 : |re (Yv b' a' ξ.1 1)| = |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      change |re ((rt (ξ.1 0) * b' + rt (ξ.1 1)) * ((a'⁻¹ : (A ℚ)ˣ) : A ℚ))| = _
      rw [re_mul, re_add, re_mul, re_rat, re_rat, re_inv, abs_mul, abs_inv, div_eq_mul_inv]
    by_cases hξ : ξ ∈ R
    · rw [Set.indicator_of_mem hξ]
      rw [e0, e1] at h1
      exact h1
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have h0 : (Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j) = 0 := by
        by_contra h
        exact hξ (h2 h)
      rw [h0, norm_zero]
  have hrew : ThR Φ t (gl (nU b * mD a) * k) =
      ∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j := by
    unfold ThR
    rw [← (swapQ q hq).tsum_eq]
    refine tsum_congr fun ξ => ?_
    rw [row_eq, Yv_swap q hq b a a' ha' ξ]
  have hsn : Summable fun ξ : Rw ℚ => ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left B0)
  rw [hrew]
  calc ‖∑' ξ : Rw ℚ, Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖
      ≤ ∑' ξ : Rw ℚ, ‖Φ fun j => (iy (Real.exp t) : A ℚ) * (Yv b' a' ξ.1 ᵥ* k.val) j‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' ξ : Rw ℚ, B0 * R.indicator Wt ξ := hsn.tsum_le_tsum hterm (hs.mul_left _)
    _ = B0 * ∑' ξ : Rw ℚ, R.indicator Wt ξ := tsum_mul_left
    _ ≤ B0 * (B1 * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) := mul_le_mul_of_nonneg_left hle hB0
    _ = B0 * B1 * (Bu / c) ^ (n + 2) * Real.exp (-((n : ℝ) * t)) * ab a ^ (n + 2) := by
        have : T = Bu / c * ab a := by rw [hT]; ring
        rw [this, mul_pow]
        ring
