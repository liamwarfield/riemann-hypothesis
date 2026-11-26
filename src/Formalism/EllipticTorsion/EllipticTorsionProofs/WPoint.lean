module

public import Formalism.EllipticTorsion.WChordSeries

@[expose] public section

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassPointSeriesTail

def wTail {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3

theorem wTail_dvd {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, rfl⟩ := h
  refine ⟨C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 +
    C W.a₆ * X ^ (2 * j + 1) * u ^ 3, ?_⟩
  unfold wTail
  ring

theorem factor {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (hw : WFixed W w) : ∃ e : PowerSeries R, w = X ^ 3 * (1 + X * e) := by
  have hsplit : w = X ^ 3 + wTail W w := by
    unfold wTail
    conv_lhs => rw [hw.2]
    ring
  have d1 : (X : PowerSeries R) ^ 1 ∣ w := by
    rw [pow_one, PowerSeries.X_dvd_iff]
    exact hw.1
  have d2 : (X : PowerSeries R) ^ 2 ∣ w := by
    rw [hsplit]
    exact dvd_add (pow_dvd_pow X (by norm_num)) (wTail_dvd W w 1 le_rfl d1)
  have d3 : (X : PowerSeries R) ^ 3 ∣ w := by
    rw [hsplit]
    exact dvd_add dvd_rfl (wTail_dvd W w 2 (by norm_num) d2)
  obtain ⟨e, he⟩ := wTail_dvd W w 3 (by norm_num) d3
  exact ⟨e, by rw [hsplit, he]; ring⟩

end WeierstrassPointSeriesTail

open WeierstrassPointSeriesTail in
theorem wSeriesNonsingularPoint_holds : WPoint := by
  intro K _ W w hw σ _ s hs0 hs
  have : IsDomain (MvPowerSeries σ K) := NoZeroDivisors.to_isDomain _
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hE : w.subst s = s ^ 3 + MvPowerSeries.C W.a₁ * s * w.subst s +
      MvPowerSeries.C W.a₂ * s ^ 2 * w.subst s + MvPowerSeries.C W.a₃ * (w.subst s) ^ 2 +
      MvPowerSeries.C W.a₄ * s * (w.subst s) ^ 2 + MvPowerSeries.C W.a₆ * (w.subst s) ^ 3 := by
    conv_lhs => rw [hw.2]
    simp only [PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
      PowerSeries.subst_X hsub, PowerSeries.subst_C]
  obtain ⟨e, he⟩ := factor W w hw
  have hfac : w.subst s = s ^ 3 * (1 + s * e.subst s) := by
    rw [← PowerSeries.coe_substAlgHom hsub, he]
    simp [PowerSeries.substAlgHom_X]
  have hwc : MvPowerSeries.constantCoeff (w.subst s) = 0 := by
    rw [hfac]
    simp [hs0]
  have hws0 : w.subst s ≠ 0 := by
    rw [hfac]
    refine mul_ne_zero (pow_ne_zero 3 hs) (fun h0 => ?_)
    have := congrArg MvPowerSeries.constantCoeff h0
    simp [hs0] at this
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have hV : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hws0
  have hC : ∀ a : K, algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries σ K)) a := fun a =>
    (IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) a).symm
  have hE' := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hE
  simp only [map_add (f := _), map_mul, map_pow, hC] at hE'
  have hx : xOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s := by
    simp only [xOf]
    exact div_mul_cancel₀ _ hV
  have hy : yOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      -1 := by
    simp only [yOf]
    rw [div_mul_cancel₀ _ hV]
  set Z := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s
  set V := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)
  set x := xOf w s
  set y := yOf w s
  set A₁ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₁
  set A₂ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₂
  set A₃ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₃
  set A₄ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₄
  set A₆ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₆
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  refine ⟨?_, ?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 3 hV)
    linear_combination hE' + (V * (y * V - 1) + A₁ * V * Z + A₃ * V ^ 2) * hy +
      (A₁ * V * (y * V) - ((x * V) ^ 2 + (x * V) * Z + Z ^ 2) - A₂ * V * (x * V + Z) - A₄ * V ^ 2) * hx
  · by_contra hcon
    push Not at hcon
    obtain ⟨hP, hQ⟩ := hcon
    have hD0 : (1 - MvPowerSeries.C W.a₁ * s - 2 * MvPowerSeries.C W.a₃ * w.subst s -
        MvPowerSeries.C W.a₂ * s ^ 2 - 2 * MvPowerSeries.C W.a₄ * s * w.subst s -
        3 * MvPowerSeries.C W.a₆ * (w.subst s) ^ 2 : MvPowerSeries σ K) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff h0
      simp [hs0, hwc] at this
    apply hD0
    apply hinj
    rw [map_zero]
    apply (mul_eq_zero.mp _).resolve_right hV
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, hC]
    linear_combination V ^ 2 * hQ - Z * V ^ 2 * hP + 3 * hE' + (-2 * V + Z * A₁ * V) * hy +
      (-A₁ * V - 3 * Z * (x * V + Z) - 2 * A₂ * Z * V) * hx

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.WeierstrassSubstitution

theorem mvsubst_psubst {K : Type u} [Field K] {τ σ : Type} (w : PowerSeries K)
    (a : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (b : τ → MvPowerSeries σ K) (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (w.subst a) = w.subst (MvPowerSeries.subst b a) := by
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply ha' hb]

theorem eq_inv_of_map {L F : Type*} [CommRing L] [Field F] (f : L →+* F) {a b : L}
    (h : a * b = 1) : f b = (f a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, h, map_one])

theorem eq_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s 0) : s = 0 := by
  unfold Formalism.ELL.WEqAt at h
  simp only [mul_zero, smul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h.symm

theorem ne_zero_of_weq {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s v : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s v) (hs : s ≠ 0) : v ≠ 0 := by
  rintro rfl
  exact hs (eq_zero_of_weq h)

end Formalism.ELL.WeierstrassSubstitution

open Formalism.ELL.WeierstrassSubstitution in
theorem Formalism.ELL.wChordSubst_of (hU : Formalism.ELL.WSubstUnique.{u}) : Formalism.ELL.WChordSubst.{u} := by
  intro K _ W w hw F₂ hF0 hch σ _ s t hs ht hs0 ht0 hxst
  classical

  have chord_forms : ∀ (L : Type u) [Field L] (V : WeierstrassCurve.Affine L)
      (x0 x1 w0 w1 D PX : L), w0 ≠ 0 → w1 ≠ 0 → D = x0 * w1 - x1 * w0 → D ≠ 0 →
      PX = (w0 - w1) ^ 2 * w0 * w1 + V.a₁ * (w0 - w1) * D * w0 * w1
        - V.a₂ * D ^ 2 * w0 * w1 - x0 * D ^ 2 * w1 - x1 * D ^ 2 * w0 →
      V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          PX / (D ^ 2 * w0 * w1) ∧
      V.addY (x0 / w0) (x1 / w1) (-1 / w0) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
          (-((w0 - w1) * (PX - x0 * D ^ 2 * w1)) + D ^ 3 * w1 - V.a₁ * D * PX
            - V.a₃ * D ^ 3 * w0 * w1) / (D ^ 3 * w0 * w1) := by
    intro L _ V x0 x1 w0 w1 D PX h0 h1 hD hd hPX
    have hl : (-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1) = (w0 - w1) / D := by
      rw [hD]
      rw [hD] at hd
      field_simp
      ring
    have hX : V.addX (x0 / w0) (x1 / w1) ((-1 / w0 - -1 / w1) / (x0 / w0 - x1 / w1)) =
        PX / (D ^ 2 * w0 * w1) := by
      rw [hl, hPX]
      simp only [WeierstrassCurve.Affine.addX]
      field_simp
    refine ⟨hX, ?_⟩
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    rw [hX, hl]
    field_simp
    ring
  have hv : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp [hs, ht]
  set φ := MvPowerSeries.substAlgHom (R := K) hv with hφ
  have φe : ∀ g, φ g = MvPowerSeries.subst ![s, t] g := fun g => by
    rw [hφ, MvPowerSeries.coe_substAlgHom]
  have φX0 : φ (MvPowerSeries.X 0) = s := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φX1 : φ (MvPowerSeries.X 1) = t := by rw [φe, MvPowerSeries.subst_X hv]; rfl
  have φw : ∀ g : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff g = 0 →
      φ (w.subst g) = w.subst (φ g) := fun g hg => by
    rw [φe, φe, mvsubst_psubst w g hg _ hv]
  have φw0 : φ (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) = w.subst s := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 0), φX0]
  have φw1 : φ (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = w.subst t := by
    rw [φw _ (MvPowerSeries.constantCoeff_X 1), φX1]
  have φwF : φ (w.subst F₂) = w.subst (φ F₂) := φw F₂ hF0
  have injA := IsFractionRing.injective (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))
  have injB := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))

  have ws0 : w.subst s ≠ 0 := ne_zero_of_weq (hU K W w hw σ s hs).1 hs0
  have wt0 : w.subst t ≠ 0 := ne_zero_of_weq (hU K W w hw σ t ht).1 ht0
  have dB : s * w.subst t - t * w.subst s ≠ 0 := by
    intro h
    apply hxst
    unfold Formalism.ELL.xOf
    rw [div_eq_div_iff ((map_ne_zero_iff _ injB).2 ws0) ((map_ne_zero_iff _ injB).2 wt0),
      ← map_mul, ← map_mul]
    congr 1
    linear_combination h
  have w00 : w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    ws0 (by rw [← φw0, h, map_zero])
  have w10 : w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    wt0 (by rw [← φw1, h, map_zero])
  have φD : φ (MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) =
      s * w.subst t - t * w.subst s := by
    simp only [map_sub, map_mul, φX0, φX1, φw0, φw1]
  have dA : MvPowerSeries.X 0 * w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) -
      MvPowerSeries.X 1 * w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 := fun h =>
    dB (by rw [← φD, h, map_zero])
  unfold Formalism.ELL.ChordAt at hch ⊢
  simp only at hch ⊢
  unfold Formalism.ELL.xOf Formalism.ELL.yOf at hch ⊢
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injA).2 w00)
      ((map_ne_zero_iff _ injA).2 w10) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injA).2 dA) rfl).2] at hch
  rw [(chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).1,
    (chord_forms _ _ _ _ _ _ _ _ ((map_ne_zero_iff _ injB).2 ws0)
      ((map_ne_zero_iff _ injB).2 wt0) rfl
      (by rw [← map_mul, ← map_mul, ← map_sub]; exact (map_ne_zero_iff _ injB).2 dB) rfl).2]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃] at hch ⊢
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K)
    (FractionRing (MvPowerSeries (Fin 2) K))] at hch
  simp only [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K)
    (FractionRing (MvPowerSeries σ K))]
  have iw0 := (map_ne_zero_iff _ injA).2 w00
  have iw1 := (map_ne_zero_iff _ injA).2 w10
  have idA : algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 0) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) -
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K)) (MvPowerSeries.X 1) *
      algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))
        (w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injA).2 dA
  have jw0 := (map_ne_zero_iff _ injB).2 ws0
  have jw1 := (map_ne_zero_iff _ injB).2 wt0
  have jdB : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst t) -
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) t *
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    exact (map_ne_zero_iff _ injB).2 dB
  obtain ⟨hx, hy⟩ := hch
  rw [← φe F₂]
  by_cases hwF : w.subst F₂ = 0
  ·
    have hF : F₂ = 0 := eq_zero_of_weq (hwF ▸ (hU K W w hw (Fin 2) F₂ hF0).1)
    have hr : w.subst (φ F₂) = 0 := by
      rw [hF, map_zero]
      exact ((hU K W w hw σ 0 (map_zero _)).2 0 (map_zero _)
        (by unfold Formalism.ELL.WEqAt; simp)).symm
    rw [hwF, map_zero, div_zero, eq_comm, div_eq_zero_iff] at hx hy
    have hx' := hx.resolve_right (by simp [iw0, iw1, idA])
    have hy' := hy.resolve_right (by simp [iw0, iw1, idA])
    simp only [← map_mul, ← map_sub, ← map_add (f := _), ← map_pow, ← map_neg] at hx' hy'
    rw [map_eq_zero_iff _ injA] at hx' hy'
    have hxB := congrArg φ hx'
    have hyB := congrArg φ hy'
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_neg, map_zero, AlgHom.commutes,
      φX0, φX1, φw0, φw1] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_neg, map_zero] at hxF hyF
    rw [hr, map_zero, div_zero, div_zero]
    constructor
    · rw [hxF, zero_div]
    · rw [hyF, zero_div]
  · have iwF := (map_ne_zero_iff _ injA).2 hwF
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA])] at hx
    rw [div_eq_div_iff iwF (by simp [iw0, iw1, idA]), neg_one_mul] at hy
    simp only [← map_mul, ← map_sub, ← map_add (f := _), ← map_pow, ← map_neg] at hx hy
    rw [injA.eq_iff] at hx hy
    have hxB := congrArg φ hx
    have hyB := congrArg φ hy
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_neg, AlgHom.commutes,
      φX0, φX1, φw0, φw1, φwF] at hxB hyB
    have hxF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hxB
    have hyF := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hyB
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_neg] at hxF hyF

    have jwr : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst (φ F₂)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at hyF
      revert hyF
      simp [jw0, jw1, jdB]
    constructor
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB])]
      linear_combination hxF
    · rw [div_eq_div_iff jwr (by simp [jw0, jw1, jdB]), neg_one_mul]
      linear_combination hyF
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassSeriesLimit

section Series

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

def T (v : PowerSeries R) : PowerSeries R :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
      + C W.a₆ * v ^ 3

def E (a b : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (a + b) + C W.a₄ * X * (a + b)
    + C W.a₆ * (a ^ 2 + a * b + b ^ 2)

theorem T_sub (a b : PowerSeries R) : T W a - T W b = (a - b) * E W a b := by
  simp only [T, E]
  ring

theorem X_dvd_E {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) : X ∣ E W a b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  refine ⟨C W.a₁ + C W.a₂ * X + C W.a₃ * (a' + b') + C W.a₄ * X * (a' + b')
    + C W.a₆ * X * (a' ^ 2 + a' * b' + b' ^ 2), ?_⟩
  simp only [E]
  ring

theorem X_dvd_wMap {a : PowerSeries R} (ha : X ∣ a) : X ∣ T W a := by
  obtain ⟨a', rfl⟩ := ha
  refine ⟨X ^ 2 + C W.a₁ * X * a' + C W.a₂ * X ^ 2 * a' + C W.a₃ * X * a' ^ 2
    + C W.a₄ * X ^ 2 * a' ^ 2 + C W.a₆ * X ^ 2 * a' ^ 3, ?_⟩
  simp only [T]
  ring

theorem contract {k : ℕ} {a b : PowerSeries R} (ha : X ∣ a) (hb : X ∣ b) (h : X ^ k ∣ a - b) :
    X ^ (k + 1) ∣ T W a - T W b := by
  rw [T_sub, pow_succ]
  exact mul_dvd_mul h (X_dvd_E W ha hb)

omit W in
theorem eq_zero_of_forall_X_pow_dvd {d : PowerSeries R} (h : ∀ k, X ^ k ∣ d) : d = 0 := by
  ext n
  simpa using (X_pow_dvd_iff.mp (h (n + 1))) n (Nat.lt_succ_self n)

def seq : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => T W (seq k)

theorem X_dvd_seq (k : ℕ) : X ∣ seq W k := by
  induction k with
  | zero => show X ∣ (0 : PowerSeries R); exact dvd_zero _
  | succ k ih => show X ∣ T W (seq W k); exact X_dvd_wMap W ih

theorem seq_step (k : ℕ) : X ^ k ∣ seq W (k + 1) - seq W k := by
  induction k with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    show X ^ (k + 1) ∣ T W (seq W (k + 1)) - T W (seq W k)
    exact contract W (X_dvd_seq W _) (X_dvd_seq W _) ih

theorem seq_far (j i : ℕ) : X ^ j ∣ seq W (j + i) - seq W j := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := seq_step W (j + i)
    have h2 : (X : PowerSeries R) ^ j ∣ X ^ (j + i) := pow_dvd_pow X (Nat.le_add_right j i)
    have e : j + (i + 1) = j + i + 1 := by omega
    rw [e, show seq W (j + i + 1) - seq W j
      = (seq W (j + i + 1) - seq W (j + i)) + (seq W (j + i) - seq W j) by ring]
    exact dvd_add (h2.trans h1) ih

def lim : PowerSeries R := PowerSeries.mk fun n => coeff n (seq W (n + 1))

theorem lim_approx (k : ℕ) : X ^ k ∣ lim W - seq W k := by
  rw [X_pow_dvd_iff]
  intro m hm
  obtain ⟨i, rfl⟩ : ∃ i, k = m + 1 + i := ⟨k - (m + 1), by omega⟩
  have h := X_pow_dvd_iff.mp (seq_far W (m + 1) i) m (Nat.lt_succ_self m)
  simp only [map_sub, lim, coeff_mk] at h ⊢
  linear_combination -h

theorem lim_fixed : WFixed W (lim W) := by
  have h1 := lim_approx W 1
  rw [pow_one] at h1
  have hX : X ∣ lim W := by
    have := dvd_add h1 (X_dvd_seq W 1)
    rwa [sub_add_cancel] at this
  refine ⟨X_dvd_iff.mp hX, ?_⟩
  show lim W = T W (lim W)
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_X_pow_dvd
  intro k
  have h2 := lim_approx W (k + 1)
  have h3 : X ^ (k + 1) ∣ T W (seq W k) - T W (lim W) :=
    contract W (X_dvd_seq W k) hX
      (by rw [← neg_sub]; exact dvd_neg.mpr (lim_approx W k))
  have e : lim W - T W (lim W)
      = (lim W - seq W (k + 1)) + (T W (seq W k) - T W (lim W)) := by
    rw [show seq W (k + 1) = T W (seq W k) from rfl]
    ring
  rw [e]
  exact (pow_dvd_pow X (Nat.le_succ k)).trans (dvd_add h2 h3)

theorem fixed_unique {w w' : PowerSeries R} (hw : WFixed W w) (hw' : WFixed W w') : w = w' := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have hX' : X ∣ w' := X_dvd_iff.mpr hw'.1
  have key : ∀ k, X ^ k ∣ w - w' := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      have h := contract W hX hX' ih
      rwa [show T W w = w from hw.2.symm, show T W w' = w' from hw'.2.symm] at h
  exact sub_eq_zero.mp (eq_zero_of_forall_X_pow_dvd key)

theorem lead {w : PowerSeries R} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hX : X ∣ w := X_dvd_iff.mpr hw.1
  have e0 : T W 0 = X ^ 3 := by simp only [T]; ring
  have hw2 : T W w = w := hw.2.symm
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := by
    intro n h
    have e : w - X ^ 3 = (w - 0) * E W w 0 := by
      rw [← T_sub, e0, hw2]
    rw [e, sub_zero, pow_succ]
    exact mul_dvd_mul h (X_dvd_E W hX (dvd_zero X))
  have hadd : ∀ n, n ≤ 3 → X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := by
    intro n hn h
    have := dvd_add h (pow_dvd_pow (X : PowerSeries R) hn)
    rwa [sub_add_cancel] at this
  have h1 : X ^ 1 ∣ w := by rw [pow_one]; exact hX
  have h2 : X ^ 2 ∣ w := hadd 2 (by norm_num) (step 1 h1)
  have h3 : X ^ 3 ∣ w := hadd 3 le_rfl (step 2 h2)
  have h4 : X ^ 4 ∣ w - X ^ 3 := step 3 h3
  have c := X_pow_dvd_iff.mp h3
  have c4 := X_pow_dvd_iff.mp h4 3 (by norm_num)
  rw [map_sub, coeff_X_pow_self] at c4
  exact ⟨c 0 (by norm_num), c 1 (by norm_num), c 2 (by norm_num), sub_eq_zero.mp c4⟩

end Series

section Subst

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem mv_eq_zero {σ : Type*} {d e : MvPowerSeries σ R}
    (he : MvPowerSeries.constantCoeff e = 0) (h : d = d * e) : d = 0 := by
  have hc : IsUnit (MvPowerSeries.constantCoeff (1 - e)) := by
    rw [map_sub, map_one, he, sub_zero]
    exact isUnit_one
  have hu : IsUnit (1 - e) := MvPowerSeries.isUnit_iff_constantCoeff.mpr hc
  have h0 : d * (1 - e) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  exact hu.mul_left_eq_zero.mp h0

private theorem hasSubst_of_constantCoeff_eq_zero_elliptic_torsion {σ : Type} {s : MvPowerSeries σ R}
    (hs : MvPowerSeries.constantCoeff s = 0) : PowerSeries.HasSubst s :=
  PowerSeries.HasSubst.of_constantCoeff_zero hs

private theorem substAlgHom_apply' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (f : PowerSeries R) : PowerSeries.substAlgHom ha f = f.subst s :=
  congrFun (PowerSeries.coe_substAlgHom ha) f

private theorem substAlgHom_X' {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s) :
    PowerSeries.substAlgHom ha (X : PowerSeries R) = s := by
  rw [substAlgHom_apply']
  exact PowerSeries.subst_X ha

private theorem powerSeries_smul_eq_C_mul (r : R) (f : PowerSeries R) : r • f = C r * f :=
  PowerSeries.smul_eq_C_mul f r

private theorem substAlgHom_C {σ : Type} {s : MvPowerSeries σ R} (ha : PowerSeries.HasSubst s)
    (r : R) : PowerSeries.substAlgHom ha (C r) = algebraMap R (MvPowerSeries σ R) r := by
  rw [show (C r : PowerSeries R) = r • (1 : PowerSeries R) by rw [powerSeries_smul_eq_C_mul, mul_one],
    map_smul, map_one, Algebra.smul_def, mul_one]

private theorem constantCoeff_subst_eq_zero_elliptic_torsion {w : PowerSeries R} (hw0 : constantCoeff w = 0)
    {σ : Type} (s : MvPowerSeries σ R) (hs : MvPowerSeries.constantCoeff s = 0) :
    MvPowerSeries.constantCoeff (w.subst s) = 0 := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  obtain ⟨w₁, hw₁⟩ := X_dvd_iff.mpr hw0
  rw [← substAlgHom_apply' ha, hw₁, map_mul, substAlgHom_X' ha, map_mul, hs, zero_mul]

theorem subst_eq {w : PowerSeries R} (hw : WFixed W w) {σ : Type} (s : MvPowerSeries σ R)
    (hs : MvPowerSeries.constantCoeff s = 0) : WEqAt W s (w.subst s) := by
  have ha := hasSubst_of_constantCoeff_eq_zero_elliptic_torsion hs
  have e := congrArg (PowerSeries.substAlgHom ha) hw.2
  simp only [map_add (f := _), map_mul, map_pow, substAlgHom_C ha, substAlgHom_X' ha] at e
  rw [substAlgHom_apply' ha] at e
  unfold Formalism.ELL.WEqAt
  simp only [Algebra.smul_def]
  linear_combination e

end Subst

end WeierstrassSeriesLimit

open WeierstrassSeriesLimit in
theorem wSeriesExistsUnique_holds : WSeriesUnique.{u} := by
  intro R _ W
  exact ⟨Formalism.ELL.WeierstrassSeriesLimit.lim W, Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W,
    fun w hw => Formalism.ELL.WeierstrassSeriesLimit.fixed_unique W hw (Formalism.ELL.WeierstrassSeriesLimit.lim_fixed W)⟩

open WeierstrassSeriesLimit in
theorem wSeriesLeadingTerm_holds : WSeriesLead.{u} := by
  intro R _ W w hw
  exact Formalism.ELL.WeierstrassSeriesLimit.lead W hw

open WeierstrassSeriesLimit in
theorem wSeriesSubstUnique_holds : WSubstUnique.{u} := by
  intro R _ W w hw σ _ s hs
  refine ⟨Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs, fun v hv hvE => ?_⟩
  have hu := Formalism.ELL.WeierstrassSeriesLimit.subst_eq W hw s hs
  have hu0 : MvPowerSeries.constantCoeff (w.subst s) = 0 := _root_.Formalism.ELL.WeierstrassSeriesLimit.constantCoeff_subst_eq_zero_elliptic_torsion hw.1 s hs
  unfold WEqAt at hu hvE
  simp only [Algebra.smul_def] at hu hvE
  have key : v - w.subst s = (v - w.subst s) *
      (algebraMap R (MvPowerSeries σ R) W.a₁ * s + algebraMap R (MvPowerSeries σ R) W.a₂ * s ^ 2
        + algebraMap R (MvPowerSeries σ R) W.a₃ * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₄ * s * (v + w.subst s)
        + algebraMap R (MvPowerSeries σ R) W.a₆ * (v ^ 2 + v * w.subst s + w.subst s ^ 2)) := by
    linear_combination hvE - hu
  refine sub_eq_zero.mp (Formalism.ELL.WeierstrassSeriesLimit.mv_eq_zero ?_ key)
  simp [hs, hv, hu0]

end Formalism.ELL
end
end
