module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFramesLastStepEigenmodules

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem loc_one_add (P : Pair p) (a b a' b' : ℤ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') 1 i j = P.loc a b 1 i j * P.loc a' b' 1 i j := by
  have h₁ : ((P.r i : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h₂ : ((P.r' j : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [loc, one_mul, zpow_add₀ h₁, zpow_add₀ h₂]
  ring

theorem rep_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' →
      P.Rep (a + a') (b + b') (M.tens M') := by
  intro k _ X _ p P a b a' b' M M' ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  have e (c : (M.tens M').B.ι) (i : P.L.B.ι) (j : P.A.B.ι) :
      (((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField) / P.loc (a + a') (b + b') 1 i j) =
        ((ρ c.1 : X.functionField) / P.loc a b 1 i j) * ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) := by
    rw [loc_one_add, Units.val_mul]
    ring
  refine ⟨fun c => ρ c.1 * ρ' c.2, GlobalTheory.PtHtComb.isRatSec_tens hρ hρ', ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [e]
    exact (hu x c.1 i j hc.1 hi hj).mul (hu' x c.2 i j hc.2 hi hj)
  · intro σ y c i j hc hi hj
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have u₁ := hu _ c.1 i j (mem_ptsIn.1 hc₁) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have u₂ := hu' _ c.2 i j (mem_ptsIn.1 hc₂) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have n₁ := hn σ y c.1 i j hc₁ hi hj
    have n₂ := hn' σ y c.2 i j hc₂ hi hj
    have z₁ : ‖ratVal ((ρ c.1 : X.functionField) / P.loc a b 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₁)
    have z₂ : ‖ratVal ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₂)
    change Real.log ‖ratVal ((((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField)) /
        P.loc (a + a') (b + b') 1 i j) y‖ - ((M.φ σ).φ c.1 y + (M'.φ σ).φ c.2 y) / 2 = _
    rw [e, ratVal_mul u₁.regAt u₂.regAt, norm_mul, Real.log_mul z₁ z₂]
    push_cast
    linear_combination n₁ + n₂

end GlobalTheory.VolBr.Pair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermPairWithSections_represents_tensor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' → P.Rep (a + a') (b + b') (M.tens M') := by
  first | exact @GlobalTheory.VolBr.Pair.rep_tens | exact GlobalTheory.VolBr.Pair.rep_tens | (intros; apply GlobalTheory.VolBr.Pair.rep_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.QuoShape

theorem antitone_of_adj {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a ≤ b := hab
  clear hab
  induction b, hab' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega))

theorem shape {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (n : ℕ)
    (hn : 4 * (W.T : ℤ) * n ≤ W.h0) :
    (∀ τ, Antitone (W.u1 τ)) ∧
    (∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b) ∧
    ∀ τ a, |(W.u1 τ a : ℝ)| ≤ W.b / 2 := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  have bar : ∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b := by
    intro τ a b ha hb
    have h := ((GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b (by omega)).2.1 hb).2
    have h2 : (n : ℤ) ≤ W.u1 τ a - W.u1 τ b - 3 * N := le_of_mul_le_mul_left (hn.trans h) (by omega)
    have h3 := b.isLt
    omega
  refine ⟨fun τ => antitone_of_adj _ fun a b hab => ?_, bar, fun τ a => ?_⟩
  · by_cases hb : (b : ℕ) = W.p
    · have := bar τ a b (by omega) hb
      omega
    · have := (GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b hab).1 hb
      omega
  · have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hH hD τ a).1
    have h2 : 4 * |W.u1 τ a| ≤ |W.u τ a| + W.c0 + 4 * N :=
      (mul_le_mul_of_nonneg_right (by omega) (abs_nonneg _)).trans h1
    have h3 : 4 * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h2
    have h4 := hH.h5 τ a
    linarith

theorem ranks_le (D : D7) : 80 * D.R.f * D.R.r ^ 2 ≤ D.R.r * D.R.f ^ 2 * D.R.m ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2) := by
  have hf := SizeTZ.two_le_f D
  have hr := SizeTZ.six_le_r D
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  generalize D.R.f = f at *
  generalize D.R.r = r at *
  generalize D.R.m = m at *
  generalize D.R.k = k at *
  have hc : r ≤ r.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ (by omega)
  calc 80 * f * r ^ 2 = r * 2 ^ 2 * 2 ^ 2 * 5 * (f * r) := by ring
    _ ≤ r * f ^ 2 * m ^ 2 * k * (f * r.choose 2) := by gcongr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem shape_at {PP : ℝ} (hPP : 1 ≤ PP) (hW : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) (u1 : Psi p.T.Q.H → Fin ((dat p i).p + (dat p i).q) → ℤ)
    (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = D.R.r ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p →
      (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ ∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * L.sc.b := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hW.hyp hi
  have hH1 := hH u1
  have hcol : (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 :=
    SizeTZ.nCol_le_of_pins p.fw.laws.pins ⟨Nat.le_add_left _ _, i.2⟩
  have hr : (80 : ℝ) * D.R.f * (D.R.r : ℝ) ^ 2 ≤
      D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) := by
    rw [hW.dim]; exact_mod_cast ranks_le D
  have hn : 4 * ((lenT p i PP : ℕ) : ℤ) * (nCol (dat p i) : ℕ) ≤ h0 := by
    have hT0 : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have h1 : 4 * (lenT p i PP : ℝ) * (nCol (dat p i) : ℝ) ≤ h0 := by
      refine le_trans ?_ hh
      generalize (lenT p i PP : ℝ) = T at *
      calc 4 * T * (nCol (dat p i) : ℝ) ≤ 4 * T * (20 * D.R.f * (D.R.r : ℝ) ^ 2) := by gcongr
        _ = 1 * (T * (80 * D.R.f * (D.R.r : ℝ) ^ 2)) := by ring
        _ ≤ PP * (T * (D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ))) := by gcongr
        _ = _ := by ring
    exact_mod_cast h1
  obtain ⟨a1, a2, a3⟩ := shape (wtsAt p i PP h0 S eta u1) hH1 ((quo_iff p i PP h0 S eta u1).1 hq) (nCol (dat p i)) hn
  have b1 : D.R.k - 1 < (dat p i).p := hH1.kc_lt
  have b2 : (dat p i).p < (dat p i).p + (dat p i).q := hH1.p_lt
  refine ⟨by omega, by omega, hW.sig.2.2, a1, a2, fun τ a => (a3 τ a).trans (le_of_eq ?_)⟩
  show 4 * L.sc.b / 2 = 2 * L.sc.b
  ring

end GlobalTheory.RefSum.QuoShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelTor

theorem zeta_pow_div_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : zeta N ^ (N / n) = zeta n := by
  obtain ⟨c, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hN
  have hc : c ≠ 0 := right_ne_zero_of_mul hN
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem cycAway_le_of_dvd {n N : ℕ} (hN : N ≠ 0) (h : n ∣ N) : cycAway n ≤ cycAway N := by
  refine Subring.closure_le.2 ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow_div_of_dvd hN h]
    exact pow_mem (zetaAway N).2 _
  · obtain ⟨c, rfl⟩ := h
    have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul hN)
    have e : (n : ℂ)⁻¹ = (c : ℂ) * ((n * c : ℕ) : ℂ)⁻¹ := by
      push_cast
      field_simp
    rw [e]
    exact mul_mem (natCast_mem _ _) (Subring.subset_closure (Or.inr rfl))

theorem zetaAway_pow_self {N : ℕ} (hN : N ≠ 0) : zetaAway N ^ N = 1 :=
  Subtype.ext (Complex.isPrimitiveRoot_exp N hN).pow_eq_one

theorem formallyUnramified_cycAway {N : ℕ} (hN : N ≠ 0) (R : Type) [CommRing R] [Algebra R (cycAway N)] :
    Algebra.FormallyUnramified R (cycAway N) := by
  have hD : ∀ x : cycAway N, KaehlerDifferential.D R (cycAway N) x = 0 := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · have h := congrArg (KaehlerDifferential.D R (cycAway N)) (zetaAway_pow_self hN)
        rw [Derivation.leibniz_pow, Derivation.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul (cycAway N), smul_smul] at h
        have hu : IsUnit ((N : cycAway N) * zetaAway N ^ (N - 1)) :=
          (isUnit_natCast hN).mul ((IsUnit.of_pow_eq_one (zetaAway_pow_self hN) hN).pow _)
        exact hu.smul_eq_zero.1 h
      · let v : cycAway N := ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
        have hv : (N : cycAway N) * v = 1 :=
          Subtype.ext (by simpa [v] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN : (N : ℂ) ≠ 0))
        have h := congrArg (KaehlerDifferential.D R (cycAway N)) hv
        rw [Derivation.leibniz, Derivation.map_one_eq_zero, Derivation.map_natCast, smul_zero, add_zero] at h
        exact (isUnit_natCast hN).smul_eq_zero.1 h
    | zero => exact map_zero _
    | one => exact Derivation.map_one_eq_zero _
    | add x y hx' hy' hx hy =>
      have := map_add (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, add_zero] at this
      exact this
    | neg x hx' hx =>
      have := map_neg (KaehlerDifferential.D R (cycAway N)) ⟨x, hx'⟩
      rw [hx, neg_zero] at this
      exact this
    | mul x y hx' hy' hx hy =>
      have := (KaehlerDifferential.D R (cycAway N)).leibniz ⟨x, hx'⟩ ⟨y, hy'⟩
      rw [hx, hy, smul_zero, smul_zero, add_zero] at this
      exact this
  refine ⟨subsingleton_of_forall_eq 0 fun ω => ?_⟩
  have hω : ω ∈ Submodule.span (cycAway N) (Set.range (KaehlerDifferential.D R (cycAway N))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  refine (Submodule.mem_bot (cycAway N)).1 (Submodule.span_le.2 ?_ hω)
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot (cycAway N)).2 (hD x)

theorem isIntegral_inclusion_cycAway {n N a : ℕ} (hN : N ≠ 0) (h : n ∣ N) (ha : N ∣ n ^ a) :
    (Subring.inclusion (cycAway_le_of_dvd hN h)).IsIntegral := by
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Polynomial.X ^ N - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hN, by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
        exact sub_eq_zero.2 (zetaAway_pow_self hN)⟩
    · obtain ⟨c, hc⟩ := ha
      let v : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
      have hc' : (n : ℂ) ^ a = N * c := by exact_mod_cast hc
      convert RingHom.isIntegralElem_map (Subring.inclusion (cycAway_le_of_dvd hN h)) (x := (c : cycAway n) * v ^ a)
      refine Subtype.ext ?_
      change (N : ℂ)⁻¹ = (c : ℂ) * ((n : ℂ)⁻¹) ^ a
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← _root_.mul_assoc, ← hc', ← mul_pow, mul_inv_cancel₀ hn', one_pow]
  | zero => exact RingHom.isIntegralElem_zero _
  | one => exact RingHom.isIntegralElem_one _
  | add x y _ _ hx hy => exact hx.add _ hy
  | neg x _ hx => exact hx.neg _
  | mul x y _ _ hx hy => exact hx.mul _ hy

theorem exists_inclusion_cycAway : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧
    j (zetaAway n) = zetaAway N ^ (N / n) ∧
    ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  intro n N hN h
  have hn : n ≠ 0 := fun h0 => hN (by simpa [h0] using h)
  let j := Subring.inclusion (cycAway_le_of_dvd hN h)
  have hj : Function.Injective j := Subring.inclusion_injective _
  refine ⟨j, hj, Subtype.ext (zeta_pow_div_of_dvd hN h).symm, fun ⟨a, ha⟩ => ?_⟩
  have hint : j.IsIntegral := isIntegral_inclusion_cycAway hN h ha
  letI := j.toAlgebra
  have : IsDedekindDomain (cycAway n) := (arBase_cycAway n hn).1
  have : Algebra.IsIntegral (cycAway n) (cycAway N) := ⟨hint⟩
  have := finiteType_cycAway N
  have : Algebra.FiniteType (cycAway n) (cycAway N) := .of_restrictScalars_finiteType ℤ _ _
  have hfin : Module.Finite (cycAway n) (cycAway N) := Algebra.IsIntegral.finite
  have : FaithfulSMul (cycAway n) (cycAway N) := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  have : Module.Flat (cycAway n) (cycAway N) := inferInstance
  have : Algebra.FinitePresentation (cycAway n) (cycAway N) := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have := formallyUnramified_cycAway hN (cycAway n)
  have het : Algebra.Etale (cycAway n) (cycAway N) := Algebra.Etale.of_formallyUnramified_of_flat
  refine ⟨(IsFinite.SpecMap_iff _).2 hfin, HasRingHomProperty.Spec_iff.2 het, ⟨?_⟩⟩
  exact hint.comap_surjective hj

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inclusion_cyclotomicAwayRing_finite_etale : ∀ n N : ℕ, N ≠ 0 → n ∣ N → ∃ j : cycAway n →+* cycAway N, Function.Injective j ∧ j (zetaAway n) = zetaAway N ^ (N / n) ∧ ((∃ a, N ∣ n ^ a) → IsFinite (spMap j) ∧ Etale (spMap j) ∧ Surjective (spMap j)) := by
  first | exact @GlobalTheory.SiegelTor.exists_inclusion_cycAway | exact GlobalTheory.SiegelTor.exists_inclusion_cycAway | (intros; apply GlobalTheory.SiegelTor.exists_inclusion_cycAway <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidOfFreeOfCrystallineDeRham
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Published.AbelianDeRham

theorem rigid_of_free_of_crystallineDeRham : GlobalTheory.Published.AbelianDeRham.Free →
    GlobalTheory.Published.CrystallineDeRham → GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro H H' R _ A _ g hA hg I κ hκ R₀ _ π hπ hI A₀ _ i h
  have := hA.smooth
  have := hA.proper
  obtain ⟨h₁, -⟩ := H' R I κ hκ R₀ π hπ hI _ _ (A.hom ≫ 𝟙 _) A₀.hom i inferInstance inferInstance
    inferInstance (by rw [Category.comp_id]; exact h.1) (liftMor κ h).isMor
  have hP := (H R A g hA hg).1
  refine ⟨fun c d e ↦ Subtype.ext (h₁.1 ?_), fun c ↦ ?_⟩
  · have := congrArg Subtype.val e
    simpa only [GrpMor.coe_pull] using this
  · obtain ⟨c', hc'⟩ := h₁.2 c.1
    have hm : c' ∈ prim (dp0 R) (𝟙 _) A := by
      rw [show prim (dp0 R) (𝟙 _) A = ⊤ from hP]; trivial
    exact ⟨⟨c', hm⟩, Subtype.ext (by rw [GrpMor.coe_pull]; exact hc')⟩

end GlobalTheory.Published.AbelianDeRham
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameStalkCompatibility
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp

theorem top_le_fromSpecStalk {Y : Scheme.{0}} (y : Y) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (U : Y.Opens) (hy : y ∈ U) : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ U := by
  intro s _
  show (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ U
  have h : (Y.fromSpecStalk y) ((Spec.map (CommRingCat.ofHom ψ)) s) ∈ Set.range (Y.fromSpecStalk y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.mem_open U.isOpen hy

theorem val_fromSpecStalk {Y : Scheme.{0}} {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) {R : Type} [CommRing R] (ψ : Y.presheaf.stalk y →+* R) (f : H0 p B ⊤)
    (hO : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ ⊤)
    (hj : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) ⁻¹ᵁ B.U i) :
    H0.val (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y) i hO hj f = ψ (H0.germ i y (memTop y) hi f) := by
  rw [H0.val_apply, H0.germ_apply]
  have hV : y ∈ (⊤ : Y.Opens) ⊓ B.U i := memInf (memTop y) hi
  have h1 : ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ ((⊤ : Y.Opens) ⊓ B.U i) := by
    intro s _
    have : Y.fromSpecStalk y s ∈ Set.range (Y.fromSpecStalk y) := ⟨s, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open (IsOpen.inter isOpen_univ (B.U i).isOpen) hV
  rw [GlobalTheory.TangentOrigin.evalPt_spMap_comp ψ (Y.fromSpecStalk y) _ h1]
  congr 1
  have : (Y.fromSpecStalk y).appLE _ ⊤ h1 ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom =
      Y.presheaf.germ _ y hV := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hV]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk y)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk y)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q _) this

theorem val_congr' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O : T'.Opens} {R : Type}
    [CommRing R] {x x' : Sp R ⟶ T'} (e : x = x') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x' ⁻¹ᵁ O)
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hi' : ⊤ ≤ x' ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO hi f = H0.val x' i hO' hi' f := by
  subst e; rfl

theorem val_restr'' {k : Type} [CommRing k] {T' : Scheme.{0}} {p : T' ⟶ Sp k} {B : LB T'} {O O' : T'.Opens}
    (h : O' ≤ O) {R : Type} [CommRing R] (x : Sp R ⟶ T') (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O')
    (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) : H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi)
    (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _


set_option maxHeartbeats 1000000 in
theorem evI_ofSpace_eq_prod_mul_val : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (x₀ : Sp T.Fr ⟶ Y₀ X Z), (X.ptY y'.1 = x₀ ≫ inc₀ X Z) → ∀ (j' : (L₀ X Z la).ι) (hO : ⊤ ≤ x₀ ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens)) (hj : ⊤ ≤ x₀ ⁻¹ᵁ (L₀ X Z la).U j') (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit)) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr (j' PUnit.unit) (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) = (∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix).val * H0.val x₀ j' hO hj w.1 := by
  intro E _ _ _ H Dw l Xo c Y X Z r U la w T io y' x₀ hx j' hO hj hz Q t hQ ht
  letI := io.toAlgebra
  let fS : GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0) := ⟨_, cusp_le_secZ Z U la (ofSpace X Z U la w).2⟩
  have hOf : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ flagOpen X :=
    GlobalTheory.FlagMod.le_preimage_map (z := X.pt y'.1) X.inc (top_le_inc X) le_top
  have a := evR_eq_val_secOf fS hOf hQ ht
  show evR Xo c fS.1 y'.1 = _
  rw [a]
  congr 1
  have hx' : X.pt y'.1 ≫ X.inc = x₀ ≫ inc₀ X Z := (X.pt_inc _).trans hx
  have hU₀ : ⊤ ≤ x₀ ⁻¹ᵁ U₀ X Z := by
    have h1 := hOf
    rw [hx', Scheme.Hom.comp_preimage] at h1
    exact h1
  have hk' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (j' PUnit.unit) := hx' ▸ hz
  have hO' : ⊤ ≤ (x₀ ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hx' ▸ hOf
  rw [val_congr' hx' _ hOf hO' hz hk']
  have b1 := H0.val_pull (inc₀ X Z) (le_refl (U₀ X Z)) x₀ j' hU₀ hj hO' hk' (secOf X _ fS)
  rw [← b1]
  have hs : H0.pull (inc₀ X Z) (le_refl (U₀ X Z)) (secOf X _ fS) = H0.restr le_top w.1 := cuspSec_ofSpace X Z U la w
  rw [hs, val_restr'' le_top x₀ j' hO hU₀ hj]


set_option maxHeartbeats 1000000 in
theorem germ_eq_unit_mul_evI_core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw) (w : space X Z U la) (y : Y₀ X Z) (T : CDVR)
    (io : c.F →+* T.Fr) (y' : IntFr Xo c T io) (g : (Y₀ X Z).presheaf.stalk y →+* T.V)
    (hpt : letI := io.toAlgebra; X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z)
    (j' : (L₀ X Z la).ι) (hj' : y ∈ (L₀ X Z la).U j') :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (g (H0.germ j' y (memTop y) hj' w.1)) =
      algebraMap T.V T.Fr (u : T.V) * evI y' ((ofSpace X Z U la w : Cusp Z U la) : Rul Xo c) := by
  letI := io.toAlgebra
  have hk : inc₀ X Z y ∈ X.F.U (j' PUnit.unit) := mem_pull.1 hj'
  have he : Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) =
      Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hx₀ : X.ptY y'.1 = (Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫
      (Y₀ X Z).fromSpecStalk y) ≫ inc₀ X Z := by rw [Category.assoc]; exact hpt
  have hpt' : X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
      (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) := by
    rw [hpt, he, Category.assoc]
  have hO := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ⊤ (memTop y)
  have hj := top_le_fromSpecStalk y ((algebraMap T.V T.Fr).comp g) ((L₀ X Z la).U j') hj'
  have hzV : ⊤ ≤ (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ X Z).fromSpecStalk y ≫ inc₀ X Z) ⁻¹ᵁ
      X.F.U (j' PUnit.unit) := by
    have := top_le_fromSpecStalk y g (inc₀ X Z ⁻¹ᵁ X.F.U (j' PUnit.unit)) hk
    rw [← Category.assoc, Scheme.Hom.comp_preimage]
    exact this
  have hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U (j' PUnit.unit) := by
    rw [X.pt_inc, hpt']
    exact FlagMod.le_preimage_comp _ hzV
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor y'.1 (j' PUnit.unit) hz
  have e2 := evI_ofSpace_eq_prod_mul_val X Z U la w T io y' _ hx₀ j' hO hj hz Q t hQ ht
  have e1 := val_fromSpecStalk y j' hj' ((algebraMap T.V T.Fr).comp g) w.1 hO hj
  have hu := GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame X T io y' _ hpt' (j' PUnit.unit) hzV hz Q t hQ ht
  have ex : ∀ ix, ∃ u : T.Vˣ, Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) u = t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    intro ix
    rcases ix with _ | ⟨σ, i⟩
    · exact ⟨1, by rw [FlagMod.exOf_none, zpow_zero, map_one]⟩
    · obtain ⟨u, hu⟩ := hu σ i
      exact ⟨u ^ GlobalTheory.AllWt.exOf Dw la 0 (some ⟨σ, i⟩), by rw [map_zpow]; congr 1; exact Units.ext hu⟩
  choose uf huf using ex
  have hP : Units.map (algebraMap T.V T.Fr : T.V →* T.Fr) (∏ ix, uf ix) = ∏ ix, t ix ^ GlobalTheory.AllWt.exOf Dw la 0 ix := by
    rw [map_prod]; exact Finset.prod_congr rfl fun ix _ => huf ix
  refine ⟨(∏ ix, uf ix)⁻¹, ?_⟩
  rw [e2, ← hP, e1, Units.coe_map, RingHom.comp_apply, ← mul_assoc, MonoidHom.coe_coe, ← map_mul, Units.inv_mul, map_one,
    one_mul]

end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem flat_and_lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    Flat (M.s ≫ spMap (algebraMap ℤ o)) ∧ LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have := h.ded
  have hΩ := h.char
  have : CharZero o := ⟨fun a b hab => by
    have := congrArg (algebraMap o Ω) hab
    simpa using this⟩
  have hft := h.ft
  have := M.lft
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (spMap (algebraMap ℤ o)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  exact ⟨inferInstance, inferInstance⟩

theorem exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z)
    (hx : IsClosed ({x} : Set M.Z)) (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  exact GlobalTheory.padicAlgCl_integral_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o)) x hx U hU

theorem exists_cen_main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z),
    IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty →
      ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y :=
  fun o Ω _ _ _ _ M x hx U hU => exists_cen o Ω M x hx U hU

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmeticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  first | exact @GlobalTheory.Poinc.exists_cen_main | exact GlobalTheory.Poinc.exists_cen_main | (intros; apply GlobalTheory.Poinc.exists_cen_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.DomPull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem unitAt_map {x : X'} {f : X.functionField} (h : UnitAt (φ x) f) :
    UnitAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, ha.map _, (functionFieldMap_algebraMap φ x a).symm⟩

abbrev unitsMap : X.functionFieldˣ →* X'.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom

theorem germOf_map_eq (D : CartierDiv X) {x : X'} {g g' : X.functionFieldˣ} (hg : D.IsEqn (φ x) g)
    (hg' : D.IsEqn (φ x) g') : germOf x (unitsMap φ g) = germOf x (unitsMap φ g') := by
  rw [germOf_eq_iff]
  have := unitAt_map φ (hg.iff_unitAt.1 hg')
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

def pullback (D : CartierDiv X) : CartierDiv X' :=
  show cartierGroup X' from ⟨fun x => germOf x (unitsMap φ (D.exists_isEqn (φ x)).choose), fun x => by
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ x)
    exact ⟨φ ⁻¹ᵁ U, hU, unitsMap φ g, fun y hy =>
      germOf_map_eq φ D (D.exists_isEqn (φ y)).choose_spec (hg _ hy)⟩⟩

theorem isEqn_pullback (D : CartierDiv X) {x : X'} {g : X.functionFieldˣ} (h : D.IsEqn (φ x) g) :
    (pullback φ D).IsEqn x (unitsMap φ g) :=
  germOf_map_eq φ D (D.exists_isEqn (φ x)).choose_spec h

theorem fnOf_app {U : X.Opens} (hU : genericPoint X' ∈ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    fnOf (φ ⁻¹ᵁ U) hU (φ.app U a) = GlobalTheory.functionFieldMap φ (fnOf U (gen_mem (x := φ (genericPoint X')) hU) a) := by
  rw [← algebraMap_germ (x := φ (genericPoint X')) hU a, functionFieldMap_algebraMap]
  erw [Scheme.Hom.germ_stalkMap_apply]
  exact (algebraMap_germ (X := X') hU _).symm

def pullEqns (D : CartierDiv X) (J : ((toLB D).pull φ).ι) : X'.functionFieldˣ :=
  unitsMap φ (J PUnit.unit).1.2

theorem fnOf_pull_g (D : CartierDiv X) (J J' : ((toLB D).pull φ).ι)
    (hg : genericPoint X' ∈ ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J') :
    fnOf _ hg (((toLB D).pull φ).g J J' : Γ(X', ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (((J PUnit.unit).1.2 : X.functionField) / ((J' PUnit.unit).1.2 : X.functionField)) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ ((toLB D).U (J PUnit.unit) ⊓ (toLB D).U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact (fnOf_app φ h₀ _).trans (congrArg _ (fnOf_toLB_g _ _ _))

theorem presents_pullback (D : CartierDiv X) :
    Presents (pullback φ D) ((toLB D).pull φ) (pullEqns φ D) := by
  refine ⟨LB.isLB_pull (isLB_toLB D) φ, fun J J' hg => ?_, fun J x hx => ?_⟩
  · rw [fnOf_pull_g φ D J J' hg]
    show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  · exact isEqn_pullback φ D ((J PUnit.unit).2.2 _ (mem_pull.1 hx))

end GlobalTheory.Cartier.DomPull

namespace GlobalTheory.Cartier


open DomPull in
theorem exists_pullback_cartierDiv : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]
    (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') =
      cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧
      ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g →
        D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  intro X X' _ _ φ _ D
  refine ⟨pullback φ D, ?_, fun x g h => isEqn_pullback φ D h⟩
  rw [← toPic_apply]
  exact (presents_pullback φ D).toPic_eq

end GlobalTheory.Cartier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClassStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDivisor_dominant_pullback_with_class : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ] (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') = cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧ ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g → D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  first | exact @GlobalTheory.Cartier.exists_pullback_cartierDiv | exact GlobalTheory.Cartier.exists_pullback_cartierDiv | (intros; apply GlobalTheory.Cartier.exists_pullback_cartierDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc


set_option maxHeartbeats 1000000 in
theorem exists_ratModel_normalization : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z →
    QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) →
    (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z ∧
    IsFinite π ∧ M.pt ≫ π = p := by
  intro A o Ω _ _ _ _ _ _ κ hκ Z z _ _ _ p hp hfin
  haveI : CharZero Ω := ArithBase.char (o := o)
  haveI : CharZero (Sp Ω).functionField :=
    charZero_of_injective_ringHom (((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫
      (Sp Ω).germToFunctionField ⊤).hom).injective
  haveI : IsFinite p.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_genericallyFinite (o := CommRingCat.of A) p z hfin
  haveI : GlobalTheory.IsNormalScheme p.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral p
  haveI : IsFinite (spMap κ) := by rw [IsFinite.SpecMap_iff]; exact hκ
  have hl : p ≫ z = spMap (algebraMap o Ω) ≫ spMap κ := by
    rw [hp, ← Spec.map_comp]; rfl
  let l : Sp Ω ⟶ pullback z (spMap κ) := pullback.lift p (spMap (algebraMap o Ω)) hl
  have hl1 : p = l ≫ pullback.fst z (spMap κ) := (pullback.lift_fst _ _ _).symm
  let d := p.normalizationDesc l (pullback.fst z (spMap κ)) hl1
  let s : p.normalization ⟶ Sp o := d ≫ pullback.snd z (spMap κ)
  have hs : s ≫ spMap κ = p.fromNormalization ≫ z := by
    simp only [s, d, Category.assoc, ← pullback.condition]
    rw [Scheme.Hom.normalizationDesc_comp_assoc]
  have hfz : LocallyOfFiniteType (s ≫ spMap κ) ∧ IsSeparated (s ≫ spMap κ) ∧ QuasiCompact (s ≫ spMap κ) := by
    rw [hs]; exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨h1, h2, h3⟩ := hfz
  have hpt_s : p.toNormalization ≫ s = spMap (algebraMap o Ω) := by
    simp only [s, d]
    rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_snd]
  have hgen : Set.range p.toNormalization = {genericPoint p.normalization} := by
    have hr : ∀ w : Sp Ω, w = IsLocalRing.closedPoint Ω := fun w => Subsingleton.elim _ _
    have hrng : Set.range p.toNormalization = {p.toNormalization (IsLocalRing.closedPoint Ω)} :=
      Set.ext fun y => ⟨fun ⟨w, hw⟩ => hw ▸ congrArg p.toNormalization (hr w),
        fun hy => ⟨_, hy.symm⟩⟩
    have : IsGenericPoint (p.toNormalization (IsLocalRing.closedPoint Ω)) (⊤ : Set p.normalization) := by
      rw [isGenericPoint_def, ← hrng]
      exact p.toNormalization.denseRange.closure_range
    rw [hrng, this.eq (genericPoint_spec p.normalization)]
  have honto : ∀ x : Ω, ∃ (U : p.normalization.Opens) (f : Γ(p.normalization, U)), (U : Set p.normalization).Nonempty ∧
      valF p.toNormalization U f = x := by
    intro x
    set ξ : Sp Ω := genericPoint (Sp Ω) with hξ
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := p ξ) (U := ⊤) trivial
    have hsub : ∀ w : Sp Ω, w = ξ := fun w => Subsingleton.elim _ _
    have hpV : ⊤ ≤ p ⁻¹ᵁ V := fun w _ => by rw [hsub w]; exact hxV
    have hξB : ξ ∈ p ⁻¹ᵁ V := hxV
    letI := (p.app V).hom.toAlgebra

    let gB := (Sp Ω).presheaf.germ (p ⁻¹ᵁ V) ξ hξB
    let gR := Z.presheaf.germ V (p ξ) hxV
    have hsq : gR ≫ p.stalkMap ξ = p.app V ≫ gB := p.germ_stalkMap V ξ hxV
    letI alO : Algebra Γ(Z, V) (Z.presheaf.stalk (p ξ)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨p ξ, hxV⟩
    letI alS : Algebra (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) := (p.stalkMap ξ).hom.toAlgebra
    letI alRS : Algebra Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) := (gR ≫ p.stalkMap ξ).hom.toAlgebra
    haveI : IsScalarTower Γ(Z, V) (Z.presheaf.stalk (p ξ)) ((Sp Ω).presheaf.stalk ξ) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI hloc : IsLocalization.AtPrime (Z.presheaf.stalk (p ξ)) (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal :=
      hV.isLocalization_stalk ⟨p ξ, hxV⟩

    have h1 : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (p ⁻¹ᵁ V) := hpV
    let E : Γ(Sp Ω, p ⁻¹ᵁ V) →+* Ω := (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
    have hE : ∀ b, E b = valR (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) b := fun b => (GlobalTheory.Points.valR_eq _ _ h1 b).symm
    have hEinj : Function.Injective E := by
      have e1 : GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1 =
          (Sp Ω).presheaf.map (homOfLE h1).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
        rw [GlobalTheory.Points.valMap, Scheme.Hom.appLE]
        simp
        rfl
      haveI : Nonempty (⊤ : (Sp Ω).Opens) := ⟨⟨ξ, trivial⟩⟩
      show Function.Injective (GlobalTheory.Points.valMap (𝟙 (Sp Ω)) (p ⁻¹ᵁ V) h1).hom
      rw [e1]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp
        (map_injective_of_isIntegral (Sp Ω) (homOfLE h1))
    obtain ⟨y', hy'⟩ : ∃ y' : Γ(Sp Ω, p ⁻¹ᵁ V), E y' = x := by
      refine ⟨((Sp Ω).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom x), ?_⟩
      rw [hE, GlobalTheory.Points.valR_res (𝟙 (Sp Ω)) le_top h1]
      have := GlobalTheory.Points.valR_specMap (𝟙 (CommRingCat.of Ω)) x
      rw [Spec.map_id] at this
      exact this

    let y := gB.hom y'
    have hy : IsIntegral (Z.presheaf.stalk (p ξ)) y := hfin.to_isIntegral y
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (hV.primeIdealOf ⟨p ξ, hxV⟩).asIdeal.primeCompl y hy
    have hcomm : ∀ r : Γ(Z, V), gB.hom (algebraMap Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V) r) =
        algebraMap Γ(Z, V) ((Sp Ω).presheaf.stalk ξ) r := fun r => by
      show gB.hom ((p.app V).hom r) = (gR ≫ p.stalkMap ξ).hom r
      rw [hsq]; rfl
    let gB' : Γ(Sp Ω, p ⁻¹ᵁ V) →ₐ[Γ(Z, V)] (Sp Ω).presheaf.stalk ξ := { gB.hom with commutes' := hcomm }
    have hgB : Function.Injective gB' := germ_injective_of_isIntegral (Sp Ω) ξ hξB
    let c' : Γ(Sp Ω, p ⁻¹ᵁ V) := algebraMap Γ(Z, V) _ (m : Γ(Z, V))
    let d' : Γ(Sp Ω, p ⁻¹ᵁ V) := c' * y'
    have hc : IsIntegral Γ(Z, V) c' := isIntegral_algebraMap
    have hd : IsIntegral Γ(Z, V) d' := by
      rw [← isIntegral_algHom_iff gB' hgB]
      have : gB' d' = (m : Γ(Z, V)) • y := by
        rw [Algebra.smul_def, map_mul]
        exact congrArg (· * y) (hcomm _)
      rw [this]
      exact hm
    have hc0 : c' ≠ 0 := by
      intro h0
      have h2 : IsUnit (gB.hom c') := by
        rw [hcomm]
        exact ((IsLocalization.map_units (Z.presheaf.stalk (p ξ)) m).map (p.stalkMap ξ).hom)
      rw [h0, map_zero] at h2
      exact not_isUnit_zero h2
    have hEc : E c' ≠ 0 := fun h0 => hc0 (hEinj (h0.trans (map_zero E).symm))

    let iso := p.normalizationObjIso hV
    have key := p.normalizationObjIso_hom_val hV
    let ac : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨c', hc⟩
    let ad : Γ(p.normalization, p.fromNormalization ⁻¹ᵁ V) := iso.inv.hom ⟨d', hd⟩
    have hle : p ⁻¹ᵁ V ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := by
      simp [← Scheme.Hom.comp_preimage]
    have hval : ∀ e : integralClosure Γ(Z, V) Γ(Sp Ω, p ⁻¹ᵁ V),
        valR p.toNormalization (p.fromNormalization ⁻¹ᵁ V) (iso.inv.hom e) = E e.1 := by
      intro e
      have h3 := congrArg (fun φ => φ.hom (iso.inv.hom e)) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at h3
      rw [hE, ← Category.id_comp p.toNormalization, ← GlobalTheory.Points.valR_appLE (𝟙 (Sp Ω)) p.toNormalization hle h1]
      congr 1
      exact h3.symm
    have hW : ⊤ ≤ p.toNormalization ⁻¹ᵁ (p.fromNormalization ⁻¹ᵁ V) := h1.trans hle
    have hU : ⊤ ≤ p.toNormalization ⁻¹ᵁ p.normalization.basicOpen ac := by
      rw [GlobalTheory.Points.le_preimage_basicOpen_iff _ hW ac]
      exact (show valR p.toNormalization _ ac ≠ 0 from (hval _).trans_ne hEc).isUnit
    have hu : IsUnit ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) :=
      p.normalization.toRingedSpace.isUnit_res_basicOpen ac
    refine ⟨p.normalization.basicOpen ac,
      (p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ad * ↑(hu.unit⁻¹),
      ⟨_, hU (x := ξ) trivial⟩, ?_⟩
    rw [GlobalTheory.Points.valF_eq_valR, GlobalTheory.Points.valR_mul _ _ hU, GlobalTheory.Points.valR_res _ _ hU, hval]
    have h4 : valR p.toNormalization _ ((p.normalization.presheaf.map (homOfLE (p.normalization.basicOpen_le ac)).op).hom ac) *
        valR p.toNormalization (p.normalization.basicOpen ac) ↑(hu.unit⁻¹) = 1 := by
      rw [← GlobalTheory.Points.valR_mul _ _ hU, ← GlobalTheory.Points.valR_one p.toNormalization _ hU]
      congr 1
      exact hu.mul_val_inv
    rw [GlobalTheory.Points.valR_res _ _ hU, hval] at h4
    rw [eq_inv_of_mul_eq_one_right h4]
    show E (c' * y') * (E c')⁻¹ = x
    rw [map_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hEc, one_mul, hy']
  haveI := IsSeparated.of_comp s (spMap κ)
  haveI := locallyOfFiniteType_of_comp s (spMap κ)
  haveI := QuasiCompact.of_comp s (spMap κ)
  let M : RatModel o Ω :=
    { Z := p.normalization
      s := s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := p.toNormalization
      pt_s := hpt_s
      gen := hgen
      onto := honto }
  exact ⟨M, p.fromNormalization, GlobalTheory.IsNormalScheme.pred _, inferInstance, p.toNormalization_fromNormalization⟩

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_normalisation_dedekind : ∀ (A o Ω : Type) [CommRing A] [IsDedekindDomain A] [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (κ : A →+* o), κ.Finite → ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A), LocallyOfFiniteType z → QuasiCompact z → IsSeparated z → ∀ p : Sp Ω ⟶ Z, p ≫ z = spMap ((algebraMap o Ω).comp κ) → (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ (M : RatModel o Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z ∧ IsFinite π ∧ M.pt ≫ π = p := by
  first | exact @GlobalTheory.Poinc.exists_ratModel_normalization | exact GlobalTheory.Poinc.exists_ratModel_normalization | (intros; apply GlobalTheory.Poinc.exists_ratModel_normalization <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorNontrivial
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section Factor

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_tau_four (D : DegPre R) (a b : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val t r z J = val (D.tau a b) r z J := by
  refine exists_gen D.P.isLB ?_ (D.tau a b) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  intro U _ h
  have e : toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, lamPts, negε, ← e]
  simp [eSec, Hom.one_def]

end Factor
end GlobalTheory.Mum
end
end
