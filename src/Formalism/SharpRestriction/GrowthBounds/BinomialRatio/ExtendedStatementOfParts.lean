module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds
public import Formalism.PolynomialDimension.DigitClassSize
public import Formalism.PolynomialDimension.MultinomialDepth.FockGaussComparisonHolds

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
section -- merged from Formalism.PolynomialDimension.EdgeSumGoodRank
noncomputable section

open scoped BigOperators TensorProduct
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

def ShareProd : Prop :=
  ∀ (J : ℕ) (κ : Fin J → ℝ) (n d : Fin J → ℕ), (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
    (∀ j, (1 - κ j) * (d j : ℝ) ≤ n j) →
      (1 - ∑ j, κ j) * ((∏ j, d j : ℕ) : ℝ) ≤ ((∏ j, n j : ℕ) : ℝ)

def dd {K σ : Type} [Field K] (x : σ) (m : ℕ) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  C ((m.factorial : K)⁻¹) * (⇑(pderiv x))^[m] f

end Formalism.CountingSumsFrames
end
end

section -- merged from Formalism.PolynomialDimension.MultinomialKLog
section -- merged from Formalism.PolynomialDimension.MultinomialDepth.DvdPowOfNotPowSuccDvd
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.CountingSumsFrames

theorem one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by
  classical
  have hP : ∀ t : Finset ι, 1 - ∑ j ∈ t, κ j ≤ ∏ j ∈ t, (1 - κ j) := by
    intro t
    refine Finset.induction_on t (by simp) ?_
    intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ 1 - κ i := by linarith [(hκ i).2]
    have h2 : 0 ≤ ∑ j ∈ t, κ j := Finset.sum_nonneg fun j _ => (hκ j).1
    have h3 := mul_le_mul_of_nonneg_left ih h1
    nlinarith [mul_nonneg (hκ i).1 h2]
  have hd0 : 0 ≤ ∏ j ∈ s, d j := Finset.prod_nonneg fun j _ => hd j
  calc (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ (∏ j ∈ s, (1 - κ j)) * ∏ j ∈ s, d j :=
        mul_le_mul_of_nonneg_right (hP s) hd0
    _ = ∏ j ∈ s, ((1 - κ j) * d j) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ j ∈ s, n j := Finset.prod_le_prod₀
        (fun j _ => mul_nonneg (by linarith [(hκ j).2]) (hd j)) (fun j _ => h j)

theorem share_product_bound : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h

section Partner

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Partner

end Formalism.CountingSumsFrames
end
end

namespace Formalism.CountingSumsFrames.Top

theorem shareProd : Formalism.CountingSumsFrames.ShareProd := Formalism.CountingSumsFrames.share_product_bound

end Formalism.CountingSumsFrames.Top
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

abbrev Lj (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc)
    [NeZero X.m] (j : Fin (numSeg X.TT)) : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t) :=
  segLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm)

abbrev rkj (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc)
    [NeZero X.m] (j : Fin (numSeg X.TT)) : ℕ :=
  segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm)

def RkAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ j, Module.finrank O (Lj O C0 CE1 CE2 Cm X j) = rkj O C0 CE1 CE2 Cm X j

def BlockDiag {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {r s t : ℕ}
    (form : SegVs O r s t → SegVs O r s t → KK O) (L : Submodule O (SegVs O r s t)) (g : ℕ) (D : ℝ) : Prop :=
  ∃ (x y : Fin g → SegVs O r s t) (β : Fin g → SegBlock s r) (z : Fin g → O),
    (∀ i, x i ∈ L ∧ y i ∈ L) ∧ (∀ i b, b ≠ β i → x i b = 0 ∧ y i b = 0) ∧ (∀ i, z i ≠ 0 ∧ vLEO p (z i) D) ∧
      ∀ i l, form (x i) (y l) = if i = l then algebraMap O (KK O) (z i) else 0

def PartnersToFactorsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (Dj : ℝ) (L₁ : Submodule O (SegVs O X.m (segS X.TT j) (X.seg C0 CE1 CE2 j).t)), 0 ≤ Dj →
      GoodSub X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) L₁ Dj →
      BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (Module.finrank O L₁) Dj

def LiftAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (Dj : Fin (numSeg X.TT) → ℝ) (g : Fin (numSeg X.TT) → ℕ), (∀ j, 0 ≤ Dj j) →
    (∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (g j) (Dj j)) →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      FactorsLE X.p (beHH (m := X.m) X.p X.TT X.aT X.bT)
        (CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) (CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e)
        (∏ j, g j) ((∑ j, Dj j) + 4 * X.kap0)

def LiftVecAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (Dj : Fin (numSeg X.TT) → ℝ) (g : Fin (numSeg X.TT) → ℕ), (∀ j, 0 ≤ Dj j) →
    (∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j) (g j) (Dj j)) →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      ∃ (F : (∀ j, Fin (g j)) → VHH (m := X.m) Kf X.TT X.aT X.bT)
        (G : (∀ j, Fin (g j)) → Module.Dual Kf (VHH (m := X.m) Kf X.TT X.aT X.bT)) (δ : (∀ j, Fin (g j)) → O),
        (∀ I, F I ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        (∀ I, G I ∈ CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) ∧
        (∀ I, δ I ≠ 0 ∧ vLEO X.p (δ I) ((∑ j, Dj j) + 4 * X.kap0)) ∧
        ∀ I J, ∃ ν : O, beHH (m := X.m) X.p X.TT X.aT X.bT (F I) (G J) =
          algebraMap O Kf ((if I = J then δ I else 0) + w ^ X.c * ν)

theorem kapP_nonneg {C0 Cde CE1 CE2 Cm Ckap H : ℝ} {X : Loc} (h : Std C0 Cde CE1 CE2 H X) (hCm : 0 ≤ Cm)
    (hCk : 0 ≤ Ckap) : 0 ≤ X.kapP C0 CE1 CE2 Cm Ckap := by
  have hk : 0 ≤ X.k := by unfold Loc.k; positivity
  have hQ : 0 ≤ X.Q := by unfold Loc.Q; positivity
  have hN : 0 ≤ X.N := by unfold Loc.N; positivity
  have hY : 0 ≤ X.Y := le_trans zero_le_one h.Y1
  have hm0 : 0 ≤ X.m0 Cm := by unfold Loc.m0 m0G4 m1G4; positivity
  have hE := h.E0nn
  have hb := h.bpos.le
  unfold Loc.kapP kappaMarginBound
  positivity

theorem Ne_pos {p n' k : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n') (hk : 1 ≤ k) : 0 < gaussianNumber (p ^ n') k := by
  have h1 : (1 : ℝ) < ((p ^ n' : ℕ) : ℝ) := by
    have : 1 < p ^ n' := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  unfold gaussianNumber
  apply div_pos
  · have := one_lt_pow₀ h1 (n := k) (by omega)
    linarith
  · linarith

theorem extended_statement_of_parts {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc H : ℝ} (hCm : 0 ≤ Cm) (hCk : 0 ≤ Ckap)
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hRk : RkAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (hL1 : PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc)
    (hLift : LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc)
    (hA2 : ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc) :
    HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc Dj kT hDj hcD e he
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have hs := hstd X hD1 hH hc
  have hkap := kapP_nonneg hs hCm hCk
  have hm0 : 0 ≤ X.m0 Cm := by
    have hk : 0 ≤ X.k := by unfold Loc.k; positivity
    have hQ : 0 ≤ X.Q := by unfold Loc.Q; positivity
    unfold Loc.m0 m0G4 m1G4; positivity
  have hNe : 0 < gaussianNumber (X.p ^ X.n') (X.m + 1) :=
    Ne_pos (by have := hS.1.five_le; omega) (by have := hS.1.two_le; omega) (by omega)

  choose L₁ hL₁ using fun j => (hDj j).2.2
  have hF : ∀ j, BlockDiag X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j)) (Lj O C0 CE1 CE2 Cm X j)
      (Module.finrank O (L₁ j)) (Dj j) := fun j =>
    hL1 X W Qq O Kf ι σ jO w hS hH hc j (Dj j) (L₁ j) (hDj j).1 (hL₁ j).1
  have hT := hLift X W Qq O Kf ι σ jO w hS hH hc Dj (fun j => Module.finrank O (L₁ j)) (fun j => (hDj j).1) hF hcD e he
  refine ⟨∏ j, Module.finrank O (L₁ j), ?_, hT⟩
  have hrank := hA2 X W Qq O Kf ι σ jO w hS hH hc (X.m0 Cm) hm0
  have hg : ∀ j, (1 - kT j) * (rkj O C0 CE1 CE2 Cm X j : ℝ) ≤ (Module.finrank O (L₁ j) : ℝ) := fun j => by
    have := (hL₁ j).2
    rwa [hRk X W Qq O Kf ι σ jO w hS hH hc j] at this
  have hdim : (0 : ℝ) ≤ (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ j, kT j := Finset.sum_nonneg fun j _ => (hDj j).2.1
  rw [div_le_iff₀ hNe]
  by_cases hall : ∀ j, kT j ≤ 1
  · by_cases hs1 : ∑ j, kT j ≤ 1
    · have hsp := Formalism.CountingSumsFrames.Top.shareProd (numSeg X.TT) kT (fun j => Module.finrank O (L₁ j))
        (fun j => rkj O C0 CE1 CE2 Cm X j) (fun j => ⟨(hDj j).2.1, hall j⟩) hg
      have hrank' : (1 - X.kapP C0 CE1 CE2 Cm Ckap) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤
          gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ) := by
        push_cast
        exact hrank
      have h1 : (1 - ∑ j, kT j) * ((1 - X.kapP C0 CE1 CE2 Cm Ckap) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ)) ≤
          (1 - ∑ j, kT j) * (gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrank' (by linarith)
      have h2 : gaussianNumber (X.p ^ X.n') (X.m + 1) * ((1 - ∑ j, kT j) * ((∏ j, rkj O C0 CE1 CE2 Cm X j : ℕ) : ℝ)) ≤
          gaussianNumber (X.p ^ X.n') (X.m + 1) * ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsp hNe.le
      have h3 : 0 ≤ (∑ j, kT j) * X.kapP C0 CE1 CE2 Cm Ckap * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) := by positivity
      nlinarith [h1, h2, h3]
    · have h0 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) ≤ 0 := by linarith [not_le.mp hs1]
      have h1 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h0 hdim
      have h2 : (0 : ℝ) ≤ ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) * gaussianNumber (X.p ^ X.n') (X.m + 1) := by positivity
      linarith
  · push Not at hall
    obtain ⟨j0, hj0⟩ := hall
    have hle : kT j0 ≤ ∑ j, kT j := Finset.single_le_sum (fun j _ => (hDj j).2.1) (Finset.mem_univ j0)
    have h0 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) ≤ 0 := by linarith
    have h1 : (1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h0 hdim
    have h2 : (0 : ℝ) ≤ ((∏ j, Module.finrank O (L₁ j) : ℕ) : ℝ) * gaussianNumber (X.p ^ X.n') (X.m + 1) := by positivity
    linarith

def RestRk : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => RkAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

def PartnersToFactors : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => PartnersToFactorsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc

def RestLift : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    LiftAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

def RestLiftVec : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => ∃ Ct0 : ℝ, 0 < Ct0 ∧ ∀ Ct : ℝ, Ct0 ≤ Ct →
    LiftVecAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc

theorem thr_std : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc => 0 ≤ Cm ∧
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 h3 _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      ⟨by linarith, fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc⟩

theorem restExt_of {D : Formalism.BasicNotions.D7} (hRk : RestRk) (hL1 : PartnersToFactors) (hLift : RestLift) (hA2 : RemainderSegmentBoundSecond D) :
    RestExt D := by
  refine TransportedAlt.mono ?_ ((((thr_std.and hRk).and hL1).and hLift).and hA2)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨⟨⟨⟨hCm, hstd⟩, rk⟩, l1⟩, ⟨Ct0, hCt0, lift⟩⟩, ⟨Ck0, hCk0, a2⟩⟩
  exact ⟨Ck0, Ct0, hCk0, hCt0, fun Ckap Ct h1 h2 =>
    extended_statement_of_parts hCm (le_trans hCk0.le h1) hstd rk l1 (lift Ct h2) (a2 Ckap h1)⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {n' : ℕ}

def rot (n : ℕ) (j : Fin n) : Fin n := ⟨(j.val + 1) % n, Nat.mod_lt _ j.pos⟩

theorem rot_val (n : ℕ) (j : Fin n) :
    (j.val + 1 < n ∧ (rot n j).val = j.val + 1) ∨ (j.val + 1 = n ∧ (rot n j).val = 0) := by
  have hj := j.isLt
  by_cases h : j.val + 1 < n
  · left
    exact ⟨h, Nat.mod_eq_of_lt h⟩
  · right
    have e : j.val + 1 = n := by omega
    refine ⟨e, ?_⟩
    show (j.val + 1) % n = 0
    rw [e, Nat.mod_self]

theorem rot_inj (n : ℕ) : Function.Injective (rot n) := by
  intro j j' h
  have h' := congrArg Fin.val h
  have a := rot_val n j
  have b := rot_val n j'
  apply Fin.ext
  omega

theorem rot_bij (n : ℕ) : Function.Bijective (rot n) := Finite.injective_iff_bijective.mp (rot_inj n)

theorem next_eq (TT : Finset (Fin n')) (j : Fin (numSeg TT)) : segNext TT j = segStart TT (rot _ j) := rfl

theorem prod_next (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segNext TT j) = ∏ j, h (segStart TT j) :=
  (rot_bij (numSeg TT)).prod_comp (fun j => h (segStart TT j))

theorem other_start (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    ∃ e, e ∈ TT ∧ Even e.val ∧ e ≠ segStart TT j := by
  by_cases h0 : j.val = 0
  · refine ⟨segStart TT ⟨1, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega
  · refine ⟨segStart TT ⟨0, by omega⟩, (start_mem TT _).1, (start_mem TT _).2, fun e => ?_⟩
    have := congrArg Fin.val ((ev_mono TT).injective e)
    simp at this
    omega

theorem segG_eq (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (j : Fin (numSeg TT)) :
    segG TT j = cdist (segStart TT j) (segNext TT j) ∧ 0 < cdist (segStart TT j) (segNext TT j) := by
  obtain ⟨e, he, hev, hne⟩ := other_start TT h2 j
  obtain ⟨m1, -⟩ := next_min TT j e he hev hne
  refine ⟨?_, m1⟩
  unfold segG
  rw [if_neg (by omega)]

theorem sum_segG (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) : ∑ j, segG TT j = n' := by
  have key : ∀ j : Fin (numSeg TT), (segG TT j : ℤ) =
      ((segStart TT (rot _ j)).val : ℤ) - ((segStart TT j).val : ℤ) +
        (if j = ⟨numSeg TT - 1, by omega⟩ then (n' : ℤ) else 0) := by
    intro j
    obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g, next_eq] at *
    have c := cd_cases (segStart TT j) (segStart TT (rot _ j))
    have l1 := (segStart TT j).isLt
    have l2 := (segStart TT (rot _ j)).isLt
    rcases rot_val _ j with ⟨r1, r2⟩ | ⟨r1, r2⟩
    · have hlt : (segStart TT j).val < (segStart TT (rot _ j)).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have hne : j ≠ ⟨numSeg TT - 1, by omega⟩ := by
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [if_neg hne]
      omega
    · have hlt : (segStart TT (rot _ j)).val < (segStart TT j).val :=
        ev_mono TT (Fin.lt_def.mpr (by omega))
      have he : j = ⟨numSeg TT - 1, by omega⟩ := by
        apply Fin.ext
        show j.val = numSeg TT - 1
        omega
      rw [if_pos he]
      omega
  have hs : (∑ j, ((segStart TT (rot _ j)).val : ℤ)) = ∑ j, ((segStart TT j).val : ℤ) :=
    (rot_bij (numSeg TT)).sum_comp (fun j => ((segStart TT j).val : ℤ))
  have : ((∑ j, segG TT j : ℕ) : ℤ) = (n' : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
    simp
  exact_mod_cast this

theorem prod_starts (TT : Finset (Fin n')) (h : Fin n' → ℝ) :
    ∏ j, h (segStart TT j) = ∏ s ∈ TT.filter (fun s => Even s.val), h s := by
  refine Finset.prod_nbij (fun j => segStart TT j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    exact Finset.mem_filter.mpr (start_mem TT j)
  · intro j _ j' _ e
    exact (ev_mono TT).injective e
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp ((ev_mem TT s).mpr hs')
    exact ⟨k, Finset.mem_coe.mpr (Finset.mem_univ _), hk⟩

theorem pos_spec (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ oddSet TT j ∧ cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i := by
  obtain ⟨s, hs, h5⟩ := get_spec TT j i
  have : segPos TT j i = s := by
    unfold segPos
    rw [← h5, posAdd_cdist]
  rw [this]
  exact ⟨Finset.mem_filter.mpr hs, h5⟩

theorem prod_pos (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (h : Fin n' → ℝ) :
    ∏ i, h (segPos TT j i) = ∏ s ∈ oddSet TT j, h s := by
  refine Finset.prod_nbij (fun i => segPos TT j i) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact (pos_spec TT j i).1
  · intro i _ i' _ e
    have e' : segPos TT j i = segPos TT j i' := e
    have h1 := (pos_spec TT j i).2
    have h2 := (pos_spec TT j i').2
    rw [e'] at h1
    exact (dist_strictMono TT j).injective (h1.symm.trans h2)
  · intro s hs
    have hs' := Finset.mem_filter.mp (Finset.mem_coe.mp hs)
    have hd : cdist (segStart TT j) s ∈ segDists TT j := mem_dists.mpr ⟨s, hs', rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
    refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show segPos TT j i = s
    unfold segPos
    rw [hi, posAdd_cdist]

theorem odd_covered (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (s : Fin n') (hs : s ∈ TT) (ho : ¬ Even s.val) :
    ∃ j, s ∈ oddSet TT j := by
  have hne : (TT.filter (fun x => Even x.val)).Nonempty :=
    ⟨segStart TT ⟨0, by omega⟩, Finset.mem_filter.mpr (start_mem TT _)⟩
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image (TT.filter (fun x => Even x.val)) (fun x => cdist x s) hne
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp ((ev_mem TT x).mpr hx')
  have hj' : segStart TT j = x := hj
  refine ⟨j, Finset.mem_filter.mpr ⟨hs, ho, ?_, ?_⟩⟩
  · rw [hj']
    have c := cd_cases x s
    have l1 := x.isLt
    have l2 := s.isLt
    have hxs : x.val ≠ s.val := by
      intro e
      rw [← e] at ho
      exact ho hx'.2
    omega
  · obtain ⟨g, g0⟩ := segG_eq TT h2 j
    rw [g]
    by_contra hcon
    have hy := hmin (segNext TT j) (Finset.mem_filter.mpr (next_mem TT j))
    rw [hj'] at g0 hcon
    have c1 := cd_cases x s
    have c2 := cd_cases x (segNext TT j)
    have c3 := cd_cases (segNext TT j) s
    have l1 := x.isLt
    have l2 := s.isLt
    have l3 := (segNext TT j).isLt
    omega

theorem biUnion_odd (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) :
    Finset.univ.biUnion (oddSet TT) = TT.filter (fun s => ¬ Even s.val) := by
  ext s
  constructor
  · intro hs
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨a0, a1, -⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨a0, a1⟩
  · intro hs
    obtain ⟨a0, a1⟩ := Finset.mem_filter.mp hs
    obtain ⟨j, hj⟩ := odd_covered TT h2 s a0 a1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem prod_tops (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (h : Fin n' → ℝ) :
    ∏ s ∈ TT, h s = ∏ j, (h (segStart TT j) * ∏ i, h (segPos TT j i)) := by
  rw [Finset.prod_mul_distrib, prod_starts, Finset.prod_congr rfl fun j _ => prod_pos TT j h,
    ← Finset.prod_biUnion (fun j _ j' _ hjj => oddSet_disj TT j j' hjj), biUnion_odd TT h2,
    Finset.prod_filter_mul_prod_filter_not]

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def sd (m g : ℕ) : ℕ := Nat.choose (g + m) m

def mmB (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) : ℕ :=
  dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
      (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
      (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
    symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)

def UpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      rankOnDigits O C0 CE1 CE2 X j m rz ry ≤ mmB C0 CE1 CE2 X j rz ry

def lowFac (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (m : ℕ) : ℝ :=
  (1 - Real.exp (-(X.La C0) / 8)) * (1 - Real.exp (-(X.La C0) / 3)) *
    (1 - (X.m : ℝ) * (m : ℝ) / ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ))

def LowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ)

def SegLowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ *
        ((symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
          (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) : ℕ) : ℝ) ≤
        (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ)

def DimHHAt : Prop :=
  ∀ (Kf : Type) [Field Kf] [CharZero Kf] (n' m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    dimHH (m := m) Kf TT aT bT = ∏ s ∈ TT, sd m (aT s) * sd m (bT s)

def CharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jO w → CharZero Kf

def RestUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => UpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => LowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestSegLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SegLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem kap_core {p k N N1 La Q c a b' Y CE1 CE2 Cm : ℝ} (hk : 1 ≤ k) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hN1 : 1 ≤ N1)
    (_hLa : 0 ≤ La) (hQ : 1 ≤ Q) (hc : 0 ≤ c) (hb : 0 < b') (hp : k ^ 2 * Y ^ 2 ≤ p)
    (hLaNY : 8 * Real.log (N * Y) ≤ La) (hLak : La ≤ k) (hkb : k * b' ≤ a) (hLaY : La * Y * b' ≤ a)
    (hHc : k ^ 3 * Q ^ 2 * c * Y ≤ b') (hHb : k ^ 3 * Q * Y ≤ b') (h1 : 0 ≤ CE1) (h2 : 0 ≤ CE2) (h3 : 0 ≤ Cm) :
    Real.exp (-La / 8) + k * Q * (m0G4 Cm k N1 Q c + N1 * k) / b' + 1 / Y +
        k * errorTermBound CE1 CE2 p k N1 Q c a b' La / a ≤ (Cm + 4 * CE1 + CE2 + 15) * (N1 / Y) := by
  have hk0 : 0 < k := by linarith
  have hY0 : 0 < Y := by linarith
  have hN0 : 0 < N := by linarith
  have hN10 : 0 < N1 := by linarith
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hk0 hb) hkb
  have hba : b' ≤ a := le_trans (le_mul_of_one_le_left hb.le hk) hkb
  have hkY : k * Y ≤ p := by
    refine le_trans ?_ hp
    exact mul_le_mul (le_self_pow₀ hk two_ne_zero) (le_self_pow₀ hY two_ne_zero) hY0.le (by positivity)
  have hp1 : 1 ≤ p := le_trans (one_le_mul_of_one_le_of_one_le hk hY) hkY
  have hp0 : 0 < p := by linarith
  have hpp : p ≤ p ^ 2 := le_self_pow₀ hp1 two_ne_zero
  have hYp : Y ≤ p := le_trans (le_mul_of_one_le_left hY0.le hk) hkY
  have y1 : 1 / Y ≤ N1 / Y := div_le_div_of_nonneg_right hN1 hY0.le
  have t1 : Real.exp (-La / 8) ≤ N1 / Y := by
    have e : Real.exp (-La / 8) ≤ Real.exp (-(Real.log (N * Y))) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity)] at e
    have : (N * Y)⁻¹ ≤ 1 / Y := by
      rw [one_div]; exact inv_anti₀ hY0 (le_mul_of_one_le_left hY0.le hN)
    linarith
  obtain ⟨β, hβ⟩ : ∃ β, β = b' / Y := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; positivity
  have c1 : k ^ 3 * Q ^ 2 * c ≤ β := by rw [hβ, le_div_iff₀ hY0]; exact hHc
  have c2 : k ^ 3 * Q ≤ β := by rw [hβ, le_div_iff₀ hY0]; exact hHb
  have k23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num)
  have k13 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have Q12 : Q ≤ Q ^ 2 := le_self_pow₀ hQ two_ne_zero
  have d1 : k ^ 2 * Q ^ 2 * c ≤ β :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right k23 (by positivity)) hc) c1
  have d2 : k * Q * c ≤ β :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul k13 Q12 hQ0.le (by positivity)) hc) c1
  have d3 : k ^ 2 * Q ≤ β := le_trans (mul_le_mul_of_nonneg_right k23 hQ0.le) c2
  have t2 : k * Q * (m0G4 Cm k N1 Q c + N1 * k) / b' ≤ (Cm + 13) * (N1 / Y) := by
    rw [div_le_iff₀ hb]
    have e1 : (Cm + 13) * (N1 / Y) * b' = (Cm + 13) * N1 * β := by rw [hβ]; ring
    have e2 : k * Q * (m0G4 Cm k N1 Q c + N1 * k) =
        Cm * N1 * (k ^ 2 * Q ^ 2 * c) + 12 * (k * Q * c) + N1 * (k ^ 2 * Q) := by unfold m0G4 m1G4; ring
    rw [e1, e2]
    have f1 : Cm * N1 * (k ^ 2 * Q ^ 2 * c) ≤ Cm * N1 * β := mul_le_mul_of_nonneg_left d1 (by positivity)
    have f3 : N1 * (k ^ 2 * Q) ≤ N1 * β := mul_le_mul_of_nonneg_left d3 hN10.le
    have f2 : β ≤ N1 * β := le_mul_of_one_le_left hβ0.le hN1
    linarith
  obtain ⟨α, hα⟩ : ∃ α, α = a / Y := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  have hβα : β ≤ α := by rw [hβ, hα]; exact div_le_div_of_nonneg_right hba hY0.le
  have g1 : k * (a / p ^ 2) ≤ α := by
    rw [← mul_div_assoc, hα, div_le_div_iff₀ (by positivity) hY0]
    calc k * a * Y = a * (k * Y) := by ring
      _ ≤ a * p ^ 2 := mul_le_mul_of_nonneg_left (le_trans hkY hpp) ha.le
  have g2 : k * (b' / p) ≤ α := by
    rw [← mul_div_assoc, hα, div_le_div_iff₀ hp0 hY0]
    exact mul_le_mul hkb hYp hY0.le ha.le
  have g3 : k * (La * N1 * a / (p * k)) ≤ N1 * α := by
    have e : k * (La * N1 * a / (p * k)) = La * N1 * a / p := by field_simp
    rw [e, hα, ← mul_div_assoc, div_le_div_iff₀ hp0 hY0]
    calc La * N1 * a * Y = N1 * a * (La * Y) := by ring
      _ ≤ N1 * a * p :=
        mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_right hLak hY0.le) hkY) (by positivity)
  have g4 : k * (La * b' / k) ≤ α := by
    have e : k * (La * b' / k) = La * b' := by field_simp
    rw [e, hα, le_div_iff₀ hY0]
    linarith [hLaY]
  have g5 : k * (k ^ 2 * N1 * Q ^ 2 * c) ≤ N1 * α := by
    have e : k * (k ^ 2 * N1 * Q ^ 2 * c) = N1 * (k ^ 3 * Q ^ 2 * c) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (le_trans c1 hβα) hN10.le
  have t4 : k * errorTermBound CE1 CE2 p k N1 Q c a b' La / a ≤ (4 * CE1 + CE2) * (N1 / Y) := by
    rw [div_le_iff₀ ha]
    have e1 : (4 * CE1 + CE2) * (N1 / Y) * a = (4 * CE1 + CE2) * (N1 * α) := by rw [hα]; ring
    have e2 : k * errorTermBound CE1 CE2 p k N1 Q c a b' La =
        CE1 * (k * (a / p ^ 2) + k * (b' / p) + k * (La * N1 * a / (p * k)) + k * (La * b' / k)) +
          CE2 * (k * (k ^ 2 * N1 * Q ^ 2 * c)) := by unfold errorTermBound; ring
    rw [e1, e2]
    have f0 : α ≤ N1 * α := le_mul_of_one_le_left hα0.le hN1
    have f1 : CE1 * (k * (a / p ^ 2) + k * (b' / p) + k * (La * N1 * a / (p * k)) + k * (La * b' / k)) ≤
        CE1 * (4 * (N1 * α)) := mul_le_mul_of_nonneg_left (by linarith) h1
    have f2 : CE2 * (k * (k ^ 2 * N1 * Q ^ 2 * c)) ≤ CE2 * (N1 * α) := mul_le_mul_of_nonneg_left g5 h2
    linarith
  linarith

theorem rest2 (D : Formalism.BasicNotions.D7) : FamilyFourthBound D := by
  apply TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hCc hC0 _ h1 h2 h3 _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 Ckap hCkap
  refine ⟨Ckap * (Cm + 4 * CE1 + CE2 + 15), by positivity, ?_⟩
  intro X hD hI hc
  have S := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  have hk5 := S.k5
  have hN2 := S.N2
  have hLaY : X.La C0 * X.Y * X.b' ≤ X.a := by
    refine le_trans ?_ S.kYLab
    have hY0 : 0 < X.Y := by have := S.Y1; linarith
    have hLa0 : 0 < X.La C0 := by have := S.La1; linarith
    have hb := S.bpos
    have : 1 * (X.Y * X.La C0 * X.b') ≤ X.k * (X.Y * X.La C0 * X.b') :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [this]
  have core := kap_core (p := X.p) (k := X.k) (N := X.N) (N1 := X.N1) (La := X.La C0) (Q := X.Q) (c := X.c)
    (a := X.a) (b' := X.b') (Y := X.Y) (CE1 := CE1) (CE2 := CE2) (Cm := Cm) (by linarith) S.Y1 (by linarith) S.one_le_level_alt
    (by have := S.La1; linarith) S.Q1 (by positivity) S.bpos S.pk S.LaNY S.LaLeK S.kb hLaY
    (by have := S.Hc2 zero_le_one; linarith) (by have := S.Hb1 zero_le_one; linarith)
    (by linarith) (by linarith) (by linarith)
  have hN0 : 0 ≤ X.N := by linarith
  calc X.kapP C0 CE1 CE2 Cm Ckap
      = Ckap * X.N * (Real.exp (-X.La C0 / 8) + X.k * X.Q * (m0G4 Cm X.k X.N1 X.Q X.c + X.N1 * X.k) / X.b' + 1 / X.Y +
        X.k * errorTermBound CE1 CE2 X.p X.k X.N1 X.Q X.c X.a X.b' (X.La C0) / X.a) := rfl
    _ ≤ Ckap * X.N * ((Cm + 4 * CE1 + CE2 + 15) * (X.N1 / X.Y)) :=
        mul_le_mul_of_nonneg_left core (by positivity)
    _ = Ckap * (Cm + 4 * CE1 + CE2 + 15) * X.N * X.N1 / X.Y := by ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end
