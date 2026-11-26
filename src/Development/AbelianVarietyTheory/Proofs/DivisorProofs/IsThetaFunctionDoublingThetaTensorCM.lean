module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DblTargetThetaF

open GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun := topR
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun x := -botR x
  map_zero' := by ext; simp [botR]
  map_add' x y := by ext; simp [botR]; ring

theorem continuous_topH (nS nT : ℕ) : Continuous (topH F E nS nT) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ j

theorem continuous_sndH (nS nT : ℕ) : Continuous (sndH F E nS nT) := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact (continuous_matrix fun i j => continuous_id.matrix_elem (finSumFinEquiv (Sum.inr i)) j).neg

theorem map_topH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (topH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j

theorem map_sndH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (sndH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u (finSumFinEquiv (Sum.inr i)) j) = 0 := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) j
    change φ (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
    rw [map_neg, e, neg_zero]

theorem hOF_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp [hOF]

theorem hOF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topH F E nS nT x) (topH F E nS nT y) -
      hOF σ JS JT (sndH F E nS nT x) (sndH F E nS nT y) := by
  change _ = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (-botR x) (-botR y)
  rw [hOF_neg]
  unfold hOF
  have hs : ∀ g : Fin (nT + nT) → AEF F E, ∑ a, g a =
      ∑ a, g (finSumFinEquiv (Sum.inl a)) + ∑ a, g (finSumFinEquiv (Sum.inr a)) := fun g => by
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hs]
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, dblG, GlobalTheory.WeilM.dbl, topH, topR, botR,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem symplOHF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topH F E nS nT x) (topH F E nS nT y) -
      symplOHF σ JS JT ξ₀ (sndH F E nS nT x) (sndH F E nS nT y) := by
  unfold symplOHF symplOF
  rw [hOF_dbl, mul_sub, map_sub, mul_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem deltaT_eq {nS nT : ℕ} (f₁ f₂ : WOF F E nS nT → ℂ) :
    deltaT f₁ f₂ = fun w => f₁ (topH F E nS nT w) * conj (f₂ (sndH F E nS nT w)) := rfl

theorem topH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    topH F E nS nT (ratWF γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl

theorem sndH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    sndH F E nS nT (ratWF γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
  ext i j
  change -((incAF F E) (γ _ j)) = (incAF F E) (-(γ _ j))
  rw [map_neg]

theorem isThetaFunOF_deltaT (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1)
    {f₁ f₂ : WOF F E nS nT → ℂ} (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  rw [deltaT_eq]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · rw [map_add (f := _), map_add (f := _), symplOHF_dbl, topH_ratWF, sndH_ratWF, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn,
      neg_neg, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (topH F E nS nT) ⊓ U₂.comap (sndH F E nS nT),
      (hU₁.preimage (continuous_topH nS nT)).inter (hU₂.preimage (continuous_sndH nS nT)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_topH _ h0)) (topH F E nS nT w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ h0)) (sndH F E nS nT w)
    simp only [heisOF] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOHF_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _), map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_topH nS nT)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH nS nT)))
  · simp only [map_add (f := _)]
    exact (h₁.smooth k ((topH F E nS nT).comp L) ((continuous_topH nS nT).comp hL) (fun t => map_topH _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH F E nS nT).comp L) ((continuous_sndH nS nT).comp hL)
        (fun t => map_sndH _ (h0 t)) _))

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
          (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ f₁ f₂ h₁ h₂
  exact isThetaFunOF_deltaT σ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1 h₁ h₂

end GlobalTheory.DblTargetThetaF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCMStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_doublingThetaTensor_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  first | exact @GlobalTheory.DblTargetThetaF.main | exact GlobalTheory.DblTargetThetaF.main | (intros; apply GlobalTheory.DblTargetThetaF.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
open GlobalTheory.SignedHC

namespace GlobalTheory.KerConjMean.TopSizes

theorem natW_wtOf_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hM : lo ≤ hi) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (a : Fin n) :
    (((wtOf n E).natW a : ℕ) : ℝ) ≤ hi - lo + 1 := by
  have hn : 0 < n := a.pos
  have key : (wtOf n E).natW a = ((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩).toNat := by
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  have hd : (((wtOf n E).w a - (wtOf n E).w ⟨n - 1, by omega⟩ : ℤ) : ℝ) ≤ hi - lo + 1 := by
    unfold wtOf
    split_ifs with h
    · have e0 := hE _ (descEnum_mem E h.1 a)
      have e1 := hE _ (descEnum_mem E h.1 ⟨n - 1, by omega⟩)
      have f0 : ((⌊highestWeight E h.1 a⌋ : ℤ) : ℝ) ≤ ((highestWeight E h.1 a : ℚ) : ℝ) := by
        exact_mod_cast Int.floor_le _
      have f1 : ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) - 1 <
          ((⌊highestWeight E h.1 ⟨n - 1, by omega⟩⌋ : ℤ) : ℝ) := by
        exact_mod_cast Int.sub_one_lt_floor _
      have hr : ((a : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast a.2
      have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
      have g0 : ((highestWeight E h.1 a : ℚ) : ℝ) ≤ hi + ((n : ℝ) - 1) / 2 := by
        simp only [highestWeight]; push_cast; linarith [e0.2]
      have g1 : lo + ((n : ℝ) - 1) / 2 ≤ ((highestWeight E h.1 ⟨n - 1, by omega⟩ : ℚ) : ℝ) := by
        simp only [highestWeight, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, hc]
        linarith [e1.1]
      push_cast
      linarith
    · simp; linarith
  rw [key]
  have c : ∀ z : ℤ, (z.toNat : ℝ) = (((z.toNat : ℕ) : ℤ) : ℝ) := fun z => (Int.cast_natCast _).symm
  rw [c, Int.toNat_eq_max]
  push_cast
  exact max_le (by push_cast at hd; exact hd) (by linarith)

theorem extend_bounds {n : ℕ} (d : ℕ) (f : Fin n → ℚ) (h : ℝ) (hh : 0 ≤ h)
    (hf : ∀ i, 0 ≤ ((f i : ℚ) : ℝ) ∧ ((f i : ℚ) : ℝ) ≤ h) (j : ℕ) :
    0 ≤ ((GridData.extend d f j : ℤ) : ℝ) ∧ ((GridData.extend d f j : ℤ) : ℝ) ≤ h := by
  unfold GridData.extend
  split_ifs with hj
  · obtain ⟨h1, h2⟩ := hf ⟨j - d, hj⟩
    have a1 : (0 : ℚ) ≤ f ⟨j - d, hj⟩ := by exact_mod_cast h1
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 a1, le_trans ?_ h2⟩
    exact_mod_cast Int.floor_le _
  · simp [hh]

theorem entry_bounds {D : D7} (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (j : ℕ) (τ : D.what₂.Tau) :
    ∀ x ∈ (num D 1 τ).weightX j, -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  obtain ⟨hN, -, -, -, hm2, -, -, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, hbe, -⟩ := hs
  have hSc := large₂.Sc_pos
  have hg0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hScb : large₂.Sc ≤ large₂.sc.b := by nlinarith
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    have : D.R.t + sLen D + 1 ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_left _ (by omega)
    unfold bigN; omega
  have hts' : (D.R.t : ℝ) + (sLen D : ℝ) + 1 ≤ large₂.sc.b := le_trans (by exact_mod_cast hts) hN
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (sLen D : ℝ) := Nat.cast_nonneg _
  have hv : ∀ j, 0 ≤ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ∧ ((GridData.extend 2 (D.hc τ).v j : ℤ) : ℝ) ≤ large₂.Sc :=
    extend_bounds 2 _ _ hSc.le fun l => large₂.cloud_v τ l
  have hel : ∀ l : Fin D.R.m, 0 ≤ (((D.hc τ).e l : ℚ) : ℝ) ∧ (((D.hc τ).e l : ℚ) : ℝ) ≤ 4 * large₂.sc.b := fun l => by
    obtain ⟨h1, h2⟩ := hbe τ l
    have h3 := (D.hc τ).gap_be l
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have h4 : 0 ≤ (D.hc τ).e l := by linarith
    exact ⟨by exact_mod_cast h4, h2⟩
  have he := extend_bounds 1 _ _ (by linarith) hel
  have hcen : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 ≤ ((cen D 1 τ j : ℤ) : ℝ) ∧ ((cen D 1 τ j : ℤ) : ℝ) ≤ large₂.sc.b := by
    intro j hj1 hj2
    have e := GridData.mid_eq (GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0) hj1
    have hv2 := hv 2
    have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hj2' : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hj2
    have hmid : 0 ≤ (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ∧
        (((GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0).mid j : ℚ) : ℝ) ≤ large₂.sc.b := by
      rw [e]
      simp only [GridData.a, GridData.ofHCParam]
      push_cast
      constructor <;> nlinarith
    unfold cen
    refine ⟨by exact_mod_cast Int.floor_nonneg.2 (by exact_mod_cast hmid.1), le_trans ?_ hmid.2⟩
    exact_mod_cast Int.floor_le _
  intro x hx
  rcases GridData.mem_weightX.1 hx with h | h | ⟨i, hi1, hi2, h⟩ | ⟨l, -, -, h⟩
  · obtain ⟨i, hi, rfl⟩ := GridData.mem_tops.1 h
    have hi' : (i : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (show i ≤ D.R.m from hi)
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have hv2 := hv 2
    simp only [GridData.a, num, GridData.ofHCParam]
    push_cast
    constructor <;> nlinarith
  · obtain ⟨i, -, -, rfl⟩ := GridData.mem_cloudHalf.1 h
    have h : 0 ≤ (((num D 1 τ).v i : ℤ) : ℝ) ∧ (((num D 1 τ).v i : ℤ) : ℝ) ≤ large₂.Sc := hv i
    simp only [GridData.vHalf]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).cen i : ℤ) : ℝ) ∧ (((num D 1 τ).cen i : ℤ) : ℝ) ≤ large₂.sc.b := hcen i hi1 hi2
    have h1 : (((num D 1 τ).s - 1 : ℕ) : ℝ) ≤ (sLen D : ℝ) := by
      exact_mod_cast (show sLen D - 1 ≤ sLen D from Nat.sub_le _ _)
    have ha' : (a : ℝ) + 1 ≤ (((num D 1 τ).s - 1 : ℕ) : ℝ) := by exact_mod_cast ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · obtain ⟨a, ha, rfl⟩ := GlobalTheory.SignedHC.mem_block.1 h
    have h : 0 ≤ (((num D 1 τ).e l : ℤ) : ℝ) ∧ (((num D 1 τ).e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := he l
    have h1 : ((num D 1 τ).t : ℝ) = (D.R.t : ℝ) := rfl
    have ha' : (a : ℝ) ≤ ((num D 1 τ).t : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 ha
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem sizesK : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch _
  obtain ⟨hN, hf, hN1, hf1, -, hrd1, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS.size
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
  have hc : ch.sc.cGap = 1 := by
    have h : ch.sc = { cGap := 1, cDep := CF, b := large₂.sc.b } := hch
    rw [h]
  refine ⟨by linarith, hN1, hN, hf1, hf, (Lnk.card_Tau D).le, by linarith, ?_, fun j hj => ⟨?_, fun τ i => ?_⟩⟩
  · exact (Real.log_le_log_iff (by linarith) (by linarith)).1 (by linarith)
  · exact GlobalTheory.DefRank.rank_le_bigN ch.G (.top j) hj
  · have key : ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top j) τ), -(5 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
      rw [hc]
      intro x hx
      have e : GlobalTheory.SignedHC.entries (Node.par D 1 (.top j) τ) = (num D 1 τ).weightX j := entries_plus _
      exact entry_bounds large₂ hS.size j τ x (e ▸ hx)
    have hw := natW_wtOf_le _ _ _ _ (by linarith) key i
    calc (((wt ch.G (.top j) τ).natW i : ℕ) : ℝ)
        = (((wtOf _ (GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top j) τ))).natW i : ℕ) : ℝ) := rfl
      _ ≤ _ := hw
      _ ≤ 8 * large₂.sc.b := by linarith

end GlobalTheory.KerConjMean.TopSizes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoicesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_parameterSizes_testChoices : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  first | exact @GlobalTheory.KerConjMean.TopSizes.sizesK | exact GlobalTheory.KerConjMean.TopSizes.sizesK | (intros; apply GlobalTheory.KerConjMean.TopSizes.sizesK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoprimeScalarCentralElement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalCentral

noncomputable def scalGL (n : ℕ) {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) : GL (Fin n) S :=
  Units.map (Matrix.scalar (Fin n)).toMonoidHom h.unit

theorem scalGL_val (n : ℕ) {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) :
    (scalGL n h).1 = m • (1 : Matrix (Fin n) (Fin n) S) := by
  show Matrix.scalar (Fin n) (m : S) = _
  rw [Matrix.scalar_apply, ← Int.cast_smul_eq_zsmul S m (1 : Matrix (Fin n) (Fin n) S), Matrix.smul_one_eq_diagonal]

theorem scalGL_comm {n : ℕ} {S : Type} [CommRing S] {m : ℤ} (h : IsUnit (m : S)) (x : GL (Fin n) S) :
    x * scalGL n h = scalGL n h * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, scalGL_val, mul_smul_comm, smul_mul_assoc, mul_one, one_mul])

theorem isUnit_of_coprime {S : Type} [CommRing S] {m M : ℤ} (h : IsCoprime m M) (h0 : (M : S) = 0) : IsUnit (m : S) := by
  obtain ⟨a, b, e⟩ := h
  have e' : (m : S) * (a : S) = 1 := by
    have := congrArg (Int.cast : ℤ → S) e
    push_cast at this
    rw [h0, mul_zero, add_zero, mul_comm] at this
    exact this
  exact ⟨⟨m, a, e', by rw [mul_comm]; exact e'⟩, rfl⟩

theorem map_int_one {n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') (m : ℤ) (i j : Fin n) :
    f ((m • (1 : Matrix (Fin n) (Fin n) S)) i j) = (m • (1 : Matrix (Fin n) (Fin n) S')) i j := by
  rw [Matrix.smul_apply, Matrix.smul_apply, map_zsmul, Matrix.one_apply, Matrix.one_apply, apply_ite f, map_one, map_zero]

theorem cast_quot {O : Type} [CommRing O] (I : Ideal O) {M : ℕ} (h : (M : O) ∈ I) : (((M : ℕ) : ℤ) : O ⧸ I) = 0 := by
  rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk I)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

theorem mem_of_prod {O : Type} [CommRing O] (A : Ideal O) {I J : Ideal O} {x : O} (hA : A ≤ I) (h : A * J = Ideal.span {x})
    : x ∈ I := by
  have h0 : x ∈ A * J := by rw [h]; exact Ideal.mem_span_singleton_self x
  exact hA (Ideal.mul_le_inf h0).1

theorem cast_res {E : Type} [Field E] [NumberField E] (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {P : Pl E} (hP : P ∈ T) : (((M : ℕ) : ℤ) : kP P) = 0 :=
  cast_quot P.asIdeal (mem_of_prod _ ((GlobalTheory.OneMapRef.Lift.mem_iff_prod_le T P).1 hP) hJ)

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_matrix_int (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y : GL (Fin n) (Formalism.L2.Herm.intAf F E)} {m : ℤ}
    (h : ∀ P ∈ T, (Formalism.UG.bc (resS F P) y).1 = m • (1 : Matrix (Fin n) (Fin n) (kP P))) {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E),
      oToS F E b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - (m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) i j) = M • c := by
    intro i j
    have h1 : y.1 i j - (m • (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))) i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      GlobalTheory.LevelUnique.mem_map_prod _ T fun P hP => GlobalTheory.LevelUnique.sub_mem_idS
        ((congrArg (fun g : Matrix (Fin n) (Fin n) (kP P) => g i j) (h P hP)).trans (map_int_one (resS F P) m i j).symm)
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_smul_sub_int {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} {m : ℤ} (h : b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) S)) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - m • (1 : Matrix (Fin n) (Fin n) R)) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - m • (1 : Matrix (Fin n) (Fin n) R)) = M • s.map S.subtype := by
    ext i j
    have : S.subtype ((b • (y.1 - m • (1 : Matrix (Fin n) (Fin n) S))) i j) = S.subtype ((M • s) i j) := by rw [h]
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_int_one, map_nsmul] at this
    exact this
  have e2 : m • (1 : Matrix (Fin n) (Fin n) R) = β.1 * (m • (1 : Matrix (Fin n) (Fin n) R)) * (β⁻¹).1 := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv]
  rw [Units.val_mul, Units.val_mul, e2, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e, mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (m : ℤ)
    (h : ∀ P ∈ T, (redFn β P x).1 = m • (1 : Matrix (Fin n) (Fin n) (kP P))) {b : 𝓞 E} (hb : b ∈ J)
    {K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) •
          (K - m • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))) = M • N := by
  obtain ⟨y, rfl⟩ := hx
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix_int T hJ h hb
  have e := conj_smul_sub_int _ β hs
  have hN := fun z hz => (hfr _).2 (GlobalTheory.LevelUnique.conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK]
    have e3 := map_int_one (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom m i j
    refine Eq.trans ?_ (congrFun (congrFun e i) j)
    exact congrArg (fun t => _ * (_ - t)) e3

variable {D : D7}

theorem exists_cong_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) (m : ℤ)
    (h : ∀ P ∈ T, (redFn β P (Lev.finE V k)).1 = m • (1 : Matrix (Fin V.rank) (Fin V.rank) (kP P))) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z -
        (m • (1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))) *ᵥ z) = M • w := by
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat_int hfr T hJ hk m h hb (K := (finHom V k).1) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem eq_int_of_submatrix {n r : ℕ} (hr : n = r) (h : r ≤ n) {S : Type} [CommRing S] {x : Matrix (Fin n) (Fin n) S} {m : ℤ}
    (e : x.submatrix (Fin.castLE h) (Fin.castLE h) = m • (1 : Matrix (Fin r) (Fin r) S)) :
    x = m • (1 : Matrix (Fin n) (Fin n) S) := by
  subst hr
  exact e

theorem int_calc {R : Type} [CommRing R] {n : ℕ} {K : Matrix (Fin n) (Fin n) R} {x z w₂ w₃ : Fin n → R} {M : ℕ} {m : ℤ}
    (e₂ : x - K *ᵥ z = M • w₂) (e₃ : K *ᵥ z - (m • (1 : Matrix (Fin n) (Fin n) R)) *ᵥ z = M • w₃) :
    x - m • z = M • (w₂ + w₃) := by
  rw [smul_add, ← e₂, ← e₃, sub_add_sub_cancel, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem redFn_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k : GA D V} (hk : Lev.IsLevelLift V β L g k) (m : ℤ)
    (hg : ∀ P, (g P).1 = m • (1 : Matrix (Fin L.r) (Fin L.r) (kP P.1))) :
    ∀ P ∈ L.Pg, (redFn β P (Lev.finE V k)).1 = m • (1 : Matrix (Fin V.rank) (Fin V.rank) (kP P)) := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = g ⟨P, hP⟩ := congrFun hk.2.2 ⟨P, hP⟩
  have e' := (congrArg Units.val e).trans (hg ⟨P, hP⟩)
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP))] at e'
  exact eq_int_of_submatrix hr L.hr e'


end GlobalTheory.GalCentral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPureTensorFixedByOpenFiniteHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPureTensorFixedByOpenFiniteHeisenberg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Topology Filter

theorem pureA_fixed_fin :
    ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  intro F _ _ ψ hψ κ _ g hg
  haveI := GlobalTheory.HeisSchA.nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → FiniteAdeleRing (𝓞 F) F) := GlobalTheory.HeisSchA.nonarch_pi
  let χ := GlobalTheory.HeisSchA.finChar ψ
  have hL : IsOpen {a | χ a = 1} := (GlobalTheory.HeisSchA.finChar_isLocallyConstant ψ hψ).isOpen_fiber 1
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2

  obtain ⟨V0, hV0⟩ : ∃ V0 : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ V0, ∀ v ∈ V0, χ (c * (u ⬝ᵥ v)) = 1 := by
    have hcont : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        c * (p.1 ⬝ᵥ p.2) :=
      continuous_const.mul (continuous_fst.dotProduct continuous_snd)
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        χ (c * (p.1 ⬝ᵥ p.2)) = 1 := by
      rw [← nhds_prod_eq]
      refine hcont.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_)
      simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff (r := fun a b => χ (c * (a ⬝ᵥ b)) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun u hu v hv => hss u (hV hu) v (hV hv)⟩

  have hloc : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, ∃ V : OpenAddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      ∀ a ∈ V, ∀ u ∈ V, g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1 := by
    intro y
    have c1 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        y + p.1 + p.2 := (continuous_const.add continuous_fst).add continuous_snd
    have c2 : Continuous fun p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
        (y + p.1) ⬝ᵥ p.2 := (continuous_const.add continuous_fst).dotProduct continuous_snd
    have h0 : ∀ᶠ p : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) in 𝓝 0 ×ˢ 𝓝 0,
        g (y + p.1 + p.2) = g y ∧ χ ((y + p.1) ⬝ᵥ p.2) = 1 := by
      rw [← nhds_prod_eq]
      refine Filter.Eventually.and (c1.continuousAt.preimage_mem_nhds ((hg.1.isOpen_fiber (g y)).mem_nhds ?_))
        (c2.continuousAt.preimage_mem_nhds (hL.mem_nhds ?_))
      · simp
      · simp [χ]
    obtain ⟨s, hs, hss⟩ := (Filter.eventually_prod_self_iff
      (r := fun a u => g (y + a + u) = g y ∧ χ ((y + a) ⬝ᵥ u) = 1)).mp h0
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean s hs
    exact ⟨V, fun a ha u hu => hss a (hV ha) u (hV hu)⟩
  choose V hV using hloc
  obtain ⟨t, -, htK⟩ := (hg.2 : IsCompact (tsupport g)).elim_nhds_subcover
    (fun y => {z | z - y ∈ (V y : Set (κ → FiniteAdeleRing (𝓞 F) F))}) (fun y _ => by
      refine (continuous_sub_right y).continuousAt.preimage_mem_nhds ?_
      rw [sub_self]
      exact (V y).isOpen.mem_nhds (V y).zero_mem)
  let M0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (V0 : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) ⊓ ⨅ y ∈ t, (V y : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F))
  have hM0 : ∀ u ∈ M0, u ∈ V0 ∧ ∀ y ∈ t, u ∈ V y := fun u hu => by
    simp only [M0, AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hu
    exact ⟨hu.1, hu.2⟩
  have hM0open : IsOpen (M0 : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
    refine M0.isOpen_of_mem_nhds (g := 0) ?_
    refine Filter.mem_of_superset (Filter.inter_mem (V0.isOpen.mem_nhds V0.zero_mem)
      ((Filter.biInter_finset_mem t).2 fun y _ => (V y).isOpen.mem_nhds (V y).zero_mem)) ?_
    intro u hu
    simp only [Set.mem_inter_iff, Set.mem_iInter] at hu
    simp only [M0, SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
    exact ⟨hu.1, hu.2⟩
  have hcov : ∀ y ∈ tsupport g, ∀ u ∈ M0, g (y + u) = g y ∧ ∀ v ∈ M0, χ (y ⬝ᵥ v) = 1 := by
    intro y hy u hu
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ t, y - z ∈ V z := by simpa using htK hy
    have e : z + (y - z) = y := by abel
    have h1 := hV z (y - z) hyz u ((hM0 u hu).2 z hz)
    have h2 := hV z (y - z) hyz 0 (V z).zero_mem
    rw [e] at h1 h2
    rw [add_zero] at h2
    refine ⟨h1.1.trans h2.1.symm, fun v hv => ?_⟩
    have h3 := hV z (y - z) hyz v ((hM0 v hv).2 z hz)
    rw [e] at h3
    exact h3.2
  have hinv : ∀ u ∈ M0, ∀ y, g (y + u) = g y := by
    intro u hu y
    by_cases hy : y ∈ tsupport g
    · exact (hcov y hy u hu).1
    by_cases hy' : y + u ∈ tsupport g
    · have := (hcov (y + u) hy' (-u) (M0.neg_mem hu)).1
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']
  refine ⟨M0.prod M0, by rw [AddSubgroup.coe_prod]; exact hM0open.prod hM0open, ?_⟩
  rintro ⟨u, v⟩ hm f
  rw [AddSubgroup.mem_prod] at hm
  obtain ⟨hu, hv⟩ := hm
  funext x
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA, finE2]
  have harg : x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v) =
      ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) := by
    have hp1 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p1 (finE F w i) = 0 := fun _ _ => rfl
    have hp2 : ∀ (w : κ → FiniteAdeleRing (𝓞 F) F) (i : κ), GlobalTheory.HeisSchA.p2 (finE F w i) = w i := fun _ _ => rfl
    refine Prod.ext ?_ ?_
    · change GlobalTheory.HeisSchA.p1 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = 0
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp1, mul_zero, Finset.sum_const_zero, add_zero]
    · change GlobalTheory.HeisSchA.p2 (x ⬝ᵥ finE F v + ⅟(2 : AdeleRing (𝓞 F) F) * (finE F u ⬝ᵥ finE F v)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_mul, dotProduct, map_sum, hp2]
      rfl
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + finE F u) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    rw [show ((x + finE F u) i).1 = (x i).1 from add_zero (x i).1]
  have hgx : (fun i => ((x + finE F u) i).2) = (fun i => (x i).2) + u := by
    funext i
    rfl
  rw [harg, hf, hgx, hinv u hu]
  by_cases h0 : g (fun i => (x i).2) = 0
  · rw [h0]
    ring
  · have hy : (fun i => (x i).2) ∈ tsupport g := subset_tsupport g h0
    have e1 := (hcov _ hy u hu).2 v hv
    have e2 := hV0 u (hM0 u hu).1 v (hM0 v hv).1
    have : ψ ((0 : InfiniteAdeleRing F), (fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1 := by
      change χ ((fun i => (x i).2) ⬝ᵥ v + c * (u ⬝ᵥ v)) = 1
      rw [AddChar.map_add_eq_mul, e1, e2, one_mul]
    rw [this, one_mul]

end GlobalTheory.WeilAdm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPureTensorFixedByOpenFiniteHeisenbergStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicPureTensor_fixed_by_open_finiteHeisenberg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  first | exact @GlobalTheory.WeilAdm.pureA_fixed_fin | exact GlobalTheory.WeilAdm.pureA_fixed_fin | (intros; apply GlobalTheory.WeilAdm.pureA_fixed_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeData
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.SumCount.DataCount

section General

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [FiniteDimensional K V]

theorem finrank_le_dim (M : Submodule (𝓞 K) V) : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
  have h1 : Module.rank (𝓞 K) M ≤ Module.rank (𝓞 K) V := Submodule.rank_le M
  have h2 : Module.rank (𝓞 K) V = Module.rank K V := (IsFractionRing.rank_right_eq (𝓞 K) K V).symm
  rw [h2, ← Module.finrank_eq_rank K V] at h1
  exact Module.finrank_le_of_rank_le h1

theorem card_quot_le_of_fg (M : Submodule (𝓞 K) V) [Module.Finite (𝓞 K) M] {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ∧
      Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Module.Flat (𝓞 K) M := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have h1 : (a : K) • (x : V) = 0 := by
      have h0 : a • (x : V) = 0 := congrArg Subtype.val hx
      rwa [← algebraMap_smul K a] at h0
    have h2 : (a : K) ≠ 0 := by
      have := nonZeroDivisors.ne_zero ha
      exact_mod_cast this
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left h2)
  have e := GlobalTheory.DVRQuotCount.card_quot_smul_top_of_flat' (N := M) I
  have hN : Nat.card (𝓞 K ⧸ I) = Ideal.absNorm I := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hI)
  rw [hN] at e
  refine ⟨Nat.finite_of_card_ne_zero (by rw [e]; exact (pow_pos hpos _).ne'), ?_⟩
  rw [e]
  exact Nat.pow_le_pow_right hpos (finrank_le_dim M)

theorem card_quot_le (M : Submodule (𝓞 K) V) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Nat.card (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) ≤ Ideal.absNorm I ^ Module.finrank K V := by
  by_cases hf : Finite (M ⧸ (I • ⊤ : Submodule (𝓞 K) M))
  swap
  · haveI := not_finite_iff_infinite.1 hf
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _
  choose s hs using Submodule.Quotient.mk_surjective (I • ⊤ : Submodule (𝓞 K) M)
  let M' : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range fun q => (s q : V))
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact (s q).2)
  haveI : Module.Finite (𝓞 K) M' := Module.Finite.span_of_finite _ (Set.finite_range _)
  obtain ⟨hfin, hc⟩ := card_quot_le_of_fg M' hI
  let φ : (M' ⧸ (I • ⊤ : Submodule (𝓞 K) M')) →ₗ[𝓞 K] (M ⧸ (I • ⊤ : Submodule (𝓞 K) M)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)
  have hφ : Function.Surjective φ := fun q =>
    ⟨Submodule.Quotient.mk ⟨s q, Submodule.subset_span ⟨q, rfl⟩⟩, hs q⟩
  exact (Nat.card_le_card_of_surjective φ hφ).trans hc

end General

theorem absNorm_le_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm w.asIdeal ≤ Ideal.absNorm (w.under (𝓞 F)).asIdeal ^ 2 := by
  have hr : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← h2]
    exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm
  have h1 := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 E) (w.under (𝓞 F)).asIdeal
  rw [hr] at h1
  rw [← h1]
  refine Nat.le_of_dvd ?_ (Ideal.absNorm_dvd_absNorm_of_le Ideal.map_comap_le)
  rw [h1]
  exact pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (w.under (𝓞 F)).ne_bot)) _

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.SumSize GlobalTheory.RowTest

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sig_nonneg : 0 ≤ sig G :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)

theorem absNorm_modul_le : (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  unfold sig
  rw [Finset.mul_sum, Real.exp_sum]
  show ((Ideal.absNorm (∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v) : ℕ) : ℝ) ≤ _
  rw [map_prod, Nat.cast_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun v hv => ?_
  have h1 := absNorm_le_sq D.sp.cm.deg2 (G.pl.w v)
  rw [G.pl.under_w hv] at h1
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  have e : Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
    rw [← pow_mul, ← mul_assoc, ← Nat.cast_ofNat, ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpos]
  rw [e, map_pow, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h1) _

theorem rank_row_le {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i 0)).rank ≤ bigN D := by
  have hr : (G.V (.grid i 0)).rank = rankV D i 0 := by
    cases i with
    | zero =>
      refine (D.sp.Y_rank _ (min_le_right _ _)).trans ?_
      rw [min_eq_left (Nat.zero_le _)]
      simp [rankV, Ranks.rankY]
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).rank
  have h1 : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have hk : D.R.r = D.R.k + D.R.m - 1 := rfl
  rw [hr]
  simp only [rankV, bigN]
  have e : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
  rw [e]
  omega

theorem card_cosAt_le {i : ℕ} (hi : i < D.R.m) :
    (Nat.card (G.CosAt i) : ℝ) ≤ Real.exp ((bigN D : ℝ) ^ 2 * (2 * sig G)) := by
  have h1 := card_quot_le (homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) (G.pl.modul_ne_bot sc)
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_fin, Fintype.card_fin] at h1
  have hpos : 0 < Ideal.absNorm G.modul := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 (G.pl.modul_ne_bot sc))
  have h2 : (G.V (.grid i 0)).rank * (G.V (.grid (i + 1) 0)).rank ≤ bigN D ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (rank_row_le G hi.le) (rank_row_le G hi)
  have h3 : Nat.card (G.CosAt i) ≤ Ideal.absNorm G.modul ^ (bigN D ^ 2) := h1.trans (Nat.pow_le_pow_right hpos h2)
  calc (Nat.card (G.CosAt i) : ℝ) ≤ (Ideal.absNorm G.modul : ℝ) ^ (bigN D ^ 2) := by exact_mod_cast h3
    _ ≤ Real.exp (2 * sig G) ^ (bigN D ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_modul_le G) _
    _ = _ := by rw [← Real.exp_nat_mul]; push_cast; rfl

theorem card_datum_le : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * ((bigN D : ℝ) ^ 2 * (2 * sig G))) := by
  rw [Nat.card_pi, Nat.cast_prod, Real.exp_nat_mul]
  refine (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun i _ => card_cosAt_le G i.2).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_datum_le_aOne {C b : ℝ} (hC : 2 ≤ C) (hb : 1 ≤ b) : (Nat.card G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne G C b) := by
  refine (card_datum_le G).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hl := Real.log_nonneg hb
  have hs : 0 ≤ (bigN D : ℝ) ^ 2 * sig G := mul_nonneg (by positivity) (sig_nonneg G)
  have h1 : 0 ≤ C * D.R.f * bigN D * b * Real.log b := by
    have : 0 ≤ C := by linarith
    have : 0 ≤ b := by linarith
    positivity
  have h2 : 2 ≤ C * D.R.m := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hs
  unfold aOne
  nlinarith

theorem dataK : GlobalTheory.SumCount.DataK := by
  refine ⟨0, fun CF _ => ⟨2, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ _ => ?_⟩⟩⟩
  have hL : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  exact card_datum_le_aOne ch.G hC (Real.one_le_exp (by linarith))

end GlobalTheory.SumCount.DataCount

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeDataStatement
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumCountBound_largeData : GlobalTheory.SumCount.DataK := by
  first | exact @GlobalTheory.SumCount.DataCount.dataK | exact GlobalTheory.SumCount.DataCount.dataK | (intros; apply GlobalTheory.SumCount.DataCount.dataK <;> assumption)
end
end
