module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem exists_flags_of_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), SameOrbit (basePart M.blk (fstPt k₀ z)) (BM.Rb.lift b' b') → ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hj hblk hca hcb hy l b' hb' z hz ho
  obtain ⟨g1, g2, g3, g4⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  set β := FC.bvec BM l b' with hβ
  obtain ⟨c, hc, ec⟩ : SameOrbit (basePart M.blk (fstPt k₀ z)) β := orbit_trans ho (orbit_symm g4)
  let t : Option K → ℂ := fun o => match o with
    | some k => if hk : ∀ p, M.blk p ≠ some k then (c ⟨k, hk⟩)⁻¹ else 1
    | none => 1
  have ht : ∀ o, t o ≠ 0 := fun o => by
    cases o with
    | none => exact one_ne_zero
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [t, dif_pos hk]
        exact inv_ne_zero (hc _)
      · simp only [t, dif_neg hk]
        exact one_ne_zero
  let z₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => t p.1 * z p
  have o2 : SameOrbit z₁ z := ⟨t, ht, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) o2 hz
  have eb : basePart M.blk (fstPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have e : z ⟨some k, m⟩ = c ⟨k, hk⟩ * β ⟨⟨k, hk⟩, m⟩ := congrFun ec ⟨⟨k, hk⟩, m⟩
    show t (some k) * z ⟨some k, m⟩ = β _
    simp only [t, dif_pos hk]
    rw [e, inv_mul_cancel_left₀ (hc _)]
  have P := GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hj hblk hca hcb hy (BM.F l) z₁ (BM.isFrame l)
    (by rw [eb]; exact g1) (by rw [eb]; exact g2) (by rw [eb]; exact g3)
  obtain ⟨h, s, f1, f2⟩ := P.1 hz₁
  refine ⟨h, s, f1.2.1, orbit_trans (orbit_symm o2) ?_⟩
  have eb2 : basePart M.blk (sndPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (by rw [hblk, e])
    have e1 : sndPt k₀ z₁ ⟨k, m⟩ = fstPt k₀ z₁ ⟨k, m⟩ := by
      show z₁ (v₁ k₀ ⟨k, m⟩) = z₁ (v₀ k₀ ⟨k, m⟩)
      rw [v₁_ne hne]
      rfl
    exact e1.trans (congrFun eb ⟨⟨k, hk⟩, m⟩)
  have key : ∀ o : Option K, ∃ e : ℂ, e ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      z₁ ⟨o, m⟩ = e * FC.wVec M (BM.F l) β h τ a k₀ ca cb s ⟨o, m⟩ := fun o => by
    cases o with
    | none =>
      obtain ⟨e, he, w⟩ := f2.2.2 (τ, a) k₀ hblk
      refine ⟨e, he, fun m => ?_⟩
      have w' := w m
      rw [eb2] at w'
      simp only [Function.update_self] at w'
      have e1 : sndPt k₀ z₁ ⟨k₀, m⟩ = z₁ ⟨none, m⟩ := by
        show z₁ (v₁ k₀ ⟨k₀, m⟩) = _
        rw [v₁_self]
      rw [← e1, w']
      rfl
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · refine ⟨1, one_ne_zero, fun m => ?_⟩
        have e1 := congrFun eb ⟨⟨k, hk⟩, m⟩
        have e2 := congrFun (FC.basePart_flagPt M (BM.F l) β h) ⟨⟨k, hk⟩, m⟩
        show z₁ ⟨some k, m⟩ = 1 * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [one_mul]
        exact e1.trans e2.symm
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨e, he, w⟩ := f1.2.2 p k hp
        refine ⟨e, he, fun m => ?_⟩
        have w' := w m
        rw [eb] at w'
        show z₁ ⟨some k, m⟩ = e * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [FC.flagPt_step M (BM.F l) β h hp m]
        exact w'
  choose e he hm using key
  exact ⟨e, he, funext fun q => hm q.1 q.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithVarietySecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_arith_variety_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), SameOrbit (basePart M.blk (fstPt k₀ z)) (BM.Rb.lift b' b') → ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flags_of_point | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flags_of_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flags_of_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_self_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  have key : minorIJ X C C = minorIJ Xᵀ C C := by
    rw [minorIJ_eq_det X C C C.card rfl rfl, minorIJ_eq_det Xᵀ C C C.card rfl rfl,
      ← Matrix.transpose_submatrix, Matrix.det_transpose]
  rw [key, minorIJ_self_of_triangular Xᵀ (fun i j hij => by simpa [Matrix.transpose_apply] using hX.2 j i hij) C]
  exact Finset.prod_eq_one (fun c _ => hX.1 c)

theorem minorIJ_insert_erase_of_isLowerUni {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) {C : Finset (Fin N)}
    {a' b' : Fin N} (hb : b' ∈ C) (hmax : ∀ c ∈ C, c ≤ b') (hlt : b' < a') :
    minorIJ X (insert a' (C.erase b')) C = X a' b' := by
  have ha : a' ∉ C := fun h => absurd (hmax a' h) (not_le.mpr hlt)
  obtain ⟨n, hn⟩ : ∃ n, C.card = n + 1 :=
    ⟨C.card - 1, by have := Finset.card_pos.mpr ⟨b', hb⟩; omega⟩
  have hR : (insert a' (C.erase b')).card = n + 1 := by
    rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hb, hn]
    rfl
  set eC := C.orderEmbOfFin hn with heC
  have hlast : eC (Fin.last n) = b' := by
    have hmem : b' ∈ Set.range eC := by rw [heC, Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨k, hk⟩ := hmem
    rcases (Fin.le_last k).lt_or_eq with h | h
    · have h1 : eC k < eC (Fin.last n) := eC.strictMono h
      have h2 : eC (Fin.last n) ∈ C := Finset.orderEmbOfFin_mem C hn _
      exact absurd (hmax _ h2) (not_le.mpr (hk ▸ h1))
    · rw [← h, hk]
  have hlt' : ∀ k : Fin (n + 1), k ≠ Fin.last n → eC k < b' := fun k hk =>
    hlast ▸ eC.strictMono (lt_of_le_of_ne (Fin.le_last k) hk)
  let f : Fin (n + 1) → Fin N := fun k => if k = Fin.last n then a' else eC k
  have hfmono : StrictMono f := by
    intro i j hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp only [f, if_neg hi]
    by_cases hj : j = Fin.last n
    · rw [if_pos hj]; exact (hlt' i hi).trans hlt
    · rw [if_neg hj]; exact eC.strictMono hij
  have hfmem : ∀ k, f k ∈ insert a' (C.erase b') := by
    intro k
    simp only [f]
    split_ifs with hk
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨(hlt' k hk).ne, Finset.orderEmbOfFin_mem C hn k⟩)
  have hR' : ⇑((insert a' (C.erase b')).orderEmbOfFin hR) = f :=
    (Finset.orderEmbOfFin_unique hR hfmem hfmono).symm
  rw [minorIJ_eq_det X _ C (n + 1) hR hn, hR', Matrix.det_of_lowerTriangular]
  · have h1 : ∀ k : Fin n, X.submatrix f eC k.castSucc k.castSucc = 1 := by
      intro k
      show X (f k.castSucc) (eC k.castSucc) = 1
      simp only [f, if_neg (Fin.castSucc_lt_last k).ne]
      exact hX.1 _
    rw [Fin.prod_univ_castSucc, Finset.prod_eq_one (fun k _ => h1 k), one_mul]
    show X (if Fin.last n = Fin.last n then a' else eC (Fin.last n)) (eC (Fin.last n)) = X a' b'
    rw [if_pos rfl, hlast]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    simp only [Matrix.submatrix_apply, f, if_neg hi]
    exact hX.2 _ _ (eC.strictMono hij')

theorem mem_stepCols_stepOf (N j : ℕ) (c : Fin N) :
    c ∈ stepCols N j (stepOf N j c) ∧ ∀ x ∈ stepCols N j (stepOf N j c), x ≤ c := by
  have hc := c.isLt
  refine ⟨?_, fun x hx => ?_⟩
  · simp only [stepCols, stepOf]
    split_ifs
    all_goals (try simp)
    all_goals omega
  · have hx' := x.isLt
    simp only [stepCols, stepOf] at hx
    rw [Fin.le_iff_val_le_val]
    split_ifs at hx
    all_goals (try simp at hx)
    all_goals omega

theorem minorIJ_stepCols_of_isLowerUni (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N) (_hj : j ≤ N)
    (_hd : IsBlockDiag j X) (hX : IsLowerUni X) (hlt : b' < a') (_hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) :
    minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧
      minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  obtain ⟨hb, hmax⟩ := mem_stepCols_stepOf N j b'
  exact ⟨minorIJ_self_of_isLowerUni hX _, minorIJ_insert_erase_of_isLowerUni hX hb hmax hlt⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_minor_formula : ∀ (N j : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (a' b' : Fin N), j ≤ N → IsBlockDiag j X → IsLowerUni X → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → minorIJ X (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) = 1 ∧ minorIJ X (insert a' ((stepCols N j (stepOf N j b')).erase b')) (stepCols N j (stepOf N j b')) = X a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowMinor.minorIJ_stepCols_of_isLowerUni <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead

theorem isProperStep_stepOf {N j : ℕ} (hj : j ≤ N) {a' b' : Fin N} (hba : b' < a')
    (hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) : IsProperStep N j (stepOf N j b') := by
  have ha := a'.2
  have hb := b'.2
  have hba' : (b' : ℕ) < a' := hba
  simp only [IsProperStep, stepOf]
  split_ifs with h
  · constructor <;> omega
  · constructor <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb hh τ' a' b' z A L U hF hzb hG hA hLU hLb hLu hUb hUt hUd
    hba hs hz
  have hj := M.j_le
  have hP : IsProperStep N j (stepOf N j b') := isProperStep_stepOf hj hba hs
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', stepOf N j b') = some k := by
    cases h : M.blk (τ', stepOf N j b') with
    | none => exact absurd hP ((M.blk_none _).1 h)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨α, hα, hzα⟩ := hz k hk
  have hT : ∀ J, twMinor M F zb (stepOf N j b') k (hh τ')⁻¹ z J =
      α * (minorIJ L J (stepCols N j (stepOf N j b')) *
        minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b'))) := by
    intro J
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', stepOf N j b') k A (hh τ')⁻¹ z α J hF hzb hG hk
      hA hzα, hLU, MinorCalc.minorIJ_mul_of_support L U J (stepCols N j (stepOf N j b'))
      (MinorCalc.support_stepCols (i := stepOf N j b') hj U hUb hUt)]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lower_unipotent_minor_formula N j L a' b' hj hLb hLu hba hs
  have hUne : minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) ≠ 0 := by
    rw [MinorCalc.minorIJ_self_of_triangular U hUt]
    exact Finset.prod_ne_zero_iff.2 hUd
  unfold lowRead
  simp only [hk, Option.elim_some]
  rw [hT, hT, h1, h2, one_mul, mul_div_mul_left _ _ hα, mul_div_assoc, div_self hUne, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValueStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_LU_minor_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorMulSelf
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto

section Mat

variable {Ψ : Type} {N j : ℕ}

theorem pMat_of_low (keep : Ψ × Fin N → Prop) (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hb : ∀ τ, IsBlockDiag j (L τ))
    (hl : ∀ τ, IsLowerUni (L τ))
    (hs : ∀ (τ : Ψ) (a b : Fin N), b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) →
      (¬ ∃ i, keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L τ a b = 0) (τ : Ψ) :
    pMat keep (fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) τ = L τ := by
  ext a b
  unfold pMat lowMat cExt
  by_cases h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · rw [dif_pos h]
    by_cases hS : Sep keep (⟨(τ, a, b), h⟩ : LowIdx Ψ N j)
    · rw [dif_pos hS]
    · rw [dif_neg hS]
      exact (hs τ a b h.1 h.2 hS).symm
  · rw [dif_neg h]
    by_cases e : a = b
    · subst e
      rw [if_pos rfl, (hl τ).1]
    · rw [if_neg e]
      rcases lt_or_gt_of_ne e with hlt | hgt
      · exact ((hl τ).2 a b hlt).symm
      · exact (hb τ a b fun hi => h ⟨hgt, hi⟩).symm

theorem minor_self {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, det_of_lowerTriangular (X.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)) fun a b e =>
    hX.2 _ _ ((C.orderEmbOfFin rfl).strictMono (show a < b from e))]
  exact Finset.prod_eq_one fun a _ => hX.1 _

theorem minor_mul_self {G W L : Matrix (Fin N) (Fin N) ℂ} (hGW : G * W = L) (hL : IsLowerUni L) {S : Finset (Fin N)}
    (hz : ∀ k c, c ∈ S → k ∉ S → W k c = 0) : 1 = minorIJ G S S * minorIJ W S S := by
  rw [← MinorCalc.minorIJ_mul_of_support G W S S hz, hGW, minor_self hL]

theorem ratio {α g s w sg x : ℂ} (hα : α ≠ 0) (h1 : sg * x = g * w) (h2 : 1 = s * w) (hsg : sg ≠ 0) :
    α * g / (sg * (α * s)) = x := by
  have hs : s ≠ 0 := fun e => by simp [e] at h2
  rw [div_eq_iff (mul_ne_zero hsg (mul_ne_zero hα hs))]
  linear_combination (α * g) * h2 - (α * s) * h1

end Mat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_scale {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : Kk → ℂ)
    (z : (Σ k, ιk k) → ℂ) {k : K} {t : ℂ} (hr : k ∈ Set.range κ) (hk : ∀ k', κ k' = k → c k' = t) (m : ι k) :
    upV v (fun p => c p.1 * z p) ⟨k, m⟩ = t * upV v z ⟨k, m⟩ := by
  obtain ⟨q, e⟩ := hb.2.2.2 ⟨k, m⟩ hr
  rw [← e, upV_apply hb.2.1, upV_apply hb.2.1]
  have e' : κ q.1 = k := by
    have := hb.2.2.1 q
    rw [e] at this
    exact this.symm
  rw [hk _ e']

end Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, pRho M Rb keep v F kb r h ε z ∈ pD ε V ∧ SameOrbit (pPhi M F keep v bl h ε (pRho M Rb keep v F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε ctx z hz
  have ctx0 := ctx
  obtain ⟨hbm, hκ, hF, hBC, hr1, hr2, hh⟩ := ctx
  obtain ⟨hzP, hs, hV, hm⟩ := hz
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := (GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hbm hκ).1 z hzP
  have hB : pB ε (pRho M Rb keep v F kb r h ε z) = Rb.A.chart kb (r (pBase M v z)) := by
    funext l
    simp only [pB, pRho, Equiv.symm_apply_apply]
  have hLp : ∀ q : PIdx j keep, pL ε (pRho M Rb keep v F kb r h ε z) q =
      pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2 := fun q => by
    simp only [pL, pRho, Equiv.symm_apply_apply]
  have hwD : pRho M Rb keep v F kb r h ε z ∈ pD ε V := by
    show pB ε _ ∈ V
    rw [hB]
    exact hV
  refine ⟨hwD, ?_⟩
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hs] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) (hr1 _ hzb)
  obtain ⟨c₀, hc₀, he⟩ := horb
  have hv : ∀ s, valAt M.x s zc = valAt M.x s (pBase M v z) := fun s => by
    have := StepW.TorusAct.valAt_torus (x := M.x) c₀ hc₀ hzb (he ▸ hblm) s
    rw [he]
    exact this
  let c : Kk → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some (κ k) then c₀ ⟨κ k, hk⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases hk : ∀ p, M.blk p ≠ some (κ k)
    · simp only [c, dif_pos hk]
      exact hc₀ _
    · simp only [c, dif_neg hk]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c p.1 * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _) c hc hzP
  have hbase : ∀ (k : NonPluckerBlocks M.blk) (m : ι k.1), upV v z' ⟨k.1, m⟩ = c₀ k * upV v z ⟨k.1, m⟩ := fun k m =>
    upV_scale hbm c z ((hκ k.1).2 (Or.inl k.2)) (fun k' e' => by
      have hk' : ∀ p, M.blk p ≠ some (κ k') := e' ▸ k.2
      simp only [c, dif_pos hk']
      congr 1
      exact Subtype.ext e') m
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨k, m⟩ := q
    exact hbase k m
  have hkept : ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v z' ⟨k, m⟩ = 1 * upV v z ⟨k, m⟩ :=
    fun p k hp hk m => upV_scale hbm c z ((hκ k).2 (Or.inr ⟨p, hp, hk⟩)) (fun k' e' => by
      have hk' : ¬ ∀ p, M.blk p ≠ some (κ k') := fun hn => hn p (hk.trans (by rw [e']))
      simp only [c, dif_neg hk']) m
  obtain ⟨H, hH, hHf⟩ := GlobalTheory.T.blockMap_frame_restriction_regular K ι Φ y Ψ N j M keep Kk ιk κ v hbm hκ F z' hF hz' (hbp ▸ hblgood)
    (by rw [hbp]; exact hblnorm)
  rw [hbp] at hHf
  have hmin : ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧
      (∀ m : ι k, upV v z' ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zc * minorIJ (H p.1) I (stepCols N j p.2)) ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)),
        twMinor M F (pBase M v z) p.2 k g (upV v z) J = α * minorIJ (g * H p.1) J (stepCols N j p.2) := by
    intro p k hp hk
    obtain ⟨α, hα, hw⟩ := hHf p k hp hk
    refine ⟨α, hα, hw, fun g J => ?_⟩
    have h1 := Cover.twMinor_of_flag M hF hblm hblgood hk (hH p.1).1 hw g J
    have h2 := Orb.twMinor_scale M F hv p.2 k g (hkept p k hp hk) J
    rw [one_mul] at h2
    rw [← h2]
    exact h1
  have hsome : ∀ p, IsProperStep N j p.2 → ∃ k, M.blk p = some k := fun p hp =>
    Option.ne_none_iff_exists'.1 fun e' => (M.blk_none p).1 e' hp
  have hproper : ∀ p k, M.blk p = some k → IsProperStep N j p.2 := fun p k hk => by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hk
    exact absurd hk (by simp)
  have hjN := M.j_le
  have hdec := fun τ => GlobalTheory.T.exists_lowerUni_blockDiag_factorization N j (fun i => keep (τ, i)) ((h τ)⁻¹ * H τ) hjN
    (((hh τ).1.inv (hh τ).2.isUnit).mul (hH τ).1)
    (by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh τ).2.isUnit).ne_zero (hH τ).2)
    (fun i hk hp => by
      obtain ⟨k, hbk⟩ := hsome (τ, i) hp
      obtain ⟨α, -, -, hT⟩ := hmin (τ, i) k hk hbk
      have := hm (τ, i) k hk hbk
      rw [hT] at this
      exact right_ne_zero_of_mul this)
  choose L W hLb hLu hLs hWb hWs hGW using hdec
  have hpm : ∀ τ, pMat keep (fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) τ = L τ :=
    pMat_of_low keep L hLb hLu hLs
  have hread : ∀ q : PIdx j keep, pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2 =
      L q.1.1.1 q.1.1.2.1 q.1.1.2.2 := by
    intro q
    obtain ⟨hk1, hp1, hb1, ha1, hc1⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads Ψ N j keep q hjN
    obtain ⟨-, hc3⟩ := hc1 fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2
    rw [hpm] at hc3
    obtain ⟨k, hbk⟩ := hsome (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) hp1
    obtain ⟨α, hα, -, hT⟩ := hmin (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) k hk1 hbk
    have hsup : ∀ x c, c ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) →
        x ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) → W q.1.1.1 x c = 0 :=
      fun x c hc' hx => hWs q.1.1.1 _ hk1 hp1 c hc' x hx
    obtain ⟨r1, r2⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace N (L q.1.1.1) _ _ _ (hLu _) ha1 hb1 q.1.2.1 (fun x hx hne => hc3 x hx hne)
    have e1 := MinorCalc.minorIJ_mul_of_support ((h q.1.1.1)⁻¹ * H q.1.1.1) (W q.1.1.1)
      (insert q.1.1.2.1 ((stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)).erase q.1.1.2.2)) _ hsup
    rw [hGW, r1] at e1
    have e2 := minor_mul_self (hGW q.1.1.1) (hLu _) hsup
    unfold pRead
    rw [hbk]
    show twMinor _ _ _ _ _ _ _ _ / (_ * twMinor _ _ _ _ _ _ _ _) = _
    rw [hT, hT]
    exact ratio hα e1 e2 r2
  have hLw : pL ε (pRho M Rb keep v F kb r h ε z) = fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2 :=
    funext fun q => (hLp q).trans (hread q)
  have hHw : ∀ τ, pH keep h ε τ (pRho M Rb keep v F kb r h ε z) = H τ * W τ := fun τ => by
    unfold pH
    rw [hLw, hpm, ← hGW τ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hh τ).2.isUnit]
  obtain ⟨-, hpb, hpk⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε ctx0 _ hwD
  have hbw : bl (pB ε (pRho M Rb keep v F kb r h ε z)) = zc := by rw [hB, hzc]
  rw [hbw] at hpb hpk
  generalize hφ : pPhi M F keep v bl h ε (pRho M Rb keep v F kb r h ε z) = φ at hpb hpk ⊢
  have hblock : ∀ k : Kk, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ιk k, φ ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some (κ k)
    · refine ⟨1, one_ne_zero, fun m => ?_⟩
      rw [one_mul, ← upV_apply hbm.2.1 φ, ← upV_apply hbm.2.1 z']
      have hfst : (v ⟨k, m⟩).1 = κ k := hbm.2.2.1 _
      generalize v ⟨k, m⟩ = q at hfst
      obtain ⟨k', m'⟩ := q
      obtain rfl : k' = κ k := hfst
      exact congrFun (hpb.trans hbp.symm) ⟨⟨κ k, hk⟩, m'⟩
    · obtain ⟨p, hp, hbk⟩ := ((hκ (κ k)).1 ⟨k, rfl⟩).resolve_left hk
      obtain ⟨α, hα, hw, -⟩ := hmin p (κ k) hp hbk
      have hsup : ∀ x c, c ∈ stepCols N j p.2 → x ∉ stepCols N j p.2 → W p.1 x c = 0 :=
        fun x c hc' hx => hWs p.1 p.2 hp (hproper p _ hbk) c hc' x hx
      have e2 := minor_mul_self (hGW p.1) (hLu _) hsup
      have hmw : minorIJ (W p.1) (stepCols N j p.2) (stepCols N j p.2) ≠ 0 := fun e0 => by
        simp [e0] at e2
      refine ⟨minorIJ (W p.1) (stepCols N j p.2) (stepCols N j p.2) / α, div_ne_zero hmw hα, fun m => ?_⟩
      rw [← upV_apply hbm.2.1 φ, ← upV_apply hbm.2.1 z']
      have hfst : (v ⟨k, m⟩).1 = κ k := hbm.2.2.1 _
      generalize v ⟨k, m⟩ = q at hfst
      obtain ⟨k', m'⟩ := q
      obtain rfl : k' = κ k := hfst
      rw [hpk p _ hp hbk m', hw m', hHw, div_mul_eq_mul_div, mul_left_comm _ α, mul_div_cancel_left₀ _ hα,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ hsup]
      ring
  choose t ht1 ht2 using hblock
  have o1 : SameOrbit φ z' := ⟨t, ht1, funext fun q => ht2 q.1 q.2⟩
  exact orbit_trans o1 ⟨c, hc, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjection
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

open GroundTheory.Heights₂.Heights.ComplexSets

theorem setChartIdeal_le_chartIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i) :
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal S σ Ψ ≤ GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal S σ i := by
  have hset : GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet S σ Ψ = GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet S σ i := by
    ext x
    simp only [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet, hΨ0]
  rw [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal, hset]

theorem chartProj_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  intro K _ _ ι _ Q e m σ i Ψ hQ hΨ hΨ0 hdim J hJ
  have hJm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cone_pow_mem hR hΨ
        ((setChartIdeal_le_chartIdeal hΨ0).trans hJm.1.2) a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ hJm.1.1 (hdim J hJ) hfin, hfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartComponentsFiniteProjectionStatement
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartComponents_finite_projection : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSheetSimpleNull
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimpleOfCount
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory Filter Topology Matrix SheetLift CxInt
open ReciprocityTheory.ChartRestriction.G.Geo (segre_differentiableAt)

section Count

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cone_lift_spec [DecidableEq K] {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    (i0 : (k : K) → ι k) (k0 : K) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) (hne : segre z i0 ≠ 0) :
    lift i0 k0 (segre z) ∈ conePts Q ∧ segre (lift i0 k0 (segre z)) = segre z := by
  have h0 : ∀ k, z ⟨k, i0 k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp hne) k (Finset.mem_univ k)
  rw [lift_segre i0 k0 hne]
  refine ⟨cone_scale hP (c := fun k => (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩)
    (fun k => div_ne_zero (by split_ifs <;> simp [hne]) (h0 k)) hz, ?_⟩
  have hprod : ∏ k, (if k = k0 then segre z i0 else 1) / z ⟨k, i0 k⟩ = 1 := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_eq' Finset.univ k0, if_pos (Finset.mem_univ _)]
    exact div_self hne
  rw [segre_bsmul, hprod]
  funext i
  rw [one_mul]

theorem cone_sheetLift {Q : Ideal (MRingOver ℂ ι)} (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ)
    (h : (Fin e → ℂ) → ((k : K) → ι k) → ℂ)
    (hev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h y' ∧ (∃ z ∈ conePts Q, segre z = h y') ∧
      Ψ (h y') = Fin.cons 1 y') :
    ∃ γ, IsSetSheet (conePts Q) Ψ y (h y) γ := by
  classical
  obtain ⟨hd0, ⟨z0, hz0, hs0⟩, -⟩ := hev.self_of_nhds
  rcases isEmpty_or_nonempty K with hK | ⟨⟨k0⟩⟩
  · refine ⟨fun _ => z0, hs0, hev.mono fun y' ⟨_, ⟨z, hz, hs⟩, hΨ⟩ => ?_⟩
    have hzz : z0 = z := funext fun p => (IsEmpty.false p.1).elim
    refine ⟨differentiableAt_const _, hzz ▸ hz, ?_⟩
    show Ψ (segre z0) = _
    rw [hzz, hs]
    exact hΨ
  · choose i0 hi0 using hz0.1
    have hy : h y i0 ≠ 0 := by
      rw [← hs0]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hi0 k
    have hnear : ∀ᶠ y' in 𝓝 y, h y' i0 ≠ 0 :=
      (differentiableAt_pi.mp hd0 i0).continuousAt.eventually_ne hy
    refine ⟨fun y' => lift i0 k0 (h y'), ?_, (hev.and hnear).mono fun y' ⟨⟨hd, ⟨z, hz, hs⟩, hΨ⟩, hne⟩ => ?_⟩
    · show segre (lift i0 k0 (h y)) = h y
      rw [← hs0]
      exact (cone_lift_spec hP i0 k0 hz0 (hs0 ▸ hy)).2
    · have hne' : segre z i0 ≠ 0 := hs ▸ hne
      obtain ⟨h1, h2⟩ := cone_lift_spec hP i0 k0 hz hne'
      refine ⟨differentiableAt_lift i0 k0 hd hne, ?_, ?_⟩
      · show lift i0 k0 (h y') ∈ conePts Q
        rw [← hs]
        exact h1
      · show Ψ (segre (lift i0 k0 (h y'))) = _
        rw [← hs, h2, hs]
        exact hΨ

theorem mem_setFibre_iff {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (y : Fin e → ℂ) (x : Fin m → ℂ) :
    (fun i' => x (σ.symm i')) ∈ setFibre S Ψ y ↔
      x ∈ setChartSet S σ Ψ ∧ chartProjMatrix σ Ψ *ᵥ x = y := by
  constructor
  · rintro ⟨z, hz, hzw, hΨ⟩
    have hx : x = fun a => segre z (σ a) := by
      funext a
      rw [hzw]
      simp
    refine ⟨⟨z, hz, by rw [hzw, hΨ]; rfl, hx⟩, ?_⟩
    funext r
    rw [chartProjMatrix_mulVec, hΨ]
    rfl
  · rintro ⟨⟨z, hz, h0, rfl⟩, hA⟩
    have hw : (fun i' => segre z (σ (σ.symm i'))) = segre z := by
      funext i'
      simp
    refine ⟨z, hz, hw.symm, ?_⟩
    rw [hw]
    funext j
    refine Fin.cases ?_ (fun r => ?_) j
    · rw [h0]
      rfl
    · have h := congrFun hA r
      rw [chartProjMatrix_mulVec, hw] at h
      rw [h]
      rfl

theorem cxGenericCount {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} (hQ : IsCxVar Q e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsSetGoodProj (conePts Q) Ψ) :
    ∃ d : ℕ, (∀ y, (setFibre (conePts Q) Ψ y).encard ≤ d) ∧
      volume {y : Fin e → ℂ | ¬ ((setFibre (conePts Q) Ψ y).encard = d ∧
        ∀ w ∈ setFibre (conePts Q) Ψ y, ∃ γ, IsSetSheet (conePts Q) Ψ y w γ)} = 0 := by
  classical
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  set σ := (Fintype.equivFin ((k : K) → ι k)).symm
  obtain ⟨hZ, hJ⟩ := cxChartModel hQ σ Ψ hΨ
  set I := setChartIdeal (conePts Q) σ Ψ
  set F := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).toFinset
  set A := chartProjMatrix σ Ψ
  have hF : ∀ J, J ∈ F ↔ J ∈ I.minimalPrimes := fun J => Set.Finite.mem_toFinset _

  have hU : ∀ x, (∃ J ∈ F, x ∈ zeroSet J) ↔ x ∈ setChartSet (conePts Q) σ Ψ := by
    intro x
    rw [← hZ]
    constructor
    · rintro ⟨J, hJF, hx⟩ q hq
      exact hx q (((hF J).1 hJF).1.2 hq)
    · intro hx
      have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => RingHom.mem_ker.2 (hx q hq)
      have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨J, hJm, hJle⟩ := Ideal.exists_minimalPrimes_le hle
      exact ⟨J, (hF J).2 hJm, fun q hq => RingHom.mem_ker.1 (hJle hq)⟩
  obtain ⟨hle, Δ, hΔ, hgen⟩ := ComponentsGenericCount.proof _ e F A
    (fun J hJF => ⟨((hF J).1 hJF).1.1, hJ J ((hF J).1 hJF)⟩)
    (fun J hJF J' hJ'F hJJ' => le_antisymm hJJ' (((hF J').1 hJ'F).2 ((hF J).1 hJF).1 hJJ'))

  have hfib : ∀ y, setFibre (conePts Q) Ψ y = (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) ''
      {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y} := by
    intro y
    ext w
    constructor
    · intro hw
      have hw' : (fun i' => (fun a => w (σ a)) (σ.symm i')) = w := by
        funext i'
        simp
      rw [← hw'] at hw
      obtain ⟨hxS, hxA⟩ := (mem_setFibre_iff σ Ψ y (fun a => w (σ a))).1 hw
      exact ⟨_, ⟨(hU _).2 hxS, hxA⟩, hw'⟩
    · rintro ⟨x, ⟨hxU, hxA⟩, rfl⟩
      exact (mem_setFibre_iff σ Ψ y x).2 ⟨(hU x).1 hxU, hxA⟩
  have hinj : Function.Injective (fun x : Fin _ → ℂ => fun i' => x (σ.symm i')) := by
    intro x x' h
    funext a
    simpa using congrFun h (σ a)
  have henc : ∀ y, (setFibre (conePts Q) Ψ y).encard = {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard :=
    fun y => by rw [hfib y, hinj.injOn.encard_image]
  refine ⟨∑ J ∈ F, projDegree J A, fun y => (henc y).trans_le (hle y), ?_⟩
  refine measure_mono_null (fun y hy => ?_) (DiscriminantSheetCover.volume_zero_set Δ hΔ)
  by_contra h0
  obtain ⟨hcount, hsec⟩ := hgen y h0
  refine hy ⟨(henc y).trans hcount, fun w hw => ?_⟩
  rw [hfib y] at hw
  obtain ⟨x, ⟨hxU, hxA⟩, rfl⟩ := hw
  obtain ⟨U, g, hUo, hyU, hg, hgy, hgU⟩ := hsec x hxU hxA
  rw [← hgy]
  refine cone_sheetLift hR Ψ y (fun y' i' => g y' (σ.symm i')) ?_
  filter_upwards [hUo.mem_nhds hyU] with y' hy'
  obtain ⟨hAg, J, hJF, hgJ⟩ := hgU y' hy'
  obtain ⟨z, hz, hzw, hΨz⟩ := (mem_setFibre_iff σ Ψ y' (g y')).2 ⟨(hU _).1 ⟨J, hJF, hgJ⟩, hAg⟩
  have hgd : DifferentiableAt ℂ g y' := hg.differentiableAt (hUo.mem_nhds hy')
  exact ⟨differentiableAt_pi.2 fun i' => differentiableAt_pi.1 hgd (σ.symm i'), ⟨z, hz, hzw⟩, hΨz⟩

theorem cxSimple_of_count {S : Set ((Σ k, ι k) → ℂ)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (setFibre S Ψ y').encard ≤ d) (hy : (setFibre S Ψ y).encard = d)
    (hsh : ∀ w ∈ setFibre S Ψ y, ∃ γ, IsSetSheet S Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ setFibre S Ψ y) : CxComp.cxSimple S Ψ w := by
  have hF : (setFibre S Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ setFibre S Ψ y,
      (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ setFibre S Ψ y, (γ a y' ∈ S ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → setFibre S Ψ y' = (fun a => segre (γ a y')) '' setFibre S Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (setFibre S Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' setFibre S Ψ y ⊆ setFibre S Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

end Count

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end
