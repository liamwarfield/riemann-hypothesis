module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSeventh

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsParabolicTransvection
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.Parab

def IsParabolic {N : ℕ} (ca cb : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b, b < a → ¬ (a = cb ∧ b = ca) → M a b = 0

theorem IsParabolic.mul {N : ℕ} {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsParabolic ca cb A) (hB : IsParabolic ca cb B) :
    IsParabolic ca cb (A * B) := by
  intro a b hba hne
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : c < a ∧ ¬ (a = cb ∧ c = ca)
  · rw [hA a c h1.1 h1.2, zero_mul]
  by_cases h2 : b < c ∧ ¬ (c = cb ∧ b = ca)
  · rw [hB c b h2.1 h2.2, mul_zero]
  exfalso
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

theorem isParabolic_of_upper {N : ℕ} (ca cb : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.BlockTriangular id) : IsParabolic ca cb M := fun _ _ h _ => hM h

theorem isParabolic_transvection {N : ℕ} (ca cb : Fin N) (t : ℂ) :
    IsParabolic ca cb (1 + Matrix.single cb ca t) := by
  intro a b hba hne
  rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]
  intro h
  exact hne ⟨h.1.symm, h.2.symm⟩

theorem eq_transvection {N : ℕ} {ca cb : Fin N} {Y : Matrix (Fin N) (Fin N) ℂ} (hne : cb ≠ ca)
    (hlt : ca < cb) (hY : IsLowerUni Y) (hP : IsParabolic ca cb Y) :
    Y = 1 + Matrix.single cb ca (Y cb ca) := by
  ext a b
  rw [Matrix.add_apply]
  by_cases e : a = cb ∧ b = ca
  · obtain ⟨rfl, rfl⟩ := e
    rw [Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
  · have hs : Matrix.single cb ca (Y cb ca) a b = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)
    rw [hs, add_zero]
    rcases lt_trichotomy a b with h | h | h
    · rw [hY.2 a b h, Matrix.one_apply_ne h.ne]
    · subst h
      rw [hY.1 a, Matrix.one_apply_eq]
    · rw [hP a b h e, Matrix.one_apply_ne h.ne']

theorem mul_transvection_eq : ∀ (N : ℕ) (h B₀ B₁ : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ),
    (cb : ℕ) = ca + 1 → B₀.BlockTriangular id → B₁.BlockTriangular id → B₀.det ≠ 0 → B₁.det ≠ 0 →
    IsLowerUni (h * B₀) → IsLowerUni (h * (1 + Matrix.single cb ca t) * B₁) →
    ∃ y : ℂ, h * (1 + Matrix.single cb ca t) * B₁ = h * B₀ * (1 + Matrix.single cb ca y) := by
  intro N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1
  have hlt : ca < cb := by simp only [Fin.lt_def]; omega
  have hL0 : IsUnit (h * B₀).det := by rw [L0.det]; exact isUnit_one
  have hB0 : IsUnit B₀.det := isUnit_iff_ne_zero.mpr d0
  letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0
  letI := Matrix.invertibleOfIsUnitDet B₀ hB0
  set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE
  set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef
  have hY : h * B₀ * Y = h * E * B₁ := by
    rw [hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]
  have low : Y.BlockTriangular OrderDual.toDual := by
    have e1 : (h * B₀).BlockTriangular OrderDual.toDual := fun a b e => L0.2 _ _ e
    have e2 : (h * E * B₁).BlockTriangular OrderDual.toDual := fun a b e => L1.2 _ _ e
    have := (blockTriangular_inv_of_blockTriangular e1).mul e2
    rwa [← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0] at this
  have hYl : IsLowerUni Y := by
    refine ⟨fun a => ?_, fun a b e => low e⟩
    have := L1.1 a
    rw [← hY, Matrix.mul_apply, Finset.sum_eq_single a
      (fun c _ hc' => by
        rcases lt_or_gt_of_ne hc' with e | e
        · rw [low e, mul_zero]
        · rw [L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul] at this
    exact this
  have hP : IsParabolic ca cb Y :=
    (isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc
      ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))
  exact ⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩

end GlobalTheory.CompanionTheory.Ar.PB.Parab
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_fstPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem orbit_sndPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, if_neg hk]

end Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem orbit_wVec_mul (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h B₀ : Ψ → Matrix (Fin N) (Fin N) ℂ) (B₁ : Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (t s : ℂ) (hB₀ : ∀ τ', IsBlockDiag j (B₀ τ') ∧ (B₀ τ').BlockTriangular id ∧ (B₀ τ').det ≠ 0)
    (hd : IsBlockDiag j B₁) (ht : B₁.BlockTriangular id) (hdet : B₁.det ≠ 0)
    (e : h τ * (1 + Matrix.single cb ca t) * B₁ = h τ * B₀ τ * (1 + Matrix.single cb ca s)) :
    SameOrbit (wVec M F b (fun τ' => h τ' * B₀ τ') τ a k₀ ca cb s) (wVec M F b h τ a k₀ ca cb t) := by
  obtain ⟨c, hc, hcz⟩ := sameOrbit_flagPt_mul K ι Φ y Ψ N j M F b h B₀ hB₀
  have hne : ∏ i ∈ stepCols N j a, B₁ i i ≠ 0 := by
    rw [Matrix.det_of_upperTriangular ht] at hdet
    exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  refine ⟨fun o => o.elim (∏ i ∈ stepCols N j a, B₁ i i) c, ?_, ?_⟩
  · rintro (_ | k)
    · exact hne
    · exact hc k
  · funext p
    obtain ⟨o, m⟩ := p
    cases o with
    | none =>
      simp only [wVec, Option.elim_none]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← e, (MinorCalc.minors_main ℂ N j a M.j_le).2.2.1 _ B₁ I hd ht]
      ring
    | some k =>
      exact congrFun hcz ⟨k, m⟩

theorem minor_ne_zero_of_plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    (b : (Σ k, baseIdx ι M.blk k) → ℂ) (hF : M.IsFrame F) (hb : b ∈ mcPts (mCoordIdeal M.x))
    (hG : M.GoodAt F (mCoordIdeal b)) (g : Ψ → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ τ', IsBlockDiag j (g τ'))
    (hp : ∀ p, plk M F b (flagPt M F b g) p ≠ 0) (τ' : Ψ) (i : Fin N) (hi : IsProperStep N j i) :
    minorIJ (g τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have e := plk_flagPt K ι Φ y Ψ N j M F b g (τ', i) k hF hb hG hg hk
  have := hp (τ', i)
  rwa [e] at this

theorem vector_of_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk hca hcb RW q hq h0 h1 hinj l x hO hp0 hp1
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  obtain ⟨x₀, hx₀⟩ := (re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 x)
  have hz := RW.mem x x (RW.mem_U x)
  have hbase : SameOrbit (basePart M.blk (fstPt k₀ (RW.lift x x)))
      (BM.Rb.lift (FA.pr (q 0 x)) (FA.pr (q 0 x))) := by
    have e1 := orbit_basePart M.blk (h0 x x₀ hx₀)
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm e1) e2
  obtain ⟨h, t, hh, ho⟩ := GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hk hca hcb FA.Re.arith l _ hO _
    hz hbase
  obtain ⟨hbv, hgood, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l _ hO
  obtain ⟨hw0, hw1⟩ := fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hk hca hcb (BM.F l)
    (bvec BM l (FA.pr (q 0 x))) h t
  have hf := orbit_fstPt ho
  have hg := orbit_sndPt ho
  rw [hw0] at hf
  rw [hw1] at hg
  have hE : IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
    intro r s hrs
    have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
    have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hrs hs.symm
    rw [Matrix.add_apply, e1, e2, add_zero]
  have hEdet : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
    refine (Matrix.det_of_lowerTriangular _ fun r s hrs => ?_).trans (Finset.prod_eq_one fun r _ => ?_)
    · have e1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne (ne_of_lt (show r < s from hrs))
      have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlt hrs
      rw [Matrix.add_apply, e1, e2, add_zero]
    · have e2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r r = 0 := by
        rw [Matrix.single_apply, if_neg]
        rintro ⟨rfl, h'⟩
        exact hlt.ne h'
      rw [Matrix.add_apply, e2, add_zero, Matrix.one_apply_eq]
  have hbd₁ : IsBlockDiag j (h τ * (1 + Matrix.single cb ca t)) :=
    ((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ).1 hE).1
  have hdet₁ : (h τ * (1 + Matrix.single cb ca t)).det ≠ 0 := by
    rw [Matrix.det_mul, hEdet, mul_one]
    exact (hh τ).2
  have hbdU : ∀ τ', IsBlockDiag j (Function.update h τ (h τ * (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact hbd₁
    · rw [Function.update_of_ne e]
      exact (hh τ').1
  have m0 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood h (fun τ' => (hh τ').1)
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hf).1 (hp0 p))
  have m1 := minor_ne_zero_of_plk M (BM.F l) _ (BM.isFrame l) hbv hgood _ hbdU
    (fun p => (plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hg).1 (hp1 p)) τ
  rw [Function.update_self] at m1
  choose B₀ hd₀ ht₀ hdet₀ hu₀ using fun τ' =>
    BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (m0 τ')
  obtain ⟨B₁, hd₁, ht₁, hdetB₁, hu₁⟩ := BigCell.exists_upper_of_minors N j _ M.j_le hbd₁ hdet₁ m1
  obtain ⟨s, es⟩ := Parab.mul_transvection_eq N (h τ) (B₀ τ) B₁ ca cb t hcb (ht₀ τ) ht₁ (hdet₀ τ) hdetB₁ (hu₀ τ) hu₁
  obtain ⟨c, a₀, hL⟩ := (LcFam.lc_main Ψ N j τ ca cb hlt hs.symm).2.2.1 (fun τ' => h τ' * B₀ τ') fun τ' =>
    ⟨((MinorCalc.minors_main ℂ N j a M.j_le).2.2.2 _ _ (hh τ').1 (hd₀ τ')).1, hu₀ τ'⟩
  refine ⟨c, a₀, a₀ + s, ?_⟩
  rw [hL, add_sub_cancel_left]
  exact orbit_trans ho (orbit_symm (orbit_wVec_mul M (BM.F l) _ h B₀ B₁ τ a k₀ ca cb t s
    (fun τ' => ⟨hd₀ τ', ht₀ τ', hdet₀ τ'⟩) hd₁ ht₁ hdetB₁ es))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_fourth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (fstPt k₀ (RW.lift x x)) p ≠ 0) → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (sndPt k₀ (RW.lift x x)) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a₀ a₁ : ℂ), SameOrbit (RW.lift x x) (FC.wVec M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x))) (FC.Lca τ ca cb c a₀) τ a k₀ ca cb (a₁ - a₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Cell.vector_of_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d)
    (τ : Ψ) (ca cb : Fin N) (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (l : Fin BM.q)
    (x₀ : FA.Re.R.X) (hO : FA.pr (FA.Re.π x₀) ∈ BM.O l)
    (hplk : ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀)
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  have hz : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  obtain ⟨h, hh, horb⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l _ hO _ hz (FA.pr_eq x₀)
  obtain ⟨hbm, hbg, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l _ hO
  have hmin : ∀ τ' (i : Fin N), IsProperStep N j i →
      minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    have h1 := (GlobalTheory.T.plucker_nonvanishing_orbit_invariant K ι Φ y Ψ N j M (BM.F l) _ _ _ (τ', i) horb).1 (hplk (τ', i))
    rwa [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h (τ', i) k (BM.isFrame l) hbm hbg
      (fun τ'' => (hh τ'').1) hk] at h1
  choose B hBd hBt hBdet hBL using fun τ' =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (hmin τ')
  obtain ⟨-, -, hlc, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main Ψ N j τ ca cb hab hblk
  have hL : ∀ τ', IsBlockDiag j (h τ' * B τ') ∧ IsLowerUni (h τ' * B τ') := by
    intro τ'
    refine ⟨fun r s hrs => ?_, hBL τ'⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : ((r : ℕ) < N - j ↔ (t : ℕ) < N - j)
    · rw [hBd τ' t s (fun e => hrs (ht.trans e)), mul_zero]
    · rw [(hh τ').1 r t ht, zero_mul]
  obtain ⟨c, a, e⟩ := hlc _ hL
  refine ⟨c, a, ?_⟩
  rw [e]
  exact orbit_trans horb (orbit_symm
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul K ι Φ y Ψ N j M (BM.F l) _ h B fun τ' => ⟨hBd τ', hBt τ', hBdet τ'⟩))
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwapStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_plucker_column_swap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (ca cb : Fin N), ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → ∀ (l : Fin BM.q) (x₀ : FA.Re.R.X), FA.pr (FA.Re.π x₀) ∈ BM.O l → (∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) → ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEquality
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEquality
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

section Minors

variable {N : ℕ}

theorem minor_self_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (C : Finset (Fin N)) :
    minorIJ L C C = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => hL.1 _
  · intro a b hab
    exact hL.2 _ _ ((C.orderEmbOfFin rfl).strictMono hab)

theorem minor_insert_of_lowerUni {L : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) {C : Finset (Fin N)} {s r : Fin N}
    (hs : s ∈ C) (hmax : ∀ a ∈ C, a ≤ s) (hr : s < r) : minorIJ L (insert r (C.erase s)) C = L r s := by
  have hrn : r ∉ C.erase s := fun h => absurd (hmax r (Finset.mem_of_mem_erase h)) (not_le.2 hr)
  have hcard : (insert r (C.erase s)).card = C.card := by
    rw [Finset.card_insert_of_notMem hrn, Finset.card_erase_of_mem hs]
    have := Finset.card_pos.2 ⟨s, hs⟩
    omega
  unfold minorIJ
  rw [dite_eq_left hcard]
  set e := C.orderEmbOfFin rfl with he
  have hmem : ∀ i, e i ∈ C := fun i => Finset.orderEmbOfFin_mem C rfl i
  obtain ⟨m, hm⟩ : ∃ m, e m = s := by
    have : s ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hs
    exact this
  have hle : ∀ i, i ≤ m := fun i => e.le_iff_le.1 (by rw [hm]; exact hmax _ (hmem i))
  let f : Fin C.card → Fin N := fun i => if i = m then r else e i
  have hf_ne : ∀ i, i ≠ m → f i = e i := fun i h => if_neg h
  have hf_m : f m = r := if_pos rfl
  have hmono : StrictMono f := by
    intro a b hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab)
    rw [hf_ne a ham]
    by_cases hb : b = m
    · rw [hb, hf_m]
      exact lt_of_le_of_lt (hmax _ (hmem a)) hr
    · rw [hf_ne b hb]
      exact e.strictMono hab
  have hin : ∀ i, f i ∈ insert r (C.erase s) := by
    intro i
    by_cases hi : i = m
    · rw [hi, hf_m]
      exact Finset.mem_insert_self _ _
    · rw [hf_ne i hi]
      refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => hi ?_, hmem i⟩)
      exact e.injective (h.trans hm.symm)
  have hfe : f = (insert r (C.erase s)).orderEmbOfFin hcard := Finset.orderEmbOfFin_unique hcard hin hmono
  rw [← hfe, Matrix.det_of_lowerTriangular]
  · rw [Finset.prod_eq_single m]
    · rw [Matrix.submatrix_apply, hf_m, hm]
    · intro i _ hi
      rw [Matrix.submatrix_apply, hf_ne i hi]
      exact hL.1 _
    · intro h
      exact absurd (Finset.mem_univ m) h
  · intro a b hab
    have hab' : a < b := hab
    have ham : a ≠ m := fun h => absurd (hle b) (by rw [← h]; exact not_le.2 hab')
    rw [Matrix.submatrix_apply, hf_ne a ham]
    exact hL.2 _ _ (e.strictMono hab')

end Minors

theorem flag_uniq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb L L' hL hL' ho
  obtain ⟨hβ, hg, -, -⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  obtain ⟨c, -, ez⟩ := ho
  have hjN := M.j_le
  have key : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → ∃ a : ℂ, ∀ I,
      minorIJ (L τ') I (stepCols N j i) = a * minorIJ (L' τ') I (stepCols N j i) := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    refine ⟨c k, fun I => ?_⟩
    have h0 := FibreCount.plucker_inj M (BM.isFrame l) hβ hg hk
      (fun I => minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i))
      (fun I hI => by
        show minorIJ (L τ') I (stepCols N j i) - c k * minorIJ (L' τ') I (stepCols N j i) = 0
        rw [FibreCount.minor_off_step hjN hi (hL τ').1 hI, FibreCount.minor_off_step hjN hi (hL' τ').1 hI]
        ring)
      (fun m => by
        have x := congrFun ez ⟨k, m⟩
        simp only at x
        rw [flagPt_step M (BM.F l) _ L hk m, flagPt_step M (BM.F l) _ L' hk m] at x
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [x, Finset.mul_sum, sub_eq_zero]
        exact Finset.sum_congr rfl fun _ _ => by ring) I
    exact sub_eq_zero.1 h0
  have ent : ∀ (τ' : Ψ) (i : Fin N) (s r : Fin N), IsProperStep N j i → s ∈ stepCols N j i →
      (∀ a ∈ stepCols N j i, a ≤ s) → s < r → L τ' r s = L' τ' r s := by
    intro τ' i s r hi hs hmax hr
    obtain ⟨a, ha⟩ := key τ' i hi
    have h1 := ha (stepCols N j i)
    rw [minor_self_of_lowerUni (hL τ').2, minor_self_of_lowerUni (hL' τ').2, mul_one] at h1
    have h2 := ha (insert r ((stepCols N j i).erase s))
    rw [minor_insert_of_lowerUni (hL τ').2 hs hmax hr, minor_insert_of_lowerUni (hL' τ').2 hs hmax hr, ← h1,
      one_mul] at h2
    exact h2
  funext τ'
  ext r s
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hsr' : (s : ℕ) < r := hsr
    by_cases hblk : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · by_cases hs : (s : ℕ) < N - j
      · have hr : (r : ℕ) < N - j := hblk.2 hs
        refine ent τ' ⟨s + j, by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_neg (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_neg (by omega)] at ha
          exact Fin.le_def.2 (by omega)
      · have hr : ¬ (r : ℕ) < N - j := fun h => hs (hblk.1 h)
        have hrN := r.2
        refine ent τ' ⟨s - (N - j), by omega⟩ s r ⟨by simp only; omega, by simp only; omega⟩ ?_ ?_ hsr
        · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [if_pos (by omega)]
          omega
        · intro a ha
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [if_pos (by omega)] at ha
          exact Fin.le_def.2 (by omega)
    · rw [(hL τ').1 r s hblk, (hL' τ').1 r s hblk]
  · rw [hsr, (hL τ').2.1, (hL' τ').2.1]
  · rw [(hL τ').2.2 r s hsr, (hL' τ').2.2 r s hsr]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEqualityStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_unipotent_orbit_equality : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ L L' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (L τ') ∧ IsLowerUni (L τ')) → (∀ τ', IsBlockDiag j (L' τ') ∧ IsLowerUni (L' τ')) → SameOrbit (FC.flagPt M (BM.F l) (FC.bvec BM l b) L) (FC.flagPt M (BM.F l) (FC.bvec BM l b) L') → L = L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flag_uniq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquiv
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord

theorem nat_card_cIdx (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (ca cb : Fin N) (hj : j ≤ N)
    (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) :
    Nat.card (FC.CIdx Ψ N j τ ca cb) + 1 = Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : LowIdx Ψ N j, q0.1 = (τ, cb, ca) := ⟨⟨(τ, cb, ca), hab, hblk⟩, rfl⟩
  have e : FC.CIdx Ψ N j τ ca cb ≃ {q : LowIdx Ψ N j // q ≠ q0} :=
    Equiv.subtypeEquivRight (fun q => by
      show q.1 ≠ (τ, cb, ca) ↔ q ≠ q0
      rw [← hq0]
      exact not_congr Subtype.ext_iff.symm)
  have h1 : Nat.card (Option {q : LowIdx Ψ N j // q ≠ q0}) = Nat.card (LowIdx Ψ N j) :=
    Nat.card_congr (Equiv.optionSubtypeNe q0)
  rw [Nat.card_eq_fintype_card, Fintype.card_option] at h1
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, h1, Nat.card_eq_fintype_card]
  convert GlobalTheory.CompanionTheory.Ar.PB.WMan.ChartCount.card_lowIdx Ψ N j hj

theorem nonempty_equiv_cIdx : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N →
    ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) →
    d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) →
    Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  intro Ψ _ _ N j n d τ ca cb hj hab hblk hd
  have h := nat_card_cIdx Ψ N j τ ca cb hj hab hblk
  apply Finite.card_eq.1
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin d), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
  omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquivStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_dimension_complement_equiv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n d : ℕ) (τ : Ψ) (ca cb : Fin N), j ≤ N → ca < cb → ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → Nonempty (Fin d ≃ Fin n ⊕ FC.CIdx Ψ N j τ ca cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.Coord.nonempty_equiv_cIdx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMap
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullImage

theorem isNull_image_of_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y),
    HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  intro e X Y _ _ A B h Z hh hZ k
  have key : ∀ j, volume ((A.chart k ∘ h ∘ (B.chart j).symm) ''
      (((B.chart j).target ∩ (B.chart j).symm ⁻¹' Z) ∩
        ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)))) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null Set.inter_subset_left (hZ j))
    intro z hz
    exact (((hh.2 j k z hz.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt)
  refine measure_mono_null ?_ (measure_iUnion_null key)
  rintro w ⟨hw, y, hy, hyw⟩
  obtain ⟨j, hj⟩ := B.cover y
  have hsymm : (B.chart j).symm (B.chart j y) = y := (B.chart j).left_inv hj
  have hsrc : h y ∈ (A.chart k).source := by
    rw [hyw]
    exact (A.chart k).map_target hw
  refine Set.mem_iUnion.2 ⟨j, B.chart j y, ⟨⟨(B.chart j).map_source hj, ?_⟩,
    ⟨(B.chart j).map_source hj, ?_⟩⟩, ?_⟩
  · simpa [hsymm] using hy
  · simpa [hsymm] using hsrc
  · simp only [Function.comp_apply, hsymm, hyw]
    exact (A.chart k).right_inv hw

end GlobalTheory.CompanionTheory.Ar.PB.NullImage
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMapStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_set_image_under_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y), HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | exact GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimension
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC


set_option maxHeartbeats 4000000 in
theorem fibre_charts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∃ (U B : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) ∧ (∀ m, MeasurableSet (B m) ∧ B m ⊆ U m) ∧ IsParamCover FA.S.A (fun m => {z | Fin.tail z ∈ U m}) (fun m => {z | Fin.tail z ∈ B m}) ΦY ∧ IsParamCover RW.A (fun m => {z | Fin.tail (Fin.tail z) ∈ U m}) (fun m => {z | Fin.tail (Fin.tail z) ∈ B m}) ΦW ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ΦY m z ∉ bdry FA.S.s) ∧ ∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq h0 h1 hinj
  have hj := M.j_le
  have hbN := b.2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hblk : ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
    unfold lastCol at hca
    split_ifs at hca <;> omega
  obtain ⟨e⟩ := GlobalTheory.T.flag_dimension_complement_equiv Ψ N j n d τ ca cb hj hlt hblk hdim
  obtain ⟨lc1, lc2, lc3, lc4, lc5⟩ := GlobalTheory.T.lower_unipotent_family_analytic Ψ N j τ ca cb hlt hblk
  haveI hSne := GlobalTheory.T.flag_analytic_space_nonempty K ι Φ y Ψ N j M n d BM FA
  haveI hWne := GlobalTheory.T.flag_adjacent_twisted_resolution_third K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW
  have hpi := GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA
  have hgood := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM
  have hnot : ∀ z : (Σ k, ι k) → ℂ, z ∉ mcPts FA.Re.J := fun z => by
    rw [FA.J_top]; exact GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _
  have hRinj : ∀ x x', SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x') → x = x' := fun x x' h =>
    FA.Re.R.inj x x' (hnot _) h
  have hWinj : ∀ x x', SameOrbit (RW.lift x x) (RW.lift x' x') → x = x' := fun x x' h =>
    RW.inj x x' (GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _) h
  let base : (Fin d → ℂ) → Fin n → ℂ := fun w i => w (e.symm (Sum.inl i))
  let cc : (Fin d → ℂ) → FC.CIdx Ψ N j τ ca cb → ℂ := fun w c => w (e.symm (Sum.inr c))
  let mk : (Fin n → ℂ) → (FC.CIdx Ψ N j τ ca cb → ℂ) → Fin d → ℂ := fun u c i => Sum.elim u c (e i)
  have base_mk : ∀ u c, base (mk u c) = u := fun u c => by
    funext i; simp [base, mk]
  have cc_mk : ∀ u c, cc (mk u c) = c := fun u c => by
    funext i; simp [cc, mk]
  have base_cont : Continuous base := continuous_pi fun i => continuous_apply _
  have base_an : AnalyticOnNhd ℂ base Set.univ := fun w _ =>
    AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e.symm (Sum.inl i))).analyticAt w
  have cc_an : AnalyticOnNhd ℂ cc Set.univ := fun w _ =>
    AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e.symm (Sum.inr i))).analyticAt w
  let Hh : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ' w => FC.Lc τ ca cb (cc w) τ'
  have hclosed : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ BM.Rb.A BM.L BM.s BM.sec
  have hOd : ∀ l, IsOpen (BM.O l \ bdry BM.s) := fun l => (BM.O_open l).sdiff hclosed
  let Ut : Fin BM.Rb.A.n → Fin BM.q → Set (Fin d → ℂ) := fun kb l =>
    {w | base w ∈ (BM.Rb.A.chart kb).target ∧ (BM.Rb.A.chart kb).symm (base w) ∈ BM.O l \ bdry BM.s}
  let bpt : Fin BM.Rb.A.n → (Fin d → ℂ) → BM.Rb.X := fun kb w => (BM.Rb.A.chart kb).symm (base w)
  have hUo : ∀ kb l, IsOpen (Ut kb l) := fun kb l => by
    have h1 := (BM.Rb.A.chart kb).continuousOn_symm.isOpen_inter_preimage (BM.Rb.A.chart kb).open_target (hOd l)
    exact h1.preimage base_cont
  have hbpc : ∀ kb l, ContinuousOn (bpt kb) (Ut kb l) := fun kb l =>
    (BM.Rb.A.chart kb).continuousOn_symm.comp base_cont.continuousOn fun w hw => hw.1
  have hbpa : ∀ kb l k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bpt kb) (Ut kb l ∩ bpt kb ⁻¹' (BM.Rb.A.chart k).source) :=
    fun kb l k w hw => AnalyticAt.comp (g := BM.Rb.A.chart k ∘ (BM.Rb.A.chart kb).symm) (f := base)
      (BM.Rb.A.holo kb k _ ⟨hw.1.1, hw.2⟩) (base_an w trivial)
  have hfam := fun (kb : Fin BM.Rb.A.n) (l : Fin BM.q) =>
    GlobalTheory.T.flag_adjacent_twisted_resolution_fifth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj l (Ut kb l) Hh (bpt kb) (hUo kb l)
      (fun τ' r s w _ => AnalyticAt.comp (g := fun c => FC.Lc τ ca cb c τ' r s) (f := cc) (lc2 τ' r s _ trivial) (cc_an w trivial))
      (hbpc kb l) (hbpa kb l) (fun w hw => ⟨hw.2, fun τ' => lc1 _ τ'⟩)
  choose ΦYt ΦWt hYc hYa hWc hWa hYs hWs using hfam
  obtain ⟨x₁⟩ := hSne
  obtain ⟨k₁, hk₁⟩ := BM.Rb.A.cover (FA.pr x₁)
  obtain ⟨l₁, hl₁⟩ := BM.O_cover (FA.pr x₁)
  haveI : Nonempty (Fin BM.Rb.A.n × Fin BM.q) := ⟨(k₁, l₁)⟩
  obtain ⟨tm, htm⟩ := exists_surjective_nat (Fin BM.Rb.A.n × Fin BM.q)
  let Ss : ℕ → Set BM.Rb.X := fun m => (BM.Rb.A.chart (tm m).1).source ∩ BM.O (tm m).2
  have hSo : ∀ m, IsOpen (Ss m) := fun m => (BM.Rb.A.chart (tm m).1).open_source.inter (BM.O_open _)
  let pc : ℕ → Set BM.Rb.X := fun m => Ss m \ ⋃ i ∈ Finset.range m, Ss i
  have hpc_dis : ∀ m m', m < m' → Disjoint (pc m) (pc m') := fun m m' hm =>
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hm)) hx.1)
  have hpc_cov : ∀ x, ∃ m, x ∈ pc m := fun x => by
    have hex : ∃ m, x ∈ Ss m := by
      obtain ⟨k, hk⟩ := BM.Rb.A.cover x
      obtain ⟨l, hl⟩ := BM.O_cover x
      obtain ⟨m, hm⟩ := htm (k, l)
      exact ⟨m, by simp only [Ss, hm]; exact ⟨hk, hl⟩⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, fun hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Nat.find_min hex (Finset.mem_range.1 hi) hxi
  let U : ℕ → Set (Fin d → ℂ) := fun m => Ut (tm m).1 (tm m).2
  let B : ℕ → Set (Fin d → ℂ) := fun m => U m ∩ bpt (tm m).1 ⁻¹' pc m
  have hBm : ∀ m, MeasurableSet (B m) := fun m => by
    have hpre : ∀ i, IsOpen (U m ∩ bpt (tm m).1 ⁻¹' Ss i) := fun i =>
      (hbpc _ _).isOpen_inter_preimage (hUo _ _) (hSo i)
    have : B m = (U m ∩ bpt (tm m).1 ⁻¹' Ss m) \ ⋃ i ∈ Finset.range m, (U m ∩ bpt (tm m).1 ⁻¹' Ss i) := by
      ext w
      constructor
      · rintro ⟨hU, hS, hn⟩
        exact ⟨⟨hU, hS⟩, fun h => hn (by
          obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 h
          exact Set.mem_iUnion₂.2 ⟨i, hi, hwi.2⟩)⟩
      · rintro ⟨⟨hU, hS⟩, hn⟩
        exact ⟨hU, hS, fun h => hn (by
          obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 h
          exact Set.mem_iUnion₂.2 ⟨i, hi, hU, hwi⟩)⟩
    rw [this]
    exact (hpre m).measurableSet.diff
      (Finset.measurableSet_biUnion _ fun i _ => (hpre i).measurableSet)
  let ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X := fun m => ΦYt (tm m).1 (tm m).2
  let ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X := fun m => ΦWt (tm m).1 (tm m).2
  let Gm : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun m w r s =>
    minorIJ ((Hh τ w)ᴴ * BM.G (tm m).2 τ (bpt (tm m).1 w) * Hh τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
        (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
      minorIJ ((Hh τ w)ᴴ * BM.G (tm m).2 τ (bpt (tm m).1 w) * Hh τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)
  have w_ext : ∀ w w' : Fin d → ℂ, base w = base w' → cc w = cc w' → w = w' := fun w w' h1 h2 => by
    funext i
    have hi : e.symm (e i) = i := e.symm_apply_apply i
    rcases hei : e i with u | c
    · rw [← hi, hei]; exact congrFun h1 u
    · rw [← hi, hei]; exact congrFun h2 c
  have tail1C : Continuous (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) := continuous_pi fun i => continuous_apply _
  have tail2C : Continuous (fun z : Fin (d + 2) → ℂ => (Fin.tail (Fin.tail z) : Fin d → ℂ)) :=
    continuous_pi fun i => continuous_apply _
  have hinjY : ∀ m, Set.InjOn (ΦY m) {z | Fin.tail z ∈ U m} := fun m z hz z' hz' heq => by
    have e1 : bpt (tm m).1 (Fin.tail z) = bpt (tm m).1 (Fin.tail z') := by
      rw [← (hYs _ _ z hz).1, ← (hYs _ _ z' hz').1]; exact congrArg FA.pr heq
    have e2 : base (Fin.tail z) = base (Fin.tail z') := (BM.Rb.A.chart (tm m).1).symm.injOn hz.1 hz'.1 e1
    obtain ⟨x₀, hx₀⟩ := hpi.2 (ΦY m z)
    have o1 := (hYs _ _ z hz).2 x₀ hx₀
    have o2 := (hYs _ _ z' hz').2 x₀ (hx₀.trans heq)
    rw [← e1] at o2
    have e3 := GlobalTheory.T.lower_unipotent_orbit_equality K ι Φ y Ψ N j M n BM (tm m).2 (bpt (tm m).1 (Fin.tail z)) hz.2.1
      (FC.Lca τ ca cb (cc (Fin.tail z)) (z 0)) (FC.Lca τ ca cb (cc (Fin.tail z')) (z' 0))
      (lc4 _ _) (lc4 _ _) (orbit_trans (orbit_symm o1) o2)
    obtain ⟨e4, e5⟩ := lc5 _ _ _ _ e3
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', w_ext _ _ e2 e4, e5]
  have hdisY : ∀ m m', m < m' → Disjoint (ΦY m '' {z | Fin.tail z ∈ B m}) (ΦY m' '' {z | Fin.tail z ∈ B m'}) :=
    fun m m' hm => Set.disjoint_left.2 fun x hx hx' => by
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨z', hz', heq⟩ := hx'
      have e1 := (hYs _ _ z hz.1).1
      have e2 := (hYs _ _ z' hz'.1).1
      have hb1 : FA.pr (ΦY m z) ∈ pc m := by
        show FA.pr (ΦYt _ _ z) ∈ _
        rw [e1]; exact hz.2
      have hb2 : FA.pr (ΦY m z) ∈ pc m' := by
        rw [← heq]
        show FA.pr (ΦYt _ _ z') ∈ _
        rw [e2]; exact hz'.2
      exact Set.disjoint_left.1 (hpc_dis m m' hm) hb1 hb2
  have hnull_un : ∀ {e' : ℕ} {X' : Type} [TopologicalSpace X'] (A' : FinHolAtlas e' X') (Z : Fin BM.q → Set X'),
      (∀ l, IsNull A' (Z l)) → IsNull A' (⋃ l, Z l) := fun A' Z h k => by
    rw [Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun l => h l k
  have hnull_mono : ∀ {e' : ℕ} {X' : Type} [TopologicalSpace X'] (A' : FinHolAtlas e' X') {Z Z' : Set X'},
      Z' ⊆ Z → IsNull A' Z → IsNull A' Z' := fun A' _ _ hs h k =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono hs)) (h k)
  refine ⟨U, B, Gm, ΦY, ΦW, fun m => hUo _ _, fun m => ⟨hBm m, Set.inter_subset_left⟩, ⟨fun m =>
    ⟨(hUo _ _).preimage tail1C, hYc _ _, hinjY m, hYa _ _⟩, fun m => ⟨(hBm m).preimage ?_, fun z hz => hz.1⟩, ?_, ?_⟩,
    ⟨fun m => ⟨(hUo _ _).preimage tail2C, hWc _ _, ?_, hWa _ _⟩, fun m => ⟨(hBm m).preimage ?_, fun z hz => hz.1⟩, ?_, ?_⟩,
    ?_, ?_⟩
  · exact tail1C.measurable
  · intro m m' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdisY m m' h
    · exact (hdisY m' m h).symm
  · refine hnull_mono _ ?_ (GlobalTheory.T.null_set_image_under_holoMap (d + 1) FA.S.X FA.Re.R.X FA.S.A FA.Re.R.A FA.Re.π _ FA.Re.holo
      (hnull_un _ _ (GlobalTheory.T.flag_analytic_bad_locus_null K ι Φ y Ψ N j M n d BM FA)))
    intro x hx
    obtain ⟨x₀, rfl⟩ := hpi.2 x
    obtain ⟨m, hm⟩ := hpc_cov (FA.pr (FA.Re.π x₀))
    refine ⟨x₀, Set.mem_iUnion.2 ⟨(tm m).2, hm.1.2, ?_⟩, rfl⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, a', ho⟩ := GlobalTheory.T.flag_analytic_plucker_column_swap K ι Φ y Ψ N j M n d BM FA τ ca cb hlt hblk (tm m).2 x₀ hm.1.2 hcon.2
    have hbs := hm.1.1
    let w := mk ((BM.Rb.A.chart (tm m).1) (FA.pr (FA.Re.π x₀))) c
    have hbw : bpt (tm m).1 w = FA.pr (FA.Re.π x₀) := by
      show (BM.Rb.A.chart (tm m).1).symm (base w) = _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).left_inv hbs
    have hwU : w ∈ U m := ⟨by
      show base w ∈ _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).map_source hbs, by
      show bpt (tm m).1 w ∈ _
      rw [hbw]; exact ⟨hm.1.2, hcon.1⟩⟩
    have hzt : Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
    have hz : Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) ∈ U m := by rw [hzt]; exact hwU
    obtain ⟨x₁', hx₁'⟩ := hpi.2 (ΦY m (Fin.cons a' w))
    have o := (hYs _ _ _ hz).2 x₁' hx₁'
    rw [hzt] at o
    have o' : SameOrbit (FA.Re.R.lift x₁' x₁') (FC.flagPt M (BM.F (tm m).2) (FC.bvec BM (tm m).2 (bpt (tm m).1 w))
      (FC.Lca τ ca cb (cc w) a')) := o
    rw [hbw, cc_mk] at o'
    have e1 : x₁' = x₀ := hRinj _ _ (orbit_trans o' (orbit_symm ho))
    refine hx (Set.mem_iUnion.2 ⟨m, Fin.cons a' w, ?_, by rw [← hx₁', e1]⟩)
    show Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) ∈ B m
    rw [hzt]
    refine ⟨hwU, ?_⟩
    show bpt (tm m).1 w ∈ pc m
    rw [hbw]; exact hm
  · intro z hz z' hz' heq
    have e0 := (hWs _ _ z hz).2
    have e0' := (hWs _ _ z' hz').2
    have hq0 : ΦY m (Fin.cons (z 0) (Fin.tail (Fin.tail z))) = ΦY m (Fin.cons (z' 0) (Fin.tail (Fin.tail z'))) := by
      have := congrArg (q 0) heq
      rwa [show q 0 (ΦW m z) = _ from e0.1, show q 0 (ΦW m z') = _ from e0'.1] at this
    have hq1 : ΦY m (Fin.tail z) = ΦY m (Fin.tail z') := by
      have := congrArg (q 1) heq
      rwa [show q 1 (ΦW m z) = _ from e0.2, show q 1 (ΦW m z') = _ from e0'.2] at this
    have t1 := hinjY m (x₁ := (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ))
      (x₂ := (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ))
      (by show Fin.tail (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ) ∈ U m
          rw [Fin.tail_cons]; exact hz)
      (by show Fin.tail (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ) ∈ U m
          rw [Fin.tail_cons]; exact hz') hq0
    have t2 := hinjY m (x₁ := Fin.tail z) hz hz' hq1
    have t3 : z 0 = z' 0 := by simpa using congrFun t1 0
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', t2, t3]
  · exact tail2C.measurable
  · intro m m' hne
    have key : ∀ m m', m < m' → Disjoint (ΦW m '' {z | Fin.tail (Fin.tail z) ∈ B m})
        (ΦW m' '' {z | Fin.tail (Fin.tail z) ∈ B m'}) := fun m m' hm => Set.disjoint_left.2 fun x hx hx' => by
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨z', hz', heq⟩ := hx'
      have e0 := (hWs _ _ z hz.1).2.1
      have e0' := (hWs _ _ z' hz'.1).2.1
      have hq0 : ΦY m (Fin.cons (z 0) (Fin.tail (Fin.tail z))) = ΦY m' (Fin.cons (z' 0) (Fin.tail (Fin.tail z'))) := by
        have := congrArg (q 0) heq
        rw [show q 0 (ΦW m z) = _ from e0, show q 0 (ΦW m' z') = _ from e0'] at this
        exact this.symm
      refine Set.disjoint_left.1 (hdisY m m' hm) ⟨_, ?_, rfl⟩ ⟨_, ?_, hq0.symm⟩
      · show Fin.tail (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ) ∈ B m
        rw [Fin.tail_cons]; exact hz
      · show Fin.tail (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ) ∈ B m'
        rw [Fin.tail_cons]; exact hz'
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h
    · exact (key m' m h).symm
  · refine hnull_mono _ ?_ (hnull_un _ _ (GlobalTheory.T.flag_adjacent_twisted_resolution_seventh K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj))
    intro x hx
    obtain ⟨m, hm⟩ := hpc_cov (FA.pr (q 0 x))
    refine Set.mem_iUnion.2 ⟨(tm m).2, hm.1.2, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, a₀, a₁, ho⟩ := GlobalTheory.T.flag_adjacent_twisted_resolution_fourth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj
      (tm m).2 x hm.1.2 (fun p => (hcon.2 p).1) (fun p => (hcon.2 p).2)
    have hbs := hm.1.1
    let w := mk ((BM.Rb.A.chart (tm m).1) (FA.pr (q 0 x))) c
    have hbw : bpt (tm m).1 w = FA.pr (q 0 x) := by
      show (BM.Rb.A.chart (tm m).1).symm (base w) = _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).left_inv hbs
    have hwU : w ∈ U m := ⟨by
      show base w ∈ _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).map_source hbs, by
      show bpt (tm m).1 w ∈ _
      rw [hbw]; exact ⟨hm.1.2, hcon.1⟩⟩
    let z : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ w)
    have hzt : Fin.tail (Fin.tail z) = w := by
      show Fin.tail (Fin.tail (Fin.cons a₀ (Fin.cons a₁ w) : Fin (d + 2) → ℂ)) = w
      rw [Fin.tail_cons, Fin.tail_cons]
    have hz0 : z 0 = a₀ := rfl
    have hz1 : z 1 = a₁ := rfl
    have hz : Fin.tail (Fin.tail z) ∈ U m := by rw [hzt]; exact hwU
    have o := (hWs _ _ z hz).1
    rw [hzt, hz0, hz1] at o
    have o' : SameOrbit (RW.lift (ΦW m z) (ΦW m z)) (FC.wVec M (BM.F (tm m).2) (FC.bvec BM (tm m).2 (bpt (tm m).1 w))
      (FC.Lca τ ca cb (cc w) a₀) τ a k₀ ca cb (a₁ - a₀)) := o
    rw [hbw, cc_mk] at o'
    have e1 : ΦW m z = x := hWinj _ _ (orbit_trans o' (orbit_symm ho))
    refine hx (Set.mem_iUnion.2 ⟨m, z, ?_, e1⟩)
    show Fin.tail (Fin.tail z) ∈ B m
    rw [hzt]
    refine ⟨hwU, ?_⟩
    show bpt (tm m).1 w ∈ pc m
    rw [hbw]; exact hm
  · intro m z hz hmem
    have h2 : FA.S.s (ΦY m z) (ΦY m z) = 0 := hmem
    rw [FA.s_eq] at h2
    have h3 : FA.pr (ΦY m z) ∈ bdry BM.s := h2
    have e1 : FA.pr (ΦY m z) = bpt (tm m).1 (Fin.tail z) := (hYs _ _ z hz).1
    rw [e1] at h3
    exact hz.2.2 h3
  · intro m
    refine ⟨(tm m).2, Hh, bpt (tm m).1,
      fun τ' r s w _ => AnalyticAt.comp (g := fun c => FC.Lc τ ca cb c τ' r s) (f := cc) (lc2 τ' r s _ trivial) (cc_an w trivial),
      hbpc _ _, hbpa _ _, fun w hw => ⟨hw.2, fun τ' => lc1 _ τ'⟩, fun w _ r s => rfl, fun z hz x₀ hx₀ => ?_,
      fun z hz => (hWs _ _ z hz).2⟩
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hgood (tm m).2 _ hz.2.1
    refine ⟨_, (hYs _ _ z hz).2 x₀ hx₀, ?_, fun τ' i => ?_⟩
    · rw [FC.basePart_flagPt]; exact hg4
    · have := FC.exactAt_flagPt M (BM.F (tm m).2) hg3
        (Function.update (fun τ' => Hh τ' (Fin.tail z)) τ (Hh τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)))) (τ', i)
      rw [Function.update_apply] at this
      exact this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimensionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_dimension : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∃ (U B : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) ∧ (∀ m, MeasurableSet (B m) ∧ B m ⊆ U m) ∧ IsParamCover FA.S.A (fun m => {z | Fin.tail z ∈ U m}) (fun m => {z | Fin.tail z ∈ B m}) ΦY ∧ IsParamCover RW.A (fun m => {z | Fin.tail (Fin.tail z) ∈ U m}) (fun m => {z | Fin.tail (Fin.tail z) ∈ B m}) ΦW ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ΦY m z ∉ bdry FA.S.s) ∧ ∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts <;> assumption)
end
