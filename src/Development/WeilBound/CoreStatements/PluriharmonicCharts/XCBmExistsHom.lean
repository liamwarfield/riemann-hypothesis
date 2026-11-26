module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentre
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsGram

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.RefNorm
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsValueAtZpow
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}

theorem isValueAt_zpow (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω} {v : ℂ} (h : IsValueAt x s w v) (hv : v ≠ 0)
    (n : ℤ) : IsValueAt x (s ^ n) w (v ^ n) := by
  have hs : s ≠ 0 := fun h0 => hv (isValueAt_zero hw (h0 ▸ h))
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using isValueAt_pow h m
  · simpa using isValueAt_pow (isValueAt_inv h hs hv) m

theorem isValueAt_prod {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) w (v i)) : IsValueAt x (∏ i ∈ S, f i) w (∏ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using isValueAt_one_self x w
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact isValueAt_mul (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_mon (hw : w ∈ mcPts (mCoordIdeal x)) {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    IsValueAt x ((∏ k, x ⟨k, c k⟩ ^ b k) / ∏ k, x ⟨k, c' k⟩ ^ b k) w (∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k) := by
  rw [← Finset.prod_div_distrib]
  refine isValueAt_prod _ _ _ fun k _ => ?_
  rw [← div_zpow]
  exact isValueAt_zpow hw (isValueAt_ratio (coord_ne hw (hc' k)) (hc' k)) (div_ne_zero (hc k) (hc' k)) _

theorem log_mon {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    Real.log ‖∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k‖ =
      ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ - ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c' k⟩‖ := by
  rw [norm_prod, Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_zpow, Real.log_zpow, norm_div, Real.log_div (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc' k))]
  ring

theorem ne_of_notMem {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal w) : w q ≠ 0 := fun h0 => h (by
  show mConeMap w (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem eval_conj (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (conjVec z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  exact congrArg (fun g => MvPolynomial.eval₂ g _ f) (RingHom.ext_int _ _)

theorem isValueAt_conj {s : Ω} {v : ℂ} (h : IsValueAt x s w v) : IsValueAt x s (conjVec w) (starRingEnd ℂ v) := by
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := h
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_conj]; exact (map_ne_zero _).2 hz0
  · rw [eval_conj, eval_conj, map_div₀]

theorem valAt_conj (hw : w ∈ mcPts (mCoordIdeal x)) (hw' : conjVec w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : valAt x s (conjVec w) = starRingEnd ℂ (valAt x s w) := by
  obtain ⟨v, hv⟩ := exists_isValueAt hw hs
  rw [valAt_eq hw hv, valAt_eq hw' (isValueAt_conj hv)]

end Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

theorem change_gen {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) (m : ι k) {I' : Finset (Fin N)} (hI : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
      ∑ I, F.u ⟨k, m⟩ I * minorIJ ((F.T p.1)⁻¹ * F'.T p.1) I I' =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.u ⟨k, m⟩ I' := by
  obtain ⟨h, bh, hh⟩ := exists_selector M.Ω M.j_le p.2 hI
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.1 p k hp m (R * h) (bR.mul bh)
  have e2 := hF'.2.1 p k hp m h bh
  have e3 : ∀ I, minorIJ (R * h) I (stepCols N j p.2) = minorIJ R I I' := fun I => by
    rw [minorIJ_mul]; simp [hh]
  simp only [e3] at e1
  rw [eT, detFac_mul _ bR, Matrix.mul_assoc] at e2
  simp only [hh, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem change_base {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N}
    (hp : M.blk p = none) :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * F.υ p =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.υ p := by
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.2.2 p hp
  have e2 := hF'.2.2.2 p hp
  rw [eT, detFac_mul _ bR] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem left_inv_val {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal w)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {f : Matrix (Fin N) (Fin N) ℂ} (bf : IsBlockDiag j f) {I : Finset (Fin N)}
    (hI : IsStepRows N j p.2 I) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') w * minorIJ f I' (stepCols N j p.2) =
      minorIJ f I (stepCols N j p.2) := by
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x w := fun q I => ⟨F.u q I, exists_isValueAt hw (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x w := fun I q => ⟨F.u' I q, exists_isValueAt hw (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * valAt M.x (F.u ⟨k, m⟩ I') w = if I = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I I' hI hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg (regVal hw) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e'
    simp only [map_mul] at e'
    refine e'.trans ?_
    split_ifs <;> simp
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rw [Finset.sum_eq_single I]
  · rw [rel I hI, if_pos rfl, one_mul]
  · intro I' _ hne
    by_cases h : IsStepRows N j p.2 I'
    · rw [rel I' h, if_neg hne.symm, zero_mul]
    · rw [minor_stepCols_eq_zero M.j_le f I' bf h, mul_zero]
  · simp

def Rel (Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop)
    (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (r : ℝ) : Prop :=
  ∃ F G, Gr F p.1 (basePart M.blk z) G ∧ ∃ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h ∧ h.det ≠ 0 ∧ ∃ t : ℝ,
    ((∃ k a, M.blk p = some k ∧ a ≠ 0 ∧ (∀ m : ι k, z ⟨k, m⟩ =
        a * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2)) ∧ t = Real.log ‖a‖) ∨
      (M.blk p = none ∧ t = -Real.log ‖valAt M.x (F.υ p) (basePart M.blk z)‖)) ∧
    r = t + blockPot j p.2 G h - ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖

variable {M}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem Rel.unique
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r r' : ℝ} (h1 : Rel M Gr p z r) (h2 : Rel M Gr p z r') : r = r' := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨F', G', hG', h', bh', dh', t', ht', rfl⟩ := h2
  obtain ⟨Rz, hRz, dR, rfl⟩ := hcomp _ _ _ _ _ _ hG hG'
  obtain ⟨hF, hw, gd, bG, pG⟩ := hgood _ _ _ _ hG
  obtain ⟨hF', -, gd', -, -⟩ := hgood _ _ _ _ hG'
  generalize basePart M.blk z = w at *
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd.1 k)
  have hc' : ∀ k, w ⟨k, F'.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd'.1 k)
  have hμ := isValueAt_mon hw hc hc' (M.b p)
  have lμ := log_mon hc hc' (M.b p)
  have μ0 : (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))
  have m0 : (∏ k, M.x ⟨k, F'.c k⟩ ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (coord_ne hw (hc' k))
  generalize (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) = μ at *
  let RA : Matrix (Fin N) (Fin N) (regRing M.x w) := Matrix.of fun a b => ⟨_, _, hRz a b⟩
  let μA : regRing M.x w := ⟨_, _, hμ⟩
  have eμ : regVal hw μA = μ := valAt_eq hw hμ
  have e1 : RA.map (regRing M.x w).subtype = (F.T p.1)⁻¹ * F'.T p.1 := by ext a b; rfl
  have e2 : RA.map (regVal hw) = Rz := by ext a b; exact valAt_eq hw (hRz a b)
  have bR : IsBlockDiag j Rz := by
    have : IsBlockDiag j RA := fun a b hab =>
      Subtype.ext ((((hF.1 p.1).1.inv (hF.1 p.1).2.isUnit).mul (hF'.1 p.1).1) a b hab)
    exact e2 ▸ this.map _
  rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩ <;> rcases ht' with ⟨k', a', hk', ha', hz', rfl⟩ | ⟨hk', rfl⟩
  · obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
    have hi : IsProperStep N j p.2 := by
      by_contra hn
      rw [(M.blk_none p).2 hn] at hk
      cases hk
    have ch : ∀ m I', IsStepRows N j p.2 I' → detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ Rz I I' = valAt M.x (F'.u ⟨k, m⟩ I') w := by
      intro m I' hI'
      let uA : Finset (Fin N) → regRing M.x w := fun I => ⟨F.u ⟨k, m⟩ I, exists_isValueAt hw (gd.2.1 _ I).1⟩
      let vA : regRing M.x w := ⟨F'.u ⟨k, m⟩ I', exists_isValueAt hw (gd'.2.1 _ I').1⟩
      have e : detFac j p.2 RA * μA * ∑ I, uA I * minorIJ RA I I' = vA := by
        apply (regRing M.x w).subtype_injective
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e1]
        have := change_gen M hF hF' hk m hI'
        show _ * (_ / _) * ∑ I, F.u ⟨k, m⟩ I * _ = F'.u ⟨k, m⟩ I'
        rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
      have e' := congrArg (regVal hw) e
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e2, eμ] at e'
      exact e'
    have ch2 : ∀ m, ∑ I, valAt M.x (F'.u ⟨k, m⟩ I) w * minorIJ h' I (stepCols N j p.2) = detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro m
      simp only [minorIJ_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun I' _ => ?_
      by_cases hs : IsStepRows N j p.2 I'
      · rw [← ch m I' hs, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ => by ring
      · simp [minor_stepCols_eq_zero M.j_le h' I' bh' hs]
    have fin : ∀ I, a * minorIJ h I (stepCols N j p.2) =
        a' * detFac j p.2 Rz * μ * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro I
      by_cases hs : IsStepRows N j p.2 I
      · rw [← left_inv_val M hF hw gd hk bh hs, ← left_inv_val M hF hw gd hk (bR.mul bh') hs, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have := (hz m).symm.trans (hz' m)
        rw [ch2] at this
        linear_combination (valAt M.x (F.u' I ⟨k, m⟩) w) * this
      · rw [minor_stepCols_eq_zero M.j_le h I bh hs, minor_stepCols_eq_zero M.j_le _ I (bR.mul bh') hs]
        simp
    have := pot_step M.j_le p.2 hi pG bG bR dR dh dh' ha ha' μ0 fin
    linarith
  · rw [hk] at hk'; cases hk'
  · rw [hk] at hk'; cases hk'
  · have hi := (M.blk_none p).1 hk
    obtain ⟨v, hv⟩ := exists_isValueAt hw (gd.2.2 p hk).2.1
    obtain ⟨v', hv'⟩ := exists_isValueAt hw (gd.2.2 p hk).2.2
    have v0 : v ≠ 0 := by
      have := isValueAt_mul hv hv'
      rw [mul_inv_cancel₀ (gd.2.2 p hk).1] at this
      have e := (valAt_eq hw this).symm.trans (valAt_eq hw (isValueAt_one_self M.x w))
      exact left_ne_zero_of_mul_eq_one e
    let uA : regRing M.x w := ⟨F.υ p, v, hv⟩
    let vA : regRing M.x w := ⟨F'.υ p, exists_isValueAt hw (gd'.2.2 p hk).2.1⟩
    have e : detFac j p.2 RA * μA * uA = vA := by
      apply (regRing M.x w).subtype_injective
      simp only [map_mul, ← detFac_map, e1]
      have := change_base M hF hF' hk
      show _ * (_ / _) * F.υ p = F'.υ p
      rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
    have e' := congrArg (regVal hw) e
    simp only [map_mul, ← detFac_map, e2, eμ] at e'
    have e'' : detFac j p.2 Rz * μ * v = valAt M.x (F'.υ p) w := by
      rw [← valAt_eq hw hv]; exact e'
    have d0 := detFac_ne_zero M.j_le p.2 bR dR
    rw [pot_base M.j_le p.2 hi h h' pG bG bR dR, ← e'', valAt_eq hw hv, norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)) (norm_ne_zero_iff.2 v0),
      Real.log_mul (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)]
    linarith

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem sum_dy (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 := by
  have e1 : ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 =
      ∑ k, if h : ∀ p', M.blk p' ≠ some k then (M.b p ⟨k, h⟩ : ℝ) * L k else 0 :=
    Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun k hk => dif_neg fun h => hk ⟨⟨k, h⟩, rfl⟩) (fun k => by rw [dif_pos k.2])
  have e2 : (M.blk p).elim 0 L = ∑ k, if M.blk p = some k then L k else 0 := by
    cases M.blk p with
    | none => simp
    | some k => simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold FlagModel.dy
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [dif_pos h, dif_pos h, if_neg (h p)]; simp
  · rw [dif_neg h, dif_neg h]; split_ifs <;> simp

theorem Rel.smul
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    Rel M Gr p (torusSmul c z) (r + ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖) := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := htor _ _ _ _ (fun k => c k.1) (fun k => hc _) hG
  have eb : basePart M.blk (torusSmul c z) = torusSmul (fun k => c k.1) (basePart M.blk z) := rfl
  have ev : ∀ s, valAt M.x s (basePart M.blk (torusSmul c z)) = valAt M.x s (basePart M.blk z) := fun s =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit _ _ _ M.x s _ _ (hgood _ _ _ _ hG').2.1
      ⟨fun k => c k.1, fun k => hc _, rfl⟩
  have el : ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk (torusSmul c z) ⟨k', F.c k'⟩‖ =
      ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * Real.log ‖c k'.1‖ +
        ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eb, torusSmul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 (ne_of_notMem (gd.1 k)))]
    ring
  refine ⟨F, G, hG', h, bh, dh, t + (M.blk p).elim 0 (fun k => Real.log ‖c k‖), ?_, ?_⟩
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, c k * a, hk, mul_ne_zero (hc k) ha, fun m => ?_, ?_⟩
      · simp only [ev]
        rw [torusSmul, hz m, mul_assoc]
      · rw [hk, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 ha), Option.elim_some, add_comm]
    · refine Or.inr ⟨hk, ?_⟩
      rw [hk, ev, Option.elim_none, add_zero]
  · rw [el, sum_dy]
    ring

theorem Rel.conj
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) : Rel M Gr p (conjVec z) r := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := hconj _ _ _ _ hG
  have hw' := (hgood _ _ _ _ hG').2.1
  have eb : basePart M.blk (conjVec z) = conjVec (basePart M.blk z) := rfl
  refine ⟨F, _, hG', h.map (starRingEnd ℂ), bh.map _, ?_, t, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 dh
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, starRingEnd ℂ a, hk, (map_ne_zero _).2 ha, fun m => ?_, by simp⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [conjVec, hz m, map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, eb, valAt_conj hw hw' (gd.2.1 _ I).1, minorIJ_map]
    · refine Or.inr ⟨hk, ?_⟩
      rw [eb, valAt_conj hw hw' (gd.2.2 p hk).2.1, RCLike.norm_conj]
  · rw [pot_conj]
    simp only [eb, conjVec, RCLike.norm_conj]

theorem exists_hom
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    (p : Ψ × Fin N) : ∃ A : HermLine ι, A.a = M.dy p ∧
      (∀ F w G, Gr F p.1 w G → M.IsInducedAt F w p G A) ∧ ∀ z, A.h (conjVec z) = A.h z := by
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ r, Rel M Gr p z r then Real.exp h.choose else refNorm (M.dy p) z
  have fr : ∀ z r, Rel M Gr p z r → f z = Real.exp r := fun z r h => by
    have hex : ∃ r, Rel M Gr p z r := ⟨r, h⟩
    simp only [f, dif_pos hex]
    rw [Rel.unique hgood hcomp hex.choose_spec h]
  refine ⟨⟨M.dy p, f, fun z hz => ?_, fun c z hc => ?_⟩, rfl, fun F w G hG z hz ho hn h bh dh => ?_, fun z => ?_⟩
  · simp only [f]
    split_ifs
    exacts [Real.exp_pos _, refNorm_pos _ hz]
  · change f (torusSmul c z) = _
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.smul hgood htor hc), Real.exp_add, mul_comm, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hc k)) _)]
    · have h' : ¬ ∃ r, Rel M Gr p (torusSmul c z) r := by
        rintro ⟨r, hr⟩
        have := hr.smul hgood htor (c := fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
        have e : torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
          funext q; simp [torusSmul, hc]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      exact refNorm_smul _ _ _
  · obtain ⟨c, hc, e⟩ := ho
    have hG' : Gr F p.1 (basePart M.blk z) G := by
      rw [e]; exact htor _ _ _ _ c hc hG
    refine ⟨fun k hk hz => ?_, fun hk => ?_⟩
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inl ⟨k, 1, hk, one_ne_zero, fun m => by rw [one_mul, hz m], rfl⟩, rfl⟩,
        Real.log_exp]
      simp [hn]
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inr ⟨hk, rfl⟩, rfl⟩, Real.log_exp]
      simp only [hn, norm_one, Real.log_one, mul_zero, Finset.sum_const_zero]
      ring
  · show f _ = f z
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.conj hgood hconj)]
    · have h' : ¬ ∃ r, Rel M Gr p (conjVec z) r := by
        rintro ⟨r, hr⟩
        have := hr.conj hgood hconj
        have e : conjVec (conjVec z) = z := by
          funext q; simp [conjVec]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      simp [refNorm, conjVec]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_hom

open GroundTheory.Heights₂.Heights.LowerBoundFree

section Lin

variable {R : Type} [CommRing R] {p q : ℕ}

theorem blocks_mul {A B : Matrix (Fin (p + q)) (Fin (p + q)) R} (hA : IsBlockDiag p A) (hB : IsBlockDiag p B) :
    omBlock (A * B) = omBlock A * omBlock B ∧ wBlock (A * B) = wBlock A * wBlock B := by
  have e := (hA.mul hB).eq_fromBlocks
  rw [← Matrix.submatrix_mul_equiv A B _ (blockEquiv p q) _, hA.eq_fromBlocks, hB.eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  exact ⟨by simpa using e.1.symm, by simpa using e.2.2.2.symm⟩

theorem omBlock_one : omBlock (1 : Matrix (Fin (p + q)) (Fin (p + q)) R) = 1 :=
  Matrix.submatrix_one _ (omEmb_strictMono p q).injective

theorem isBlockDiag_conjTranspose {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) :
    IsBlockDiag j Aᴴ := fun a b h => by
  rw [Matrix.conjTranspose_apply, hA b a fun e => h e.symm, star_zero]

theorem blockG_conj (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    blockG (Γ.map (starRingEnd ℂ)) = (blockG Γ).map (starRingEnd ℂ) := by
  have e : (omBlock (Γ.map (starRingEnd ℂ)))ᵀ⁻¹ = ((omBlock Γ)ᵀ⁻¹).map (starRingEnd ℂ) := by
    show ((omBlock Γ)ᵀᴴᵀ)⁻¹ = ((omBlock Γ)ᵀ⁻¹)ᴴᵀ
    rw [← Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_nonsing_inv]
  unfold blockG
  rw [e, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [Matrix.map_zero _ (map_zero (starRingEnd ℂ))]
  rfl

theorem blockG_change {Γ Γ' Rz Rz' : Matrix (Fin (p + q)) (Fin (p + q)) ℂ} (hΓ : Γ.PosDef) (hΓ' : Γ'.PosDef)
    (bR : IsBlockDiag p Rz) (bR' : IsBlockDiag p Rz') (e : Rz' * Rz = 1)
    (eo : omBlock Γ' = (omBlock Rz')ᵀᴴ * omBlock Γ * (omBlock Rz')ᵀ)
    (ew : wBlock Γ' = (wBlock Rz)ᴴ * wBlock Γ * wBlock Rz) : blockG Γ' = Rzᴴ * blockG Γ * Rz := by
  have b := (PositivityTheory.Xgp.t_c_bm_exists_blockpos p q Γ hΓ).1
  have b' := (PositivityTheory.Xgp.t_c_bm_exists_blockpos p q Γ' hΓ').1
  have c := isBlockDiag_conjTranspose bR
  have e1 : (omBlock Rz')⁻¹ = omBlock Rz :=
    Matrix.inv_eq_right_inv (by rw [← (blocks_mul bR' bR).1, e, omBlock_one])
  refine b'.ext_blocks ((c.mul b).mul bR) ?_ ?_
  · rw [(blocks_mul (c.mul b) bR).1, (blocks_mul c b).1, omBlock_blockG, omBlock_blockG, eo, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_inv_rev, Matrix.mul_inv_rev, e1]
    have : (omBlock Rz')ᵀᴴᵀ⁻¹ = omBlock Rzᴴ := by
      show ((omBlock Rz')ᴴ)⁻¹ = (omBlock Rz)ᴴ
      rw [← Matrix.conjTranspose_nonsing_inv, e1]
    rw [this]
  · rw [(blocks_mul (c.mul b) bR).2, (blocks_mul c b).2, wBlock_blockG, wBlock_blockG, ew]
    rfl

end Lin

theorem frame_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {L : Lat ξ V} {r : ℕ} {b : Fin r → V} {S : Matrix (Fin r) (Fin r) Ω} {q : Cpt ξ}
    (h : L.IsFrameAt b q) (h' : L.IsFrameAt (colFrame b S) q) (a c : Fin r) : S a c ∈ regAt ξ q := by
  have hm : colFrame b S c ∈ Submodule.span (regAt ξ q) (Set.range b) := by
    rw [← h.2, h'.2]; exact Submodule.subset_span ⟨c, rfl⟩
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
  have h0 : ∑ i, (S i c - t i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 ht.symm
  have := sub_eq_zero.1 (Fintype.linearIndependent_iff.1 h.1 _ h0 a)
  rw [this]
  exact (t a).2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem frames_rel (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H) :
    IsBlockDiag D.p ((F.T τ)⁻¹ * F'.T τ) ∧
    tie.wFrame F' τ = colFrame (tie.wFrame F τ) (wBlock ((F.T τ)⁻¹ * F'.T τ)) ∧
    tie.omFrame F' τ = colFrame (tie.omFrame F τ) (omBlock ((F.T τ)⁻¹ * F'.T τ)) := by
  have hu : IsUnit (F.T τ).det := (hF.1 τ).2.isUnit
  have bR : IsBlockDiag D.p ((F.T τ)⁻¹ * F'.T τ) := ((hF.1 τ).1.inv hu).mul (hF'.1 τ).1
  have e := blocks_mul (hF.1 τ).1 bR
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu] at e
  refine ⟨bR, ?_, ?_⟩
  · unfold FlagTie.wFrame
    rw [e.2, colFrame_mul]
  · unfold FlagTie.omFrame
    rw [e.1, colFrame_mul]

theorem change_reg (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : CoordsAt 𝔐.ξ M.x z w) (gd : M.GoodAt F (mCoordIdeal w)) (gd' : M.GoodAt F' (mCoordIdeal w)) :
    ∃ Rz : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ, ∀ a b, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (((F.T τ)⁻¹ * F'.T τ) a b) (Rz a b) := by
  obtain ⟨bR, ew, eo⟩ := frames_rel tie hF hF' τ
  obtain ⟨f1, f2⟩ := tie.frames_centre hw hF gd τ
  obtain ⟨f1', f2'⟩ := tie.frames_centre hw hF' gd' τ
  rw [ew] at f1'
  rw [eo] at f2'
  have key : ∀ a b, ((F.T τ)⁻¹ * F'.T τ) a b ∈ regAt 𝔐.ξ ⟨centre z, 𝔐.all _⟩ := by
    intro a b
    obtain ⟨a, rfl⟩ := (blockEquiv D.p D.q).surjective a
    obtain ⟨b, rfl⟩ := (blockEquiv D.p D.q).surjective b
    have e := congrFun (congrFun bR.eq_fromBlocks a) b
    rw [Matrix.submatrix_apply] at e
    rw [e]
    rcases a with a | a <;> rcases b with b | b
    exacts [frame_coeff f2 f2' a b, zero_mem _, zero_mem _, frame_coeff f1 f1' a b]
  choose s hs using key
  exact ⟨Matrix.of fun a b => (Scheme.stalkClosedPointTo z).hom (s a b), fun a b => ⟨𝔐.all _, s a b, hs a b, rfl⟩⟩

theorem dual_change (tie : FlagTie M 𝔐) {F F' : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (hF' : M.IsFrame F') (τ : CMType H)
    (hv : ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0)
    (hv' : ∀ a b, tie.omFrame F' τ a (dualFam tie F' τ b) = if a = b then 1 else 0) (m : Fin D.q) :
    dualFam tie F' τ m = colFrame (dualFam tie F τ) (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ m := by
  obtain ⟨bR, -, eo⟩ := frames_rel tie hF hF' τ
  obtain ⟨bR', -, -⟩ := frames_rel tie hF' hF τ
  have hu : IsUnit (F.T τ).det := (hF.1 τ).2.isUnit
  have hu' : IsUnit (F'.T τ).det := (hF'.1 τ).2.isUnit
  have e1 : omBlock ((F'.T τ)⁻¹ * F.T τ) * omBlock ((F.T τ)⁻¹ * F'.T τ) = 1 := by
    rw [← (blocks_mul bR' bR).1, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.nonsing_inv_mul _ hu', omBlock_one]
  have e2 : (omBlock ((F.T τ)⁻¹ * F'.T τ))ᵀ⁻¹ = (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ := by
    rw [← Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv e1]
  have e3 := fun k => colFrame_dual _ _ hv (omBlock ((F.T τ)⁻¹ * F'.T τ)) (Matrix.isUnit_det_of_left_inverse e1) k m
  rw [e2, ← eo] at e3
  rw [← sub_eq_zero]
  generalize hd : dualFam tie F' τ m - colFrame (dualFam tie F τ) (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ m = d
  have h1 : ∀ k, tie.omFrame F' τ k d = 0 := fun k => by rw [← hd, map_sub, e3, hv', sub_self]
  have e4 : (tie.eO τ : Fin D.q → _) = colFrame (tie.omFrame F' τ) (omBlock (F'.T τ)⁻¹) := by
    unfold FlagTie.omFrame
    rw [← colFrame_mul, ← (blocks_mul (hF'.1 τ).1 ((hF'.1 τ).1.inv hu')).1, Matrix.mul_nonsing_inv _ hu',
      omBlock_one, colFrame_one]
  have h2 : ∀ k, tie.eO τ k d = 0 := fun k => by
    rw [e4]; simp [colFrame, h1]
  refine (Module.forall_dual_apply_eq_zero_iff M.Ω d).1 fun ψ => ?_
  rw [← (tie.eO τ).sum_repr ψ, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [LinearMap.smul_apply, h2, smul_zero]

theorem gramAt_sub {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li}
    {L : LB G.left} {z : Spec (CommRingCat.of ℂ) ⟶ X} {r s : ℕ} {b : Fin r → Li} {Γ : Matrix (Fin r) (Fin r) ℂ}
    (h : M.GramAt L z b Γ) (e : Fin s → Fin r) : M.GramAt L z (fun a => b (e a)) (Γ.submatrix e e) :=
  let ⟨v, hv, h'⟩ := h
  ⟨fun a => v (e a), fun a => hv (e a), fun a a' => h' (e a) (e a')⟩

theorem gb_om (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.q) :
    gb tie F τ (omEmb D.p D.q a) = dualFam tie F τ a := by
  simp [gb, gbS, ← blockEquiv_inl]

theorem gb_w (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) (a : Fin D.p) :
    gb tie F τ (wEmb D.p D.q a) = tie.wFrame F τ a := by
  simp [gb, gbS, ← blockEquiv_inr]

theorem dualFam_spec (tie : FlagTie M 𝔐) {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F)
    (τ : CMType H) {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : CoordsAt 𝔐.ξ M.x z w) (gd : M.GoodAt F (mCoordIdeal w)) :
    ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  have h := (omBundle_dualFrame 𝔐 τ _ (tie.frames_centre hw hF gd τ).2).1
  unfold dualFam
  rw [dite_eq_left h]
  exact h.choose_spec

def Gr (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (w : (Σ k, baseIdx ι M.blk k) → ℂ) (G : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal w) ∧ ∃ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
    (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ), CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ ∧ Γ.PosDef ∧ G = blockG Γ

theorem gr_good (tie : FlagTie M 𝔐) (F τ w G) (h : Gr tie F τ w G) : M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧
    M.GoodAt F (mCoordIdeal w) ∧ IsBlockDiag D.p G ∧ G.PosDef := by
  obtain ⟨hF, gd, z, Γ, hw, -, -, hp, rfl⟩ := h
  exact ⟨hF, (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).2 ⟨z, 𝔐.all _, hw⟩, gd,
    PositivityTheory.Xgp.t_c_bm_exists_blockpos _ _ Γ hp⟩

theorem gr_tor (tie : FlagTie M 𝔐) (F τ w G) (cv : NonPluckerBlocks M.blk → ℂ) (hc : ∀ k, cv k ≠ 0) (h : Gr tie F τ w G) :
    Gr tie F τ (torusSmul cv w) G := by
  obtain ⟨hF, gd, z, Γ, hw, h'⟩ := h
  have hz' : CoordsAt 𝔐.ξ M.x z (torusSmul cv w) :=
    (((GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ).2.2 z w (𝔐.all _) hw).2 _).2
      ⟨fun k => Units.mk0 (cv k) (hc k), rfl⟩
  refine ⟨hF, ?_, z, Γ, hz', h'⟩
  rwa [← ptIdeal_centre hz' (𝔐.all _), ptIdeal_centre hw]

theorem gr_conj (tie : FlagTie M 𝔐) (F τ w G) (h : Gr tie F τ w G) :
    Gr tie F τ (conjVec w) (G.map (starRingEnd ℂ)) := by
  obtain ⟨hF, gd, z, Γ, hw, hi, hΓ, hp, rfl⟩ := h
  have hcc := GlobalTheory.T.conjugate_point_same_centre 𝔐.X M.Ω 𝔐.ξ _ _ M.x z w
  refine ⟨hF, ?_, _, _, hcc.2 hw, ?_, GlobalTheory.T.gramAt_conj_point_map_conj E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ hΓ, ?_,
    (blockG_conj Γ).symm⟩
  · have e : mCoordIdeal (conjVec w) = mCoordIdeal w :=
      (ptIdeal_centre (hcc.2 hw) (𝔐.all _)).symm.trans
        ((congrArg (ptIdeal 𝔐.ξ M.x) (Subtype.ext hcc.1)).trans (ptIdeal_centre hw (𝔐.all _)))
    rwa [e]
  · show centre _ ∈ _
    rw [hcc.1]
    exact hi
  · show (Γᴴᵀ).PosDef
    rw [hp.1.eq]
    exact hp.transpose

theorem gr_comp (tie : FlagTie M 𝔐) (F F' τ w G G') (h : Gr tie F τ w G) (h' : Gr tie F' τ w G') :
    ∃ Rz : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz := by
  have hm := (gr_good tie F τ w G h).2.1
  obtain ⟨hF, gd, z, Γ, hw, hi, hΓ, hp, rfl⟩ := h
  obtain ⟨hF', gd', z', Γ', hw', -, hΓ', hp', rfl⟩ := h'
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  obtain rfl : z = z' := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw⟩ ⟨𝔐.all _, hw'⟩
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z hi
  obtain ⟨Rz, hR⟩ := change_reg tie hF hF' τ hw gd gd'
  obtain ⟨Rz', hR'⟩ := change_reg tie hF' hF τ hw gd' gd
  have tv := GlobalTheory.T.valAt_iff_value_at 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie z w (𝔐.all _) hw
  obtain ⟨bR, ew, -⟩ := frames_rel tie hF hF' τ
  obtain ⟨bR', -, -⟩ := frames_rel tie hF' hF τ
  let RA : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (CPts.regRing M.x w) :=
    Matrix.of fun a b => ⟨_, _, (tv _ _).1 (hR a b)⟩
  let RA' : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) (CPts.regRing M.x w) :=
    Matrix.of fun a b => ⟨_, _, (tv _ _).1 (hR' a b)⟩
  have e1 : RA.map (CPts.regRing M.x w).subtype = (F.T τ)⁻¹ * F'.T τ := by ext a b; rfl
  have e1' : RA'.map (CPts.regRing M.x w).subtype = (F'.T τ)⁻¹ * F.T τ := by ext a b; rfl
  have e2 : RA.map (CPts.regVal hm) = Rz := by ext a b; exact valAt_eq hm ((tv _ _).1 (hR a b))
  have e2' : RA'.map (CPts.regVal hm) = Rz' := by ext a b; exact valAt_eq hm ((tv _ _).1 (hR' a b))
  have b1 : IsBlockDiag D.p Rz := by
    have : IsBlockDiag D.p RA := fun a b hab => Subtype.ext (bR a b hab)
    exact e2 ▸ this.map _
  have b1' : IsBlockDiag D.p Rz' := by
    have : IsBlockDiag D.p RA' := fun a b hab => Subtype.ext (bR' a b hab)
    exact e2' ▸ this.map _
  have e3 : Rz' * Rz = 1 := by
    have : RA' * RA = 1 := by
      apply Matrix.map_injective (CPts.regRing M.x w).subtype_injective
      show (RA' * RA).map _ = Matrix.map 1 _
      rw [Matrix.map_mul, e1, e1', Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_assoc,
        Matrix.mul_nonsing_inv_cancel_left _ _ (hF.1 τ).2.isUnit, Matrix.nonsing_inv_mul _ (hF'.1 τ).2.isUnit]
    rw [← e2, ← e2', ← Matrix.map_mul, this, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨Rz, fun a b => (tv _ _).1 (hR a b), (Matrix.isUnit_det_of_left_inverse e3).ne_zero,
    blockG_change hp hp' b1 b1' e3 ?_ ?_⟩
  · refine GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _ _ (omBlock ((F'.T τ)⁻¹ * F.T τ))ᵀ _ hpol
      (gramAt_sub hΓ (omEmb D.p D.q)) (gramAt_sub hΓ' (omEmb D.p D.q)) (fun m => ?_) fun a b => hR' _ _
    simp only [gb_om]
    rw [dual_change tie hF hF' τ (dualFam_spec tie hF τ hw gd) (dualFam_spec tie hF' τ hw gd') m]
    simp [colFrame]
  · refine GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _ _ (wBlock ((F.T τ)⁻¹ * F'.T τ)) _ hpol
      (gramAt_sub hΓ (wEmb D.p D.q)) (gramAt_sub hΓ' (wEmb D.p D.q)) (fun m => ?_) fun a b => hR _ _
    simp only [gb_w]
    exact congrFun ew m

end PositivityTheory.Xgp.c_bm_exists_hom

theorem PositivityTheory.Xgp.t_c_bm_exists_hom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (s : Rb.X → Rb.X → ℂ), (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), (∀ x, ∃ l, x ∈ O l) → (∀ l, M.IsFrame (F l)) → (∀ l, ∀ x ∈ O l, M.GoodAt (F l) (mCoordIdeal (Rb.lift x x))) → ∃ hom : CMType H × Fin (D.p + D.q) → HermLine ι, (∀ p, (hom p).a = M.dy p) ∧ (∀ l, ∀ x ∈ O l \ bdry s, ∀ p, M.IsInducedAt (F l) (Rb.lift x x) p (blockG (baseGram tie (F l) p.1 Rb x)) (hom p)) ∧ ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry s → SameOrbit (basePart M.blk z) (Rb.lift x x) → (hom p).h (fun q => starRingEnd ℂ (z q)) = (hom p).h z := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb s hInt q O F _ hF hgd
  choose hom h1 h2 h3 using PositivityTheory.Xgp.c_bm_exists_hom.exists_hom (PositivityTheory.Xgp.c_bm_exists_hom.gr_good tie)
    (PositivityTheory.Xgp.c_bm_exists_hom.gr_tor tie) (PositivityTheory.Xgp.c_bm_exists_hom.gr_conj tie)
    (PositivityTheory.Xgp.c_bm_exists_hom.gr_comp tie)
  refine ⟨hom, h1, fun i x hx p => h2 p _ _ _ ?_, fun p z _ _ _ _ => h3 p z⟩
  obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).1 (Rb.mem x x (Rb.mem_U x))
  have hi := (hInt x z hz).1 hx.2
  obtain ⟨g1, g2, -⟩ := PositivityTheory.Xgp.t_c_bm_exists_gram E H D Xo l c Y S K ι Φ y M 𝔐 tie (F i) (hF i) p.1 _ z hz hi
    (hgd i x hx.1)
  exact ⟨hF i, hgd i x hx.1, z, _, hz, hi, g1, g2, rfl⟩
