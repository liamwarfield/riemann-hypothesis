module

public import Development.WeilBound.CoreStatements.PluriharmonicCharts.BlockFnFieldCompLe

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsOpenHoloPreimage
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Re

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {x : X}

theorem holo_mono {W W' : Set X} {f : X → ℂ} (h : A.HoloOn W f) (hW : W' ⊆ W) : A.HoloOn W' f :=
  fun j w hw => h j w ⟨hw.1, hW hw.2⟩

def LocRe (A : FinHolAtlas e X) (x : X) (u : X → ℝ) : Prop :=
  ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, u y = (G y).re

theorem LocRe.congr {u u' : X → ℝ} (h : LocRe A x u) {W : Set X} (hW : IsOpen W) (hx : x ∈ W)
    (e : ∀ y ∈ W, u' y = u y) : LocRe A x u' := by
  obtain ⟨V, hV, hxV, G, hG, hu⟩ := h
  exact ⟨V ∩ W, hV.inter hW, ⟨hxV, hx⟩, G, holo_mono hG Set.inter_subset_left,
    fun y hy => (e y hy.2).trans (hu y hy.1)⟩

theorem LocRe.zero : LocRe A x fun _ => 0 :=
  ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ _ _ => analyticAt_const, fun _ _ => rfl⟩

theorem LocRe.add {u u' : X → ℝ} (h : LocRe A x u) (h' : LocRe A x u') : LocRe A x fun y => u y + u' y := by
  obtain ⟨V, hV, hxV, G, hG, hu⟩ := h
  obtain ⟨V', hV', hxV', G', hG', hu'⟩ := h'
  refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y + G' y, fun j w hw => ?_, fun y hy => ?_⟩
  · exact (hG j w ⟨hw.1, hw.2.1⟩).add (hG' j w ⟨hw.1, hw.2.2⟩)
  · rw [Complex.add_re, ← hu y hy.1, ← hu' y hy.2]

theorem LocRe.smul {u : X → ℝ} (h : LocRe A x u) (c : ℝ) : LocRe A x fun y => c * u y := by
  obtain ⟨V, hV, hxV, G, hG, hu⟩ := h
  refine ⟨V, hV, hxV, fun y => c * G y, fun j w hw => ?_, fun y hy => ?_⟩
  · exact analyticAt_const.mul (hG j w hw)
  · rw [Complex.re_ofReal_mul, ← hu y hy]

theorem LocRe.sub {u u' : X → ℝ} (h : LocRe A x u) (h' : LocRe A x u') : LocRe A x fun y => u y - u' y :=
  (h.add (h'.smul (-1))).congr isOpen_univ trivial fun y _ => by ring

theorem LocRe.sum {σ : Type} (s : Finset σ) {u : σ → X → ℝ} (h : ∀ i, LocRe A x (u i)) :
    LocRe A x fun y => ∑ i ∈ s, u i y := by
  induction s using Finset.induction_on with
  | empty => simpa using LocRe.zero
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

theorem LocRe.log {W : Set X} {f : X → ℂ} (hW : IsOpen W) (h : A.HoloOn W f) (hx : x ∈ W)
    (h0 : f x ≠ 0) : LocRe A x fun y => Real.log ‖f y‖ := by
  have hc : ContinuousOn (fun y => f y / f x) W := fun y hy =>
    ((FA.BlockPot.continuousAt_of_holoOn h hy).div_const _).continuousWithinAt
  refine ⟨W ∩ (fun y => f y / f x) ⁻¹' Complex.slitPlane, hc.isOpen_inter_preimage hW Complex.isOpen_slitPlane,
    ⟨hx, by simp [div_self h0]⟩, fun y => Complex.log (f y / f x) + (Real.log ‖f x‖ : ℝ), ?_, ?_⟩
  · intro j w hw
    have h1 : AnalyticAt ℂ (fun w => (f ∘ (A.chart j).symm) w / f x) w :=
      (h j w ⟨hw.1, hw.2.1⟩).div analyticAt_const h0
    exact (h1.clog hw.2.2).add analyticAt_const
  · intro y hy
    have h1 : f y / f x ≠ 0 := Complex.slitPlane_ne_zero hy.2
    have h2 : f y ≠ 0 := fun e => h1 (by simp [e])
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h2) (norm_ne_zero_iff.2 h0)]
    ring

theorem LocRe.comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {g : Y → X} (hg : HoloMap B A g)
    {y₀ : Y} {u : X → ℝ} (h : LocRe A (g y₀) u) : LocRe B y₀ fun y => u (g y) := by
  obtain ⟨V, hV, hxV, G, hG, hu⟩ := h
  exact ⟨g ⁻¹' V, hV.preimage hg.1, hxV, _, FA.BlockPot.holoOn_comp hg hG, fun y hy => hu _ hy⟩

theorem holo_comp_an {σ : Type} [Fintype σ] {W : Set X} {Z : X → σ → ℂ} (hZ : ∀ q, A.HoloOn W fun y => Z y q)
    {r : (σ → ℂ) → ℂ} (hr : ∀ y ∈ W, AnalyticAt ℂ r (Z y)) : A.HoloOn W fun y => r (Z y) := fun j w hw =>
  (hr _ hw.2).comp (f := fun w => Z ((A.chart j).symm w)) (analyticAt_pi_iff.2 fun q => hZ q j w hw)

theorem isOpen_holo_preimage {σ : Type} {W : Set X} (hW : IsOpen W) {Z : X → σ → ℂ}
    (hZ : ∀ q, A.HoloOn W fun y => Z y q) {V : Set (σ → ℂ)} (hV : IsOpen V) : IsOpen (W ∩ Z ⁻¹' V) :=
  ContinuousOn.isOpen_inter_preimage (continuousOn_pi.2 fun q y hy =>
    (FA.BlockPot.continuousAt_of_holoOn (hZ q) hy).continuousWithinAt) hW hV

end Re

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem log_smul (A : HermLine ι) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have h0 : ∀ k ∈ (Finset.univ : Finset K), ‖c k‖ ^ A.a k ≠ 0 := fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 h0) (A.pos z hz).ne', Real.log_prod h0, add_comm]
  simp only [Real.log_zpow]

theorem sum_dy (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ kb : NonPluckerBlocks M.blk, (M.b p kb : ℝ) * L kb.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => ∀ p', M.blk p' ≠ some k), add_comm, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · have e : ∀ k : {k // ¬ ∀ p', M.blk p' ≠ some k}, (M.dy p k.1 : ℝ) * L k.1 = if M.blk p = some k.1 then L k.1 else 0 :=
      fun k => by
        rw [FlagModel.dy, dite_eq_right k.2]
        split_ifs <;> simp
    simp only [e]
    cases hp : M.blk p with
    | none => simp
    | some k₁ =>
      rw [Finset.sum_eq_single (⟨k₁, fun h => h p hp⟩ : {k // ¬ ∀ p', M.blk p' ≠ some k})]
      · simp
      · intro k _ hk
        rw [if_neg]
        intro h
        exact hk (Subtype.ext (Option.some.inj h).symm)
      · simp
  · refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun k _ => ?_
    rw [FlagModel.dy, dif_pos k.2]
    simp

theorem exists_exact (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F z h) :
    ∃ z₁, SameOrbit z₁ z ∧ basePart M.blk z₁ = basePart M.blk z ∧ ∀ p, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p z₁ (h p.1) := by
  have key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ((∀ p, M.blk p ≠ some k) → c = 1) ∧ ∀ p, M.blk p = some k → ∀ m,
      c * z ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ (h p.1) I (stepCols N j p.2) := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · exact ⟨1, one_ne_zero, fun _ => rfl, fun p hp => absurd hp (hk p)⟩
    · obtain ⟨a, ha, e⟩ := H.2.2 _ k (blk_stepOf M k hk)
      refine ⟨a⁻¹, inv_ne_zero ha, fun h => absurd h hk, fun p hp m => ?_⟩
      rw [M.blk_inj _ _ k hp (blk_stepOf M k hk), e m, inv_mul_cancel_left₀ ha]
  choose c hc hb hs using key
  have eb : basePart M.blk (fun q => c q.1 * z q) = basePart M.blk z := funext fun q => by
    show c q.1.1 * _ = _
    rw [hb _ q.1.2, one_mul]
    rfl
  exact ⟨_, ⟨c, hc, rfl⟩, eb, fun p => ⟨by rw [eb]; exact H.1, fun k hk m => by rw [eb]; exact hs k p hk m⟩⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j}

theorem img_exact (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x)) (hF' : M'.IsFrame F')
    (hG' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z))) (hh : ∀ τ, IsBlockDiag j (h τ)) {p : Ψ × Fin N} {k : K}
    {k' : K'} (hp : M.blk p = some k) (hk' : M'.blk p = some k') {a : ℂ}
    (hz : ∀ m' : ι' k', z ⟨k', m'⟩ = a * plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = a * plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩
      (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (stepCols_ne_empty M.j_le)
  have hdelta : ∀ I' J, IsStepRows N j p.2 I' → IsStepRows N j p.2 J →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
        valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z) = if I' = J then 1 else 0 := by
    intro I' J hI hJ
    have hu' := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ I').2
    have hu := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ J).1
    have e1 := (reg_sum hb Finset.univ (fun m' : ι' k' => F'.u' I' ⟨k', m'⟩ * F'.u ⟨k', m'⟩ J)
      fun m' _ => (reg_mul hb (hu' m') (hu m')).1).2
    rw [hF'.2.2.1 p k' hk' I' J hI hJ] at e1
    rw [Finset.sum_congr rfl fun m' _ => ((reg_mul hb (hu' m') (hu m')).2).symm, ← e1]
    split_ifs
    · exact map_one (regVal M'.x hb)
    · exact map_zero (regVal M'.x hb)
  have hread : ∀ I', IsStepRows N j p.2 I' →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * minorIJ (h p.1) I' (stepCols N j p.2) := by
    intro I' hI
    have e1 : ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * ∑ J, (∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
          valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z)) * minorIJ (h p.1) J (stepCols N j p.2) := by
      simp_rw [hz, plk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m' _ => ?_
      ring
    rw [e1]
    congr 1
    rw [Finset.sum_eq_single I']
    · rw [hdelta I' I' hI hI, if_pos rfl, one_mul]
    · intro J _ hne
      by_cases hJ : IsStepRows N j p.2 J
      · rw [hdelta I' J hI hJ, if_neg hne.symm, zero_mul]
      · rw [hoff J hJ, mul_zero]
    · simp
  rw [img_step Cv F' F z hp hk' m]
  unfold stepCoord plk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hCB.1, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j p.2 I'
  · rw [if_pos hI, hread I' hI]; ring
  · rw [if_neg hI, hoff I' hI, mul_zero, mul_zero]

variable {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d} {Cv : FlagCover M' M}

theorem met (CR : CovReal FA Cv) {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y'))
    {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk} (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) (p : Ψ × Fin N) :
    Real.log ((CR.Re.ref p).h z) = Real.log ((fsHerm ι (M.dy p)).h (img Cv F' F z)) +
      ∑ kb, (M.b p kb : ℝ) * Real.log ‖(basePart M'.blk z ∘ Cv.v) ⟨kb, F.c kb⟩‖ -
      ∑ kb, (M'.b p kb : ℝ) * Real.log ‖basePart M'.blk z ⟨kb, F'.c kb⟩‖ +
      (M.blk p).elim (Real.log ‖valAt M.x (F.υ p) (basePart M'.blk z ∘ Cv.v)‖) (fun _ => 0) -
      (M'.blk p).elim (Real.log ‖valAt M'.x (F'.υ p) (basePart M'.blk z)‖) (fun _ => 0) +
      Real.log ‖detFac j p.2 (Cv.trans F' F (basePart M'.blk z) p.1)‖ := by
  have hb := CPts.base_mem M' hz
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  have hI' := CoordinateConeArithVar.isMultiHomogIdeal y'
  obtain ⟨z₁, o₁, n₁⟩ := FibreCount.exists_normal_base M'.blk F'.c z fun k => FibreCount.chart_ne (hg'.1 k)
  obtain ⟨h, H⟩ := CPts.flag_fwd M' hF' (mem_mcPts_of_sameOrbit hI' o₁ hz)
    (by rw [ideal_orbit (base_orbit o₁)]; exact hg') n₁
  obtain ⟨z₂, o₂, -, hex⟩ := exists_exact M' H
  have o := orbit_trans o₂ o₁
  have hz₂ := mem_mcPts_of_sameOrbit hI' o hz
  have ob := base_orbit (blk := M'.blk) o
  have obv := comp_orbit Cv.block ob
  have htr : Cv.trans F' F (basePart M'.blk z₂) p.1 = Cv.trans F' F (basePart M'.blk z) p.1 := by
    ext a c
    exact valAt_orbit ob hb _
  obtain ⟨c, hc, rfl⟩ := o
  obtain ⟨hw, -⟩ := img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  have hch : ∀ k, (basePart M'.blk z ∘ Cv.v) ⟨k, F.c k⟩ ≠ 0 := fun k => FibreCount.chart_ne (hg.1 k)
  obtain ⟨e, he, heb, hes⟩ : ∃ e : K → ℂ, (∀ k, e k ≠ 0) ∧
      (∀ kb : NonPluckerBlocks M.blk, e kb.1 = ((basePart M'.blk z ∘ Cv.v) ⟨kb, F.c kb⟩)⁻¹) ∧
      ∀ k k', M.blk p = some k → M'.blk p = some k' → e k = c k' := by
    refine ⟨fun k => if hk : ∀ p, M.blk p ≠ some k then ((basePart M'.blk z ∘ Cv.v) ⟨⟨k, hk⟩, F.c ⟨k, hk⟩⟩)⁻¹
      else (M'.blk p).elim 1 c, fun k => ?_, fun kb => dif_pos kb.2, fun k k' h1 h2 => ?_⟩
    · dsimp only
      split_ifs with hk
      · exact inv_ne_zero (hch _)
      · cases M'.blk p <;> simp [hc]
    · dsimp only
      rw [dite_eq_right fun h => h p h1, h2]
      rfl
  have ow : SameOrbit (fun q => e q.1 * img Cv F' F z q) (img Cv F' F z) := ⟨e, he, rfl⟩
  have owb : SameOrbit (basePart M.blk fun q => e q.1 * img Cv F' F z q) (basePart M'.blk z ∘ Cv.v) := by
    rw [← img_base Cv F' F z]; exact base_orbit ow
  have hM := CR.metric _ hz₂ _ (mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ow hw) F' F hF' hF
    (by rw [ideal_orbit ob]; exact hg') (by rw [ideal_orbit obv]; exact hg) (orbit_trans owb (orbit_symm obv)) p (h p.1)
    (H.2.1 _).1 (H.2.1 _).2 (hex p) ⟨fun kb => by
      show e kb.1 * basePart M.blk (img Cv F' F z) ⟨kb, F.c kb⟩ = 1
      rw [heb, img_base, inv_mul_cancel₀ (hch kb)], fun k hk m => by
      obtain ⟨k', hk'⟩ := exists_blk_cover M' hk
      have h1 := img_exact Cv z F' F h hb hF' hg' (fun τ => (H.2.1 τ).1) hk hk' (a := (c k')⁻¹) (fun m' => by
        have h2 := (hex p).2 k' hk' m'
        simp only [valAt_orbit ob hb] at h2
        rw [plk, ← h2, inv_mul_cancel_left₀ (hc k')]) m
      simp only [valAt_orbit owb hbv, htr]
      rw [h1, hes k k' hk hk', mul_inv_cancel_left₀ (hc k')]
      rfl⟩
  rw [log_smul _ c hc hz.1, log_smul _ e he hw.1, CR.ref_deg, show (fsHerm ι (M.dy p)).a = M.dy p from rfl,
    sum_dy, sum_dy, htr] at hM
  simp only [FlagModel.upsLog, valAt_orbit ob hb, valAt_orbit owb hbv, heb, norm_inv, Real.log_inv] at hM
  have hcb : ∀ kb : NonPluckerBlocks M'.blk, Real.log ‖c kb.1‖ = -Real.log ‖basePart M'.blk z ⟨kb, F'.c kb⟩‖ := fun kb => by
    have h1 : c kb.1 * basePart M'.blk z ⟨kb, F'.c kb⟩ = 1 := (hex p).1 kb
    rw [eq_inv_of_mul_eq_one_left h1, norm_inv, Real.log_inv]
  have hel : (M'.blk p).elim 0 (fun k => Real.log ‖c k‖) = (M.blk p).elim 0 fun k => Real.log ‖e k‖ := by
    cases hp : M.blk p with
    | none => rw [(M'.blk_none p).2 ((M.blk_none p).1 hp)]; rfl
    | some k =>
      obtain ⟨k', hk'⟩ := exists_blk_cover M' hp
      simp only [hk', Option.elim, hes k k' hp hk']
  simp only [hcb, hel, mul_neg, Finset.sum_neg_distrib] at hM
  linarith

theorem detFac_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin N)
    (T : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (h : ∀ a b, AnalyticAt ℂ (fun w => T w a b) x) :
    AnalyticAt ℂ (fun w => detFac j i (T w)) x := by
  unfold detFac
  refine AnalyticAt.mul ?_ ?_ <;> split_ifs
  · exact CovLift.minor_analytic T x _ _ h
  · exact analyticAt_const
  · exact CovLift.minor_analytic T x _ _ h
  · exact analyticAt_const

theorem val_ne_zero {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂]
    {x₂ : (Σ k, ι₂ k) → Ω₂} {zb : (Σ k, ι₂ k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x₂)) {s : Ω₂} (h0 : s ≠ 0)
    (hs : RegAt x₂ (mCoordIdeal zb) s) (hs' : RegAt x₂ (mCoordIdeal zb) s⁻¹) : valAt x₂ s zb ≠ 0 := by
  intro h
  have h1 := (reg_mul hz hs hs').2
  rw [mul_inv_cancel₀ h0, valAt_eq hz (isValueAt_one_self _ _), h, zero_mul] at h1
  exact one_ne_zero h1

theorem locRe_val {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {x : X} {K₂ : Type} [Fintype K₂]
    {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)] {Ω₂ : Type} [Field Ω₂] {x₂ : (Σ k, ι₂ k) → Ω₂} {W : Set X} (hW : IsOpen W)
    (hx : x ∈ W) {Z : X → (Σ k, ι₂ k) → ℂ} (hZ : ∀ q, A.HoloOn W fun y => Z y q)
    (hm : ∀ y ∈ W, Z y ∈ mcPts (mCoordIdeal x₂)) {σ : Type} [Fintype σ] (s : σ → Ω₂)
    (hs : ∀ a, RegAt x₂ (mCoordIdeal (Z x)) (s a)) (Q : (σ → ℂ) → ℂ) (hQ : ∀ u, AnalyticAt ℂ Q u)
    (h0 : Q (fun a => valAt x₂ (s a) (Z x)) ≠ 0) : LocRe A x fun y => Real.log ‖Q fun a => valAt x₂ (s a) (Z y)‖ := by
  obtain ⟨V, r, hV, hxV, -, hr, hv⟩ := CovLift.exists_value_family (hm x hx) s hs
  have hO := isOpen_holo_preimage hW hZ hV
  have e1 : ∀ y ∈ W ∩ Z ⁻¹' V, (fun a => valAt x₂ (s a) (Z y)) = fun a => r a (Z y) := fun y hy =>
    funext fun a => valAt_eq (hm y hy.1) (hv a _ hy.2).1
  have hH : A.HoloOn (W ∩ Z ⁻¹' V) fun y => Q fun a => r a (Z y) :=
    holo_comp_an (Z := fun y a => r a (Z y)) (fun a => holo_comp_an (fun q => holo_mono (hZ q) Set.inter_subset_left)
      fun y hy => hr a _ hy.2) fun _ _ => hQ _
  refine (LocRe.log hO hH ⟨hx, hxV⟩ (by rw [← e1 x ⟨hx, hxV⟩]; exact h0)).congr hO ⟨hx, hxV⟩ fun y hy => ?_
  rw [e1 y hy]

theorem pot_loc (CR : CovReal FA Cv) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (hy' : IsArithVar (mCoordIdeal y') (d + 2)) {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {x : X}
    {W : Set X} (hW : IsOpen W) (hx : x ∈ W) {Z : X → (Σ k, ι' k) → ℂ} (hZ : ∀ q, A.HoloOn W fun y => Z y q)
    (hm : ∀ u ∈ W, Z u ∈ mcPts (mCoordIdeal y')) {Y : X → (Σ k, ι k) → ℂ} (hY : ∀ q, A.HoloOn W fun y => Y y q)
    (hY0 : ∀ u ∈ W, ∀ k, ∃ i, Y u ⟨k, i⟩ ≠ 0) (hi : ∀ u ∈ W, IsImg Cv (Z u) (Y u)) (p : Ψ × Fin N) :
    LocRe A x fun u => Real.log ((CR.Re.ref p).h (Z u)) - Real.log ((fsHerm ι (M.dy p)).h (Y u)) := by
  have hz := hm x hx
  have hb := CPts.base_mem M' hz
  have hbv := fun u hu => (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (CPts.base_mem M' (hm u hu))).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ (hbv x hx)
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hz hF' hF hg' hg
  have hO := isOpen_holo_preimage hW hZ hV
  have hxO : x ∈ W ∩ Z ⁻¹' V := ⟨hx, hzV⟩
  have hfZ : ∀ q, A.HoloOn (W ∩ Z ⁻¹' V) fun u => f (Z u) q := fun q =>
    holo_comp_an (r := fun z => f z q) (fun q => holo_mono (hZ q) Set.inter_subset_left)
      fun u hu => analyticAt_pi_iff.1 (hf _ hu.2) q
  have horb : ∀ u ∈ W ∩ Z ⁻¹' V, SameOrbit (f (Z u)) (Y u) := fun u hu => by
    obtain ⟨g1, g2, e1⟩ := hs _ ⟨hu.2, hm u hu.1⟩
    rw [e1]
    exact GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (hm u hu.1) _ _
      (img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F (hm u hu.1) hF' hF g1 g2).2 (hi u hu.1)
  choose m hm0 using hY0 x hx
  have hO₂ : IsOpen (W ∩ Y ⁻¹' {w | ∀ k, w ⟨k, m k⟩ ≠ 0}) := isOpen_holo_preimage hW hY (by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const)
  have hfx : ∀ k, f (Z x) ⟨k, m k⟩ ≠ 0 := fun k => by
    obtain ⟨c, hc, e1⟩ := horb x hxO
    rw [e1]
    exact mul_ne_zero (hc k) (hm0 k)
  have L1 : LocRe A x fun u => ∑ k, (M.dy p k : ℝ) * (Real.log ‖f (Z u) ⟨k, m k⟩‖ - Real.log ‖Y u ⟨k, m k⟩‖) :=
    LocRe.sum _ fun k => ((LocRe.log hO (hfZ _) hxO (hfx k)).sub (LocRe.log hW (hY _) hx (hm0 k))).smul _
  have L2 : LocRe A x fun u => ∑ kb, (M.b p kb : ℝ) * Real.log ‖(basePart M'.blk (Z u) ∘ Cv.v) ⟨kb, F.c kb⟩‖ :=
    LocRe.sum _ fun kb => (LocRe.log hW (hZ _) hx (FibreCount.chart_ne (z := basePart M'.blk (Z x) ∘ Cv.v) (hg.1 kb))).smul _
  have L3 : LocRe A x fun u => ∑ kb, (M'.b p kb : ℝ) * Real.log ‖basePart M'.blk (Z u) ⟨kb, F'.c kb⟩‖ :=
    LocRe.sum _ fun kb => (LocRe.log hW (hZ _) hx (FibreCount.chart_ne (z := basePart M'.blk (Z x)) (hg'.1 kb))).smul _
  have hev : ∀ u : Unit → ℂ, AnalyticAt ℂ (fun u : Unit → ℂ => u ()) u := fun u =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ℂ) ()).analyticAt u
  have L4 : LocRe A x fun u =>
      (M.blk p).elim (Real.log ‖valAt M.x (F.υ p) (basePart M'.blk (Z u) ∘ Cv.v)‖) (fun _ => 0) := by
    cases hp : M.blk p with
    | some k => exact LocRe.zero
    | none =>
      obtain ⟨h1, h2, h3⟩ := hg.2.2 p hp
      exact locRe_val hW hx (Z := fun u => basePart M'.blk (Z u) ∘ Cv.v) (fun q => hZ _) hbv (fun _ : Unit => F.υ p)
        (fun _ => h2) (fun u => u ()) hev (val_ne_zero (hbv x hx) h1 h2 h3)
  have L5 : LocRe A x fun u =>
      (M'.blk p).elim (Real.log ‖valAt M'.x (F'.υ p) (basePart M'.blk (Z u))‖) (fun _ => 0) := by
    cases hp : M'.blk p with
    | some k => exact LocRe.zero
    | none =>
      obtain ⟨h1, h2, h3⟩ := hg'.2.2 p hp
      exact locRe_val hW hx (Z := fun u => basePart M'.blk (Z u)) (fun q => hZ _)
        (fun u hu => CPts.base_mem M' (hm u hu)) (fun _ : Unit => F'.υ p)
        (fun _ => h2) (fun u => u ()) hev (val_ne_zero hb h1 h2 h3)
  have L6 : LocRe A x fun u => Real.log ‖detFac j p.2 (Cv.trans F' F (basePart M'.blk (Z u)) p.1)‖ := by
    have hT := FibreCount.trans_unit Cv hb hF' hF hg' hg p.1
    exact locRe_val hW hx (Z := fun u => basePart M'.blk (Z u)) (fun q => hZ _)
      (fun u hu => CPts.base_mem M' (hm u hu))
      (fun ab : Fin N × Fin N => (((F.T p.1).map Cv.φ)⁻¹ * F'.T p.1) ab.1 ab.2)
      (fun ab => (Cv.agree _ hb F' F hF' hF hg' hg p.1 ab.1 ab.2).1)
      (fun u => detFac j p.2 (Matrix.of fun a b => u (a, b)))
      (fun u => detFac_analytic p.2 _ u fun a b =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N × Fin N => ℂ) (a, b)).analyticAt u)
      (CPts.detFac_ne_zero M.j_le p.2 hT.1 hT.2)
  refine (((((L1.add L2).sub L3).add L4).sub L5).add L6).congr (hO.inter hO₂) ⟨hxO, hx, hm0⟩ fun u hu => ?_
  obtain ⟨g1, g2, e1⟩ := hs _ ⟨hu.1.2, hm u hu.1.1⟩
  rw [met CR (hm u hu.1.1) hF' hF g1 g2 p, ← e1]
  obtain ⟨c, hc, e2⟩ := horb u hu.1
  have h3 : ∀ k, Real.log ‖f (Z u) ⟨k, m k⟩‖ - Real.log ‖Y u ⟨k, m k⟩‖ = Real.log ‖c k‖ := fun k => by
    rw [e2, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hu.2.2 k))]
    ring
  simp only [h3]
  rw [e2, log_smul _ c hc fun k => ⟨m k, hu.2.2 k⟩, show (fsHerm ι (M.dy p)).a = M.dy p from rfl]
  ring

end PositivityTheory.Xgp.c_sqsys
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Fac

variable {N j : ℕ}

def mfac (j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ h (wIdx N j) (wIdx N j) else 1)
  else minorIJ h (omIdx N j) (omIdx N j)

theorem mfac_mul (a i : Fin N) (T : Matrix (Fin N) (Fin N) ℂ) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) :
    mfac j a i (T * h) = mfac j a i T * mfac j a i h := by
  unfold mfac
  rw [MinorCalc.minorIJ_mul_of_support T h _ _ (MinorCalc.support_wIdx hh),
    MinorCalc.minorIJ_mul_of_support T h _ _ (MinorCalc.support_omIdx hh)]
  split_ifs <;> simp

theorem mfac_ne (a i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    mfac j a i h ≠ 0 := by
  have h1 := mfac_mul a i h⁻¹ hh
  rw [Matrix.nonsing_inv_mul _ hd.isUnit] at h1
  have h2 : mfac j a i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold mfac
    split_ifs <;> simp [CPts.minorIJ_one]
  rw [h2] at h1
  exact right_ne_zero_of_mul_eq_one h1.symm

theorem minor_w_ne {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    minorIJ h (wIdx N j) (wIdx N j) ≠ 0 ∧ minorIJ h (omIdx N j) (omIdx N j) ≠ 0 := by
  have h1 := MinorCalc.minorIJ_mul_of_support h⁻¹ h (wIdx N j) _ (MinorCalc.support_wIdx hh)
  have h2 := MinorCalc.minorIJ_mul_of_support h⁻¹ h (omIdx N j) _ (MinorCalc.support_omIdx hh)
  rw [Matrix.nonsing_inv_mul _ hd.isUnit, CPts.minorIJ_one] at h1 h2
  exact ⟨right_ne_zero_of_mul_eq_one h1.symm, right_ne_zero_of_mul_eq_one h2.symm⟩

theorem sum_detFac (hj : j ≤ N) {a b : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : IsBlockDiag j T) (hd : T.det ≠ 0) :
    ∑ i, (xiCoef () a ((), i) : ℝ) * (Real.log ‖detFac j i T‖ -
      if IsProperStep N j i then 0 else Real.log ‖mfac j a i T‖) = 0 := by
  obtain ⟨hw, ho⟩ := minor_w_ne hT hd
  have ha := a.2
  have hb' := b.2
  have key : ∀ i : Fin N, (a : ℕ) ≤ i + 1 → (i : ℕ) ≤ a + 1 → (Real.log ‖detFac j i T‖ -
      if IsProperStep N j i then 0 else Real.log ‖mfac j a i T‖) =
      if j ≤ (a : ℕ) then Real.log ‖minorIJ T (wIdx N j) (wIdx N j)‖ else 0 := by
    intro i h1 h2
    have hi := i.2
    have ho1 : j = N → minorIJ T (omIdx N j) (omIdx N j) = 1 := fun e => by
      rw [show omIdx N j = ∅ by ext c; simp [omIdx, e]]
      exact SchurCalc.minor_empty T
    unfold detFac mfac IsProperStep
    by_cases c1 : (i : ℕ) + 1 = j <;> by_cases c2 : (i : ℕ) + 1 = N <;> by_cases c3 : j ≤ (a : ℕ)
    · omega
    · rw [ho1 (by omega)]
      simp [c1, c3, not_le.1 c3]
    · simp [c1, c3, not_lt.2 c3, show ¬ j = N by omega]
    · simp [c1, c3, not_le.1 c3, show ¬ j = N by omega]
    · simp [c1, c2, c3, hj, show ¬ N = j by omega, Real.log_mul (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 ho)]
    · omega
    · simp [c1, c2, c3, show j ≤ (i : ℕ) + 1 by omega]
    · simp [c1, c2, c3, show ¬ j ≤ (i : ℕ) + 1 by omega]
  rw [SchurCalc.sum_xi _ a b hb (if j ≤ (a : ℕ) then Real.log ‖minorIJ T (wIdx N j) (wIdx N j)‖ else 0)
    (fun i hi => key i (by omega) (by omega)) ?_, key b (by omega) (by omega), key a (by omega) (by omega)]
  · ring
  · intro h0
    split_ifs with c
    · rw [show wIdx N j = ∅ by ext c; simp [wIdx, show j = 0 by omega], SchurCalc.minor_empty]
      simp
    · rfl

theorem sum_xi_prod {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (τ : Ψ) (a : Fin N) (T : Ψ × Fin N → ℝ) :
    ∑ p, (xiCoef τ a p : ℝ) * T p = ∑ i, (xiCoef τ a (τ, i) : ℝ) * T (τ, i) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · intro τ' _ h
    simp [xiCoef, h]
  · simp

theorem log_fac {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (a : Fin N) {t : ℂ} (ht : t ≠ 0) {A : Fin N → ℂ} (hA : ∀ i, A i ≠ 0) :
    Real.log ‖t * ∏ i, A i ^ xiCoef τ a (τ, i)‖ = Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) * Real.log ‖A i‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 ht)
    (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hA i))), norm_prod,
    Real.log_prod fun i _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (hA i))]
  simp only [norm_zpow, Real.log_zpow]

end Fac

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem log_eval_smul {g : MRing ι} {dg : K → ℕ} (hg : IsMultiHomog g dg) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (h0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) :
    eval (fun q => c q.1 * z q) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
    Real.log ‖eval (fun q => c q.1 * z q) (map (Int.castRingHom ℂ) g)‖ =
      Real.log ‖eval z (map (Int.castRingHom ℂ) g)‖ + ∑ k, (dg k : ℝ) * Real.log ‖c k‖ := by
  have hu : (∏ k, c k ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [eval_smul_homog g dg hg]
  refine ⟨mul_ne_zero hu h0, ?_⟩
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hu) (norm_ne_zero_iff.2 h0), norm_prod,
    Real.log_prod fun k _ => norm_ne_zero_iff.2 (pow_ne_zero _ (hc k)), add_comm]
  simp only [norm_pow, Real.log_pow]

def lognorm (τ : Ψ) (a : Fin N) (k₀ : K) (g h : MRing fun o : Option K => ι (o.getD k₀))
    (A : Ψ × Fin N → HermLine ι) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : ℝ :=
  Real.log ‖eval z (map (Int.castRingHom ℂ) g)‖ - Real.log ‖eval z (map (Int.castRingHom ℂ) h)‖ +
    (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + Real.log ((A p).h (sndPt k₀ z)))

theorem lognorm_orbit {τ : Ψ} {a : Fin N} {k₀ : K} {g h : MRing fun o : Option K => ι (o.getD k₀)}
    {dg dh : Option K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) {A : Ψ × Fin N → HermLine ι}
    (hxi : ∑ p, xiCoef τ a p * (A p).a k₀ = -2)
    (hdeg : ∀ o : Option K, (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (A p).a k) - if k₀ = k then 1 else 0)
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (ho : SameOrbit z' z)
    (h₀ : ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0) (h₁ : ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0)
    (g0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) (h0 : eval z (map (Int.castRingHom ℂ) h) ≠ 0) :
    eval z' (map (Int.castRingHom ℂ) g) ≠ 0 ∧ eval z' (map (Int.castRingHom ℂ) h) ≠ 0 ∧
      lognorm τ a k₀ g h A z' = lognorm τ a k₀ g h A z := by
  obtain ⟨c, hc, rfl⟩ := ho
  obtain ⟨g1, g2⟩ := log_eval_smul hg c hc g0
  obtain ⟨h1, h2⟩ := log_eval_smul hh c hc h0
  refine ⟨g1, h1, ?_⟩
  have e₀ : fstPt k₀ (fun q => c q.1 * z q) = fun q => (fun k => c (some k)) q.1 * fstPt k₀ z q := rfl
  have e₁ : sndPt k₀ (fun q => c q.1 * z q) = fun q => (fun k => c (κ₁ k₀ k)) q.1 * sndPt k₀ z q := by
    funext q
    show c (v₁ k₀ q).1 * _ = _
    rw [(isBlockMap_v₁ k₀).2.2.1]
    rfl
  unfold lognorm
  rw [g2, h2, e₀, e₁]
  simp only [fun p => log_smul (A p) (fun k => c (some k)) (fun k => hc _) h₀,
    fun p => log_smul (A p) (fun k => c (κ₁ k₀ k)) (fun k => hc _) h₁]
  have hd : ∀ o, (dg o : ℝ) - dh o = (((o.elim 1 fun k => -(∑ p, xiCoef τ a p * (A p).a k) -
      if k₀ = k then 1 else 0 : ℤ)) : ℝ) := fun o => by rw [← hdeg]; push_cast; rfl
  have key : ∑ o, (dg o : ℝ) * Real.log ‖c o‖ - ∑ o, (dh o : ℝ) * Real.log ‖c o‖ + (1 / 2) * ∑ p, (xiCoef τ a p : ℝ) *
      (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) = 0 := by
    have e2 : ∑ p, (xiCoef τ a p : ℝ) *
        (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) =
        ∑ k, ((∑ p, xiCoef τ a p * (A p).a k : ℤ) : ℝ) * (Real.log ‖c (some k)‖ + Real.log ‖c (κ₁ k₀ k)‖) := by
      simp only [← Finset.sum_add_distrib, Finset.mul_sum, Int.cast_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => by push_cast; ring
    rw [e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [← sub_mul, hd]
    rw [Fintype.sum_option, add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_single k₀]
    · simp only [Option.elim, hxi, κ₁_self, if_true]
      push_cast
      ring
    · intro k _ hk
      simp only [Option.elim, κ₁_ne hk, if_neg (Ne.symm hk)]
      push_cast
      ring
    · simp
  have e3 : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ +
      (Real.log ((A p).h (sndPt k₀ z)) + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖)) =
      ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((A p).h (fstPt k₀ z)) + Real.log ((A p).h (sndPt k₀ z))) +
      ∑ p, (xiCoef τ a p : ℝ) *
        (∑ k, ((A p).a k : ℝ) * Real.log ‖c (some k)‖ + ∑ k, ((A p).a k : ℝ) * Real.log ‖c (κ₁ k₀ k)‖) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [e3]
  linarith

theorem flag_of_exact (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (p₀ : Ψ × Fin N) (hh : ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0)
    (H : ∀ p, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p z (h p.1)) : M.IsFlagOf F z h :=
  ⟨(H p₀).1, hh, fun p k hk => ⟨1, one_ne_zero, fun m => by rw [one_mul]; exact (H p).2 k hk m⟩⟩

theorem log_A (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {z : (Σ k, ι k) → ℂ}
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (τ : Ψ) (a i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0) :
    (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z) * mfac j a i h) ≠ 0 ∧
    Real.log ‖(if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z) * mfac j a i h)‖ =
      M.upsLog F (τ, i) z + if IsProperStep N j i then 0 else Real.log ‖mfac j a i h‖ := by
  by_cases hp : IsProperStep N j i
  · obtain ⟨k, hk⟩ : ∃ k, M.blk (τ, i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hp
    simp [hp, FlagModel.upsLog, hk]
  · have hn := (M.blk_none (τ, i)).2 hp
    obtain ⟨h1, h2, h3⟩ := hG.2.2 _ hn
    have h4 := val_ne_zero hz h1 h2 h3
    have h5 := mfac_ne a i hh hd
    simp only [if_neg hp, FlagModel.upsLog, hn, Option.elim, norm_mul]
    exact ⟨mul_ne_zero h4 h5, Real.log_mul (norm_ne_zero_iff.2 h4) (norm_ne_zero_iff.2 h5)⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {n d : ℕ} {BM : BaseMetric M n} {FA : FlagAn BM d}
  {Cv : FlagCover M' M} {τ : Ψ} {a b : Fin N} {k₀' : K'} {ca cb : Fin N}

theorem norm_pt (CR : CovReal FA Cv) (S' : Sw M' τ a b k₀' ca cb) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {g h : MRing fun o : Option K' => ι' (o.getD k₀')} {dg dh : Option K' → ℕ} (hg : IsMultiHomog g dg)
    (hh : IsMultiHomog h dh) (hxi : ∑ p, xiCoef τ a p * (CR.Re.ref p).a k₀' = -2)
    (hdeg : ∀ o : Option K', (dg o : ℤ) - dh o =
      o.elim 1 fun k => -(∑ p, xiCoef τ a p * (CR.Re.ref p).a k) - if k₀' = k then 1 else 0)
    (LC : ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), ∀ F, M'.IsFrame F →
      M'.GoodAt F (mCoordIdeal (basePart M'.blk (fstPt k₀' z))) → ∀ (hm : Matrix (Fin N) (Fin N) ℂ) (t : ℂ),
      IsBlockDiag j hm → hm.det ≠ 0 → (∀ i, M'.ExactAt F (τ, i) (fstPt k₀' z) hm) →
      M'.ExactAt F (τ, a) (sndPt k₀' z) (hm * (1 + Matrix.single cb ca t)) →
      eval z (map (Int.castRingHom ℂ) g) = t * (∏ i : Fin N, (if IsProperStep N j i then 1 else
        valAt M'.x (F.υ (τ, i)) (basePart M'.blk (fstPt k₀' z)) * mfac j a i hm) ^ xiCoef τ a (τ, i)) *
        eval z (map (Int.castRingHom ℂ) h))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)))
    (g0 : eval z (map (Int.castRingHom ℂ) g) ≠ 0) (h0 : eval z (map (Int.castRingHom ℂ) h) ≠ 0)
    {w₀ w₁ : (Σ k, ι k) → ℂ} (hw₀ : w₀ ∈ mcPts (mCoordIdeal y)) (hw₁ : w₁ ∈ mcPts (mCoordIdeal y))
    (i₀ : IsImg Cv (fstPt k₀' z) w₀) (i₁ : IsImg Cv (sndPt k₀' z) w₁) :
    ∃ (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (hm : Matrix (Fin N) (Fin N) ℂ) (t : ℂ),
      M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ w₀ ∧ SameOrbit z₁ w₁ ∧
      IsBlockDiag j hm ∧ hm.det ≠ 0 ∧ t ≠ 0 ∧ (∀ i, M.ExactAt F (τ, i) z₀ hm) ∧
      (∀ i, M.ExactAt F (τ, i) z₁ (hm * (1 + Matrix.single cb ca t))) ∧
      lognorm τ a k₀' g h CR.Re.ref z = normRhs M τ a F z₀ z₁ hm t := by
  have hz₀ := fst_mem hz
  have hz₁ := S'.snd_mem hy' hz
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ (CPts.base_mem M' hz₀)
  obtain ⟨z', oz', H, t, fl₀, fl₁⟩ := S'.data hz₀ hz₁ hF' hg'
  obtain ⟨u₀, ou₀, bu₀, ex₀⟩ := exists_exact M' fl₀
  obtain ⟨u₁, ou₁, bu₁, ex₁⟩ := exists_exact M' fl₁
  have bu : basePart M'.blk u₁ = basePart M'.blk u₀ := by rw [bu₀, bu₁, Pts.basePart_snd M' S'.hk]
  have e₁ : sndPt k₀' (joinPt k₀' u₀ u₁) = u₁ := by
    refine join_v₁ fun k hk m => ?_
    by_cases hkb : ∀ p, M'.blk p ≠ some k
    · exact (congrFun bu ⟨⟨k, hkb⟩, m⟩).symm
    · obtain ⟨⟨τ', i⟩, hp⟩ : ∃ p, M'.blk p = some k := by simpa using hkb
      rw [(ex₀ _).2 k hp m, (ex₁ _).2 k hp m, bu]
      by_cases e' : τ' = τ
      · subst e'
        have hi : i ≠ a := fun e => hk (by rw [e, S'.hk] at hp; exact (Option.some.inj hp).symm)
        simp only [Function.update_self, minor_transv M'.j_le S'.hb S'.hab S'.hca S'.hcb hi]
      · simp only [Function.update_of_ne e']
  have e₀ : fstPt k₀' (joinPt k₀' u₀ u₁) = u₀ := rfl
  have oj : SameOrbit (joinPt k₀' u₀ u₁) z := orbit_trans (join_orbit ou₀ ou₁) oz'
  obtain ⟨g1, h1, hl⟩ := lognorm_orbit hg hh hxi hdeg oj hz₀.1 hz₁.1 g0 h0
  have hj := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) oj hz
  have o₀ : SameOrbit u₀ (fstPt k₀' z) := e₀ ▸ fst_orbit oj
  have o₁ : SameOrbit u₁ (sndPt k₀' z) := e₁ ▸ snd_orbit oj
  have m₀ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₀ hz₀
  have m₁ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₁ hz₁
  have hb := CPts.base_mem M' m₀
  have hG' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk u₀)) := by rw [ideal_orbit (base_orbit o₀)]; exact hg'
  have hlc := LC _ hj F' hF' hG' (H τ) t (fl₀.2.1 τ).1 (fl₀.2.1 τ).2 (fun i => ex₀ (τ, i))
    (by rw [e₁]; simpa only [FlagModel.ExactAt, Function.update_self] using ex₁ (τ, a))
  rw [e₀] at hlc
  have ht : t ≠ 0 := fun e => g1 (by rw [hlc, e, zero_mul, zero_mul])
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨x₀, ox₀, bx₀, fx₀⟩ := i₀ u₀ o₀ F' F hF' hF hG' hG H (flag_of_exact M' (τ, a) fl₀.2.1 ex₀)
  obtain ⟨x₁, ox₁, bx₁, fx₁⟩ := i₁ u₁ o₁ F' F hF' hF (by rw [bu]; exact hG') (by rw [bu]; exact hG) _
    (flag_of_exact M' (τ, a) fl₁.2.1 ex₁)
  obtain ⟨z₀, oz₀, bz₀, ez₀⟩ := exists_exact M fx₀
  obtain ⟨z₁, oz₁, bz₁, ez₁⟩ := exists_exact M fx₁
  rw [← bz₀] at bx₀
  rw [← bz₁] at bx₁
  have hI := CoordinateConeArithVar.isMultiHomogIdeal y
  have M₀ := fun p => CR.metric _ m₀ _ (mem_mcPts_of_sameOrbit hI (orbit_trans oz₀ ox₀) hw₀) F' F hF' hF hG' hG bx₀ p _
    (fl₀.2.1 p.1).1 (fl₀.2.1 p.1).2 (ex₀ p) (ez₀ p)
  have M₁ := fun p => CR.metric _ m₁ _ (mem_mcPts_of_sameOrbit hI (orbit_trans oz₁ ox₁) hw₁) F' F hF' hF
    (by rw [bu]; exact hG') (by rw [bu]; exact hG) bx₁ p _ (fl₁.2.1 p.1).1 (fl₁.2.1 p.1).2 (ex₁ p) (ez₁ p)
  rw [bu] at bx₁ ez₁
  have hT := FibreCount.trans_unit Cv hb hF' hF hG' hG τ
  have hGz : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [ideal_orbit bx₀]; exact hG
  have hbz := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) bx₀ hbv
  refine ⟨z₀, z₁, F, Cv.trans F' F (basePart M'.blk u₀) τ * H τ, t, hF, hGz, orbit_trans oz₀ ox₀, orbit_trans oz₁ ox₁,
    (fx₀.2.1 τ).1, (fx₀.2.1 τ).2, ht, fun i => ez₀ (τ, i),
    fun i => by simpa only [FlagModel.ExactAt, Function.update_self, Matrix.mul_assoc] using ez₁ (τ, i), ?_⟩
  have A' := fun i => log_A M' hb hG' τ a i (fl₀.2.1 τ).1 (fl₀.2.1 τ).2
  have A := fun i => log_A M hbz hGz τ a i (fx₀.2.1 τ).1 (fx₀.2.1 τ).2
  have hU' : ∀ p, M'.upsLog F' p u₁ = M'.upsLog F' p u₀ := fun p => by simp only [FlagModel.upsLog, bu]
  have hU : ∀ p, M.upsLog F p z₁ = M.upsLog F p z₀ := fun p => by
    simp only [FlagModel.upsLog, valAt_orbit bx₀ hbv, valAt_orbit bx₁ hbv]
  have hs := sum_detFac M.j_le S'.hb S'.hab hT.1 hT.2
  have hx : ∀ i, xiCoef () a ((), i) = xiCoef τ a (τ, i) := fun i => by simp [xiCoef]
  simp only [hx] at hs
  rw [← hl, lognorm, hlc, e₀, e₁, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (left_ne_zero_of_mul (hlc ▸ g1)))
    (norm_ne_zero_iff.2 h1), log_fac τ a ht fun i => (A' i).1]
  show _ = Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) *
      mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ * H τ)) ^ xiCoef τ a (τ, i)‖ + _
  rw [log_fac τ a ht fun i => (A i).1, sum_xi_prod, sum_xi_prod]
  simp only [fun i => (A' i).2, fun i => (A i).2]
  have fin : ∀ i, (xiCoef τ a (τ, i) : ℝ) * (M'.upsLog F' (τ, i) u₀ + if IsProperStep N j i then 0 else
        Real.log ‖mfac j a i (H τ)‖) + (1 / 2) * ((xiCoef τ a (τ, i) : ℝ) *
        (Real.log ((CR.Re.ref (τ, i)).h u₀) + Real.log ((CR.Re.ref (τ, i)).h u₁))) =
      (xiCoef τ a (τ, i) : ℝ) * (M.upsLog F (τ, i) z₀ + if IsProperStep N j i then 0 else
        Real.log ‖mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ * H τ)‖) + (1 / 2) * ((xiCoef τ a (τ, i) : ℝ) *
        (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) +
      (xiCoef τ a (τ, i) : ℝ) * (Real.log ‖detFac j i (Cv.trans F' F (basePart M'.blk u₀) τ)‖ -
        if IsProperStep N j i then 0 else Real.log ‖mfac j a i (Cv.trans F' F (basePart M'.blk u₀) τ)‖) := fun i => by
    have r₀ := M₀ (τ, i)
    have r₁ := M₁ (τ, i)
    rw [hU, hU', bu] at r₁
    rw [mfac_mul a i _ (fl₀.2.1 τ).1, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (mfac_ne a i hT.1 hT.2))
      (norm_ne_zero_iff.2 (mfac_ne a i (fl₀.2.1 τ).1 (fl₀.2.1 τ).2))]
    split_ifs
    · linear_combination (1 / 2 * (xiCoef τ a (τ, i) : ℝ)) * (r₀ + r₁)
    · linear_combination (1 / 2 * (xiCoef τ a (τ, i) : ℝ)) * (r₀ + r₁)
  have tot := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N)) = _) fun i _ => fin i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs] at tot
  linarith

end PositivityTheory.Xgp.c_sqsys
