module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LeviDiagonalOfIsPeriodChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBundleMetricLine

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemTop
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

noncomputable section

namespace PositivityTheory.Xgp.c_smooth

theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P)
    (hcov : ∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) :
    ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ),
      IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧
        ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.exists_res (K := K) (ι := ι) (P := P) (e := e) hP hnd hcov

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb hd keep Kk _ ιk _ κ v hb hrng
  obtain ⟨e, he, ⟨ε⟩⟩ : ∃ e, e = n + Nat.card (PIdx j keep) ∧ Nonempty (Fin n ⊕ PIdx j keep ≃ Fin e) :=
    ⟨_, rfl, ⟨(Equiv.sumCongr (Equiv.refl _) (Finite.equivFin _)).trans finSumFinEquiv⟩⟩
  have hP : IsMultiHomogIdeal (mCoordIdeal (y ∘ v)) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
  have hnd : ¬ (⊤ : Ideal (MRing ιk)) ≤ mCoordIdeal (y ∘ v) := fun h =>
    (RingHom.ker_isPrime _ : (mCoordIdeal (y ∘ v)).IsPrime).ne_top (top_le_iff.mp h)
  have hcov := GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover.main K ι Φ y Ψ N j M n Rb keep Kk ιk κ v hb hrng
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h →
      ∃ C : OrbitChart (mCoordIdeal (y ∘ v)) e, C.D = pD ε V ∧ C.φ = pPhi M F keep v bl h ε ∧
        C.O = pO M Rb keep v F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.1.1
    have hh := GlobalTheory.T.frameData_local_resolution_regular K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hr := GlobalTheory.T.frameData_local_integrability K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ho := GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hO := GlobalTheory.T.frameData_local_degree_bound K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hb' := GlobalTheory.T.frameData_local_norm_comparison K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ht := GlobalTheory.T.frameData_local_norm_bound K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hi := GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm.chart_immersion K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    exact ⟨{ D := pD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := pPhi M F keep v bl h ε
             holo := hh
             mem := fun w hw => (hr w hw).1.1
             O := pO M Rb keep v F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := pRho M Rb keep v F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := exists_res (e := e) hP hnd (fun z hz => by
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
    obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
    exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = pD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (pPhi M F keep v bl h ε (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩
  have hob := (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hb hrng).2

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (pBase M v (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    refine ⟨(Rb.A.chart kb).symm (pB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := hob _ _ (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h → ψ.target = pD ε V → x ∈ ψ.source →
      SameOrbit (pPhi M F keep v bl h ε (ψ x)) (R.lift x x) →
      pr x = (Rb.A.chart kb).symm (pB ε (ψ x)) ∧ pr x ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    have h1 : SameOrbit (bl (pB ε (ψ x))) (pBase M v (R.lift x x)) := by
      have := hob _ _ hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (pB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_top _) h2
    have hwt : pB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨rfl, (Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  have hlast : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hψ, hT, hx, hs⟩ := key x
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun a b e' => Sum.inl_injective (ε.injective e')⟩, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨-, h1, h2⟩ := hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')
    exact ⟨h1, h2⟩
  refine ⟨e, R, ?_, pr, ?_, ?_, hlast⟩
  · intro hall
    rw [he, GlobalTheory.T.card_pIdx_eq_choose Ψ N j keep M.j_le hall, hd]
  · refine GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord e n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨ψ, kb, σ, h1, h2, h3⟩ := hlast x
    exact ⟨ψ, kb, σ, h1, h2, h3⟩
  · intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    obtain ⟨z₀, hz₀, hzv, hzb⟩ := GlobalTheory.T.frameData_local_degree_estimate K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    obtain ⟨hpe, -, -⟩ := hcoord x F kb V bl r h ψ hc hT hx (hs x hx)
    obtain ⟨c, hc0, hce⟩ := orbit_symm (hs x hx)
    let c' : K → ℂ := fun k => if hk : ∃ k', κ k' = k then c hk.choose else 1
    have hc'0 : ∀ k, c' k ≠ 0 := fun k => by
      simp only [c']
      split_ifs
      · exact hc0 _
      · exact one_ne_zero
    have hc'κ : ∀ k', c' (κ k') = c k' := fun k' => by
      have hk : ∃ k'', κ k'' = κ k' := ⟨k', rfl⟩
      simp only [c']
      rw [dite_eq_left hk, hb.1 hk.choose_spec]
    have hyP : IsMultiHomogIdeal (mCoordIdeal y) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
    refine ⟨fun p => c' p.1 * z₀ p, mcPts_smul hyP c' hc'0 hz₀, ?_, ?_⟩
    · funext q
      have e1 : z₀ (v q) = pPhi M F keep v bl h ε (ψ x) q := congrFun hzv q
      have e2 := congrFun hce q
      show c' (v q).1 * z₀ (v q) = _
      rw [e2, e1, hb.2.2.1 q, hc'κ]
    · have h1 : SameOrbit (fun q => c' q.1.1 * basePart M.blk z₀ q) (bl (pB ε (ψ x))) := by
        rw [hzb]
        exact ⟨fun k => c' k.1, fun k => hc'0 _, rfl⟩
      have h2 : (basePart M.blk fun p => c' p.1 * z₀ p) = fun q => c' q.1.1 * basePart M.blk z₀ q := rfl
      rw [h2, hpe]
      exact orbit_trans h1 (orbit_symm (hB.2.2.2.2 _ hw).2.2.2)

end PositivityTheory.Xgp.c_smooth
end
end

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJOneSelf
noncomputable section

namespace PositivityTheory.Xgp.plurisubharmonic_charts

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW.holoOn_comp (e' := e') (Y := Y) (B := B) (h := h) (V := V) (g := g) hh hg

theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  refine ⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane,
    ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane,
    ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖,
    fun k u hu => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

end Holo

theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  have hu : IsUnit H.det := hd.isUnit
  have h1 := ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu] at h1
  have h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold detFac
    split_ifs <;> simp [minorIJ_one_self]
  intro h0
  rw [h2, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := PositivityTheory.Xgp.per_diag.levi_diagonal_of_isPeriodChart e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end PositivityTheory.Xgp.plurisubharmonic_charts
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_fl_an

open GlobalTheory.CompanionTheory.Ar.PB.FA GlobalTheory.CompanionTheory.Ar.PB.StepW
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem onStep_fs (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : M.OnStep p (fsHerm ι (M.dy p)) := by
  intro z z' h1 h2
  rw [fsHerm_h, fsHerm_h, refNorm, refNorm]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : ∀ p', M.blk p' ≠ some k
  · have : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := fun i => congrFun h1 ⟨⟨k, hk⟩, i⟩
    simp only [this]
  · by_cases hk' : M.blk p = some k
    · simp only [h2 k hk']
    · have : M.dy p k = 0 := by
        unfold FlagModel.dy
        rw [dite_eq_right hk, if_neg hk']
      simp [this]

theorem isPsh_of_univ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {P : LocPot X}
    (hU : ∀ x, x ∈ U) (h : IsPshOn A U P) : IsPsh A P :=
  fun x j w hw v => h x j w ⟨hw.1, hw.2, hU _⟩ v

theorem step_member [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (hbd : bdry BM.s = ∅) (hh : ∀ p, BM.hom p = fsHerm ι (M.dy p))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (pL : IsPotential R.A (BM.L.pullback pr hp.1))
    (sL : IsSection R.A (BM.L.pullback pr hp.1) fun x y => BM.s (pr x) (pr y))
    (nL : IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m fun k => pr ⁻¹' BM.W k)
    (p : Ψ × Fin N) :
    ∃ C₅ : ℝ, IsStepMember BM R pr hp p 0 (fun _ => 0) (fun _ => fsHerm ι (M.dy p)) C₅ C₅
      (Real.exp (-Real.exp 1)) := by
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ e R
  have hfsa : IsSmoothHerm (fsHerm ι (M.dy p)) := FlagHeightMultilinear.isSmoothHerm_fsHerm _
  have hU : ∀ x, x ∈ (bdry fun x y => BM.s (pr x) (pr y))ᶜ := fun x hx => by
    have : pr x ∈ bdry BM.s := hx
    rw [hbd] at this
    exact this
  have hpts : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ id = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) :=
    fun x => ⟨R.lift x x, R.mem x x (R.mem_U x), rfl, hb x⟩
  have hyp : IsStepHyp M BM p id id R pr := ⟨isBlockMap_id, fun k _ => ⟨k, rfl⟩, hp, hpts⟩
  have h0 : stepPh M BM p id R pr = 0 := by
    funext x
    unfold stepPh
    split_ifs
    · rw [stepGap, hh, sub_self]; rfl
    · rfl
  have hps := PositivityTheory.Xgp.plurisubharmonic_charts.isPshOn_stepPot K ι Φ y Ψ N j M n BM p K ι id id e R pr hp
    (GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p K ι id id e R pr hyp)
  rw [h0] at hps
  have hps' : IsPsh R.A (potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (0 : R.X → ℝ)) := isPsh_of_univ hU hps
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  obtain ⟨C₀, s0, r0, c0⟩ := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e R.X R.A
    (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn (hA _ hfs) hΘ).2.2 _ 0 (hA _ hfsa) hsm0 hps'
  refine ⟨C₀, s0, r0, c0, fun _ => rfl, fun _ => onStep_fs M p, fun t _ _ => ⟨hfsa, fun x => by simp⟩,
    fun x _ => by rw [hh]; simp, fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩, fun hc t => ⟨?_, hps', rfl⟩⟩
  have flat := GlobalTheory.CompanionTheory.Ar.PB.FA.Flat.flat_off_boundary K ι Φ y Ψ N j M n BM p hc K ι id id isBlockMap_id
    (fun k _ => ⟨k, rfl⟩) e R pr hp 0 hpts (fun x _ z _ _ => by rw [hh]; simp)
  exact isPsh_of_univ hU flat.2

theorem flagAn_of_res [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n : ℕ} (d : ℕ) (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ (d + 1))
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (harith : IsArithVar (mCoordIdeal y) (d + 2))
    (hbd : bdry BM.s = ∅) (hh : ∀ p, BM.hom p = fsHerm ι (M.dy p))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (hch : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin (d + 1) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 1)),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))) :
    ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  obtain ⟨pL, sL, nL, B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection (d + 1) n R.X BM.Rb.X R.A BM.Rb.A BM.Bat pr hp BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ (d + 1) R
  have hfsa : ∀ a : K → ℤ, IsSmoothHerm (fsHerm ι a) := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm
  choose C₅ hm using fun p => step_member M BM R pr hp hbd hh hb pL sL nL p
  let ph : Ψ × Fin N → R.X → ℝ := fun _ => 0
  let phT : Ψ × Fin N → ℝ → R.X → ℝ := fun _ _ => 0
  let line : Ψ × Fin N → ℝ → HermLine ι := fun p _ => fsHerm ι (M.dy p)
  let C := C₅
  let t₀ : Ψ × Fin N → ℝ := fun _ => Real.exp (-Real.exp 1)
  obtain ⟨m₁, m₂, m₃⟩ := GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members (d + 1) R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn
    (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hΘ x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfs) hsm0 hpsh0
  obtain ⟨D₅, hD₅⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim C₀ C₅
  obtain ⟨D, hD⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim |C₀| fun p => |C p|
  obtain ⟨T, hT0, hT⟩ := common_scale (fun o : Option (Option (Ψ × Fin N)) =>
    o.elim (Real.exp (-1)) fun o' => o'.elim (Real.exp (-Real.exp 1)) t₀) (by
      rintro (_ | _ | p)
      · exact Real.exp_pos _
      · exact Real.exp_pos _
      · exact (hm p).2.1.1)
  have hT1 : T ≤ Real.exp (-1) := hT none
  have hm' : ∀ p, IsStepMember BM R pr hp p (ph p) (phT p) (line p) D₅ D T := fun p =>
    IsStepMember.mono m₁ m₂ (hm p) (hD₅ (some p)) (hD (some p)) hT0 (hT (some (some p))) hT1
  have s0' := m₁ _ _ _ _ (hD₅ none) s0
  have r0' := m₂ _ _ _ _ _ _ _ (hD none) hT0 (hT (some none)) hT1 r0 (hA _ hfs)
  let S : AnSys (d + 1) (Option (Ψ × Fin N)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm ι fun _ => 1)
      L := BM.L.pullback pr hp.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := hn
      th := fun o => o.elim (potOf R (fsHerm ι fun _ => 1)) fun p => potOf R (fsHerm ι (M.dy p))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := D₅
      C := D
      t₀ := T
      sing := by
        rintro (_ | p)
        · exact s0'
        · exact (hm' p).1
      reg := by
        rintro (_ | p)
        · exact r0'
        · exact (hm' p).2.1
      c2 := by
        rintro (_ | p)
        · exact c0
        · exact (hm' p).2.2.1 }
  let Re : Realis S (mCoordIdeal y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := degree_id_self R.A
      ref := fun o => o.elim (fsHerm ι fun _ => 1) fun p => fsHerm ι (M.dy p)
      ref_smooth := by
        rintro (_ | p)
        · exact hfs
        · exact hfsa _
      ref_pot := by
        rintro (_ | p) <;>
        exact fun x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o t => o.elim (fsHerm ι fun _ => 1) fun p => line p t
      line_deg := by
        rintro (_ | p) t
        · rfl
        · exact (hm' p).2.2.2.1 t
      line_smooth := by
        rintro (_ | p) t h0 h1
        · exact hfs
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).1
      line_eq := by
        rintro (_ | p) t h0 h1 x
        · exact (add_zero _).symm
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).2 x }
  refine ⟨{ S := S, Re := Re, J_top := rfl, deg_one := rfl, br_empty := rfl, ref_some := fun _ => rfl, ref_none := rfl,
            line_none := fun _ => rfl, ph_none := ⟨rfl, fun _ => rfl⟩, pos_none := ?_, pr := pr, pr_holo := hp,
            pr_eq := hb, L_eq := rfl, s_eq := rfl, hom_eq := ?_, step := ?_, step_ph := ?_, flat := ?_ }, fun _ _ => rfl⟩
  · refine ⟨1, one_pos, fun t x jj z _ w => ?_⟩
    have e1 : (S.potT none t + S.Θ.rsmul (-1)).φ x ∘ (S.A.chart jj).symm = fun _ => (0 : ℝ) := by
      funext u
      show ((potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ)) + (-1) * (potOf R (fsHerm ι fun _ => 1)).φ x _ = 0
      ring
    rw [e1]
    simp [levi]
  · exact fun p x hx => (hm' p).2.2.2.2.2.2.1 x hx
  · exact fun p t => (hm' p).2.2.2.2.1 t
  · exact fun p x x' h1 h2 => (hm' p).2.2.2.2.2.2.2.1 x x' h1 h2
  · exact fun p h1 t => (hm' p).2.2.2.2.2.2.2.2 h1 t

end PositivityTheory.Xgp.c_fl_an

end

theorem PositivityTheory.Xgp.t_c_fl_an : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → bdry BM.s = ∅ → (∀ p, BM.hom p = fsHerm ι (M.dy p)) → ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM harith hd hbd hh
  obtain ⟨e, R, he, pr, hp, hpts, hch⟩ := PositivityTheory.Xgp.c_smooth.main K ι Φ y Ψ N j M n (d + 1) BM.Rb hd (fun _ => True) K ι id id
    isBlockMap_id (fun k => ⟨fun _ => by
      by_cases h : ∀ p', M.blk p' ≠ some k
      · exact Or.inl h
      · push Not at h
        obtain ⟨p, hp⟩ := h
        exact Or.inr ⟨p, trivial, hp⟩, fun _ => ⟨k, rfl⟩⟩)
  obtain rfl := he fun _ => trivial
  refine PositivityTheory.Xgp.c_fl_an.flagAn_of_res M d BM R pr hp harith hbd hh (fun x => ?_) hch
  obtain ⟨z, -, hz, ho⟩ := hpts x
  have hz' : z = R.lift x x := hz
  rw [← hz']
  exact ho
