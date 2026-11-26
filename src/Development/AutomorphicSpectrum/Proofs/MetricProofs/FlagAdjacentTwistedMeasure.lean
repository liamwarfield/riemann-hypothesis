module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.EqOfOrbitNormal
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem holoOn_congr' {V : Set X} {f g : X → ℂ} (hV : IsOpen V) (h : A.HoloOn V f)
    (hfg : ∀ w ∈ V, g w = f w) : A.HoloOn V g := fun j =>
  (h j).congr ((A.chart j).isOpen_inter_preimage_symm hV) fun u hu => (hfg _ hu.2).symm

theorem holoOn_mono' {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_add' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x + g x :=
  fun j z hz => (hf j z hz).add (hg j z hz)

theorem holoOn_const' (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_minor' {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    exact holoOn_sum' _ fun s => holoOn_mul' (holoOn_const' _ _) (holoOn_prod' _ fun a => h _ _)
  · simp only [dif_neg e]
    exact holoOn_const' _ _

theorem holoOn_of_chart {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ)
    {g : (Fin e → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target) : A.HoloOn ψ.source fun w => g (ψ w) :=
  fun j u hu => AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hu.2)) ((hψ j).1 u hu)

theorem holoOn_transv {N : ℕ} {V : Set X} {h : X → Matrix (Fin N) (Fin N) ℂ} {t : X → ℂ}
    (hh : ∀ a b, A.HoloOn V fun y => h y a b) (ht : A.HoloOn V t) (cb ca : Fin N) (a b : Fin N) :
    A.HoloOn V fun y => (h y * (1 + Matrix.single cb ca (t y))) a b := by
  simp only [Matrix.mul_apply]
  refine holoOn_sum' _ fun c => holoOn_mul' (hh _ _) ?_
  simp only [Matrix.add_apply, Matrix.single_apply]
  refine holoOn_add' (holoOn_const' _ _) ?_
  by_cases e : cb = c ∧ ca = b
  · simpa only [if_pos e] using ht
  · simpa only [if_neg e] using holoOn_const' V 0

end Holo

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem lift_fst {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (fstPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : K → ℂ, (∀ k, b k ≠ 0) ∧ ∀ q : Σ k, ι k, L' ⟨some q.1, q.2⟩ = b q.1 * z q := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨fun k => d (some k) * (c k)⁻¹, fun k => mul_ne_zero (hd _) (inv_ne_zero (hc k)), fun q => ?_⟩
  have hq : c q.1 ≠ 0 := hc q.1
  show d (some q.1) * L ⟨some q.1, q.2⟩ = d (some q.1) * (c q.1)⁻¹ * (c q.1 * L ⟨some q.1, q.2⟩)
  field_simp

theorem lift_snd {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (sndPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ m : ι k₀, L' ⟨none, m⟩ = b * z ⟨k₀, m⟩ := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨d none * (c k₀)⁻¹, mul_ne_zero (hd _) (inv_ne_zero (hc k₀)), fun m => ?_⟩
  have hq : c k₀ ≠ 0 := hc k₀
  show d none * L ⟨none, m⟩ = d none * (c k₀)⁻¹ * (c k₀ * L (v₁ k₀ ⟨k₀, m⟩))
  rw [v₁_self]
  field_simp

theorem basePart_orbit' {σ : Type} {blk : σ → Option K} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem eq_of_orbit_normal {κ : Type} {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z')
    (c₀ : ∀ k, ρ k) (h₁ : ∀ k, z ⟨k, c₀ k⟩ = 1) (h₂ : ∀ k, z' ⟨k, c₀ k⟩ = 1) : z = z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc1 : ∀ k, c k = 1 := fun k => by
    have := h₁ k
    simp only [h₂ k, mul_one] at this
    exact this
  funext q
  simp only [hc1, one_mul]

end Orbit

theorem holoOn_step {N e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X} (hV : IsOpen V)
    {S : Finset (Fin N)} {f : X → ℂ} {v : Finset (Fin N) → X → ℂ} {h : X → Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ I, A.HoloOn V (v I)) (hh : ∀ a b, A.HoloOn V fun y => h y a b)
    (hf : ∀ w ∈ V, f w = ∑ I, v I w * minorIJ (h w) I S) : A.HoloOn V f :=
  holoOn_congr' hV (holoOn_sum' _ fun I => holoOn_mul' (hv I) (holoOn_minor' hh I S)) hf

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hA x ψ kb σ i₀ F H hx hw
  obtain ⟨hcc, hfr, -, -, hHan, hpts⟩ := hw
  have hex : ∀ w, ∃ z₀ z₁ : (Σ k, ι k) → ℂ, w ∈ ψ.source →
      SameOrbit z₀ (fstPt k₀ (RW.lift w w)) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift w w)) ∧
        ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₀ (H τ' (ψ w)) ∧
          ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) z₁
            (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w)) := fun w => by
    by_cases hwS : w ∈ ψ.source
    · obtain ⟨-, -, z₀, z₁, h⟩ := hpts w hwS
      exact ⟨z₀, z₁, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hwS⟩
  choose z₀ z₁ hz using hex
  have hpb := fun w (hwS : w ∈ ψ.source) => GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hA w
    (z₀ w) (z₁ w) (hz w hwS).1 (hz w hwS).2.1
  have hn₀ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₀ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).1.1
  have hn₁ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₁ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).2.1
  have hbeq : ∀ w ∈ ψ.source, basePart M.blk (z₁ w) = basePart M.blk (z₀ w) := fun w hwS =>
    eq_of_orbit_normal (hpb w hwS).2.1 F.c (hn₁ w hwS) (hn₀ w hwS)
  obtain ⟨W, hWdef⟩ : ∃ W, W = ψ.source ∩ RW.U x := ⟨_, rfl⟩
  have hWo : IsOpen W := hWdef ▸ ψ.open_source.inter (RW.isOpen_U x)
  have hxW : x ∈ W := hWdef ▸ ⟨hx, RW.mem_U x⟩
  have hWS : W ⊆ ψ.source := hWdef ▸ Set.inter_subset_left
  have hWU : W ⊆ RW.U x := hWdef ▸ Set.inter_subset_right
  have hlift : ∀ w ∈ W, SameOrbit (RW.lift x w) (RW.lift w w) := fun w hwW =>
    RW.compat x w w ⟨hWU hwW, RW.mem_U w⟩
  have hb₀ := fun w (hwW : w ∈ W) => lift_fst (hz w (hWS hwW)).1 (hlift w hwW)
  have hb₁ := fun w (hwW : w ∈ W) => lift_snd (hz w (hWS hwW)).2.1 (hlift w hwW)
  have hbase : ∀ (k : NonPluckerBlocks M.blk) (m : ι k.1), RW.A.HoloOn W fun w => z₀ w ⟨k.1, m⟩ := fun k m => by
    refine StepW.ValHolo.holoOn_div_congr RW.A hWo (f := fun w => RW.lift x w ⟨some k.1, m⟩)
      (g := fun w => RW.lift x w ⟨some k.1, F.c k⟩) (holoOn_mono' (RW.holo x _) hWU)
      (holoOn_mono' (RW.holo x _) hWU) ?_ ?_
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      exact h1 ▸ hd k.1
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      have h3 := hq ⟨k.1, m⟩
      show z₀ w ⟨k.1, m⟩ = RW.lift x w ⟨some k.1, m⟩ / RW.lift x w ⟨some k.1, F.c k⟩
      rw [h3, h1, mul_div_cancel_left₀ _ (hd k.1)]
  have hbH : ∀ q, RW.A.HoloOn W fun w => basePart M.blk (z₀ w) q := fun q => hbase q.1 q.2
  have hid : mCoordIdeal (basePart M.blk (z₀ x)) = mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x x))) := by
    obtain ⟨c, hc, hce⟩ := basePart_orbit' (blk := M.blk) (hz x hx).1
    rw [hce]
    exact StepW.TorusAct.mCoordIdeal_torus c hc _
  have hreg : ∀ q I, RegAt M.x (mCoordIdeal (basePart M.blk (z₀ x))) (F.u q I) := fun q I => by
    rw [hid]
    exact ((hpts x hx).2.1.2.1 q I).1
  have hval := fun q I => StepW.ValHolo.holoOn_valAt _ _ _ M.x (F.u q I) e RW.X RW.A W
    (fun w => basePart M.blk (z₀ w)) x hWo hxW hbH (fun w hwW => (hpb w (hWS hwW)).1) (hreg q I)
  choose Wv hWv₁ hWv₂ hWv₃ hWv₄ using hval
  obtain ⟨V₁, hV₁def⟩ : ∃ V₁, V₁ = W ∩ ⋂ q, ⋂ I, Wv q I := ⟨_, rfl⟩
  have hV₁o : IsOpen V₁ := hV₁def ▸ hWo.inter
    (isOpen_iInter_of_finite fun q => isOpen_iInter_of_finite fun I => hWv₁ q I)
  have hxV₁ : x ∈ V₁ := hV₁def ▸ ⟨hxW, Set.mem_iInter.2 fun q => Set.mem_iInter.2 fun I => hWv₂ q I⟩
  have hV₁W : V₁ ⊆ W := hV₁def ▸ Set.inter_subset_left
  have hV₁S : V₁ ⊆ ψ.source := hV₁W.trans hWS
  have hvV : ∀ q I, RW.A.HoloOn V₁ fun w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)) := fun q I =>
    holoOn_mono' (hWv₄ q I) fun w hwV => by
      rw [hV₁def] at hwV
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hwV.2 q) I
  have hHH : ∀ τ' r s, RW.A.HoloOn ψ.source fun w => H τ' (ψ w) r s := fun τ' r s =>
    holoOn_of_chart hcc (hHan τ' r s)
  have hti : RW.A.HoloOn ψ.source fun w => ψ w i₀ := holoOn_of_chart hcc (g := fun v => v i₀)
    fun v _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i₀).analyticAt v
  have hzH : ∀ q, RW.A.HoloOn V₁ fun w => z₀ w q := fun q => by
    by_cases hq : ∀ p, M.blk p ≠ some q.1
    · exact holoOn_mono' (hbase ⟨q.1, hq⟩ q.2) hV₁W
    · push_neg at hq
      obtain ⟨⟨τ', i⟩, hp⟩ := hq
      exact holoOn_step hV₁o (v := fun I w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)))
        (h := fun w => H τ' (ψ w)) (S := stepCols N j i) (fun I => hvV q I)
        (fun r s => holoOn_mono' (hHH τ' r s) hV₁S)
        fun w hwV => ((hz w (hV₁S hwV)).2.2 τ' i).1.2 q.1 hp q.2
  have hz₁H : ∀ m : ι k₀, RW.A.HoloOn V₁ fun w => z₁ w ⟨k₀, m⟩ := fun m => by
    refine holoOn_step hV₁o (v := fun I w => valAt M.x (F.u ⟨k₀, m⟩ I) (basePart M.blk (z₀ w)))
      (h := fun w => H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀))) (S := stepCols N j a)
      (fun I => hvV _ I)
      (fun r s => holoOn_transv (fun r s => holoOn_mono' (hHH τ r s) hV₁S) (holoOn_mono' hti hV₁S) cb ca r s)
      fun w hwV => ?_
    have h1 := ((hz w (hV₁S hwV)).2.2 τ a).2.2 k₀ hk m
    rw [if_pos rfl, hbeq w (hV₁S hwV)] at h1
    exact h1
  choose mk hmk using (hpb x hx).2.2.1
  obtain ⟨m₁, hm₁⟩ := (hpb x hx).2.2.2 k₀
  obtain ⟨V, hVdef⟩ : ∃ V, V = (⋂ k, (V₁ ∩ {w | z₀ w ⟨k, mk k⟩ ≠ 0})) ∩ (V₁ ∩ {w | z₁ w ⟨k₀, m₁⟩ ≠ 0}) :=
    ⟨_, rfl⟩
  have hVo : IsOpen V := hVdef ▸ (isOpen_iInter_of_finite fun k =>
    StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hzH ⟨k, mk k⟩)).inter
      (StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hz₁H m₁))
  have hxV : x ∈ V := hVdef ▸ ⟨Set.mem_iInter.2 fun k => ⟨hxV₁, hmk k⟩, hxV₁, hm₁⟩
  have hVV₁ : V ⊆ V₁ := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.1
  have hV0 : ∀ w ∈ V, ∀ k, z₀ w ⟨k, mk k⟩ ≠ 0 := fun w hwV k => by
    rw [hVdef] at hwV
    exact (Set.mem_iInter.1 hwV.1 k).2
  have hV1 : ∀ w ∈ V, z₁ w ⟨k₀, m₁⟩ ≠ 0 := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.2
  have hVW : V ⊆ W := hVV₁.trans hV₁W
  have hVS : V ⊆ ψ.source := hVW.trans hWS
  obtain ⟨c, hcs, hcn⟩ : ∃ c : Option K → RW.X → ℂ,
      (∀ k w, c (some k) w = RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩) ∧
        ∀ w, c none w = RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩ :=
    ⟨fun o w => o.elim (RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩)
      fun k => RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩, fun _ _ => rfl, fun _ => rfl⟩
  have hcs' : ∀ w ∈ V, ∀ (d : K → ℂ), (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = d q.1 * z₀ w q) →
      ∀ k, c (some k) w = d k := fun w hwV d hq k => by
    rw [hcs]
    have h1 := hq ⟨k, mk k⟩
    exact h1 ▸ mul_div_cancel_right₀ _ (hV0 w hwV k)
  have hcn' : ∀ w ∈ V, ∀ d : ℂ, (∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = d * z₁ w ⟨k₀, m⟩) → c none w = d :=
    fun w hwV d hq => by
      rw [hcn, hq m₁]
      exact mul_div_cancel_right₀ _ (hV1 w hwV)
  refine ⟨V, z₀, z₁, c, hVo, hxV, hVS, hVW.trans hWU, fun q => holoOn_mono' (hzH q) hVV₁, ?_, ?_, ?_⟩
  · rintro (_ | k)
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hz₁H m₁) hVV₁) hV1 fun w _ => hcn w
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hzH ⟨k, mk k⟩) hVV₁) (fun w hwV => hV0 w hwV k) fun w _ => hcs k w
  · rintro (_ | k) w hwV
    · obtain ⟨d, hd, hq⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq]
      exact hd
    · obtain ⟨d, hd, hq⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq k]
      exact hd k
  · intro w hwV
    have hwS := hVS hwV
    refine ⟨(hz w hwS).1, (hz w hwS).2.1, (hz w hwS).2.2, fun q hq₀ => ?_, fun q => ?_, fun m => ?_⟩
    · by_cases hq : ∀ p, M.blk p ≠ some q.1
      · exact congrFun (hbeq w hwS) ⟨⟨q.1, hq⟩, q.2⟩
      · push_neg at hq
        obtain ⟨⟨τ', i⟩, hp⟩ := hq
        have e₀ := ((hz w hwS).2.2 τ' i).1.2 q.1 hp q.2
        have e₁ := ((hz w hwS).2.2 τ' i).2.2 q.1 hp q.2
        refine e₁.trans (Eq.trans ?_ e₀.symm)
        rw [hbeq w hwS]
        refine Finset.sum_congr rfl fun I _ => ?_
        congr 1
        by_cases ht : τ' = τ
        · subst ht
          rw [if_pos rfl]
          have hia : i ≠ a := fun hia => hq₀ (by
            subst hia
            exact Option.some_injective _ (hp.symm.trans hk))
          exact GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb M.j_le hb hab hca hcb _ _ i hia I
        · rw [if_neg ht]
    · obtain ⟨d, hd, hq'⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq' q.1]
      exact hq' q
    · obtain ⟨d, hd, hq'⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq']
      exact hq' m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPoint
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor

section Holo

variable {e : ℕ} {S : Type} [TopologicalSpace S]

theorem holoOn_mono (A : FinHolAtlas e S) {U V : Set S} {f : S → ℂ} (h : A.HoloOn V f) (hU : U ⊆ V) :
    A.HoloOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hU))

theorem holoOn_const (A : FinHolAtlas e S) (U : Set S) (c : ℂ) : A.HoloOn U fun _ => c := fun _ _ _ =>
  analyticAt_const

theorem holoOn_mul (A : FinHolAtlas e S) {U : Set S} {f g : S → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun w => f w * g w := fun j u hu => (hf j u hu).mul (hg j u hu)

theorem holoOn_zpow (A : FinHolAtlas e S) {U : Set S} {f : S → ℂ} (hf : A.HoloOn U f)
    (h0 : ∀ w ∈ U, f w ≠ 0) (n : ℤ) : A.HoloOn U fun w => f w ^ n := fun j u hu =>
  (hf j u hu).zpow (h0 _ hu.2)

theorem holoOn_prod (A : FinHolAtlas e S) {U : Set S} {κ : Type} (s : Finset κ) {f : κ → S → ℂ}
    (hf : ∀ i ∈ s, A.HoloOn U (f i)) : A.HoloOn U fun w => ∏ i ∈ s, f i w := by
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h := holoOn_mul A (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h

theorem holoOn_minor (A : FinHolAtlas e S) {U : Set S} {N : ℕ} {H : S → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ r s, A.HoloOn U fun w => H w r s) (I J : Finset (Fin N)) :
    A.HoloOn U fun w => minorIJ (H w) I J := by
  have h := StepW.ValHolo.holoOn_eval A (b := fun w (q : Fin N × Fin N) => H w q.1 q.2) (fun q => hH q.1 q.2)
    (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)
  have e : (fun w => minorIJ (H w) I J) = fun w => eval (fun q : Fin N × Fin N => H w q.1 q.2)
      (map (Int.castRingHom ℂ)
        (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)) := by
    funext w
    let f : MvPolynomial (Fin N × Fin N) ℤ →+* ℂ :=
      (eval fun q : Fin N × Fin N => H w q.1 q.2).comp (map (Int.castRingHom ℂ))
    have hm : (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)).map f = H w := by
      ext r s
      simp [f]
    have := minorIJ_map f (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J
    rw [hm] at this
    exact this
  rw [e]
  exact h

theorem prod_local (A : FinHolAtlas e S) {V : Set S} {y₀ : S} {N : ℕ} (hV : IsOpen V) (hy : y₀ ∈ V)
    (g : Fin N → S → ℂ) (n : Fin N → ℤ)
    (key : ∀ i, ∃ W : Set S, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ V ∧ A.HoloOn W (g i) ∧ ∀ w ∈ W, g i w ≠ 0) :
    ∃ V' : Set S, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i, g i w ^ n i) ∧
      ∀ w ∈ V', ∏ i, g i w ^ n i ≠ 0 := by
  choose W hW hyW hWV hh h0 using key
  have hsub : ∀ i, V ∩ ⋂ i, W i ⊆ W i := fun i => Set.inter_subset_right.trans (Set.iInter_subset _ i)
  refine ⟨V ∩ ⋂ i, W i, hV.inter (isOpen_iInter_of_finite hW), ⟨hy, Set.mem_iInter.2 hyW⟩,
    Set.inter_subset_left, ?_, ?_⟩
  · exact holoOn_prod A _ fun i _ =>
      holoOn_zpow A (holoOn_mono A (hh i) (hsub i)) (fun w hw => h0 i w (hsub i hw)) (n i)
  · exact fun w hw => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h0 i w (hsub i hw))

end Holo

theorem minor_w_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = j) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (wIdx N j) (wIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi.ge] at h
  exact left_ne_zero_of_mul h

theorem minor_om_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = N) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (omIdx N j) (omIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi] at h
  exact right_ne_zero_of_mul h

theorem val_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hi : RegAt x (mCoordIdeal z) s⁻¹) : valAt x s z ≠ 0 := by
  intro e
  have h := (reg_mul hz hs hi).2
  rw [mul_inv_cancel₀ h0, e, zero_mul] at h
  exact one_ne_zero (((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1).symm.trans h)

theorem improper_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M e X _ A V y₀ zb Hm F τ a hV hy hzb hpt hgood hHm hdiag
  refine prod_local A hV hy (fun i w => if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) *
    (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
      else minorIJ (Hm w) (omIdx N j) (omIdx N j))) (fun i => xiCoef τ a (τ, i)) fun i => ?_
  by_cases hp : IsProperStep N j i
  · refine ⟨V, hV, hy, subset_rfl, ?_, fun w _ => ?_⟩
    · simp only [if_pos hp]
      exact holoOn_const A V 1
    · simp only [if_pos hp]
      exact one_ne_zero
  · have hnone : M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp
    obtain ⟨W, hW, hyW, hWV, hval⟩ := StepW.ValHolo.holoOn_valAt _ _ M.Ω M.x (F.υ (τ, i)) e X A V zb y₀ hV hy hzb hpt
      ((hgood y₀ hy).2.2 _ hnone).2.1
    have hm : A.HoloOn W fun w => (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
        else minorIJ (Hm w) (omIdx N j) (omIdx N j)) := by
      have hH : ∀ r s, A.HoloOn W fun w => Hm w r s := fun r s => holoOn_mono A (hHm r s) hWV
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact holoOn_minor A hH _ _
        · simp only [if_pos h1, if_neg h2]
          exact holoOn_const A W 1
      · simp only [if_neg h1]
        exact holoOn_minor A hH _ _
    refine ⟨W, hW, hyW, hWV, ?_, fun w hw => ?_⟩
    · simp only [if_neg hp]
      exact holoOn_mul A hval hm
    · simp only [if_neg hp]
      have hwV := hWV hw
      have hv : valAt M.x (F.υ (τ, i)) (zb w) ≠ 0 :=
        val_ne (hpt w hwV) ((hgood w hwV).2.2 _ hnone).1 ((hgood w hwV).2.2 _ hnone).2.1
          ((hgood w hwV).2.2 _ hnone).2.2
      refine mul_ne_zero hv ?_
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact minor_w_ne M.j_le i h1 (hdiag w hwV).1 (hdiag w hwV).2
        · simp only [if_pos h1, if_neg h2]
          exact one_ne_zero
      · simp only [if_neg h1]
        have h3 : (i : ℕ) + 1 = N := by
          by_contra h3
          exact hp ⟨h1, h3⟩
        exact minor_om_ne M.j_le i h3 (hdiag w hwV).1 (hdiag w hwV).2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPointStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frame_metric_near_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormula
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem log_refNorm_blocks {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (d : κ → ℤ)
    {z : (Σ k, ρ k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm d z) = ∑ k, (d k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hpos k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hpos k) _

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem xiDeg_self (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) :
    xiDeg M τ a k₀ = -2 := by
  have hd : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := fun p => by
    have hn : ¬ ∀ p', M.blk p' ≠ some k₀ := fun h => h _ hk
    unfold FlagModel.dy
    rw [dite_eq_right hn]
    by_cases hp : p = (τ, a)
    · rw [if_pos (hp ▸ hk), if_pos hp]
    · rw [if_neg fun e => hp (M.blk_inj _ _ k₀ e hk), if_neg hp]
  unfold xiDeg
  simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [xiCoef]

theorem log_potA : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ hk zz hz
  have hf : ∀ k, ∃ i, fstPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => hz (some k)
  have hs : ∀ k, ∃ i, sndPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      obtain ⟨i, hi⟩ := hz none
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_self] using hi
    · obtain ⟨i, hi⟩ := hz (some k)
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_ne (p := ⟨k, i⟩) e] using hi
  set A : K → ℝ := fun k => Real.log (∑ i, ‖fstPt k₀ zz ⟨k, i⟩‖ ^ 2) with hA
  set B : K → ℝ := fun k => Real.log (∑ i, ‖sndPt k₀ zz ⟨k, i⟩‖ ^ 2) with hB
  set Ln : ℝ := Real.log (∑ i : ι k₀, ‖zz ⟨none, i⟩‖ ^ 2) with hLn
  have hB₀ : B k₀ = Ln := by
    simp only [hB, hLn, sndPt, Function.comp_apply, v₁_self]
  have hBne : ∀ k, k ≠ k₀ → B k = A k := fun k e => by
    simp only [hA, hB, fstPt, sndPt, Function.comp_apply, v₀]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [v₁_ne (p := ⟨k, i⟩) e]
  have hlhs : Real.log ((potA M τ a k₀).h zz) = 1 / 2 * Ln + ∑ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k := by
    show Real.log (refNorm (aDeg M τ a k₀) zz) = _
    rw [log_refNorm_blocks _ hz, Fintype.sum_option]
    simp only [aDeg, hLn, hA]
    norm_num
    rfl
  have hrhs : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) +
      Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) = ∑ k, (xiDeg M τ a k : ℝ) / 2 * (A k + B k) := by
    have hp : ∀ p, Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz)) =
        ∑ k, (M.dy p k : ℝ) / 2 * (A k + B k) := fun p => by
      rw [fsHerm_h, fsHerm_h, log_refNorm_blocks _ hf, log_refNorm_blocks _ hs, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hA, hB]; ring
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiDeg]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hlhs, hrhs]
  have hterm : ∀ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k + 1 / 2 * ((xiDeg M τ a k : ℝ) / 2 * (A k + B k)) =
      if k = k₀ then -(1 / 2) * Ln else 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      rw [if_pos rfl, hB₀, xiDeg_self M hk]
      simp only [aDeg, if_true]
      push_cast
      ring
    · rw [if_neg e, hBne k e]
      simp only [aDeg, if_neg e]
      push_cast
      ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset K) = _) fun k _ => hterm k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k₀, if_pos (Finset.mem_univ _)] at hsum
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_metric_log_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedMeasure
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem holoOn_mul_prod_zpow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} {κ : Type}
    [Fintype κ] {f : X → ℂ} {c : κ → X → ℂ} (d : κ → ℤ) (hf : A.HoloOn U f) (hc : ∀ k, A.HoloOn U (c k))
    (h0 : ∀ k, ∀ y ∈ U, c k y ≠ 0) : A.HoloOn U fun y => f y * ∏ k, c k y ^ d k := by
  intro j z hz
  have h1 : AnalyticAt ℂ (fun v => ∏ k, ((c k ∘ (A.chart j).symm) v) ^ d k) z :=
    Finset.analyticAt_fun_prod _ fun k _ => (hc k j z hz).zpow (h0 k _ hz.2)
  exact (hf j z hz).mul h1

theorem holoOn_comp_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {g : (Fin e → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g ψ.target) {V : Set X} (hV : V ⊆ ψ.source) : A.HoloOn V fun w => g (ψ w) := by
  intro j z hz
  have hs : (A.chart j).symm z ∈ ψ.source := hV hz.2
  have h1 : AnalyticAt ℂ (g ∘ (ψ ∘ (A.chart j).symm)) z :=
    AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hs)) ((hψ j).1 z ⟨hz.1, hs⟩)
  exact h1

def mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p =>
  match p with
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem fstPt_mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : fstPt k₀ (mixPt k₀ z₀ z₁) = z₀ := by
  funext q
  obtain ⟨k, m⟩ := q
  rfl

theorem sndPt_mixPt {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h : ∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ q = z₀ q) :
    sndPt k₀ (mixPt k₀ z₀ z₁) = z₁ := by
  funext q
  obtain ⟨k, m⟩ := q
  by_cases e : k = k₀
  · subst e
    change mixPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]
    rfl
  · change mixPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact (h ⟨k, m⟩ e).symm

theorem mixPt_blocks {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) : ∀ o, ∃ i, mixPt k₀ z₀ z₁ ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact h₁ k₀
  | some k => exact h₀ k

theorem log_norm_sub {k₀ : K} (A : HermLine fun o : Option K => ι (o.getD k₀)) {c : Option K → ℂ}
    (hc : ∀ o, c o ≠ 0) {z zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z = fun p => c p.1 * zz p)
    (hzz : ∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) {f t : ℂ} (hf : f ≠ 0) (ht : t ≠ 0) :
    Real.log ‖f * (∏ o, c o ^ A.a o) * t‖ - Real.log (A.h z) = Real.log ‖t * f‖ - Real.log (A.h zz) := by
  have hC : (∏ o, ‖c o‖ ^ A.a o) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc o))
  have hP : ‖∏ o, c o ^ A.a o‖ = ∏ o, ‖c o‖ ^ A.a o := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun o _ => norm_zpow _ _
  have hN : ‖f * (∏ o, c o ^ A.a o) * t‖ = (∏ o, ‖c o‖ ^ A.a o) * ‖t * f‖ := by
    rw [norm_mul, norm_mul, norm_mul, hP]
    ring
  have hA : A.h z = (∏ o, ‖c o‖ ^ A.a o) * A.h zz := by
    rw [hz]
    exact A.smul c zz hc
  have hp : A.h zz ≠ 0 := (A.pos zz hzz).ne'
  have hn : ‖t * f‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero ht hf)
  rw [hN, hA, Real.log_mul hC hn, Real.log_mul hC hp]
  ring

theorem goodAt_of_orbit {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
    {F : FrameData ι Ψ N M.Ω M.blk} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z'))) : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := by
  obtain ⟨c, hc0, hzc⟩ := h
  have e₀ : basePart M.blk z = fun q : Σ k, baseIdx ι M.blk k =>
      (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z' q := by
    rw [hzc]; rfl
  rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk z')]
  exact hG

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x
  obtain ⟨ψ, kb, σ, i₀, F, H, hx, hC⟩ := hW.2.2 x
  obtain ⟨V, z₀, z₁, c, hVo, hxV, hVs, hVU, hz₀h, hch, hc0, hL⟩ :=
    GlobalTheory.T.flag_adjacent_twisted_resolution_alt K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x ψ kb σ i₀ F H hx hC
  have hFr : M.IsFrame F := hC.2.1
  have hsrc := hC.2.2.2.2.2
  have hfacts : ∀ w ∈ V, basePart M.blk (z₀ w) ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, ∃ i, z₀ w ⟨k, i⟩ ≠ 0) ∧
      (∀ k, ∃ i, z₁ w ⟨k, i⟩ ≠ 0) ∧ basePart M.blk (z₁ w) = basePart M.blk (z₀ w) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (z₀ w))) := by
    intro w hw
    obtain ⟨ho₀, ho₁, -, hoff, -, -⟩ := hL w hw
    obtain ⟨h1, -, h3, h4⟩ := PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW w (z₀ w) (z₁ w) ho₀ ho₁
    refine ⟨h1, h3, h4, ?_, goodAt_of_orbit M ho₀ (hsrc w (hVs hw)).2.1⟩
    funext q
    exact hoff ⟨q.1.1, q.2⟩ fun e' => q.1.2 (τ, a) (hk.trans (congrArg some (Eq.symm e')))
  have hdata : ∀ w ∈ V, ψ w i₀ ≠ 0 → IsPtData M τ a k₀ ca cb RW w (z₀ w) (z₁ w) F (H τ (ψ w)) (ψ w i₀) := by
    intro w hw h0
    obtain ⟨ho₀, ho₁, hex, -⟩ := hL w hw
    have hH := (hsrc w (hVs hw)).1 τ
    exact ⟨hFr, (hfacts w hw).2.2.2.2, ho₀, ho₁, hH.1, hH.2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  obtain ⟨V', hV'o, hxV', hV'V, hfh, hf0⟩ := GlobalTheory.T.holomorphic_frame_metric_near_point K ι Φ y Ψ N j M e RW.X RW.A V x
    (fun w => basePart M.blk (z₀ w)) (fun w => H τ (ψ w)) F τ a hVo hxV (fun q => hz₀h ⟨q.1.1, q.2⟩)
    (fun w hw => (hfacts w hw).1) (fun w hw => (hfacts w hw).2.2.2.2)
    (fun r s => holoOn_comp_chart RW.A hC.1 (hC.2.2.2.2.1 τ r s) hVs) (fun w hw => (hsrc w (hVs hw)).1 τ)
  obtain ⟨f, hfh, hf0, hfd⟩ : ∃ f : RW.X → ℂ, RW.A.HoloOn V' f ∧ (∀ w ∈ V', f w ≠ 0) ∧ ∀ w, f w =
      ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (z₀ w)) *
        (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (H τ (ψ w)) (wIdx N j) (wIdx N j) else 1)
          else minorIJ (H τ (ψ w)) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i) :=
    ⟨_, hfh, hf0, fun _ => rfl⟩
  refine ⟨ψ, kb, σ, i₀, V', fun w => f w * ∏ o, c o w ^ aDeg M τ a k₀ o, ⟨F, H, hC⟩, hV'o, hxV',
    hV'V.trans hVs, hV'V.trans hVU, ?_, ?_, ?_, ?_⟩
  · exact holoOn_mul_prod_zpow RW.A _ hfh (fun o j' => (hch o j').mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono hV'V))) fun o w hw => hc0 o w (hV'V hw)
  · intro w hw
    exact mul_ne_zero (hf0 w hw) (Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (hc0 o w (hV'V hw)))
  · intro w hw
    have hwV := hV'V hw
    constructor
    · intro h0
      obtain ⟨ho₀, ho₁, hex, hoff, -, -⟩ := hL w hwV
      have hbase := (hfacts w hwV).2.2.2.1
      have hz : z₁ w = z₀ w := by
        funext q
        obtain ⟨k, m⟩ := q
        by_cases e' : k = k₀
        · subst e'
          have h1 := (hex τ a).1.2 k hk m
          have h2 := (hex τ a).2.2 k hk m
          rw [if_pos rfl, h0, Matrix.single_zero, add_zero, mul_one, hbase] at h2
          exact h2.trans h1.symm
        · exact hoff ⟨k, m⟩ e'
      rw [hz] at ho₁
      exact orbit_trans (orbit_symm ho₀) ho₁
    · intro hs
      by_contra h0
      exact GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW w _ _ _ _ _
        (hdata w hwV h0) hs
  · intro w hw h0 z₀' z₁' F' h' t' hD
    have hwV := hV'V hw
    obtain ⟨ho₀, ho₁, -, hoff, hl0, hl1⟩ := hL w hwV
    obtain ⟨hmc, hn₀, hn₁, hbase, hG⟩ := hfacts w hwV
    obtain ⟨hF', hG', hp₀, hp₁, hB', hd', ht', he₀', he₁'⟩ := hD
    have hd := hdata w hwV h0
    have hind := GlobalTheory.T.flag_adjacent_two_frames_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hj hk hca hcb F F' (z₀ w) (z₁ w) z₀' z₁'
      (H τ (ψ w)) h' (ψ w i₀) t' hmc hn₀ hn₁ hbase hFr hF' hG hG' (orbit_trans ho₀ (orbit_symm hp₀))
      (orbit_trans ho₁ (orbit_symm hp₁)) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hB' hd' h0 ht' hd.2.2.2.2.2.2.2.1
      hd.2.2.2.2.2.2.2.2 he₀' he₁'
    rw [← hind]
    have hlift : RW.lift x w = fun p => c p.1 w * mixPt k₀ (z₀ w) (z₁ w) p := by
      funext p
      obtain ⟨o, m⟩ := p
      cases o with
      | none => exact hl1 m
      | some k => exact hl0 ⟨k, m⟩
    have hzz := mixPt_blocks (k₀ := k₀) hn₀ hn₁
    have hnorm := log_norm_sub (potA M τ a k₀) (c := fun o => c o w) (fun o => hc0 o w hwV) hlift hzz
      (hf0 w hw) h0
    have hcombo := GlobalTheory.T.twisted_metric_log_formula K ι Φ y Ψ N j M τ a k₀ hk _ hzz
    rw [fstPt_mixPt, sndPt_mixPt hoff] at hcombo
    have e₁ : Real.log ‖(f w * ∏ o, c o w ^ aDeg M τ a k₀ o) * ψ w i₀‖ -
        Real.log ((potA M τ a k₀).h (RW.lift x w)) = _ := hnorm
    refine e₁.trans ?_
    rw [hcombo, normRhs, ← hfd w]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedMeasureStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_measure : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main <;> assumption)
end
