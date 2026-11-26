module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerFunctional
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open GlobalTheory.CuspRep.Generic

namespace PositivityTheory.jumpWindows.WhittakerFunctional

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem norm_avg_le (Γ : AddSubgroup G) (Φ : G → ℂ) {C : ℝ} (h0 : 0 ≤ C) (hC : ∀ x, ‖Φ x‖ ≤ C) :
    ‖avg Γ Φ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  unfold avg
  split_ifs with h
  · have h1 := h.choose_spec.2.2
    have hs : h.choose.1 h.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    have := norm_setIntegral_le_of_norm_le_const hs (f := Φ) (fun x _ => hC x)
    simpa [Measure.real, h1] using this
  · simpa using h0

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem norm_colT_le (hψ : StdPsi ψ) (k : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖colT ψ k f g‖ ≤ C := by
  refine norm_avg_le _ _ h0 fun x => ?_
  rw [norm_mul, hψ.norm, one_mul]
  exact hf _

theorem norm_whit_le (hψ : StdPsi ψ) (m : ℕ) {f : GA E a → ℂ} {C : ℝ} (h0 : 0 ≤ C) (hf : ∀ g, ‖f g‖ ≤ C)
    (g : GA E a) : ‖whit ψ m f g‖ ≤ C := by
  induction m generalizing f g with
  | zero => exact hf g
  | succ m ih =>
    rw [whit_succ]
    exact ih (fun g => norm_colT_le hψ (m + 1) h0 hf g) g

theorem good_add {m : ℕ} {f f' : GA E a → ℂ} (hf : Good ψ m f) (hf' : Good ψ m f') :
    Good ψ m (fun g => f g + f' g) := by
  refine ⟨hf.cont.add hf'.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g, hf'.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g, hf'.law k hk y g, mul_add]
  · intro r hr hrm g
    have := GlobalTheory.T.quotientAverage_add_of_periodic _ (ratV E (UnipotentBlockColumnIndex a r m)) (isCoLat_ratV E _) _ _
      (per_blk hf.cont (fun c g => hf.left _ (isMir_blkU c) g) g)
      (per_blk hf'.cont (fun c g => hf'.left _ (isMir_blkU c) g) g)
    rw [this, hf.van r hr hrm g, hf'.van r hr hrm g, add_zero]

theorem good_smul (c : ℂ) {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) : Good ψ m (fun g => c * f g) := by
  refine ⟨continuous_const.mul hf.cont, ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [hf.left γ hγ g]
  · intro k hk y g
    simp only [hf.law k hk y g]
    ring
  · intro r hr hrm g
    show avg _ (fun x => c * f (blkU x * g)) = 0
    rw [avg_const_mul, hf.van r hr hrm g, mul_zero]

theorem good_zero (m : ℕ) : Good ψ m (fun _ : GA E a => (0 : ℂ)) := by
  refine ⟨continuous_const, fun _ _ _ => rfl, ?_, ?_⟩
  · intro _ _ _ _
    simp
  · intro r _ _ g
    have := avg_const_mul (ratV E (UnipotentBlockColumnIndex a r m)) 0 (fun _ => 0)
    simpa using this

theorem good_rt {m : ℕ} {f : GA E a → ℂ} (hf : Good ψ m f) (h : GA E a) : Good ψ m (fun x => f (x * h)) := by
  refine ⟨hf.cont.comp (continuous_id.mul continuous_const), ?_, ?_, ?_⟩
  · intro γ hγ g
    simp only [mul_assoc, hf.left γ hγ (g * h)]
  · intro k hk y g
    simp only [mul_assoc, hf.law k hk y (g * h)]
  · intro r hr hrm g
    simp only [mul_assoc]
    exact hf.van r hr hrm (g * h)

theorem dot_eLast (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) : dot (eLast a k) y = lastE k y := by
  simp only [dot, eLast, lastE]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp


variable (E a) in
def Yg (hψ : StdPsi ψ) : Submodule ℂ (XB E a) where
  carrier := {φ | Good ψ (a - 1) φ}
  add_mem' h h' := good_add h h'
  zero_mem' := good_zero (a - 1)
  smul_mem' c _ h := good_smul c h

def whL (hψ : StdPsi ψ) (g : GA E a) : Yg E a hψ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => whit ψ (a - 1) (φ.1 : GA E a → ℂ) g
      map_add' := fun φ φ' => congrFun (whit_add hψ (a - 1) (by omega) φ.2 φ'.2) g
      map_smul' := fun c φ => congrFun (whit_smul (a - 1) c (φ.1 : GA E a → ℂ)) g } 1
    fun φ => by
      rw [one_mul]
      exact norm_whit_le hψ _ (norm_nonneg _) (fun g => φ.1.norm_coe_le_norm g) g

end PositivityTheory.jumpWindows.WhittakerFunctional

namespace PositivityTheory.jumpWindows

theorem local_group_averaging_tensor : G5 := by
  intro E _ _ _ a ψ hψ
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  refine ⟨fun g => ?_, fun φ g h => ?_, fun φ h hφ => ?_, fun φ hφ => ⟨?_, fun hne => ?_, fun k hk y g => ?_⟩⟩
  · obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq (WhittakerFunctional.Yg E a hψ) (WhittakerFunctional.whL hψ g)
    refine ⟨Λ, fun φ hφ => ?_⟩
    have := hΛ ⟨φ, hφ⟩
    rw [WhittakerFunctional.whL, LinearMap.mkContinuous_apply] at this
    exact this
  · exact whit_rt (a - 1) φ h g
  · exact WhittakerFunctional.good_rt hφ h
  · exact (whit_good hψ (a - 1) h0 hφ).1.cont
  · have hf : (φ : GA E a → ℂ) ≠ 0 := fun h => hne (DFunLike.coe_injective (by simpa using h))
    obtain ⟨g, hg⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 hφ).2 hf)
    exact ⟨g, hg⟩
  · rw [← WhittakerFunctional.dot_eLast]
    exact (whit_good hψ (a - 1) h0 hφ).1.law k hk y g

end PositivityTheory.jumpWindows

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MeetOf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOfSteps
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.ClosedInvariantMeet

theorem exists_space (hG2a : G2a) (hG2b : G2b) (hG2c : G2c) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    {a : ℕ} (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    (S : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (hB : ∀ w, w ∉ S → (B w).card = a)
    (H : Submodule ℂ (L2 (latticeGL E a) μ)) (hH : IsSubrep (R (latticeGL E a) μ) H) :
    ∃ Y : Submodule ℂ (XB E a), YOK ψ S Y ∧ ∀ φ : XB E a, φ ∈ Y ↔
      (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧
        (∃ h : MemL2Quotient (latticeGL E a) μ φ, h.toL2 ∈ H) ∧ ∀ w, w ∉ S → SatFn w (B w) φ := by
  obtain ⟨Y0, c0, s0, m0⟩ := hG2a E a ψ hψ
  obtain ⟨YH, cH, sH, mH⟩ := hG2b E a μ H hH
  have hw := fun w (hw : w ∉ S) => hG2c E a w (B w) (hB w hw)
  choose! Yw cw sw mw using hw
  have mem : ∀ φ : XB E a, φ ∈ Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w ↔
      (φ ∈ Y0 ∧ φ ∈ YH) ∧ ∀ w, w ∉ S → φ ∈ Yw w := fun φ => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w, ⟨?_, ?_, ?_⟩, fun φ => ?_⟩
  · have e : ((Y0 ⊓ YH ⊓ ⨅ w, ⨅ (_ : w ∉ S), Yw w : Submodule ℂ (XB E a)) : Set (XB E a)) =
        ((Y0 : Set (XB E a)) ∩ YH) ∩ ⋂ w, ⋂ (_ : w ∉ S), (Yw w : Set (XB E a)) := by
      ext φ
      simp only [SetLike.mem_coe, mem, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    exact (c0.inter cH).inter (isClosed_iInter fun w => isClosed_iInter fun h => cw w h)
  · intro g hg φ hφ
    obtain ⟨⟨h0, h1⟩, h2⟩ := (mem φ).1 hφ
    exact (mem _).2 ⟨⟨s0 g φ h0, sH g φ h1⟩, fun w h => sw w h g (hg w h) φ (h2 w h)⟩
  · intro φ hφ
    exact ((m0 φ).1 ((mem φ).1 hφ).1.1).1
  · rw [mem, m0, mH]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨h0, h1, fun w h => (mw w h φ).1 (h2 w h)⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, h1⟩, fun w h => (mw w h φ).2 (h2 w h)⟩

theorem eq_of_wh (hG5 : G5) (hG13 : WhittakerVanishingImpliesZero) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (S : Finset (Pl E)) (hc : ∀ w, w ∉ S → Cond ψ w) (B : Pl E → Multiset ℂˣ)
    (hYs : ∀ w, w ∉ S → ∃ Z : Submodule ℂ (XB E a), ∀ φ, φ ∈ Z ↔ SatFn w (B w) φ)
    (hY0 : ∃ Z : Submodule ℂ (XB E a), ∀ φ : XB E a, φ ∈ Z ↔ Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g)
    {φ φ' : XB E a} (h : (Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ)
    (h' : (Good ψ (a - 1) φ' ∧ ∀ γ g, φ' (ratGL E a γ * g) = φ' g) ∧ ∀ w, w ∉ S → SatFn w (B w) φ')
    (hW : ∀ g, MirS S g → InS S g → Wh ψ φ g = Wh ψ φ' g) : φ = φ' := by
  obtain ⟨Z, hZ⟩ := hY0
  have d0 : φ - φ' ∈ Z := Z.sub_mem ((hZ φ).2 h.1) ((hZ φ').2 h'.1)
  have hd := (hZ _).1 d0
  have e := hG13 E a ψ hψ S hc (φ - φ') hd.1 hd.2
    (fun w hw => ⟨B w, by
      obtain ⟨Z', hZ'⟩ := hYs w hw
      exact (hZ' _).1 (Z'.sub_mem ((hZ' φ).2 (h.2 w hw)) ((hZ' φ').2 (h'.2 w hw)))⟩)
    (fun g h1 h2 => by
      obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 g
      rw [← hΛ _ hd.1, map_sub, hΛ _ h.1.1, hΛ _ h'.1.1, hW g h1 h2, sub_self])
  exact sub_eq_zero.1 e

theorem meet_of_steps : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet := by
  intro _ hS10 hG0 hG1 hG1b hG2a hG2b hG2c hG5 _ hG7i hG8 hG10 hG13 E _ _ _ a μ _ _ π π' H H' hn hn' hH hH' hm hm' hss
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  obtain ⟨φ0, hφ0, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨φ0', hφ0', h0'⟩ := (Submodule.ne_bot_iff _).1 π'.ne_bot
  obtain ⟨x, hx, hxs, hxl⟩ := hG1 E a π hn φ0 hφ0
  obtain ⟨x', hx', hxs', hxl'⟩ := hG1 E a π' hn' φ0' hφ0'
  have hev := hcond.and (hss.and ((hG1b E a π hn φ0 hφ0 x hx).and (hG1b E a π' hn' φ0' hφ0' x' hx')))
  obtain ⟨S, hS⟩ : ∃ S : Finset (Pl E), ∀ w, w ∉ S → Cond ψ w ∧
      (∃ B, (CG.mk π).HasSat w B ∧ (CG.mk π').HasSat w B) ∧
      (∀ B, (CG.mk π).HasSat w B → SatFn w B x) ∧ (∀ B, (CG.mk π').HasSat w B → SatFn w B x') :=
    ⟨(Filter.eventually_cofinite.1 hev).toFinset, fun w hw => by
      by_contra h
      exact hw ((Set.Finite.mem_toFinset _).2 h)⟩
  have hBex := fun w (hw : w ∉ S) => (hS w hw).2.1
  choose! B hB using hBex
  have hcard : ∀ w, w ∉ S → (B w).card = a := fun w hw => CG.HasSat.card (hB w hw).1
  have hc : ∀ w, w ∉ S → Cond ψ w := fun w hw => (hS w hw).1
  obtain ⟨Y, hYok, hY⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H hH
  obtain ⟨Y', hYok', hY'⟩ := exists_space hG2a hG2b hG2c μ hψ S B hcard H' hH'

  have hxY : x ∈ Y := by
    refine (hY x).2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.1 _ (hB w hw).1⟩
    · rw [hx]; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0 (π.cusp _ hφ0)
    · rw [hx]; exact (π.cusp _ hφ0).1.left
    · rw [hx]; exact hm φ0 hφ0
  have hxY' : x' ∈ Y' := by
    refine (hY' x').2 ⟨⟨?_, ?_⟩, ?_, fun w hw => (hS w hw).2.2.2 _ (hB w hw).2⟩
    · rw [hx']; exact _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ φ0' (π'.cusp _ hφ0')
    · rw [hx']; exact (π'.cusp _ hφ0').1.left
    · rw [hx']; exact hm' φ0' hφ0'
  have hx0 : x ≠ 0 := fun e => h0 (Subtype.ext (by rw [← hx, e]; rfl))
  have hx0' : x' ≠ 0 := fun e => h0' (Subtype.ext (by rw [← hx', e]; rfl))
  obtain ⟨φ₁, hφ₁, hs₁, hl₁, hw₁⟩ := hG8 E a ψ hψ S hc Y hYok x hxY hx0 hxs (hxl S)
    fun w hw => ⟨B w, ((hY x).1 hxY).2.2 w hw⟩
  obtain ⟨φ₂, hφ₂, hs₂, hl₂, hw₂⟩ := hG8 E a ψ hψ S hc Y' hYok' x' hxY' hx0' hxs' (hxl' S)
    fun w hw => ⟨B w, ((hY' x').1 hxY').2.2 w hw⟩
  have hst : St ψ S Y Y' 0 (fun _ => 0) := by
    refine ⟨φ₁, hφ₁, φ₂, hφ₂, hs₁, hs₂, hl₁, hl₂, by rw [hw₁]; exact one_ne_zero, fun g hg => ?_⟩
    have e : g = 1 := by
      obtain ⟨-, -, -, -, -, hext, -⟩ := hG0 E a
      refine hext g 1 ?_ fun w => ?_
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ hg.1
      · rw [map_one]; exact (hS10 _ a 0).2.1 _ (hg.2 w)
    rw [e, hw₁, hw₂]
  obtain ⟨φ, hφ, φ', hφ', -, -, -, -, hw, hag⟩ := hG7i E a ψ hψ S Y Y' hYok hYok' hst
  have hφm := (hY φ).1 hφ
  have hφm' := (hY' φ').1 hφ'
  obtain ⟨Z, -, -, hZ⟩ := hG2a E a ψ hψ
  have heq : φ = φ' := by
    refine eq_of_wh hG5 hG13 hψ S hc B (fun w hw => ?_) ⟨Z, hZ⟩ ⟨hφm.1, hφm.2.2⟩
      ⟨hφm'.1, hφm'.2.2⟩ fun g hg hi => hag g ⟨hg.1, fun w => ?_⟩
    · obtain ⟨Z', -, -, hZ'⟩ := hG2c E a w (B w) (hcard w hw)
      exact ⟨Z', hZ'⟩
    · by_cases hw : w ∈ S
      · simpa only [if_pos hw] using hg.2 w hw
      · simp only [if_neg hw]
        rw [hi w hw]
        exact (hS10 _ a 0).2.2.1
  subst heq
  obtain ⟨h, hhH⟩ := hφm.2.1
  obtain ⟨h', hhH'⟩ := hφm'.2.1
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨Λ, hΛ⟩ := (hG5 E a ψ hψ).1 1
    exact hw (by rw [← hΛ _ hφm.1.1, map_zero])
  have hne : h.toL2 ≠ 0 := toL2_ne_zero h φ.continuous fun e => hφ0 (DFunLike.coe_injective e)
  intro hbot
  have hmem : h.toL2 ∈ H ⊓ H' := ⟨hhH, hhH'⟩
  rw [hbot] at hmem
  exact hne ((Submodule.mem_bot _).1 hmem)

end GlobalTheory.CompanionTheory.ClosedInvariantMeet

end
end

namespace PositivityTheory.jumpWindows

theorem meet_of : S2 → MirabolicColumnBlock → G0 → G1 → AlmostEverywhereSpherical → G2a → G2b → G2c → G5 → G5b → FourierInductionSteps → G8 → StandardCharacterExists → WhittakerVanishingImpliesZero → Meet :=
  GlobalTheory.CompanionTheory.ClosedInvariantMeet.meet_of_steps

end PositivityTheory.jumpWindows
end
