module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabel
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicity

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRank
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRank
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone

theorem vanish_of_inRCone_of_genRank_le : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → GlobalTheory.PolFan.Dominates bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ τ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
  classical
  let P : Fin m → Prop := fun j => ∀ y, β y y = 0 → τ j y y = 0
  have hw : ∀ j, ∃ y, β y y = 0 ∧ (¬ P j → 0 < τ j y y) := by
    intro j
    by_cases hj : P j
    · exact ⟨0, by simp, fun h => (h hj).elim⟩
    · simp only [P, not_forall] at hj
      obtain ⟨y, hy, hne⟩ := hj
      exact ⟨y, hy, fun _ => lt_of_le_of_ne (hτ.nonneg j y) (Ne.symm hne)⟩
  choose w hw0 hwpos using hw
  let T : Finset (Fin m) := Finset.univ.filter P
  let s : Fin T.card ↪ Fin m := (T.orderEmbOfFin rfl).toEmbedding
  have hsr : Set.range s = ↑T := Finset.range_orderEmbOfFin T rfl
  have hP : ∀ k, P k ↔ k ∈ Set.range s := fun k => by rw [hsr]; simp [T]
  let hf : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ i, LinearMap.applyₗ (w i) ∘ₗ LinearMap.applyₗ (w i)
  have hfa : ∀ x : LinearMap.BilinForm ℤ X, hf x = ∑ i, x (w i) (w i) := fun x => by
    simp [hf, LinearMap.sum_apply]
  have hcut : IsFaceCut τ s hf := by
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rw [hfa]; exact Finset.sum_nonneg fun i _ => hτ.nonneg k (w i)
    · rw [← hP, hfa]
      constructor
      · intro h0
        by_contra hk
        have h1 : τ k (w k) (w k) ≤ ∑ i, τ k (w i) (w i) :=
          Finset.single_le_sum (f := fun i => τ k (w i) (w i)) (fun i _ => hτ.nonneg k (w i)) (Finset.mem_univ k)
        have h2 := hwpos k hk
        omega
      · intro hk
        exact Finset.sum_eq_zero fun i _ => hk _ (hw0 i)
  have hcell : IsCell bar ψ (fun k => τ (s k)) :=
    GlobalTheory.T.cell_face_restriction O bar hb q ψ hψ X hX hdom m τ hτ _ s hf hcut
  obtain ⟨c, hc, hce⟩ := hβc
  have hc0 : ∀ i, ¬ P i → c i = 0 := by
    intro i hi
    have e : (β (w i) (w i) : ℝ) = ∑ k, c k * (τ k (w i) (w i) : ℝ) := by
      have := LinearMap.congr_fun₂ hce (w i) (w i)
      simpa [LinearMap.sum_apply] using this
    rw [hw0 i, Int.cast_zero] at e
    have h1 : c i * (τ i (w i) (w i) : ℝ) ≤ ∑ k, c k * (τ k (w i) (w i) : ℝ) :=
      Finset.single_le_sum (f := fun k => c k * (τ k (w i) (w i) : ℝ))
        (fun k _ => mul_nonneg (hc k) (by exact_mod_cast hτ.nonneg k (w i))) (Finset.mem_univ i)
    have h2 : (0 : ℝ) < τ i (w i) (w i) := by exact_mod_cast hwpos i hi
    rw [← e] at h1
    nlinarith [hc i]
  have hmap : Finset.univ.map s = T := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    rw [← Set.mem_range, ← hP]
    simp [T]
  have hcone : InRCone (fun k => τ (s k)) β := by
    refine ⟨fun k => c (s k), fun k => hc _, ?_⟩
    rw [hce]
    have e1 := Finset.sum_map Finset.univ s (fun i => c i • toReal (τ i))
    rw [hmap] at e1
    rw [← e1]
    refine (Finset.sum_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    rw [hc0 i (by simpa [T] using hi), zero_smul]
  have hl := hlab X hX β hβ hβp
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k} ≤ genRank (fun k => τ (s k)) := Nat.sInf_le ⟨_, _, hcell, hcone, rfl⟩
  have hrk' : genRank τ ≤ genRank (fun k => τ (s k)) := by
    rw [hl] at hrk
    have h4 : ((genRank τ : ℕ) : ℝ) ≤ ((genRank (fun k => τ (s k)) : ℕ) : ℝ) := hrk.trans (Nat.cast_le.2 hle)
    exact_mod_cast h4
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range τ)) := Module.Finite.span_of_finite ℤ (Set.finite_range τ)
  have hNL : Submodule.span ℤ (Set.range fun k => τ (s k)) ≤ Submodule.span ℤ (Set.range τ) :=
    Submodule.span_mono (Set.range_comp_subset_range s τ)
  obtain ⟨n, hn, hnmem⟩ := exists_zsmul_mem_of_finrank_le_of_le hNL hrk' (Submodule.subset_span ⟨j, rfl⟩)
  have key : ∀ x ∈ Submodule.span ℤ (Set.range fun k => τ (s k)), x y y = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact (hP (s k)).2 ⟨k, rfl⟩ y hy
    | zero => simp
    | add x z _ _ h1 h2 => simp [h1, h2]
    | smul a x _ h => simp [h]
  have h3 := key _ hnmem
  simp only [LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left hn

end GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRankStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_balanced_form_vanishes_low_rank : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → GlobalTheory.PolFan.Dominates bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ τ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.VanishingInRationalCone.vanish_of_inRCone_of_genRank_le <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFan
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOne
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal

theorem smoothEnd : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ :=
  fun _ _ _ _ _ _ _ _ _ _ hD hPF hSL hM => GlobalTheory.PolFan.SmoothEnd.isPolFan_of_maxMult_le_one hD hPF hSL hM

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.SmoothOfMaxMultiplicityLeOneStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_max_multiplicity_le_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q φ → SimpLab bar q φ lab → maxMult bar q φ ≤ 1 → IsPolFan bar q φ ∧ NoSelfInt bar q φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd | exact GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SmoothFanTerminal.smoothEnd <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTop
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite


open GlobalTheory.PolFan.MultBound in
theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MaxMultiplicityLtTopStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_multiplicity_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | exact GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite.maxMult_lt_top <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.FanResolution

theorem resolution : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ := by
  intro O _ _ _ _ bar w0 hO q φ lab hDom
  suffices key : ∀ (n : ℕ) (φ lab : InvFun O), maxMult bar q φ = n → IsPolyFan bar q φ →
      IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab →
      ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ by
    intro hP hT hL hS
    have hfin := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ hP
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin.ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult bar q φ
    · have hfin : maxMult bar q φ < ⊤ := by
        rw [hn]
        exact ENat.natCast_lt_top n
      obtain ⟨φ', lab', hP', hT', hL', hS', hSub, hlt⟩ :=
        GlobalTheory.T.exists_fan_lower_max_multiplicity O bar w0 hO q φ lab hDom hP hT hL hS hfin h2
      have hfin' := GlobalTheory.T.max_multiplicity_lt_top O bar hO q φ' hP'
      obtain ⟨n', hn'⟩ := ENat.ne_top_iff_exists.mp hfin'.ne
      have hlt' : n' < n := by
        rw [hn, ← hn'] at hlt
        exact_mod_cast hlt
      obtain ⟨φ'', g1, g2, g3, g4⟩ := ih n' hlt' φ' lab' hn'.symm hP' hT' hL' hS'
      exact ⟨φ'', g1, g2, g3, fun χ hχ => g4 χ (hSub χ hχ)⟩
    · have hle : maxMult bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have h3 : ¬ (2 ≤ n) := by exact_mod_cast h2
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨g1, g2⟩ := GlobalTheory.T.smooth_of_max_multiplicity_le_one O bar hO q φ lab hDom hP hS hle
      exact ⟨φ, g1, g2, hT, fun χ hχ => hχ⟩

end GlobalTheory.CompanionTheory.Ar.Fan.FanResolution
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothSubordinateFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_smooth_subordinate_fan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ Subordinate bar q φ' φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution | exact GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.FanResolution.resolution <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSimplicialLabelledRefinement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtension
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunction
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimFanCellExists
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimFanCellExists
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
open _root_.GlobalTheory.PolFan.Mark.Exist

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone

section Face

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {q : ℕ}
  {ψ lab : InvFun O} {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]

theorem inFace_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : GlobalTheory.PolFan.Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ InRCone τ x := by
  have b1 := cone_bal hτ.mem hβ
  have b2 := cone_nonneg hτ.nonneg hβ
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ x h1 h2 h4 h5
  · intro hx
    have hs := cone_add hβ hx
    refine ⟨cone_bal hτ.mem hx, cone_nonneg hτ.nonneg hx, fun y hy => cone_vanish hx fun j =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ hr j y hy,
      evalZ_add_of_linearOn_inRCone _ ψ X m τ hτ.linear _ _ hβ hx, le_antisymm ((lab_le hl hX hτ hs).trans hr) ?_⟩
    obtain ⟨c, hc, e⟩ := hx
    refine carrierDim_le_of_add_cell _ bar q ψ lab hl X hX m τ hτ β b1 b2 _ (cone_bal hτ.mem hs)
      (cone_nonneg hτ.nonneg hs) hβ 1 c one_pos hc ?_
    rw [← e]
    exact LinearMap.ext₂ fun a b => by simp

theorem isIndec_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : GlobalTheory.PolFan.Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab β x ↔
      InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x := by
  simp only [IsIndec, inFace_iff hb hψ hl hX hD hτ hβ hr]

end Face

theorem exists_isMarked_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β₀ ∧ InRCone v β₀ := by
  intro O _ _ _ _ bar hbar q ψ lab i hDom hψ hl X _ _ _ _ hX m v hv β hb hp hvβ hlab
  classical
  have hD := hDom X
  have hfan := hψ X hX
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, τ, hτ, hβ, hr⟩ := exists_min hl hX hv hvβ
  have hF := inFace_iff hbar hψ hl hX hD hτ hβ hr.le
  have hI := isIndec_iff hbar hψ hl hX hD hτ hβ hr.le
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have h0 : ∀ j, τ j = 0 := fun j => eq_zero_of_diag (hτ.mem j).1 fun y =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hbar q ψ lab hψ hl X hX hD n τ hτ 0 hb hp hβ hr.le j y rfl
    have h1 : Submodule.span ℤ (Set.range τ) = ⊥ := Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    have h2 : genRank τ = 0 := by rw [genRank, h1, finrank_bot]
    rw [h2, hlab] at hr
    have : (0 : ℕ) = i + 1 := by exact_mod_cast hr
    omega
  have hfin := finite_indec_inRCone X n τ
  set S := hfin.toFinset with hSdef
  have hS : ∀ x, x ∈ S ↔ InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x :=
    fun x => by simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSτ : ∀ x ∈ S, InRCone τ x := fun x hx => ((hS x).1 hx).1
  have hcl : β ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} :=
    GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive _ bar ψ lab X β
      (fun x y hx hy => ⟨(hF _).2 (cone_add ((hF _).1 hx) ((hF _).1 hy)),
        evalZ_add_of_linearOn_inRCone _ ψ X n τ hτ.linear _ _ ((hF _).1 hx) ((hF _).1 hy)⟩)
      (fun x hx => hfan.integral x hx.1 hx.2.1) (fun x hx h0 => hfan.pos x hx.1 hx.2.1 h0) β ((hF _).2 hβ)
  have hadd := evalZ_sum hτ.linear S hSτ
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : {y | IsIndec bar ψ lab β y} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
      have := (hS y).2 ((hI y).1 hy)
      rw [h] at this
      exact Finset.notMem_empty _ this
    rw [this, AddSubmonoid.closure_empty, AddSubmonoid.mem_bot] at hcl
    exact hβ0 hcl
  have hσ : ∑ x ∈ S, x ≠ 0 := fun h => by
    rw [h, evalZ_zero'] at hadd
    refine (Finset.sum_pos (fun x hx => ?_) hne).ne hadd
    exact hfan.pos x (cone_bal hτ.mem (hSτ x hx)) (cone_nonneg hτ.nonneg (hSτ x hx)) ((hS x).1 hx).2.1
  obtain ⟨g, β₀, hg, hgβ, hprim⟩ := GlobalTheory.bilinForm_exists_primitive_of_ne_zero X _ hσ
  have hτ0 : InRCone τ β₀ := (cone_smul_iff hg).1 (hgβ ▸ cone_sum hSτ)
  have hge : lab.evalZ β ≤ lab.evalZ β₀ := by
    obtain ⟨k, γ, hγ, hγ0, hrγ⟩ := exists_min hl hX hτ hτ0
    have hσγ : InRCone γ (∑ x ∈ S, x) := hgβ ▸ (cone_smul_iff hg).2 hγ0
    let u : Fin S.card → LinearMap.BilinForm ℤ X := fun j => (S.equivFin.symm j : LinearMap.BilinForm ℤ X)
    have hu : ∀ {M : Type} [AddCommMonoid M] (f : LinearMap.BilinForm ℤ X → M), ∑ j, f (u j) = ∑ x ∈ S, f x :=
      fun f => by
        rw [← Finset.sum_coe_sort S f]
        exact S.equivFin.symm.sum_comp fun x => f x
    have hu1 : ∑ j, u j = ∑ x ∈ S, x := hu fun x => x
    have huτ : ∀ j, InRCone τ (u j) := fun j => hSτ _ (S.equivFin.symm j).2
    have hall := inRCone_of_evalZ_sum_le _ bar ψ X k γ hγ _ u (fun j => cone_bal hτ.mem (huτ j))
      (fun j => cone_nonneg hτ.nonneg (huτ j)) (by rw [hu1]; exact hσγ) (by rw [hu1, hu ψ.evalZ, hadd])
    have hSγ : ∀ x ∈ S, InRCone γ x := fun x hx => by
      simpa [u] using hall (S.equivFin ⟨x, hx⟩)
    have hβγ : InRCone γ β := AddSubmonoid.closure_induction (motive := fun x _ => InRCone γ x)
      (fun x hx => hSγ x ((hS x).2 ((hI x).1 hx))) cone_zero (fun _ _ _ _ => cone_add) hcl
    exact (lab_le hl hX hγ hβγ).trans hrγ.le
  have hle : lab.evalZ β₀ ≤ lab.evalZ β := (lab_le hl hX hτ hτ0).trans hr.le
  refine ⟨β₀, ⟨cone_bal hτ.mem hτ0, cone_nonneg hτ.nonneg hτ0, hprim, (le_antisymm hle hge).trans hlab, S,
    fun x => (hS x).trans (isIndec_iff hbar hψ hl hX hD hτ hτ0 (hr.le.trans hge) x).symm, g, hg, hgβ⟩, ?_⟩
  refine (cone_smul_iff hg).1 (hgβ ▸ cone_sum fun x hx => ?_)
  obtain ⟨h1, h2, -, h4, h5⟩ := (hF x).2 (hSτ x hx)
  exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hbar q ψ lab hψ hl X hX hD m v hv β hb hp hvβ x h1 h2 h4 h5

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimFanCellExistsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_isMarked_inRCone_of_isCell_of_evalZ_eq : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β₀ ∧ InRCone v β₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone.exists_isMarked_inRCone | exact GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone.exists_isMarked_inRCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone.exists_isMarked_inRCone <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierLabelMarkedFaceBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierLabelMarkedFaceBound
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces

theorem genRank_le_of_label_le {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X) (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) :
    genRank v ≤ i + 1 := by
  set σ := ∑ j, v j with hσ
  have hσ1 : σ ∈ balForms bar X := Submodule.sum_mem _ fun j _ => hv.mem j
  have hσ2 : ∀ y, 0 ≤ σ y y := fun y => by
    simp only [hσ, LinearMap.sum_apply]; exact Finset.sum_nonneg fun j _ => hv.nonneg j y
  have hσv : InRCone v σ := ⟨fun _ => 1, fun _ => zero_le_one, toReal_sum' v⟩
  have hl := hb σ hσ1 hσ2 hσv
  rw [hlab X hX σ hσ1 hσ2] at hl
  have hS : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k}).Nonempty := ⟨_, m, v, hv, hσv, rfl⟩
  obtain ⟨m', γ, hγ, hσγ, hrk⟩ := Nat.sInf_mem hS
  have hψσ : ψ.evalZ σ = ∑ j, ψ.evalZ (v j) := by
    have := (linearOn_iff ψ v).1 hv.linear (fun _ => 1) fun _ => zero_le_one
    rw [← toReal_sum', evalR_toReal] at this
    simpa using this
  have hin := GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell O bar ψ X m' γ hγ m v hv.mem hv.nonneg hσγ hψσ.le
  have hr := GlobalTheory.T.spanRank_le_of_inRealCone_polyhedralCell O bar ψ X m' m γ v hγ hv.mem hv.nonneg hin
  have h2 : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ σ ∧
      genRank γ = k} ≤ i + 1 := by exact_mod_cast hl
  rw [hrk] at hr
  exact hr.trans h2

theorem inFace_iff_of_isMarked {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (hO : CMOrd O bar) (q : ℕ)
    (ψ lab : InvFun O) (i : ℕ) (hψ : IsPolyFan bar q ψ) (hlab : IsCarrierDim bar q ψ lab)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) (hDom : GlobalTheory.PolFan.Dominates bar X) {m : ℕ} (v : Fin m → LinearMap.BilinForm ℤ X)
    (hv : IsCell bar ψ v)
    (hb : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ))
    {β : LinearMap.BilinForm ℤ X} (hβ : IsMarked bar ψ lab i X β) (hβv : InRCone v β) (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ x ∈ balForms bar X ∧ (∀ y, 0 ≤ x y y) ∧ InRCone v x := by
  obtain ⟨hβ1, hβ2, -, hβl, -⟩ := hβ
  constructor
  · rintro ⟨hx1, hx2, -, hx4, hx5⟩
    exact ⟨hx1, hx2, GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv x hx1 hx2 hx4 hx5⟩
  · rintro ⟨hx1, hx2, hxv⟩
    have hrk := genRank_le_of_label_le bar q ψ lab i hlab X hX v hv hb
    have hvan := GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hO q ψ lab hψ hlab X hX hDom m v hv β hβ1 hβ2 hβv (by rw [hβl]; exact_mod_cast hrk)
    have hsum := inRCone_add' hβv hxv
    have hs1 : β + x ∈ balForms bar X := add_mem hβ1 hx1
    have hs2 : ∀ y, 0 ≤ (β + x) y y := fun y => by
      simp only [LinearMap.add_apply]; exact add_nonneg (hβ2 y) (hx2 y)
    refine ⟨hx1, hx2, fun y hy => inRCone_apply_self_eq_zero hxv y fun j => hvan j y hy,
      GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone O ψ X m v hv.linear β x hβv hxv, le_antisymm ?_ ?_⟩
    · rw [hβl]; exact hb _ hs1 hs2 hsum
    · obtain ⟨c, hc, e⟩ := hxv
      exact carrierDim_le_of_add_cell O bar q ψ lab hlab X hX m v hv β hβ1 hβ2 (β + x) hs1 hs2 hβv 1 c one_pos hc
        (by rw [toReal_add', e, one_smul])

theorem eq_of_isMarked_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β → IsMarked bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  intro O _ _ _ _ bar hO q ψ lab i hDom hψ hlab X _ _ _ _ hX m v hv hb β β' hβ hβ' hβv hβ'v
  have hiff : ∀ x, InFace bar ψ lab β x ↔ InFace bar ψ lab β' x := fun x => by
    rw [inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ hβv x,
      inFace_iff_of_isMarked bar hO q ψ lab i hψ hlab X hX (hDom X) v hv hb hβ' hβ'v x]
  have hind : ∀ x, IsIndec bar ψ lab β x ↔ IsIndec bar ψ lab β' x := fun x => by
    simp only [IsIndec, hiff]
  obtain ⟨-, -, hp, -, S, hS, k, hk, hkS⟩ := hβ
  obtain ⟨-, -, hp', -, S', hS', k', -, hkS'⟩ := hβ'
  have hSS : S = S' := Finset.ext fun x => by rw [hS, hS', hind]
  exact eq_of_primitive_of_smul_eq hp hp' hk (by rw [hkS, hkS', hSS])

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierLabelMarkedFaceBoundStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.isMarked_unique_of_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β β' : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β → IsMarked bar ψ lab i X β' → InRCone v β → InRCone v β' → β = β' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone | exact GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MarkedFaces.eq_of_isMarked_of_inRCone <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariant
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm

variable {O : Type} [CommRing O]

def twPi (σ : O ≃+* O) (n : ℕ) : (Fin n → O) ≃+ (Fin n → O) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : O ≃+* O) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → O) ≃+ LinearMap.BilinForm ℤ (Fin n → O) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : O ≃+* O) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → O)) (a b : Fin n → O) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

theorem twForm_mem_balForms {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    {β : LinearMap.BilinForm ℤ (Fin n → O)}
    (h : β ∈ balForms bar (Fin n → O)) : twForm σ n β ∈ balForms bar (Fin n → O) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((bar a • z) j)) = bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [hb.comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : O ≃+* O) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff {bar : O → O} (hb : CMOrd O bar) (σ : O ≃+* O) {n : ℕ}
    (β : LinearMap.BilinForm ℤ (Fin n → O)) :
    twForm σ n β ∈ balForms bar (Fin n → O) ↔ β ∈ balForms bar (Fin n → O) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms hb σ.symm h, twForm_mem_balForms hb σ⟩

theorem evalZ_twForm {w0 : O} {φ : InvFun O} (hφ : IsTwG w0 φ) {σ : O ≃+* O} (hσ : σ w0 = w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → O)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab →
    ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ),
      markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  intro O _ _ _ _ bar w0 hb ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff hb σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.MarkingValueGaloisInvariantStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_value_galois_invariant : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ lab : InvFun O) (i : ℕ), IsTwG w0 ψ → IsTwG w0 lab → ∀ σ : O ≃+* O, σ w0 = w0 → ∀ (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ), markVal bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal bar ψ lab i n B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedForm.markVal_twist <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunction
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction

theorem exists_markFun_props_gen : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  intro O _ _ _ _ bar w0 hb q ψ lab i hD hψ htψ htlab hlab
  classical
  obtain ⟨w, hw⟩ := GlobalTheory.PolFan.Mark.exists_markFun bar ψ lab i
  have ev := fun {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) => GlobalTheory.PolFan.Mark.evalZ_markFun hw (X := X) β
  have mk : ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
      (β : LinearMap.BilinForm ℤ X), w.evalZ β = 1 → GlobalTheory.PolFan.Mark.IsMarked bar ψ lab i X β := fun β h => by
    rw [ev] at h
    split_ifs at h with h'
    · exact h'
    · norm_num at h
  refine ⟨w, fun σ hσ n B => by rw [hw, hw]; exact GlobalTheory.T.marking_value_galois_invariant O bar w0 hb ψ lab i htψ htlab σ hσ n B, ?_⟩
  intro X _ _ _ _ hX
  refine ⟨fun β _ _ => ?_, fun β _ _ h1 => (mk β h1).2.2.1, fun β _ _ h1 => (mk β h1).2.2.2.1,
    fun m v hv hle β _ _ β' _ _ h1 h1' hc hc' =>
      GlobalTheory.T.isMarked_unique_of_inRCone O bar hb q ψ lab i hD hψ hlab X hX m v hv hle β β' (mk β h1) (mk β' h1') hc hc',
    fun m v hv β hβ hp hc hl => ?_⟩
  · rw [ev]
    split_ifs <;> simp
  · obtain ⟨β₀, h0, hc0⟩ := GlobalTheory.T.exists_isMarked_inRCone_of_isCell_of_evalZ_eq O bar hb q ψ lab i hD hψ hlab X hX m v hv β hβ hp hc hl
    exact ⟨β₀, h0.1, h0.2.1, by rw [ev, if_pos h0], hc0⟩

end GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMarkingCentreFunctionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_marking_centre_function : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → ∃ w : InvFun O, IsTwG w0 w ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen | exact GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.MarkingFunction.exists_markFun_props_gen <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtension
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision

theorem baryStep : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab φ : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → IsTwG w0 φ → IsBaryStage bar q ψ lab φ (i + 1) → ∃ φ' : InvFun O, IsTwG w0 φ' ∧ IsBaryStage bar q ψ lab φ' i := by
  intro O _ _ _ _ bar w0 hO q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.exists_marking_centre_function O bar w0 hO q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_star_subdivision O bar w0 hO q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell bar φ (Fin.append v u) → IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage O bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.cell_face_restriction O bar hO q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators O bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BarycentricStageExtensionStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.barycentric_stage_extension : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ lab φ : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 lab → IsCarrierDim bar q ψ lab → IsTwG w0 φ → IsBaryStage bar q ψ lab φ (i + 1) → ∃ φ' : InvFun O, IsTwG w0 φ' ∧ IsBaryStage bar q ψ lab φ' i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision.baryStep | exact GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision.baryStep | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.BarycentricSubdivision.baryStep <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBounded
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBounded
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity

private theorem exists_int_ne_zero_eq_mul_of_ne_zero (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O]
    (s : O) (hs : s ≠ 0) : ∃ n : ℤ, n ≠ 0 ∧ ∃ o : O, o * s = (n : O) := by
  have hI : Ideal.comap (algebraMap ℤ O) (Ideal.span {s}) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hs (Ideal.mem_span_singleton_self s)
      (Algebra.IsIntegral.isIntegral s)
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff _).mp hI
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hn)
  exact ⟨n, hn0, o, by rw [ho]; exact eq_intCast (algebraMap ℤ O) n⟩

private theorem isLocalizedModule_int_restrictScalars_mkLinearMap (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    IsLocalizedModule (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨n, hn⟩
    rw [Module.End.isUnit_iff]
    have hn0 : (n : O) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hn)
    have hu : algebraMap O (FractionRing O) (n : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hn0)
    have key : ∀ v : LocalizedModule (nonZeroDivisors O) X,
        (algebraMap ℤ (Module.End ℤ (LocalizedModule (nonZeroDivisors O) X)) n) v =
          algebraMap O (FractionRing O) (n : O) • v := by
      intro v
      rw [Module.algebraMap_end_apply, algebraMap_smul, Int.cast_smul_eq_zsmul]
    constructor
    · intro a b h
      rw [key, key] at h
      have h2 := congrArg (fun w => (algebraMap O (FractionRing O) (n : O))⁻¹ • w) h
      simpa only [smul_smul, inv_mul_cancel₀ hu, one_smul] using h2
    · intro v
      exact ⟨(algebraMap O (FractionRing O) (n : O))⁻¹ • v, by
        rw [key, smul_smul, mul_inv_cancel₀ hu, one_smul]⟩
  · intro y
    refine LocalizedModule.induction_on (fun m s => ?_) y
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O s (nonZeroDivisors.ne_zero s.2)
    refine ⟨⟨o • m, ⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply]
    rw [← Int.cast_smul_eq_zsmul O, LocalizedModule.smul'_mk, ← ho, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, mul_smul]
    exact smul_comm _ _ _
  · intro x₁ x₂ h
    simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    obtain ⟨n, hn0, o, ho⟩ := exists_int_ne_zero_eq_mul_of_ne_zero O u (nonZeroDivisors.ne_zero u.2)
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩, ?_⟩
    simp only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] at hu ⊢
    rw [← Int.cast_smul_eq_zsmul O, ← Int.cast_smul_eq_zsmul O, ← ho, mul_smul, mul_smul, hu]

private theorem finrank_int_eq_mul_finrank (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    [Module.Finite ℤ O] (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  haveI := isLocalizedModule_int_restrictScalars_mkLinearMap O X
  haveI : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  letI : Module ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.compHom _ (algebraMap ℚ (FractionRing O))
  haveI : IsScalarTower ℚ (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have e1 : Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) = Module.finrank ℤ X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ)
      ((LocalizedModule.mkLinearMap (nonZeroDivisors O) X).restrictScalars ℤ) le_rfl
  have e2 : Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℤ (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  have e3 : Module.finrank ℚ (FractionRing O) *
      Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank ℚ (LocalizedModule (nonZeroDivisors O) X) :=
    Module.finrank_mul_finrank ℚ (FractionRing O) _
  haveI : @IsScalarTower ℤ ℚ (FractionRing O) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have e4 : Module.finrank ℚ (FractionRing O) = Module.finrank ℤ O :=
    IsFractionRing.finrank_eq ℤ ℚ O (FractionRing O)
  have e5 : Module.finrank (FractionRing O) (LocalizedModule (nonZeroDivisors O) X) =
      Module.finrank O (LocalizedModule (nonZeroDivisors O) X) :=
    IsFractionRing.finrank_right_eq O (FractionRing O) _
  have e6 : Module.finrank O (LocalizedModule (nonZeroDivisors O) X) = Module.finrank O X :=
    IsLocalizedModule.finrank_eq (nonZeroDivisors O)
      (LocalizedModule.mkLinearMap (nonZeroDivisors O) X) le_rfl
  rw [← e1, ← e2, ← e3, e4, e5, e6]

theorem finrank_int_eq_fraction_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (K : Type) [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℚ K * Module.finrank O X := by
  rw [finrank_int_eq_mul_finrank O X, IsFractionRing.finrank_eq ℤ ℚ O K]

theorem finrank_int_eq_finrank_mul (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (X : Type) [AddCommGroup X] [Module O X] :
    Module.finrank ℤ X = Module.finrank ℤ O * Module.finrank O X := by
  have : CharZero (FractionRing O) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))
  have h := finrank_int_eq_fraction_mul O (FractionRing O) O
  rw [Module.finrank_self, mul_one] at h
  rw [finrank_int_eq_fraction_mul O (FractionRing O) X, h]

private theorem isTorsionFree_int_of_isTorsionFree (O : Type) [CommRing O] [IsDomain O] [CharZero O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.IsTorsionFree O Y] :
    Module.IsTorsionFree ℤ Y :=
  Module.IsTorsionFree.comap (S := O) (fun r : ℤ => (r : O))
    (fun r hr => IsRegular.of_ne_zero (Int.cast_ne_zero.mpr hr.ne_zero))
    (fun r m => Int.cast_smul_eq_zsmul O r m)

theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] : Module.Free ℤ Y := by
  haveI : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := fun a b h => by
    have ha := LinearMap.congr_fun hs a
    have hb := LinearMap.congr_fun hs b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, h]
  haveI : Module.IsTorsionFree O Y :=
    Function.Injective.moduleIsTorsionFree s hinj (fun r m => s.map_smul r m)
  haveI : Module.IsTorsionFree ℤ Y := isTorsionFree_int_of_isTorsionFree O Y
  exact Module.free_of_finite_type_torsion_free'

theorem genRank_le_sq (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] (q : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    genRank γ ≤ (q * Module.finrank ℤ O) ^ 2 := by
  haveI : Module.IsTorsionFree ℤ O := isTorsionFree_int_of_isTorsionFree O O
  haveI : Module.Free ℤ O := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  haveI : Module.Free ℤ X := free_int_of_projective O
  have hX' : Module.finrank ℤ X ≤ q * Module.finrank ℤ O := by
    rw [finrank_int_eq_finrank_mul O X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  show Module.finrank ℤ (Submodule.span ℤ (Set.range γ)) ≤ _
  calc Module.finrank ℤ (Submodule.span ℤ (Set.range γ))
      ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) := Submodule.finrank_le _
    _ = Module.finrank ℤ X * Module.finrank ℤ X := by
      show Module.finrank ℤ (X →ₗ[ℤ] X →ₗ[ℤ] ℤ) = _
      rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_self, mul_one]
    _ ≤ (q * Module.finrank ℤ O) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hX' hX'

private theorem nat_sInf_le_of_forall_le {s : Set ℕ} {N : ℕ} (h : ∀ k ∈ s, k ≤ N) : sInf s ≤ N := by
  rcases s.eq_empty_or_nonempty with hs | ⟨k, hk⟩
  · rw [hs, Nat.sInf_empty]
    exact Nat.zero_le _
  · exact (Nat.sInf_le hk).trans (h k hk)

theorem carrierDim_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro O _ _ _ _ bar _ q ψ lab hC
  refine ⟨(q * Module.finrank ℤ O) ^ 2, ?_⟩
  intro X _ _ _ _ hX β hβ hpos
  rw [hC X hX β hβ hpos]
  exact_mod_cast nat_sInf_le_of_forall_le (fun k hk => by
    obtain ⟨m, γ, -, -, rfl⟩ := hk
    exact genRank_le_sq O q X hX γ)

end GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBoundedStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_dimension_label_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded | exact GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSimplicialLabelledRefinement
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement

theorem exists_simpLab_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ lab : InvFun O, IsPolyFan bar q φ ∧ IsTwG w0 φ ∧ IsTwG w0 lab ∧ SimpLab bar q φ lab ∧ Subordinate bar q φ ψ := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ hT
  obtain ⟨lab, hlT, hlab⟩ := GlobalTheory.T.exists_carrier_dimension_label O bar w0 hb q ψ hD hψ hT
  obtain ⟨N, hN⟩ := GlobalTheory.T.carrier_dimension_label_bounded O bar hb q ψ lab hlab
  have key : ∀ d : ℕ, ∃ φ : InvFun O, IsTwG w0 φ ∧ IsBaryStage bar q ψ lab φ (N - d) := by
    intro d
    induction d with
    | zero => exact ⟨ψ, hT, isBaryStage_start hψ hN⟩
    | succ d ih =>
      obtain ⟨φ, hφT, hφ⟩ := ih
      rcases Nat.eq_zero_or_pos (N - d) with h | h
      · exact ⟨φ, hφT, by rw [show N - (d + 1) = N - d by omega]; exact hφ⟩
      · have e : N - d = (N - (d + 1)) + 1 := by omega
        rw [e] at hφ
        exact GlobalTheory.T.barycentric_stage_extension O bar w0 hb q ψ lab φ _ hD hψ hT hlT hlab hφT hφ
  obtain ⟨φ, hφT, hφ⟩ := key N
  rw [Nat.sub_self] at hφ
  exact ⟨φ, lab, hφ.1, hφT, hlT, GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero _ bar q ψ lab φ hlab hφ, hφ.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSimplicialLabelledRefinementStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_simplicial_labelled_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ lab : InvFun O, IsPolyFan bar q φ ∧ IsTwG w0 φ ∧ IsTwG w0 lab ∧ SimpLab bar q φ lab ∧ Subordinate bar q φ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement | exact GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement

theorem exists_smooth_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ' γ → ψ.LinearOn γ := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ hT
  obtain ⟨φ, lab, hφ, hφT, hlT, hSL, hsub⟩ := GlobalTheory.T.exists_simplicial_labelled_refinement O bar w0 hb q ψ hD hψ hT
  obtain ⟨φ', h1, h2, h3, hsub'⟩ := GlobalTheory.T.exists_smooth_subordinate_fan O bar w0 hb q φ lab hD hφ hφT hlT hSL
  exact ⟨φ', h1, h2, h3, fun X _ _ _ _ hX m γ hγ => (hsub'.trans hsub).linearOn hX hγ.isCell⟩

end GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinementStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_smooth_polyhedral_fan_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], GlobalTheory.PolFan.Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ' : InvFun O, IsPolFan bar q φ' ∧ NoSelfInt bar q φ' ∧ IsTwG w0 φ' ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone bar φ' γ → ψ.LinearOn γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement | exact GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement <;> assumption)
end
