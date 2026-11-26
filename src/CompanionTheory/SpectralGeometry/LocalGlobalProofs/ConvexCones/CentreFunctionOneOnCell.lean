module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestriction

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CentreFunctionOneOnCell
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CentreFunctionOneOnCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell


open GlobalTheory.PolFan.StarOnCell in
theorem starDepth_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β) ∧ (starDepth bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro O _ _ _ _ bar _hb q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := GlobalTheory.T.centreDepth_le_starDepth_of_cell O bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
    nlinarith
  ·
    intro β _ _ hβ heq
    have hβr : toReal β ∈ rcone γ := by obtain ⟨c, hc0, e⟩ := hβ; exact ⟨c, hc0, e⟩
    obtain ⟨m'', s'', h'', hf'', hpos'', t, ht, e⟩ :=
      GlobalTheory.StarCover.star_cover X m γ β₀ (toReal β) (fun i => (hγ.mem i).1) hγ.nonneg hne hin hβr
    have hpos''' : (0 : ℝ) < h'' β₀ := by exact_mod_cast hpos''

    have r2 := ell_of_eq h'' e
    rw [Fin.sum_univ_succ] at r2
    simp only [Fin.cons_zero, Fin.cons_succ] at r2
    have z2 : ∀ j, (h'' (γ (s'' j)) : ℝ) = 0 := fun j => by
      rw [(hf''.2 (s'' j)).2 ⟨j, rfl⟩, Int.cast_zero]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero] at r2
    have hle : (starDepth bar ψ w).evalZ β ≤ t 0 := by
      have := mul_starDepth_le hγ huniq h'' hf''.1 hpos'' hβ
      rw [r2] at this
      nlinarith

    have r1 := ell_of_eq h e
    rw [Fin.sum_univ_succ] at r1
    simp only [Fin.cons_zero, Fin.cons_succ] at r1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ t j.succ * (h (γ (s'' j)) : ℝ) := fun j _ =>
      mul_nonneg (ht _) (by exact_mod_cast hf.1 _)
    have hsum : ∑ j, t j.succ * (h (γ (s'' j)) : ℝ) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have hcone : InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) β := by
      refine inRCone_of_sum t ht e fun i hi => ?_
      refine Fin.cases (fun _ => ?_) (fun j hj => ?_) i hi
      · simpa using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) 0
      · have h0 : (h (γ (s'' j)) : ℝ) = 0 := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_left hj
        have h0' : h (γ (s'' j)) = 0 := by exact_mod_cast h0
        obtain ⟨k, hk⟩ := (hf.2 (s'' j)).1 h0'
        simpa [hk] using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k.succ
    exact exists_nat_of_inRCone _ β hcone

end GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CentreFunctionOneOnCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_starDepth_le_faceCut_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), IsPolyFan bar q ψ → IsCentreSet bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β) ∧ (starDepth bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarDepthOnCell.starDepth_on_cell <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellCone
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
open GlobalTheory.PolFan.Mark.FaceIn

namespace GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum

theorem inRCone_of_add : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    GlobalTheory.PolFan.Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro O _ _ _ _ bar hb q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone (bar := bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β + x] ![1] (by simp [hs])
        (by simpa using hsp) (by simp)
    obtain ⟨S, -, hcov⟩ := (hψ X hX).finite
    obtain ⟨e, mm, γ, c, hγ, -, hc, hsum⟩ := hcov _ hR
    refine ⟨_, mm, fun i => pull e.symm.toLinearMap (γ i), CarDim.isCell_pull_equiv hγ e.symm, ⟨c, hc, ?_⟩, rfl⟩
    exact LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply] using this
  obtain ⟨n, γ, hγ, hγs, hrk⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨N', ℓ', hN', h1', h2', h3'⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have e0 := apply_eq_of_inRCone hγ.linear h1 hγs
  rw [map_add (f := _), Int.cast_add, hadd, mul_add] at e0
  have eβ : (N : ℝ) * ψ.evalZ β = ℓ β := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have ex : (N : ℝ) * ψ.evalZ x = ℓ x := by linarith [h2 β hβ hβp, h2 x hx hxp]
  have hγβ : InRCone γ β := by
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hβp eβ
    exact inRCone_of_nsmul_eq hk hc
  obtain ⟨cx, -, hcx⟩ : InRCone γ x := by
    obtain ⟨k, c, hk, hc⟩ := h3 x hx hxp ex
    exact inRCone_of_nsmul_eq hk hc
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (N : ℤ) • ℓ' - (N' : ℤ) • ℓ with hh
  have happ : ∀ u, (h u : ℝ) = N * ℓ' u - N' * ℓ u := fun u => by simp [hh]
  let Z : Finset (Fin n) := Finset.univ.filter fun j => h (γ j) = 0
  let s : Fin Z.card ↪ Fin n := (Z.orderEmbOfFin rfl).toEmbedding
  have hcut : IsFaceCut γ s h := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have : (0 : ℝ) ≤ h (γ j) := by
        rw [happ, h1]
        have := mul_le_mul_of_nonneg_left (h2' _ (hγ.mem j) (hγ.nonneg j)) hNr.le
        linarith
      exact_mod_cast this
    · have : Set.range s = Z := Z.range_orderEmbOfFin rfl
      rw [this]
      simp [Z]
  have hface := GlobalTheory.CompanionTheory.Ar.Fan.FaceCells.isCell_face_of_isFaceCut O bar hb q ψ hψ X hX hD n γ hγ _ s h hcut
  have hβ0 : h β = 0 := by
    have : (h β : ℝ) = 0 := by
      rw [happ, apply_eq_of_inRCone hv.linear h1' hvβ, ← eβ]; ring
    exact_mod_cast this
  have hle : genRank γ ≤ genRank fun j => γ (s j) := by
    rw [hlab X hX _ hs hsp, hlab X hX _ hβ hβp, Nat.cast_inj] at hl
    rw [hrk, hl]
    exact Nat.sInf_le ⟨_, _, hface, inRCone_face hcut hγβ hβ0, rfl⟩
  have hall := apply_eq_zero_of_genRank_le (h := h) (fun j => (hcut.2 _).2 ⟨j, rfl⟩) hle
  have hx0 : (h x : ℝ) = 0 := by
    rw [apply_eq_of_toReal_eq hcx h]
    simp [hall]
  rw [happ, ← ex] at hx0
  have ex' : (N' : ℝ) * ψ.evalZ x = ℓ' x := by
    have : (N : ℝ) * (N' * ψ.evalZ x - ℓ' x) = 0 := by linarith
    linarith [(mul_eq_zero.1 this).resolve_left hNr.ne']
  obtain ⟨k, c, hk, hc⟩ := h3' x hx hxp ex'
  exact inRCone_of_nsmul_eq hk hc

end GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psd_balanced_form_mem_cell_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → GlobalTheory.PolFan.Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms bar X, (∀ y, 0 ≤ x y y) → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add | exact GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.RationalConeOfSum.inRCone_of_add <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCell
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear

theorem starFun_linearOn : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (K D : ℕ), IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  intro O _ _ _ _ bar _ q ψ w K D hcent
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX m γ hγ hno
    have ps0 : ∀ B ∈ rcone γ, evalR (starDepth bar ψ w) B = 0 := fun B hB =>
      le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ bar ψ w X m γ B 0 hγ hB le_rfl fun v hv hp hw hin _ _ _ =>
        absurd (hno v hv hp hin) (by rw [hw]; norm_num)) (starDepth_eval_nonneg _)
    have psγ : ∀ i, (starDepth bar ψ w).evalZ (γ i) = 0 := fun i => by
      rw [← evalR_toReal]; exact ps0 _ (inRCone_self γ i)
    rw [linearOn_iff]
    intro c hc
    rw [starFun_evalR, (linearOn_iff ψ γ).1 hγ.linear c hc, ps0 _ ⟨c, hc, rfl⟩, add_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [starFun_evalZ, psγ i]; ring
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hh
    obtain ⟨-, hC2, hC3⟩ := hcent X hX
    have uniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
      fun v hv hp hw hin => hC3 m γ hγ v hv hp β₀ hβ₀ hp₀ hw hw₀ hin hin₀
    have hne : β₀ ≠ 0 := by
      rintro rfl
      have := hC2 0 hβ₀ hp₀ hw₀ 2 0 (by simp)
      norm_num at this
    obtain ⟨e, he, hβe⟩ := id hin₀
    have coords : ∀ (a : ℝ) (d : Fin m' → ℝ), a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) =
        ∑ i, (a * e i + Function.extend s d 0 i) • toReal (γ i) := fun a d => by
      rw [hβe, Finset.smul_sum, ← sum_extend_smul_starLin s d (fun i => toReal (γ i))]
      simp only [add_smul, mul_smul, Finset.sum_add_distrib]
    have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hcut.2 (s j)).2 ⟨j, rfl⟩
    have psv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR (starDepth bar ψ w) (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a := by
      intro a d ha hd
      have hB : a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) ∈ rcone γ :=
        ⟨fun i => a * e i + Function.extend s d 0 i,
          fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i), coords a d⟩
      refine le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ bar ψ w X m γ _ a hγ hB ha fun v hv hp hw hin t ht hBt => ?_)
        (GlobalTheory.T.centreDepth_le_starDepth_of_cell _ bar ψ w X m γ _ β₀ a hγ hB hβ₀ hp₀ hw₀ hin₀ hne uniq ha ?_)
      · rw [uniq v hv hp hw hin] at hBt
        obtain ⟨g, hg, hBg⟩ := hBt
        have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) h
          (β := Sum.elim (fun j => γ (s j)) (fun o : Option (Fin m) => o.elim β₀ γ))
          (c := Sum.elim d (fun o : Option (Fin m) => o.elim (a - t) fun i => -g i)) (by
            simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
              LinearMap.id_apply, neg_smul, Finset.sum_neg_distrib]
            rw [← hBg, sub_smul]
            abel)
        simp only [Fintype.sum_sum_type, Fintype.sum_option, Sum.elim_inl, Sum.elim_inr, Option.elim,
          hs0, Int.cast_zero, mul_zero, Finset.sum_const_zero, zero_add, neg_mul, Finset.sum_neg_distrib] at rel
        have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hcut.1 i)
        have hh' : (0 : ℝ) < h β₀ := by exact_mod_cast hh
        nlinarith
      · exact ⟨Function.extend s d 0, extend_nonneg_starLin s hd, by
          rw [add_sub_cancel_left, sum_extend_smul_starLin]⟩
    have psβ : (starDepth bar ψ w).evalZ β₀ = 1 := by
      have := psv 1 0 zero_le_one fun _ => le_rfl
      simpa using this
    have psγs : ∀ j, (starDepth bar ψ w).evalZ (γ (s j)) = 0 := fun j => by
      have := psv 0 (Pi.single j 1) le_rfl fun i => by by_cases hi : i = j <;> simp [Pi.single_apply, hi]
      simpa [Pi.single_apply] using this
    have ψv : ∀ (a : ℝ) (d : Fin m' → ℝ), 0 ≤ a → (∀ j, 0 ≤ d j) →
        evalR ψ (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a * ψ.evalZ β₀ + ∑ j, d j * ψ.evalZ (γ (s j)) := by
      intro a d ha hd
      have hψβ : ψ.evalZ β₀ = ∑ i, e i * ψ.evalZ (γ i) := by
        rw [← evalR_toReal, hβe, (linearOn_iff ψ γ).1 hγ.linear e he]
      have hx := sum_extend_smul_starLin s d fun i => ψ.evalZ (γ i)
      simp only [smul_eq_mul] at hx
      rw [coords, (linearOn_iff ψ γ).1 hγ.linear _
        (fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i)), hψβ, Finset.mul_sum, ← hx]
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib]
    rw [linearOn_iff]
    intro c hc
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [starFun_evalR, ψv _ _ (hc 0) (fun j => hc _), psv _ _ (hc 0) (fun j => hc _), starFun_evalZ, psβ]
    simp only [starFun_evalZ, psγs, add_zero]
    have e1 : ∑ j : Fin m', c j.succ * ((D : ℝ) * (K * ψ.evalZ (γ (s j)))) =
        D * K * ∑ j : Fin m', c j.succ * ψ.evalZ (γ (s j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1]; ring

end GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_function_linear_on_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O) (K D : ℕ), IsCentreSet bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | exact GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn <;> assumption)
end
end
