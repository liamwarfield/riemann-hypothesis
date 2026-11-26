module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCell
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

theorem exists_semilinear_pull_of_evalZ_eq_one : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  intro O _ w0 X₀ _ _ v X _ _ _ β h1
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.evalZ, (orbFun O w0 v).eval_eq hr, orbFun_toFun] at h1
  split_ifs at h1 with hc
  swap
  · exact absurd h1 zero_ne_one
  obtain ⟨-, σ, hσ, s, hs, H⟩ := hc

  let g : (Fin n → O) →+ X :=
    { toFun := fun a => r (twv σ a)
      map_zero' := by rw [twv_zero, map_zero]
      map_add' := fun a b => by
        have e : twv σ (a + b) = twv σ a + twv σ b := funext fun _ => map_add σ _ _
        rw [e, map_add (f := _)] }
  have hg : ∀ a, g a = r (twv σ a) := fun _ => rfl
  have hgs : ∀ (c : O) a, g (c • a) = σ c • g a := fun c a => by
    rw [hg, hg, twv_smul, map_smul]
  have hgsurj : Function.Surjective g := fun x => by
    obtain ⟨a, ha⟩ := hr x
    exact ⟨twv σ.symm a, by rw [hg, twv_twv_symm, ha]⟩
  have hker : ∀ z, g z = 0 → s z = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ (s z)
    rw [← hx]
    refine (Submodule.Quotient.mk_eq_zero _).2 fun c y => ?_
    obtain ⟨b, hb⟩ := hs (Submodule.Quotient.mk y)
    have h1 := H (c • z) b (c • x) y
      (by rw [Submodule.Quotient.mk_smul, map_smul]; exact congrArg _ hx) hb.symm
    have e : r (twv σ (c • z)) = 0 := by rw [← hg, hgs, hz, smul_zero]
    dsimp only at h1
    rw [e, map_zero, LinearMap.zero_apply] at h1
    exact_mod_cast h1.symm
  have hwd : ∀ a a', g a = g a' → s a = s a' := fun a a' h => by
    have := hker (a - a') (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  let pre : X → (Fin n → O) := fun x => (hgsurj x).choose
  have hpre : ∀ x, g (pre x) = x := fun x => (hgsurj x).choose_spec
  have hf : ∀ a, s (pre (g a)) = s a := fun a => hwd _ _ (hpre _)
  let f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
    { toFun := fun x => s (pre x)
      map_zero' := by
        have := hf 0
        rw [map_zero] at this
        rw [this, map_zero]
      map_add' := fun x y => by
        have := hf (pre x + pre y)
        rw [map_add (f := _), hpre, hpre] at this
        rw [this, map_add (f := _)] }
  have hfg : ∀ a, f (g a) = s a := hf
  refine ⟨σ.symm, f, by rw [RingEquiv.symm_apply_eq, hσ], fun q => ?_, fun c x => ?_, fun x y x₀ y₀ hx hy => ?_⟩
  · obtain ⟨a, rfl⟩ := hs q
    exact ⟨g a, hfg a⟩
  · obtain ⟨a, rfl⟩ := hgsurj x
    have e : c • g a = g (σ.symm c • a) := by rw [hgs, σ.apply_symm_apply]
    rw [e, hfg, hfg, map_smul]
  · obtain ⟨a, rfl⟩ := hgsurj x
    obtain ⟨b, rfl⟩ := hgsurj y
    rw [hfg] at hx hy
    have h := H a b x₀ y₀ hx hy
    dsimp only at h
    rw [← hg, ← hg] at h
    exact_mod_cast h

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicatorStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator : ∀ {O : Type} [CommRing O] (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] (v : LinearMap.BilinForm ℤ X₀)
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X), (OrbMark.orbFun O w0 v).evalZ β = 1 →
  ∃ (τ : O ≃+* O) (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule O X₀)), τ w0 = w0 ∧ Function.Surjective f ∧
    (∀ (a : O) (x : X), f (a • x) = τ a • f x) ∧
    ∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀ := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | exact GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one | (intros; apply GlobalTheory.PolFan.OrbMark.exists_semilinear_pull_of_evalZ_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCells
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCells
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem sum_extend_smul_starLin {M : Type} [AddCommMonoid M] [Module ℝ M] {m m' : ℕ} (s : Fin m' ↪ Fin m)
    (d : Fin m' → ℝ) (f : Fin m → M) : ∑ i, Function.extend s d 0 i • f i = ∑ j, d j • f (s j) := by
  symm
  refine Fintype.sum_of_injective s s.injective _ _ (fun i hi => ?_) fun j => by rw [s.injective.extend_apply]
  rw [Function.extend_apply' _ _ _ hi]; simp

theorem extend_nonneg_starLin {m m' : ℕ} (s : Fin m' ↪ Fin m) {d : Fin m' → ℝ} (hd : ∀ j, 0 ≤ d j) (i : Fin m) :
    0 ≤ Function.extend s d 0 i := by
  by_cases hi : ∃ j, s j = i
  · obtain ⟨j, rfl⟩ := hi; rw [s.injective.extend_apply]; exact hd j
  · rw [Function.extend_apply' _ _ _ hi]; rfl

theorem starFun_linearOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w K D hcent
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX m γ hγ hno
    have ps0 : ∀ B ∈ rcone γ, evalR (starDepth H.bar ψ w) B = 0 := fun B hB =>
      le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ B 0 hγ hB le_rfl fun v hv hp hw hin _ _ _ =>
        absurd (hno v hv hp hin) (by rw [hw]; norm_num)) (starDepth_eval_nonneg _)
    have psγ : ∀ i, (starDepth H.bar ψ w).evalZ (γ i) = 0 := fun i => by
      rw [← evalR_toReal]; exact ps0 _ (inRCone_self γ i)
    rw [linearOn_iff]
    intro c hc
    rw [starFun_evalR, (linearOn_iff ψ γ).1 hγ.linear c hc, ps0 _ ⟨c, hc, rfl⟩, add_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [starFun_evalZ, psγ i]; ring
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hh
    obtain ⟨-, hC2, hC3⟩ := hcent X hX
    have uniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
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
        evalR (starDepth H.bar ψ w) (a • toReal β₀ + ∑ j, d j • toReal (γ (s j))) = a := by
      intro a d ha hd
      have hB : a • toReal β₀ + ∑ j, d j • toReal (γ (s j)) ∈ rcone γ :=
        ⟨fun i => a * e i + Function.extend s d 0 i,
          fun i => add_nonneg (mul_nonneg ha (he i)) (extend_nonneg_starLin s hd i), coords a d⟩
      refine le_antisymm (GlobalTheory.T.evalR_starDepth_le_of_centre_bound _ H.bar ψ w X m γ _ a hγ hB ha fun v hv hp hw hin t ht hBt => ?_)
        (GlobalTheory.T.centreDepth_le_starDepth_of_cell _ H.bar ψ w X m γ _ β₀ a hγ hB hβ₀ hp₀ hw₀ hin₀ hne uniq ha ?_)
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
    have psβ : (starDepth H.bar ψ w).evalZ β₀ = 1 := by
      have := psv 1 0 zero_le_one fun _ => le_rfl
      simpa using this
    have psγs : ∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0 := fun j => by
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

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCellsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_function_linearOn_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (K D : ℕ), IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → (starFun H.bar ψ w K D).LinearOn γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (starFun H.bar ψ w K D).LinearOn (Fin.cons β₀ fun j => γ (s j))) := by
  first | exact @GlobalTheory.PolFan.starFun_linearOn | exact GlobalTheory.PolFan.starFun_linearOn | (intros; apply GlobalTheory.PolFan.starFun_linearOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonal
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem exists_zsmul_mem_of_finrank_le_of_le {M : Type} [AddCommGroup M] {N L : Submodule ℤ M}
    [Module.Finite ℤ L] (hNL : N ≤ L) (hr : Module.finrank ℤ L ≤ Module.finrank ℤ N) {x : M} (hx : x ∈ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have h1 := Submodule.finrank_quotient_add_finrank (N.comap L.subtype)
  have h2 : Module.finrank ℤ (N.comap L.subtype) = Module.finrank ℤ N :=
    (Submodule.comapSubtypeEquivOfLe hNL).finrank_eq
  have h0 : Module.finrank ℤ (L ⧸ N.comap L.subtype) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem vanish_of_inRCone_of_genRank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hdom m τ hτ β hβ hβp hβc hrk j y hy
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
  have hcell : IsCell H.bar ψ (fun k => τ (s k)) :=
    isCell_face_of_isFaceCut E H q ψ hψ X hX hdom m τ hτ _ s hf hcut
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
  have hle : sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
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

end GlobalTheory.PolFan.Mark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellLeastDimVanishesWhereFormVanishesDiagonalStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMField
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark.FaceIn

section Lattice

variable {X : Type} [AddCommGroup X]

theorem inRCone_of_nsmul_eq {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {c : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * γ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * β a b = ∑ i, (c i : ℝ) * γ i a b := by exact_mod_cast h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_right_inj' hk', h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  obtain ⟨c, hc, e⟩ := hβ
  have e1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at e1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hc j) (show (0 : ℝ) ≤ h (γ j) by exact_mod_cast hcut.1 j)).1 e1.symm
  have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
    have hne : (h (γ j) : ℝ) ≠ 0 := fun h0 => hj ((hcut.2 j).1 (by exact_mod_cast h0))
    exact (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
  refine ⟨fun i => c (s i), fun i => hc _, ?_⟩
  rw [e]
  classical
  rw [← Finset.sum_map Finset.univ s (fun j => c j • toReal (γ j))]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
  rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

theorem apply_eq_zero_of_genRank_le {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' → Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h0 : ∀ j, h (γ (s j)) = 0) (hr : genRank γ ≤ genRank fun j => γ (s j))
    (j : Fin m) : h (γ j) = 0 := by
  unfold genRank at hr
  set B := Submodule.span ℤ (Set.range γ) with hB
  set A := Submodule.span ℤ (Set.range fun j => γ (s j)) with hA
  haveI : Module.Finite ℤ B := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  have hAB : A ≤ B := Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨s j, rfl⟩)
  have hAk : A ≤ LinearMap.ker h := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
  set K : Submodule ℤ B := LinearMap.ker (h.domRestrict B) with hK
  have h1 : Module.finrank ℤ A ≤ Module.finrank ℤ K := by
    rw [← (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq]
    exact Submodule.finrank_mono fun y hy => hAk hy
  have h2 := Submodule.finrank_quotient_add_finrank K
  have h3 : Module.finrank ℤ (B ⧸ K) = 0 := by omega
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h3
    (Submodule.Quotient.mk ⟨γ j, Submodule.subset_span ⟨j, rfl⟩⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at e
  have e' : a * h (γ j) = 0 := by simpa [hK] using e
  exact (mul_eq_zero.1 e').resolve_left ha

end Lattice

theorem apply_eq_of_inRCone {O : Type} [CommRing O] {ψ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : ψ.LinearOn γ) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (γ i) : ℝ) = N * ψ.evalZ (γ i)) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) : (ℓ β : ℝ) = N * ψ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff ψ γ).1 hγ c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem inRCone_of_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X,
    (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) →
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  intro E _ _ _ H q ψ lab hψ hlab X _ _ _ _ hX hD m v hv β hβ hβp hvβ x hx hxp hadd hl
  classical
  have hs : β + x ∈ balForms H.bar X := Submodule.add_mem _ hβ hx
  have hsp : ∀ y, 0 ≤ (β + x) y y := fun y => add_nonneg (hβp y) (hxp y)
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ (β + x) ∧
      genRank γ = k}.Nonempty := by
    have hR : toReal (β + x) ∈ psdCone (bar := H.bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β + x] ![1] (by simp [hs])
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
  have hface := isCell_face_of_isFaceCut E H q ψ hψ X hX hD n γ hγ _ s h hcut
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

end GlobalTheory.PolFan.Mark.FaceIn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeCellOfInFaceOfCellFormCMFieldStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  first | exact @GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | exact GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | (intros; apply GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan.StarOnCell

variable {X : Type} [AddCommGroup X]

theorem ell_of_eq {n : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    {u : Fin n → LinearMap.BilinForm ℤ X} {c : Fin n → ℝ} (h : toReal β = ∑ i, c i • toReal (u i)) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) c : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, h]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem ell_of_sub_mem {m : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β v : LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {t : ℝ} (h : toReal β - t • toReal v ∈ rcone γ) :
    ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ (ℓ β : ℝ) = t * ℓ v + ∑ j, d j * ℓ (γ j) := by
  obtain ⟨d, hd, e⟩ := h
  refine ⟨d, hd, ?_⟩
  have e' : toReal β = ∑ i : Fin (m + 1), (Fin.cons t d : Fin (m + 1) → ℝ) i •
      toReal ((Fin.cons v γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← e]
    abel
  rw [ell_of_eq ℓ e', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem inRCone_of_sum {p n : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {u : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i) (e : toReal β = ∑ i, x i • toReal (δ i))
    (h : ∀ i, x i ≠ 0 → InRCone u (δ i)) : InRCone u β := by
  classical
  have hi : ∀ i, ∃ g : Fin n → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (u j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨c, hc, hcs⟩ := h i h0
    exact ⟨fun j => x i * c j, fun j => mul_nonneg (hx i) (hc j), by
      rw [hcs, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [e, Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem exists_nat_of_inRCone {n : ℕ} (u : Fin n → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : InRCone u β) : ∃ (k : ℕ) (c : Fin n → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  obtain ⟨r, v, hiff, -⟩ := GlobalTheory.MinkWeylReal.cone_orthant_fg (n + 1) ∅
    (Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ))
    Set.finite_empty
  have h1 : (∀ i, 0 ≤ (Fin.cons 1 c : Fin (n + 1) → ℝ) i) ∧
      (∀ a ∈ (∅ : Set (Fin (n + 1) → ℤ)), ∑ i, (a i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i ≤ 0) ∧
      (∀ b ∈ Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ),
        ∑ i, (b i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i = 0) := by
    refine ⟨fun i => Fin.cases (by simp) (fun j => by simpa using hc j) i, by simp, ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have he := LinearMap.congr_fun₂ e a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg, mul_one]
    rw [he]
    rw [show ∑ i, (u i a b : ℝ) * c i = ∑ i, c i * (u i a b : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨e', he', ht⟩ := (hiff _).1 h1
  have h0 := congr_fun ht 0
  simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  obtain ⟨k, hk⟩ : ∃ k, v k 0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    simp [hne] at h0
  have hv := (hiff fun i => (v k i : ℝ)).2 ⟨Pi.single k 1, fun j => by
    by_cases h : j = k <;> simp [Pi.single_apply, h], by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp⟩
  obtain ⟨-, -, hV⟩ := hv
  refine ⟨v k 0, fun i => v k i.succ, Nat.pos_of_ne_zero hk, ?_⟩
  ext a b
  have h2 := hV _ ⟨(a, b), rfl⟩
  rw [Fin.sum_univ_succ] at h2
  simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg] at h2
  have h3 : ((v k 0 : ℤ) * β a b : ℝ) = ((∑ i, (v k i.succ : ℤ) * u i a b : ℤ) : ℝ) := by
    push_cast
    rw [show ∑ i, ((v k i.succ : ℝ) * (u i a b : ℝ)) = ∑ i, (u i a b : ℝ) * (v k i.succ : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    linarith
  have h4 : (v k 0 : ℤ) * β a b = ∑ i, (v k i.succ : ℤ) * u i a b := by exact_mod_cast h3
  simpa [LinearMap.sum_apply] using h4

end GlobalTheory.PolFan.StarOnCell

namespace GlobalTheory.PolFan.StarOnCell

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem mul_starDepth_le (hγ : IsCell bar ψ γ) {β₀ : LinearMap.BilinForm ℤ X}
    (huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hh : ∀ j, 0 ≤ h (γ j)) (hpos : 0 < h β₀)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hhβ : (0 : ℝ) ≤ h β := by
    rw [ell_of_eq h e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hh i)
  have key := evalR_starDepth_le O bar ψ w X m γ (toReal β) ((h β : ℝ) / h β₀) hγ ⟨c, hc, e⟩
    (div_nonneg hhβ hpos'.le) (fun v hv hvp hwv hvin t ht hrest => by
      obtain rfl := huniq v hv hvp hwv hvin
      obtain ⟨d, hd, hrel⟩ := ell_of_sub_mem h hrest
      rw [le_div_iff₀ hpos']
      have : (0 : ℝ) ≤ ∑ j, d j * h (γ j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (by exact_mod_cast hh j)
      linarith)
  rw [evalR_toReal] at key
  calc (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β₀ * ((h β : ℝ) / h β₀) :=
        mul_le_mul_of_nonneg_left key hpos'.le
    _ = h β := by field_simp

end GlobalTheory.PolFan.StarOnCell


open GlobalTheory.PolFan.StarOnCell in
theorem GlobalTheory.PolFan.starDepth_on_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X,
    (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧
    (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β →
      ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧
        k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro E _ _ _ H q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := GlobalTheory.T.centreDepth_le_starDepth_of_cell (𝓞 E) H.bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth H.bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
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
    have hle : (starDepth H.bar ψ w).evalZ β ≤ t 0 := by
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
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starDepth_le_on_centre_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧ (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β → ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧ k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  first | exact @GlobalTheory.PolFan.starDepth_on_cell | exact GlobalTheory.PolFan.starDepth_on_cell | (intros; apply GlobalTheory.PolFan.starDepth_on_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl.WitTr

open GlobalTheory.Mem.Db

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)


set_option maxHeartbeats 8000000 in
def nchTTr {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) :
    NchT w (setDivZ Z N h) Wt { nch with } :=
  { n with tp := { n.tp with }, tie := { n.tie with }, chrPsi := n.chrPsi }


set_option maxHeartbeats 8000000 in
def kerTr {Gt : GatTies (w.D Z)} {cmp : LatCmp (w.D Z)} {Gy : G.LatInst (w.D Z)} (k : KerFam (w.D Z) Gt cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) { Gt with } { cmp with } (w.tw (setDivZ Z N h)) { Gy with } :=
  fun u v g => { k u v g with }


set_option maxHeartbeats 8000000 in
def columnLocalDataTransportDivision (c : ColumnDataSplitPrimes K w Z)
    (hR : let t := DivTr.colTTr w Z N h c.toColT
          IsRecG K.s (w.D (setDivZ Z N h)) t.Gt t.cmp t.g.herm t.g.forms) :
    ColumnDataSplitPrimes K w (setDivZ Z N h) :=
  { DivTr.colTTr w Z N h c.toColT with isRec := hR, om := c.om }

end GlobalTheory.Mem.Top.Bl.WitTr

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDim
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDim
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.FlagBaseDim

theorem dims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) ∧ X.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ _ hL
  have hcard : Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  refine ⟨by rw [Φ.dim_eq k, hcard], ?_⟩
  obtain ⟨hj', -, -⟩ := hL
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.FlagBaseDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDimStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagComponent_dim_and_base_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) ∧ X.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.FlagBaseDim.dims | exact GlobalTheory.FlagBaseDim.dims | (intros; apply GlobalTheory.FlagBaseDim.dims <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

theorem evalZ_eq_sum_of_toReal_eq_addcone {O : Type} [CommRing O] (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {v : Fin m → LinearMap.BilinForm ℤ X} (hv : ψ.LinearOn v)
    {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (v i)) : ψ.evalZ β = ∑ i, c i * ψ.evalZ (v i) := by
  rw [← hv c hc]
  unfold InvFun.evalZ
  congr 1
  funext a b
  have := LinearMap.congr_fun₂ h a b
  simpa [LinearMap.sum_apply] using this

theorem evalZ_add_of_linearOn_inRCone (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X) (hv : ψ.LinearOn v)
    (β x : LinearMap.BilinForm ℤ X) (hβ : InRCone v β) (hx : InRCone v x) :
    ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  obtain ⟨a, ha, hβ⟩ := hβ
  obtain ⟨b, hb, hx⟩ := hx
  have hs : toReal (β + x) = ∑ i, (a i + b i) • toReal (v i) := by
    have : toReal (β + x) = toReal β + toReal x := LinearMap.ext₂ fun s t => by simp
    rw [this, hβ, hx, ← Finset.sum_add_distrib]
    simp only [add_smul]
  rw [evalZ_eq_sum_of_toReal_eq_addcone ψ hv (fun i => add_nonneg (ha i) (hb i)) hs,
    evalZ_eq_sum_of_toReal_eq_addcone ψ hv ha hβ, evalZ_eq_sum_of_toReal_eq_addcone ψ hv hb hx,
    ← Finset.sum_add_distrib]
  simp only [add_mul]

end GlobalTheory.PolFan.Mark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvFunEvalZAddOfLinearOnRealConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invFun_evalZ_add_of_linearOn_realCone : ∀ (O : Type) [CommRing O] (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), ψ.LinearOn v → ∀ β x : LinearMap.BilinForm ℤ X, InRCone v β → InRCone v x → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x := by
  first | exact @GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | exact GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone | (intros; apply GlobalTheory.PolFan.Mark.evalZ_add_of_linearOn_inRCone <;> assumption)
end
end
