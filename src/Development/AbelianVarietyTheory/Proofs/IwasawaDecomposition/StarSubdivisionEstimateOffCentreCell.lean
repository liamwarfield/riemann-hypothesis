module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearPullbackOfMarkedOrbitIndicator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey.OffCell

theorem lin_eq_sum {X : Type} [AddCommGroup X] {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X}
    {t : Fin n → ℝ} (hsum : toReal β = ∑ i, t i • toReal (u i)) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (ℓ β : ℝ) = ∑ i, t i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) t : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem inRCone_of_sum {X : Type} [AddCommGroup X] {n m : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {t : Fin n → ℝ} (ht : ∀ i, 0 ≤ t i)
    (hsum : toReal β = ∑ i, t i • toReal (u i)) (h : ∀ i, t i ≠ 0 → InRCone γ (u i)) : InRCone γ β := by
  have h' : ∀ i, ∃ c : Fin m → ℝ, (∀ j, 0 ≤ c j) ∧ t i • toReal (u i) = ∑ j, c j • toReal (γ j) := fun i => by
    by_cases h0 : t i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    · obtain ⟨c, hc, e⟩ := h i h0
      refine ⟨fun j => t i * c j, fun j => mul_nonneg (ht i) (hc j), ?_⟩
      rw [e, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  choose c hc e using h'
  refine ⟨fun j => ∑ i, c i j, fun j => Finset.sum_nonneg fun i _ => hc i j, ?_⟩
  rw [hsum, Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem inRCone_of_nsmul {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin m → ℕ} (hk : 0 < k) (e : k • β = ∑ i, c i • γ i) : InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨fun i => c i / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 := congrArg (fun B : LinearMap.BilinForm ℤ X => ((B a b : ℤ) : ℝ)) e
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h1
  push_cast at h1
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hk'.ne'
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by field_simp

theorem arith {K N C b h₀ f ps h l p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hb : 0 ≤ b) (hh₀ : 1 ≤ h₀) (hf : 1 ≤ f)
    (hfe : f = l - N * p) (hp : p ≤ b) (hps : ps ≤ 1) (hh : -h ≤ C * l) (hK : N + N * C + N ^ 2 * C * b + 1 ≤ K) :
    N * h₀ * ps - N * h < K * h₀ * (l - N * p) := by
  rw [← hfe]
  have hl : l = f + N * p := by linarith
  have hhf : 1 ≤ h₀ * f := by nlinarith
  have a1 : (N + N * C + N ^ 2 * C * b + 1) * (h₀ * f) ≤ K * (h₀ * f) := by gcongr
  have a2 : N * h₀ * ps ≤ N * (h₀ * f) := by
    rw [mul_assoc]; gcongr; linarith
  have a3 : N * C * f ≤ N * C * (h₀ * f) := by
    gcongr; nlinarith
  have a4 : N ^ 2 * C * b ≤ N ^ 2 * C * b * (h₀ * f) := le_mul_of_one_le_right (by positivity) hhf
  have a5 : N * (-h) ≤ N * (C * l) := by gcongr
  have a6 : N ^ 2 * C * p ≤ N ^ 2 * C * b := by gcongr
  rw [hl] at a5
  nlinarith

theorem off_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  intro E _ _ _ H q ψ w b hψ hw X _ _ _ _ hX hgen m γ N ℓ hγ hN hsw β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos C hC K hK β hβ hβn
    hoff
  have hon := (GlobalTheory.T.starDepth_le_on_centre_cell E H q ψ w hψ hw X hX m γ hγ β₀ hβ₀ hβ₀n hw₀ hc₀ m' s h hcut hpos).1
  obtain ⟨n, u, hu, hun, hlψ, hlp, hub, hu1, t, ht, hsum⟩ := hgen β hβ hβn
  have hh₀ : (1 : ℝ) ≤ h β₀ := by exact_mod_cast hpos
  have hoffu : ∀ i, ¬ InRCone γ (u i) → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) <
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i hi => by
    obtain ⟨z, hz⟩ := (hψ X hX).integral (u i) (hu i) (hun i)
    have hle := hsw.2.1 (u i) (hu i) (hun i)
    have hne : (N : ℝ) * ψ.evalZ (u i) ≠ ℓ (u i) := fun e => by
      obtain ⟨k, c, hk, e'⟩ := hsw.2.2 (u i) (hu i) (hun i) e
      exact hi (inRCone_of_nsmul hk e')
    have hlt : (N : ℤ) * z < ℓ (u i) := by
      have := lt_of_le_of_ne hle hne
      rw [hz] at this
      exact_mod_cast this
    have hf : (1 : ℝ) ≤ ℓ (u i) - N * ψ.evalZ (u i) := by
      rw [hz]
      have : (1 : ℤ) ≤ ℓ (u i) - N * z := by omega
      exact_mod_cast this
    refine arith (C := C) (b := b) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hh₀ hf rfl (hub i) (hu1 i) ?_ ?_
    · exact_mod_cast hC (u i) (hu i) (hun i)
    · exact_mod_cast hK
  have hall : ∀ i, (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i) ≤
      K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i)) := fun i => by
    by_cases hi : InRCone γ (u i)
    · rw [ell_eq_of_inRCone hγ.linear hsw hi, sub_self, mul_zero, mul_assoc, ← mul_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.2 (hon _ (hu i) (hun i) hi))
    · exact (hoffu i hi).le
  obtain ⟨i₀, hi₀, hi₀'⟩ : ∃ i, t i ≠ 0 ∧ ¬ InRCone γ (u i) := by
    by_contra hcon
    exact hoff (inRCone_of_sum ht hsum fun i hi => by_contra fun h' => hcon ⟨i, hi, h'⟩)
  have e1 : ψ.evalZ β = ∑ i, t i * ψ.evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff ψ u).1 hlψ t ht
  have e2 : (starDepth H.bar ψ w).evalZ β = ∑ i, t i * (starDepth H.bar ψ w).evalZ (u i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff _ u).1 hlp t ht
  have key : ∑ i, t i * ((N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ (u i) - N * h (u i)) <
      ∑ i, t i * (K * h β₀ * (ℓ (u i) - N * ψ.evalZ (u i))) :=
    Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hall i) (ht i))
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hoffu i₀ hi₀') (lt_of_le_of_ne (ht i₀) hi₀.symm)⟩
  rw [e1, e2, lin_eq_sum hsum h, lin_eq_sum hsum ℓ]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  convert key using 2 with i _ i _ <;> ring

end GlobalTheory.PolFan.StarKey.OffCell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionEstimateOffCentreCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_subdivision_estimate_off_centre_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)) (b : ℕ), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → ∀ C : ℕ, (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h β) ≤ C * ℓ β) → ∀ K : ℕ, N + N * C + N ^ 2 * C * b + 1 ≤ K → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ¬ InRCone γ β → (N : ℝ) * h β₀ * (starDepth H.bar ψ w).evalZ β - N * h β < K * h β₀ * (ℓ β - N * ψ.evalZ β) := by
  first | exact @GlobalTheory.PolFan.StarKey.OffCell.off_cell | exact GlobalTheory.PolFan.StarKey.OffCell.off_cell | (intros; apply GlobalTheory.PolFan.StarKey.OffCell.off_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendedRaysMarkedFormPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendedRaysMarkedFormPieces
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem exists_desc_rays_pullAdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]
  [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms H.bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, hm i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) (τ : 𝓞 E ≃+* 𝓞 E)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)), τ H.w0 = H.w0 → Function.Surjective f →
    (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  intro E _ _ _ H X₀ _ _ _ m₀ δ₀ hm hpos hli hprim v t ht hv X _ _ _ β τ f hτ hf hsm hβ
  classical
  generalize hK : (CarDim.orad v : Submodule (𝓞 E) X₀) = K at *
  have hvan : ∀ i, 0 < t i → ∀ x ∈ K, ∀ y, δ₀ i x y = 0 := by
    intro i hi x hx y
    have hxx : v x x = 0 := by rw [← hK] at hx; simpa using (CarDim.mem_orad.1 hx) 1 x
    have hsum := LinearMap.congr_fun₂ hv x x
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hxx, Int.cast_zero] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (ht j) (Int.cast_nonneg (hpos j x))).1 hsum.symm i (Finset.mem_univ _)
    have h0 : δ₀ i x x = 0 := by
      rcases mul_eq_zero.1 hall with h | h
      · exact absurd h hi.ne'
      · exact_mod_cast h
    exact ConeSub.eq_zero_of_self_eq_zero (δ₀ i) (hm i).1 (hpos i) h0 y
  have hex : ∀ i, ∃ u : LinearMap.BilinForm ℤ (X₀ ⧸ K), 0 < t i → pull K.mkQ u = δ₀ i := by
    intro i
    by_cases hi : 0 < t i
    · obtain ⟨u, hu⟩ := CarDim.exists_pull_mkQ_eq_of_vanish K (δ₀ i) (hvan i hi)
        (fun x y hy => by rw [(hm i).1]; exact hvan i hi y hy x)
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose u hu using hex
  have hU : ∀ i, 0 < t i → ∀ y₀ z₀ : X₀, u i (Submodule.Quotient.mk y₀) (Submodule.Quotient.mk z₀) = δ₀ i y₀ z₀ :=
    fun i hi y₀ z₀ => LinearMap.congr_fun₂ (hu i hi) y₀ z₀
  have hq : ∀ z : X₀ ⧸ K, ∃ z₀ : X₀, Submodule.Quotient.mk z₀ = z := Submodule.Quotient.mk_surjective K
  let P : LinearMap.BilinForm ℤ (X₀ ⧸ K) →ₗ[ℤ] LinearMap.BilinForm ℤ X₀ :=
    { toFun := pull K.mkQ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine ⟨u, ?_, ?_, ?_⟩
  · refine LinearMap.ext₂ fun x y => ?_
    obtain ⟨x₀, hx₀⟩ := hq (f x)
    obtain ⟨y₀, hy₀⟩ := hq (f y)
    have h1 := LinearMap.congr_fun₂ hv x₀ y₀
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pullAdd_apply] at h1 ⊢
    rw [hβ x y x₀ y₀ hx₀ hy₀, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases (ht i).lt_or_eq with hi | hi
    · rw [← hx₀, ← hy₀, hU i hi]
    · rw [← hi, zero_mul, zero_mul]
  · have hδ : LinearIndependent ℤ (fun i : {i // 0 < t i} => δ₀ i) := hli.comp _ Subtype.val_injective
    have hu' : LinearIndependent ℤ (fun i : {i // 0 < t i} => u i) := by
      refine LinearIndependent.of_comp P ?_
      convert hδ using 1
      funext i
      exact hu i i.2
    exact hu'.map' (pullAddLin f) (LinearMap.ker_eq_bot.2 (pullAdd_injective hf))
  · intro i hi
    refine ⟨hu i hi, ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, fun k β' hk => ?_, fun lab hlab => ?_⟩
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, ← hy₀, ← hz₀, hU i hi]
      exact (hm i).1 y₀ z₀
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      obtain ⟨z₀, hz₀⟩ := hq (f z)
      simp only [pullAdd_apply, hsm, ← hy₀, ← hz₀, ← Submodule.Quotient.mk_smul, hU i hi]
      rw [(hm i).2, GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation E H τ a]
    · obtain ⟨y₀, hy₀⟩ := hq (f y)
      simp only [pullAdd_apply, ← hy₀, hU i hi]
      exact hpos i y₀
    · obtain ⟨ζ, hζ⟩ : ∃ ζ : LinearMap.BilinForm ℤ (X₀ ⧸ K), (k : ℤ) • ζ = u i := by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · refine ⟨0, ?_⟩
          have : pullAdd f (u i) = pullAdd f 0 := by
            rw [← hk]; ext; simp
          rw [pullAdd_injective hf this]; simp
        · have hk0' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
          have hval : ∀ x y, (k : ℤ) * β' x y = u i (f x) (f y) := fun x y => by
            rw [← pullAdd_apply, ← hk]; simp
          obtain ⟨ζ, hζ⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β'
            (fun x hx y => by
              have := hval x y
              rw [hx, map_zero, LinearMap.zero_apply] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
            (fun x hx y => by
              have := hval y x
              rw [hx, map_zero] at this
              exact (mul_eq_zero.1 this).resolve_left hk0')
          refine ⟨ζ, LinearMap.ext₂ fun a b => ?_⟩
          obtain ⟨x, rfl⟩ := hf a
          obtain ⟨y, rfl⟩ := hf b
          simp [hζ, hval]
      refine isPrim_eq_one_of_smul_eq H.bar (δ₀ i) (hm i) (hprim i) k (pull K.mkQ ζ) ?_
      rw [← hu i hi, ← hζ]
      ext a b
      simp
    · have h1 := eval_pull_semilinear_of_isTwInv E H lab hlab τ hτ f hf hsm (fun a b => (u i a b : ℝ))
      rw [← hu i hi, evalZ_pull lab K.mkQ_surjective]
      exact h1

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendedRaysMarkedFormPiecesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_rays_marked_form_pieces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]
  [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms H.bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, hm i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) (τ : 𝓞 E ≃+* 𝓞 E)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)), τ H.w0 = H.w0 → Function.Surjective f →
    (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | exact GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | (intros; apply GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellRayInConeOfMarkedFormPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellRayInConeOfMarkedFormPieces
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem exists_face_coord_of_linearOn {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ γ)
    (hind : LinearIndependent ℤ γ) {e : Fin k → LinearMap.BilinForm ℤ X} (hem : ∀ i, e i ∈ balForms bar X)
    (hen : ∀ i y, 0 ≤ e i y y) (hel : φ.LinearOn e) {v : LinearMap.BilinForm ℤ X} {t : Fin m → ℝ} {b : Fin k → ℝ}
    (ht : ∀ i, 0 ≤ t i) (hb : ∀ i, 0 < b i) (hvt : toReal v = ∑ i, t i • toReal (γ i))
    (hvb : toReal v = ∑ i, b i • toReal (e i)) (j : Fin k) :
    ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (e j) = ∑ i, a i • toReal (γ i) := by
  have h := GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint bar φ γ e hγ hem hen hel v t b ht hb hvt hvb
  choose a ha he using h
  have h1 : toReal v = ∑ i, (∑ l, b l * a l i) • toReal (γ i) := by
    rw [hvb]
    simp only [he, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : (fun i => (∑ l, b l * a l i) - t i) = 0 := by
    refine eq_zero_of_toReal_rel (u := γ) (v := (![] : Fin 0 → _)) (s := ![]) (fun d c hc => ?_) ?_
    · funext i
      exact Fintype.linearIndependent_iff.1 hind c (by simpa using hc) i
    · simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← hvt]
      simp
  refine ⟨a j, ha j, fun i hi => ?_, he j⟩
  have h3 : ∑ l, b l * a l i = 0 := by
    have := congrFun h2 i
    simpa [hi] using this
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => mul_nonneg (hb l).le (ha l i)).1 h3 j (Finset.mem_univ _)
  exact (mul_eq_zero.1 h4).resolve_left (hb j).ne'

theorem mem_balForms_of_descend {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E) {f : X →+ Y} (hf : Function.Surjective f)
    (hsm : ∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) {δ : LinearMap.BilinForm ℤ X} (hδ : δ ∈ balForms H.bar X)
    {ε : LinearMap.BilinForm ℤ Y} (hε : ∀ x y, ε (f x) (f y) = δ x y) : ε ∈ balForms H.bar Y := by
  refine ⟨fun y z => ?_, fun a y z => ?_⟩
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    rw [hε, hε, hδ.1]
  · obtain ⟨y, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hf z
    obtain ⟨a, rfl⟩ := τ.surjective a
    rw [← GlobalTheory.T.ringOfIntegers_aut_comm_hostConjugation E H τ a, ← hsm, ← hsm, hε, hε, hδ.2]

theorem exists_coord_pullAdd_of_pos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  intro E _ _ _ H φ htw X₀ _ _ _ m₀ δ₀ h₀ hind v t ht hvt X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc j hj
  classical
  have hval : ∀ x y, (β x y : ℝ) = ∑ l, c l * (δ l x y : ℝ) := fun x y => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hβc x y
  have hvan : ∀ l, 0 < c l → ∀ x, f x = 0 → ∀ y, δ l x y = 0 := by
    intro l hl x hx y
    have hb : β x x = 0 := by simpa using hβ x x 0 0 (by simp [hx]) (by simp [hx])
    have hk := hval x x
    rw [hb, Int.cast_zero] at hk
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hc i) (Int.cast_nonneg (hδ.nonneg i x))).1 hk.symm l (Finset.mem_univ _)
    have h0 : δ l x x = 0 := Int.cast_eq_zero.1 ((mul_eq_zero.1 hall).resolve_left hl.ne')
    exact ConeSub.eq_zero_of_self_eq_zero (δ l) (hδ.mem l).1 (hδ.nonneg l) h0 y
  set S : Finset (Fin m) := Finset.univ.filter fun l => 0 < c l with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hspos : ∀ i, 0 < c (s i) := fun i => by
    have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
    simpa [hS] using this
  have hdesc : ∀ i : Fin S.card, ∃ ε : LinearMap.BilinForm ℤ Y, ∀ x y, ε (f x) (f y) = δ (s i) x y := fun i =>
    GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf _ (hvan _ (hspos i)) fun x hx y => by rw [(hδ.mem _).1]; exact hvan _ (hspos i) x hx y
  choose ε hε using hdesc
  have hεm : ∀ i, ε i ∈ balForms H.bar Y := fun i => mem_balForms_of_descend H τ hf hsm (hδ.mem _) (hε i)
  have hεn : ∀ i y, 0 ≤ ε i y y := fun i y => by
    obtain ⟨y, rfl⟩ := hf y
    rw [hε]; exact hδ.nonneg _ _
  have hsemi := eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm
  have hεl : φ.LinearOn ε := by
    intro d hd
    have h1 := linearOn_comp hδ.linear s d hd
    have h2 : ∀ i, φ.evalZ (δ (s i)) = φ.evalZ (ε i) := fun i => by
      have := hsemi fun a b => (ε i a b : ℝ)
      simp only [hε] at this
      exact this
    have h3 := hsemi fun a b => ∑ i, d i * (ε i a b : ℝ)
    simp only [hε] at h3
    simp only [h2] at h1
    exact h3.symm.trans h1
  have hvb : toReal v = ∑ i, c (s i) • toReal (pull π (ε i)) := LinearMap.ext₂ fun x₀ y₀ => by
    obtain ⟨x, hx⟩ := hf (π x₀)
    obtain ⟨y, hy⟩ := hf (π y₀)
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply]
    rw [← hβ x y x₀ y₀ hx.symm hy.symm, hval, ← hx, ← hy]
    simp only [hε]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun l hl => ?_) fun i => rfl).symm
    have : ¬ 0 < c l := by rw [hs] at hl; simpa [hS] using hl
    rw [le_antisymm (not_lt.1 this) (hc l), zero_mul]
  obtain ⟨j, rfl⟩ : j ∈ Set.range s := by rw [hs]; simpa [hS] using hj
  obtain ⟨a, ha, ha0, he⟩ := exists_face_coord_of_linearOn h₀ hind (fun i => pull_mem π (hεm i)) (fun i y => hεn i _)
    ((linearOn_pull_iff hπ).2 hεl) ht hspos hvt hvb j
  refine ⟨a, ha, ha0, LinearMap.ext₂ fun x y => ?_⟩
  obtain ⟨x₀, hx⟩ := hπ (f x)
  obtain ⟨y₀, hy⟩ := hπ (f y)
  have h1 := LinearMap.congr_fun₂ he x₀ y₀
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pull_apply, pullAdd_apply] at h1 ⊢
  rw [hx, hy, hε] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).eq_or_lt with h | h
  · rw [ha0 i h.symm, zero_mul, zero_mul]
  · rw [← hu i h, pull_apply, hx, hy]

end GlobalTheory.PolFan.OrbMark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellRayInConeOfMarkedFormPiecesStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_ray_in_cone_of_marked_form_pieces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → LinearIndependent ℤ δ₀ →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y, (∀ i, 0 < t i → pull π (u i) = δ₀ i) →
  ∀ β : LinearMap.BilinForm ℤ X, (∀ (x y : X) (x₀ y₀ : X₀), π x₀ = f x → π y₀ = f y → β x y = v x₀ y₀) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
    toReal (δ j) = ∑ i, a i • toReal (pullAdd f (u i)) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos | exact GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos | (intros; apply GlobalTheory.PolFan.OrbMark.exists_coord_pullAdd_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionCone
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionCone
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGens

section General

variable {O : Type} [CommRing O] {bar : O → O} {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  [AddCommGroup Y] [Module O Y] [Module.Finite O Y]

theorem transport {φ χ : InvFun O} {b : ℕ} (e : X ≃ₗ[O] Y) {β : LinearMap.BilinForm ℤ Y}
    (h : ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧
      InRCone u (pull e.toLinearMap β)) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ Y), (∀ i, u i ∈ balForms bar Y) ∧ (∀ i y, 0 ≤ u i y y) ∧
      φ.LinearOn u ∧ χ.LinearOn u ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, χ.evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨n, u, h1, h2, h3, h4, h5, h6, c, hc, h7⟩ := h
  refine ⟨n, fun i => pull e.symm.toLinearMap (u i), fun i => pull_mem _ (h1 i), fun i y => h2 i _,
    (linearOn_pull_iff e.symm.surjective).2 h3, (linearOn_pull_iff e.symm.surjective).2 h4,
    fun i => by rw [evalZ_pull φ e.symm.surjective]; exact h5 i,
    fun i => by rw [evalZ_pull χ e.symm.surjective]; exact h6 i, c, hc, LinearMap.ext₂ fun x y => ?_⟩
  have := LinearMap.congr_fun₂ h7 (e.symm x) (e.symm y)
  simpa [LinearMap.sum_apply] using this

theorem linearOn_starDepth {ψ w : InvFun O} {n : ℕ} {u : Fin n → LinearMap.BilinForm ℤ X}
    (h : (starFun bar ψ w 0 1).LinearOn u) : (starDepth bar ψ w).LinearOn u := by
  rw [linearOn_iff] at h ⊢
  intro c hc
  simpa [starFun_evalR, starFun_evalZ] using h c hc


omit [Module O X] [Module.Finite O X] in
theorem mul_le_of_sub_mem_rcone {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hγ : ∀ i, 0 ≤ h (γ i)) {β v : LinearMap.BilinForm ℤ X} {t : ℝ} (hm : toReal β - t • toReal v ∈ rcone γ) :
    t * (h v : ℝ) ≤ h β := by
  obtain ⟨g, hg, hBg⟩ := hm
  have key := apply_eq_of_toReal_eq (β := β) (γ := Fin.cons v γ) (c := Fin.cons t g) (by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [← hBg]; abel) h
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at key
  have hpos : 0 ≤ ∑ i, g i * (h (γ i) : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hg i) (by exact_mod_cast hγ i)
  linarith

theorem exists_nat_bound {α : Type} {S : Set α} (hS : S.Finite) (f : α → ℝ) : ∃ b : ℕ, ∀ x ∈ S, f x ≤ b := by
  obtain ⟨r, hr⟩ := (hS.image f).bddAbove
  exact ⟨⌈r⌉₊, fun x hx => (hr ⟨x, hx, rfl⟩).trans (Nat.le_ceil r)⟩

end General

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {q : ℕ} {ψ w : InvFun (𝓞 E)}

theorem centres_finite (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q)
    {S : Set (LinearMap.BilinForm ℤ X)} (hS : S.Finite) :
    {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell H.bar ψ γ ∧ (∀ i, γ i ∈ S) ∧ InRCone γ v}.Finite := by
  refine (hS.finite_subsets.biUnion (t := fun T => {v | v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧ InRCone γ v})
    fun T _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩ v' ⟨b1, b2, b3, m', γ', -, b5, b6⟩
    refine (hw X hX).2.2 m γ a4 v a1 a2 v' b1 b2 a3 b3 a6 (inRCone_trans (fun j => ?_) b6)
    obtain ⟨i, hi⟩ : γ' j ∈ Set.range γ := by rw [a5, ← b5]; exact ⟨j, rfl⟩
    rw [← hi]; exact inRCone_self γ i
  · rintro v ⟨a1, a2, a3, m, γ, a4, a5, a6⟩
    exact Set.mem_biUnion (x := Set.range γ) (by rintro _ ⟨i, rfl⟩; exact a5 i) ⟨a1, a2, a3, m, γ, a4, rfl, a6⟩

theorem of_cell (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {b m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell H.bar ψ γ) (hb : ∀ i, ψ.evalZ (γ i) ≤ b)
    (hb' : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → ψ.evalZ v ≤ b)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨hC1, hC2, hC3⟩ := hw X hX
  obtain ⟨lin1, lin2⟩ := GlobalTheory.T.starSubdivision_function_linearOn_cells E H q ψ w 0 1 hw
  by_cases hc : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hv, hvp, hvw, hvin⟩ := hc
    have hne : v ≠ 0 := by
      rintro rfl
      have := hC2 0 hv hvp hvw 2 0 (by simp)
      norm_num at this
    obtain ⟨m', s, h, hcut, hh, hin⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i => (hγ.mem i).1)
      hγ.nonneg hne hvin hβ
    have hh' : (0 : ℝ) < h v := by exact_mod_cast hh
    have hmem : ∀ j, InRCone γ ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) := fun j =>
      Fin.cases (by simpa using hvin) (fun k => by simpa using inRCone_self γ (s k)) j
    have hle : ∀ j, (h ((Fin.cons v fun j => γ (s j) : Fin (m' + 1) → _) j) : ℝ) ≤ h v := fun j =>
      Fin.cases (by simp) (fun k => by
        simp only [Fin.cons_succ]; rw [(hcut.2 (s k)).2 ⟨k, rfl⟩]; simpa using hh.le) j
    refine ⟨m' + 1, Fin.cons v fun j => γ (s j), fun j => Fin.cases hv (fun k => hγ.mem (s k)) j,
      fun j => Fin.cases hvp (fun k => hγ.nonneg (s k)) j, linearOn_of_forall_inRCone ψ hγ.linear hmem,
      linearOn_starDepth (lin2 X hX m γ hγ v hv hvp hvw hvin m' s h hcut hh),
      fun j => Fin.cases (hb' v hv hvp hvw hvin) (fun k => hb (s k)) j, fun j => ?_, hin⟩
    rw [← evalR_toReal]
    refine evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (hmem j) zero_le_one fun v' a1 a2 a3 a4 t _ ht => ?_
    rw [hC3 m γ hγ v' a1 a2 v hv hvp a3 hvw a4 hvin] at ht
    have := (mul_le_of_sub_mem_rcone hcut.1 ht).trans (hle j)
    nlinarith
  · have hno : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0 := fun v a1 a2 a3 =>
      (hC1 v a1 a2).resolve_right fun a4 => hc ⟨v, a1, a2, a4, a3⟩
    refine ⟨m, γ, hγ.mem, hγ.nonneg, hγ.linear, linearOn_starDepth (lin1 X hX m γ hγ hno), hb, fun j => ?_, hβ⟩
    rw [← evalR_toReal]
    exact evalR_starDepth_le _ H.bar ψ w X m γ _ 1 hγ (inRCone_self γ j) zero_le_one fun v' a1 a2 a3 a4 _ _ _ =>
      (hc ⟨v', a1, a2, a3, a4⟩).elim

theorem per_module (hψ : IsPolyFan H.bar q ψ) (hw : IsCentreSet H.bar q ψ w) (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) :
    ∃ b : ℕ, ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) →
      ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧
      ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧
      (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨b, hb⟩ := exists_nat_bound (hS.union (centres_finite H hw X hX hS)) fun v => ψ.evalZ v
  refine ⟨b, fun β hβ hp => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ (toReal_mem_psdCone_of_nonneg E H X β hβ hp)
  refine transport e (of_cell H hw X hX hγ (fun i => hb _ (Or.inl (hγS i)))
    (fun v a1 a2 a3 a4 => hb _ (Or.inr ⟨a1, a2, a3, m, γ, hγ, hγS, a4⟩)) ⟨c, hc, ?_⟩)
  rw [← hsum]
  exact LinearMap.ext₂ fun x y => by simp

end CM

theorem exists_bounded_gens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  intro E _ _ _ H q ψ w hψ hw
  obtain ⟨n, R, hR, hiso⟩ := GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key := fun k => @per_module E _ _ _ H q ψ w hψ hw (R k) _ _ (hR k).1 (hR k).2.1 (hR k).2.2
  choose b hb using key
  refine ⟨Finset.univ.sup b, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hiso X hX
  haveI := (hR k).1
  obtain ⟨m, u, h1, h2, h3, h4, h5, h6, h7⟩ := hb k (pull f.symm.toLinearMap β) (pull_mem _ hβ) fun y => hp _
  have hk : (b k : ℝ) ≤ (Finset.univ.sup b : ℕ) := by exact_mod_cast Finset.le_sup (f := b) (Finset.mem_univ k)
  exact transport f.symm ⟨m, u, h1, h2, h3, h4, fun i => (h5 i).trans hk, h6, h7⟩

end GlobalTheory.PolFan.StarGens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedGeneratorsStarSubdivisionConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_generators_star_subdivision_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ b : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X), (∀ i, u i ∈ balForms H.bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ ψ.LinearOn u ∧ (starDepth H.bar ψ w).LinearOn u ∧ (∀ i, ψ.evalZ (u i) ≤ b) ∧ (∀ i, (starDepth H.bar ψ w).evalZ (u i) ≤ 1) ∧ InRCone u β := by
  first | exact @GlobalTheory.PolFan.StarGens.exists_bounded_gens | exact GlobalTheory.PolFan.StarGens.exists_bounded_gens | (intros; apply GlobalTheory.PolFan.StarGens.exists_bounded_gens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntForms
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

namespace ConeMatch

variable {V : Type} [AddCommGroup V] [Module ℝ V]

theorem coef_eq {n : ℕ} {P : Fin n → V} (hP : LinearIndependent ℝ P) {a b : Fin n → ℝ}
    (h : ∑ i, a i • P i = ∑ i, b i • P i) : a = b := by
  have := Fintype.linearIndependent_iff.1 hP (a - b) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext i; exact sub_eq_zero.1 (this i)

theorem exists_pos_of_sum_eq_one {n : ℕ} (f : Fin n → ℝ) (h : ∑ i, f i = 1) : ∃ i, 0 < f i := by
  by_contra hc
  push_neg at hc
  have : ∑ i, f i ≤ 0 := Finset.sum_nonpos fun i _ => hc i
  linarith

theorem match_vec {k m : ℕ} (P : Fin k → V) (Q : Fin m → V) (hP : LinearIndependent ℝ P)
    (hQ : LinearIndependent ℝ Q) (t : Fin k → ℝ) (c : Fin m → ℝ) (ht : ∀ i, 0 < t i) (hc : ∀ j, 0 ≤ c j)
    (hsum : ∑ i, t i • P i = ∑ j, c j • Q j)
    (hPQ : ∀ i, ∃ a : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ P i = ∑ j, a j • Q j)
    (hQP : ∀ j, 0 < c j → ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ Q j = ∑ l, b l • P l) :
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ P i = d • Q j) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ P i = d • Q j ∧ c j = t i * d) := by
  choose D hD0 hD using hPQ
  have hQP' : ∀ j, ∃ b : Fin k → ℝ, (∀ l, 0 ≤ b l) ∧ (0 < c j → Q j = ∑ l, b l • P l) := fun j => by
    by_cases h : 0 < c j
    · obtain ⟨b, hb, e⟩ := hQP j h
      exact ⟨b, hb, fun _ => e⟩
    · exact ⟨0, fun _ => le_rfl, fun h' => absurd h' h⟩
  choose E hE0 hE using hQP'

  have hcD : ∀ j, c j = ∑ i, t i * D i j := by
    have h1 : ∑ j, c j • Q j = ∑ j, (∑ i, t i * D i j) • Q j := by
      rw [← hsum]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact congrFun (coef_eq hQ h1)
  have hDz : ∀ i j, ¬ 0 < c j → D i j = 0 := fun i j h => by
    have h0 : c j = 0 := le_antisymm (not_lt.1 h) (hc j)
    rw [hcD j] at h0
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (ht i).le (hD0 i j)).1 h0 i
      (Finset.mem_univ _)
    exact (mul_eq_zero.1 this).resolve_left (ht i).ne'
  have hDQ : ∀ i j, D i j • Q j = D i j • ∑ l, E j l • P l := fun i j => by
    by_cases h : 0 < c j
    · rw [← hE j h]
    · simp [hDz i j h]
  have hDE : ∀ i l, ∑ j, D i j * E j l = if i = l then 1 else 0 := by
    intro i l
    have h1 : ∑ l, (if i = l then (1 : ℝ) else 0) • P l = ∑ l, (∑ j, D i j * E j l) • P l := by
      rw [show ∑ l, (if i = l then (1 : ℝ) else 0) • P l = P i by simp [ite_smul]]
      conv_lhs => rw [hD i]
      simp only [hDQ, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hP h1) l).symm
  have hED : ∀ j, 0 < c j → ∀ j', ∑ l, E j l * D l j' = if j = j' then 1 else 0 := by
    intro j hj j'
    have h1 : ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = ∑ j', (∑ l, E j l * D l j') • Q j' := by
      rw [show ∑ j', (if j = j' then (1 : ℝ) else 0) • Q j' = Q j by simp [ite_smul]]
      conv_lhs => rw [hE j hj]
      simp only [hD, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact (congrFun (coef_eq hQ h1) j').symm
  have single : ∀ i j, 0 < D i j * E j i → 0 < c j ∧ 0 < D i j ∧ P i = D i j • Q j := by
    intro i j hpos
    have hcj : 0 < c j := by
      by_contra h
      rw [hDz i j h, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hEne : E j i ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
    have hDpos : 0 < D i j := lt_of_le_of_ne (hD0 i j) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl _ hpos
    have hoff : ∀ j', j' ≠ j → D i j' = 0 := fun j' hj' => by
      have hle : E j i * D i j' ≤ ∑ l, E j l * D l j' :=
        Finset.single_le_sum (f := fun l => E j l * D l j') (fun l _ => mul_nonneg (hE0 j l) (hD0 l j'))
          (Finset.mem_univ i)
      rw [hED j hcj j', if_neg (Ne.symm hj')] at hle
      have h0 : E j i * D i j' = 0 := le_antisymm hle (mul_nonneg (hE0 j i) (hD0 i j'))
      exact (mul_eq_zero.1 h0).resolve_left hEne
    refine ⟨hcj, hDpos, ?_⟩
    rw [hD i, Finset.sum_eq_single j (fun j' _ hj' => by rw [hoff j' hj', zero_smul])
      (fun h => absurd (Finset.mem_univ j) h)]
  refine ⟨fun i => ?_, fun j hj => ?_⟩
  · obtain ⟨j, hj⟩ := exists_pos_of_sum_eq_one _ ((hDE i i).trans (if_pos rfl))
    obtain ⟨hcj, hd, e⟩ := single i j hj
    exact ⟨j, hcj, D i j, hd, e⟩
  · obtain ⟨l, hl⟩ := exists_pos_of_sum_eq_one _ ((hED j hj j).trans (if_pos rfl))
    have hl' : 0 < D l j * E j l := by rw [mul_comm]; exact hl
    obtain ⟨-, hd, e⟩ := single l j hl'
    have hEne : E j l ≠ 0 := fun h => by rw [h, zero_mul] at hl; exact lt_irrefl _ hl
    have hoff : ∀ i, i ≠ l → D i j = 0 := fun i hi => by
      have hle : D i j * E j l ≤ ∑ j'', D i j'' * E j'' l :=
        Finset.single_le_sum (f := fun j'' => D i j'' * E j'' l) (fun j'' _ => mul_nonneg (hD0 i j'') (hE0 j'' l))
          (Finset.mem_univ j)
      rw [hDE i l, if_neg hi] at hle
      have h0 : D i j * E j l = 0 := le_antisymm hle (mul_nonneg (hD0 i j) (hE0 j l))
      exact (mul_eq_zero.1 h0).resolve_right hEne
    refine ⟨l, D l j, hd, e, ?_⟩
    rw [hcD j, Finset.sum_eq_single l (fun i _ hi => by rw [hoff i hi, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h)]

end ConeMatch

section Forms

variable {X : Type} [AddCommGroup X]

theorem linearIndependent_toReal {n : ℕ} {p : Fin n → LinearMap.BilinForm ℤ X} (hp : LinearIndependent ℤ p) :
    LinearIndependent ℝ fun i => toReal (p i) := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin n → ℤ), ∑ j, c j • p j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c h => by
    funext i
    exact Fintype.linearIndependent_iff.1 hp c (by simpa using h) i
  have := eq_zero_of_toReal_rel (u := p) (v := (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X)) hind
    (r := g) (s := 0) (by simpa using hg)
  exact fun i => congrFun this i

theorem cone_match_rays {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X)
    (δ : Fin m → LinearMap.BilinForm ℤ X) :
    LinearIndependent ℤ p → LinearIndependent ℤ δ →
    ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) →
      ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
      (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
      (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
      (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) :=
  fun hp hδ t c ht hc hsum hpδ hδp =>
    ConeMatch.match_vec (fun i => toReal (p i)) (fun j => toReal (δ j)) (linearIndependent_toReal hp)
      (linearIndependent_toReal hδ) t c ht hc hsum hpδ hδp

end Forms

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysOfLinearIndependentIntFormsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms : ∀ {X : Type} [AddCommGroup X] {k m : ℕ} (p : Fin k → LinearMap.BilinForm ℤ X) (δ : Fin m → LinearMap.BilinForm ℤ X),
  LinearIndependent ℤ p → LinearIndependent ℤ δ →
  ∀ (t : Fin k → ℝ) (c : Fin m → ℝ), (∀ i, 0 < t i) → (∀ j, 0 ≤ c j) → ∑ i, t i • toReal (p i) = ∑ j, c j • toReal (δ j) →
    (∀ i, InRCone δ (p i)) → (∀ j, 0 < c j → InRCone p (δ j)) →
    (∀ i, ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays | exact GlobalTheory.PolFan.cone_match_rays | (intros; apply GlobalTheory.PolFan.cone_match_rays <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoords
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan

theorem cone_match_rays_of_nonneg {X : Type} [AddCommGroup X] {m₀ : ℕ}
    (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hp : LinearIndependent ℤ (fun i : {i // 0 < t i} => p i))
    (β : LinearMap.BilinForm ℤ X) (hβ : toReal β = ∑ i, t i • toReal (p i))
    (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (hδ : LinearIndependent ℤ δ)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hβ' : toReal β = ∑ j, c j • toReal (δ j))
    (h1 : ∀ i, 0 < t i → InRCone δ (p i))
    (h2 : ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
      toReal (δ j) = ∑ i, a i • toReal (p i)) :
    (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧
      c j = t i * d) := by
  classical
  set e := (Fintype.equivFin {i // 0 < t i}).symm with he
  have key : ∀ a : Fin m₀ → ℝ, (∀ i, t i = 0 → a i = 0) →
      ∑ i', a (e i') • toReal (p (e i')) = ∑ i, a i • toReal (p i) := by
    intro a ha
    refine Fintype.sum_of_injective (fun i' => ((e i' : {i // 0 < t i}) : Fin m₀))
      (Subtype.val_injective.comp e.injective) _ _ ?_ (fun _ => rfl)
    intro i hi
    have : t i = 0 := by
      by_contra h0
      exact hi ⟨e.symm ⟨i, lt_of_le_of_ne (ht i) (Ne.symm h0)⟩, by simp⟩
    rw [ha i this, zero_smul]
  obtain ⟨r1, r2⟩ := GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms (fun i' => p (e i')) δ (hp.comp e e.injective) hδ
    (fun i' => t (e i')) c (fun i' => (e i').2) hc
    (by rw [key t (fun _ h => h), ← hβ, hβ'])
    (fun i' => h1 _ (e i').2)
    (fun j hj => by
      obtain ⟨a, ha0, ha1, ha2⟩ := h2 j hj
      exact ⟨fun i' => a (e i'), fun i' => ha0 _, by rw [ha2, ← key a ha1]⟩)
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simpa using r1 (e.symm ⟨i, hi⟩)
  · obtain ⟨i', h⟩ := r2 j hj
    exact ⟨e i', (e i').2, h⟩

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoordsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_match_rays_after_dropping_zero_coords : ∀ {X : Type} [AddCommGroup X] {m₀ : ℕ} (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) →
  LinearIndependent ℤ (fun i : {i // 0 < t i} => p i) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), LinearIndependent ℤ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  (∀ i, 0 < t i → InRCone δ (p i)) →
  (∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (δ j) = ∑ i, a i • toReal (p i)) →
  (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays_of_nonneg | exact GlobalTheory.PolFan.cone_match_rays_of_nonneg | (intros; apply GlobalTheory.PolFan.cone_match_rays_of_nonneg <;> assumption)
end
end
