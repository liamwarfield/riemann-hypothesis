module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFrameSliceComponentUniformisati
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardTorsionQuotSpanDvdOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntForm
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosRatMultipleOfPosRealMultipleIntFormStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d → y ≠ 0 → toReal x = d • toReal y →
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  first | exact @GlobalTheory.posReal_multiple_rat | exact GlobalTheory.posReal_multiple_rat | (intros; apply GlobalTheory.posReal_multiple_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFan
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

theorem exists_cell {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)} {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hfan : IsPolyFanOn H.bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.PolFan.CarDim

theorem GlobalTheory.PolFan.CarDim.exists_isCarrierDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  intro E _ _ _ H q ψ hD hψ htw
  refine ⟨carFun H.bar ψ, GlobalTheory.T.carrierDimInvFun_hostFixingAut_invariant E H ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := GlobalTheory.T.polyhedralPolarisation_face_cut_isCell E H ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone E H ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet H.bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet H.bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone E H ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_cell_radical_pullback E H ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_carrierDim_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  first | exact @GlobalTheory.PolFan.CarDim.exists_isCarrierDim | exact GlobalTheory.PolFan.CarDim.exists_isCarrierDim | (intros; apply GlobalTheory.PolFan.CarDim.exists_isCarrierDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

noncomputable section

namespace GlobalTheory.PolFan.Mark

theorem inRCone_of_evalZ_sum_le (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : IsCell bar ψ γ) (k : ℕ)
    (u : Fin k → LinearMap.BilinForm ℤ X) (hu : ∀ j, u j ∈ balForms bar X) (hp : ∀ j y, 0 ≤ u j y y)
    (hs : InRCone γ (∑ j, u j)) (hle : ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j)) : ∀ j, InRCone γ (u j) := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨c, hc, e⟩ := hs
  have hsum : ψ.evalZ (∑ j, u j) = ∑ i, c i * ψ.evalZ (γ i) := by
    rw [← hγ.linear c hc]
    unfold InvFun.evalZ
    congr 1
    funext a b
    have := LinearMap.congr_fun₂ e a b
    simpa [LinearMap.sum_apply] using this
  have hℓ : (ℓ (∑ j, u j) : ℝ) = N * ψ.evalZ (∑ j, u j) := by
    rw [apply_eq_of_toReal_eq e ℓ, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  have hd : ∀ j, 0 ≤ (ℓ (u j) : ℝ) - N * ψ.evalZ (u j) := fun j => sub_nonneg.2 (h2 _ (hu j) (hp j))
  have hz : ∑ j, ((ℓ (u j) : ℝ) - N * ψ.evalZ (u j)) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hd j)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e1 : (∑ j, (ℓ (u j) : ℝ)) = ℓ (∑ j, u j) := by rw [map_sum]; push_cast; rfl
    rw [e1, hℓ]
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left hle h0]
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hd j).1 hz j (Finset.mem_univ _)
  obtain ⟨n, c', hn, hc'⟩ := h3 _ (hu j) (hp j) (by linarith)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => (c' i : ℝ) / n, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc' a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h4
  have h5 : (n : ℝ) * u j a b = ∑ i, (c' i : ℝ) * γ i a b := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show ∑ i, (c' i : ℝ) / n * (γ i a b : ℝ) = (∑ i, (c' i : ℝ) * γ i a b) / n by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring, ← h5]
  field_simp

end GlobalTheory.PolFan.Mark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSummandsOfEvalZAdditiveCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_summands_of_evalZ_additive_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ (k : ℕ) (u : Fin k → LinearMap.BilinForm ℤ X), (∀ j, u j ∈ balForms bar X) → (∀ j y, 0 ≤ u j y y) → InRCone γ (∑ j, u j) → ψ.evalZ (∑ j, u j) ≤ ∑ j, ψ.evalZ (u j) → ∀ j, InRCone γ (u j) := by
  first | exact @GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | exact GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le | (intros; apply GlobalTheory.PolFan.Mark.inRCone_of_evalZ_sum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGap

theorem gap_eq_sum {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hlin : φ.LinearOn γ) {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsum : toReal β = ∑ i, c i • toReal (γ i)) :
    (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (γ i) : ℝ) - N * φ.evalZ (γ i)) := by
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem starDepth_le_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro E _ _ _ H q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ H.bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.PolFan.StarGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentresStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starDepth_le_strictnessGap_off_centres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  first | exact @GlobalTheory.PolFan.StarGap.starDepth_le_gap | exact GlobalTheory.PolFan.StarGap.starDepth_le_gap | (intros; apply GlobalTheory.PolFan.StarGap.starDepth_le_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_range_subset {X : Type} [AddCommGroup X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hsub : Set.range γ ⊆ Set.range γ') {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) : InRCone γ' β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  have hj : ∀ i, ∃ j, γ' j = γ i := fun i => hsub ⟨i, rfl⟩
  choose j hj using hj
  refine ⟨fun k => ∑ i, if j i = k then c i else 0, fun k => Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hc i
    · exact le_refl 0, ?_⟩
  rw [hβ]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (j i) (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_smul]) (by simp), if_pos rfl, hj]

theorem evalZ_zero_form {O : Type} [CommRing O] (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  rw [← evalR_toReal]
  have : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp
  rw [this, evalR_zero]

theorem isStarOf_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X),
      ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨hw1, -, hw3⟩ := hw X hX

  let C : Set (LinearMap.BilinForm ℤ X) := {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
    (∀ i, γ i ∈ S) ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  let CT : Set (LinearMap.BilinForm ℤ X) → Set (LinearMap.BilinForm ℤ X) := fun T =>
    {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧
      v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  have hCT : ∀ T, (CT T).Subsingleton := by
    rintro T v₁ ⟨m₁, γ₁, hγ₁, hr₁, hb₁, hp₁, hv₁, hi₁⟩ v₂ ⟨m₂, γ₂, hγ₂, hr₂, hb₂, hp₂, hv₂, hi₂⟩
    exact hw3 m₁ γ₁ hγ₁ v₁ hb₁ hp₁ v₂ hb₂ hp₂ hv₁ hv₂ hi₁
      (inRCone_of_range_subset (by rw [hr₁, hr₂]) hi₂)
  have hC : C.Finite := by
    refine (hS.powerset.biUnion fun T _ => (hCT T).finite).subset ?_
    rintro v ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    refine Set.mem_biUnion (x := Set.range γ) ?_ ⟨m, γ, hγ, rfl, hb, hp, hv, hi⟩
    rintro _ ⟨i, rfl⟩
    exact hγS i
  refine ⟨S ∪ C, hS.union hC, fun B hB => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hBc⟩ := hcov B hB
  by_cases hex : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hb, hp, hv, hi⟩ := hex
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [evalZ_zero_form] at hv
      exact zero_ne_one hv
    obtain ⟨m', s, h, hcut, hpos, t, ht, hBt⟩ :=
      GlobalTheory.T.realCone_covered_by_star_at_point X m γ v (pullR e.toLinearMap B) (fun i y z => (hγ.mem i).1 y z) hγ.nonneg hv0 hi ⟨c, hc, hBc⟩
    refine ⟨e, m' + 1, Fin.cons v fun j => γ (s j), t,
      hst.2.1 X hX m γ hγ v hb hp hv hi m' s h hcut hpos, fun i => ?_, ht, hBt⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    · simp only [Fin.cons_succ]
      exact Or.inl (hγS (s j))
  · refine ⟨e, m, γ, c, hst.1 X hX m γ hγ fun β hb hp hi => ?_, fun i => Or.inl (hγS i), hc, hBc⟩
    rcases hw1 β hb hp with h0 | h1
    · exact h0
    · exact (hex ⟨β, hb, hp, h1, hi⟩).elim

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolFan.isStarOf_finite_cover | exact GlobalTheory.PolFan.isStarOf_finite_cover | (intros; apply GlobalTheory.PolFan.isStarOf_finite_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStarOfOfCover
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem inCone_of_strict {m' n : ℕ} {σ : Fin m' → LinearMap.BilinForm ℤ X} (hσs : IsStrict bar φ σ)
    (hσl : φ.LinearOn σ) {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (σ j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • σ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hσs
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (σ j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β σ) (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (σ j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ σ).1 hσl b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem inRCone_of_nsmul {m : ℕ} {σ : Fin m → LinearMap.BilinForm ℤ X} {β : LinearMap.BilinForm ℤ X} {k : ℕ}
    {d : Fin m → ℕ} (hk : 0 < k) (h : k • β = ∑ j, d j • σ j) : InRCone σ β := by
  refine ⟨fun j => (d j : ℝ) / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have e := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at e
  have e' : (k : ℝ) * (β a b : ℝ) = ∑ j, (d j : ℝ) * (σ j a b : ℝ) := by exact_mod_cast e
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ j, (d j : ℝ) * (σ j a b : ℝ)) / k by rw [← e']; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolFan.StarCells

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_cover (hcover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j))) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w ψ' hψ hw h1 h2
  refine ⟨h1, h2, ?_⟩
  intro X _ _ _ _ hX n γ' hγ'
  set B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ := ∑ j, (1 : ℝ) • toReal (γ' j) with hBdef
  have hB : B ∈ psdCone (bar := H.bar) (X := X) :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X n γ' _ hγ'.mem hγ'.nonneg fun _ => zero_le_one
  obtain ⟨S, -, hfin⟩ := (hψ X hX).finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hfin B hB
  set δ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hγ e.symm
  have hBδ : B = ∑ i, c i • toReal (δ i) := by
    refine LinearMap.ext₂ fun a b => ?_
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, toReal_apply, smul_eq_mul] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hδdef, pull_apply,
      LinearEquiv.coe_coe]
    exact this
  have key : ∀ (k : ℕ) (σ : Fin k → LinearMap.BilinForm ℤ X), IsCell H.bar ψ' σ → B ∈ rcone σ →
      ∀ j, InRCone σ (γ' j) := by
    rintro k σ hσ ⟨t, ht, hBt⟩ j
    obtain ⟨kk, d, hk, hkd⟩ := inCone_of_strict hσ.strict hσ.linear hγ'.mem hγ'.nonneg (a := fun _ => 1) (b := t)
      (fun _ => zero_le_one) ht ((linearOn_iff ψ' γ').1 hγ'.linear _ fun _ => zero_le_one) hBt j one_ne_zero
    exact inRCone_of_nsmul hk hkd
  by_cases hc0 : ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ InRCone δ β ∧ w.evalZ β = 1
  · obtain ⟨β₀, hβ₀, hβ₀p, hin, hw1⟩ := hc0
    have hne : β₀ ≠ 0 := by
      intro h0
      have := (hw X hX).2.1 β₀ hβ₀ hβ₀p hw1 2 0 (by simp [h0])
      omega
    obtain ⟨m', s, h, hfc, hpos, hBc⟩ :=
      hcover X m δ β₀ B (fun i => (hδ.mem i).1) hδ.nonneg hne hin ⟨c, hc, hBδ⟩
    exact Or.inr ⟨m, δ, β₀, m', s, h, hδ, hβ₀, hβ₀p, hw1, hin, hfc, hpos,
      key _ _ (h2 X hX m δ hδ β₀ hβ₀ hβ₀p hw1 hin m' s h hfc hpos) hBc⟩
  · push_neg at hc0
    have h0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone δ β → w.evalZ β = 0 := fun β hβ hp hi =>
      ((hw X hX).1 β hβ hp).resolve_right (hc0 β hβ hp hi)
    exact Or.inl ⟨m, δ, hδ, h0, key _ _ (h1 X hX m δ hδ h0) ⟨c, hc, hBδ⟩⟩

end GlobalTheory.PolFan.StarCells
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarCells

theorem isStarOf_of_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' :=
  isStarOf_of_cover GlobalTheory.T.realCone_covered_by_star_at_point

end GlobalTheory.PolFan.StarCells
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentrelessStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStarOf_of_cells_starCone_or_centreless : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | exact GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | (intros; apply GlobalTheory.PolFan.StarCells.isStarOf_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {T : X ≃ X} {e : LinearMap.BilinForm ℤ X ≃+ LinearMap.BilinForm ℤ X}
  (he : ∀ β y z, e β y z = β (T y) (T z))
  (hbal : ∀ β, e β ∈ balForms bar X ↔ β ∈ balForms bar X)
  (hψ : ∀ β, ψ.evalZ (e β) = ψ.evalZ β) (hlab : ∀ β, lab.evalZ (e β) = lab.evalZ β)
include he hbal hψ hlab

theorem inFace_transport (β x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab (e β) (e x) ↔ InFace bar ψ lab β x := by
  unfold InFace
  simp only [he]
  rw [hbal, ← map_add (f := _), hψ, hψ, hψ, hlab, hlab]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩

theorem isIndec_transport (β x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab (e β) (e x) ↔ IsIndec bar ψ lab β x := by
  unfold IsIndec
  rw [inFace_transport he hbal hψ hlab, e.map_ne_zero_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y z hy hz hy0 hz0 hs => ?_, fun h y z hy hz hy0 hz0 hs => ?_⟩)
  · refine h (e y) (e z) ((inFace_transport he hbal hψ hlab β y).2 hy) ((inFace_transport he hbal hψ hlab β z).2 hz)
      (e.map_ne_zero_iff.2 hy0) (e.map_ne_zero_iff.2 hz0) ?_
    rw [← map_add (f := _), hs]
  · refine h (e.symm y) (e.symm z) ?_ ?_ ?_ ?_ ?_
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hy
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hz
    · exact fun h0 => hy0 (by rw [← e.apply_symm_apply y, h0, map_zero])
    · exact fun h0 => hz0 (by rw [← e.apply_symm_apply z, h0, map_zero])
    · apply e.injective; rw [map_add (f := _), e.apply_symm_apply, e.apply_symm_apply, hs]

theorem isMarked_transport_of (β : LinearMap.BilinForm ℤ X) (h : IsMarked bar ψ lab i X β) :
    IsMarked bar ψ lab i X (e β) := by
  obtain ⟨hb, hn, hp, hl, S, hS, k, hk, hsum⟩ := h
  refine ⟨(hbal β).2 hb, fun y => by rw [he]; exact hn _, fun k' β' h' => hp k' (e.symm β') ?_, by rw [hlab]; exact hl,
    S.map e.toEquiv.toEmbedding, fun x => ?_, k, hk, ?_⟩
  · apply e.injective; rw [map_zsmul, e.apply_symm_apply, h']
  · rw [Finset.mem_map_equiv, hS, ← isIndec_transport he hbal hψ hlab]
    show IsIndec bar ψ lab (e β) (e (e.symm x)) ↔ _
    rw [e.apply_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_map, ← map_zsmul, hsum, map_sum]; rfl

theorem isMarked_transport (β : LinearMap.BilinForm ℤ X) :
    IsMarked bar ψ lab i X (e β) ↔ IsMarked bar ψ lab i X β := by
  refine ⟨fun h => ?_, isMarked_transport_of he hbal hψ hlab β⟩
  have := isMarked_transport_of (T := T.symm) (e := e.symm) (fun β y z => ?_) (fun β => ?_) (fun β => ?_)
    (fun β => ?_) (e β) h
  · simpa using this
  · have := he (e.symm β) (T.symm y) (T.symm z); simp only [AddEquiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [← hbal, e.apply_symm_apply]
  · rw [← hψ, e.apply_symm_apply]
  · rw [← hlab, e.apply_symm_apply]

end Transport

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def twPi (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → 𝓞 E) ≃+ LinearMap.BilinForm ℤ (Fin n → 𝓞 E) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) (a b : Fin n → 𝓞 E) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

end Twist

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twForm_mem_balForms (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} {β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)}
    (h : β ∈ balForms H.bar (Fin n → 𝓞 E)) : twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((H.bar a • z) j)) = H.bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [host_bar_map_comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) ↔ β ∈ balForms H.bar (Fin n → 𝓞 E) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms H σ.symm h, twForm_mem_balForms H σ⟩

theorem evalZ_twForm {H : Host E} {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E))
    (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 →
    ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
      markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  intro E _ _ _ H ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff H σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end Main

end GlobalTheory.PolFan.Mark
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAutStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFormIndicatorValue_invariant_hostFixingAut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E)) (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ), markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  first | exact @GlobalTheory.PolFan.Mark.markVal_twist | exact GlobalTheory.PolFan.Mark.markVal_twist | (intros; apply GlobalTheory.PolFan.Mark.markVal_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.LvT.Built.KMap


set_option maxHeartbeats 1000000 in
theorem jetC_th_mem_Qbar : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  classical
  intro B X I hOk hPins l Z Qp O hO hJ u μ i hi c c' m hm
  rw [hO.dgen, hO.Th]
  have hdeg : ∀ τ, (monoDeg m τ : ℤ) = nuDeg B u i τ := by
    intro τ
    rw [monoDeg_eq_sum, hm τ, Nat.cast_sum]
    unfold nuDeg
    refine Finset.sum_congr rfl fun r _ => ?_
    have e1 : ((nuT (I.rec7 l Z) u i τ r : ℕ) : ℝ) = DV.nuRow (I.rec7 l Z) u (i + 1) τ r := (nu_t_identity (I.rec7 l Z) u i hi τ r).1
    have e2 := GlobalTheory.ColPeriod.nuRow_succ_eq_wt (I.rec7 l Z) u i hi τ r r.2
    have e3 := B.wts.nuW_eq u hi τ r
    have e4 := lamOf_wtN (B.wts.hc u τ) hi.le r
    have key : (((nuT (I.rec7 l Z) u i τ r : ℕ) : ℤ) : ℝ) = (((B.wts.nuW u (i + 1) τ).w r : ℤ) : ℝ) := by
      rw [Int.cast_natCast, e1, e2, ← Rat.cast_intCast, e3]
      unfold Wts.lamN at e3 ⊢
      rw [e4]
      rfl
    exact_mod_cast key
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨hLa, hE⟩ := GlobalTheory.T.trueColumn_periodLattice_vacuumSmooth I hOk hPins l Z μ u i hi
  set p := (I.stp u μ i).rep c
  set p' := (I.stp u μ (i + 1)).rep c'
  have hN : IsSdLat p.1.1.deco.1.N := ⟨p.1.1.deco.2.lat, p.1.1.deco.2.uni⟩
  have hN' : IsSdLat p'.1.1.deco.1.N := ⟨p'.1.1.deco.2.lat, p'.1.1.deco.2.uni⟩
  have hA : 0 < cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) :=
    pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _
  have hB : 0 < cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u := GlobalTheory.MoveCompare.cBof_pos hPr _ _ _ u
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup μ) (I.cst μ) (I.idx μ) _ _ u i hX hPr
    hOk.sel_ok (hOk.T_mem u) hOk.g_mem (hOk.idx_ok μ) hi ⟨_, _, _, _, hOk.ch_tied⟩ c.1 c'.1 p p'
  set N := p.1.1.deco.1.N
  set N' := p'.1.1.deco.1.N
  have span_of_self_dual {n : ℕ} {L : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hLat : IsSdLat L) :
      Submodule.span B.fields.E (L : Set (Sp B.fields.E n)) = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v : Sp B.fields.E n := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E n v = f := by
      apply (Pi.basisFun B.fields.E (Fin n)).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ L := by
      rw [← show Formalism.HermitianLatticesTheory.dual (hStd B.fields.E n) L = L from hLat.2, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E n v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E n y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E) (n := n)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      -- A nonzero coordinate would make the field finite over its ring of integers.
      let coord := (LinearMap.proj i : Sp B.fields.E n →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : L.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ hLat.1.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hNfull : Submodule.IsFullLattice B.fields.E N :=
    { toIsLattice := hN.1, span_eq_top := span_of_self_dual hN }
  set cA := cAof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ)
  set cB := cBof (Pr := B.primes X) I.sel (I.tup μ) (I.cst μ) u
  set Ξ := xiAt (Pr := B.primes X) I.Ch I.sel (I.tup μ) (I.cst μ) (I.idx μ) u i c.1 c'.1 p p'
  have hth := GlobalTheory.latSum_thInd_eq_thC B.fields I.A _ _ (I.Sb μ u) N N' cA cB (fun x => I.A.σ₀ (Ξ x))
    (indTieD_of_la I.A _ _ _ _ (Nat.mul_pos hA hB) hLa) hN hN' hA hB (volC_pos_of_laHyp I.A _ _ _ hLa hN hN')
    (GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ _ _ _ _ _ hNfull hN'.1 hA hB) (fun x hx => hbox.1 x ((map_ne_zero _).1 hx))
    (fun x y hy => congrArg I.A.σ₀ (hbox.2 x y hy))
  have hfin := GlobalTheory.finite_divLat_quot_mulLat_homAt _ _ _ (I.Sb μ u) N N' cA cB hNfull hN'.1 hA hB
  let _ := @Fintype.ofFinite _ hfin
  rw [show I.th u μ i c.1 c'.1 p p' = fun z => _ from funext fun z => (hth z).symm]
  unfold latSum
  simp only [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((Formalism.L2.Col.mulLat cB (homAt (I.Sb μ u) N N')).comap (divLat cA (homAt (I.Sb μ u) N N')).subtype))
  have hs : ∀ q (k : ℕ), ContDiff ℂ k (I.A.thInd (I.Sb μ u) N N' cB (r q)) := fun q =>
    indSmooth_of I.A _ _ (I.Sb μ u) (cA * cB) hE N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩
  rw [show I.J.cD = I.A.cD from rfl]
  have hsum := jetC_sum I.A.cD (fun q => I.A.σ₀ (Ξ (r q))) (fun q => I.A.thInd (I.Sb μ u) N N' cB (r q)) hs m
  have hchi : ∀ 𝔞, I.chi 𝔞 ≠ 0 := fun 𝔞 => by
    unfold ColIn.chi chiId
    exact Units.ne_zero _
  have hF0 : I.A.chiF _ _ N N' ≠ 0 := by
    show Th.chiFac B.host I.chi _ _ N N' ≠ 0
    unfold Th.chiFac
    exact mul_ne_zero (zpow_ne_zero _ (hchi _)) (zpow_ne_zero _ (hchi _))
  have hF : I.A.chiF _ _ N N' ∈ B.embLL.fieldRange := by
    show Th.chiFac B.host I.chi _ _ N N' ∈ B.embLL.fieldRange
    unfold Th.chiFac
    have hv := (GlobalTheory.Mem.ChiVal.chi_values B X I hOk).2
    exact mul_mem (zpow_mem (hv _) _) (zpow_mem (hv _) _)
  have hmem : (∑ q, I.A.σ₀ (Ξ (r q)) * jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m) ∈ B.embLL.fieldRange := by
    refine Subfield.sum_mem _ fun q _ => Subfield.mul_mem _ (RingHom.mem_fieldRange_self _ _) ?_
    obtain ⟨y, hy⟩ := hJ.exists_eq (a := μ) (u := u) (N := N) (N' := N') (c := cB) (x := (r q).1) (e := m) hi
      ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (r q).2⟩ hdeg
    rw [← mul_inv_cancel_left₀ hF0 (jetC I.A.cD (I.A.thInd (I.Sb μ u) N N' cB (r q)) m)]
    exact Subfield.mul_mem _ hF ⟨y, hy⟩
  have hQ : ∀ x ∈ B.embLL.fieldRange, x ∈ Qbar := by
    rintro _ ⟨y, rfl⟩
    exact mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) y).algHom B.embLL.toRatAlgHom)
  show jetC I.A.cD (fun z => ∑ q, I.A.σ₀ (Ξ (r q)) * I.A.thInd (I.Sb μ u) N N' cB (r q) z) m ∈ Qbar
  rw [hsum]
  exact hQ _ hmem

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueKernelJetsLiftDegreesAlgebraicStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueKernelJets_liftDegrees_algebraic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Qp : I.ι → Finset ℕ)
    (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)), I.StdO l Z Qp O → ColIn.JetsIn I →
    ∀ u μ i, i < B.R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1))
      (m : DVar (I.rec7 l Z).what₂.Tau ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) →₀ ℕ),
      (∀ τ, ∑ β, ∑ α, m (τ, β, α) = ∑ r, nuT (I.rec7 l Z) u i τ r) → jetC (O u μ).dgen ((O u μ).Th i c c') m ∈ Qbar := by
  first | exact @GlobalTheory.Mem.Col2.TC.jetC_th_mem_Qbar | exact GlobalTheory.Mem.Col2.TC.jetC_th_mem_Qbar | (intros; apply GlobalTheory.Mem.Col2.TC.jetC_th_mem_Qbar <;> assumption)
end
end
