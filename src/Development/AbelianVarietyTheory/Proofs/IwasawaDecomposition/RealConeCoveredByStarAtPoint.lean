module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPoint
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.StarCover

theorem exists_points {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) :
    ∃ (n : ℕ) (p : Fin n → X × X), ∀ r : Fin m → ℝ,
      (∀ k, ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) = 0) → ∀ x y, ∑ j, r j * (γ j x y : ℝ) = 0 := by
  classical
  let S : X × X → (Fin m → ℚ) := fun q j => (γ j q.1 q.2 : ℚ)
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range S)
  obtain ⟨n, f, hf⟩ := (hli.setFinite).fin_embedding
  have hfb : ∀ k, f k ∈ b := fun k => hf ▸ Set.mem_range_self k
  have hpre : ∀ k, ∃ q, S q = f k := fun k => hbS (hfb k)
  let p : Fin n → X × X := fun k => (hpre k).choose
  have hp : ∀ k, S (p k) = f k := fun k => (hpre k).choose_spec
  refine ⟨n, p, fun r hr x y => ?_⟩
  have hmem : S (x, y) ∈ Submodule.span ℚ (Set.range f) := by
    rw [hf, hspan]; exact Submodule.subset_span ⟨(x, y), rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
  have hj : ∀ j, (γ j x y : ℝ) = ∑ k, (c k : ℝ) * (γ j (p k).1 (p k).2 : ℝ) := fun j => by
    have := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hp, S] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h2
    exact h2.symm
  calc ∑ j, r j * (γ j x y : ℝ) = ∑ k, (c k : ℝ) * ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) := by
        simp only [hj, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [hr]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem dotR_comb {n m : ℕ} (a : Fin n → ℚ) (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) :
    dotR a (∑ j, r j • castR (u j)) = ∑ j, r j * ((a ⬝ᵥ u j : ℚ) : ℝ) := by
  simp only [dotR, castR, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    Rat.cast_sum, Rat.cast_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (r : Fin m → ℝ) (hr : ∀ j, 0 ≤ r j) :
    ∑ j, r j • castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => ∑ j ∈ Finset.univ.filter (fun j => u j = y), r j,
    fun y _ => Finset.sum_nonneg fun j _ => hr j, ?_⟩
  symm
  refine Finset.sum_image' _ fun j _ => ?_
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

theorem exists_of_mem_rcone_image {n m : ℕ} (u : Fin m → Fin n → ℚ) (x : Fin n → ℝ)
    (hx : x ∈ rcone (Finset.univ.image u)) :
    ∃ r : Fin m → ℝ, (∀ j, 0 ≤ r j) ∧ x = ∑ j, r j • castR (u j) := by
  classical
  obtain ⟨c, hc, rfl⟩ := hx
  let k : Fin m → ℝ := fun j => ((Finset.univ.filter (fun i => u i = u j)).card : ℝ)
  have hk : ∀ j, 0 < k j := fun j => by
    simp only [k, Nat.cast_pos, Finset.card_pos]
    exact ⟨j, by simp⟩
  refine ⟨fun j => c (u j) / k j, fun j => div_nonneg (hc _ (by simp)) (hk j).le, ?_⟩
  refine Finset.sum_image' _ fun j _ => ?_
  have : ∀ i ∈ Finset.univ.filter (fun i => u i = u j), (c (u i) / k i) • castR (u i) = (c (u j) / k j) • castR (u j) :=
    fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      have hki : k i = k j := by simp only [k, hi']
      rw [hi', hki]
  rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  change c (u j) = k j * (c (u j) / k j)
  field_simp [(hk j).ne']

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem toReal_apply' {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x y : X) :
    toReal β x y = (β x y : ℝ) := by simp [toReal]

theorem comb_apply {X : Type} [AddCommGroup X] {m : ℕ} (r : Fin m → ℝ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (x y : X) : (∑ j, r j • toReal (γ j)) x y = ∑ j, r j * (γ j x y : ℝ) := by
  simp [LinearMap.sum_apply, toReal_apply']

theorem castR_mem_rcone {n m : ℕ} (u : Fin m → Fin n → ℚ) (j : Fin m) :
    castR (u j) ∈ rcone (Finset.univ.image u) := by
  classical
  refine ⟨fun y => if y = u j then 1 else 0, fun y _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp [ite_smul]

end GlobalTheory.StarCover

namespace GlobalTheory.StarCover
open GlobalTheory.MinkWeylReal

theorem star_cover : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) →
    v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  classical
  intro X _ m γ v B hsym hpsd hv0 ⟨c, hc, hvc⟩ ⟨t, ht, hBt⟩
  obtain ⟨n, p, hp⟩ := exists_points γ
  set u : Fin m → Fin n → ℚ := fun j k => (γ j (p k).1 (p k).2 : ℚ) with hu
  set T := Finset.univ.image u with hT
  obtain ⟨A, hA⟩ := minkR T
  have hcomb : ∀ r : Fin m → ℝ, (∑ j, r j • castR (u j)) = fun k => ∑ j, r j * (γ j (p k).1 (p k).2 : ℝ) :=
    fun r => by funext k; simp [castR, u, Finset.sum_apply]
  have hv_app : ∀ x y, (v x y : ℝ) = ∑ j, c j * (γ j x y : ℝ) := fun x y => by
    rw [← toReal_apply', hvc, comb_apply]
  have hB_app : ∀ x y, B x y = ∑ j, t j * (γ j x y : ℝ) := fun x y => by rw [hBt, comb_apply]
  set Ev : Fin n → ℝ := ∑ j, c j • castR (u j) with hEv
  set EB : Fin n → ℝ := ∑ j, t j • castR (u j) with hEB
  have hEvT : Ev ∈ rcone T := mem_rcone_image u c hc
  have hEBT : EB ∈ rcone T := mem_rcone_image u t ht
  have hAv : ∀ a ∈ A, 0 ≤ dotR a Ev := (hA Ev).mp hEvT
  have hAB : ∀ a ∈ A, 0 ≤ dotR a EB := (hA EB).mp hEBT
  have hAu : ∀ a ∈ A, ∀ j, 0 ≤ a ⬝ᵥ u j := fun a ha j => by
    have := (hA _).mp (castR_mem_rcone u j) a ha
    rw [dotR_castR] at this
    exact_mod_cast this

  have hne : (A.filter fun a => 0 < dotR a Ev).Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hno
    have hneg : (-1 : ℝ) • Ev ∈ rcone T := (hA _).mpr fun a ha => by
      rw [dotR_smul]; have := hno ha; push_neg at this; linarith
    obtain ⟨r, hr, hrEq⟩ := exists_of_mem_rcone_image u _ hneg
    have hzero : ∀ x y, ∑ j, (r j + c j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hrEq k
      rw [hcomb r, hEv, hcomb c] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      simp only [add_mul, Finset.sum_add_distrib]; linarith
    have hvyy : ∀ y, v y y = 0 := fun y => by
      have h1 := hzero y y
      have h2 : ∀ j, 0 ≤ (γ j y y : ℝ) := fun j => by exact_mod_cast hpsd j y
      have h3 : ∑ j, c j * (γ j y y : ℝ) ≤ ∑ j, (r j + c j) * (γ j y y : ℝ) :=
        Finset.sum_le_sum fun j _ => by nlinarith [hr j, h2 j]
      have h4 : 0 ≤ ∑ j, c j * (γ j y y : ℝ) := Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (h2 j)
      have : (v y y : ℝ) = 0 := by rw [hv_app]; linarith
      exact_mod_cast this
    have hvs : ∀ x y, v x y = v y x := fun x y => by
      have : (v x y : ℝ) = v y x := by
        rw [hv_app, hv_app]; exact Finset.sum_congr rfl fun j _ => by rw [hsym j x y]
      exact_mod_cast this
    apply hv0
    refine LinearMap.ext₂ fun x y => ?_
    have := hvyy (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, hvyy x, hvyy y, hvs y x] at this
    simp only [LinearMap.zero_apply]; omega
  obtain ⟨a, haF, hamin⟩ := Finset.exists_min_image _ (fun a => dotR a EB / dotR a Ev) hne
  obtain ⟨haA, hapos⟩ := Finset.mem_filter.mp haF
  set ts := dotR a EB / dotR a Ev with hts
  have hts0 : 0 ≤ ts := div_nonneg (hAB a haA) hapos.le
  have hB'T : EB - ts • Ev ∈ rcone T := (hA _).mpr fun a' ha' => by
    rw [dotR_sub, dotR_smul]
    by_cases hpos : 0 < dotR a' Ev
    · have := hamin a' (Finset.mem_filter.mpr ⟨ha', hpos⟩)
      rw [le_div_iff₀ hpos] at this
      linarith
    · push_neg at hpos; nlinarith [hAB a' ha']
  have hB'a : dotR a (EB - ts • Ev) = 0 := by
    rw [dotR_sub, dotR_smul, hts]; field_simp; ring
  obtain ⟨d, hd, hdEq⟩ := exists_of_mem_rcone_image u _ hB'T
  have hdz : ∀ j, d j * ((a ⬝ᵥ u j : ℚ) : ℝ) = 0 := by
    have := hB'a; rw [hdEq, dotR_comb] at this
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j)
      (by exact_mod_cast hAu a haA j))).mp this j (Finset.mem_univ j)
  obtain ⟨N, hN, z, hz⟩ := GordanGenProof.exists_int_multiple a
  let w : (X × X) →₀ ℤ := ∑ k, Finsupp.single (p k) (z k)
  let h := linW w
  have hh : ∀ β : LinearMap.BilinForm ℤ X, h β = ∑ k, z k * β (p k).1 (p k).2 := fun β => by
    simp only [h, linW_apply, w]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    simp [Finsupp.sum_single_index]
  have hzk : ∀ k, (z k : ℝ) = (N : ℝ) * (a k : ℝ) := fun k => by
    have := congrFun hz k
    simp only [GordanCones.toQ, Pi.smul_apply, smul_eq_mul] at this
    have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
    simpa using h2
  have hhR : ∀ β : LinearMap.BilinForm ℤ X, (h β : ℝ) = N * dotR a (fun k => (β (p k).1 (p k).2 : ℝ)) := fun β => by
    rw [hh]; push_cast; simp only [hzk, dotR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hhγ : ∀ j, (h (γ j) : ℝ) = N * ((a ⬝ᵥ u j : ℚ) : ℝ) := fun j => by
    rw [hhR, ← dotR_castR]; congr 2
  have hhv : (h v : ℝ) = N * dotR a Ev := by
    rw [hhR]; congr 2; funext k; rw [hEv, hcomb c]; exact hv_app _ _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set Z := Finset.univ.filter fun j => h (γ j) = 0 with hZ
  let s : Fin Z.card ↪ Fin m := (Z.orderEmbOfFin rfl).toEmbedding
  have hsZ : ∀ j, j ∈ Set.range s ↔ j ∈ Z := fun j => by
    have := Finset.range_orderEmbOfFin Z rfl
    simp only [s, RelEmbedding.coe_toEmbedding]; rw [this]; rfl
  refine ⟨Z.card, s, h, ⟨fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
  · have : (0 : ℝ) ≤ h (γ j) := by rw [hhγ]; exact mul_nonneg hNR.le (by exact_mod_cast hAu a haA j)
    exact_mod_cast this
  · rw [hsZ]; simp [Z]
  · have : (0 : ℝ) < h v := by rw [hhv]; exact mul_pos hNR hapos
    exact_mod_cast this
  · have hdZ : ∀ j, j ∉ Z → d j = 0 := fun j hj => by
      have hne' : h (γ j) ≠ 0 := by simpa [Z] using hj
      have : ((a ⬝ᵥ u j : ℚ) : ℝ) ≠ 0 := fun h0 => hne' (by
        have := hhγ j; rw [h0, mul_zero] at this; exact_mod_cast this)
      exact (mul_eq_zero.mp (hdz j)).resolve_right this
    have hsum : ∀ F : Fin m → (X →ₗ[ℤ] X →ₗ[ℤ] ℝ), ∑ i, d (s i) • F (s i) = ∑ j, d j • F j := fun F => by
      calc ∑ i, d (s i) • F (s i) = ∑ j ∈ Finset.univ.map s, d j • F j := (Finset.sum_map Finset.univ s (fun j => d j • F j)).symm
        _ = ∑ j ∈ Z, d j • F j := by
          congr 1; ext j; rw [← hsZ]; simp
        _ = ∑ j, d j • F j := Finset.sum_subset (Finset.subset_univ Z) (fun j _ hj => by rw [hdZ j hj, zero_smul])
    have hexp : ∀ e : X × X, ∑ j, (t j - ts * c j - d j) * (γ j e.1 e.2 : ℝ) =
        ∑ j, t j * (γ j e.1 e.2 : ℝ) - ts * ∑ j, c j * (γ j e.1 e.2 : ℝ) - ∑ j, d j * (γ j e.1 e.2 : ℝ) := fun e => by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have key : ∀ x y, ∑ j, (t j - ts * c j - d j) * (γ j x y : ℝ) = 0 := hp _ fun k => by
      have := congrFun hdEq k
      rw [hEB, hEv, hcomb, hcomb, hcomb] at this
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hexp (p k)]; linarith
    refine ⟨Fin.cons ts fun i => d (s i), fun i => Fin.cases hts0 (fun i => hd _) i, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hsum (fun j => toReal (γ j))]
    refine LinearMap.ext₂ fun x y => ?_
    have k1 := key x y
    rw [hexp (x, y)] at k1
    rw [hB_app]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply', hv_app, comb_apply]
    linarith

end GlobalTheory.StarCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoveredByStarAtPointStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realCone_covered_by_star_at_point : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ), (∀ i y z, γ i y z = γ i z y) → (∀ i y, 0 ≤ γ i y y) → v ≠ 0 → InRCone γ v → B ∈ rcone γ → ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h ∧ 0 < h v ∧ B ∈ rcone (Fin.cons v fun j => γ (s j)) := by
  first | exact @GlobalTheory.StarCover.star_cover | exact GlobalTheory.StarCover.star_cover | (intros; apply GlobalTheory.StarCover.star_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def rootToFlag (H : Host E) (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have := x.2.isLt; simp only [Datum.mult, h, if_true] at this; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have := x.2.isLt; simp only [Datum.mult, h, if_false] at this; omega⟩)

noncomputable def rho (H : Host E) (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (rootToFlag H Dw)

noncomputable def intGr (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : ℝ :=
  Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
            (rho H Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) /
    ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H))

noncomputable def relIdeal (H : Host E) (Dw : Datum H) : Ideal (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : E →+* ℂ => (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)) ∪
    {P | ∃ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k ∧ P = X (τ, k)} ∪
    {P | ∃ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k ∧
      P = ∑ a ∈ Finset.range (k + 1),
        C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)})

end GlobalTheory.GrassTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

namespace GlobalTheory.BaseDim

theorem two_card_psi (E : Type) [Field E] [NumberField E] [IsCMField E] {r : ℕ} (D : ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    2 * D.Ψ.card = Module.finrank ℚ E := Formalism.L2.Pj.DatLin.two_card D.cmType

theorem eq_of_smooth_two {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (m n : ℕ) (hm : SmoothOfRelativeDimension m f) (hn : SmoothOfRelativeDimension n f) : m = n := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := genericPoint X) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨α, hα⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  algebraize [α.hom]
  have t₁ := trdeg_eq_of_smoothOfRelativeDimension K X f m hm Γ(X, U) hU.fromSpec inferInstance hα.symm
  have t₂ := trdeg_eq_of_smoothOfRelativeDimension K X f n hn Γ(X, U) hU.fromSpec inferInstance hα.symm
  exact_mod_cast t₁.symm.trans t₂

theorem card_eq_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ Φ k X j f f₀ Eb A₀ hj hL
  have hoi : IsOpenImmersion j := hL.1
  have hs : SmoothOfRelativeDimension Dw.dim (genStr T.Z) := T.smooth
  have hi : IsIso (spMap e.toRingHom) := inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have h0 : SmoothOfRelativeDimension 0 (spMap e.toRingHom) := inferInstance
  have h2 : SmoothOfRelativeDimension (Dw.dim + 0) (genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [Nat.add_zero] at h2
  have h1 : SmoothOfRelativeDimension (0 + Dw.dim) (j ≫ genStr T.Z ≫ spMap e.toRingHom) := inferInstance
  rw [hj, Nat.zero_add] at h1
  have hd : Dw.dim = X.dim := eq_of_smooth_two X.X X.str Dw.dim X.dim h1 X.smooth
  rw [← hd, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.dim, ← two_card_psi E (U.X k), Nat.mul_div_cancel_left _ two_pos]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.add_sub_cancel_left, Nat.mul_assoc]

end GlobalTheory.BaseDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPqStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  first | exact @GlobalTheory.BaseDim.card_eq_dim | exact GlobalTheory.BaseDim.card_eq_dim | (intros; apply GlobalTheory.BaseDim.card_eq_dim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pull_ample_kTriv {S S' : Scheme.{0}} [IsAffine S] {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) :
    Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S)
    (fun _ => trivial) hA, kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem ample_kTriv_of_iso {S S' : Scheme.{0}} [IsAffine S'] {t : SAB H S} {u : SAB H S'} {j : S' ⟶ S} [IsIso j]
    (m : SABMap u t j) (hA : Out.RelAmple u.G u.PP.L) (hK : Out.KTriv u.G u.PP.L) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m n (g := inv j) (by simp)
  exact pull_ample_kTriv m' hA hK

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (hf : Function.Bijective f) :
    IsIso (spMap f) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  exact exists_sab f t

theorem isProper_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (hp : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback m.cart.1 hp

end GlobalTheory.PolLocal

namespace GlobalTheory.PolLocal

theorem algebraMap_fractionRing_bijective (O : Type) [CommRing O] [IsDomain O] (hf : IsField O) :
    Function.Bijective (algebraMap O (FractionRing O)) := by
  refine ⟨IsFractionRing.injective O (FractionRing O), fun z => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) z
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (nonZeroDivisors.ne_zero y.2)
  refine ⟨x * b, ?_⟩
  calc algebraMap O (FractionRing O) (x * b) = z * algebraMap O (FractionRing O) (y * b) := by
        rw [map_mul, map_mul, ← mul_assoc, ← hxy]
    _ = z := by rw [hb, map_one, mul_one]

end GlobalTheory.PolLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem carrierDim_le_of_add_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  intro O _ bar q ψ lab hlab X _ _ _ _ hX b v hv β₀ hβ₀ hp₀ β hβ hp hin c₀ c hc₀ hc hrel
  obtain ⟨e, he, he'⟩ := hin
  have hw : ∀ k, 0 ≤ c₀ * e k + c k := fun k => add_nonneg (mul_nonneg hc₀.le (he k)) (hc k)
  have hcomb : toReal β = ∑ k, (c₀ * e k + c k) • toReal (v k) := by
    rw [hrel, he', Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, add_smul]
  have hβv : InRCone v β := ⟨_, hw, hcomb⟩
  have hne : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}).Nonempty := ⟨_, b, v, hv, hβv, rfl⟩
  obtain ⟨m, τ, hτ, hβτ, hrank⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hτ.strict
  have hψτ : ((ℓ β : ℤ) : ℝ) = N * ψ.evalZ β := by
    obtain ⟨d, hd, hde⟩ := hβτ
    rw [apply_eq_of_toReal_eq hde ℓ]
    have A := (linearOn_iff ψ τ).1 hτ.linear d hd
    rw [← hde, evalR_toReal] at A
    rw [A, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
  have hψv : ψ.evalZ β = c₀ * ψ.evalZ β₀ + ∑ k, c k * ψ.evalZ (v k) := by
    have A := (linearOn_iff ψ v).1 hv.linear _ hw
    rw [← hcomb, evalR_toReal] at A
    have B := (linearOn_iff ψ v).1 hv.linear e he
    rw [← he', evalR_toReal] at B
    rw [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hℓv : ((ℓ β : ℤ) : ℝ) = c₀ * ℓ β₀ + ∑ k, c k * ℓ (v k) := by
    rw [apply_eq_of_toReal_eq hcomb ℓ, apply_eq_of_toReal_eq he' ℓ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, (N : ℝ) * ψ.evalZ (v k) ≤ ℓ (v k) := fun k => h2 _ (hv.mem k) (hv.nonneg k)
  have h0 : (N : ℝ) * ψ.evalZ β₀ ≤ ℓ β₀ := h2 _ hβ₀ hp₀
  have heq : (N : ℝ) * ψ.evalZ β₀ = ℓ β₀ := by
    have hsum : ∑ k, c k * (N * ψ.evalZ (v k)) ≤ ∑ k, c k * (ℓ (v k) : ℝ) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hc k)
    have E : c₀ * (ℓ β₀ : ℝ) + ∑ k, c k * (ℓ (v k) : ℝ) = c₀ * (N * ψ.evalZ β₀) + ∑ k, c k * (N * ψ.evalZ (v k)) := by
      rw [← hℓv, hψτ, hψv, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    by_contra hne'
    have hlt : (N : ℝ) * ψ.evalZ β₀ < ℓ β₀ := lt_of_le_of_ne h0 hne'
    have := mul_lt_mul_of_pos_left hlt hc₀
    linarith
  obtain ⟨kk, d, hkk, hd⟩ := h3 β₀ hβ₀ hp₀ heq
  have hβ₀τ : InRCone τ β₀ := by
    refine ⟨fun i => (d i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b' => ?_⟩
    have h := LinearMap.congr_fun₂ hd a b'
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have hR : (kk : ℝ) * (β₀ a b' : ℝ) = ∑ i, (d i : ℝ) * (τ i a b' : ℝ) := by exact_mod_cast h
    have hkR : (kk : ℝ) ≠ 0 := by positivity
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc (β₀ a b' : ℝ) = ((kk : ℝ) * (β₀ a b' : ℝ)) / kk := by field_simp
      _ = _ := by rw [hR, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hle := Nat.sInf_le (s := {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β₀ ∧ genRank γ = k}) ⟨m, τ, hτ, hβ₀τ, rfl⟩
  rw [hlab X hX β hβ hp, hlab X hX β₀ hβ₀ hp₀]
  exact_mod_cast hle.trans hrank.le

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGeneratorsStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrierDim_le_of_add_cell_generators : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  first | exact @GlobalTheory.PolFan.carrierDim_le_of_add_cell | exact GlobalTheory.PolFan.carrierDim_le_of_add_cell | (intros; apply GlobalTheory.PolFan.carrierDim_le_of_add_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChart
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.ChartCoords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem co_congr {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} {f f' g : EigFrame Z φ x}
    (h : ∀ τ i, f'.v τ i = f.v τ i) (τ : E →+* ℂ) : f'.co g τ = f.co g τ :=
  EigFrame.co_eq fun i => by rw [funext (h τ)]; exact f.co_spec g τ i

theorem v_of_isMap_trans {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} {φ₁ : c.F →+* R₁} {x₁ : Sp R₁ ⟶ Z.X} {φ₂ : c.F →+* R₂} {x₂ : Sp R₂ ⟶ Z.X}
    {f : EigFrame Z φ x} {f₁ : EigFrame Z φ₁ x₁} {f₂ f₂' : EigFrame Z φ₂ x₂} {ψ₁ : R →+* R₁} {ψ₂ : R₁ →+* R₂}
    {ψ : R →+* R₂} (h₁ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ₁ f₁) (h₂ : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f₁ embτ basisIdx) ψ₂ f₂) (h : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f₂') (hψ : ψ₂.comp ψ₁ = ψ)
    (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : f₂.v τ i = f₂'.v τ i := by
  rw [h₂ τ i, h₁ τ i, GlobalTheory.GradedPieces.dual_comp, hψ, h τ i]

end GlobalTheory.LieBase.ChartCoords

open GlobalTheory.ProjVar.Var GlobalTheory.LieBase.ChartCoords

theorem GlobalTheory.LieBase.coords_eq_ratVal_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ F _ e X j f₀ S A₀ hj _hoi hT V φ Φ hV A
  classical
  have hVa : IsAffineOpen V.1 := V.2
  haveI : Mono (LogKS.chart V) := inferInstanceAs (Mono hVa.fromSpec)
  have hmem : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 →
      under z ∈ j ⁻¹ᵁ V.1 := fun z hz => mem_ptsIn.1 hz
  by_cases hη : genericPoint X.X ∈ j ⁻¹ᵁ V.1
  swap
  · exact ⟨0, fun z _ hz => absurd (gen_mem (hmem z hz)) hη⟩
  have key : ∀ x : X.X, x ∈ j ⁻¹ᵁ V.1 → ∃ ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x,
      spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j := fun x hx =>
    TieBase.exists_affine_factor _ V.2 (by
      show j (X.X.fromSpecStalk x (IsLocalRing.closedPoint _)) ∈ V.1
      rw [Scheme.fromSpecStalk_closedPoint]; exact hx)
  have key' : ∀ (x : X.X) (ψ : Γ(gen Z, V.1) →+* X.X.presheaf.stalk x), spMap ψ ≫ LogKS.chart V = stalkPt X x ≫ j →
      spMap ((algebraMap (X.X.presheaf.stalk x) X.X.functionField).comp ψ) ≫ LogKS.chart V = genericPt X ≫ j :=
    fun x ψ h => by rw [TieBase.spMap_trans, Category.assoc, h, TieBase.genericPt_eq X x, Category.assoc]
  obtain ⟨ψη, hψη⟩ := key _ hη
  obtain ⟨ρ, h₀⟩ : ∃ ρ : Γ(gen Z, V.1) →+* X.X.functionField, spMap ρ ≫ LogKS.chart V = genericPt X ≫ j :=
    ⟨_, key' _ ψη hψη⟩
  have hφK : constF e X = ρ.comp φ := EigLoc.spMap_inj (by
    rw [← TieBase.genericPt_str e X j hj, ← h₀, Category.assoc, hV, ← TieBase.spMap_trans])
  obtain ⟨ΦK, hΦK⟩ := Φ.exists_isMap ρ hφK (x' := genericPt X ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← h₀, Category.assoc])
  refine ⟨fun τ => ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹, fun z hA hz => ?_⟩
  have hx := hmem z hz
  obtain ⟨φx, fz, hc⟩ := hT.2 (under z) A hA
  obtain ⟨ψx, hψx⟩ := key _ hx
  have hρx : (algebraMap _ X.X.functionField).comp ψx = ρ :=
    EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 ((key' _ ψx hψx).trans h₀.symm))
  have hφx : φx = ψx.comp φ := RingHom.ext fun a => IsFractionRing.injective (X.X.presheaf.stalk (under z))
    X.X.functionField (by
      have h1 := RingHom.congr_fun hc.2.1 a
      have h2 := RingHom.congr_fun hφK a
      rw [← hρx] at h2
      exact h1.symm.trans h2)
  obtain ⟨Φx, hΦx⟩ := Φ.exists_isMap ψx hφx (x' := stalkPt X (under z) ≫ j ≫ genι Z)
    (by rw [← Category.assoc, ← hψx, Category.assoc])
  have hM : ∀ fz' : EigFrame Z φx (stalkPt X (under z) ≫ j ≫ genι Z),
      fz'.Coord (algebraMap (X.X.presheaf.stalk (under z)) X.X.functionField) f₀ (A₀ * A⁻¹) → ∀ τ,
      ΦK.co f₀ τ * (((A₀ * A⁻¹) τ)ᵀ)⁻¹ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := by
    intro fz' hc' τ
    obtain ⟨k, hk⟩ := fz'.exists_isMap _ hc'.2.1 hc'.1
    obtain ⟨Φk, hΦk⟩ := Φx.exists_isMap _ hc'.2.1 hc'.1
    have h1 : k.co f₀ τ = ((A₀ * A⁻¹) τ)ᵀ := EigFrame.co_eq fun i => by rw [funext (hk τ)]; exact hc'.2.2 τ i
    have h3 : Φk.co k τ = (Φx.co fz' τ).map (algebraMap _ X.X.functionField) := hΦk.co τ hk hc'.1
    have h4 : Φk.co f₀ τ = ΦK.co f₀ τ := co_congr (v_of_isMap_trans hΦx hΦk hΦK hρx) τ
    have h5 : f₀.co k τ = (k.co f₀ τ)⁻¹ := (Matrix.inv_eq_right_inv ((k.co_mul f₀ k τ).trans (k.co_self τ))).symm
    rw [← h3, ← Φk.co_mul f₀ k τ, h4, h5, h1]
  have hs : spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) = z.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1
  have hxz : (cxOf e σ hj z).1 ≫ genι Z = spMap (Scheme.stalkClosedPointTo z.1).hom ≫ stalkPt X (under z) ≫ j ≫ genι Z := by
    show (z.1 ≫ j) ≫ genι Z = _
    conv_lhs => rw [← hs]
    simp only [Category.assoc]
  refine ⟨fun τ p q => ?_, ?_, ?_⟩
  · beta_reduce
    rw [hM fz hc τ]
    exact ⟨Φx.co fz τ p q, rfl⟩
  · have hφ : σ = (Scheme.stalkClosedPointTo z.1).hom.comp φx := RingHom.ext fun a => by
      have h3 : φx a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
        ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under z)).commutes _).symm)
      show σ a = evStalk z (φx a)
      rw [h3]
      refine Eq.trans ?_ ((evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
      simp
    obtain ⟨g, hg⟩ := fz.exists_isMap _ hφ hxz
    exact ⟨g, φx, fz, _, (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm, hc, hg⟩
  · rintro g ⟨φ', fz', ψ', hψ', hc', hm'⟩ f hf τ
    obtain rfl : ψ' = (Scheme.stalkClosedPointTo z.1).hom :=
      EigLoc.spMap_inj ((cancel_mono (X.X.fromSpecStalk (under z))).1
        (hψ'.symm.trans (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z.1).symm))
    obtain rfl : φ' = φx := RingHom.ext fun a => IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc'.2.1 a).symm.trans (RingHom.congr_fun hc.2.1 a))
    have hev : (Scheme.stalkClosedPointTo z.1).hom.comp ψx = evHom hz :=
      EigLoc.spMap_inj ((cancel_mono (LogKS.chart V)).1 (by
        rw [TieBase.spMap_trans, Category.assoc, hψx, LieMet.spMap_evHom hz, ← Category.assoc, hs]
        rfl))
    have hfx : Φx.IsMap (Scheme.stalkClosedPointTo z.1).hom f := fun τ i => by
      rw [hf τ i, hΦx τ i, GlobalTheory.GradedPieces.dual_comp, hev]
    beta_reduce
    rw [hfx.co τ hm' hxz, hM fz' hc' τ]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply]
    rw [GlobalTheory.TrueGeo.Res.ratVal_eq_valAt z ⟨_, rfl⟩, GlobalTheory.TrueGeo.Res.valAt_algebraMap]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoordinatesEqRationalMatrixValuesChartStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ A : Mat Dw.mult X.Fn, ∃ M : Mat Dw.mult X.Fn, ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), A ∈ S.S (under z) → ∀ hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1, (∀ τ p q, RegAt (under z) (M τ p q)) ∧ (∃ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g) ∧ ∀ g : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), FrameAt e f₀ A₀ A z g → ∀ f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → ∀ τ, f.co g τ = (M τ).map (fun r => ratVal r z) := by
  first | exact @GlobalTheory.LieBase.coords_eq_ratVal_of_chart | exact GlobalTheory.LieBase.coords_eq_ratVal_of_chart | (intros; apply GlobalTheory.LieBase.coords_eq_ratVal_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarrySpec

theorem carries_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk :=
  GlobalTheory.CarrySpec.spec_of_anypoint GlobalTheory.T.carried_frame_triangular_through_stalkFrames

end GlobalTheory.CarrySpec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRingStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriedFrames_specialise_flagComponent_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  first | exact @GlobalTheory.CarrySpec.carries_spec | exact GlobalTheory.CarrySpec.carries_spec | (intros; apply GlobalTheory.CarrySpec.carries_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

theorem exists_rescale_prim : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  intro O _ _ bar φ X _ _ _ m δ hδ hli
  choose n u hmem hn hu hprim using fun i => exists_prim (bar := bar) (hδ.mem i) (hli.ne_zero i)
  have hcu : IsCell bar φ u := cell_rescale hδ n hn hu hmem
  refine ⟨u, hcu, linearIndependent_of_smul hli n hn hu, fun i => hprim i, ?_⟩
  rintro β ⟨c, hc, hβ⟩
  refine ⟨fun i => c i * n i, fun i => mul_nonneg (hc i) (Nat.cast_nonneg _), ?_⟩
  rw [hβ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : toReal (δ i) = (n i : ℝ) • toReal (u i) := by
    rw [hu i]; exact LinearMap.ext₂ fun x y => by simp
  rw [e, smul_smul]

end GlobalTheory.PolFan.SmoothEnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescalePrimitiveLinearIndependentCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_primitive_linearIndependent_cell : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ δ → LinearIndependent ℤ δ →
    ∃ (δ' : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ'), LinearIndependent ℤ δ' ∧
      (∀ i, IsPrim bar (⟨δ' i, h.mem i⟩ : balForms bar X)) ∧ ∀ β, InRCone δ β → InRCone δ' β := by
  first | exact @GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | exact GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim | (intros; apply GlobalTheory.PolFan.SmoothEnd.exists_rescale_prim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPos
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPos
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cellMult_pos {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → balForms bar X) : 0 < cellMult bar δ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  unfold cellMult
  set M := balForms bar X ⧸ Submodule.span ℤ (Set.range δ)
  set T := Submodule.torsion ℤ M
  haveI : IsNoetherian ℤ (LinearMap.BilinForm ℤ X) := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  haveI : IsNoetherian ℤ M := inferInstance
  haveI : IsNoetherian ℤ T := isNoetherian_of_submodule_of_noetherian ℤ M T inferInstance
  haveI : Module.Finite ℤ T := ⟨IsNoetherian.noetherian ⊤⟩
  haveI : AddGroup.FG T := by
    rw [← Module.Finite.iff_addGroup_fg]; infer_instance
  haveI : Finite T := by
    apply AddCommGroup.finite_of_fg_torsion
    rintro ⟨x, hx⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hx
    refine (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    ext
    exact hax
  exact Nat.card_pos

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPosStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedFormCellMultiplicity_pos : ∀ {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m : ℕ} (δ : Fin m → balForms bar X), 0 < cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.cellMult_pos | exact GlobalTheory.PolFan.cellMult_pos | (intros; apply GlobalTheory.PolFan.cellMult_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPq
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DimOpenlyImmersedVarietyEqCmTypeCardMulPqStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.OpenBaseDim.dim_eq | exact GlobalTheory.OpenBaseDim.dim_eq | (intros; apply GlobalTheory.OpenBaseDim.dim_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFan
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem linearOn_of_forall_inRCone {O : Type} [CommRing O] (χ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin n → LinearMap.BilinForm ℤ X}
    (hχ : χ.LinearOn γ) (h : ∀ j, InRCone γ (γ' j)) : χ.LinearOn γ' := by
  intro c hc
  choose a ha he using h
  have hpt : ∀ j x y, (γ' j x y : ℝ) = ∑ i, a j i * (γ i x y : ℝ) := by
    intro j x y
    have := LinearMap.congr_fun₂ (he j) x y
    simpa [LinearMap.sum_apply] using this
  have hev : ∀ j, χ.evalZ (γ' j) = ∑ i, a j i * χ.evalZ (γ i) := by
    intro j
    rw [← hχ (a j) (ha j)]
    simp only [InvFun.evalZ, hpt]
  have e : (fun x y => ∑ j, c j * (γ' j x y : ℝ)) = fun x y => ∑ i, (∑ j, c j * a j i) * (γ i x y : ℝ) := by
    funext x y
    simp only [hpt, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e, hχ _ (fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j i))]
  simp only [hev, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem subordinate_of_isStarOf : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O),
    IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  intro O _ bar q ψ w ψ' hs χ hχ X _ _ _ _ hX n γ' hγ'
  rcases hs.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, -, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, -, -, -, hβ₀, -, -, hin⟩
  · exact linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) hin
  · refine linearOn_of_forall_inRCone χ (hχ X hX m γ hγ) fun j => inRCone_trans (fun k => ?_) (hin j)
    refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hβ₀
    · simpa using inRCone_self γ (s k)

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_subordinate_to_fan : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  first | exact @GlobalTheory.PolFan.subordinate_of_isStarOf | exact GlobalTheory.PolFan.subordinate_of_isStarOf | (intros; apply GlobalTheory.PolFan.subordinate_of_isStarOf <;> assumption)
end
end
