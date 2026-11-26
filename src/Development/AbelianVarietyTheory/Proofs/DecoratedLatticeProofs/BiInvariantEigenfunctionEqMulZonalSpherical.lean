module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrder

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMul
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalSum

open GlobalTheory.CuspRep.ParLaws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem diagU_mul (p q : borel k (Fin N)) (i : Fin N) : diagU (p * q) i = diagU p i * diagU q i := by
  unfold diagU
  erw [map_mul]
  rw [Pi.mul_apply, map_mul]

theorem borelSph_mul_left {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin N) k} (hb : b ∈ borel k (Fin N)) (x : GL (Fin N) k) : ψ (b * x) = ψ b * ψ x := by
  obtain ⟨b', hb', w, hw, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val x
  have hb'' : b' ∈ borel k (Fin N) := (mem_borel _).2 hb'
  have hbb : b * b' ∈ borel k (Fin N) := mul_mem hb hb''
  have e1 : b * (b' * w) = (b * b') * w := (mul_assoc _ _ _).symm
  rw [e1, h.1 _ _ hw, h.1 _ _ hw]
  have t1 := fun i => (val_diagU ⟨b, hb⟩ i).symm
  have t2 := fun i => (val_diagU ⟨b', hb''⟩ i).symm
  have t3 := fun i => (val_diagU ⟨b * b', hbb⟩ i).symm
  rw [h.2 _ hb _ t1, h.2 _ hb'' _ t2, h.2 _ hbb _ t3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e2 : (⟨b * b', hbb⟩ : borel k (Fin N)) = ⟨b, hb⟩ * ⟨b', hb''⟩ := rfl
  rw [e2, diagU_mul, ord_mul, zpow_add₀ (hγ i)]

theorem eq_of_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {g₁ g₂ : GL (Fin N) k} (h₁ : g₁ ∈ R) (h₂ : g₂ ∈ R) (h : g₁⁻¹ * g₂ ∈ KO k (Fin N)) : g₁ = g₂ := by
  obtain ⟨κ, hκ, κ', hκ', e⟩ := hR.1 g₂ h₂
  obtain ⟨g, -, hu⟩ := hR.2 κ hκ
  have a2 : g₂⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₂⁻¹ * (κ * g₀) = κ'⁻¹ := by rw [e]; group
    rw [this]; exact inv_mem hκ'
  have a1 : g₁⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₁⁻¹ * (κ * g₀) = (g₁⁻¹ * g₂) * (g₂⁻¹ * (κ * g₀)) := by group
    rw [this]; exact mul_mem h a2
  rw [hu g₁ ⟨h₁, a1⟩, hu g₂ ⟨h₂, a2⟩]

theorem exists_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) {g : GL (Fin N) k} (hg : g ∈ R) :
    ∃ g' ∈ R, g'⁻¹ * (κ * g) ∈ KO k (Fin N) := by
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', e⟩ := hR.1 g hg
  obtain ⟨g', ⟨hg', hm⟩, -⟩ := hR.2 (κ * κ₁) (mul_mem hκ hκ₁)
  refine ⟨g', hg', ?_⟩
  have : g'⁻¹ * (κ * g) = (g'⁻¹ * (κ * κ₁ * g₀)) * κ₁' := by rw [e]; group
  rw [this]; exact mul_mem hm hκ₁'

theorem sum_kappa_mul {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ)
    {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) : ∑ g ∈ R, ψ (κ * g) = ∑ g ∈ R, ψ g := by
  classical
  choose f hf hfK using fun g (hg : g ∈ R) => exists_isRepsK hR hκ hg
  refine Finset.sum_bij f hf (fun a ha b hb e => ?_) (fun c hc => ?_) (fun a ha => ?_)
  · have h1 := hfK a ha
    have h2 := hfK b hb
    rw [e] at h1
    apply eq_of_isRepsK hR ha hb
    have : a⁻¹ * b = ((f b hb)⁻¹ * (κ * a))⁻¹ * ((f b hb)⁻¹ * (κ * b)) := by group
    rw [this]; exact mul_mem (inv_mem h1) h2
  · obtain ⟨a, ha, hm⟩ := exists_isRepsK hR (inv_mem hκ) hc
    refine ⟨a, ha, eq_of_isRepsK hR (hf a ha) hc ?_⟩
    have : (f a ha)⁻¹ * c = ((f a ha)⁻¹ * (κ * a)) * (a⁻¹ * (κ⁻¹ * c)) := by group
    rw [this]; exact mul_mem (hfK a ha) hm
  · have : κ * a = f a ha * ((f a ha)⁻¹ * (κ * a)) := by group
    rw [this, h.1 _ _ (hfK a ha)]

end GlobalTheory.ZonalSum

open GlobalTheory.ZonalSum in
theorem GlobalTheory.ZonalSum.sum_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  intro k _ _ _ _ N γ ψ h hγ g₀ R hR m
  obtain ⟨b, hb, κ, hκ, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val m
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have e : ∀ g, ψ (b * κ * g) = ψ b * ψ (κ * g) := fun g => by
    rw [mul_assoc]; exact borelSph_mul_left h hγ hb' _
  simp only [e]
  rw [← Finset.mul_sum, sum_kappa_mul h hR hκ, h.1 _ _ hκ]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMulStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  first | exact @GlobalTheory.ZonalSum.sum_mul_eq | exact GlobalTheory.ZonalSum.sum_mul_eq | (intros; apply GlobalTheory.ZonalSum.sum_mul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalEig

theorem zonalInt_eig : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hμ ψ hψ R c hR m
  have hKo := (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N))
  have hcont : Continuous ψ := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_)
    have ho : IsOpen ((fun x => g⁻¹ * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k))) := hKo.preimage (by fun_prop)
    filter_upwards [ho.mem_nhds (show g⁻¹ * g ∈ (KO k (Fin N) : Set (GL (Fin N) k)) by
      rw [inv_mul_cancel]; exact one_mem _)] with x hx
    have := hψ g _ hx
    rwa [mul_inv_cancel_left] at this
  have hint : ∀ y, IntegrableOn (fun κ => ψ (κ * y)) (KO k (Fin N) : Set (GL (Fin N) k)) μK := fun y =>
    (hcont.comp (continuous_mul_const y)).continuousOn.integrableOn_compact GlobalTheory.SplitFlip.isCompact_KO
  simp only [zonalInt]
  rw [← integral_finsetSum _ (fun g _ => hint (m * g)), ← integral_const_mul]
  congr 1
  funext κ
  have := hR (κ * m)
  simpa only [mul_assoc] using this

end GlobalTheory.ZonalEig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEigStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ (R : Finset (GL (Fin N) k)) (c : ℂ), (∀ m, ∑ g ∈ R, ψ (m * g) = c * ψ m) → ∀ m, ∑ g ∈ R, zonalInt μK ψ (m * g) = c * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalEig.zonalInt_eig | exact GlobalTheory.ZonalEig.zonalInt_eig | (intros; apply GlobalTheory.ZonalEig.zonalInt_eig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariant
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalBi

theorem zonalInt_biInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ψ hψ κ₀ hκ₀ m
  have hKo : IsOpen (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isOpen_KO
  have hKc : IsCompact (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hKcl : IsClosed (KO k (Fin N) : Set (GL (Fin N) k)) := Subgroup.isClosed_of_isOpen _ hKo
  have hKfr : frontier (KO k (Fin N) : Set (GL (Fin N) k)) = ∅ := (IsClopen.frontier_eq ⟨hKcl, hKo⟩)
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := hKo.measurableSet
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hmem : (fun y => g⁻¹ * y) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) ∈ nhds g :=
      (hKo.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])
    have hev : ∀ᶠ y in nhds g, ψ y = ψ g := by
      filter_upwards [hmem] with y hy
      have := hψ g (g⁻¹ * y) hy
      rwa [mul_inv_cancel_left] at this
    exact tendsto_nhds_of_eventually_eq hev
  refine ⟨?_, ?_⟩
  · set ν : Measure (GL (Fin N) k) := Measure.map (· * κ₀) μK with hν
    set c := Measure.haarScalarFactor ν μK with hc
    have L : ∀ f : GL (Fin N) k → ℝ, Continuous f → HasCompactSupport f →
        ∫ x, f x ∂ν = ∫ x, f x ∂(c • μK) := fun f hf hs =>
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μK hf hs
    have hpre : (· * κ₀) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) = KO k (Fin N) := by
      ext x; simp [Subgroup.mul_mem_cancel_right _ hκ₀]
    have hc1 : c = 1 := by
      have h1 := L ((KO k (Fin N) : Set (GL (Fin N) k)).indicator 1)
        (continuous_indicator (by simp [hKfr]) continuous_one.continuousOn)
        (HasCompactSupport.intro hKc fun x hx => by simp [hx])
      rw [integral_indicator_one hKm, integral_indicator_one hKm] at h1
      simp only [Measure.real, hν, Measure.map_apply (measurable_mul_const κ₀) hKm, hpre, Measure.smul_apply, hK] at h1
      simpa using h1.symm
    set F : GL (Fin N) k → ℂ := (KO k (Fin N) : Set (GL (Fin N) k)).indicator fun x => ψ (x * m) with hFdef
    have hF : Continuous F :=
      continuous_indicator (by simp [hKfr]) (hψc.comp (continuous_mul_const m)).continuousOn
    have hFs : HasCompactSupport F := HasCompactSupport.intro hKc fun x hx => by simp [F, hx]
    have e1 : zonalInt μK ψ (κ₀ * m) = ∫ x, F (x * κ₀) ∂μK := by
      unfold zonalInt
      rw [← integral_indicator hKm]
      congr 1; funext x
      by_cases hx : x ∈ KO k (Fin N)
      · have hx' : x * κ₀ ∈ KO k (Fin N) := mul_mem hx hκ₀
        rw [hFdef, Set.indicator_of_mem (SetLike.mem_coe.2 hx), Set.indicator_of_mem (SetLike.mem_coe.2 hx'), mul_assoc]
      · have hx' : x * κ₀ ∉ KO k (Fin N) := fun h => hx ((Subgroup.mul_mem_cancel_right _ hκ₀).1 h)
        rw [hFdef, Set.indicator_of_notMem (fun h => hx (SetLike.mem_coe.1 h)),
          Set.indicator_of_notMem (fun h => hx' (SetLike.mem_coe.1 h))]
    have e2 : zonalInt μK ψ m = ∫ x, F x ∂μK := by
      unfold zonalInt; rw [← integral_indicator hKm]
    have e3 : ∫ x, F (x * κ₀) ∂μK = ∫ x, F x ∂ν :=
      (integral_map (measurable_mul_const κ₀).aemeasurable hF.aestronglyMeasurable).symm
    have hIν : Integrable F ν := hF.integrable_of_hasCompactSupport hFs
    have hIμ : Integrable F μK := hF.integrable_of_hasCompactSupport hFs
    have Lre := L (fun x => (F x).re) (Complex.continuous_re.comp hF) (hFs.comp_left Complex.zero_re)
    have Lim := L (fun x => (F x).im) (Complex.continuous_im.comp hF) (hFs.comp_left Complex.zero_im)
    rw [hc1, one_smul] at Lre Lim
    have e4 : ∫ x, F x ∂ν = ∫ x, F x ∂μK := by
      apply Complex.ext
      · have a := integral_re hIν
        have b := integral_re hIμ
        simp only [RCLike.re_to_complex] at a b
        rw [← a, ← b, Lre]
      · have a := integral_im hIν
        have b := integral_im hIμ
        simp only [RCLike.im_to_complex] at a b
        rw [← a, ← b, Lim]
    rw [e1, e3, e4, e2]
  · unfold zonalInt
    congr 1; funext κ
    rw [← mul_assoc, hψ _ _ hκ₀]

end GlobalTheory.ZonalBi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariantStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zonalInt_mul_KO_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalBi.zonalInt_biInvariant | exact GlobalTheory.ZonalBi.zonalInt_biInvariant | (intros; apply GlobalTheory.ZonalBi.zonalInt_biInvariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSum
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem two_mul_card_lt_pairs {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card + S.card = S.card * S.card := by
  have hsw : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · intro p _ r _ h
      exact Prod.swap_injective h
    · intro r hr
      refine ⟨r.swap, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at hr ⊢
      exact ⟨⟨hr.1.2, hr.1.1⟩, hr.2⟩
  have hoff : S.offDiag = ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2) ∪
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, ne_of_gt h⟩
  have hdisj : Disjoint ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2)
      ((S ×ˢ S).filter fun p : Fin N × Fin N => p.2 < p.1) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hc := Finset.offDiag_card S
  rw [hoff, Finset.card_union_of_disjoint hdisj, ← hsw] at hc
  have hle : S.card ≤ S.card * S.card := Nat.le_mul_self _
  omega

theorem count_identity {N : ℕ} (S : Finset (Fin N)) :
    2 * ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card + 2 * ∑ a ∈ S, (a : ℕ)
      + S.card * (S.card + 1) = 2 * S.card * N := by
  classical
  have hP := two_mul_card_lt_pairs S
  have hsplit : ((S ×ˢ S).filter fun p : Fin N × Fin N => p.1 < p.2).card
      + ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ∑ a ∈ S, (Finset.Ioi a).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_add_sum_compl, ← Finset.card_filter, Finset.filter_lt_eq_Ioi]
  have hterm : ∀ a : Fin N, (Finset.Ioi a).card + (a : ℕ) + 1 = N := by
    intro a
    rw [Fin.card_Ioi]
    have := a.isLt
    omega
  have hsum : ∑ a ∈ S, (Finset.Ioi a).card + ∑ a ∈ S, (a : ℕ) + S.card = S.card * N := by
    have h0 : ∑ a ∈ S, ((Finset.Ioi a).card + (a : ℕ) + 1) = S.card * N := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, smul_eq_mul]
    rwa [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at h0
  nlinarith [hP, hsplit, hsum]

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem prod_zpow_eq {ι : Type} (s : ℂ) (hs : s ≠ 0) (S : Finset ι) (e : ι → ℤ) :
    ∏ a ∈ S, s ^ e a = s ^ (∑ a ∈ S, e a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert b T hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add₀ hs]

theorem cpow_half_int (q : ℕ) (m : ℤ) :
    (q : ℂ) ^ ((m : ℂ) / 2) = ((Real.sqrt q : ℝ) : ℂ) ^ m := by
  have h1 : ((q : ℝ) : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((((q : ℝ) ^ ((m : ℝ) / 2) : ℝ)) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg q) _).symm
  have h2 : (q : ℝ) ^ ((m : ℝ) / 2) = (Real.sqrt q) ^ m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [h2] at h1
  push_cast at h1
  exact h1

theorem borelParam_eq (q N : ℕ) (α : Fin N → ℂˣ) (a : Fin N) :
    borelParam q α a = (α a : ℂ) * ((Real.sqrt q : ℝ) : ℂ) ^ (2 * (a : ℤ) - N + 1) := by
  unfold borelParam
  rw [← cpow_half_int]
  congr 2
  push_cast
  ring

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem term_eq (q N : ℕ) (hq : 0 < q) (α : Fin N → ℂˣ) (S : Finset (Fin N)) :
    (q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a
      = ((Real.sqrt q : ℝ) : ℂ) ^ (S.card * (N - S.card)) * ∏ a ∈ S, (α a : ℂ) := by
  set s : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hsdef
  have hs : s ≠ 0 := by
    rw [hsdef, Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
    exact_mod_cast hq
  have hs2 : (q : ℂ) = s ^ 2 := by
    rw [hsdef, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; rfl
  have hnN : S.card ≤ N := by
    simpa using Finset.card_le_univ S
  set inv := ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card with hinv
  have hcount := count_identity S
  rw [← hinv] at hcount
  simp_rw [borelParam_eq]
  rw [Finset.prod_mul_distrib, prod_zpow_eq s hs, hs2, ← pow_mul, ← zpow_natCast, ← zpow_natCast,
    mul_left_comm, ← zpow_add₀ hs, mul_comm]
  congr 2
  have hc : ((2 * inv + 2 * ∑ a ∈ S, (a : ℕ) + S.card * (S.card + 1) : ℕ) : ℤ) = ((2 * S.card * N : ℕ) : ℤ) := by
    rw [hcount]
  push_cast at hc
  push_cast [Nat.cast_sub hnN]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul]
  push_cast
  linear_combination hc

end GlobalTheory.SatakeSubsetSum

namespace GlobalTheory.SatakeSubsetSum

open Finset

theorem satake_subset_sum : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ),
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n,
      ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a)
      = genVal q 0 N (Finset.univ.val.map α) n := by
  intro q N hq α n
  unfold genVal
  rw [Multiset.map_map, Finset.esymm_map_val, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powersetCard] at hS
  rw [term_eq q N hq α S, hS.2, zero_mul, zero_add]
  rfl

end GlobalTheory.SatakeSubsetSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSumStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal : ∀ (q N : ℕ), 0 < q → ∀ (α : Fin N → ℂˣ) (n : ℕ), ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard n, ((q : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, borelParam q α a) = genVal q 0 N (Finset.univ.val.map α) n := by
  first | exact @GlobalTheory.SatakeSubsetSum.satake_subset_sum | exact GlobalTheory.SatakeSubsetSum.satake_subset_sum | (intros; apply GlobalTheory.SatakeSubsetSum.satake_subset_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.BorelCosetSum

open Formalism.UG Formalism.UG.P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem _root_.GlobalTheory.BorelCosetSum.unif_mem {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) : (ϖ : k) ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, hϖ]
  exact (uniformizer_lt_one (R := k)).le

abbrev RepIdx {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (n j : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes 𝒪[k] ⟨ϖ, unif_mem hϖ⟩

def cosetRep {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {n j : ℕ} (i : RepIdx hϖ n j) : GL (Fin n) k :=
  satakeRep 𝒪[k] ⟨(ϖ : k), unif_mem hϖ⟩ ϖ.ne_zero j i

private theorem torusElt_indic_eq_satakeGL {N : ℕ} (ϖ : kˣ) (s : Finset (Fin N)) :
    _root_.GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ (_root_.GlobalTheory.ParHecke.indic s) =
      _root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero s (fun _ => 0) := by
  refine Units.ext (Matrix.ext fun a l => ?_)
  rw [_root_.GlobalTheory.GLDoubling.val_torusElt, _root_.Formalism.UG.P.satakeGL_apply]
  by_cases h : a = l
  · subst h
    by_cases ha : a ∈ s <;> simp [_root_.GlobalTheory.ParHecke.indic, _root_.Formalism.UG.P.satakeN, ha]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, _root_.Formalism.UG.P.satakeN]

private theorem irreducible_of_valuation_eq_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) :
    Irreducible (⟨ϖ, _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩ : 𝒪[k]) := by
  have hint := Valuation.integer.integers (valuation k)
  have hlt : uniformizer k < 1 := uniformizer_lt_one
  have hpos : 0 < uniformizer k := uniformizer_pos
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [hint.isUnit_iff_valuation_eq_one] at hu
    exact hlt.ne (by rw [← hϖ]; exact hu)
  · rw [hint.isUnit_iff_valuation_eq_one, hint.isUnit_iff_valuation_eq_one]
    have hv : valuation k (a : k) * valuation k (b : k) = uniformizer k := by
      rw [← hϖ, ← map_mul]
      exact congrArg (fun x : 𝒪[k] => valuation k (x : k)) hab.symm
    have ha : valuation k (a : k) ≤ 1 := a.2
    have hb : valuation k (b : k) ≤ 1 := b.2
    by_contra h
    push_neg at h
    have ha' := le_uniformizer_iff.mpr (lt_of_le_of_ne ha h.1)
    have hb' := le_uniformizer_iff.mpr (lt_of_le_of_ne hb h.2)
    have h1 : uniformizer k ≤ uniformizer k * uniformizer k := hv.symm.le.trans (mul_le_mul' ha' hb')
    have h2 : uniformizer k * uniformizer k < uniformizer k := by
      simpa using mul_lt_mul_of_pos_left hlt hpos
    exact lt_irrefl _ (h1.trans_lt h2)

private theorem uniformizer_inv_mul_mem_integer_iff_residue_eq_zero {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : 𝒪[k]) :
    (ϖ : k)⁻¹ * x ∈ 𝒪[k] ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
  have hx : valuation k (x : k) ≤ 1 := x.2
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one, Valuation.mem_integer_iff,
    map_mul, map_inv₀, hϖ, inv_mul_le_iff₀ uniformizer_pos, mul_one, le_uniformizer_iff]
  exact ⟨ne_of_lt, lt_of_le_of_ne hx⟩

private theorem uniformizer_inv_not_mem_integer {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    (ϖ : k)⁻¹ ∉ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, map_inv₀, hϖ, not_le]
  exact (one_lt_inv₀ uniformizer_pos).mpr uniformizer_lt_one

private theorem isBorelSph_apply_satakeGL_eq {N : ℕ} {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ}
    (hψ : _root_.GlobalTheory.SatakeBound.IsBorelSph k γ ψ) (S : Finset (Fin N)) (c : _root_.Formalism.UG.P.satakePairs S → 𝒪[k]) :
    ψ (_root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c) = ∏ a ∈ S, γ a := by
  have hone : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
    _root_.GlobalTheory.SmGL.ord_eq_zero (by simp)
  rw [hψ.2 _ ((_root_.GlobalTheory.SmGL.mem_borel k).mpr fun a l h => _root_.Formalism.UG.P.satakeGL_lower _ _ _ _ _ _ h)
    (fun a => if a ∈ S then ϖ else 1) (fun a => by rw [_root_.Formalism.UG.P.satakeGL_diag]; split_ifs <;> simp)]
  calc ∏ i, γ i ^ _root_.GlobalTheory.SmGL.ord k (if i ∈ S then ϖ else 1)
      = ∏ i, if i ∈ S then γ i else 1 := Finset.prod_congr rfl fun i _ => by
        split_ifs <;> simp [_root_.GlobalTheory.SmGL.ord_eq_one hϖ, hone]
    _ = ∏ a ∈ S, γ a := by rw [Finset.prod_ite_mem, Finset.univ_inter]

private theorem card_satakePairs_eq_card_filter_lt {N : ℕ} (S : Finset (Fin N)) :
    Fintype.card (_root_.Formalism.UG.P.satakePairs S) = ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card := by
  rw [← Nat.card_eq_fintype_card]
  show Nat.card {p : Fin N × Fin N // p.1 ∈ S ∧ p.2 ∉ S ∧ p.1 < p.2} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext p
  simp [Finset.mem_product, and_assoc]

theorem _root_.GlobalTheory.BorelCosetSum.sum_cosets_eq : ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ),
    _root_.GlobalTheory.SatakeBound.IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N))
    (R : Finset (GL (Fin N) k)),
    _root_.GlobalTheory.ParHecke.IsRepsK
      (_root_.GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ (_root_.GlobalTheory.ParHecke.indic s)) R →
    ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card,
      ((_root_.GlobalTheory.SplitWeil.resCard k : ℂ) ^
        ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  intro k _ _ _ _ N ϖ hϖ γ ψ hψ _ s R hR
  classical
  set π : 𝒪[k] := ⟨ϖ, _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩ with hπdef
  set j := s.card with hj
  set q := _root_.GlobalTheory.SplitWeil.resCard k with hqdef
  set K := _root_.GlobalTheory.SplitWeil.KO k (Fin N) with hK
  set dJ := _root_.Formalism.UG.P.tjcosets_dG N j (ϖ : k) ϖ.ne_zero with hdJ
  set d := _root_.GlobalTheory.GLDoubling.torusElt (k := k) (n := Fin N) ϖ
    (_root_.GlobalTheory.ParHecke.indic s) with hddef
  obtain ⟨hR1, hR2⟩ := hR
  let P : GL (Fin N) k → Prop := fun g => ∃ a ∈ K, ∃ b ∈ K, g = a * dJ * b
  have hPsat : ∀ (S : Finset (Fin N)) (c : _root_.Formalism.UG.P.satakePairs S → 𝒪[k]), S.card = j →
      P (_root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c) := by
    intro S c hS
    obtain ⟨a, ha, b, hb, h⟩ := _root_.Formalism.UG.P.satakeGL_mem_doset 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero S c
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [h, Units.val_mul, Units.val_mul, hdJ, _root_.Formalism.UG.P.tjcosets_dG_val, hS]
  have hPmul : ∀ g, P g → ∀ κ ∈ K, ∀ κ' ∈ K, P (κ * g * κ') := by
    rintro g ⟨a, ha, b, hb, rfl⟩ κ hκ κ' hκ'
    exact ⟨κ * a, K.mul_mem hκ ha, b * κ', K.mul_mem hb hκ', by group⟩
  obtain ⟨a₀, ha₀, b₀, hb₀, hd⟩ : P d := by
    have := hPsat s (fun _ => 0) rfl
    rwa [← torusElt_indic_eq_satakeGL] at this
  have hPiff : ∀ g, P g ↔ ∃ κ ∈ K, ∃ κ' ∈ K, g = κ * d * κ' := by
    intro g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨a * a₀⁻¹, K.mul_mem ha (K.inv_mem ha₀), b₀⁻¹ * b, K.mul_mem (K.inv_mem hb₀) hb, ?_⟩
      rw [hd]; group
    · rintro ⟨κ, hκ, κ', hκ', rfl⟩
      rw [hd]
      exact ⟨κ * a₀, K.mul_mem hκ ha₀, b₀ * κ', K.mul_mem hb₀ hκ', by group⟩
  have hout : ∀ g : GL (Fin N) k, ∃ κ ∈ K,
      Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = g * κ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K g
    exact ⟨h, h.2, hh⟩
  have hmkP : ∀ g, P g → P (Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K)) := by
    intro g hg
    obtain ⟨κ, hκ, h⟩ := hout g
    rw [h]
    have := hPmul g hg 1 K.one_mem κ hκ
    rwa [one_mul] at this
  have hirr := irreducible_of_valuation_eq_uniformizer hϖ
  have hq1 : 1 < q := _root_.GlobalTheory.SplitWeil.one_lt_resCard k
  have hcardres : Nat.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) = q := by
    have := _root_.GlobalTheory.SatakeBound.card_quot hirr 1
    rw [pow_one, pow_one] at this
    exact this
  haveI : Finite (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) := Nat.finite_of_card_ne_zero (by rw [hcardres]; omega)
  haveI : Fintype (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) := Fintype.ofFinite _
  have hcardres' : Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] π) = q := by
    rw [← Nat.card_eq_fintype_card, hcardres]
  let X := _root_.GlobalTheory.BorelCosetSum.RepIdx hϖ N j
  let f : X → GL (Fin N) k := fun i => _root_.GlobalTheory.BorelCosetSum.cosetRep hϖ i
  have hf : ∀ i : X, f i = _root_.Formalism.UG.P.satakeGL 𝒪[k] (π := (ϖ : k)) ϖ.ne_zero i.1.1
      (fun p => _root_.Formalism.UG.P.satakeSec 𝒪[k] π (i.2 p)) := fun i => rfl
  have hcardX : Fintype.card X =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, q ^ _root_.Formalism.UG.P.satakeInv Finset.univ S := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fun, _root_.Formalism.UG.P.satakePairs_card]
    rw [show Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] ⟨(ϖ : k), _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩) = q
      from hcardres']
    exact (Finset.sum_subtype _ (fun S => by simp [Finset.mem_powersetCard])
      (fun S => q ^ _root_.Formalism.UG.P.satakeInv Finset.univ S)).symm
  haveI : Fintype (IsLocalRing.ResidueField 𝒪[k]) := Fintype.ofFinite _
  have hqres : Fintype.card (IsLocalRing.ResidueField 𝒪[k]) = q := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hjN : j ≤ N := by simpa using s.card_le_univ
  have hidx := _root_.Formalism.UG.P.tjcosets_ff_count (𝔽 := IsLocalRing.ResidueField 𝒪[k]) N j hjN
  rw [hqres] at hidx
  have h1 := _root_.Formalism.UG.P.tjcosets_arith q N j _ (by omega) hjN hidx
  have h2 := _root_.Formalism.UG.P.satake_qbinom (q : ℤ) (Finset.univ : Finset (Fin N)) j
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have hprod : ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr ?_
    exact (one_lt_pow₀ (by exact_mod_cast hq1) (Nat.succ_ne_zero i)).ne'
  have hindex : (_root_.Formalism.UG.P.tjcosets_par (𝔽 := IsLocalRing.ResidueField 𝒪[k]) N j).index = Fintype.card X := by
    have := mul_right_cancel₀ hprod (h1.trans h2.symm)
    rw [hcardX]
    exact_mod_cast this
  let Q := {x : GL (Fin N) k ⧸ K // ∃ a ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k], ∃ b ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k],
    Quotient.out x = a * dJ * b}
  have hQcard : Nat.card Q = Fintype.card X := by
    rw [← hindex]
    exact _root_.Formalism.UG.P.tjcosets_index (O := 𝒪[k]) N j (ϖ : k) (_root_.GlobalTheory.BorelCosetSum.unif_mem hϖ) ϖ.ne_zero
      (uniformizer_inv_mul_mem_integer_iff_residue_eq_zero hϖ)
  have hmk : ∀ g : GL (Fin N) k, P g →
      ∃ a ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k], ∃ b ∈ _root_.Formalism.UG.GLint (Fin N) 𝒪[k],
        Quotient.out (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = a * dJ * b := fun g hg => hmkP g hg
  let FX : X → Q := fun i => ⟨QuotientGroup.mk (f i), hmk _ (by rw [hf]; exact hPsat _ _ i.1.2)⟩
  have hFXinj : Function.Injective FX := by
    intro i i' h
    have h' : (QuotientGroup.mk (f i) : GL (Fin N) k ⧸ K) = QuotientGroup.mk (f i') :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h'
    exact _root_.Formalism.UG.P.satakeRep_inj 𝒪[k] π ϖ.ne_zero (uniformizer_inv_not_mem_integer hϖ) j i i' h'
  let FR : R → Q := fun g => ⟨QuotientGroup.mk g.1, hmk _ ((hPiff _).mpr (hR1 g.1 g.2))⟩
  have hFRinj : Function.Injective FR := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    have h' : (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = QuotientGroup.mk g' :=
      congrArg Subtype.val h
    rw [QuotientGroup.eq] at h'
    obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR1 g hg
    obtain ⟨g₁, _, huniq⟩ := hR2 κ hκ
    have e1 := huniq _ ⟨hg, by
      rw [show (κ * d * κ')⁻¹ * (κ * d) = κ'⁻¹ by group]
      exact K.inv_mem hκ'⟩
    have e2 := huniq g' ⟨hg', by
      rw [show g'⁻¹ * (κ * d) = ((κ * d * κ')⁻¹ * g')⁻¹ * κ'⁻¹ by group]
      exact K.mul_mem (K.inv_mem h') (K.inv_mem hκ')⟩
    exact Subtype.ext (e1.trans e2.symm)
  have hFRsurj : Function.Surjective FR := by
    rintro ⟨x, a, ha, b, hb, hx⟩
    have hd' : dJ = a₀⁻¹ * d * b₀⁻¹ := by rw [hd]; group
    obtain ⟨g, ⟨hg, hgκ⟩, _⟩ := hR2 (a * a₀⁻¹) (K.mul_mem ha (K.inv_mem ha₀))
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    show (QuotientGroup.mk g : GL (Fin N) k ⧸ K) = x
    rw [← QuotientGroup.out_eq' x, QuotientGroup.eq, hx, hd',
      show g⁻¹ * (a * (a₀⁻¹ * d * b₀⁻¹) * b) = (g⁻¹ * (a * a₀⁻¹ * d)) * (b₀⁻¹ * b) by group]
    exact K.mul_mem hgκ (K.mul_mem (K.inv_mem hb₀) hb)
  haveI : Nonempty X := ⟨⟨⟨s, rfl⟩, fun _ => (0 : 𝒪[k] ⧸ Ideal.span {π})⟩⟩
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQcard]; exact Fintype.card_ne_zero)
  have hFXbij : Function.Bijective FX := by
    refine hFXinj.bijective_of_nat_card_le ?_
    rw [hQcard, Nat.card_eq_fintype_card]
  let e : R ≃ X := (Equiv.ofBijective FR ⟨hFRinj, hFRsurj⟩).trans (Equiv.ofBijective FX hFXbij).symm
  have he : ∀ g : R, ψ g.1 = ψ (f (e g)) := by
    intro g
    have hfe : FX (e g) = FR g := Equiv.ofBijective_apply_symm_apply FX hFXbij (FR g)
    have h' : (QuotientGroup.mk g.1 : GL (Fin N) k ⧸ K) = QuotientGroup.mk (f (e g)) :=
      (congrArg Subtype.val hfe).symm
    rw [QuotientGroup.eq] at h'
    rw [show f (e g) = g.1 * (g.1⁻¹ * f (e g)) by group, hψ.1 _ _ h']
  calc ∑ g ∈ R, ψ g = ∑ g : R, ψ g.1 := (Finset.sum_coe_sort R ψ).symm
    _ = ∑ i : X, ψ (f i) := Fintype.sum_equiv e _ _ he
    _ = ∑ i : X, ∏ a ∈ i.1.1, γ a := Finset.sum_congr rfl fun i _ => by
        rw [hf]; exact isBorelSph_apply_satakeGL_eq hϖ hψ _ _
    _ = ∑ S : {S : Finset (Fin N) // S.card = j},
          (q : ℂ) ^ Fintype.card (_root_.Formalism.UG.P.satakePairs S.1) * ∏ a ∈ S.1, γ a := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
        rw [show Fintype.card (_root_.Formalism.UG.P.satakeRes 𝒪[k] ⟨(ϖ : k), _root_.GlobalTheory.BorelCosetSum.unif_mem hϖ⟩) = q
            from hcardres']
        push_cast
        ring
    _ = _ := by
        rw [Finset.sum_subtype ((Finset.univ : Finset (Fin N)).powersetCard j)
          (p := fun S => S.card = j) (fun S => by simp [Finset.mem_powersetCard])]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [card_satakePairs_eq_card_filter_lt]

end GlobalTheory.BorelCosetSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetRepsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (s : Finset (Fin N)) (R : Finset (GL (Fin N) k)), IsRepsK (GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (indic s)) R → ∑ g ∈ R, ψ g = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s.card, ((resCard k : ℂ) ^ ((S ×ˢ Sᶜ).filter fun p : Fin N × Fin N => p.1 < p.2).card * ∏ a ∈ S, γ a) := by
  first | exact @GlobalTheory.BorelCosetSum.sum_cosets_eq | exact GlobalTheory.BorelCosetSum.sum_cosets_eq | (intros; apply GlobalTheory.BorelCosetSum.sum_cosets_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalOne

theorem zonalInt_one_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure] :
    μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  intro hK γ ψ hψ
  have h1 : ψ 1 = 1 := by
    rw [hψ.2 1 (one_mem _) (fun _ => 1) (fun i => by simp)]
    simp [ord]
  have hκ : ∀ κ ∈ (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * 1) = 1 := by
    intro κ hκ
    rw [mul_one, ← one_mul κ, hψ.1 1 κ hκ, h1]
  unfold zonalInt
  rw [setIntegral_congr_fun GlobalTheory.SplitFlip.isOpen_KO.measurableSet hκ]
  simp [Measure.real, hK]

end GlobalTheory.ZonalOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOneStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  first | exact @GlobalTheory.ZonalOne.zonalInt_one_eq_one | exact GlobalTheory.ZonalOne.zonalInt_one_eq_one | (intros; apply GlobalTheory.ZonalOne.zonalInt_one_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSpherical
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalUnique

theorem genVal_top_ne_zero (q N : ℕ) (α : Fin N → ℂˣ) : genVal q 0 N (Finset.univ.val.map α) N ≠ 0 := by
  simp only [genVal, Nat.sub_self, mul_zero, zero_mul, add_zero, pow_zero, one_mul, Multiset.map_map]
  have e : (Multiset.map ((fun b : ℂˣ => (b : ℂ)) ∘ α) Finset.univ.val).esymm N = ∏ i, (α i : ℂ) := by
    rw [Finset.esymm_map_val]
    have : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rw [this, Finset.sum_singleton]; rfl
  rw [e, Finset.prod_ne_zero_iff]
  exact fun i _ => (α i).ne_zero

theorem eq_mul_zonalInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ϖ hϖ α
  have hq : (1 : ℕ) < resCard k := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hγ : ∀ i, borelParam (resCard k) α i ≠ 0 := by
    intro i
    unfold borelParam
    refine mul_ne_zero (α i).ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (show resCard k ≠ 0 by omega) (by exact_mod_cast h.1)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_borelSphericalFunction k N _ hγ
  refine ⟨ψ, hψ, fun f hf he m => ?_⟩
  have hr : ∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g := hψ.1
  have hωb := GlobalTheory.T.zonalInt_mul_KO_invariant k N μK hK ψ hr
  have hω1 := GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph k N μK hK _ ψ hψ
  have hωe : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, zonalInt μK ψ (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * zonalInt μK ψ m := by
    intro s R hR
    refine GlobalTheory.T.sum_zonalInt_mul_eq_of_eigen k N μK hK ψ hr R _ fun m => ?_
    rw [GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul k N _ ψ hψ hγ _ R hR m, GlobalTheory.T.sum_borelSpherical_over_diagonalDoubleCosetReps k N ϖ hϖ _ ψ hψ hγ s R hR,
      GlobalTheory.T.sum_powersetCard_borelParam_eq_genVal (resCard k) N (by omega) α s.card, mul_comm]
  have hcN : genVal (resCard k) 0 N (Finset.univ.val.map α) N ≠ 0 := genVal_top_ne_zero _ N α
  have key := GlobalTheory.T.cartan_decomposition_dominance_order k N ϖ (fun n => genVal (resCard k) 0 N (Finset.univ.val.map α) n) hcN
    (GlobalTheory.T.exists_antitone_cartan_decomposition k N ϖ hϖ) (GlobalTheory.T.cartan_decomposition_dominance_local_field k N ϖ hϖ) (fun g => (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k Unit (Fin N)).2 g)
    (fun m => f m - f 1 * zonalInt μK ψ m)
    (fun κ hκ m => ⟨by rw [(hf κ hκ m).1, (hωb κ hκ m).1], by rw [(hf κ hκ m).2, (hωb κ hκ m).2]⟩)
    (fun s R hR m => by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he s R hR m, hωe s R hR m]
      ring)
    (by simp [hω1]) m
  exact sub_eq_zero.1 key

end GlobalTheory.ZonalUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiInvariantEigenfunctionEqMulZonalSphericalStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_eigenfunction_eq_mul_zonalSpherical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  first | exact @GlobalTheory.ZonalUnique.eq_mul_zonalInt | exact GlobalTheory.ZonalUnique.eq_mul_zonalInt | (intros; apply GlobalTheory.ZonalUnique.eq_mul_zonalInt <;> assumption)
end
