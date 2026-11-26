module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestBump
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ValNhds
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem inf_cont (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ ((continuous_const.sub continuous_const).add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem val_nhds (E : Type) [Field E] [NumberField E] (a : ℕ) (y : GL (Fin a) (Cinf E))
    {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 y) : (fun z : GL (Fin a) (Cinf E) => toL z.val) '' N ∈ 𝓝 (toL y.val) :=
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

open scoped Pointwise in
private theorem loc_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (x : G) :
    ∃ s : Finset Γ, ∀ᶠ z in 𝓝 x, GlobalTheory.AutomorphicL2Unitary.orbitSum Γ f z = ∑ γ ∈ s, f (γ * z) := by
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  have hS : {γ : Γ | (γ : G) ∈ tsupport f * K⁻¹}.Finite := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (hf.isCompact.mul hK.inv)
  refine ⟨hS.toFinset, Filter.mem_of_superset hx fun z hz => tsum_eq_sum fun γ hγ => ?_⟩
  by_contra h
  exact hγ (hS.mem_toFinset.2 ⟨_, subset_tsupport f h, z⁻¹, Set.inv_mem_inv.2 hz, by simp⟩)

theorem UpperTheory.V.Cj.H.orbSm :
    UpperTheory.V.Cj.H.OrbSm := by
  intro E _ _ _ a u hu
  have hm : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) u.1 ∈ Sm E a := by
    intro g x hx
    obtain ⟨y, hy⟩ := hx
    obtain rfl : x = toL y.val := hy.symm
    obtain ⟨s, hs⟩ := loc_fin (latticeGL E a) hu.1 (g * infGL E a y)
    have hc : Continuous fun z => g * infGL E a z := continuous_const.mul (inf_cont E a)
    have h1 := val_nhds E a y (hc.continuousAt.preimage_mem_nhds hs)
    refine ((ContDiffAt.sum (s := s) fun γ _ =>
      contDiffAt_chart u.2 (γ.1 * g) (val_mem_invSet y)).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [h1]
    rintro _ ⟨z, hz, rfl⟩
    simp only [chart_val, mul_assoc]
    exact hz
  refine ⟨⟨_, hm⟩, ?_, rfl⟩
  have key : ∀ k, act (.fin k) u = u → act (.fin k) (⟨_, hm⟩ : Sm E a) = ⟨_, hm⟩ := fun k hk =>
    Subtype.ext (funext fun g => tsum_congr fun γ => by
      have h : u.1 (γ.1 * g * finGL E a k) = u.1 (γ.1 * g) := congrFun (congrArg Subtype.val hk) _
      rw [← h, mul_assoc])
  let S : ∀ φ : Sm E a, Subgroup (GL (Fin a) (Af E)) := fun φ =>
    { carrier := {k | act (.fin k) φ = φ}
      one_mem' := Subtype.ext (funext fun g => by
        change φ.1 (g * finGL E a 1) = φ.1 g
        rw [map_one, mul_one])
      mul_mem' := fun {k l} hk hl => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k) = φ.1 g := congrFun (congrArg Subtype.val hk) _
        have h2 : φ.1 (g * finGL E a k * finGL E a l) = φ.1 (g * finGL E a k) := congrFun (congrArg Subtype.val hl) _
        change φ.1 (g * finGL E a (k * l)) = φ.1 g
        rw [map_mul, ← mul_assoc, h2, h1])
      inv_mem' := fun {k} hk => Subtype.ext (funext fun g => by
        have h1 : φ.1 (g * finGL E a k⁻¹ * finGL E a k) = φ.1 (g * finGL E a k⁻¹) :=
          congrFun (congrArg Subtype.val hk) _
        change φ.1 (g * finGL E a k⁻¹) = φ.1 g
        rw [← h1, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]) }
  exact Subgroup.isOpen_mono (H₁ := S u) (H₂ := S ⟨_, hm⟩) key hu.2
end

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {G H : Type} [Group G] [Group H]

private def stab (ι : H →* G) (f : G → ℂ) : Subgroup H where
  carrier := {k | ∀ g, f (g * ι k) = f g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * ι k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]

private theorem summ (u : G → ℂ) (hu : HasCompactSupport u) (g : G) : Summable fun γ : Γ => u (γ * g) := by
  have hd : _root_.IsDiscrete (Γ : Set G) := ⟨inferInstanceAs (DiscreteTopology Γ)⟩
  have ht := Subgroup.tendsto_coe_cofinite_of_discrete Γ hd
  have hK : IsCompact ((fun x => x * g⁻¹) '' tsupport u) := IsCompact.image hu (by fun_prop)
  have hf := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hf
  refine summable_of_hasFiniteSupport (hf.subset fun γ hγ => ?_)
  simp only [Set.mem_compl_iff, Set.mem_preimage, not_not]
  exact ⟨γ * g, subset_tsupport _ hγ, by simp⟩

private theorem orb_ne (u : G → ℂ) (hu : HasCompactSupport u) (hp : ∀ g, ∃ t : ℝ, 0 ≤ t ∧ u g = t) (g : G)
    (γ : G) (hγ : γ ∈ Γ) (h : u (γ * g) ≠ 0) : GlobalTheory.AutomorphicL2Unitary.orbitSum Γ u g ≠ 0 := by
  have hs := summ Γ u hu g
  have h0 : ∀ x, 0 ≤ (u x).re := fun x => by
    obtain ⟨t, ht, e⟩ := hp x
    rw [e, Complex.ofReal_re]; exact ht
  have h1 : 0 < (u (γ * g)).re := by
    obtain ⟨t, ht, e⟩ := hp (γ * g)
    rw [e] at h ⊢
    rw [Complex.ofReal_re]
    exact lt_of_le_of_ne ht fun e' => h (by rw [← e', Complex.ofReal_zero])
  intro hz
  have h2 := congrArg Complex.re hz
  rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, Complex.re_tsum hs, Complex.zero_re] at h2
  exact (Summable.tsum_pos (Complex.hasSum_re hs.hasSum).summable (fun δ => h0 _) ⟨γ, hγ⟩ h1).ne' h2

end

private theorem lev_iff {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (φ : Sm E a) :
    HasLev φ ↔ IsOpen (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab (finGL E a) φ.1 : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

open scoped Pointwise in
theorem UpperTheory.V.Cj.H.orbLift :
    UpperTheory.V.Cj.H.OrbLift := by
  intro E _ _ _ a φ hφ hL C hC hs
  obtain ⟨u, hu, hp, hne, -⟩ := testBump E a C Set.univ hC isOpen_univ (Set.subset_univ _)
  obtain ⟨w, hw, ew⟩ := orbSm E a u hu
  have hZ : IsClosed ((latticeGL E a : Set (GA E a)) * C) :=
    by
      set_option synthInstance.maxHeartbeats 200000 in
        exact IsClosed.mul_right_of_isCompact Subgroup.isClosed_of_discrete hC
  have hwZ : ∀ g ∈ (latticeGL E a : Set (GA E a)) * C, w.1 g ≠ 0 := by
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    rw [ew]
    refine orb_ne _ u.1 hu.1 hp _ γ⁻¹ (inv_mem hγ) ?_
    rw [inv_mul_cancel_left]
    exact hne c hc
  have hφZ : ∀ g ∉ (latticeGL E a : Set (GA E a)) * C, φ.1 g = 0 := by
    intro g hg
    by_contra h
    obtain ⟨γ, hγ, hc⟩ := hs g h
    exact hg ⟨γ⁻¹, inv_mem hγ, γ * g, hc, inv_mul_cancel_left γ g⟩
  have hq := (smDiv E a φ u w).2 _ hZ hφZ hwZ
  have hf := (smDiv E a ⟨_, hq⟩ u w).1
  refine ⟨⟨_, hf⟩, ⟨HasCompactSupport.mul_left hu.1, ?_⟩, ?_⟩
  · rw [lev_iff]
    refine Subgroup.isOpen_mono
      (H₁ := stab (finGL E a) φ.1 ⊓ (stab (finGL E a) w.1 ⊓ stab (finGL E a) u.1)) ?_ ?_
    · rintro k ⟨h1, h2, h3⟩ g
      show φ.1 _ / w.1 _ * u.1 _ = φ.1 _ / w.1 _ * u.1 _
      rw [h1 g, h2 g, h3 g]
    · exact ((lev_iff φ).1 hφ).inter (((lev_iff w).1 hw).inter ((lev_iff u).1 hu.2))
  · funext g
    have hwL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) w.1 := ew ▸ GlobalTheory.AutomorphicL2Unitary.leftInv_orbitSum u.1
    have e : GlobalTheory.AutomorphicL2Unitary.orbitSum (latticeGL E a) (fun g => φ.1 g / w.1 g * u.1 g) g = φ.1 g / w.1 g * w.1 g := by
      conv_rhs => rw [congrFun ew g]
      rw [GlobalTheory.AutomorphicL2Unitary.orbitSum, GlobalTheory.AutomorphicL2Unitary.orbitSum, ← tsum_mul_left]
      refine tsum_congr fun γ => ?_
      rw [hL γ γ.2, hwL γ γ.2, congrFun ew g, GlobalTheory.AutomorphicL2Unitary.orbitSum]
    refine Eq.trans ?_ e.symm
    by_cases h : g ∈ (latticeGL E a : Set (GA E a)) * C
    · rw [div_mul_cancel₀ _ (hwZ g h)]
    · rw [hφZ g h, zero_div, zero_mul]
