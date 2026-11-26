module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixedVectorMemLocalModelImage
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixedVectorMemLocalModelImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

namespace GlobalTheory.LocMod.Place

theorem heisO_mem_iSup_range_of_fixed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ c hc g hg hfix hhalf r hr
  classical
  obtain ⟨FT', hFT'⟩ := GlobalTheory.LocMod.Witness.exists_scaled FT (Equiv.refl Y) (fun _ => c) (fun _ => hc)
  have hβ : FT'.β = c • FT.β := by
    ext i j
    simp [hFT']
  have hup : ∀ x, p.up FS FT' x = p.up FS FT (c • x) := by
    intro x
    unfold GlobalTheory.LocMod.Place.up
    rw [hβ, Matrix.smul_mul, Matrix.mul_smul]
  obtain ⟨T₁, hT₁, hT₁Φ⟩ := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT' ψ hψ).2.2 g hg
    (fun x hx => by rw [hup]; exact hfix x hx)
    (fun y hy h => hhalf y hy (fun x hx => by rw [← hup]; exact h x hx))
  let Φ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨_, GlobalTheory.LocMod.Place.intInd_mem_SB k Y Y'⟩
  have hΦ : T₁ Φ = g := hT₁Φ Φ rfl
  have hr' : p.up FS FT' (p.down FS FT' r) = r := GlobalTheory.LocMod.Witness.up_down p FS FT' hr
  let Φ₁ : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ.1 (t + p.down FS FT' r),
    Φ.2.1.comp_continuous (continuous_add_const _), Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have h1 : T₁ Φ₁ = heisO ψ S T r g := by
    rw [hT₁.trans (p.down FS FT' r) Φ Φ₁ (fun t => rfl), hr', hΦ]
  obtain ⟨Tm', hTm', hchg⟩ := GlobalTheory.LocMod.Place.exists_isModel_chg D k p Y Y' S T FS FT' Y Y' FS FT ψ T₁ hT₁
  let e : Matrix Y Y' k ≃ₜ Matrix Y Y' k := Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc)
  let Φ' : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) := ⟨fun t => Φ₁.1 (c⁻¹ • t), Φ₁.2.1.comp_continuous e.continuous, Φ₁.2.2.comp_homeomorph e⟩
  have h2 : Tm' Φ' = T₁ Φ₁ := hchg Φ₁ Φ' (fun x => by
    show Φ₁.1 x = Φ₁.1 (c⁻¹ • (FT.γ * FT'.β * x * (FS.γ * FS.β)))
    rw [hβ, FS.γβ, Matrix.mul_one, Matrix.mul_smul, FT.γβ, Matrix.smul_mul, Matrix.one_mul,
      smul_smul, inv_mul_cancel₀ hc, one_smul])
  rw [← h1, ← h2]
  exact Submodule.mem_iSup_of_mem Tm' (Submodule.mem_iSup_of_mem hTm' (LinearMap.mem_range_self Tm' Φ'))

end GlobalTheory.LocMod.Place
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixedVectorMemLocalModelImageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (c : k), c ≠ 0 → ∀ g, Formalism.IndefR.Datum.IsThetaFunO ψ S T g → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → Formalism.IndefR.Datum.heisO ψ S T (p.up FS FT (c • x)) g = g) → (∀ y : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → ψ (Formalism.IndefR.Datum.symplO S T (p.up FS FT (c • x)) y) = 1) → Formalism.IndefR.Datum.heisO ψ S T y g = g) → ∀ r : Formalism.IndefR.Datum.WO S T, Formalism.IndefR.Datum.IsHalf p.e r → Formalism.IndefR.Datum.heisO ψ S T r g ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  first | exact @GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | exact GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed | (intros; apply GlobalTheory.LocMod.Place.heisO_mem_iSup_range_of_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitRescaledLatticeAndDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitRescaledLatticeAndDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
open Filter Topology

namespace GlobalTheory.LatChoiceSplit

theorem mem_half_iff {D : D7} {S T : HSp D} (e : AE D) (u : WO S T) : u ∈ half S T e ↔ IsHalf e u := by
  change e • u = u ↔ _
  rw [← Matrix.ext_iff]
  rfl

theorem nhdsNE_neBot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem isCompact_int_mat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] : IsCompact {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} = Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_smul_int_mem (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Y Y' : Type) [Fintype Y] [Fintype Y'] (A : Set (Matrix Y Y' k)) (hA : IsOpen A) (h0 : (0 : Matrix Y Y' k) ∈ A) :
    ∃ c : k, c ≠ 0 ∧ ∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → c • x ∈ A := by
  have hev : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}, c • x ∈ A := by
    refine (isCompact_int_mat k Y Y').eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : k × Matrix Y Y' k => z.1 • z.2 := continuous_fst.smul continuous_snd
    have : (fun z : k × Matrix Y Y' k => z.1 • z.2) (0, y) ∈ A := by simpa using h0
    exact hc.continuousAt.preimage_mem_nhds (hA.mem_nhds this)
  haveI := nhdsNE_neBot k
  obtain ⟨c, hc1, hc2⟩ := ((hev.filter_mono (nhdsWithin_le_nhds (s := {(0 : k)}ᶜ))).and (self_mem_nhdsWithin (s := {(0 : k)}ᶜ))).exists
  exact ⟨c, hc2, fun x hx => hc1 x hx⟩

theorem natCast_smul {D : D7} {S T : HSp D} (N : ℕ) (x : WO S T) : (N : AE D) • x = N • x :=
  Nat.cast_smul_eq_nsmul _ _ _

theorem symplO_nsmul_swap {D : D7} (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  rw [← natCast_smul, GlobalTheory.PlaceModel.symplO_smul, map_natCast, natCast_smul]

theorem psi_neg_eq_one {F : Type} [AddGroup F] (ψ : AddChar F ℂ) (z : F) (h : ψ z = 1) : ψ (-z) = 1 := by
  have := AddChar.map_add_eq_mul ψ z (-z)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem nsmul_inv_smul {D : D7} {S T : HSp D} {N : ℕ} (hN : 0 < N) (t : WO S T) :
    N • ((incA D (N : D.host.E)⁻¹) • t) = t := by
  rw [smul_comm]
  exact GlobalTheory.PlaceModel.inv_smul_nsmul S T hN t

theorem isHalf_nsmul {D : D7} {m n : ℕ} {e : AE D} {u : Mx D m n} (h : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  intro i j
  show e * (N • u i j) = N • u i j
  rw [nsmul_eq_mul, mul_left_comm, h i j]

theorem isHalf_smul_idem {D : D7} {m n : ℕ} {e : AE D} (he : e * e = e) (w : AE D) (a : Mx D m n) :
    IsHalf e (w • (e • a)) := by
  intro i j
  show e * (w * (e * a i j)) = w * (e * a i j)
  rw [mul_left_comm, ← mul_assoc e e, he]


open GlobalTheory.LocMod.Witness in
theorem exists_split_lattices : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (U : AddSubgroup (Formalism.IndefR.Datum.WO S T)), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) → ∃ c : k, c ≠ 0 ∧ ∃ L' K : AddSubgroup (Formalism.IndefR.Datum.WO S T), (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → p.up FS FT (c • x) ∈ L' ∧ p.up FS FT (c • x) ∈ U) ∧ (∀ t ∈ L', Formalism.IndefR.Datum.IsHalf p.e t) ∧ (∀ y ∈ K, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y ∧ y ∈ U) ∧ (∃ R : Finset (Formalism.IndefR.Datum.WO S T), ∀ t ∈ L', ∃ r ∈ R, ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ t - r = p.up FS FT (c • x)) ∧ (∀ x ∈ L', ∀ y ∈ K, ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) ∧ (∀ y, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x ∈ L', ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) → y ∈ K) := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ U hU
  classical
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  set Λ₀ := latO S T (GlobalTheory.PlaceModel.latFrame S : Set _) (GlobalTheory.PlaceModel.latFrame T : Set _) (fun _ => True) with hΛ₀
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have he : p.e * p.e = p.e := p.split.1
  have hinfe : infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinfe' : infPart D (cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinfe
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hNk : (N : k) ≠ 0 := by
    intro h0
    have h1 : (N : AE D) * incA D ((N : D.host.E)⁻¹) = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    have h2 := congrArg p.π h1
    rw [map_mul, map_natCast, h0, zero_mul, map_one] at h2
    exact zero_ne_one h2
  obtain ⟨c, hc0, hc⟩ := exists_smul_int_mem k Y Y'
    (((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) ∩ ((U.comap (upH p FS FT) : AddSubgroup _) : Set _))
    ((lat_open p FS FT hS hT).inter (hU.preimage (up_cont p FS FT)))
    ⟨zero_mem (Λ₀.comap (upH p FS FT)), zero_mem (U.comap (upH p FS FT))⟩
  let L' : AddSubgroup (WO S T) := half S T p.e ⊓ Λ₀.comap (nsmulAddMonoidHom N)
  let K : AddSubgroup (WO S T) := (Λ₀ ⊓ half S T (cA D p.e)).map (nsmulAddMonoidHom N)
  have hL' : ∀ t, t ∈ L' ↔ IsHalf p.e t ∧ N • t ∈ Λ₀ := fun t => by
    rw [AddSubgroup.mem_inf, mem_half_iff]; rfl
  have hK : ∀ y, y ∈ K ↔ ∃ b, (b ∈ Λ₀ ∧ IsHalf (cA D p.e) b) ∧ N • b = y := fun y => by
    simp only [K, AddSubgroup.mem_map, AddSubgroup.mem_inf, mem_half_iff, nsmulAddMonoidHom_apply]
  refine ⟨c, hc0, L', K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := hc x hx
    exact ⟨(hL' _).2 ⟨up_half p FS FT _, nsmul_mem (show p.up FS FT (c • x) ∈ Λ₀ from h1) N⟩, h2⟩
  · exact fun t ht => ((hL' t).1 ht).1
  · intro y hy
    obtain ⟨b, ⟨hb1, hb2⟩, rfl⟩ := (hK y).1 hy
    exact ⟨isHalf_nsmul hb2 N, hNU b hb1⟩
  · have hAc := lat_compact p FS FT hS hT
    have hB : IsCompact ((fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k))) :=
      hAc.image (continuous_const_smul _)
    have hint : IsOpen {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} := by
      have : {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]} =
          ⋂ i, ⋂ j, (fun x : Matrix Y Y' k => x i j) ⁻¹' (𝒪[k] : Set k) := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (Valuation.isOpen_integer (v := valuation k)).preimage ((continuous_apply j).comp (continuous_apply i))
    have hVo : IsOpen ((fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]}) :=
      hint.preimage (continuous_const_smul _)
    obtain ⟨G, hG⟩ := compact_covered_by_add_left_translates hB
      (V := (fun m : Matrix Y Y' k => c⁻¹ • m) ⁻¹' {x : Matrix Y Y' k | ∀ i j, x i j ∈ 𝒪[k]})
      ⟨0, by rw [hVo.interior_eq]; intro i j; simp⟩
    refine ⟨G.image (fun g => p.up FS FT (-g)), fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := (hL' t).1 ht
    have hm : N • p.down FS FT t ∈ ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
      change upH p FS FT (N • p.down FS FT t) ∈ Λ₀
      rw [map_nsmul]
      change N • p.up FS FT (p.down FS FT t) ∈ Λ₀
      rw [up_down p FS FT h1]
      exact h2
    have hmB : p.down FS FT t ∈ (fun m => (N : k)⁻¹ • m) '' ((Λ₀.comap (upH p FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) :=
      ⟨_, hm, by simp only; rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hNk, one_smul]⟩
    have hG' := hG hmB
    rw [Set.mem_iUnion₂] at hG'
    obtain ⟨g, hg, hgV⟩ := hG'
    refine ⟨p.up FS FT (-g), Finset.mem_image_of_mem _ hg, c⁻¹ • (g + p.down FS FT t), hgV, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have h3 := up_add p FS FT (-g) (g + p.down FS FT t)
    rw [neg_add_cancel_left, up_down p FS FT h1] at h3
    exact sub_eq_of_eq_add' h3
  · intro x hx y hy
    obtain ⟨h1, h2⟩ := (hL' x).1 hx
    obtain ⟨b, ⟨hb1, -⟩, rfl⟩ := (hK y).1 hy
    rw [← symplO_nsmul_swap]
    have hhalf : IsHalf p.e (N • x) := isHalf_nsmul h1 N
    exact (hdual (N • x) (GlobalTheory.PlaceDatum.infPart_of_half hinfe hhalf)).1 h2 b hb1
  · intro y hy hyL
    obtain ⟨y', hy'h, rfl⟩ := GlobalTheory.PlaceModel.half_div S T (cA D p.e) N hN y ((mem_half_iff _ _).2 hy)
    have hy'h' := (mem_half_iff _ _).1 hy'h
    refine (hK _).2 ⟨y', ⟨?_, hy'h'⟩, rfl⟩
    refine (hdual y' (GlobalTheory.PlaceDatum.infPart_of_half hinfe' hy'h')).2 fun a ha => ?_
    rw [GlobalTheory.PlaceModel.symplO_skew]
    refine psi_neg_eq_one ψ _ ?_
    have hea : p.e • a ∈ Λ₀ := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ p.e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) a ha
    have hNx : N • (incA D ((N : D.host.E)⁻¹) • (p.e • a)) = p.e • a := nsmul_inv_smul hN _
    have hx : incA D ((N : D.host.E)⁻¹) • (p.e • a) ∈ L' := by
      exact (hL' _).2 ⟨isHalf_smul_idem he _ a, by rw [hNx]; exact hea⟩
    have h4 := hyL _ hx
    rw [← symplO_nsmul_swap, hNx, GlobalTheory.PlaceModel.symplO_smul] at h4
    have hcy : cA D p.e • y' = y' := hy'h
    rwa [hcy] at h4

end GlobalTheory.LatChoiceSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitRescaledLatticeAndDualStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_rescaled_lattice_and_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (U : AddSubgroup (Formalism.IndefR.Datum.WO S T)), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) → ∃ c : k, c ≠ 0 ∧ ∃ L' K : AddSubgroup (Formalism.IndefR.Datum.WO S T), (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → p.up FS FT (c • x) ∈ L' ∧ p.up FS FT (c • x) ∈ U) ∧ (∀ t ∈ L', Formalism.IndefR.Datum.IsHalf p.e t) ∧ (∀ y ∈ K, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y ∧ y ∈ U) ∧ (∃ R : Finset (Formalism.IndefR.Datum.WO S T), ∀ t ∈ L', ∃ r ∈ R, ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ t - r = p.up FS FT (c • x)) ∧ (∀ x ∈ L', ∀ y ∈ K, ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) ∧ (∀ y, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x ∈ L', ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) → y ∈ K) := by
  first | exact @GlobalTheory.LatChoiceSplit.exists_split_lattices | exact GlobalTheory.LatChoiceSplit.exists_split_lattices | (intros; apply GlobalTheory.LatChoiceSplit.exists_split_lattices <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLatticeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLattice
noncomputable section

namespace GlobalTheory.FourierSpan

variable {G : Type} [AddCommGroup G]

def annihIn (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (Yh L : AddSubgroup G) : AddSubgroup G where
  carrier := {y | y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1}
  add_mem' := fun {a b} ha hb => ⟨Yh.add_mem ha.1 hb.1, fun x hx => by rw [hχ.right, ha.2 x hx, hb.2 x hx, one_mul]⟩
  zero_mem' := ⟨Yh.zero_mem, fun x _ => hχ.zero_right x⟩
  neg_mem' := fun {a} ha => ⟨Yh.neg_mem ha.1, fun x hx => by
    have e : χ x (-a) * χ x a = 1 := by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
    rwa [ha.2 x hx, mul_one] at e⟩

theorem bichar_pow_left {χ : G → G → ℂ} (hχ : GlobalTheory.PlaceModel.IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [hχ.zero_left]
  | succ k ih => rw [succ_nsmul, hχ.left, ih, pow_succ]

theorem mem_span_translates_of_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G)
    (hLL' : L ≤ L') (hL'X : L' ≤ X) (hKY : K ≤ Yh) (ρ0 : ∀ v, ρ 0 v = v)
    (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v)
    (ρY : ∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v))
    (hR : ∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L)
    (hLK : ∀ x ∈ L', ∀ y ∈ K, χ x y = 1)
    (hsep : ∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K)
    (W : Submodule ℂ V) (hWX : ∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) (hWY : ∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W)
    (f : V) (hfW : f ∈ W) (hfL : ∀ x ∈ L, ρ x f = f) (hfK : ∀ y ∈ K, ρ y f = f) :
    f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧
      (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  classical
  obtain ⟨R, hR⟩ := hR
  have negR : ∀ x y, χ x (-y) * χ x y = 1 := fun x y => by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
  set P := annihIn χ hχ Yh L with hPdef
  have memP : ∀ y, y ∈ P ↔ y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1 := fun y => Iff.rfl
  have hPY : ∀ y ∈ P, y ∈ Yh := fun y hy => ((memP y).1 hy).1
  have hKP : K ≤ P := fun y hy => (memP y).2 ⟨hKY hy, fun x hx => hLK x (hLL' hx) y hy⟩

  have wdQ : ∀ y ∈ P, ∀ u v : L', (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = QuotientAddGroup.mk v →
      χ u y = χ v y := by
    intro y hy u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : L') : G) := by simp
    rw [e, hχ.left, ((memP y).1 hy).2 _ huv, mul_one]
  have wdQ' : ∀ h : V, (∀ k ∈ K, ρ k h = h) → ∀ u v : P,
      (QuotientAddGroup.mk u : P ⧸ K.addSubgroupOf P) = QuotientAddGroup.mk v → ρ u h = ρ v h := by
    intro h hh u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : P) : G) := by simp
    rw [e, ← ρY _ (hPY _ u.2) _ (hKY huv), hh _ huv]

  have finQ : Finite (L' ⧸ L.addSubgroupOf L') := by
    let φ : R → L' ⧸ L.addSubgroupOf L' := fun r =>
      if h : (r : G) ∈ L' then QuotientAddGroup.mk ⟨r, h⟩ else 0
    refine Finite.of_surjective φ ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, htr⟩ := hR t t.2
    have hrL' : r ∈ L' := by
      have := L'.sub_mem t.2 (hLL' htr)
      simpa using this
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [φ, dif_pos hrL']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    convert htr using 1
    simp only
    abel
  letI : Fintype (L' ⧸ L.addSubgroupOf L') := Fintype.ofFinite _
  set n := Fintype.card (L' ⧸ L.addSubgroupOf L') with hn_def
  have hn : 0 < n := Fintype.card_pos
  have powQ : ∀ y ∈ P, ∀ u : L', χ u y ^ n = 1 := by
    intro y hy u
    have hnu : ((n • u : L') : G) ∈ L := by
      have h0 : n • (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = 0 := card_nsmul_eq_zero
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
      exact h0
    rw [← bichar_pow_left hχ, ← AddSubgroup.coe_nsmul]
    exact ((memP y).1 hy).2 _ hnu

  have finS : ({z : ℂ | z ^ n = 1} : Set ℂ).Finite :=
    (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hn).2 hz
  haveI := finS.to_subtype
  have finQ' : Finite (P ⧸ K.addSubgroupOf P) := by
    let Φ : (P ⧸ K.addSubgroupOf P) → ((L' ⧸ L.addSubgroupOf L') → ({z : ℂ | z ^ n = 1} : Set ℂ)) :=
      fun q' q => ⟨χ (q.out : L') (q'.out : P), powQ _ (q'.out).2 _⟩
    refine Finite.of_injective Φ ?_
    intro a b hab
    rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hsep _ (hPY _ (-a.out + b.out : P).2) fun x hx => ?_
    have e := congrArg Subtype.val (congrFun hab (QuotientAddGroup.mk ⟨x, hx⟩))
    simp only [Φ] at e
    have ea := wdQ _ (a.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    have eb := wdQ _ (b.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    rw [ea, eb] at e
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hχ.right, ← e]
    exact negR _ _
  letI : Fintype (P ⧸ K.addSubgroupOf P) := Fintype.ofFinite _

  have hKh : ∀ r ∈ L', ∀ k ∈ K, ρ k (ρ (-r) f) = ρ (-r) f := by
    intro r hr k hk
    have := ρXY (-r) (X.neg_mem (hL'X hr)) k (hKY hk) f
    rw [hfK k hk, hLK _ (L'.neg_mem hr) k hk, one_smul] at this
    exact this.symm
  let g : (L' ⧸ L.addSubgroupOf L') → V := fun q =>
    ∑ q' : P ⧸ K.addSubgroupOf P, ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)
  have gW : ∀ q, g q ∈ W := fun q => Submodule.sum_mem _ fun q' _ =>
    hWY _ (hWX f hfW _ (X.neg_mem (hL'X (q.out).2))) _ (hPY _ (q'.out).2)
  have gL : ∀ q, ∀ x ∈ L, ρ x (g q) = g q := by
    intro q x hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, map_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    have hxX : x ∈ X := hL'X (hLL' hx)
    have hrX : -((q.out : L') : G) ∈ X := X.neg_mem (hL'X (q.out).2)
    rw [ρXY x hxX _ (hPY _ (q'.out).2), ((memP _).1 (q'.out).2).2 x hx, one_smul, ρX x hxX _ hrX, add_comm,
      ← ρX _ hrX _ hxX, hfL x hx]
  have gP : ∀ q, ∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y (g q) = g q := by
    intro q y hy hyL
    have hyP : y ∈ P := (memP y).2 ⟨hy, hyL⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, map_sum]
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨y, hyP⟩ : P ⧸ K.addSubgroupOf P))
      (fun q' : P ⧸ K.addSubgroupOf P => ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)))
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [Equiv.coe_addRight]
    rw [ρY y hy _ (hPY _ (q'.out).2), ← wdQ' _ (hKh _ (q.out).2) (q'.out + ⟨y, hyP⟩) _ ?_]
    · rw [AddSubgroup.coe_add, add_comm]
    · rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  have key : ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) = (n : ℂ) • f := by
    have step : ∀ q : L' ⧸ L.addSubgroupOf L', ∀ q' : P ⧸ K.addSubgroupOf P,
        ρ ((q.out : L') : G) (ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)) =
          χ ((q.out : L') : G) ((q'.out : P) : G) • ρ ((q'.out : P) : G) f := by
      intro q q'
      have hrX := hL'X (q.out).2
      rw [ρXY _ hrX _ (hPY _ (q'.out).2), ρX _ hrX _ (X.neg_mem hrX), add_neg_cancel, ρ0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, map_sum, step]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : P ⧸ K.addSubgroupOf P)]
    · have h0K : (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) ∈ K := by
        have := QuotientAddGroup.out_eq' (0 : P ⧸ K.addSubgroupOf P)
        rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this
        exact this
      have h1 : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ ((q.out : L') : G) (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) = 1 :=
        fun q => hLK _ (q.out).2 _ h0K
      rw [hfK _ h0K]
      simp only [h1, Finset.sum_const, Finset.card_univ, ← hn_def, nsmul_eq_mul, mul_one]
    · intro q' _ hq'
      have hnK : ((q'.out : P) : G) ∉ K := by
        intro hK
        apply hq'
        rw [← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        exact hK
      obtain ⟨x, hx, hxy⟩ : ∃ x ∈ L', χ x ((q'.out : P) : G) ≠ 1 := by
        by_contra hc
        push_neg at hc
        exact hnK (hsep _ (hPY _ (q'.out).2) hc)
      have hyP := (q'.out).2
      have shift : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ (((q + (QuotientAddGroup.mk (⟨x, hx⟩ : L') : L' ⧸ L.addSubgroupOf L')).out : L') : G) ((q'.out : P) : G) =
            χ ((q.out : L') : G) ((q'.out : P) : G) * χ x ((q'.out : P) : G) := by
        intro q
        rw [← wdQ _ hyP (q.out + (⟨x, hx⟩ : L')) _ ?_, AddSubgroup.coe_add, hχ.left]
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have hS2 := Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L'))
        (fun q : L' ⧸ L.addSubgroupOf L' => χ ((q.out : L') : G) ((q'.out : P) : G))
      simp only [Equiv.coe_addRight, shift, ← Finset.sum_mul] at hS2
      have hsum : ∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G) = 0 := by
        have h3 : (∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G)) *
            (χ x ((q'.out : P) : G) - 1) = 0 := by
          rw [mul_sub, hS2, mul_one, sub_self]
        exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hxy)
      rw [hsum, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hf : f = (n : ℂ)⁻¹ • ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) := by
    rw [key, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [hf]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_)
  exact ⟨_, hL'X (q.out).2, g q, gW q, gL q, gP q, rfl⟩
end GlobalTheory.FourierSpan
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_of_fixed_lattice : ∀ {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G), L ≤ L' → L' ≤ X → K ≤ Yh → (∀ v, ρ 0 v = v) → (∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v) → (∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v) → (∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v)) → (∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L) → (∀ x ∈ L', ∀ y ∈ K, χ x y = 1) → (∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K) → ∀ (W : Submodule ℂ V), (∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) → (∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W) → ∀ f ∈ W, (∀ x ∈ L, ρ x f = f) → (∀ y ∈ K, ρ y f = f) → f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧ (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  first | exact @GlobalTheory.FourierSpan.mem_span_translates_of_fixed | exact GlobalTheory.FourierSpan.mem_span_translates_of_fixed | (intros; apply GlobalTheory.FourierSpan.mem_span_translates_of_fixed <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
namespace GlobalTheory.LocMod.SpanModels

theorem mem_iSup_range_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ S T f → f ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ f hf
  classical
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨c, hc, L', K, hL, hL'e, hK, ⟨R, hR⟩, hL'K, hsep⟩ := GlobalTheory.T.exists_split_rescaled_lattice_and_dual D k p Y Y' S T FS FT ψ hψ U hUo
  have hinf : Formalism.L2.Theta.infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinf' : Formalism.L2.Theta.infPart D (Formalism.L2.Theta.cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hec : p.e * Formalism.L2.Theta.cA D p.e = 0 := p.split.2.1
  let I : AddSubgroup (Matrix Y Y' k) :=
    { carrier := {x | ∀ i j, x i j ∈ 𝒪[k]}
      add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
      zero_mem' := fun i j => zero_mem _
      neg_mem' := fun ha i j => neg_mem (ha i j) }
  let L : AddSubgroup (Formalism.IndefR.Datum.WO S T) :=
    I.map ((Witness.upH p FS FT).comp (DistribSMul.toAddMonoidHom (Matrix Y Y' k) c))
  have memL : ∀ t, t ∈ L ↔ ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ p.up FS FT (c • x) = t := fun t => Iff.rfl
  let W : Submodule ℂ (Formalism.IndefR.Datum.WO S T → ℂ) :=
    { carrier := {g | Formalism.IndefR.Datum.IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb
      zero_mem' := GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
      smul_mem' := fun c _ hg => GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hg }
  have key := GlobalTheory.T.mem_span_translates_of_fixed_lattice (fun x y => ψ (Formalism.IndefR.Datum.symplO S T x y)) (isBichar_symplO S T ψ) (heisL S T ψ)
    (half S T p.e) (half S T (Formalism.L2.Theta.cA D p.e)) L L' K
    (by rintro _ ⟨x, hx, rfl⟩; exact (hL x hx).1)
    (fun t ht => (isHalf_iff S T).1 (hL'e t ht))
    (fun y hy => (isHalf_iff S T).1 (hK y hy).1)
    (fun v => by
      funext w
      change ψ (Formalism.IndefR.Datum.symplOH S T w 0) * v (w + 0) = v w
      simp [Formalism.IndefR.Datum.symplOH, symplO_zero_right])
    (fun x hx x' hx' v => heisL_half S T ψ (by rw [mul_comm]; exact hec) x hx x' hx' v)
    (fun y hy y' hy' v => heisL_half S T ψ (by rw [Formalism.L2.Theta.cA_cA, hec]) y hy y' hy' v)
    (fun x _ y _ v => heisL_comm S T ψ x y v)
    ⟨R, fun t ht => by
      obtain ⟨r, hr, x, hx, e⟩ := hR t ht
      exact ⟨r, hr, x, hx, e.symm⟩⟩
    hL'K (fun y hy h => hsep y ((isHalf_iff S T).2 hy) h) W
    (fun v hv x _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv x)
    (fun v hv y _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv y)
    f hf
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hUf _ (hL x hx).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf (Witness.up_half p FS FT _)))
    (fun y hy => hUf y (hK y hy).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf' (hK y hy).1))
  refine Submodule.span_le.2 ?_ key
  rintro _ ⟨r, hr, g, hg, hgL, hgY, rfl⟩
  exact GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage D k p Y Y' S T FS FT ψ hψ c hc g hg (fun x hx => hgL _ ⟨x, hx, rfl⟩)
    (fun y hy hyL => hgY y ((isHalf_iff S T).1 hy) (by rintro _ ⟨x, hx, rfl⟩; exact hyL x hx)) r ((isHalf_iff S T).2 hr)

end GlobalTheory.LocMod.SpanModels
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionMemSpanLocalSchrodingerModelsSplitStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ S T f → f ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  first | exact @GlobalTheory.LocMod.SpanModels.mem_iSup_range_isModel | exact GlobalTheory.LocMod.SpanModels.mem_iSup_range_isModel | (intros; apply GlobalTheory.LocMod.SpanModels.mem_iSup_range_isModel <;> assumption)
end
