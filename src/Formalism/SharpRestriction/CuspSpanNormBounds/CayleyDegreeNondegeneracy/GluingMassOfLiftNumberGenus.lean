module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyStatementOfAbsAndVandermonde
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeStructureOfDet
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.AutomorphismsOfLiftTransitivity
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FlagStabilizerMemIsotropic
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatticeClassesOfLiftTransitivity
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsDecompOrthIsotropicPlus
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he in
theorem isotropic_le_orth_range : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  rw [he]
  change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  exact (D.sp.hyp_orthX a w).1

include hz in
theorem z_mem_orth_range : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  rw [hz]
  exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)


include hT he hz in
theorem exists_decomp_orth_isotropic_plus (x : (VS D).V) (hx : x ∈ orth (hS D) F0.Xplus) :
    ∃ w, x - D.sp.iXY 0 w ∈ F0.X := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hx' : x ∈ Wsp D ⊔ Xsp (lf D F0) := by rw [hW]; exact hx
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨w, by simpa using hξ⟩


include hT he hz in
theorem exists_decomp_orth_isotropic (x : (VS D).V) (hx : x ∈ orth (hS D) F0.X) :
    ∃ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X := by
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  obtain ⟨w, hw⟩ := exists_decomp_orth_isotropic_plus D u hT F0 he hz
    (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by
      rw [Formalism.MainNotions.mem_orth_iff]
      refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
      · rw [map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]
        exact hx' _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [map_sub, map_smul, F0.z_norm, smul_eq_mul]
        field_simp
        ring)
  refine ⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩
  rw [add_comm, ← sub_sub]
  exact hw


include hT he hz in
theorem Lsub_eq_of_latticeWithZ_eq (Λ₁ Λ₂ : LatV D) (h : latticeWithZ D F0 Λ₁ = latticeWithZ D F0 Λ₂) :
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) := by
  have key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔
      x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E),
        x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ := by
    intro Λ x
    have hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0) := by
      intro w c
      unfold latticeWithZ
      rw [Submodule.mem_comap]
      simp [embedWithZ]
    constructor
    · intro hx
      refine ⟨hx.2, fun w c hξ => ?_⟩
      rw [hj]
      have := (Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
    · rintro ⟨hxO, hall⟩
      obtain ⟨w, c, hξ⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x hxO
      have h1 := (hj w c).1 (hall w c hξ)
      have := (Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
  ext x
  rw [key Λ₁, key Λ₂, h]

def projWAlt : (VS D).V →ₗ[D.host.E] (D.sp.X 0).V :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm.toLinearMap ∘ₗ LinearMap.fst D.host.E _ _ ∘ₗ
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm.toLinearMap

theorem projW_apply (w : (D.sp.X 0).V) (b : (VS D).V) (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    projWAlt D (D.sp.iXY 0 w + b) = w := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold projWAlt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]


include hT he hz in
theorem exists_induced_isometry_W (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    ∃ γ ∈ isom (D.sp.X 0).hT, ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ.1
  have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
    have := hσ.2.1 D.R.rS
    rwa [partial_isotropic_top] at this
  have hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus := by
    unfold FlagG.Xplus
    rw [Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]
    congr 3
    exact hσ.2.2
  have hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus := by
    intro w
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    have : D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0) := Submodule.mem_sup_left ⟨w, rfl⟩
    rw [hW] at this
    exact this
  have hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X := by
    intro w
    refine exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_
    rw [Formalism.MainNotions.mem_orth_iff]
    intro x hx
    rw [← hXp] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    change (VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0
    rw [hσ']
    exact (Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'
  let γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0
  have hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X := by
    intro w
    obtain ⟨w', hw'⟩ := hdec w
    have e : γ0 w = w' := by
      change projWAlt D (σ (D.sp.iXY 0 w)) = w'
      have : σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w') := by abel
      rw [this]
      exact projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')
    rw [e]
    exact hw'
  have hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w' := by
    intro w w'
    have e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w)) := by abel
    have e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w')) := by abel
    have h1 := hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')
    rw [e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w))
      (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W,
      (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero] at h1
    exact h1
  have hinj : Function.Injective γ0 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  refine ⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩
  · simpa using hiso w w'
  · simpa using hγ0 w

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_latticeWithZ_iff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (Λ : LatV D) (w : (D.sp.X 0).V) (c : D.host.E) :
    (w, c) ∈ latticeWithZ D F Λ ↔ D.sp.iXY 0 w + c • F.z ∈ Lsub Λ (lf D F) := by
  unfold latticeWithZ
  rw [Submodule.mem_comap]
  simp [embedWithZ]

include he hz in
theorem extendByIdentity_mem_flag_stabilizer (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) :
    extendByIdentity D γ ∈ stabF D F0 := by
  have hfix : ∀ y ∈ F0.X, (extendByIdentity D γ).symm y = y :=
    fun y hy => extendByIdentity_symm_fix_orth D γ y (isotropic_le_orth_range D u F0 he hy)
  refine ⟨extendByIdentity_mem_isom D γ hγ, fun j => ?_, ?_⟩
  · ext x
    rw [Submodule.mem_map_equiv]
    constructor
    · intro h
      have e : (extendByIdentity D γ).symm x = x := (extendByIdentity D γ).symm.injective (hfix _ (partial_isotropic_le F0 j h))
      rwa [e] at h
    · intro h
      rw [hfix x (partial_isotropic_le F0 j h)]
      exact h
  · rw [← LinearEquiv.eq_symm_apply]
    exact (extendByIdentity_symm_fix_orth D γ _ (z_mem_orth_range D u F0 hz)).symm


include he hz in
theorem transport_isLattice_latticeWithZ (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hγ : γ ∈ isom (D.sp.X 0).hT) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap (extendByIdentity D γ) Λ) ∧
      latticeWithZ D F0 (gmap (extendByIdentity D γ) Λ) = gmap (extendByOne D γ) (latticeWithZ D F0 Λ) := by
  have hzO := z_mem_orth_range D u F0 hz
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (isotropic_le_orth_range D u F0 he hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ hΛ
  refine ⟨hrow, ?_⟩
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLsub, isomAct_mem_gmap,
    extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem lattice_classes_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : LatticeClassesIff D u := by
  intro hTp hT3 hsp F0 he hz Λ₁ Λ₂ h₁ h₂
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨γ, hγ, ?_⟩
    have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      have := hσ.2.1 D.R.rS
      rwa [partial_isotropic_top] at this
    have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ₁
    ext ⟨w, c⟩
    have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
    have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
      have h1 := hind (γ.symm w)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
        rw [← Submodule.mem_map_equiv, hX]
        exact h1
      have hzs : σ.symm F0.z = F0.z := by
        rw [LinearEquiv.symm_apply_eq]
        exact hσ.2.2.symm
      have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
          -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
        rw [map_add (f := _), map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
        abel
      rw [e3]
      exact F0.X.neg_mem h2
    have hd' := isotropic_le_Lsub F0 Λ₁ hd
    constructor
    · intro ha
      have := (Lsub Λ₁ (lf D F0)).add_mem ha hd'
      simpa using this
    · intro hb
      have := (Lsub Λ₁ (lf D F0)).sub_mem hb hd'
      simpa using this
  · rintro ⟨γ, hγ, hγe⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ₁ h₁
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγe)
    obtain ⟨n, hn, _, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow h₂ hLs
    exact ⟨n * extendByIdentity D γ, mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ), by rw [gmap_mul, hne]⟩

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Aut

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

theorem mem_perpS_iff_mem_orth (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ y ∈ orth (hS D) F0.X := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rfl

theorem flag_stabilizer_map_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
  have := hσ.2.1 D.R.rS
  rwa [partial_isotropic_top] at this

theorem flag_stabilizer_mem_isotropic (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (x : (VS D).V) (hx : x ∈ F0.X) :
    σ x ∈ F0.X := by
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ]
  exact ⟨x, hx, rfl⟩

theorem flag_stabilizer_mem_perp (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) (y : (VS D).V)
    (hy : y ∈ perpS (VS D) F0.X) : σ y ∈ perpS (VS D) F0.X := by
  intro x hx
  rw [← flag_stabilizer_map_isotropic D u F0 σ hσ] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  change (VS D).hT (σ x') (σ y) = 0
  rw [hσ.1 x' y]
  exact hy x' hx'

include he in
theorem embedding_add_smul_z_mem_perp (w : (D.sp.X 0).V) (c : D.host.E) : D.sp.iXY 0 w + c • F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  have h1 : (VS D).hT x (D.sp.iXY 0 w) = 0 :=
    Formalism.MainNotions.hT_swap_zero ((Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_range D u F0 he hx) _ ⟨w, rfl⟩)
  have h2 : (VS D).hT x F0.z = 0 := Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth x hx
  rw [map_add (f := _), map_smul, h1, h2, smul_zero, add_zero]

def quotientClass (w : (D.sp.X 0).V) (c : D.host.E) : WbQ D F0 :=
  Submodule.Quotient.mk ⟨D.sp.iXY 0 w + c • F0.z, embedding_add_smul_z_mem_perp D u F0 he w c⟩

include hT hz in
theorem quotientClass_surjective (q : WbQ D F0) : ∃ w c, q = quotientClass D u F0 he w c := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨w, c, h⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x.1 ((mem_perpS_iff_mem_orth D u F0 _).1 x.2)
  refine ⟨w, c, ?_⟩
  unfold quotientClass
  rw [Submodule.Quotient.eq]
  exact h

include hT hz in
theorem quotientClass_injective_left {w w' : (D.sp.X 0).V} {c c' : D.host.E} (h : quotientClass D u F0 he w c = quotientClass D u F0 he w' c') :
    w = w' := by
  unfold quotientClass at h
  rw [Submodule.Quotient.eq] at h
  have h' : D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z) ∈ F0.X := h
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hzW : ∀ v, (VS D).hT F0.z (D.sp.iXY 0 v) = 0 := fun v => by rw [hz]; exact z_orth_embedding D u v
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c' • F0.z)) = 0 :=
    Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 F0.z_orth _ h')
  have hc : c = c' := by
    simp only [map_sub, map_add (f := _), map_smul, hzW, F0.z_norm, smul_eq_mul, zero_add] at h0
    have : (c - c') * ((Tu D u : ℕ) : D.host.E) = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hT'
  subst hc
  have h2 : D.sp.iXY 0 (w - w') ∈ Wsp D ⊓ Xsp (lf D F0) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    have e : D.sp.iXY 0 (w - w') = D.sp.iXY 0 w + c • F0.z - (D.sp.iXY 0 w' + c • F0.z) := by
      rw [map_sub]; abel
    rw [e]
    exact h'
  rw [(Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).2.1, Submodule.mem_bot] at h2
  exact sub_eq_zero.1 (embedding_W_injective D (by rw [h2, map_zero]))

def ActsAsExtendByOne (φ : WbQ D F0 → WbQ D F0) (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w c, φ (quotientClass D u F0 he w c) = quotientClass D u F0 he (γ w) c

theorem actsAsExtendByOne_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (φ : WbQ D F0 → WbQ D F0)
    (hφ : ∀ (x : perpS (VS D) F0.X) (hx : σ x.1 ∈ perpS (VS D) F0.X),
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨σ x.1, hx⟩) : ActsAsExtendByOne D u F0 he φ γ := by
  intro w c
  unfold quotientClass
  rw [hφ _ (flag_stabilizer_mem_perp D u F0 σ hσ _ (embedding_add_smul_z_mem_perp D u F0 he w c)), Submodule.Quotient.eq]
  change σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) ∈ F0.X
  have e : σ (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ w) + c • F0.z) = σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) := by
    rw [map_add (f := _), map_smul, hσ.2.2]
    abel
  rw [e]
  exact hind w

theorem gmap_latticeWithZ_of_induced (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0)
    (γ : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) (hind : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X)
    (Λ : LatV D) : gmap (extendByOne D γ) (latticeWithZ D F0 Λ) = latticeWithZ D F0 (gmap σ Λ) := by
  have hX := flag_stabilizer_map_isotropic D u F0 σ hσ
  have hLs := Lsub_gmap_of_isometry F0 σ hσ.1 hX Λ
  ext ⟨w, c⟩
  have e : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
  rw [isomAct_mem_gmap, e, mem_latticeWithZ_iff, mem_latticeWithZ_iff, hLs, isomAct_mem_gmap]
  have hd : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) ∈ F0.X := by
    have h1 := hind (γ.symm w)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w) ∈ F0.X := by
      rw [← Submodule.mem_map_equiv, hX]
      exact h1
    have hzs : σ.symm F0.z = F0.z := by
      rw [LinearEquiv.symm_apply_eq]
      exact hσ.2.2.symm
    have e3 : σ.symm (D.sp.iXY 0 w + c • F0.z) - (D.sp.iXY 0 (γ.symm w) + c • F0.z) =
        -(σ.symm (σ (D.sp.iXY 0 (γ.symm w)) - D.sp.iXY 0 w)) := by
      rw [map_add (f := _), map_smul, hzs, map_sub, LinearEquiv.symm_apply_apply]
      abel
    rw [e3]
    exact F0.X.neg_mem h2
  have hd' := isotropic_le_Lsub F0 Λ hd
  constructor
  · intro ha
    have := (Lsub Λ (lf D F0)).add_mem ha hd'
    simpa using this
  · intro hb
    have := (Lsub Λ (lf D F0)).sub_mem hb hd'
    simpa using this

end Aut

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u : D.what₂.Word)

theorem automorphisms_of_lift_transitivity (hL : LiftsConjugateUnderStabilizer D u) : CardAutEqCardIsometryStabilizer D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ
  have hT : Tu D u ≠ 0 := hTp.ne_zero
  have hD : ∀ φ : autLz D F0 Λ,
      ∃ γ : {γ : isom (D.sp.X 0).hT // gmap (extendByOne D γ.1) (latticeWithZ D F0 Λ) = latticeWithZ D F0 Λ},
        ActsAsExtendByOne D u F0 he φ.1 γ.1.1 := by
    rintro ⟨φ, σ, hσ, hσΛ, hφ⟩
    obtain ⟨γ, hγ, hind⟩ := exists_induced_isometry_W D u hT F0 he hz σ hσ
    refine ⟨⟨⟨γ, hγ⟩, ?_⟩, actsAsExtendByOne_of_induced D u F0 he σ hσ γ hind φ hφ⟩
    rw [gmap_latticeWithZ_of_induced D u F0 σ hσ γ hind Λ, hσΛ]
  choose f hf using hD
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro φ₁ φ₂ h12
    apply Subtype.ext
    funext q
    obtain ⟨w, c, rfl⟩ := quotientClass_surjective D u hT F0 he hz q
    rw [hf φ₁ w c, hf φ₂ w c, h12]
  · rintro ⟨⟨γ, hγ⟩, hγΛ⟩
    obtain ⟨hrow, hLd⟩ := transport_isLattice_latticeWithZ D u F0 he hz γ hγ Λ hΛ
    have hLs := Lsub_eq_of_latticeWithZ_eq D u hT F0 he hz _ _ (hLd.trans hγΛ)
    obtain ⟨n, hn, hnX, hne⟩ := hL hTp hT3 hsp F0 he hz _ _ hrow hΛ hLs
    have hσ : n * extendByIdentity D γ ∈ stabF D F0 := mul_mem_flag_stabilizer F0 hn (extendByIdentity_mem_flag_stabilizer D u F0 he hz γ hγ)
    have hσΛ : gmap (n * extendByIdentity D γ) Λ = Λ := by rw [gmap_mul, hne]
    have hind : ∀ w, (n * extendByIdentity D γ) (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
      intro w
      change n (extendByIdentity D γ (D.sp.iXY 0 w)) - _ ∈ _
      have e : extendByIdentity D γ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ w) := by
        simpa using extendByIdentity_apply D γ w 0 (Submodule.zero_mem _)
      rw [e]
      refine hnX _ ((mem_perpS_iff_mem_orth D u F0 _).1 ?_)
      simpa using embedding_add_smul_z_mem_perp D u F0 he (γ w) 0
    let φ : WbQ D F0 → WbQ D F0 := Submodule.mapQ (F0.X.comap (perpS (VS D) F0.X).subtype) (F0.X.comap (perpS (VS D) F0.X).subtype)
      (((n * extendByIdentity D γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrict
        (fun x hx => flag_stabilizer_mem_perp D u F0 _ hσ x hx))
      (fun x hx => flag_stabilizer_mem_isotropic D u F0 _ hσ x.1 hx)
    have hφ : ∀ (x : perpS (VS D) F0.X) (hx : (n * extendByIdentity D γ) x.1 ∈ perpS (VS D) F0.X),
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(n * extendByIdentity D γ) x.1, hx⟩ := fun _ _ => rfl
    refine ⟨⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    have h1 := hf ⟨φ, n * extendByIdentity D γ, hσ, hσΛ, hφ⟩ w 0
    have h2 := actsAsExtendByOne_of_induced D u F0 he _ hσ γ hind φ hφ w 0
    exact quotientClass_injective_left D u hT F0 he hz (h1.symm.trans h2)

theorem gluing_mass_of_lift_transitivity (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingCount D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_iso_aut_count_genus D u hpos hlat (lattice_classes_of_lift_transitivity D u hL) (automorphisms_of_lift_transitivity D u hL) h4 h5

def GluingNumber : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ M ∈ genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    {𝓛 | (∃ Λ', IsRowLat D F0 Λ' ∧ latticeWithZ D F0 Λ' = 𝓛) ∧ intersectFirstSummand D 𝓛 = M}.ncard = (Tu D u - 1) ^ D.R.f

theorem gluing_count_of_gluing_number (h : GluingNumber D u) : GluingCount D u := by
  intro hTp hT3 hsp F0 he hz Λ hΛ M hM
  have h1 := h hTp hT3 hsp F0 he hz Λ hΛ M hM
  refine ⟨Set.finite_of_ncard_ne_zero ?_, h1⟩
  have h2 : (Tu D u - 1) ^ D.R.f ≠ 0 := pow_ne_zero _ (by omega)
  intro h0
  exact h2 (h1.symm.trans h0)

theorem gluing_mass_of_lift_and_number (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u) (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_lift_transitivity D u hpos hlat hL (gluing_count_of_gluing_number D u h4) h5

end Formalism.MainNotions.BridgeLemma₂

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassLowerBoundOfMassFormula
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.LatticeGluingRadicals

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem exists_not_mem_mul_mem_span {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    ∃ c : 𝓞 E, c ∉ P ∧ ∀ x ∈ P, c * x ∈ Ideal.span {t} := by
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ht
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    have h2 : Ideal.span {t} ≤ P ^ 2 := by
      rw [hI, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span (Set.mem_singleton t))
  obtain ⟨c, hcI, hcP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨c, hcP, fun x hx => ?_⟩
  rw [hI, mul_comm c x]
  exact Ideal.mul_mem_mul hx hcI

def quotientSpanToQuotientPrime (P : Ideal (𝓞 E)) (t : 𝓞 E) (ht : t ∈ P) : (𝓞 E ⧸ Ideal.span {t}) →ₗ[𝓞 E] (𝓞 E ⧸ P) :=
  Submodule.mapQ (Ideal.span {t}) P LinearMap.id ((Ideal.span_singleton_le_iff_mem _).2 ht)

theorem isLocalizedModule_quotient_prime {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    haveI := hP.isPrime
    IsLocalizedModule P.primeCompl (quotientSpanToQuotientPrime P t ht) := by
  constructor
  · intro s
    have hs : (s : 𝓞 E) ∉ P := s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro y1 y2 h
      obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective P y1
      obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective P y2
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
      rw [← smul_sub, smul_eq_mul] at h
      exact (hP.isPrime.mem_or_mem h).resolve_left hs
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
      obtain ⟨b, i, hi, hb⟩ := hP.exists_inv hs
      refine ⟨Submodule.Quotient.mk (b * a), ?_⟩
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : (s : 𝓞 E) * (b * a) - a = -(i * a) := by linear_combination a * hb
      rw [e]
      exact P.neg_mem (P.mul_mem_right a hi)
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
    exact ⟨(Submodule.Quotient.mk a, 1), by simp [quotientSpanToQuotientPrime]⟩
  · intro x1 x2 h
    obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective _ x1
    obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    simp only [quotientSpanToQuotientPrime, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq] at h
    obtain ⟨c, hcP, hc⟩ := exists_not_mem_mul_mem_span hP ht ht2
    refine ⟨⟨c, hcP⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← smul_sub, smul_eq_mul]
    exact hc _ h

end Loc

section Idx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem localLength_cyclic_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) (hP : P.IsMaximal) (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : haveI := hP.isPrime; Formalism.HermitianLatticesTheory.locLen P A B = 1 := by
  have := hP.isPrime
  unfold Formalism.HermitianLatticesTheory.locLen
  have := isLocalizedModule_quotient_prime hP ht ht2
  have eq := IsLocalizedModule.linearEquiv P.primeCompl (i_g P A B) (quotientSpanToQuotientPrime P t ht ∘ₗ e.toLinearMap)
  rw [eq.length_eq]
  have : IsSimpleModule (𝓞 E) (𝓞 E ⧸ P) := isSimpleModule_iff_isCoatom.2 hP.out
  rw [Module.length_eq_one]
  rfl

theorem localLength_cyclic_not_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) [P.IsPrime] (ht : t ∉ P) :
    Formalism.HermitianLatticesTheory.locLen P A B = 0 := by
  have htA : ∀ x ∈ A, t • x ∈ B := by
    intro x hx
    have h1 : e (Submodule.Quotient.mk (t • (⟨x, hx⟩ : A))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self t)
    have h2 := (LinearEquiv.map_eq_zero_iff e).mp h1
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h2
    exact h2
  have hsub : Subsingleton ((Formalism.HermitianLatticesTheory.localization₂ P A) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P B).comap (Formalism.HermitianLatticesTheory.localization₂ P A).subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : ∃ s ∈ P.primeCompl, s • x ∈ A := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    show ∃ s ∈ P.primeCompl, s • x ∈ B
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mpr fun h => ?_, ?_⟩
    · rcases ‹P.IsPrime›.mem_or_mem h with h | h
      · exact ht h
      · exact Ideal.mem_primeCompl_iff.mp hs h
    · rw [mul_smul]
      exact htA _ hsx
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [Module.length_eq_zero_iff.mpr hsub]
  rfl

theorem genIdx_cyclic_split_prime {A B : Submodule (𝓞 E) S.V} (hBA : B ≤ A) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T)
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)})) :
    genIdxH A B = (T : ℝ) ^ finrank ℚ E := by
  unfold genIdxH
  have h1 : ∀ P : HeightOneSpectrum (𝓞 E),
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.lidx P.asIdeal A B) =
        ∏ᶠ (_ : P ∈ plOver E T), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    intro P
    classical
    have := P.isPrime
    rw [i_lidx_of_le P.asIdeal hBA]
    by_cases hP : P ∈ plOver E T
    · have hmax := P.isPrime.isMaximal P.ne_bot
      rw [finprod_eq_if, if_pos hP, localLength_cyclic_mem e P.asIdeal hmax hP (hs P.asIdeal hmax hP).2]
      simp
    · rw [finprod_eq_if, if_neg hP, localLength_cyclic_not_mem e P.asIdeal hP]
      simp
  rw [finprod_congr h1]
  exact finprod_plOver E hT hs id

theorem latDet_sq_of_cyclic_dual_quotient (M : Submodule (𝓞 E) S.V) (hl : Submodule.IsLattice E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual S.hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T) (w₁ : S.V)
    (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual S.hT M) (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual S.hT M, ∃ a : 𝓞 E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 E) ∣ a) :
    latDetH S.hT M = Real.sqrt ((T : ℝ) ^ finrank ℚ E) := by
  have hA : Formalism.HermitianLatticesTheory.dual S.hT M ⊓ Submodule.restrictScalars (𝓞 E) (Submodule.span E (M : Set S.V)) =
      Formalism.HermitianLatticesTheory.dual S.hT M := by
    apply inf_eq_left.mpr
    intro w hw'
    change w ∈ Submodule.span E (M : Set S.V)
    have hw₁ : w₁ ∈ Submodule.span E (M : Set S.V) := by
      have hm : ((T : ℕ) : 𝓞 E) • w₁ ∈ M := (hker _).2 (dvd_refl _)
      have hs : ((T : ℕ) : E) • w₁ ∈ Submodule.span E (M : Set S.V) := by
        have hm' : ((T : ℕ) : 𝓞 E) • w₁ ∈ Submodule.span E (M : Set S.V) := Submodule.subset_span hm
        simpa only [Nat.cast_smul_eq_nsmul] using hm'
      have hn : ((T : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne_zero
      simpa only [inv_smul_smul₀ hn] using
        (Submodule.span E (M : Set S.V)).smul_mem (((T : ℕ) : E)⁻¹) hs
    obtain ⟨a, ha⟩ := hgen w hw'
    have ha' : w + a • w₁ ∈ Submodule.span E (M : Set S.V) := Submodule.subset_span ha
    have hs : a • w₁ ∈ Submodule.span E (M : Set S.V) := by
      simpa only [IsScalarTower.algebraMap_smul] using
        (Submodule.span E (M : Set S.V)).smul_mem (algebraMap (𝓞 E) E a) hw₁
    simpa only [add_sub_cancel_right] using (Submodule.span E (M : Set S.V)).sub_mem ha' hs
  have hφ : ∀ a : 𝓞 E, LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩) a =
      Submodule.Quotient.mk ⟨a • w₁, (Formalism.HermitianLatticesTheory.dual S.hT M).smul_mem a hw⟩ := by
    intro a
    rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul]
    rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) := by
    intro y
    obtain ⟨⟨w, hwA⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨a, ha⟩ := hgen w hwA
    refine ⟨-a, ?_⟩
    rw [hφ, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, Submodule.subtype_apply,
      Submodule.subtype_apply]
    have h1 : -a • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [h1]
    exact M.neg_mem ha
  have hK : LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) =
      Ideal.span {((T : ℕ) : 𝓞 E)} := by
    ext a
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Ideal.mem_span_singleton]
    exact hker a
  unfold latDetH dualInH
  rw [hA]
  congr 1
  exact genIdx_cyclic_split_prime hint hT hs
    ((Submodule.quotEquivOfEq _ _ hK).symm.trans (LinearMap.quotKerEquivOfSurjective _ hsurj)).symm

end Idx

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_rat_E_eq_two_f (D : D7) : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)
  ring

theorem latDet_of_cyclic_dual_quotient (D : D7) (M : Submodule (𝓞 D.host.E) (D.sp.X 0).V) (hl : Submodule.IsLattice D.host.E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl D.host.E T)
    (w₁ : (D.sp.X 0).V) (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M)
    (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a) :
    latDetH (D.sp.X 0).hT M = ((T ^ D.R.f : ℕ) : ℝ) := by
  rw [latDet_sq_of_cyclic_dual_quotient M hl hint hT hs w₁ hw hgen hker, finrank_rat_E_eq_two_f, pow_mul',
    Real.sqrt_sq (by positivity)]
  norm_cast

end Record

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_orthLattice_eq_pow (D : D7) (u : D.what₂.Word) :
    ForPrimeFlagLattice D u fun F0 Λ => latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  refine latDet_of_cyclic_dual_quotient D _ (orthLattice_isLattice F0 he hz Λ hΛ hu) ?_ hTp hsp w₁ hw₁ hgen hann
  intro x hx
  exact (i_mem_dual _ _).2 fun y hy => orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y hy x hx

theorem orthLattice_structure (D : D7) (u : D.what₂.Word) : BaseLatticeStructure D u := orthLattice_structure_of_det D u (det_orthLattice_eq_pow D u)

theorem orth_space_posDef (D : D7) (u : D.what₂.Word) (hT : 0 < Tu D u) : IsPosDef (D.sp.X 0).hT :=
  orth_space_posDef_every_place (Formalism.MainNotions.S.Inh.tie_flag0 D u) rfl rfl hT

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gluing_mass_of_lift_number_genus (D : D7) (u : D.what₂.Word) (hL : LiftsConjugateUnderStabilizer D u) (h4 : GluingNumber D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u := by
  intro hT
  exact gluing_mass_of_lift_and_number D u (orth_space_posDef D u hT.pos)
    (fun hT h3 hsp F0 he hz Λ hΛ => (orthLattice_structure D u hT h3 hsp F0 he hz Λ hΛ).1) hL h4 h5 hT

end Formalism.MainNotions.BridgeLemma₂

end
