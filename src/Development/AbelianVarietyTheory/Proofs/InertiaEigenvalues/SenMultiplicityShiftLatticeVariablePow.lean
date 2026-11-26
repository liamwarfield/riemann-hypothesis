module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow
noncomputable section
namespace GlobalTheory.PhiGam.SenShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem mem_iSup_comap_pow {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (Q : Submodule k U) (hQ : ∀ p ∈ Q, S p ∈ Q) (u : U) :
    u ∈ (⨆ m : ℕ, Q.comap (S ^ m)) ↔ ∃ m : ℕ, (S ^ m) u ∈ Q := by
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  exact Submodule.mem_iSup_of_directed _ hmono.directed_le

theorem gmult_transport {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T T' : Module.End k U)
    (P Q P' Q' : Submodule k U) (e : U ≃ₗ[k] U) (x y : k)
    (heP : ∀ u, e u ∈ P' ↔ u ∈ P) (heQ : ∀ u, e u ∈ Q' ↔ u ∈ Q)
    (hP : ∀ p ∈ P, T p ∈ P) (hQ : ∀ p ∈ Q, T p ∈ Q) (hQ' : ∀ p ∈ Q', T' p ∈ Q')
    (h : ∀ p ∈ P, T' (e p) - x • e p - e (T p - y • p) ∈ Q') :
    gmult T' P' Q' x = gmult T P Q y := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) y with hSdef
  set S' := T' - algebraMap k (Module.End k U) x with hS'def
  have hS : ∀ u, S u = T u - y • u := fun u => by simp [hSdef, Module.algebraMap_end_apply]
  have hS' : ∀ u, S' u = T' u - x • u := fun u => by simp [hS'def, Module.algebraMap_end_apply]
  have hSP : ∀ p ∈ P, S p ∈ P := fun p hp => by rw [hS]; exact P.sub_mem (hP p hp) (P.smul_mem _ hp)
  have hSQ : ∀ p ∈ Q, S p ∈ Q := fun p hp => by rw [hS]; exact Q.sub_mem (hQ p hp) (Q.smul_mem _ hp)
  have hSQ' : ∀ p ∈ Q', S' p ∈ Q' := fun p hp => by
    rw [hS']; exact Q'.sub_mem (hQ' p hp) (Q'.smul_mem _ hp)
  have hpow : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ P ∧ (S' ^ m) (e p) - e ((S ^ m) p) ∈ Q' := by
    intro m p hp
    induction m with
    | zero => simpa using hp
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      refine ⟨hSP _ h1, ?_⟩
      have h3 := h _ h1
      rw [← hS, ← hS'] at h3
      have h4 := Q'.add_mem (hSQ' _ h2) h3
      rw [map_sub] at h4
      simpa using h4
  set A := P ⊓ ⨆ m : ℕ, Q.comap (S ^ m) with hA
  set A' := P' ⊓ ⨆ m : ℕ, Q'.comap (S' ^ m) with hA'
  have heA : ∀ u, e u ∈ A' ↔ u ∈ A := by
    intro u
    rw [hA, hA', Submodule.mem_inf, Submodule.mem_inf, heP, mem_iSup_comap_pow S Q hSQ,
      mem_iSup_comap_pow S' Q' hSQ']
    refine and_congr_right fun hu => exists_congr fun m => ?_
    rw [← heQ]
    have h2 := (hpow m u hu).2
    constructor
    · intro h1; simpa using Q'.sub_mem h1 h2
    · intro h1; simpa using Q'.add_mem h2 h1
  have hmap : A.map (e : U →ₗ[k] U) = A' := by
    ext u
    obtain ⟨u, rfl⟩ := e.surjective u
    rw [heA]
    exact Submodule.mem_map_equiv A |>.trans (by simp)
  let E : A ≃ₗ[k] A' := e.ofSubmodules A A' hmap
  have hE : ∀ z : A, ((E z : A') : U) = e z := fun z => rfl
  refine (Submodule.Quotient.equiv (Q.submoduleOf A) (Q'.submoduleOf A') E ?_).finrank_eq.symm
  ext z
  obtain ⟨z, rfl⟩ := E.surjective z
  refine (Submodule.mem_map_equiv _).trans ?_
  rw [LinearEquiv.symm_apply_apply]
  change (z : U) ∈ Q ↔ ((E z : A') : U) ∈ Q'
  rw [hE, heQ]

theorem sen_sh : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N _ hC a x
  have hv : vv k ≠ 0 := vv_ne_zero k
  let e : V ≃ₗ[k] V :=
    (LinearEquiv.smulOfNeZero k⸨X⸩ V (vv k ^ a) (zpow_ne_zero a hv)).restrictScalars k
  have he : ∀ u, e u = vv k ^ a • u := fun u => rfl
  have hmem : ∀ (M : Submodule k⟦X⟧ V) (u : V), e u ∈ sh a M ↔ u ∈ M := fun M u => by
    rw [he, mem_sh_iff_smul_mem, smul_smul, ← zpow_add₀ hv, neg_add_cancel, zpow_zero, one_smul]
  have hsh : sh 1 (sh a N) = sh a (sh 1 N) := by rw [sh_sh_eq, sh_sh_eq, add_comm]
  unfold sen qmult
  refine gmult_transport (nab g) (nab g) _ _ _ _ e x (x + a) (fun u => hmem N u) (fun u => ?_)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (fun p hp => ?_)
    (fun p hp => ?_)
  · rw [hsh]; exact hmem _ u
  · rw [sh_sh_eq] at hp ⊢
    exact Window.nab_mem_sh R hg hC _ hp
  · obtain ⟨n', hn', h⟩ := Window.nab_shift R hg hC a hp
    rw [← he, ← he] at h
    rw [hsh, h, ← map_smul, ← map_sub, ← map_sub]
    refine (hmem _ _).2 (mem_sh_iff_exists.2 ⟨n', hn', ?_⟩)
    rw [zpow_one, add_smul]
    abel

end GlobalTheory.PhiGam.SenShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePowStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_shift_lattice_variablePow : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  first | exact @GlobalTheory.PhiGam.SenShift.sen_sh | exact GlobalTheory.PhiGam.SenShift.sen_sh | (intros; apply GlobalTheory.PhiGam.SenShift.sen_sh <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbedding
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CutOff

theorem exists_isClopen_isCompact_superset {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by
  classical
  have h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V := by
    intro z
    obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
    obtain ⟨V, hV, hzV, hVK⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 hKz
    exact ⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩
  choose V hVc hVk hzV using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))
  exact ⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z,
    t.isCompact_biUnion fun z _ => hVk z, ht⟩

theorem exists_nhds_one_mul_mem_iff {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by
  open scoped Pointwise in
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_left hUk hUo subset_rfl
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩
  rintro w ⟨hw, hw'⟩ x
  constructor
  · intro h
    have : w⁻¹ * (w * x) ∈ U := hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)
    simpa using this
  · intro h
    exact hVU (Set.mul_mem_mul hw h)

theorem isLocallyConstant_indicator_one {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hx, Set.notMem_compl_iff.not.1 (by simpa using hy)]

theorem exists_cutoff : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ
  classical
  obtain ⟨U, hUc, hUk, hZU⟩ := exists_isClopen_isCompact_superset hZ
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_mul_mem_iff hUc.isOpen hUk
  set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ
  have hβlc : IsLocallyConstant β := isLocallyConstant_indicator_one hUc
  have hβc : Continuous β := hβlc.continuous
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF
  have hFinv : ∀ g t, F (g * i t) = F g := by
    intro g t
    have := integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t
    simpa [hF, mul_assoc, map_mul] using this
  have hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x := by
    intro w hw x
    simp [hβ, Set.indicator, hWU w hw x]
  have hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g := by
    intro w hw g
    simp only [hF, mul_assoc, hβmul w hw]
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1) := by
      simpa using (continuous_mul_const g⁻¹).tendsto g
    filter_upwards [hc hW] with y hy
    have := hFW _ hy g
    rwa [inv_mul_cancel_right] at this
  have hFpos : ∀ g ∈ U, 0 < F g := by
    intro g hg
    have hcont : Continuous (fun s => β (g * i s)) :=
      hβc.comp (continuous_const.mul hi.continuous)
    have hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)
    have hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      (hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous
    have hsupp : HasCompactSupport (fun s => β (g * i s)) := by
      refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
      have hx' : g * i x ∉ U := hx
      simp [hβ, hx']
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp
      (fun s => hβ0 _) (by simp [hβ, hg])
  refine ⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hβlc hFlc (· / ·)
  · refine HasCompactSupport.intro hUk fun x hx => ?_
    simp [hβ, hx]
  · intro g
    exact div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)
  · intro z hz s₀
    have h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν
        = ∫ s, β (z * i s) / F (z * i s) ∂ν := by
      have := integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀
      simpa [mul_assoc, map_mul] using this
    rw [h1]
    have h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z := fun s => by rw [hFinv]
    simp_rw [h2]
    rw [integral_div]
    exact div_self (hFpos z (hZU hz)).ne'

end GlobalTheory.CutOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbeddingStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  first | exact @GlobalTheory.CutOff.exists_cutoff | exact GlobalTheory.CutOff.exists_cutoff | (intros; apply GlobalTheory.CutOff.exists_cutoff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Act

variable (O : Type) [CommRing O] (E : Type) [Field E] {A : Type} [CommRing A] [Algebra O A] [Algebra E A]

def stLat (g : A) : Set (Submodule O A) := {L | IsLat O E L ∧ ∀ y ∈ L, g * y ∈ L}

theorem mem_mulLat_iff (t : Aˣ) (L : Submodule O A) (x : A) :
    x ∈ mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * x ∈ L := by
  unfold mulLat
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [← mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [← mul_assoc]⟩

theorem mulLat_one (L : Submodule O A) : mulLat O (1 : A) L = L := by
  simp [mulLat, LinearMap.mulLeft_one]

theorem mulLat_mul (a b : A) (L : Submodule O A) : mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  simp [mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

variable {O E} in
theorem mulLat_mem_stLat {g : A} (t : Aˣ) {L : Submodule O A} (hL : L ∈ stLat O E g) :
    mulLat O (t : A) L ∈ stLat O E g := by
  refine ⟨⟨hL.1.1.map _, ?_⟩, ?_⟩
  · have himg : ((mulLat O (t : A) L : Submodule O A) : Set A) = (LinearMap.mulLeft E (t : A)) '' (L : Set A) := by
      ext x; simp [mulLat]
    rw [himg, Submodule.span_image, hL.1.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((t⁻¹ : Aˣ) : A) * z, by simp [← mul_assoc]⟩
  · intro x hx
    rw [mem_mulLat_iff] at hx ⊢
    have := hL.2 _ hx
    rwa [mul_left_comm]

instance (g : A) : MulAction Aˣ (stLat O E g) where
  smul t L := ⟨mulLat O (t : A) L, mulLat_mem_stLat t L.2⟩
  one_smul L := Subtype.ext (by change mulLat O ((1 : Aˣ) : A) L = L; rw [Units.val_one]; exact mulLat_one O _)
  mul_smul a b L := Subtype.ext (by change mulLat O ((a * b : Aˣ) : A) L = mulLat O (a : A) (mulLat O (b : A) L); rw [Units.val_mul]; exact mulLat_mul O _ _ _)

theorem stLat_smul_val (g : A) (t : Aˣ) (L : stLat O E g) :
    ((t • L : stLat O E g) : Submodule O A) = mulLat O (t : A) L := rfl

end Act

section Pair

variable (O : Type) [CommRing O] (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂]
  [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]

def LatPair (g₁ : A₁) (g₂ : A₂) : Type := stLat O E g₁ × stLat O E g₂

instance (g₁ : A₁) (g₂ : A₂) : MulAction (A₁ × A₂)ˣ (LatPair O E g₁ g₂) where
  smul t p := (Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2)
  one_smul p := by
    change (_, _) = p
    rw [map_one, map_one, one_smul, one_smul]
    rfl
  mul_smul a b p := by
    change (_, _) = (_, _)
    rw [map_mul, map_mul, mul_smul, mul_smul]
    rfl

theorem latPair_smul (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (p : LatPair O E g₁ g₂) :
    t • p = ((Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2) :
      LatPair O E g₁ g₂) := rfl

variable [IsDomain O] [IsNoetherianRing O] [Algebra O E] [IsFractionRing O E]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

variable {O E} in
theorem comap_inl_mem_stLat {g₁ : A₁} {g₂ : A₂} {M : Submodule O (A₁ × A₂)}
    (hM : M ∈ stLat O E ((g₁, g₂) : A₁ × A₂)) :
    M.comap (LinearMap.inl O A₁ A₂) ∈ stLat O E g₁ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI := isNoetherian_of_fg_of_noetherian M hM.1.1
    have hle : (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) ≤ M := Submodule.map_comap_le _ _
    have h1 : (((M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂)).comap M.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
    exact Submodule.fg_of_fg_map_injective _ LinearMap.inl_injective h2
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : ((y, 0) : A₁ × A₂) ∈ Submodule.span E (M : Set (A₁ × A₂)) := by rw [hM.1.2]; trivial
    obtain ⟨r, hr, hrM⟩ := ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span M hy
    have hrC : algebraMap O E r ≠ 0 := by
      rw [Ne, ← (algebraMap O E).map_zero]
      exact fun h => hr (IsFractionRing.injective O E h)
    have hmem : r • y ∈ M.comap (LinearMap.inl O A₁ A₂) := by
      simpa [Submodule.mem_comap] using hrM
    have : y = (algebraMap O E r)⁻¹ • (algebraMap O E r • y) := by
      rw [smul_smul, inv_mul_cancel₀ hrC, one_smul]
    rw [this, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · intro y hy
    simp only [Submodule.mem_comap, LinearMap.coe_inl] at hy ⊢
    have := hM.2 _ hy
    simpa using this

variable {O E} in
theorem map_snd_mem_stLat {g₁ : A₁} {g₂ : A₂} {M : Submodule O (A₁ × A₂)}
    (hM : M ∈ stLat O E ((g₁, g₂) : A₁ × A₂)) :
    M.map (LinearMap.snd O A₁ A₂) ∈ stLat O E g₂ := by
  refine ⟨⟨hM.1.1.map _, ?_⟩, ?_⟩
  · have himg : ((M.map (LinearMap.snd O A₁ A₂) : Submodule O A₂) : Set A₂) =
        (LinearMap.snd E A₁ A₂) '' (M : Set (A₁ × A₂)) := by
      ext x; simp
    rw [himg, Submodule.span_image, hM.1.2, Submodule.map_top, LinearMap.range_eq_top.mpr LinearMap.snd_surjective]
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hM.2 m hm, by simp⟩

def latProj (g₁ : A₁) (g₂ : A₂) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) : LatPair O E g₁ g₂ :=
  (⟨_, comap_inl_mem_stLat M.2⟩, ⟨_, map_snd_mem_stLat M.2⟩)

end Pair

end GlobalTheory.UnitLemma
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem integral_eq_zero_of_shift_mul {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + t) ∂μ := (integral_add_right_eq_self g t).symm
      _ = ∫ x, g x * z ∂μ := by simp only [h]
      _ = (∫ x, g x ∂μ) * z := integral_mul_const z g
  have h2 : (∫ x, g x ∂μ) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hz

theorem exists_short_dot_eq {F : Type} [NormedField F] {r : ℕ} (x₀ : F) {ε : ℝ} (hε : 0 < ε) (b : Fin r → F)
    (hb : b ∉ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε)) :
    ∃ t : Fin r → F, ‖t‖ < ε ∧ t ⬝ᵥ b = x₀ := by
  have hR : 0 ≤ ‖x₀‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hb' : ‖x₀‖ / ε < ‖b‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
  obtain ⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by
    by_contra hcon
    push Not at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')
  have hbi : b i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hi
    exact absurd hi (not_lt.2 hR)
  refine ⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hε] at hi
      calc ‖x₀‖ < ‖b j‖ * ε := hi
        _ = ε * ‖b j‖ := mul_comm _ _
    · rw [Pi.single_eq_of_ne hj, norm_zero]
      exact hε
  · rw [single_dotProduct, div_mul_cancel₀ _ hbi]

theorem fourG_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
    HasCompactSupport (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf' hU
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨U, hU0, hUinv⟩ := hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F) := rfl
  obtain ⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  obtain ⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  have key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 →
      f' (A, b + t, c, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hB t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  have key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 →
      f' (A, b, c + t, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hC t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  let P : Set (Matrix (Fin r) (Fin r) F × F) := (fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'
  have hPc : IsCompact P := hf'.2.image (by fun_prop)
  let K : Set (Gl r F) :=
    (fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) ''
      (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))
  have hKc : IsCompact K :=
    (hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)
  refine HasCompactSupport.intro hKc fun Y hY => ?_
  obtain ⟨A, b, c, l⟩ := Y
  show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0
  by_cases hP : (A, l) ∈ P
  · by_cases hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)
    · by_cases hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)
      · exact absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY
      · obtain ⟨t, ht, htc⟩ := exists_short_dot_eq x₀ hε2 c hc
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
        simp only
        rw [key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc,
          mul_assoc]
    · obtain ⟨t, ht, htb⟩ := exists_short_dot_eq x₀ hε3 b hb
      have hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0 := by
        intro b'
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_
        rw [key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]
      simp only [hin, integral_zero]
  · have hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0 := by
      intro b' c'
      by_contra hne
      exact hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩
    simp only [hz, zero_mul, integral_zero]

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlockStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → HasCompactSupport (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_hasCompactSupport | exact GlobalTheory.JR.fourG_hasCompactSupport | (intros; apply GlobalTheory.JR.fourG_hasCompactSupport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLeMaximalIdealPowSmulOfDirected
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

end GlobalTheory.Chevalley

namespace GlobalTheory.Chevalley

private theorem isArtinian_quotient_maximalIdeal_pow_succ_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (n : ℕ) : IsArtinian B (M ⧸ (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M))) := by
  have hmin : maximalIdeal B ∈ (maximalIdeal B ^ (n + 1)).minimalPrimes := by
    refine ⟨⟨(maximalIdeal.isMaximal B).isPrime, Ideal.pow_le_self (Nat.succ_ne_zero n)⟩, ?_⟩
    rintro q ⟨hq, hle⟩ -
    exact hq.le_of_pow_le hle
  have : IsArtinianRing (B ⧸ maximalIdeal B ^ (n + 1)) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hmin
  exact isArtinian_of_surjective_algebraMap
    (Ideal.Quotient.mk_surjective (I := maximalIdeal B ^ (n + 1)))

private theorem mem_of_forall_mem_sup_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (K : Submodule B M) (x : M)
    (h : ∀ n, x ∈ K ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M)) : x ∈ K := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⧸ K) (maximalIdeal B)
    (maximalIdeal.isMaximal B).ne_top
  have hx : K.mkQ x ∈ ⨅ n, maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h n)
    have hmap : (maximalIdeal B ^ n • (⊤ : Submodule B M)).map K.mkQ ≤
        maximalIdeal B ^ n • (⊤ : Submodule B (M ⧸ K)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    have hzq := hmap (Submodule.mem_map_of_mem hz)
    have hy0 : K.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [map_add (f := _), hy0, zero_add]
    exact hzq
  rw [hbot, Submodule.mem_bot] at hx
  exact (Submodule.Quotient.mk_eq_zero K).mp hx

private theorem exists_limit_of_sub_mem_maximalIdeal_pow_smul (B M : Type) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M]
    [Module B M] [Module.Finite B M] (s : ℕ) (y : ℕ → M)
    (hy : ∀ k, y (k + 1) - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M)) :
    ∃ x, ∀ k, x - y k ∈ maximalIdeal B ^ (s + k) • (⊤ : Submodule B M) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := B) (M := M)
  have hlift : ∀ (J : Ideal B) (z : M), z ∈ J • (⊤ : Submodule B M) →
      ∃ c : Fin m → B, (∀ l, c l ∈ J) ∧ ∑ l, c l • g l = z := by
    intro J z hz
    rw [← hg, Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, ha, (Finsupp.sum_fintype a (fun i c => c • g i) fun i => zero_smul B (g i)).symm⟩
  choose c hcI hcsum using fun k => hlift _ _ (hy k)
  obtain ⟨S, hS⟩ : ∃ S : Fin m → ℕ → B, ∀ l n, S l n = ∑ k ∈ Finset.range n, c k l :=
    ⟨_, fun _ _ => rfl⟩
  have hSdiff : ∀ l n p, n ≤ p → S l p - S l n ∈ maximalIdeal B ^ (s + n) := by
    intro l n p hnp
    rw [hS, hS, ← Finset.sum_range_add_sum_Ico _ hnp, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk' := (Finset.mem_Ico.mp hk).1
    exact Ideal.pow_le_pow_right (by omega) (hcI k l)
  have hprec : IsPrecomplete (maximalIdeal B) B := inferInstance
  have hlim : ∀ l, ∃ L, ∀ n, S l n - L ∈ maximalIdeal B ^ (s + n) := by
    intro l
    obtain ⟨L, hL⟩ := hprec.prec (f := S l) (fun {a b} hab => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Submodule.neg_mem_iff]
      exact Ideal.pow_le_pow_right (by omega) (hSdiff l a b hab))
    refine ⟨L, fun n => ?_⟩
    have h1 := hL (s + n)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hSdiff l n (s + n) (by omega)
    have e : S l n - L = (S l (s + n) - L) - (S l (s + n) - S l n) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.pow_le_pow_right (by omega) h1) h2
  choose L hL using hlim
  refine ⟨y 0 + ∑ l, L l • g l, fun k => ?_⟩
  have htel : ∑ l, S l k • g l = y k - y 0 := by
    simp only [hS, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp_rw [hcsum]
    exact Finset.sum_range_sub y k
  have e : y 0 + ∑ l, L l • g l - y k = -∑ l, (S l k - L l) • g l := by
    simp only [sub_smul, Finset.sum_sub_distrib, htel]
    abel
  rw [e, Submodule.neg_mem_iff]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem_smul (hL l k) Submodule.mem_top

theorem _root_.GlobalTheory.Chevalley.exists_le_maximalIdeal_pow_smul_of_directed :
    ∀ (B M ι : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [IsAdicComplete (maximalIdeal B) B] [AddCommGroup M] [Module B M] [Module.Finite B M]
      (K : ι → Submodule B M), Nonempty ι → Directed (· ≥ ·) K → (⨅ i, K i) = ⊥ →
      ∀ N : ℕ, ∃ i, K i ≤ maximalIdeal B ^ N • (⊤ : Submodule B M) := by
  intro B M ι _ _ _ _ _ _ _ K hne hdir hbot N
  haveI := hne
  have hmin : ∀ n, ∃ j, ∀ i, K j ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
      K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    haveI := isArtinian_quotient_maximalIdeal_pow_succ_smul B M n
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
      (wellFounded_lt (α := Submodule B (M ⧸ (maximalIdeal B ^ (n + 1) •
        (⊤ : Submodule B M))))).has_min
        (Set.range fun i => (K i).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ)
        (Set.range_nonempty _)
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hki, hkj⟩ := hdir i j
    have hle := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hkj
    have heq : (K k).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ =
        (K j).map (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ := by
      by_contra hne'
      exact hj _ ⟨k, rfl⟩ (lt_of_le_of_ne hle hne')
    have hji := Submodule.map_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hki
    rw [heq] at hji
    have hc := Submodule.comap_mono (f := (maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)).mkQ) hji
    rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ] at hc
    rwa [sup_comm (K j), sup_comm (K i)]
  choose j hj using hmin
  by_contra hcon
  push_neg at hcon
  have hE_step : ∀ n, ∀ x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M),
      ∃ x' ∈ K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M),
        x - x' ∈ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hj n (j (n + 1)) hx)
    exact ⟨a, Submodule.mem_sup_left ha, by simpa using hb⟩
  have hE_anti : ∀ n, K (j (n + 1)) ⊔ maximalIdeal B ^ (n + 1 + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := fun n =>
    (hj (n + 1) (j n)).trans
      (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _)
  have hE_mono : ∀ n p, n ≤ p → K (j p) ⊔ maximalIdeal B ^ (p + 1) • (⊤ : Submodule B M) ≤
      K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n p hnp
    induction hnp with
    | refl => exact le_rfl
    | step _ ih => exact (hE_anti _).trans ih
  have hE_zero : ∀ x, (∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M)) →
      x = 0 := by
    intro x hx
    have hmem : x ∈ ⨅ i, K i := Submodule.mem_iInf _ |>.mpr fun i =>
      mem_of_forall_mem_sup_maximalIdeal_pow_smul B M (K i) x fun n => by
        have hle : K i ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) ≤
            K i ⊔ maximalIdeal B ^ n • (⊤ : Submodule B M) :=
          sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) _
        exact hle (hj n i (hx n))
    rwa [hbot, Submodule.mem_bot] at hmem
  have hnot : ¬ K (j N) ⊔ maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) ≤
      maximalIdeal B ^ (N + 1) • (⊤ : Submodule B M) := fun h =>
    hcon (j N) ((le_sup_left.trans h).trans
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))))
  obtain ⟨x0, hx0, hx0P⟩ := SetLike.not_le_iff_exists.mp hnot
  choose f hf1 hf2 using hE_step
  let y : (k : ℕ) → {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)} :=
    fun k => Nat.rec (motive := fun k =>
        {x // x ∈ K (j (N + k)) ⊔ maximalIdeal B ^ (N + k + 1) • (⊤ : Submodule B M)})
      ⟨x0, hx0⟩ (fun k z => ⟨f (N + k) z.1 z.2, hf1 _ _ _⟩) k
  have hy_succ : ∀ k, (y (k + 1)).1 = f (N + k) (y k).1 (y k).2 := fun k => rfl
  obtain ⟨x, hx⟩ := exists_limit_of_sub_mem_maximalIdeal_pow_smul B M (N + 1)
    (fun k => (y k).1) (fun k => by
      have e : N + 1 + k = N + k + 1 := by omega
      rw [hy_succ, e, ← neg_sub, Submodule.neg_mem_iff]
      exact hf2 (N + k) (y k).1 (y k).2)
  have hxE : ∀ n, x ∈ K (j n) ⊔ maximalIdeal B ^ (n + 1) • (⊤ : Submodule B M) := by
    intro n
    have e : N + 1 + n = N + n + 1 := by omega
    have hd := hx n
    rw [e] at hd
    have hk := Submodule.add_mem _ (y n).2 (Submodule.mem_sup_right hd)
    rw [add_sub_cancel] at hk
    exact hE_mono n (N + n) (by omega) hk
  have hx0' := hE_zero x hxE
  apply hx0P
  have h0 := hx 0
  rw [hx0', zero_sub, Submodule.neg_mem_iff] at h0
  exact h0

end GlobalTheory.Chevalley
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermBasisOrthonormal
noncomputable section

namespace GlobalTheory.UnitLemma.OrthBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem herm_add_right (x y z₁ z₂ : B.A) : B.herm x y (z₁ + z₂) = B.herm x y z₁ + B.herm x y z₂ := by
  unfold InvAlg.herm
  rw [map_add (f := _), mul_add, map_add (f := _)]

theorem herm_zero_right (x y : B.A) : B.herm x y 0 = 0 := by
  unfold InvAlg.herm
  simp

theorem herm_smul_right' (x y z : B.A) (a : K.E) : B.herm x y (a • z) = K.c a * B.herm x y z := by
  unfold InvAlg.herm
  rw [Algebra.smul_def, map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem herm_sum_smul_left {n : ℕ} (x z : B.A) (a : Fin n → K.E) (v : Fin n → B.A) :
    B.herm x (∑ j, a j • v j) z = ∑ j, a j * B.herm x (v j) z := by
  unfold InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

theorem herm_mul_left_of_fixed (x g y z : B.A) (hg : B.σ g = g) :
    B.herm x (g * y) z = B.herm x y (g * z) := by
  unfold InvAlg.herm
  rw [map_mul B.σ, hg]; congr 1; ring

theorem repr_mul {n : ℕ} (e : Module.Basis (Fin n) K.E B.A) (g z : B.A) (i : Fin n) :
    e.repr (g * z) i = ∑ j, e.repr z j * e.repr (g * e j) i := by
  conv_lhs => rw [← e.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

end GlobalTheory.UnitLemma.OrthBasis

namespace GlobalTheory.UnitLemma

open GlobalTheory.UnitLemma.OrthBasis

theorem herm_basis_orthonormal : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by
  intro K B x w hg hw hspan n e hM hwj

  let P : B.A → Prop := fun z => ∀ i, B.herm x (e i) z = K.c (e.repr z i)
  have hstep : ∀ z, P z → P (B.g * z) := by
    intro z hz i
    rw [← herm_mul_left_of_fixed B x B.g (e i) z hg]
    conv_lhs => rw [← e.sum_repr (B.g * e i)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [herm_sum_smul_left, repr_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, RingEquiv.map_mul K.c, hM, mul_comm]
  have hpow : ∀ l : ℕ, P (B.g ^ l * w) := by
    intro l
    induction l with
    | zero => simpa [P] using hwj
    | succ l ih => rw [pow_succ', mul_assoc]; exact hstep _ ih
  have hspanP : ∀ a ∈ Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l), P (a * w) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hpow l
    | zero => intro i; simp [herm_zero_right]
    | add y z _ _ hy hz =>
      intro i; rw [add_mul, herm_add_right, hy i, hz i, map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    | smul a y _ hy =>
      intro i; rw [smul_mul_assoc, herm_smul_right', hy i, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
        RingEquiv.map_mul K.c]
  have hall : ∀ z, P z := by
    intro z
    obtain ⟨u, rfl⟩ := hw
    have := hspanP (z * ((u⁻¹ : B.Aˣ) : B.A)) (by rw [hspan]; exact Submodule.mem_top)
    rwa [mul_assoc, Units.inv_mul, mul_one] at this
  intro i j
  rw [hall (e j) i, e.repr_self, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero _

end GlobalTheory.UnitLemma
end
end
