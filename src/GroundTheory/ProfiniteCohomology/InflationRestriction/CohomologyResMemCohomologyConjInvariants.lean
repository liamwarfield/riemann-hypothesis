module

public import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
public import GroundTheory.ProfiniteCohomology.InflationRestriction.Coinduced
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.QuotientToInvariantsFunctorPreservesZeroMorphism
public import GroundTheory.ProfiniteCohomology.CoinducedModules.CohomologyCoindCokernelIsoHom

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
section -- merged from GroundTheory.TateCohomology.ConjAction
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

def conjHom (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, ‹S.Normal›.conj_mem' (s : G) s.2 g⟩
  map_one' := by ext; simp
  map_mul' s t := by ext; simp only [Subgroup.coe_mul]; group

@[simp]
lemma coe_conjHom_apply (g : G) (s : S) : (conjHom S g s : G) = g⁻¹ * s * g := rfl

noncomputable def conjMor (g : G) : res (conjHom S g) (res S.subtype A) ⟶ res S.subtype A :=
  ofHom ⟨A.ρ g, fun s => by
    ext a
    simp only [LinearMap.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, coe_conjHom_apply]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group⟩


end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Formulas

variable (A : Rep.{u} k G) [IsDiscreteRep A]

theorem cochainsComplex_d_zero_apply (a : locallyConstantCochains A 0) (g : Fin 1 → G) :
    (((cochainsComplex A).d 0 1).hom a).1 g =
      A.ρ (g 0) (a.1 Fin.elim0) - a.1 Fin.elim0 := by
  rw [cochainsComplex_d_zero_one]
  change (inhomogeneousCochains.d A 0).hom a.1 g = _
  rw [inhomogeneousCochains.d_hom_apply]
  rw [Fin.sum_univ_one, Subsingleton.elim (fun i : Fin 0 => g i.succ) Fin.elim0,
    Subsingleton.elim (Fin.contractNth 0 (fun x1 x2 => x1 * x2) g) Fin.elim0]
  simp [sub_eq_add_neg]

theorem cochainsComplex_d_one_apply (f : locallyConstantCochains A 1) (g : Fin 2 → G) :
    (((cochainsComplex A).d 1 2).hom f).1 g =
      A.ρ (g 0) (f.1 fun _ => g 1) - f.1 (fun _ => g 0 * g 1) + f.1 (fun _ => g 0) := by
  have h := cochainsComplex_d A 1
  simp only [Nat.reduceAdd] at h
  rw [h]
  change (inhomogeneousCochains.d A 1).hom f.1 g = _
  rw [inhomogeneousCochains.d_hom_apply, Fin.sum_univ_two]
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := funext fun i => by
    rw [Subsingleton.elim i 0]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_eq _ _ _ _ rfl]; rfl
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := funext fun i => by
    rw [Subsingleton.elim i 0, Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]; rfl
  rw [e1, e2, e3]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one, Nat.reduceAdd,
    even_two, Even.neg_pow, one_pow]
  abel

omit [IsTopologicalGroup G] in
theorem fin_one_eq_const (g : Fin 1 → G) : g = fun _ => g 0 :=
  funext fun i => by rw [Subsingleton.elim i 0]

theorem cochainsComplex_d_one_eq_zero_iff (f : locallyConstantCochains A 1) :
    ((cochainsComplex A).d 1 2).hom f = 0 ↔
      ∀ g h : G, f.1 (fun _ => g * h) = f.1 (fun _ => g) + A.ρ g (f.1 fun _ => h) := by
  constructor
  · intro hf g h
    have := congrArg (fun c : locallyConstantCochains A 2 => c.1 ![g, h]) hf
    simp only [cochainsComplex_d_one_apply] at this
    change A.ρ g (f.1 fun _ => h) - f.1 (fun _ => g * h) + f.1 (fun _ => g) = 0 at this
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  · intro hf
    apply Subtype.ext
    funext x
    rw [cochainsComplex_d_one_apply, hf]
    change _ = (0 : A)
    abel

theorem cocycle_one_apply_one {f : locallyConstantCochains A 1}
    (hf : ((cochainsComplex A).d 1 2).hom f = 0) : f.1 (fun _ => 1) = 0 := by
  have := (cochainsComplex_d_one_eq_zero_iff A f).1 hf 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at this
  simpa using this

end Formulas

section Conj

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

theorem continuous_conjHom (g : G) : Continuous (GroundTheory.GroupCoh.conjHom N g) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

noncomputable def cohomologyConj (n : ℕ) (g : G) :
    cohomology (Rep.res N.subtype A) n ⟶ cohomology (Rep.res N.subtype A) n :=
  cohomologyMapAlong (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (GroundTheory.GroupCoh.conjMor A N g) n

def cohomologyConjInvariants (n : ℕ) : Submodule k (cohomology (Rep.res N.subtype A) n) where
  carrier := {x | ∀ g : G, (cohomologyConj A N n g).hom x = x}
  add_mem' hx hy g := by rw [map_add (f := _), hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' r x hx g := by rw [map_smul, hx g]

noncomputable abbrev cocycleOneApply (z : cocycles (Rep.res N.subtype A) 1) (n : N) : A :=
  (((cochainsComplex (Rep.res N.subtype A)).iCycles 1).hom z).1 fun _ => n

theorem cohomologyConj_π_eq_iff (z : cocycles (Rep.res N.subtype A) 1) (g : G) :
    (cohomologyConj A N 1 g).hom ((cohomologyπ _ 1).hom z) = (cohomologyπ _ 1).hom z ↔
      ∃ a : A, ∀ n : N, A.ρ g (cocycleOneApply A N z (GroundTheory.GroupCoh.conjHom N g n)) -
        cocycleOneApply A N z n = A.ρ n a - a := by
  rw [cohomologyConj, cohomologyMapAlong]
  erw [homologyMap_homologyπ_apply]
  change ((cochainsComplex (Rep.res N.subtype A)).homologyπ 1).hom _ =
    ((cochainsComplex (Rep.res N.subtype A)).homologyπ 1).hom z ↔ _
  rw [← sub_eq_zero, ← map_sub]
  change ((cochainsComplex (Rep.res N.subtype A)).homologyπ (0 + 1)).hom _ = 0 ↔ _
  rw [homologyπ_succ_eq_zero_iff, map_sub, iCycles_cyclesMap_apply]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.1 Fin.elim0, fun n => ?_⟩
    have := congrArg (fun c : locallyConstantCochains (Rep.res N.subtype A) 1 => c.1 fun _ => n) hw
    exact this.symm.trans (cochainsComplex_d_zero_apply (Rep.res N.subtype A) w fun _ => n)
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun _ => a, IsLocallyConstant.const _⟩, ?_⟩
    apply Subtype.ext
    funext x
    rw [cochainsComplex_d_zero_apply, fin_one_eq_const x]
    exact (ha (x 0)).symm

theorem cocycleOneApply_mul (z : cocycles (Rep.res N.subtype A) 1) (a b : N) :
    cocycleOneApply A N z (a * b) = cocycleOneApply A N z a + A.ρ a (cocycleOneApply A N z b) :=
  (cochainsComplex_d_one_eq_zero_iff (Rep.res N.subtype A) _).1
    (iCycles_d_apply _ 1 2 z) a b

noncomputable abbrev cocycleOneApplyG (y : cocycles A 1) (g : G) : A :=
  (((cochainsComplex A).iCycles 1).hom y).1 fun _ => g

theorem cocycleOneApplyG_mul (y : cocycles A 1) (a b : G) :
    cocycleOneApplyG A y (a * b) = cocycleOneApplyG A y a + A.ρ a (cocycleOneApplyG A y b) :=
  (cochainsComplex_d_one_eq_zero_iff A _).1 (iCycles_d_apply _ 1 2 y) a b

theorem cohomologyRes_mem_cohomologyConjInvariants (h : cohomology A 1) :
    (cohomologyRes A N 1).hom h ∈ cohomologyConjInvariants A N 1 := by
  obtain ⟨y, rfl⟩ := homologyπ_surjective (cochainsComplex A) 1 h
  intro g
  rw [cohomologyRes, cohomologyMapAlong]
  erw [homologyMap_homologyπ_apply]
  refine (cohomologyConj_π_eq_iff A N _ g).2 ⟨cocycleOneApplyG A y g, fun n => ?_⟩
  have hY : ∀ n : N, cocycleOneApply A N ((cocyclesMapAlong N.subtype
      (continuous_subgroup_subtype N) (𝟙 _) 1).hom y) n = cocycleOneApplyG A y n := fun n => by
    simp only [cocycleOneApply, cocyclesMapAlong, iCycles_cyclesMap_apply]
    rfl
  rw [hY, hY]
  have e : (g : G) * (GroundTheory.GroupCoh.conjHom N g n : G) = n * g := by simp; group
  have h1 := cocycleOneApplyG_mul A y g (GroundTheory.GroupCoh.conjHom N g n)
  rw [e, cocycleOneApplyG_mul A y n g] at h1
  have h2 : A.ρ g (cocycleOneApplyG A y (GroundTheory.GroupCoh.conjHom N g n)) =
      cocycleOneApplyG A y n + A.ρ n (cocycleOneApplyG A y g) - cocycleOneApplyG A y g := by
    rw [h1]
    abel
  rw [h2]
  abel

end Conj

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Complex

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℕ)

theorem homologyπ_zero_injective : Function.Injective (K.homologyπ 0).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, hw⟩ := (homologyπ_eq_zero_iff K z).1 hz
  have hd : K.d ((ComplexShape.up ℕ).prev 0) 0 = 0 := K.shape _ _ (by simp)
  rw [hd] at hw
  apply iCycles_injective K 0
  rw [← hw, map_zero]
  rfl

end Complex

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Invariants

variable {X : ShortComplex (Rep.{u} k G)} [IsDiscreteRep X.X₁] [IsDiscreteRep X.X₂]
  [IsDiscreteRep X.X₃]

theorem exists_mem_invariants_map_eq (hX : X.ShortExact) (h1 : IsZero (cohomology X.X₁ 1))
    (x₃ : X.X₃) (hx₃ : x₃ ∈ X.X₃.ρ.invariants) :
    ∃ x₂ ∈ X.X₂.ρ.invariants, X.g.hom x₂ = x₃ := by
  have hepi : Epi (cohomologyMap X.g 0) := (cohomology_exact₃ hX 0 1 rfl).epi_f (h1.eq_of_tgt _ _)
  have hsurj : Function.Surjective (cohomologyMap X.g 0).hom :=
    (ModuleCat.epi_iff_surjective _).1 hepi
  let c₃ : locallyConstantCochains X.X₃ 0 := invariantsToCochains₀ X.X₃ ⟨x₃, hx₃⟩
  have hc₃ : ((cochainsComplex X.X₃).d 0 (0 + 1)).hom c₃ = 0 := by
    rw [cochainsComplex_d]
    have := congrArg (fun φ => ModuleCat.Hom.hom φ (⟨x₃, hx₃⟩ : X.X₃.ρ.invariants))
      (shortComplexH0 X.X₃).zero
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at this
    exact this
  obtain ⟨z₃, hz₃⟩ := exists_iCycles_eq_of_d_eq_zero (cochainsComplex X.X₃) 0 c₃ hc₃
  obtain ⟨h₂, hh₂⟩ := hsurj (((cochainsComplex X.X₃).homologyπ 0).hom z₃)
  obtain ⟨z₂, rfl⟩ := homologyπ_surjective (cochainsComplex X.X₂) 0 h₂
  change (HomologicalComplex.homologyMap (cochainsMap X.g) 0).hom _ = _ at hh₂
  rw [homologyMap_homologyπ_apply] at hh₂
  have hcyc := homologyπ_zero_injective (cochainsComplex X.X₃) hh₂
  have hcyc' := congrArg ((cochainsComplex X.X₃).iCycles 0).hom hcyc
  rw [iCycles_cyclesMap_apply, hz₃] at hcyc'

  have hd₂ : (dLocallyConstant X.X₂ 0).hom (((cochainsComplex X.X₂).iCycles 0).hom z₂) = 0 := by
    rw [← cochainsComplex_d]
    exact iCycles_d_apply _ 0 (0 + 1) z₂
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).1 (shortComplexH0_exact X.X₂)
    (((cochainsComplex X.X₂).iCycles 0).hom z₂) hd₂
  refine ⟨v.1, v.2, ?_⟩
  have e1 : X.g.hom ((((cochainsComplex X.X₂).iCycles 0).hom z₂ :
      locallyConstantCochains X.X₂ 0).1 Fin.elim0) = x₃ :=
    congrArg (fun c : locallyConstantCochains X.X₃ 0 => c.1 Fin.elim0) hcyc'
  have e2 : v.1 = (((cochainsComplex X.X₂).iCycles 0).hom z₂ :
      locallyConstantCochains X.X₂ 0).1 Fin.elim0 :=
    congrArg (fun c : locallyConstantCochains X.X₂ 0 => c.1 Fin.elim0) hv
  rw [e2]
  exact e1

theorem isIso_δ_of_isZero (hX : X.ShortExact) (n : ℕ) (h₁ : IsZero (cohomology X.X₂ (n + 1)))
    (h₂ : IsZero (cohomology X.X₂ (n + 1 + 1))) : IsIso (δ hX (n + 1) (n + 1 + 1) rfl) := by
  have hm : Mono (δ hX (n + 1) (n + 1 + 1) rfl) :=
    (cohomology_exact₃ hX (n + 1) (n + 1 + 1) rfl).mono_g (h₁.eq_of_src _ _)
  have he : Epi (δ hX (n + 1) (n + 1 + 1) rfl) :=
    (cohomology_exact₁ hX (n + 1) (n + 1 + 1) rfl).epi_f (h₂.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Invariants

section ShortComplex

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

noncomputable def infResShortComplex (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := cohomology (A.quotientToInvariants N) (n + 1)
  X₂ := cohomology A (n + 1)
  X₃ := cohomology (Rep.res N.subtype A) (n + 1)
  f := cohomologyInfl A N (n + 1)
  g := cohomologyRes A N (n + 1)
  zero := cohomologyInfl_comp_cohomologyRes A N n

theorem infResShortComplex_zero_mono_exact :
    Mono (infResShortComplex A N 0).f ∧ (infResShortComplex A N 0).Exact := by
  refine ⟨(ModuleCat.mono_iff_injective _).2 (cohomologyInfl_one_injective A N), ?_⟩
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro h hh
  exact exists_cohomologyInfl_one_eq A N h hh

end ShortComplex

section Shift

variable [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

theorem shortExact_map_quotientToInvariants_coindShortComplex
    (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) :
    ((coindShortComplex A).map (Rep.quotientToInvariantsFunctor k N)).ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k (G ⧸ N)) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro x hx
    have hrk := ((coindShortComplex_shortExact A).exact.map
      (forget₂ (Rep.{u} k G) (ModuleCat k))).moduleCat_range_eq_ker
    have hx' : x.1 ∈ LinearMap.ker
        ((coindShortComplex A).map (forget₂ (Rep.{u} k G) (ModuleCat k))).g.hom :=
      congrArg Subtype.val hx
    rw [← hrk] at hx'
    obtain ⟨a, ha⟩ := hx'
    have ha' : (coindEmbedding A).hom a = x.1 := ha
    refine ⟨⟨a, fun s => coindEmbedding_injective A ?_⟩, Subtype.ext ha'⟩
    refine (Rep.hom_comm_apply (coindEmbedding A) (s : G) a).trans ?_
    rw [ha']
    exact x.2 s
  · exact (Rep.mono_iff_injective _).2 fun x y h =>
      Subtype.ext (coindEmbedding_injective A (congrArg Subtype.val h))
  · apply (Rep.epi_iff_surjective _).2
    intro y
    obtain ⟨x₂, hx₂, hg⟩ := exists_mem_invariants_map_eq
      (X := (coindShortComplex A).map (Rep.resFunctor N.subtype))
      (shortExact_map_res N (coindShortComplex_shortExact A)) h1 y.1 y.2
    exact ⟨⟨x₂, hx₂⟩, Subtype.ext hg⟩

instance isDiscreteRep_res_coindCokernel : IsDiscreteRep (Rep.res N.subtype (coindCokernel A)) :=
  isDiscreteRep_res_subtype _ N

variable [TotallyDisconnectedSpace G]

theorem infRes_step (hN : IsClosed (N : Set G)) (n : ℕ)
    (ih : ∀ (B : Rep.{u} k G) [IsDiscreteRep B],
      (∀ i, 0 < i → i < n + 1 → IsZero (cohomology (Rep.res N.subtype B) i)) →
        Mono (infResShortComplex B N n).f ∧ (infResShortComplex B N n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (cohomology (Rep.res N.subtype A) i)) :
    Mono (infResShortComplex A N (n + 1)).f ∧ (infResShortComplex A N (n + 1)).Exact := by
  have hX := coindShortComplex_shortExact A
  have hS := shortExact_map_res N hX
  have hQ := shortExact_map_quotientToInvariants_coindShortComplex A N (hA 1 one_pos (by omega))
  have hC : ∀ i, 0 < i → i < n + 1 →
      IsZero (cohomology (Rep.res N.subtype (coindCokernel A)) i) := by
    intro i hi hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS m (isZero_cohomology_res_discreteCoind (k := k) A N hN m)
      (isZero_cohomology_res_discreteCoind (k := k) A N hN (m + 1))
    exact (hA (m + 1 + 1) (by omega) (by omega)).of_iso (@asIso _ _ _ _ _ hδ)
  obtain ⟨ihm, ihe⟩ := ih (coindCokernel A) hC
  have hδQ := isIso_δ_of_isZero hQ n
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N n)
    (isZero_cohomology_quotientToInvariants_discreteCoind (k := k) A N (n + 1))
  have hδX := isIso_δ_of_isZero hX n (isZero_cohomology_discreteCoind (k := k) (G := G) (X := A) n)
    (isZero_cohomology_discreteCoind (k := k) (G := G) (X := A) (n + 1))
  have hδS := isIso_δ_of_isZero hS n (isZero_cohomology_res_discreteCoind (k := k) A N hN n)
    (isZero_cohomology_res_discreteCoind (k := k) A N hN (n + 1))
  have h1 := δ_comp_cohomologyInfl N hX hQ (n + 1) (n + 1 + 1) rfl
  have h2 := δ_comp_cohomologyRes N hX (n + 1) (n + 1 + 1) rfl
  let e : infResShortComplex (coindCokernel A) N n ≅ infResShortComplex A N (n + 1) :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ hδQ) (@asIso _ _ _ _ _ hδX) (@asIso _ _ _ _ _ hδS) h1 h2
  refine ⟨?_, (ShortComplex.exact_iff_of_iso e).1 ihe⟩
  have hf : e.inv.τ₁ ≫ (infResShortComplex (coindCokernel A) N n).f ≫ e.hom.τ₂ =
      (infResShortComplex A N (n + 1)).f := by
    rw [← Category.assoc, e.inv.comm₁₂, Category.assoc, ← ShortComplex.comp_τ₂, e.inv_hom_id,
      ShortComplex.id_τ₂, Category.comp_id]
  rw [← hf]
  infer_instance

theorem infResShortComplex_mono_exact (hN : IsClosed (N : Set G)) (n : ℕ) :
    ∀ (A : Rep.{u} k G) [IsDiscreteRep A],
      (∀ i, 0 < i → i < n + 1 → IsZero (cohomology (Rep.res N.subtype A) i)) →
        Mono (infResShortComplex A N n).f ∧ (infResShortComplex A N n).Exact := by
  induction n with
  | zero => exact fun A _ _ => infResShortComplex_zero_mono_exact A N
  | succ n ih => exact fun A _ hA => infRes_step A N hN n ih hA

variable {A N}

theorem cohomologyInfl_injective (hN : IsClosed (N : Set G)) {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res N.subtype A) i)) :
    Function.Injective (cohomologyInfl A N q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (ModuleCat.mono_iff_injective _).1 (infResShortComplex_mono_exact N hN n A hA).1

theorem range_cohomologyInfl_eq_ker_cohomologyRes (hN : IsClosed (N : Set G)) {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res N.subtype A) i)) :
    LinearMap.range (cohomologyInfl A N q).hom = LinearMap.ker (cohomologyRes A N q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (infResShortComplex_mono_exact N hN n A hA).2.moduleCat_range_eq_ker

end Shift

end GroundTheory.ProfCoh
end
