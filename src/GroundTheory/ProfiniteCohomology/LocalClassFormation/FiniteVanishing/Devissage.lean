module

public import GroundTheory.ProfiniteCohomology.EulerChar
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake
public import GroundTheory.ProfiniteCohomology.ClassFormations
public import GroundTheory.TateCohomology.TateTheorem
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.IntScalars

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

attribute [local instance 2000] Rep.hV2

section Exact

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cohomology_X₁_succ {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (r : ℕ)
    [Finite (cohomology S.X₃ r)] [Finite (cohomology S.X₂ (r + 1))] :
    Finite (cohomology S.X₁ (r + 1)) :=
  finite_of_exact (δ hS r (r + 1) rfl).hom.toAddMonoidHom
    (cohomologyMap S.f (r + 1)).hom.toAddMonoidHom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (cohomology_exact₁ hS r (r + 1) rfl))

end Exact

section Coker

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (i : A ⟶ B)

theorem range_hom_le_comap (g : G) :
    LinearMap.range i.hom.toLinearMap ≤ (LinearMap.range i.hom.toLinearMap).comap (B.ρ g) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨A.ρ g a, Rep.hom_comm_apply i g a⟩

def cokerShortComplex : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk i (Rep.mkQ B _ (range_hom_le_comap i)) (by
    ext a
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨a, rfl⟩)

theorem cokerShortComplex_shortExact (hi : Function.Injective i.hom) :
    (cokerShortComplex i).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective i).2 hi) ?_
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    intro b hb
    change Submodule.Quotient.mk (p := LinearMap.range i.hom.toLinearMap) b = 0 at hb
    obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hb
    exact ⟨a, ha⟩
  · exact (Rep.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

end Coker

section SubgroupOf

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (h : V ≤ U)

abbrev subgroupOfTransport (B : Rep.{u} k (V.subgroupOf U)) : Rep.{u} k V :=
  Rep.res (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom B

def subgroupOfTransportHom (B : Rep.{u} k (V.subgroupOf U)) :
    Rep.res (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (subgroupOfTransport h B) ⟶ B :=
  Rep.ofHom ⟨LinearMap.id, fun g => by
    ext b
    exact congrArg (fun τ => B.ρ τ b) ((Subgroup.subgroupOfEquivOfLe h).symm_apply_apply g)⟩

instance isDiscreteRep_subgroupOfTransport (B : Rep.{u} k (V.subgroupOf U)) [IsDiscreteRep B] :
    IsDiscreteRep (subgroupOfTransport h B) :=
  IsDiscreteRep.res (continuous_subgroupOfEquivOfLe_symm h) B

def cohomologySubgroupOfIso (B : Rep.{u} k (V.subgroupOf U)) [IsDiscreteRep B] (r : ℕ) :
    cohomology (subgroupOfTransport h B) r ≅ cohomology B r :=
  haveI := isIso_cohomologyMapAlong_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h)
    (continuous_subgroupOfEquivOfLe h) (continuous_subgroupOfEquivOfLe_symm h)
    (subgroupOfTransportHom h B) Function.bijective_id r
  asIso (cohomologyMapAlong (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (continuous_subgroupOfEquivOfLe h) (subgroupOfTransportHom h B) r)

end SubgroupOf

section Devissage

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cohomology_zero (M : Rep.{u} k G) [IsDiscreteRep M] [Finite M] :
    Finite (cohomology M 0) :=
  Finite.of_equiv _ (H0Iso M).toLinearEquiv.toEquiv.symm


omit [IsTopologicalGroup G] in
theorem exists_openSubgroup_le_fixing (U W₀ : OpenSubgroup G) (M : Rep.{u} k (U : Subgroup G))
    [IsDiscreteRep M] [Finite M] :
    ∃ (V : OpenSubgroup G) (_ : (V : Subgroup G) ≤ U), V ≤ W₀ ∧
      ∀ (g : (V : Subgroup G).subgroupOf U) (m : M), M.ρ g m = m := by
  let F : Subgroup (U : Subgroup G) := ⨅ m : M, stabilizer M.ρ m
  have hF : IsOpen (F : Set (U : Subgroup G)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun m => isOpen_stabilizer M m
  have hFG : IsOpen ((F.map (U : Subgroup G).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact U.isOpen.isOpenMap_subtype_val _ hF
  let V : OpenSubgroup G :=
    { toSubgroup := F.map (U : Subgroup G).subtype ⊓ W₀
      isOpen' := hFG.inter W₀.isOpen }
  refine ⟨V, fun x hx => ?_, fun x hx => hx.2, fun g m => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx.1
    exact y.2
  · have hg : ((g : (U : Subgroup G)) : G) ∈ F.map (U : Subgroup G).subtype :=
      (Subgroup.mem_subgroupOf.1 g.2).1
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 hg
    have hyg' : y = (g : (U : Subgroup G)) := Subtype.ext hyg
    rw [← hyg']
    exact (mem_stabilizer _ _ _).1 (Subgroup.mem_iInf.1 hy m)

theorem finite_cohomology_of_forall_trivial [CompactSpace G] (n R : ℕ) (W₀ : OpenSubgroup G)
    (h : ∀ V : OpenSubgroup G, V ≤ W₀ → ∀ (A : Rep.{u} (ULift.{u} ℤ) (V : Subgroup G))
      [IsDiscreteRep A] [Finite A], (∀ (g : (V : Subgroup G)) (a : A), A.ρ g a = a) →
        (∀ a : A, n • a = 0) → ∀ r ≤ R, Finite (cohomology A r))
    (U : OpenSubgroup G) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) : ∀ r ≤ R, Finite (cohomology M r) := by
  intro r
  induction r generalizing M with
  | zero => exact fun _ => finite_cohomology_zero M
  | succ r ih =>
    intro hr
    obtain ⟨V, hVU, hVW, hfix⟩ := exists_openSubgroup_le_fixing U W₀ M
    let V' : OpenSubgroup (U : Subgroup G) :=
      { toSubgroup := (V : Subgroup G).subgroupOf U
        isOpen' := V.isOpen.preimage continuous_subtype_val }
    let B : Rep.{u} (ULift.{u} ℤ) ((V : Subgroup G).subgroupOf U) :=
      Rep.res ((V' : Subgroup (U : Subgroup G))).subtype M
    let i := coindUnit (V' : Subgroup (U : Subgroup G)) M
    have hi : Function.Injective i.hom := by
      intro a b hab
      have h1 := congrArg (fun f : Rep.coind (V' : Subgroup (U : Subgroup G)).subtype B => f.1 1) hab
      simp only [i] at h1
      rw [coindUnit_hom_apply, coindUnit_hom_apply] at h1
      simpa using h1
    have hS := cokerShortComplex_shortExact i hi
    have : IsDiscreteRep B := isDiscreteRep_res_subtype M _
    have : IsDiscreteRep (cokerShortComplex i).X₁ := (inferInstance : IsDiscreteRep M)
    have : CompactSpace (U : Subgroup G) := compactSpace_openSubgroup U
    have hN2 : IsDiscreteRep (Rep.coind (V' : Subgroup (U : Subgroup G)).subtype
        (Rep.res (V' : Subgroup (U : Subgroup G)).subtype M)) :=
      @isDiscreteRep_coind (ULift.{u} ℤ) (U : Subgroup G) _ _ _ _ V' B (isDiscreteRep_res_subtype M _) _
    have : IsDiscreteRep (cokerShortComplex i).X₂ := hN2
    have : IsDiscreteRep (cokerShortComplex i).X₃ := isDiscreteRep_quotient _ _ _
    have : Finite B := inferInstanceAs (Finite M)
    have : Finite (cokerShortComplex i).X₂ :=
      finite_coind (k := ULift.{u} ℤ) (G := (U : Subgroup G)) V' B
    have : Finite (cokerShortComplex i).X₃ :=
      Finite.of_surjective (cokerShortComplex i).g.hom
        ((Rep.epi_iff_surjective _).1 hS.epi_g)
    have hNn : ∀ b : (cokerShortComplex i).X₂, n • b = 0 := by
      intro b
      apply Subtype.ext
      funext x
      exact hM (b.1 x)
    have hQ : ∀ q : (cokerShortComplex i).X₃, n • q = 0 := by
      intro q
      obtain ⟨b, rfl⟩ := (Rep.epi_iff_surjective _).1 hS.epi_g q
      rw [← map_nsmul, hNn b, map_zero]
    have : Finite (cohomology (cokerShortComplex i).X₃ r) := ih _ hQ (by omega)
    have : Finite (cohomology (cokerShortComplex i).X₂ (r + 1)) := by
      have : IsDiscreteRep (subgroupOfTransport hVU B) := isDiscreteRep_subgroupOfTransport hVU B
      have : Finite (cohomology (subgroupOfTransport hVU B) (r + 1)) :=
        h V hVW (subgroupOfTransport hVU B) (fun g a => hfix _ a) (fun a => hM a) (r + 1) hr
      exact Finite.of_equiv _
        (cohomologySubgroupOfIso hVU B (r + 1) ≪≫
          (shapiroIso V' B (r + 1)).symm).toLinearEquiv.toEquiv
    exact finite_cohomology_X₁_succ hS r

end Devissage

end GroundTheory.ProfCoh
end
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.FormationThree
section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.TateThree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem additive_addMonoidHom_int_eq_zero (f : Additive Γ →+ ℤ) : f = 0 := by
  refine AddMonoidHom.ext fun g => ?_
  have h : (Nat.card (Additive Γ) : ℤ) * f g = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Nat.card_pos.ne')

theorem isZero_groupCohomology_one_trivial_int :
    IsZero (groupCohomology (Rep.trivial ℤ Γ ℤ) 1) := by
  refine IsZero.of_iso ?_ (H1IsoOfIsTrivial (Rep.trivial ℤ Γ ℤ))
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun f g => ?_⟩
  rw [additive_addMonoidHom_int_eq_zero f, additive_addMonoidHom_int_eq_zero g]

theorem subsingleton_groupCohomology_three_of_tate_int (M : Rep ℤ Γ) (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) :
    Subsingleton (groupCohomology M 3) := by
  have hT1 : IsZero (tateCohomology (Rep.trivial ℤ Γ ℤ) ((1 : ℕ) : ℤ)) :=
    isZero_groupCohomology_one_trivial_int.of_iso
      ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ Γ ℤ))
  have hT3 : IsZero (tateCohomology M (((1 : ℕ) : ℤ) + 2)) :=
    hT1.of_iso (GroundTheory.GroupCoh.tateTheoremIsoTop M u h1 h2 h3 _).symm
  have e3 : (((1 : ℕ) : ℤ) + 2) = ((3 : ℕ) : ℤ) := by norm_num
  rw [e3] at hT3
  exact ModuleCat.subsingleton_of_isZero
    (hT3.of_iso ((TateCohomology.isoGroupCohomology 3).app M).symm)

theorem subsingleton_groupCohomology_three_of_tate (M : Rep.{0} (ULift.{0} ℤ) Γ)
    (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) :
    Subsingleton (groupCohomology M 3) := by
  have H := subsingleton_groupCohomology_three_of_tate_int (uliftIntToIntRep M)
    (groupCohomologyULiftIntAddEquiv M 2 u) (fun S => ?_) (fun S => ?_) (fun S y => ?_)
  · exact (groupCohomologyULiftIntAddEquiv M 3).injective.subsingleton
  · have : Subsingleton (groupCohomology (Rep.res S.subtype M) 1) :=
      ModuleCat.subsingleton_of_isZero (h1 S)
    have : Subsingleton (groupCohomology (uliftIntToIntRep (Rep.res S.subtype M)) 1) :=
      (groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 1).symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have e := groupCohomologyULiftIntAddEquiv_map_subtype M S 2 u
    change addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)) = Nat.card S
    rw [← e, AddEquiv.addOrderOf_eq]
    exact h2 S
  · obtain ⟨m, hm⟩ := h3 S ((groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 2).symm y)
    refine ⟨m, ?_⟩
    change y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)
    rw [← groupCohomologyULiftIntAddEquiv_map_subtype, ← map_zsmul, ← hm, AddEquiv.apply_symm_apply]

end GroundTheory.ProfCoh
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]


omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem exists_openSubgroup_subgroupOf_eq (U : OpenSubgroup G) (N : Subgroup (U : Subgroup G))
    (hN : IsOpen (N : Set (U : Subgroup G))) :
    ∃ V : OpenSubgroup G, V ≤ U ∧ (V : Subgroup G).subgroupOf U = N := by
  refine ⟨⟨N.map (U : Subgroup G).subtype, ?_⟩, Subgroup.map_subtype_le N, ?_⟩
  · exact U.isOpen.isOpenMap_subtype_val _ hN
  · exact Subgroup.comap_map_eq_self_of_injective (U : Subgroup G).subtype_injective N

variable {C : Rep.{0} (ULift.{0} ℤ) G} [IsDiscreteRep C] (F : ClassFormation C)


include F in
theorem ClassFormation.subsingleton_groupCohomology_three_quot (U : OpenSubgroup G)
    (N : Subgroup (U : Subgroup G)) [N.Normal] (hN : IsOpen (N : Set (U : Subgroup G))) :
    Subsingleton (groupCohomology
      ((Rep.res (U : Subgroup G).subtype C).quotientToInvariants N) 3) := by
  obtain ⟨V, hVU, rfl⟩ := exists_openSubgroup_subgroupOf_eq U N hN
  have : ((V : Subgroup G).subgroupOf U).FiniteIndex :=
    finiteIndex_openSubgroup (⟨_, hN⟩ : OpenSubgroup (U : Subgroup G))
  have : Finite ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) :=
    Subgroup.finite_quotient_of_finiteIndex
  let : Fintype ((U : Subgroup G) ⧸ (V : Subgroup G).subgroupOf U) := Fintype.ofFinite _
  exact subsingleton_groupCohomology_three_of_tate _ (F.groupFundamentalClass U V)
    (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).1) (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).2.1)
    (fun S => (F.tate_hypotheses (U := U) (V := V) hVU S).2.2)


include F in
theorem ClassFormation.subsingleton_cohomology_three (U : OpenSubgroup G) :
    Subsingleton (cohomology (Rep.res (U : Subgroup G).subtype C) 3) := by
  have h0 : ∀ z : cohomology (Rep.res (U : Subgroup G).subtype C) 3, z = 0 := fun z => by
    obtain ⟨W, w, rfl⟩ := exists_inflation_eq (Rep.res (U : Subgroup G).subtype C) 3 z
    have := F.subsingleton_groupCohomology_three_quot U (W : Subgroup (U : Subgroup G)) W.isOpen
    rw [Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

end GroundTheory.ProfCoh
end
end
