module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreSide
theorem UpperTheory.Reformulated.B.Qi36.aux :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) → ∃ (m : M), ∀ (g : Q), H.index • f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH
  by_cases h0 : H.index = 0
  · exact ⟨0, fun g => by simp [h0]⟩
  haveI : Finite (Q ⧸ H) := Nat.finite_of_card_ne_zero h0
  letI : Fintype (Q ⧸ H) := Fintype.ofFinite _
  have key : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hm : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [hH _ hm, map_zero, add_zero, mul_inv_cancel_left] at h1
    exact h1.symm
  have step : ∀ (g : Q) (x : Q ⧸ H), f (g • x).out = f g + π g (f x.out) := by
    intro g x
    rw [← hf]
    apply key
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe, QuotientGroup.out_eq']
  refine ⟨-∑ x : Q ⧸ H, f x.out, fun g => ?_⟩
  have hs : ∑ x : Q ⧸ H, f (g • x).out = ∑ x : Q ⧸ H, f x.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun x : Q ⧸ H => f x.out)
  simp only [step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum] at hs
  rw [Subgroup.index, Nat.card_eq_fintype_card, map_neg, sub_neg_eq_add,
    eq_sub_of_add_eq hs]
  abel
end

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem aux {R Q M : Type} [CommRing R] [Group Q] [AddCommGroup M] [Module R M]
    (π : Representation R Q M) (H : Subgroup Q) (f : Q → M) (hf : ∀ g h, f (g * h) = f g + π g (f h))
    (h0 : ∀ u ∈ H, f u = 0) : ∃ m, ∀ g, H.index • f g = π g m - m :=
  _root_.UpperTheory.Reformulated.B.Qi36.aux π H f hf h0

theorem UpperTheory.V.Base.kerResSmul :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (x : H1U ρ U), resU ρ h x = 0 → U'.relIndex U • x = 0 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
  obtain ⟨s, hs⟩ := aux (ρ.comp U.subtype : Representation R U M) (U'.subgroupOf U)
    (fun u => z.1 u - (ρ u m - m))
    (fun g k => by
      have e : z.1 (g * k) = z.1 g + ρ g (z.1 k) := z.2.2 g k
      show z.1 (g * k) - (ρ ((g : G) * k) m - m) = z.1 g - (ρ g m - m) + ρ g (z.1 k - (ρ k m - m))
      rw [e, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel)
    (fun u hu => sub_eq_zero.2 (hm ⟨u.1, hu⟩))
  have e0 : U'.relIndex U • (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk (U'.relIndex U • z) :=
    (map_nsmul (Submodule.mkQ _) _ z).symm
  rw [e0, Submodule.Quotient.mk_eq_zero]
  refine (mem_coboundaries1 _ _).2 ⟨s + U'.relIndex U • m, fun g => ?_⟩
  have e : U'.relIndex U • (z.1 g - (ρ g m - m)) = ρ g s - s := hs g
  show U'.relIndex U • z.1 g = ρ g (s + U'.relIndex U • m) - (s + U'.relIndex U • m)
  rw [smul_sub, smul_sub, sub_eq_iff_eq_add] at e
  rw [e, map_add (f := _), map_nsmul]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenComp
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.length R B ≤ Module.length R C + Module.length R A := by
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [e, add_comm]
  refine add_le_add (Module.length_le_of_injective _ (Submodule.subtype_injective _)) ?_
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
    (Module.length_le_of_surjective _ f.surjective_rangeRestrict)

theorem UpperTheory.V.Base.lenComp :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] (a b : Module.End R N),
      Module.length R (LinearMap.ker (a * b)) ≤ Module.length R (LinearMap.ker a) + Module.length R (LinearMap.ker b) ∧
      Module.length R (N ⧸ LinearMap.range (a * b)) ≤ Module.length R (N ⧸ LinearMap.range a) + Module.length R (N ⧸ LinearMap.range b) := by
  intro R N _ _ _ a b
  constructor
  · have h1 : LinearMap.ker b ≤ LinearMap.ker (a * b) := fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [Module.End.mul_apply, hx, map_zero]
    have h2 : ∀ x ∈ LinearMap.ker (a * b), b x ∈ LinearMap.ker a := fun x hx => hx
    refine length_le_of_exact (Submodule.inclusion h1) (LinearMap.restrict b h2) fun x hx => ?_
    exact ⟨⟨x.1, congrArg Subtype.val hx⟩, rfl⟩
  · have h1 : LinearMap.range b ≤ (LinearMap.range (a * b)).comap a := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have h2 : LinearMap.range (a * b) ≤ (LinearMap.range a).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩
      exact ⟨b y, rfl⟩
    refine length_le_of_exact (Submodule.mapQ _ _ a h1) (Submodule.mapQ _ _ LinearMap.id h2) fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, hy]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private noncomputable def h1MapOfAgreeOnSubgroup (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) : H1U ρ U →ₗ[R] H1U ρ' U :=
  pairH1DecompositionMap _ _ (MonoidHom.id U) continuous_id LinearMap.id continuous_id fun u m => h u m

private theorem sameH1_mk (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ' U, h1MapOfAgreeOnSubgroup ρ ρ' U h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = z.1 u := ⟨_, rfl, fun _ => rfl⟩

private theorem sameH1_involutive (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (h' : ∀ (u : U) m, ρ' u m = ρ u m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ' ρ U h' (h1MapOfAgreeOnSubgroup ρ ρ' U h x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem sameH1_mem_localSelmer (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) (x : H1U ρ U) (hx : x ∈ LocSel ρ U 𝒟) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := sameH1_mk ρ ρ' U h z
  rw [e]
  rw [mk_mem_locSel] at hx ⊢
  intro D hD
  obtain ⟨m, hm⟩ := hx D hD
  exact ⟨m, fun u hu => by rw [f, hm u hu, h]⟩

private noncomputable def sameSel (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟 :=
  LinearEquiv.ofLinear ((h1MapOfAgreeOnSubgroup ρ ρ' U h).restrict (sameH1_mem_localSelmer ρ ρ' U h 𝒟))
    ((h1MapOfAgreeOnSubgroup ρ' ρ U fun u m => (h u m).symm).restrict (sameH1_mem_localSelmer ρ' ρ U _ 𝒟))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ' ρ U _ h x.1))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ ρ' U h _ x.1))

private theorem sameH1_conjugation_scalar [IsTopologicalGroup G] [DiscreteTopology M] (ρ ρ' : Representation R G M)
    (U : Subgroup G) [U.Normal] (h : ∀ (u : U) m, ρ u m = ρ' u m) (g : G) (c : R)
    (hg : ∀ m, ρ g m = c • ρ' g m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h (conjRep ρ U g x) = c • conjRep ρ' U g (h1MapOfAgreeOnSubgroup ρ ρ' U h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := sameH1_mk ρ ρ' U h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ' U g z₁
  obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U g z
  obtain ⟨z₄, e₄, f₄⟩ := sameH1_mk ρ ρ' U h z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  show z₄.1 u = c • z₂.1 u
  rw [f₄, f₃, f₂, f₁, hg]

end

theorem UpperTheory.V.Base.selTwist :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) →
      ∀ (U : Subgroup G) [U.Normal], (∀ u ∈ U, θ u = 1) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∃ Φ : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟, ∀ g x, Φ (selRep ρ U h𝒟 g x) = ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (Φ x)) ∧
      ∀ (W : Subgroup G) (φ : W →* Rˣ), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)) = Module.length R (selEig ρ' U h𝒟 W φ) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hθ U _ hU 𝒟 h𝒟
  have h : ∀ (u : U) m, ρ u m = ρ' u m := fun u m => by
    rw [hθ, hU u u.2, Units.val_one, one_smul]
  have hΦ : ∀ g x, sameSel ρ ρ' U h 𝒟 (selRep ρ U h𝒟 g x) =
      ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (sameSel ρ ρ' U h 𝒟 x) := fun g x =>
    Subtype.ext (sameH1_conjugation_scalar ρ ρ' U h g _ (hθ g) x.1)
  refine ⟨⟨_, hΦ⟩, fun W φ => ?_⟩
  generalize sameSel ρ ρ' U h 𝒟 = Φ at hΦ
  have key : ∀ x, x ∈ selEig ρ U h𝒟 W (θ.comp W.subtype * φ) ↔ Φ x ∈ selEig ρ' U h𝒟 W φ := by
    intro x
    rw [mem_eig, mem_eig]
    refine forall_congr' fun w => ?_
    show selRep ρ U h𝒟 w x = ((θ w * φ w : Rˣ) : R) • x ↔ selRep ρ' U h𝒟 w (Φ x) = ((φ w : Rˣ) : R) • Φ x
    rw [← Φ.injective.eq_iff, hΦ, map_smul, Units.val_mul, mul_smul]
    exact (Units.isUnit (θ w)).smul_left_cancel
  have hmap : (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)).map (Φ : _ →ₗ[R] _) = selEig ρ' U h𝒟 W φ := by
    ext y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [← key]
    exact ⟨fun ⟨x', hx', e⟩ => Φ.injective e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  exact (Φ.ofSubmodules _ _ hmap).length_eq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ExistsO
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.existsO :
    ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n], ∃ O : Subalgebra ℤ_[l] (PadicAlgCl l),
      IsDiscreteValuationRing O ∧ Module.Finite ℤ_[l] O ∧ HasEnoughRootsOfUnity O n := by
  intro l _ n _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨(integralClosure ℤ_[l] K).map f, ?_, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  · exact Module.Finite.equiv e.toLinearEquiv
  · have hz : ζ ∈ K := IntermediateField.mem_adjoin_simple_self _ _
    have hmem : ζ ∈ (integralClosure ℤ_[l] K).map f :=
      ⟨⟨ζ, hz⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩
    refine ⟨⟨⟨ζ, hmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenLeAdd
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_add {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) :
    Module.length R A ≤ Module.length R B + Module.length R (LinearMap.ker k) := by
  have h1 : Module.length R A = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _)
      g.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have h2 : Module.length R (LinearMap.range g) ≤ Module.length R B :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)
  have h3 : Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.ker k) :=
    Module.length_le_of_injective (j.restrict (p := LinearMap.ker g) (q := LinearMap.ker k) fun x hx => hk x hx)
      fun x y e => Subtype.ext (hj (congrArg Subtype.val e))
  rw [h1, add_comm]
  exact add_le_add h2 h3

private theorem len_sub {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) (P : Submodule R A) (Q : Submodule R B)
    (hPQ : ∀ x ∈ P, g x ∈ Q) :
    Module.length R P ≤ Module.length R Q + Module.length R (LinearMap.ker k) :=
  len_le_add (g.restrict hPQ) (j.comp P.subtype) k (hj.comp (Submodule.injective_subtype P))
    fun x hx => hk x.1 (congrArg Subtype.val hx)

theorem UpperTheory.V.Base.selUp :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U' 𝒟) + Module.length R (LinearMap.ker (resU ρ h)) ∧
      (∀ [U'.Normal], Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (selEig ρ U' h𝒟 U 1) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      (∀ [U'.Normal] [U.Normal] (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W ψ) ≤ Module.length R (selEig ρ U' h𝒟 W ψ) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      ∀ [U'.Normal] [U.Normal] (g : G) (s : R), Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) ≤
        Module.length R (Module.End.eigenspace (selRep ρ U' h𝒟 g) s) + Module.length R (LinearMap.ker (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 h𝒟
  have hj := Submodule.injective_subtype (LocSel ρ U 𝒟)
  have hk : ∀ x, selRes ρ h 𝒟 x = 0 → resU ρ h ((LocSel ρ U 𝒟).subtype x) = 0 :=
    fun x hx => congrArg Subtype.val hx
  refine ⟨len_le_add (selRes ρ h 𝒟) _ _ hj hk, ?_, ?_, ?_⟩
  · intro _
    have hm : ∀ x, selRes ρ h 𝒟 x ∈ selEig ρ U' h𝒟 U 1 := fun x => by
      rw [selEig, eig_one]
      intro g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    exact len_le_add ((selRes ρ h 𝒟).codRestrict _ hm) _ _ hj fun x hx => hk x (congrArg Subtype.val hx)
  · intro _ _ W ψ
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [mem_eig] at hx ⊢
    intro g
    have e : selRep ρ U h𝒟 g.1 x = ((ψ g : Rˣ) : R) • x := hx g
    show selRep ρ U' h𝒟 g.1 _ = _
    rw [← selRes_selRep, e, map_smul]
  · intro _ _ g s
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← selRes_selRep, hx, map_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenCokerLe
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_ker_eq_coker {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (A ⧸ LinearMap.range f) = Module.length R (LinearMap.ker f) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(f.quotKerEquivRange).length_eq] at h2
  have h3 : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h1
    exact hfin h1
  rw [h1, add_comm] at h2
  exact (WithTop.add_right_inj h3).1 h2

private theorem len_sup_ne_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (S T : Submodule R A) (hS : Module.length R S ≠ ⊤) (hT : Module.length R T ≠ ⊤) :
    Module.length R (S ⊔ T : Submodule R A) ≠ ⊤ := by
  have h := Module.length_le_of_surjective (S.subtype.coprod T.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.length_prod] at h
  exact ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hS, hT⟩) h

private theorem len_map_le {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (a : R)
    (F : Submodule R N) (hF : Module.length R F ≠ ⊤) :
    Module.length R (F.map (LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))).mkQ) ≤
      Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  let g : F →ₗ[R] F.map P.mkQ := P.mkQ.submoduleMap F
  have hg : Function.Surjective g := LinearMap.submoduleMap_surjective _ _
  have hle : LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    show P.mkQ (a • (x : N)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hg' : Function.Surjective (Submodule.liftQ _ g hle) := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hg').trans ?_
  rw [len_ker_eq_coker _ hF]
  refine Module.length_le_of_injective
    (F.subtype.restrict (p := LinearMap.ker (a • (LinearMap.id : F →ₗ[R] F)))
      (q := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) ?_) ?_
  · intro x hx
    exact congrArg Subtype.val hx
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem UpperTheory.V.Base.lenCokerLe :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N], (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → ∀ a : R,
      Module.length R (N ⧸ LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))) ≤ Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  intro R N _ _ _ hN a
  by_contra hlt
  rw [not_le] at hlt
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  set K := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N)) with hK
  have key : ∀ k : ℕ, ∃ F : Submodule R N, Module.length R F ≠ ⊤ ∧
      (k : ℕ∞) ≤ Module.length R (F.map P.mkQ) := by
    intro k
    induction k with
    | zero => exact ⟨⊥, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hk⟩ := ih
      have h1 : Module.length R (F.map P.mkQ) ≤ Module.length R K := len_map_le a F hF
      have h2 : F.map P.mkQ ≠ ⊤ := by
        intro h
        rw [h, Module.length_top] at h1
        exact absurd hlt (not_lt.2 h1)
      obtain ⟨y, hy⟩ : ∃ y, y ∉ F.map P.mkQ := by
        by_contra hh
        exact h2 (eq_top_iff.2 fun y _ => by_contra fun h => hh ⟨y, h⟩)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      refine ⟨F ⊔ Submodule.span R {x}, len_sup_ne_top _ _ hF (hN x), ?_⟩
      have h3 : F.map P.mkQ < (F ⊔ Submodule.span R {x}).map P.mkQ := by
        refine lt_of_le_of_ne (Submodule.map_mono le_sup_left) fun h => hy ?_
        rw [h]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      have h4 : Order.height (F.map P.mkQ) < ⊤ := by
        rw [← Module.length_submodule]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hlt le_top)
      have h5 := Order.height_strictMono h3 h4
      rw [← Module.length_submodule, ← Module.length_submodule] at h5
      rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hk h5)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lt_of_lt_of_le hlt le_top).ne
  obtain ⟨F, hF, hk⟩ := key (n + 1)
  have h := hk.trans (len_map_le a F hF)
  rw [← hK, ← hn] at h
  exact absurd (Nat.cast_le.1 h) (by omega)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem exists_inj_of_ker_eq {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (p : A →ₗ[R] B) (q : A →ₗ[R] C)
    (hp : Function.Surjective p) (hk : ∀ a, p a = 0 ↔ q a = 0) :
    ∃ φ : B →ₗ[R] C, Function.Injective φ := by
  have hle : LinearMap.ker p ≤ LinearMap.ker q := fun a ha => (hk a).1 ha
  have hle' : LinearMap.ker q ≤ LinearMap.ker p := fun a ha => (hk a).2 ha
  refine ⟨(LinearMap.ker p).liftQ q hle ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap, ?_⟩
  rw [LinearMap.coe_comp]
  exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ q hle hle')).comp
    (p.quotKerEquivOfSurjective hp).symm.injective

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]

private theorem cocycle_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) {γ : G} (hγ : γ ∈ U)
    (hU : U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure) (z : Z1U ρ U)
    (h1 : ∀ u : U, u.1 ∈ U' → z.1 u = 0) (h2 : z.1 ⟨γ, hγ⟩ = 0) (u : U) : z.1 u = 0 := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.2
  have hone : z.1 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at e
    simpa using e
  let K : Subgroup U :=
    { carrier := {x | z.1 x = 0}
      mul_mem' := fun {a b} ha hb => by
        show z.1 (a * b) = 0
        rw [hcoc, ha, hb, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show z.1 a⁻¹ = 0
        have e := hcoc a⁻¹ a
        rw [inv_mul_cancel, hone, ha, map_zero, add_zero] at e
        exact e.symm }
  have hS : Subgroup.zpowers γ ⊔ U' ≤ K.map U.subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨γ, hγ⟩, h2, rfl⟩
    · intro x hx
      exact ⟨⟨x, h hx⟩, h1 ⟨x, h hx⟩ hx, rfl⟩
  have hu := hU u.2
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hu
  have hV : IsOpen (z.1 ⁻¹' {z.1 u}) := hcont.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.1 hV
  have huO : u.1 ∈ O := by
    have : u ∈ Subtype.val ⁻¹' O := by rw [hOV]; rfl
    exact this
  obtain ⟨s, hsO, hsS⟩ := mem_closure_iff.1 hu O hO huO
  obtain ⟨⟨s', hs'U⟩, hzs, rfl⟩ := hS hsS
  have hmem : (⟨s', hs'U⟩ : U) ∈ Subtype.val ⁻¹' O := hsO
  rw [hOV] at hmem
  have e : z.1 ⟨s', hs'U⟩ = z.1 u := hmem
  rw [← e]
  exact hzs

private noncomputable def cob (ρ : Representation R G M) (hρ : ContAction ρ) (U : Subgroup G) (m : M) : Z1U ρ U :=
  ⟨d0 (ρ.comp U.subtype : Representation R U M) m, coboundaries_le_cocycles (ρ.comp U.subtype : Representation R U M)
    (Continuous.comp (f := fun p : U × M => ((p.1.1, p.2) : G × M)) hρ (by fun_prop)) ⟨m, rfl⟩⟩

private def Z0 (ρ : Representation R G M) (U' U : Subgroup G) : Submodule R (Z1U ρ U) where
  carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb u hu => by
    show a.1 u + b.1 u = 0
    rw [ha u hu, hb u hu, add_zero]
  smul_mem' := fun c a ha u hu => by
    show c • a.1 u = 0
    rw [ha u hu, smul_zero]

private theorem cocycle_zero_mem_invariants (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) [hN : (U'.subgroupOf U).Normal]
    (g : U) (z : Z0 ρ U' U) : z.1.1 g ∈ H0U ρ U' := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.1.2
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  intro v
  let v' : U := ⟨v.1, h v.2⟩
  have hw : g⁻¹ * v' * g ∈ U'.subgroupOf U := by
    have := hN.conj_mem v' (by rw [Subgroup.mem_subgroupOf]; exact v.2) g⁻¹
    simpa using this
  rw [Subgroup.mem_subgroupOf] at hw
  have hzw : z.1.1 (g⁻¹ * v' * g) = 0 := z.2 _ hw
  have hzv : z.1.1 v' = 0 := z.2 v' v.2
  have e1 := hcoc v' g
  have e2 := hcoc g (g⁻¹ * v' * g)
  rw [show g * (g⁻¹ * v' * g) = v' * g by group, hzw, map_zero, add_zero] at e2
  rw [hzv, zero_add, e2] at e1
  exact e1.symm

end

theorem UpperTheory.V.Base.kerResGen1 :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure → ∀ T : H0U ρ U' →ₗ[R] H0U ρ U', (∀ m, (T m : M) = ρ γ m - m) →
      ∃ φ : LinearMap.ker (resU ρ h) →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T), Function.Injective φ := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h hN γ hγ hU T hT
  have hcobv : ∀ (m : M) (u : U), (cob ρ hρ U m).1 u = ρ u m - m := fun m u => rfl
  let ev : Z0 ρ U' U →ₗ[R] H0U ρ U' :=
    { toFun := fun a => ⟨a.1.1 ⟨γ, hγ⟩, cocycle_zero_mem_invariants ρ h ⟨γ, hγ⟩ a⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  let q : Z0 ρ U' U →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T) := (LinearMap.range T).mkQ ∘ₗ ev
  let p0 : Z0 ρ U' U →ₗ[R] H1U ρ U :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (MonoidHom.comp ρ U.subtype))).mkQ ∘ₗ (Z0 ρ U' U).subtype
  have hp0 : ∀ a, p0 a ∈ LinearMap.ker (resU ρ h) := by
    intro a
    rw [LinearMap.mem_ker]
    refine (resU_mk_eq_zero ρ h a.1).2 ⟨0, fun u => ?_⟩
    rw [map_zero, sub_zero]
    exact a.2 _ u.2
  let p : Z0 ρ U' U →ₗ[R] LinearMap.ker (resU ρ h) := LinearMap.codRestrict _ p0 hp0
  have hp : Function.Surjective p := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 (LinearMap.mem_ker.1 hx)
    refine ⟨⟨z - cob ρ hρ U m, fun u hu => ?_⟩, ?_⟩
    · show z.1 u - (cob ρ hρ U m).1 u = 0
      rw [hcobv]
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · apply Subtype.ext
      show Submodule.Quotient.mk (z - cob ρ hρ U m) = Submodule.Quotient.mk z
      rw [mk_eq_mk]
      refine ⟨-m, fun u => ?_⟩
      show z.1 u - (cob ρ hρ U m).1 u - z.1 u = ρ u (-m) - -m
      rw [hcobv, map_neg]
      abel
  have hk : ∀ a, p a = 0 ↔ q a = 0 := by
    intro a
    have hpa : p a = 0 ↔ ∃ m : M, ∀ u : U, a.1.1 u - (0 : Z1U ρ U).1 u = ρ u m - m := by
      rw [Subtype.ext_iff]
      show Submodule.Quotient.mk a.1 = (0 : H1U ρ U) ↔ _
      rw [← Submodule.Quotient.mk_zero, mk_eq_mk]
    have hqa : q a = 0 ↔ ∃ n : H0U ρ U', (T n : M) = a.1.1 ⟨γ, hγ⟩ := by
      show Submodule.Quotient.mk (ev a) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
    rw [hpa, hqa]
    constructor
    · rintro ⟨m, hm⟩
      have hmH : m ∈ H0U ρ U' := by
        rw [mem_riemannRochSpace_iff_regularAt_everywhere]
        intro v
        have e := hm ⟨v.1, h v.2⟩
        rw [a.2 ⟨v.1, h v.2⟩ v.2] at e
        exact (sub_eq_zero.1 (by simpa using e.symm))
      refine ⟨⟨m, hmH⟩, ?_⟩
      rw [hT]
      simpa using (hm ⟨γ, hγ⟩).symm
    · rintro ⟨n, hn⟩
      rw [hT] at hn
      have hnH := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 n.2
      have hv1 : ∀ u : U, u.1 ∈ U' → (a.1 - cob ρ hρ U n.1).1 u = 0 := by
        intro u hu
        show a.1.1 u - (cob ρ hρ U n.1).1 u = 0
        rw [hcobv, a.2 u hu]
        have e := hnH ⟨u.1, hu⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at e
        simp [e]
      have hv2 : (a.1 - cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0 := by
        show a.1.1 ⟨γ, hγ⟩ - (cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0
        rw [hcobv, ← hn]
        simp
      refine ⟨n.1, fun u => ?_⟩
      have hz := cocycle_eq_zero ρ h hγ hU (a.1 - cob ρ hρ U n.1) hv1 hv2 u
      have e : a.1.1 u - (cob ρ hρ U n.1).1 u = 0 := hz
      rw [hcobv] at e
      simpa using sub_eq_zero.1 e
  exact exists_inj_of_ker_eq p q hp hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBase
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContinuousCocycleMapApply
noncomputable section

open ReciprocityTheory.Gal TensorProduct

namespace UpperTheory.V.Base

section Alg

variable {R O ι N N' : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module O N'] [Module R N'] [IsScalarTower R O N']

def coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') : (ι → N) →ₗ[R] N' where
  toFun x := ∑ i, b i • j (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, smul_comm r]

theorem coordSum_apply (b : Module.Basis ι R O) (j : N →ₗ[R] N') (x : ι → N) :
    coordSum b j x = ∑ i, b i • j (x i) := rfl

theorem isBaseChange_iff_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') :
    IsBaseChange O j ↔ Function.Bijective (coordSum b j) := by
  classical
  let e : (ι → N) ≃ₗ[R] O ⊗[R] N :=
    (Finsupp.linearEquivFunOnFinite R N ι).symm ≪≫ₗ (TensorProduct.equivFinsuppOfBasisLeft b).symm
  have he : ∀ x, e x = ∑ i, b i ⊗ₜ x i := fun x => by
    simp [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  unfold IsBaseChange IsTensorProduct
  rw [← Function.Bijective.of_comp_iff _ e.bijective]
  refine iff_of_eq (congrArg _ (funext fun x => ?_))
  simp [he, coordSum_apply]

theorem isBaseChange_restrict (b : Module.Basis ι R O) {j : N →ₗ[R] N'} (hj : IsBaseChange O j)
    (P : Submodule R N) (P' : Submodule O N') (h : ∀ x, coordSum b j x ∈ P' ↔ ∀ i, x i ∈ P)
    (j' : P →ₗ[R] P') (hj' : ∀ x, (j' x : N') = j x) : IsBaseChange O j' := by
  rw [isBaseChange_iff_coordSum b] at hj ⊢
  have e : ∀ x : ι → P, (coordSum b j' x : N') = coordSum b j fun i => x i := fun x => by
    simp [coordSum_apply, hj']
  refine ⟨fun x y hxy => funext fun i => Subtype.ext ?_, fun y => ?_⟩
  · exact congrFun (hj.1 ((e x).symm.trans ((congrArg Subtype.val hxy).trans (e y)))) i
  · obtain ⟨x, hx⟩ := hj.2 y
    exact ⟨fun i => ⟨x i, (h x).1 (hx ▸ y.2) i⟩, Subtype.ext ((e _).trans hx)⟩

theorem length_of_isBaseChange [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Flat R O]
    {j : N →ₗ[R] N'} (hj : IsBaseChange O j) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  rw [← hj.equiv.length_eq, IsLocalRing.length_baseChange]

theorem map_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') (f : N → N) (f' : N' →ₗ[O] N')
    (h : ∀ x, j (f x) = f' (j x)) (x : ι → N) : f' (coordSum b j x) = coordSum b j fun i => f (x i) := by
  simp [coordSum_apply, h]

end Alg

section Coh

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M']
  [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (j : M →ₗ[R] M') (hj : ∀ g m, j (ρ g m) = ρ' g (j m))
  (U : Subgroup G)

def continuousCocycleMap : Z1U ρ U →ₗ[R] Z1U ρ' U where
  toFun z := ⟨fun u => j (z.1 u), (continuous_of_discreteTopology (f := j)).comp z.2.1, fun g h => by
    show j _ = j _ + ρ' g (j _)
    rw [z.2.2, map_add (f := _), ← hj]
    rfl⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add j _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul j _ _)

theorem continuousCocycleMap_apply (z : Z1U ρ U) (u : U) : (continuousCocycleMap ρ ρ' j hj U z).1 u = j (z.1 u) := rfl

def h1Map : H1U ρ U →ₗ[R] H1U ρ' U :=
  Submodule.liftQ _ (((Submodule.mkQ _).restrictScalars R).comp (continuousCocycleMap ρ ρ' j hj U)) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨j m, fun u => ?_⟩)
    have e : z.1 u = ρ u m - m := hm u
    show j (z.1 u) = ρ' u (j m) - j m
    rw [e, map_sub, hj]

theorem h1Map_mk (z : Z1U ρ U) :
    h1Map ρ ρ' j hj U (Submodule.Quotient.mk z) = Submodule.Quotient.mk (continuousCocycleMap ρ ρ' j hj U z) := rfl

theorem h1Map_mem_locSel (𝒟 : Set (Subgroup G)) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    h1Map ρ ρ' j hj U x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [h1Map_mk, mk_mem_locSel]
  intro D hD
  obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
  exact ⟨j m, fun u hu => by rw [continuousCocycleMap_apply, hm u hu, map_sub, hj]⟩

def selMap (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 →ₗ[R] LocSel ρ' U 𝒟 where
  toFun x := ⟨h1Map ρ ρ' j hj U x, h1Map_mem_locSel ρ ρ' j hj U 𝒟 x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

variable {ι : Type} [Fintype ι] (b : Module.Basis ι R O)

theorem coordSum_z1Map (z : ι → Z1U ρ U) (u : U) :
    (coordSum b (continuousCocycleMap ρ ρ' j hj U) z).1 u = coordSum b j fun i => (z i).1 u := by
  simp [coordSum_apply, continuousCocycleMap_apply]

theorem coordSum_h1Map (z : ι → Z1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) (fun i => Submodule.Quotient.mk (z i)) =
      Submodule.Quotient.mk (coordSum b (continuousCocycleMap ρ ρ' j hj U) z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordSum_apply, h1Map_mk, ← Submodule.mkQ_apply, map_sum, map_smul]
  rfl

include hj in
theorem exists_cob_iff (hb : IsBaseChange O j) (p : U → Prop) (z : ι → U → M) :
    (∃ m', ∀ u : U, p u → coordSum b j (fun i => z i u) = ρ' u m' - m') ↔
      ∀ i, ∃ m, ∀ u : U, p u → z i u = ρ u m - m := by
  rw [isBaseChange_iff_coordSum b] at hb
  have e : ∀ (u : U) (m : ι → M), ρ' u (coordSum b j m) - coordSum b j m = coordSum b j fun i => ρ u (m i) - m i :=
    fun u m => by
      rw [map_coordSum b j (ρ u) (ρ' u) (hj u), ← map_sub]
      rfl
  constructor
  · rintro ⟨m', hm⟩ i
    obtain ⟨m, rfl⟩ := hb.2 m'
    exact ⟨m i, fun u hu => congrFun (hb.1 ((hm u hu).trans (e u m))) i⟩
  · intro h
    choose m hm using h
    exact ⟨coordSum b j m, fun u hu => by rw [e]; exact congrArg _ (funext fun i => hm i u hu)⟩

theorem coordSum_z1Map_surjective [DiscreteTopology M'] (hb : IsBaseChange O j) :
    Function.Surjective (coordSum b (continuousCocycleMap ρ ρ' j hj U)) := by
  rw [isBaseChange_iff_coordSum b] at hb
  intro y
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ m, coordSum b j (e.symm m) = m := e.apply_symm_apply
  refine ⟨fun i => ⟨fun u => e.symm (y.1 u) i,
    (continuous_of_discreteTopology (f := fun m => e.symm m i)).comp y.2.1, fun g h => ?_⟩, ?_⟩
  · have : e.symm (y.1 (g * h)) = e.symm (y.1 g) + fun i => ρ g (e.symm (y.1 h) i) := by
      apply hb.1
      rw [map_add (f := _), ← map_coordSum b j (ρ g) (ρ' g) (hj g), he, he, he]
      exact y.2.2 g h
    exact congrFun this i
  · exact Subtype.ext (funext fun u => (coordSum_z1Map ρ ρ' j hj U b _ u).trans (he _))

include b in
private theorem isBaseChange_h1Map' [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) := by
  rw [isBaseChange_iff_coordSum b]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
    obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
    rw [coordSum_h1Map] at hx
    obtain ⟨m', hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    funext i
    obtain ⟨m, hm⟩ := (exists_cob_iff ρ ρ' j hj U b hb (fun _ => True) fun i => (z i).1).1
      ⟨m', fun u _ => (coordSum_z1Map ρ ρ' j hj U b z u).symm.trans (hm' u)⟩ i
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun u => hm u trivial⟩)
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, rfl⟩ := coordSum_z1Map_surjective ρ ρ' j hj U b hb y
    exact ⟨_, coordSum_h1Map ρ ρ' j hj U b z⟩

theorem coordSum_mem_locSel (hb : IsBaseChange O j) (𝒟 : Set (Subgroup G)) (x : ι → H1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) x ∈ LocSel ρ' U 𝒟 ↔ ∀ i, x i ∈ LocSel ρ U 𝒟 := by
  choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
  obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
  rw [coordSum_h1Map]
  simp only [mk_mem_locSel, coordSum_z1Map]
  rw [forall_comm]
  refine forall_congr' fun D => ?_
  rw [forall_comm]
  exact imp_congr_right fun _ => exists_cob_iff ρ ρ' j hj U b hb (fun u => u.1 ∈ D) fun i => (z i).1


omit [Fintype ι] in
theorem isBaseChange_h1Map [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) :=
  isBaseChange_h1Map' ρ ρ' j hj U (Module.Free.chooseBasis R O) hb


omit [Fintype ι] in
theorem isBaseChange_selMap [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j)
    (𝒟 : Set (Subgroup G)) : IsBaseChange O (selMap ρ ρ' j hj U 𝒟) :=
  isBaseChange_restrict (Module.Free.chooseBasis R O) (isBaseChange_h1Map ρ ρ' j hj U hb) _ _
    (coordSum_mem_locSel ρ ρ' j hj U _ hb 𝒟) _ fun _ => rfl

end Coh

end UpperTheory.V.Base

end
end

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel ρ' U 𝒟) = Module.length R (LocSel ρ U 𝒟) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hb hj U 𝒟
  exact length_of_isBaseChange (isBaseChange_selMap ρ ρ' j hj U hb 𝒟)
end
