module

public import GroundTheory.TateCohomology.Induced
public import GroundTheory.TateCohomology.CupCochains
public import GroundTheory.TateCohomology.HerbrandAbstract
public import GroundTheory.TateCohomology.TateLow

@[expose] public section

section -- merged from GroundTheory.TateCohomology.InducedNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

section Criterion

variable (M : Rep.{u} k G)

noncomputable def toCoindRes :
    M ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) :=
  ofHom ⟨LinearMap.codRestrict _ (LinearMap.pi fun x : G => M.ρ x) fun m => by
      rw [Representation.mem_coindV]
      intro s x
      simp [map_mul],
    fun g => LinearMap.ext fun m => by
      apply Subtype.ext
      funext x
      change M.ρ x (M.ρ g m) = M.ρ (x * g) m
      rw [map_mul, Module.End.mul_apply]⟩

noncomputable def fromCoindRes (φ : M.V →ₗ[k] M.V) :
    coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M) ⟶ M :=
  ofHom ⟨∑ x : G, M.ρ x⁻¹ ∘ₗ φ ∘ₗ LinearMap.proj x ∘ₗ
      (Representation.coindV (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M).ρ).subtype,
    fun g => LinearMap.ext fun f => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.coe_comp, LinearMap.coe_sum, Function.comp_apply, Finset.sum_apply,
        map_sum]
      refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun x => ?_
      change M.ρ x⁻¹ (φ (f.1 (x * g))) = M.ρ g (M.ρ (x * g)⁻¹ (φ (f.1 (x * g))))
      rw [← Module.End.mul_apply (M.ρ g) (M.ρ (x * g)⁻¹), ← map_mul, mul_inv_rev,
        mul_inv_cancel_left]⟩

theorem toCoindRes_fromCoindRes (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    toCoindRes M ≫ fromCoindRes M φ = 𝟙 M := by
  ext m
  change (fromCoindRes M φ).hom.toLinearMap ((toCoindRes M).hom.toLinearMap m) = m
  refine (LinearMap.sum_apply _ _ _).trans ?_
  change ∑ x : G, M.ρ x⁻¹ (φ (M.ρ x m)) = m
  conv_rhs => rw [← hφ m]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun x => by simp

theorem tateAcyclic_of_sum_eq (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) : TateAcyclic M :=
  (tateAcyclic_coind_bot _).of_retract _ _ (toCoindRes_fromCoindRes M φ hφ)

end Criterion

section Tensor


omit [Fintype G] in
noncomputable def coeffOneProj : MonoidAlgebra k G →ₗ[k] MonoidAlgebra k G :=
  MonoidAlgebra.lsingle 1 ∘ₗ Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap


omit [Fintype G] in
theorem coeffOneProj_apply (x : MonoidAlgebra k G) :
    coeffOneProj x = MonoidAlgebra.single 1 (x.coeff 1) := rfl

variable (B : Rep.{u} k G)

theorem sum_leftRegular_tensor (t : (leftRegular k G ⊗ B : Rep k G)) :
    ∑ g : G, (leftRegular k G ⊗ B).ρ g
      (TensorProduct.map coeffOneProj LinearMap.id ((leftRegular k G ⊗ B).ρ g⁻¹ t)) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]
  | tmul x b =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add (f := _), Finset.sum_add_distrib, hx, hy]
    | single h c =>
      rw [Fintype.sum_eq_single h]
      · simp [Rep.tensor_ρ, coeffOneProj_apply]
      · intro g hg
        have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
        simp [Rep.tensor_ρ, coeffOneProj_apply, this]

theorem tateAcyclic_leftRegular_tensor : TateAcyclic (leftRegular k G ⊗ B) :=
  tateAcyclic_of_sum_eq _ (TensorProduct.map coeffOneProj LinearMap.id) (sum_leftRegular_tensor B)

theorem tateAcyclic_leftRegular_tensor_trivial (V : Type u) [AddCommGroup V] [Module k V] :
    TateAcyclic (leftRegular k G ⊗ trivial k G V) :=
  tateAcyclic_leftRegular_tensor _

theorem tateAcyclic_leftRegular : TateAcyclic (leftRegular k G) :=
  (tateAcyclic_leftRegular_tensor (𝟙_ (Rep k G))).of_iso (ρ_ (leftRegular k G)).symm

theorem tateAcyclic_free (α : Type u) : TateAcyclic (free k G α) := by
  classical
  exact (tateAcyclic_leftRegular_tensor_trivial _).of_iso (leftRegularTensorTrivialIsoFree k G α).symm

end Tensor

section Free

variable (M : Rep.{u} k G)

end Free

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.CupProduct
set_option maxSynthPendingDepth 1

noncomputable section

universe u

open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits

namespace GroundTheory.GroupCoh

variable {k G : Type u} [CommRing k] [Group G]

section Cocycles

variable {A B : Rep k G} {p q n : ℕ}

theorem cocycles_ext {z z' : cocycles A n} (h : iCocycles A n z = iCocycles A n z') : z = z' :=
  (ModuleCat.mono_iff_injective _).1 inferInstance h

theorem d_iCocycles (z : cocycles A n) :
    (inhomogeneousCochains.d A n).hom (iCocycles A n z) = 0 := by
  have h := congr(($((inhomogeneousCochains A).iCycles_d n (n + 1))).hom z)
  simpa using h

theorem iCocycles_toCocycles {m : ℕ} (y : (Fin m → G) → A) :
    iCocycles A (m + 1) (toCocycles A m (m + 1) y) = (inhomogeneousCochains.d A m).hom y := by
  change (toCocycles A m (m + 1) ≫ iCocycles A (m + 1)).hom y = _
  rw [HomologicalComplex.toCycles_i]
  simp

theorem toCocycles_eq_zero {i : ℕ} (h : i + 1 ≠ n) : toCocycles A i n = 0 :=
  (inhomogeneousCochains A).toCycles_eq_zero (by simpa using h)

theorem π_eq_zero_of_eq_d {m : ℕ} (z : cocycles A (m + 1)) (y : (Fin m → G) → A)
    (hz : iCocycles A (m + 1) z = (inhomogeneousCochains.d A m).hom y) :
    π A (m + 1) z = 0 := by
  have : z = toCocycles A m (m + 1) y := cocycles_ext (by rw [hz, iCocycles_toCocycles])
  subst this
  exact congr(($((inhomogeneousCochains A).toCycles_comp_homologyπ m (m + 1))).hom y)

def descH {M : Type u} [AddCommGroup M] [Module k M] (φ : cocycles A n →ₗ[k] M)
    (hφ : ∀ (i : ℕ) (y : (Fin i → G) → A), φ (toCocycles A i n y) = 0) :
    groupCohomology A n →ₗ[k] M :=
  (((inhomogeneousCochains A).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ (Z := ModuleCat.of k M) (ModuleCat.ofHom φ)
      (by ext y; exact hφ _ y))).hom

theorem descH_π {M : Type u} [AddCommGroup M] [Module k M] (φ : cocycles A n →ₗ[k] M)
    (hφ : ∀ (i : ℕ) (y : (Fin i → G) → A), φ (toCocycles A i n y) = 0) (z : cocycles A n) :
    descH φ hφ (π A n z) = φ z :=
  congr(($(((inhomogeneousCochains A).homologyIsCokernel _ n rfl).fac
    (CokernelCofork.ofπ (Z := ModuleCat.of k M) (ModuleCat.ofHom φ)
      (by ext y; exact hφ _ y)) WalkingParallelPair.one)).hom z)

theorem linearMap_ext {M : Type u} [AddCommGroup M] [Module k M]
    {φ ψ : groupCohomology A n →ₗ[k] M} (h : ∀ z : cocycles A n, φ (π A n z) = ψ (π A n z)) :
    φ = ψ :=
  LinearMap.ext fun x => groupCohomology_induction_on x h

theorem cupCochain_zero_left (h : p + q = n) (g : (Fin q → G) → B) :
    cupCochain h (0 : (Fin p → G) → A) g = 0 :=
  (cupₗ h).map_zero₂ g

theorem cupCochain_zero_right (h : p + q = n) (f : (Fin p → G) → A) :
    cupCochain h f (0 : (Fin q → G) → B) = 0 :=
  (cupₗ h f).map_zero

theorem d_cupCochain_iCocycles (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    (inhomogeneousCochains.d (A ⊗ B) n).hom (cupCochain h (iCocycles A p z) (iCocycles B q w)) =
      0 := by
  rw [d_cupCochain, d_iCocycles, d_iCocycles, cupCochain_zero_left, cupCochain_zero_right,
    smul_zero, add_zero]

def cupCocycle (h : p + q = n) (z : cocycles A p) (w : cocycles B q) : cocycles (A ⊗ B) n :=
  cocyclesMk (cupCochain h (iCocycles A p z) (iCocycles B q w)) (d_cupCochain_iCocycles h z w)

theorem iCocycles_cupCocycle (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycle h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_mk _ (d_cupCochain_iCocycles h z w)

def cupCocycles (h : p + q = n) : cocycles A p →ₗ[k] cocycles B q →ₗ[k] cocycles (A ⊗ B) n :=
  LinearMap.mk₂ k (cupCocycle h)
    (fun z z' w => cocycles_ext (by
      rw [map_add (f := _), iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add (f := _)]
      exact (cupₗ h).map_add₂ _ _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h).map_smul₂ _ _ _))
    (fun z w w' => cocycles_ext (by
      rw [map_add (f := _), iCocycles_cupCocycle, iCocycles_cupCocycle, iCocycles_cupCocycle, map_add (f := _)]
      exact (cupₗ h _).map_add _ _))
    (fun c z w => cocycles_ext (by
      rw [map_smul, iCocycles_cupCocycle, iCocycles_cupCocycle, map_smul]
      exact (cupₗ h _).map_smul _ _))

theorem iCocycles_cupCocycles (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    iCocycles (A ⊗ B) n (cupCocycles h z w) = cupCochain h (iCocycles A p z) (iCocycles B q w) :=
  iCocycles_cupCocycle h z w

end Cocycles

section Cohomology

variable {A B : Rep k G} {p q n : ℕ}

theorem π_cupCocycles_toCocycles_right (h : p + q = n) (z : cocycles A p) (i : ℕ)
    (y : (Fin i → G) → B) : π (A ⊗ B) n (cupCocycles h z (toCocycles B i q y)) = 0 := by
  by_cases hi : i + 1 = q
  · subst hi
    obtain rfl : n = p + i + 1 := by omega
    refine π_eq_zero_of_eq_d _ ((-1 : k) ^ p • cupCochain rfl (iCocycles A p z) y) ?_
    rw [map_smul, d_cupCochain, d_iCocycles, cupCochain_zero_left, zero_add, smul_smul, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul, iCocycles_cupCocycles,
      iCocycles_toCocycles]
  · simp [toCocycles_eq_zero hi]

theorem π_cupCocycles_toCocycles_left (h : p + q = n) (i : ℕ) (y : (Fin i → G) → A)
    (w : cocycles B q) : π (A ⊗ B) n (cupCocycles h (toCocycles A i p y) w) = 0 := by
  by_cases hi : i + 1 = p
  · subst hi
    obtain rfl : n = i + q + 1 := by omega
    refine π_eq_zero_of_eq_d _ (cupCochain rfl y (iCocycles B q w)) ?_
    rw [d_cupCochain, d_iCocycles, cupCochain_zero_right, smul_zero, add_zero,
      iCocycles_cupCocycles, iCocycles_toCocycles]
  · simp [toCocycles_eq_zero hi]

def cupHLeft (h : p + q = n) (z : cocycles A p) :
    groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) n :=
  descH ((π (A ⊗ B) n).hom ∘ₗ cupCocycles h z) (π_cupCocycles_toCocycles_right h z)

theorem cupHLeft_π (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupHLeft h z (π B q w) = π (A ⊗ B) n (cupCocycles h z w) :=
  descH_π _ _ w

def cupH (h : p + q = n) :
    groupCohomology A p →ₗ[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) n :=
  descH
    { toFun := cupHLeft h
      map_add' := fun z z' => linearMap_ext fun w => by
        rw [LinearMap.add_apply, cupHLeft_π, cupHLeft_π, cupHLeft_π, map_add (f := _),
          LinearMap.add_apply, map_add]
      map_smul' := fun c z => linearMap_ext fun w => by
        rw [LinearMap.smul_apply, cupHLeft_π, cupHLeft_π, map_smul, LinearMap.smul_apply,
          map_smul, RingHom.id_apply] }
    (fun i y => linearMap_ext fun w => by
      show cupHLeft h (toCocycles A i p y) (π B q w) = 0
      rw [cupHLeft_π, π_cupCocycles_toCocycles_left])

theorem cupH_π (h : p + q = n) (z : cocycles A p) (w : cocycles B q) :
    cupH h (π A p z) (π B q w) = π (A ⊗ B) n (cupCocycles h z w) := by
  rw [cupH, descH_π]
  exact cupHLeft_π h z w


variable (A B p q) in
def cupTensor :
    groupCohomology A p ⊗[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (cupH rfl)


variable (A B p q) in
def cup : groupCohomology A p ⊗ groupCohomology B q ⟶ groupCohomology (A ⊗ B) (p + q) :=
  ModuleCat.ofHom (cupTensor A B p q)

theorem map_π_apply {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    map (MonoidHom.id G) φ n (π A n z) = π A' n (cocyclesMap (MonoidHom.id G) φ n z) := by
  change (π A n ≫ map (MonoidHom.id G) φ n).hom z =
    (cocyclesMap (MonoidHom.id G) φ n ≫ π A' n).hom z
  rw [π_map]

theorem iCocycles_cocyclesMap {A' : Rep k G} (φ : A ⟶ A') (z : cocycles A n) :
    iCocycles A' n (cocyclesMap (MonoidHom.id G) φ n z) =
      fun x => φ.hom (iCocycles A n z x) := by
  change (cocyclesMap (MonoidHom.id G) φ n ≫ iCocycles A' n).hom z = _
  rw [HomologicalComplex.cyclesMap_i]
  rfl

theorem map_cupH {A' B' : Rep k G} (φ : A ⟶ A') (ψ : B ⟶ B') (h : p + q = n)
    (a : groupCohomology A p) (b : groupCohomology B q) :
    map (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupH h a b) =
      cupH h (map (MonoidHom.id G) φ p a) (map (MonoidHom.id G) ψ q b) := by
  refine groupCohomology_induction_on a fun z => ?_
  refine groupCohomology_induction_on b fun w => ?_
  have key : cocyclesMap (A := A ⊗ B) (MonoidHom.id G) (φ ⊗ₘ ψ) n (cupCocycles h z w) =
      cupCocycles h (cocyclesMap (MonoidHom.id G) φ p z) (cocyclesMap (MonoidHom.id G) ψ q w) := by
    refine cocycles_ext ?_
    rw [iCocycles_cocyclesMap, iCocycles_cupCocycles, iCocycles_cupCocycles, iCocycles_cocyclesMap,
      iCocycles_cocyclesMap]
    funext x
    exact tensorHom_cupCochain φ ψ h _ _ x
  rw [cupH_π, map_π_apply, map_π_apply, cupH_π, ← key]
  exact map_π_apply _ _

theorem d_oneCochain :
    (inhomogeneousCochains.d (𝟙_ (Rep k G)) 0).hom (oneCochain (k := k) (G := G)) = 0 := by
  funext x
  simp [inhomogeneousCochains.d_hom_apply, oneCochain]
  rfl


end Cohomology

end GroundTheory.GroupCoh
end
end

section -- merged from GroundTheory.TateCohomology.InfRes
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem map_one_succ {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (n : ℕ) : map 1 φ (n + 1) = 0 := by
  let f : PUnit.{u + 1} →* H := 1
  let g : G →* PUnit.{u + 1} := 1
  let ψ : res g (res f A) ⟶ B := ofHom ⟨φ.hom.toLinearMap, fun x => φ.hom.isIntertwining' x⟩
  have h : map 1 φ (n + 1) = map (f.comp g) ((resFunctor g).map (𝟙 (res f A)) ≫ ψ) (n + 1) :=
    map_congr (by ext; rfl) rfl (n + 1)
  rw [h, map_comp, (isZero_groupCohomology_succ_of_subsingleton (res f A) n).eq_zero_of_src
    (map g ψ (n + 1)), Limits.comp_zero]

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

noncomputable abbrev inflation (n : ℕ) :
    groupCohomology (A.quotientToInvariants S) n ⟶ groupCohomology A n :=
  map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) n

noncomputable abbrev restriction (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res S.subtype A) n :=
  map S.subtype (𝟙 _) n

theorem inflation_comp_restriction (n : ℕ) :
    inflation A S (n + 1) ≫ restriction A S (n + 1) = 0 := by
  rw [← map_comp, Category.comp_id, groupCohomology.congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ (n + 1)), map_one_succ]

noncomputable def infResShortComplex (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) (n + 1)
  X₂ := groupCohomology A (n + 1)
  X₃ := groupCohomology (res S.subtype A) (n + 1)
  f := inflation A S (n + 1)
  g := restriction A S (n + 1)
  zero := inflation_comp_restriction A S n

lemma invariants_map_surjective {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((invariantsFunctor k G).map X.g).hom := by
  have ex := (map_cochainsFunctor_shortExact hX).homology_exact₃ 0 1 rfl
  have e : Epi (map (MonoidHom.id G) X.g 0) := ex.epi_f (h1.eq_of_tgt _ _)
  have hc := map_id_comp_H0Iso_hom X.g
  have e2 : Epi ((H0Iso X.X₂).hom ≫ (invariantsFunctor k G).map X.g) := by
    rw [← hc]; infer_instance
  have e3 := epi_of_epi (H0Iso X.X₂).hom ((invariantsFunctor k G).map X.g)
  exact (ModuleCat.epi_iff_surjective _).1 e3

noncomputable def toCoindOne : A ⟶ coindOne k G A :=
  ofHom ⟨LinearMap.pi fun x => A.ρ x, fun g => by
    ext a x
    change A.ρ x (A.ρ g a) = A.ρ (x * g) a
    rw [map_mul, mul_apply_eq_comp]⟩

lemma toCoindOne_injective : Function.Injective (toCoindOne A).hom := fun a b h => by
  have h' : A.ρ 1 a = A.ρ 1 b := congrFun h 1
  simpa using h'

instance : Mono (toCoindOne A) := (Rep.mono_iff_injective _).2 (toCoindOne_injective A)

noncomputable abbrev shiftSC : ShortComplex (Rep k G) :=
  ShortComplex.mk (toCoindOne A) (cokernel.π (toCoindOne A)) (cokernel.condition _)

lemma shiftSC_shortExact : (shiftSC A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (toCoindOne A))
  epi_g := inferInstanceAs (Epi (cokernel.π _))

instance : (quotientToInvariantsFunctor k S).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl

noncomputable abbrev shiftSCQ : ShortComplex (Rep k (G ⧸ S)) :=
  (shiftSC A).map (quotientToInvariantsFunctor k S)

lemma shiftSCQ_shortExact (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    (shiftSCQ A S).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro x hx
    have hrk := ((shiftSC_shortExact A).exact.map
      (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
    have hx' : x.1 ∈ LinearMap.ker ((shiftSC A).map (forget₂ (Rep k G) (ModuleCat k))).g.hom :=
      congrArg Subtype.val hx
    rw [← hrk] at hx'
    obtain ⟨a, ha⟩ := hx'
    have ha' : (toCoindOne A).hom a = x.1 := ha
    refine ⟨⟨a, fun s => toCoindOne_injective A ?_⟩, Subtype.ext ha'⟩
    refine (hom_comm_apply (toCoindOne A) (s : G) a).trans ?_
    rw [ha']
    exact x.2 s
  · exact (Rep.mono_iff_injective _).2 fun x y h =>
      Subtype.ext (toCoindOne_injective A (congrArg Subtype.val h))
  · exact (Rep.epi_iff_surjective (shiftSCQ A S).g).2
      (invariants_map_surjective (X := (shiftSC A).map (resFunctor S.subtype))
        ((shortExact_res S.subtype).2 (shiftSC_shortExact A)) h1)

theorem infRes_step (n : ℕ)
    (ih : ∀ B : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype B) i)) →
      Mono (infResShortComplex B S n).f ∧ (infResShortComplex B S n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (groupCohomology (res S.subtype A) i)) :
    Mono (infResShortComplex A S (n + 1)).f ∧ (infResShortComplex A S (n + 1)).Exact := by
  have hX := shiftSC_shortExact A
  have hS := (shortExact_res S.subtype).2 hX
  have hQ := shiftSCQ_shortExact A S (hA 1 one_pos (by omega))
  have hC : ∀ i, 0 < i → i < n + 1 →
      IsZero (groupCohomology (res S.subtype (shiftSC A).X₃) i) := by
    intro i hi hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS (m + 1) (isZero_res_coindOne k A S m)
      (isZero_res_coindOne k A S (m + 1))
    exact (hA (m + 1 + 1) (by omega) (by omega)).of_iso (@asIso _ _ _ _ _ hδ)
  obtain ⟨ihm, ihe⟩ := ih (shiftSC A).X₃ hC
  have hδQ := isIso_δ_of_isZero hQ (n + 1) (isZero_quotientToInvariants_coindOne k A S n)
    (isZero_quotientToInvariants_coindOne k A S (n + 1))
  have hδX := isIso_δ_of_isZero hX (n + 1) (isZero_coindOne k G A n)
    (isZero_coindOne k G A (n + 1))
  have hδS := isIso_δ_of_isZero hS (n + 1) (isZero_res_coindOne k A S n)
    (isZero_res_coindOne k A S (n + 1))
  let F : (shiftSCQ A S).map (resFunctor (QuotientGroup.mk' S)) ⟶ shiftSC A :=
    { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
      τ₂ := ofHom ((coindOne k G A).ρ.quotientToInvariants_lift S)
      τ₃ := ofHom ((shiftSC A).X₃.ρ.quotientToInvariants_lift S)
      comm₁₂ := by ext; rfl
      comm₂₃ := by ext; rfl }
  have h1 : δ hQ (n + 1) (n + 1 + 1) rfl ≫ inflation A S (n + 1 + 1) =
      inflation (shiftSC A).X₃ S (n + 1) ≫ δ hX (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map (QuotientGroup.mk' S) hQ hX F (n + 1) (n + 1 + 1) rfl
  have h2 : δ hX (n + 1) (n + 1 + 1) rfl ≫ restriction A S (n + 1 + 1) =
      restriction (shiftSC A).X₃ S (n + 1) ≫ δ hS (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map_res S.subtype hX (n + 1) (n + 1 + 1) rfl
  let e : infResShortComplex (shiftSC A).X₃ S n ≅ infResShortComplex A S (n + 1) :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ hδQ) (@asIso _ _ _ _ _ hδX) (@asIso _ _ _ _ _ hδS) h1 h2
  refine ⟨?_, (ShortComplex.exact_iff_of_iso e).1 ihe⟩
  have hf : e.inv.τ₁ ≫ (infResShortComplex (shiftSC A).X₃ S n).f ≫ e.hom.τ₂ =
      (infResShortComplex A S (n + 1)).f := by
    rw [← Category.assoc, e.inv.comm₁₂, Category.assoc, ← ShortComplex.comp_τ₂, e.inv_hom_id,
      ShortComplex.id_τ₂, Category.comp_id]
  rw [← hf]
  infer_instance

theorem infResShortComplex_mono_exact (n : ℕ) :
    ∀ A : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype A) i)) →
      Mono (infResShortComplex A S n).f ∧ (infResShortComplex A S n).Exact := by
  induction n with
  | zero => exact fun A _ => ⟨inferInstanceAs (Mono (H1InfRes A S).f), H1InfRes_exact A S⟩
  | succ n ih => exact fun A hA => infRes_step A S n ih hA

variable {A S}

theorem inflation_injective {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    Function.Injective (inflation A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (ModuleCat.mono_iff_injective _).1 (infResShortComplex_mono_exact S n A hA).1

theorem range_inflation_eq_ker_restriction {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    LinearMap.range (inflation A S q).hom = LinearMap.ker (restriction A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (infResShortComplex_mono_exact S n A hA).2.moduleCat_range_eq_ker

theorem inflation_two_injective (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    Function.Injective (inflation A S 2).hom :=
  inflation_injective two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

theorem range_inflation_two_eq_ker_restriction
    (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    LinearMap.range (inflation A S 2).hom = LinearMap.ker (restriction A S 2).hom :=
  range_inflation_eq_ker_restriction two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.HerbrandTate
section -- merged from GroundTheory.TateCohomology.HerbrandRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def repSubOne (A : Rep.{w} k G) (σ : G) : A →+ A :=
  (A.ρ σ - 1 : Module.End k A).toAddMonoidHom

theorem repSubOne_apply (A : Rep.{w} k G) (σ : G) (x : A) : repSubOne A σ x = A.ρ σ x - x :=
  rfl

variable [Fintype G]

def repNorm (A : Rep.{w} k G) : A →+ A :=
  A.ρ.norm.toAddMonoidHom

end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

universe u

open CategoryTheory

theorem natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker :=
  rfl

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]


omit [Fintype G] in
theorem ker_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).ker = A.ρ.invariants.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, repSubOne_apply, sub_eq_zero, Submodule.mem_toAddSubgroup,
    Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ σ hσ]

theorem range_repSubOne (A : Rep.{u} R G) {σ : G} (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    (repSubOne A σ).range = (Representation.Coinvariants.ker A.ρ).toAddSubgroup := by
  rw [Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ σ hσ]
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem ker_repNorm (A : Rep.{u} R G) :
    (repNorm A).ker = (LinearMap.ker A.ρ.norm).toAddSubgroup :=
  rfl

theorem range_repNorm (A : Rep.{u} R G) :
    (repNorm A).range = (LinearMap.range A.ρ.norm).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
  rfl

theorem natCard_tateCohomology_zero (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A 0) = Nat.card (KerModRange (repSubOne A σ) (repNorm A)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repSubOne A hσ, range_repNorm]
  exact Nat.card_congr ((tateCohomologyZeroIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

theorem natCard_tateCohomology_neg_one (A : Rep.{u} R G) {σ : G}
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology A (-1)) = Nat.card (KerModRange (repNorm A) (repSubOne A σ)) := by
  rw [natCard_kerModRange_eq_relIndex, ker_repNorm, range_repSubOne A hσ]
  exact Nat.card_congr ((tateCohomologyNegOneIso (R := R) (G := G)).app A).toLinearEquiv.toEquiv

end GroundTheory.GroupCoh
end
