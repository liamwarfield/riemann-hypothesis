module

public import GroundTheory.TateCohomology.AugmentationSES
public import GroundTheory.TateCohomology.CohTrivial

@[expose] public section

section -- merged from GroundTheory.TateCohomology.SplittingCohTrivial
section -- merged from GroundTheory.TateCohomology.SplittingModule
section -- merged from GroundTheory.TateCohomology.AugTrivial
set_option maxSynthPendingDepth 1

open CategoryTheory groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

variable (k G : Type u) [CommRing k] [Group G]

noncomputable def augHom : Rep.leftRegular k G ⟶ Rep.trivial k G k :=
  Rep.ofHom ⟨augmentation k G, fun g => LinearMap.ext fun x => by
    change augmentation k G ((Rep.leftRegular k G).ρ g x) = augmentation k G x
    exact augmentation_ρ g x⟩

theorem augIdealι_augHom : augIdealι k G ≫ augHom k G = 0 := by
  ext x
  exact LinearMap.mem_ker.1 x.2

noncomputable def augTrivSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (augIdealι k G) (augHom k G) (augIdealι_augHom k G)

theorem augTrivSES_shortExact : (augTrivSES k G).ShortExact := by
  refine shortExact_of_linear (fun a b h => Subtype.ext h)
    (fun r => ⟨MonoidAlgebra.single (1 : G) (show k from r), ?_⟩)
    (fun y hy => ⟨⟨y, LinearMap.mem_ker.2 hy⟩, rfl⟩)
  exact augmentation_single (k := k) (1 : G) (show k from r)

theorem cohTrivial_leftRegular [Fintype G] : CohTrivial (Rep.leftRegular k G) := by
  refine cohTrivial_of_sum_eq _ coeffOneProj fun m => ?_
  induction m using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]
  | single h c =>
    rw [Fintype.sum_eq_single h]
    · simp [coeffOneProj_apply]
    · intro g hg
      have : g⁻¹ * h ≠ 1 := fun e => hg (inv_mul_eq_one.mp e)
      simp [coeffOneProj_apply, this]

variable {k G}

noncomputable def augIdealSubOne (g : G) : augIdeal k G :=
  ⟨MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1, by
    rw [LinearMap.mem_ker, map_sub, augmentation_single, augmentation_single, sub_self]⟩

@[simp] theorem augIdealSubOne_val (g : G) :
    ((augIdealSubOne g : augIdeal k G) : MonoidAlgebra k G) =
      MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1 := rfl

section Cocycle

variable {A : Rep.{u} k G}

noncomputable def cocycleLinear (f : cocycles₁ A) : MonoidAlgebra k G →ₗ[k] A.V :=
  Finsupp.linearCombination k (fun g => f g) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem cocycleLinear_single (f : cocycles₁ A) (g : G) (r : k) :
    cocycleLinear f (MonoidAlgebra.single g r) = r • f g := by
  simp [cocycleLinear]

theorem cocycleLinear_ρ (f : cocycles₁ A) (s : G) (x : MonoidAlgebra k G) :
    cocycleLinear f ((Rep.leftRegular k G).ρ s x) =
      A.ρ s (cocycleLinear f x) + augmentation k G x • f s := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_smul]; abel
  | single g r =>
    have hf : f (s * g) = A.ρ s (f g) + f s := (mem_cocycles₁_iff _).1 f.2 s g
    rw [Representation.ofMulAction_single, smul_eq_mul, cocycleLinear_single, cocycleLinear_single,
      augmentation_single, map_smul, hf, smul_add]

noncomputable def cocycleHom (f : cocycles₁ A) : augIdeal k G ⟶ A :=
  Rep.ofHom ⟨cocycleLinear f ∘ₗ (LinearMap.ker (augmentation k G)).subtype, fun s =>
    LinearMap.ext fun x => by
      have hx : augmentation k G x.1 = 0 := LinearMap.mem_ker.1 x.2
      change cocycleLinear f ((Rep.leftRegular k G).ρ s x.1) = A.ρ s (cocycleLinear f x.1)
      rw [cocycleLinear_ρ, hx, zero_smul, add_zero]⟩

theorem cocycleHom_apply (f : cocycles₁ A) (x : augIdeal k G) :
    (cocycleHom f).hom x = cocycleLinear f x.1 := rfl

theorem cocycleHom_augIdealSubOne (f : cocycles₁ A) (g : G) :
    (cocycleHom f).hom (augIdealSubOne g) = f g := by
  rw [cocycleHom_apply, augIdealSubOne_val, map_sub, cocycleLinear_single, cocycleLinear_single,
    cocycles₁_map_one, smul_zero, sub_zero, one_smul]

end Cocycle

section Restrict

variable (k) {H : Type u} [Group H] (φ : H →* G)

noncomputable def augCocycle : cocycles₁ (Rep.res φ (augIdeal k G)) :=
  ⟨fun h => augIdealSubOne (φ h), (mem_cocycles₁_iff _).2 fun a b => by
    apply Subtype.ext
    change MonoidAlgebra.single (φ (a * b)) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ a) (MonoidAlgebra.single (φ b) 1 - MonoidAlgebra.single 1 1) +
        (MonoidAlgebra.single (φ a) 1 - MonoidAlgebra.single 1 1)
    rw [map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single, smul_eq_mul,
      smul_eq_mul, mul_one, map_mul]
    abel⟩

theorem augTrivSES_res_shortExact : ((augTrivSES k G).map (resFunctor φ)).ShortExact :=
  (shortExact_res φ).2 (augTrivSES_shortExact k G)

def oneInvariant : (Rep.res φ (Rep.trivial k G k)).ρ.invariants :=
  ⟨(1 : k), fun _ => rfl⟩

theorem δ₀_augTrivSES_res :
    δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ)) =
      H1π _ (augCocycle k φ) := by
  have hx : ((augTrivSES k G).map (resFunctor φ)).f.hom ∘ (fun h => augIdealSubOne (φ h)) =
      d₀₁ ((augTrivSES k G).map (resFunctor φ)).X₂ (MonoidAlgebra.single (1 : G) (1 : k)) := by
    funext h
    change MonoidAlgebra.single (φ h) (1 : k) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular k G).ρ (φ h) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  exact δ₀_apply (augTrivSES_res_shortExact k φ) (oneInvariant k φ)
    (MonoidAlgebra.single (1 : G) (1 : k)) (by exact augmentation_single (k := k) (1 : G) (1 : k)) _ hx

end Restrict

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.PullbackExtension
set_option maxSynthPendingDepth 1

open CategoryTheory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)

variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]

noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)

noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl

noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]

noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩

theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl

noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)


variable {S} in
theorem pullbackSES_shortExact (hS : S.ShortExact) : (pullbackSES S β).ShortExact := by
  have hex := function_exact_of_shortExact hS
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_linear ?_ ?_ ?_
  · intro a b hab
    exact hinj (congrArg (fun p : pullbackRep S β => p.1.1) hab)
  · intro y
    obtain ⟨x, hx⟩ := hsurj (β.hom y)
    exact ⟨⟨(x, y), mem_pullbackSubmodule.2 hx⟩, rfl⟩
  · intro p hp
    have hp2 : p.1.2 = 0 := hp
    have hg : S.g.hom p.1.1 = 0 := by
      rw [(mem_pullbackSubmodule.1 p.2), hp2, map_zero]
    obtain ⟨x, hx⟩ := (hex p.1.1).1 hg
    refine ⟨x, Subtype.ext (Prod.ext hx hp2.symm)⟩

end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section Construction

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem isZero_groupCohomology_coind_two : IsZero (groupCohomology (coindSES.obj M).X₂ 2) :=
  ((tateAcyclic_coindSES_X₂ M) 2).of_iso (tateIsoH _ 2 2 rfl).symm

theorem exists_cocycle_δ_eq : ∃ f : cocycles₁ (coindSES.obj M).X₃,
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ f) = u := by
  have : Epi (δ (coindSES_shortExact M) 1 2 rfl) :=
    epi_δ_of_isZero (coindSES_shortExact M) 1 (isZero_groupCohomology_coind_two M)
  obtain ⟨v, hv⟩ := (ModuleCat.epi_iff_surjective _).1 this u
  obtain ⟨f, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π _)).1 inferInstance v
  exact ⟨f, hv⟩

noncomputable def splittingCocycle : cocycles₁ (coindSES.obj M).X₃ :=
  (exists_cocycle_δ_eq M u).choose

theorem δ_splittingCocycle :
    δ (coindSES_shortExact M) 1 2 rfl (H1π _ (splittingCocycle M u)) = u :=
  (exists_cocycle_δ_eq M u).choose_spec

noncomputable def splittingSES : ShortComplex (Rep.{u} k G) :=
  pullbackSES (coindSES.obj M) (cocycleHom (splittingCocycle M u))

theorem splittingSES_shortExact : (splittingSES M u).ShortExact :=
  pullbackSES_shortExact (cocycleHom (splittingCocycle M u)) (coindSES_shortExact M)

noncomputable abbrev splittingModule : Rep.{u} k G := (splittingSES M u).X₂


omit [Fintype G] in
theorem map_H1π_augCocycle {H : Type u} [Group H] (φ : H →* G) {A : Rep.{u} k G}
    (f : cocycles₁ A) :
    map (A := res φ (augIdeal k G)) (B := res φ A) (MonoidHom.id H)
      ((resFunctor φ).map (cocycleHom f)) 1 (H1π _ (augCocycle k φ)) =
    map φ (𝟙 (res φ A)) 1 (H1π A f) := by
  rw [H1π_comp_map_apply, H1π_comp_map_apply]
  congr 1
  apply cocycles₁_ext
  intro h
  exact cocycleHom_augIdealSubOne f (φ h)

noncomputable def splittingSESResHom {H : Type u} [Group H] (φ : H →* G) :
    (splittingSES M u).map (resFunctor φ) ⟶ (coindSES.obj M).map (resFunctor φ) where
  τ₁ := 𝟙 _
  τ₂ := (resFunctor φ).map (pullbackFst _ (cocycleHom (splittingCocycle M u)))
  τ₃ := (resFunctor φ).map (cocycleHom (splittingCocycle M u))
  comm₁₂ := by
    ext x
    rfl
  comm₂₃ := by
    ext p
    exact mem_pullbackSubmodule.1 p.2

theorem δ_splittingSES_res_δ₀ {H : Type u} [Group H] (φ : H →* G) :
    δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
      (δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ))) =
    map φ (𝟙 (res φ M)) 2 u := by
  rw [δ₀_augTrivSES_res]
  have hN := groupCohomology.δ_naturality ((shortExact_res φ).2 (splittingSES_shortExact M u))
    ((shortExact_res φ).2 (coindSES_shortExact M)) (splittingSESResHom M u φ) 1 2 rfl
  have e : (map (MonoidHom.id H) (𝟙 (res φ M)) 2).hom
      (δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
        (H1π (res φ (augIdeal k G)) (augCocycle k φ))) =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map (A := res φ (augIdeal k G)) (B := res φ (coindSES.obj M).X₃) (MonoidHom.id H)
          ((resFunctor φ).map (cocycleHom (splittingCocycle M u))) 1).hom
          (H1π _ (augCocycle k φ))) :=
    congr(($hN).hom (H1π _ (augCocycle k φ)))
  have hid : ∀ y, (map (A := res φ M) (B := res φ M) (MonoidHom.id H) (𝟙 (res φ M)) 2).hom y =
      y := fun y => by
    rw [groupCohomology.map_id]
    rfl
  have hR := congr(($(δ_comp_map_res φ (coindSES_shortExact M) 1 2 rfl)).hom
    (H1π _ (splittingCocycle M u)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hR
  have hR' : (map φ (𝟙 (res φ M)) 2).hom u =
      (δ ((shortExact_res φ).2 (coindSES_shortExact M)) 1 2 rfl).hom
        ((map φ (𝟙 (res φ (coindSES.obj M).X₃)) 1).hom (H1π _ (splittingCocycle M u))) := by
    conv_lhs => rw [← δ_splittingCocycle M u]
    exact hR
  refine (hid _).symm.trans (e.trans ?_)
  rw [map_H1π_augCocycle φ (splittingCocycle M u)]
  exact hR'.symm

end Construction

end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory Limits groupCohomology Rep

namespace GroundTheory.GroupCoh

universe u

section LES

variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)

theorem eq_zero_of_isZero {A : ModuleCat.{u} k} (h : IsZero A) (x : A) : x = 0 :=
  (ModuleCat.subsingleton_of_isZero h).elim x 0

theorem isZero_of_forall_eq_zero {A : ModuleCat.{u} k} (h : ∀ x : A, x = 0) : IsZero A :=
  ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => (h a).trans (h b).symm⟩


include hX in
theorem δ_map_g_apply (i j : ℕ) (hij : i + 1 = j) (x : groupCohomology X.X₂ i) :
    δ hX i j hij (map (MonoidHom.id H) X.g i x) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).comp_δ i j hij)).hom x)
  exact h


include hX in
theorem map_f_δ_apply (i j : ℕ) (hij : i + 1 = j) (z : groupCohomology X.X₃ i) :
    map (MonoidHom.id H) X.f j (δ hX i j hij z) = 0 := by
  have h := congr(($((map_cochainsFunctor_shortExact hX).δ_comp i j hij)).hom z)
  exact h


include hX in
theorem exists_map_f_eq (n : ℕ) (x : groupCohomology X.X₂ n)
    (hx : map (MonoidHom.id H) X.g n x = 0) : ∃ w, map (MonoidHom.id H) X.f n w = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₂_exact hX n) x hx


include hX in
theorem isZero_X₂_of_injective_δ (n : ℕ) (h₁ : IsZero (groupCohomology X.X₁ n))
    (hδ : Function.Injective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ n) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  have h1 : map (MonoidHom.id H) X.g n x = 0 :=
    hδ (by rw [δ_map_g_apply hX n (n + 1) rfl, map_zero])
  obtain ⟨w, hw⟩ := exists_map_f_eq hX n x h1
  rw [← hw, eq_zero_of_isZero h₁ w, map_zero]


include hX in
theorem isZero_X₂_succ_of_surjective_δ (n : ℕ) (h₃ : IsZero (groupCohomology X.X₃ (n + 1)))
    (hδ : Function.Surjective (δ hX n (n + 1) rfl)) : IsZero (groupCohomology X.X₂ (n + 1)) := by
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨w, hw⟩ := exists_map_f_eq hX (n + 1) x (eq_zero_of_isZero h₃ _)
  obtain ⟨z, rfl⟩ := hδ w
  rw [← hw, map_f_δ_apply hX n (n + 1) rfl z]

end LES

section TrivialInt

theorem isZero_H1_trivial_int {H : Type} [Group H] [Finite H] :
    IsZero (groupCohomology (Rep.trivial ℤ H ℤ) 1) := by
  have : Subsingleton (Additive H →+ ℤ) := ⟨fun f g => AddMonoidHom.ext fun x => by
    have key : ∀ φ : Additive H →+ ℤ, φ x = 0 := fun φ => by
      have h : addOrderOf x • φ x = 0 := by rw [← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
      exact (smul_eq_zero.1 h).resolve_left (addOrderOf_pos x).ne'
    rw [key f, key g]⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (H1IsoOfIsTrivial _)

end TrivialInt

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
variable (S : Subgroup G) [Fintype S]

theorem tateAcyclic_res_leftRegular : TateAcyclic (res S.subtype (Rep.leftRegular ℤ G)) :=
  cohTrivial_leftRegular ℤ G S

theorem isZero_groupCohomology_res_leftRegular (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (res S.subtype (Rep.leftRegular ℤ G)) n) :=
  ((tateAcyclic_res_leftRegular S) n).of_iso (tateIsoH _ n n rfl).symm

noncomputable def augClass : groupCohomology (res S.subtype (augIdeal ℤ G)) 1 :=
  δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl ((H0Iso _).inv (oneInvariant ℤ S.subtype))

theorem exists_eq_zsmul_augClass (y : groupCohomology (res S.subtype (augIdeal ℤ G)) 1) :
    ∃ m : ℤ, y = m • augClass S := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 0 1 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 0
      (isZero_groupCohomology_res_leftRegular S 1)
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep y
  let c : ℤ := show ℤ from ((H0Iso _).hom w).1
  refine ⟨c, ?_⟩
  have hw : w = (H0Iso _).inv (c • oneInvariant ℤ S.subtype) := by
    have : ((H0Iso _).hom w) = c • oneInvariant ℤ S.subtype := by
      apply Subtype.ext
      change _ = c * 1
      rw [mul_one]
    rw [← this]
    exact ((Iso.hom_inv_id_apply (H0Iso _) w)).symm
  conv_lhs => rw [hw]
  rw [map_zsmul]
  exact map_zsmul _ c _

noncomputable def subgroupNormElt : MonoidAlgebra ℤ G :=
  ∑ t : S, MonoidAlgebra.single (t : G) (1 : ℤ)


omit [Fintype G] in
theorem ρ_subgroupNormElt (s : S) :
    (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) = subgroupNormElt S := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [subgroupNormElt, map_sum, Representation.ofMulAction_single, smul_eq_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft s) _ _ (fun t => rfl)


omit [Fintype G] in
theorem augmentation_subgroupNormElt :
    augmentation ℤ G (subgroupNormElt S) = (Fintype.card S : ℤ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [subgroupNormElt, map_sum,
    Finset.sum_congr rfl (fun (x : S) _ => augmentation_single (k := ℤ) (x : G) (1 : ℤ))]
  simp

theorem card_smul_augClass : (Fintype.card S : ℤ) • augClass S = 0 := by
  let z : (res S.subtype (Rep.trivial ℤ G ℤ)).ρ.invariants := ⟨(Fintype.card S : ℤ), fun _ => rfl⟩
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (0 : S → res S.subtype (augIdeal ℤ G)) =
      d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂ (subgroupNormElt S) := by
    funext s
    change (augIdealι ℤ G).hom 0 =
      (Rep.leftRegular ℤ G).ρ (s : G) (subgroupNormElt S) - subgroupNormElt S
    rw [map_zero, ρ_subgroupNormElt, sub_self]
  have hδ := δ₀_apply (augTrivSES_res_shortExact ℤ S.subtype) z (subgroupNormElt S)
    (by exact augmentation_subgroupNormElt S) _ hx
  have hz : z = (Fintype.card S : ℤ) • oneInvariant ℤ S.subtype := by
    apply Subtype.ext
    change _ = (Fintype.card S : ℤ) * 1
    rw [mul_one]
  have h0 : H1π ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁
      ⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ = 0 := by
    have : (⟨0, mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        cocycles₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₁) = 0 := rfl
    rw [this, map_zero]
  have e1 : (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv z =
      (Fintype.card S : ℤ) • (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv
        (oneInvariant ℤ S.subtype) :=
    (congrArg (H0Iso ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₃).inv hz).trans
      (map_zsmul _ _ _)
  exact (map_zsmul _ _ _).symm.trans ((congrArg _ e1.symm).trans (hδ.trans h0))

noncomputable abbrev resClass : groupCohomology (res S.subtype M) 2 :=
  map S.subtype (𝟙 (res S.subtype M)) 2 u

noncomputable abbrev splitδ :
    groupCohomology (res S.subtype (augIdeal ℤ G)) 1 ⟶ groupCohomology (res S.subtype M) 2 :=
  δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 2 rfl


omit [Fintype S] in
theorem splitδ_augClass : splitδ M u S (augClass S) = resClass M u S :=
  δ_splittingSES_res_δ₀ M u S.subtype

theorem splitδ_injective (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    Function.Injective (splitδ M u S) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_augClass S y
  rw [map_zsmul, splitδ_augClass] at hy
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 hy
  rw [h2, Nat.card_eq_fintype_card] at hd
  obtain ⟨t, rfl⟩ := hd
  rw [mul_comm, mul_zsmul, card_smul_augClass, zsmul_zero]


omit [Fintype S] in
theorem splitδ_surjective
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    Function.Surjective (splitδ M u S) := by
  intro y
  obtain ⟨m, rfl⟩ := h3 y
  exact ⟨m • augClass S, by rw [map_zsmul, splitδ_augClass]⟩

theorem isZero_groupCohomology_res_augIdeal_two :
    IsZero (groupCohomology (res S.subtype (augIdeal ℤ G)) 2) := by
  have hep : Epi (δ (augTrivSES_res_shortExact ℤ S.subtype) 1 2 rfl) :=
    epi_δ_of_isZero (augTrivSES_res_shortExact ℤ S.subtype) 1
      (isZero_groupCohomology_res_leftRegular S 2)
  refine isZero_of_forall_eq_zero fun x => ?_
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective _).1 hep x
  have hz : IsZero (groupCohomology (res S.subtype (Rep.trivial ℤ G ℤ)) 1) :=
    isZero_H1_trivial_int (H := S)
  exact (congrArg _ (eq_zero_of_isZero hz z)).trans (map_zero _)

theorem isZero_groupCohomology_res_splittingModule_one
    (h1 : IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : addOrderOf (resClass M u S) = Nat.card S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 1) :=
  isZero_X₂_of_injective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 h1
    (splitδ_injective M u S h2)

theorem isZero_groupCohomology_res_splittingModule_two
    (h3 : ∀ y : groupCohomology (res S.subtype M) 2, ∃ m : ℤ, y = m • resClass M u S) :
    IsZero (groupCohomology (res S.subtype (splittingModule M u)) 2) :=
  isZero_X₂_succ_of_surjective_δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1
    (isZero_groupCohomology_res_augIdeal_two S) (splitδ_surjective M u S h3)


omit [Fintype S] in
theorem cohTrivial_splittingModule
    (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
    (h2 : ∀ S : Subgroup G, addOrderOf (map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
      ∃ m : ℤ, y = m • map S.subtype (𝟙 (res S.subtype M)) 2 u) :
    CohTrivial (splittingModule M u) := by
  refine cohTrivial_of_forall_subgroup _ 1 fun T _ => ⟨?_, ?_⟩
  · exact (isZero_groupCohomology_res_splittingModule_one M u T (h1 T) (h2 T)).of_iso
      (tateIsoH _ 1 1 rfl)
  · exact (isZero_groupCohomology_res_splittingModule_two M u T (h3 T)).of_iso
      (tateIsoH _ (1 + 1) 2 (by norm_num))

end Tate

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.TateDeltaZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {X : ShortComplex (Rep.{u} k G)}
  (hX : X.ShortExact)

theorem tateIsoH_δ_zero_apply (z : X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = d₀₁ X.X₂ y) (c : (tateComplex X.X₃).cycles 0)
    (hc : ((tateComplex X.X₃).iCycles 0).hom c = (cochainsIso₀ X.X₃).inv.hom z) :
    (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom
      ((TateCohomology.δ hX 0).hom (((tateComplex X.X₃).homologyπ 0).hom c)) =
      H1π X.X₁ ⟨x, mem_cocycles₁_of_comp_eq_d₀₁ hX hx⟩ := by
  have hxc : x ∈ cocycles₁ X.X₁ := mem_cocycles₁_of_comp_eq_d₀₁ hX hx
  let x₁ : (tateComplex X.X₁).X (0 + 1) := (cochainsIso₁ X.X₁).inv.hom x
  let x₂ : (tateComplex X.X₂).X 0 := (cochainsIso₀ X.X₂).inv.hom y
  have hd : ((tateComplex X.X₁).d (0 + 1) (0 + 1 + 1)).hom x₁ = 0 := by
    have e := congr(($(eq_d₁₂_comp_inv X.X₁)).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    have h0 : d₁₂ X.X₁ x = 0 := LinearMap.mem_ker.1 hxc
    rw [h0, map_zero] at e
    exact e
  have hx₂ : ((tateComplex.map X.g).f 0).hom x₂ = ((tateComplex X.X₃).iCycles 0).hom c := by
    rw [hc]
    funext v
    exact hy
  have hx₁ : ((tateComplex.map X.f).f (0 + 1)).hom x₁ = ((tateComplex X.X₂).d 0 (0 + 1)).hom x₂ := by
    have e := congr(($(eq_d₀₁_comp_inv X.X₂)).hom y)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    refine Eq.trans ?_ e.symm
    funext v
    exact congrFun hx (v 0)
  have h1 := tδ_apply hX 0 (((tateComplex X.X₃).iCycles 0).hom c)
    (tate_d_iCycles_int _ 0 c) x₂ hx₂ x₁ hx₁ hd
  rw [tateCyclesMk_iCycles] at h1
  have h2 := tateIsoH_homologyπ X.X₁ 1 (tateCyclesMk X.X₁ (0 + 1) x₁ hd)
  refine (congrArg (tateIsoH X.X₁ (0 + 1) 1 (by norm_num)).hom.hom h1).trans (h2.trans ?_)
  have h3 := cocyclesMk₁_eq X.X₁ ⟨x, hxc⟩
  refine Eq.trans ?_ (congrArg (π X.X₁ 1).hom h3)
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans ((iCycles_tateCyclesMk _ _ _ _).trans (iCocycles_mk _ _).symm)

end GroundTheory.GroupCoh
end

set_option maxSynthPendingDepth 1

open CategoryTheory Limits Rep

namespace GroundTheory.GroupCoh

section Basics

variable {G : Type} [Group G] [Fintype G] (S : Subgroup G) [Fintype S]


omit [Fintype G] in
noncomputable def tateOneClass : tateCohomology (Rep.trivial ℤ S ℤ) 0 :=
  ((tateCohomologyZeroIso (R := ℤ) (G := S)).app (Rep.trivial ℤ S ℤ)).inv.hom
    (Submodule.Quotient.mk ⟨(1 : ℤ), fun _ => rfl⟩)

end Basics

section Tate

variable {G : Type} [Group G] [Fintype G] (M : Rep ℤ G) (u : groupCohomology M 2)
  (h1 : ∀ S : Subgroup G, IsZero (groupCohomology (res S.subtype M) 1))
  (h2 : ∀ S : Subgroup G,
    addOrderOf (groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u) = Nat.card S)
  (h3 : ∀ (S : Subgroup G) (y : groupCohomology (res S.subtype M) 2),
    ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u)

include h1 h2 h3

noncomputable def tateTheoremIsoTop (n : ℤ) :
    tateCohomology (Rep.trivial ℤ G ℤ) n ≅ tateCohomology M (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_shortExact ℤ G) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_shortExact ℤ G) (tateAcyclic_leftRegular (k := ℤ)) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ (splittingSES_shortExact M u) (n + 1))
      (isIso_δ_of_tateAcyclic (splittingSES_shortExact M u)
        (cohTrivial_splittingModule M u h1 h2 h3).tateAcyclic (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology M) (by ring))

variable (S : Subgroup G) [Fintype S]

noncomputable def tateTheoremIso (n : ℤ) :
    tateCohomology (Rep.trivial ℤ S ℤ) n ≅ tateCohomology (res S.subtype M) (n + 2) :=
  @asIso _ _ _ _ (TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) n)
      (isIso_δ_of_tateAcyclic (augTrivSES_res_shortExact ℤ S.subtype)
        (tateAcyclic_res_leftRegular S) n) ≪≫
    @asIso _ _ _ _ (TateCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (n + 1))
      (isIso_δ_of_tateAcyclic ((shortExact_res S.subtype).2 (splittingSES_shortExact M u))
        (cohTrivial_splittingModule M u h1 h2 h3 S) (n + 1)) ≪≫
    eqToIso (congrArg (tateCohomology (res S.subtype M)) (by ring))

theorem tateTheoremIso_zero_apply :
    (tateIsoH (res S.subtype M) (0 + 2) 2 (by norm_num)).hom.hom
      ((tateTheoremIso M u h1 h2 h3 S 0).hom.hom (tateOneClass S)) =
      groupCohomology.map S.subtype (𝟙 (res S.subtype M)) 2 u := by
  obtain ⟨c, hc⟩ := exists_tateComplex_cycles_zero (Rep.trivial ℤ S ℤ) ⟨(1 : ℤ), fun _ => rfl⟩
  have hcls : tateOneClass S = ((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c :=
    tateCohomologyZeroIso_inv_mk _ c _ hc.symm
  have hx : ((augTrivSES ℤ G).map (resFunctor S.subtype)).f.hom ∘
      (fun s : S => augIdealSubOne (k := ℤ) (s : G)) =
      groupCohomology.d₀₁ ((augTrivSES ℤ G).map (resFunctor S.subtype)).X₂
        (MonoidAlgebra.single (1 : G) (1 : ℤ)) := by
    funext h
    change MonoidAlgebra.single (h : G) (1 : ℤ) - MonoidAlgebra.single 1 1 =
      (Rep.leftRegular ℤ G).ρ (h : G) (MonoidAlgebra.single 1 1) - MonoidAlgebra.single 1 1
    rw [Representation.ofMulAction_single, smul_eq_mul, mul_one]
  have ha := tateIsoH_δ_zero_apply (augTrivSES_res_shortExact ℤ S.subtype)
    (oneInvariant ℤ S.subtype) (MonoidAlgebra.single (1 : G) (1 : ℤ))
    (by exact augmentation_single (k := ℤ) (1 : G) (1 : ℤ)) _ hx c hc
  have hcoc : (⟨fun s : S => augIdealSubOne (k := ℤ) (s : G),
      groupCohomology.mem_cocycles₁_of_comp_eq_d₀₁ (augTrivSES_res_shortExact ℤ S.subtype) hx⟩ :
        groupCohomology.cocycles₁ (res S.subtype (augIdeal ℤ G))) = augCocycle ℤ S.subtype := rfl
  have hs : (tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₁ ((1 : ℕ) + 1) (1 + 1)
      (Nat.cast_succ 1).symm).hom.hom
      ((tδ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) (1 : ℕ) ((1 : ℕ) + 1)
        rfl).hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) =
      (groupCohomology.δ ((shortExact_res S.subtype).2 (splittingSES_shortExact M u)) 1 (1 + 1)
        rfl).hom ((tateIsoH ((splittingSES M u).map (resFunctor S.subtype)).X₃ (1 : ℕ) 1
          rfl).hom.hom ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
            (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c))) :=
    congr(($(tδ_comp_tateIsoH ((shortExact_res S.subtype).2
      (splittingSES_shortExact M u)) 1)).hom
        ((TateCohomology.δ (augTrivSES_res_shortExact ℤ S.subtype) 0).hom
          (((tateComplex (Rep.trivial ℤ S ℤ)).homologyπ 0).hom c)))
  have key := δ_splittingSES_res_δ₀ M u S.subtype
  rw [δ₀_augTrivSES_res] at key
  rw [hcls]
  refine hs.trans ?_
  refine Eq.trans ?_ key
  exact congrArg (groupCohomology.δ ((shortExact_res S.subtype).2
    (splittingSES_shortExact M u)) 1 2 rfl).hom (ha.trans (congrArg _ hcoc))

end Tate

end GroundTheory.GroupCoh
