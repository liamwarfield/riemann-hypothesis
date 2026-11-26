module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.TateCohomology.Induced
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology groupHomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)

theorem TateAcyclic.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]

theorem TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

theorem isZero_tateCohomology_zero_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_neg_one_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_zero_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]

theorem isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]

section Coind

variable (B : Rep.{u} k (⊥ : Subgroup G))


open scoped Classical in
noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V := by
  classical
  exact LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp


open scoped Classical in
theorem sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  classical
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)

theorem isZero_tateCohomology_coind_bot (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm

theorem isZero_tateCohomology_ind_bot (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))

theorem tateAcyclic_coind_bot : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B

theorem tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B

end Coind

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.DeltaMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
end

section -- merged from GroundTheory.TateCohomology.CoindOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable (k G : Type u) [CommRing k] [Group G] (X : Type u) [AddCommGroup X] [Module k X]

noncomputable def coindOneRep : Representation k G (G → X) where
  toFun g := LinearMap.funLeft k X (· * g)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

noncomputable abbrev coindOne : Rep k G := Rep.of (coindOneRep k G X)

instance : Subsingleton (⊥ : Subgroup G) :=
  ⟨fun a b => Subtype.ext <| by rw [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]⟩

noncomputable def coindOneIsoCoind :
    coindOne k G X ≅ coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F => ⟨F, fun g h => by rw [Subsingleton.elim g 1]; simp⟩
      invFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ => LinearMap.ext fun _ => Subtype.ext rfl)

theorem isZero_coindOne (n : ℕ) : Limits.IsZero (groupCohomology (coindOne k G X) (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton (Rep.trivial k (⊥ : Subgroup G) X) n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso (coindOneIsoCoind k G X) ≪≫
      groupCohomology.coindIso _ (n + 1))

variable {G} (S : Subgroup G)

lemma out_inv_mul_mem (x : G) : ((x : G ⧸ S).out)⁻¹ * x ∈ S :=
  QuotientGroup.leftRel_apply.1 (Quotient.exact' (QuotientGroup.out_eq' (x : G ⧸ S)))

noncomputable def cosetPart (x : G) : S := ⟨((x : G ⧸ S).out)⁻¹ * x, out_inv_mul_mem S x⟩

lemma out_mul_cosetPart (x : G) : (x : G ⧸ S).out * (cosetPart S x : G) = x := by
  simp [cosetPart]

lemma mk_out_mul (c : G ⧸ S) (s : S) : ((c.out * s : G) : G ⧸ S) = c := by
  conv_rhs => rw [← QuotientGroup.out_eq' c]
  exact (QuotientGroup.eq).2 (by simp)

lemma cosetPart_out_mul (c : G ⧸ S) (s : S) : cosetPart S (c.out * s) = s := by
  apply Subtype.ext
  simp [cosetPart]

noncomputable def resCoindOneIso :
    res S.subtype (coindOne k G X) ≅ coindOne k S (G ⧸ S → X) :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F s c => F (c.out * s)
      invFun := fun F x => F (cosetPart S x) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun F => funext fun x => by
        simp only
        rw [out_mul_cosetPart]
      right_inv := fun F => funext fun s => funext fun c => by
        simp only
        rw [cosetPart_out_mul, mk_out_mul] }
    (fun t => LinearMap.ext fun F => funext fun s => funext fun c => by
      change F ((c.out * s) * t) = F (c.out * ((s * t : S) : G))
      simp [mul_assoc])

noncomputable def quotientToInvariantsCoindOneIso [S.Normal] :
    (coindOne k G X).quotientToInvariants S ≅ coindOne k (G ⧸ S) X :=
  Rep.mkIso <| Representation.Equiv.mk
    { toFun := fun F c => Quotient.liftOn' c F.1 fun x y hxy => by
        have h := congrFun (F.2 ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.1 hxy⟩) x
        change F.1 (x * (x⁻¹ * y)) = F.1 x at h
        simpa using h.symm
      invFun := fun F => ⟨fun x => F x, fun s => funext fun x => by
        change F (↑(x * (s : G)) : G ⧸ S) = F (x : G ⧸ S)
        exact congrArg F (QuotientGroup.eq.2 (by simp))⟩
      map_add' := fun F F' => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      map_smul' := fun r F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl
      left_inv := fun F => Subtype.ext rfl
      right_inv := fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl }
    (fun g => by
      induction g using QuotientGroup.induction_on
      exact LinearMap.ext fun F => funext fun c => by
        induction c using QuotientGroup.induction_on; rfl)

theorem isZero_res_coindOne (n : ℕ) :
    Limits.IsZero (groupCohomology (res S.subtype (coindOne k G X)) (n + 1)) :=
  (isZero_coindOne k S (G ⧸ S → X) n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso (resCoindOneIso k X S))

theorem isZero_quotientToInvariants_coindOne [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology ((coindOne k G X).quotientToInvariants S) (n + 1)) :=
  (isZero_coindOne k (G ⧸ S) X n).of_iso
    ((groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso (quotientToInvariantsCoindOneIso k X S))

end GroundTheory.GroupCoh
end
