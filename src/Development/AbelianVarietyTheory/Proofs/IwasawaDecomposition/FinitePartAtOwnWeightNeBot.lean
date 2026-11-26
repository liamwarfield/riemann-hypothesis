module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfIsotypicCommutingSubgroupsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfCommutingEndAlgHom
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

theorem exists_multilinear_of_commuting_endAlgHom :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)]
      [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V),
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) →
      ∃ F : (∀ v, Wv v) →ₘₗ[ℂ] V, F w = y ∧
        ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u),
          Φ v A (F x) = F (Function.update x v (A (x v))) := by
  intro ι _ hd Wv _ _ V _ _ Φ w ℓ y hc hfix
  let f : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v => Φ v ((ℓ v).smulRight (x v))
  have comm : ∀ x, ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute (f x)) :=
    fun x a _ b _ hab => hc a b hab _ _
  let G : (∀ v, Wv v) → V := fun x => (Finset.univ.noncommProd (f x) (comm x)) y

  let R : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v =>
    (Finset.univ.erase v).noncommProd (f x)
      (fun _ ha _ hb hab => comm x (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)
  have hsplit : ∀ x v, G x = f x v (R x v y) := by
    intro x v
    simp only [G, R]
    rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ v) (f x) (comm x)]
    rfl
  have hR : ∀ x v (a : Wv v), R (Function.update x v a) v = R x v := by
    intro x v a
    simp only [R]
    apply Finset.noncommProd_congr rfl
    intro u hu
    simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  have hfu : ∀ x v (a : Wv v), f (Function.update x v a) v = Φ v ((ℓ v).smulRight a) := by
    intro x v a
    simp only [f, Function.update_self]
  refine ⟨{ toFun := G, map_update_add' := ?_, map_update_smul' := ?_ }, ?_, ?_⟩
  · intro dec x v a b
    obtain rfl : dec = hd := Subsingleton.elim _ _
    have e : (ℓ v).smulRight (a + b) = (ℓ v).smulRight a + (ℓ v).smulRight b := by
      ext z; simp [smul_add]
    rw [hsplit _ v, hsplit _ v, hsplit _ v, hR, hR, hR, hfu, hfu, hfu, e, map_add (f := _),
      LinearMap.add_apply]
  · intro dec x v c a
    obtain rfl : dec = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    have e : (ℓ v).smulRight (c • a) = c • (ℓ v).smulRight a := by
      ext z; simp [smul_comm c]
    rw [hsplit _ v, hsplit _ v, hR, hR, hfu, hfu, e, map_smul, LinearMap.smul_apply]
  · show (Finset.univ.noncommProd (f w) (comm w)) y = y
    exact Finset.noncommProd_induction _ _ _ (fun T : Module.End ℂ V => T y = y)
      (fun S T hS hT => by rw [mul_apply_eq_comp, hT, hS]) rfl
      (fun v _ => hfix v)
  · intro v A x
    show Φ v A (G x) = G (Function.update x v (A (x v)))
    rw [hsplit x v, hsplit _ v, hR, hfu]
    have : (ℓ v).smulRight (A (x v)) = A * (ℓ v).smulRight (x v) := by
      ext z; simp
    rw [this, map_mul, mul_apply_eq_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVector
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVector
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

private theorem sum_smulRight_finBasis_mul_smulRight_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (w : W) (ℓ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ∑ i, ℓ.smulRight (Module.finBasis ℂ W i) * ((Module.finBasis ℂ W).coord i).smulRight w = 1 := by
  ext x
  simpa [h] using (Module.finBasis ℂ W).sum_repr x

private theorem exists_dual_algHom_smulRight_apply_ne_zero {W V : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (w : W) (ℓ : Module.Dual ℂ W)
    (h : ℓ w = 1) (Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V) {y : V} (hy : y ≠ 0) :
    ∃ φ : Module.Dual ℂ W, Φ (φ.smulRight w) y ≠ 0 := by
  by_contra! hzero
  apply hy
  calc y = Φ 1 y := by simp
    _ = ∑ i, Φ (ℓ.smulRight (Module.finBasis ℂ W i))
          (Φ (((Module.finBasis ℂ W).coord i).smulRight w) y) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← sum_smulRight_finBasis_mul_smulRight_eq_one w ℓ h, map_sum, LinearMap.sum_apply]
        simp only [map_mul, Module.End.mul_apply]
    _ = 0 := by simp [hzero]

private theorem smulRight_mul_smulRight_of_apply_eq_one {W : Type} [AddCommGroup W] [Module ℂ W]
    (w : W) (ℓ φ : Module.Dual ℂ W) (h : ℓ w = 1) :
    ℓ.smulRight w * φ.smulRight w = φ.smulRight w := by
  ext x
  simp [h]

theorem _root_.GlobalTheory.commuting_endAlgebras_common_fixed_vector :
    ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
      [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) →
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  intro ι _ Wv _ _ _ V _ _ Φ w ℓ _ hℓ hcomm
  classical
  have key : ∀ s : Finset ι, ∃ y : V, y ≠ 0 ∧ ∀ v ∈ s, Φ v ((ℓ v).smulRight (w v)) y = y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨y, hy⟩ := exists_ne (0 : V)
      exact ⟨y, hy, by simp⟩
    | insert v s hv ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      obtain ⟨φ, hφ⟩ := exists_dual_algHom_smulRight_apply_ne_zero (w v) (ℓ v) (hℓ v) (Φ v) hy0
      refine ⟨Φ v (φ.smulRight (w v)) y, hφ, fun u hu => ?_⟩
      rcases Finset.mem_insert.mp hu with rfl | hu
      · rw [← Module.End.mul_apply, ← map_mul,
          smulRight_mul_smulRight_of_apply_eq_one _ _ _ (hℓ u)]
      · have huv : u ≠ v := fun h => hv (h ▸ hu)
        rw [← Module.End.mul_apply, (hcomm u v huv _ _).eq, Module.End.mul_apply, hy u hu]
  obtain ⟨y, hy0, hy⟩ := key Finset.univ
  exact ⟨y, hy0, fun v => hy v (Finset.mem_univ v)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVectorStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images : ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) → (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  first | exact @GlobalTheory.commuting_endAlgebras_common_fixed_vector | exact GlobalTheory.commuting_endAlgebras_common_fixed_vector | (intros; apply GlobalTheory.commuting_endAlgebras_common_fixed_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwiners
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwiners
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.FinPart

open scoped MonoidAlgebra

theorem exists_algHom_end_of_span_intertwiners :
    ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V),
      σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ →
      ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  intro H W V _ _ _ _ _ _ σ ρ hirr hspan
  classical

  have hsurj : Function.Surjective σ.asAlgebraHom := by
    have hB := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hirr
    have hle : Submodule.span ℂ (Set.range σ) ≤ Subalgebra.toSubmodule σ.asAlgebraHom.range := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      exact ⟨MonoidAlgebra.single h 1, by simp [Representation.asAlgebraHom_single]⟩
    intro A
    have : A ∈ Subalgebra.toSubmodule σ.asAlgebraHom.range := hle (hB ▸ Submodule.mem_top)
    exact this

  have hint : ∀ (f : σ.IntertwiningMap ρ) (a : MonoidAlgebra ℂ H) (w : W),
      ρ.asAlgebraHom a (f.toLinearMap w) = f.toLinearMap (σ.asAlgebraHom a w) := by
    intro f a w
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add (f := _)]
    | single g c =>
      simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul]
      congr 1
      exact (Representation.IntertwiningMap.isIntertwining σ ρ f g w).symm
  have hker : RingHom.ker σ.asAlgebraHom ≤ RingHom.ker ρ.asAlgebraHom := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have hle : (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) ≤
        LinearMap.ker (ρ.asAlgebraHom a) := by
      refine iSup_le fun f => ?_
      rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker, hint, ha]
      simp
    rw [hspan, top_le_iff] at hle
    exact LinearMap.ker_eq_top.1 hle
  let Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V :=
    (Ideal.Quotient.liftₐ (RingHom.ker σ.asAlgebraHom) ρ.asAlgebraHom hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hΦ : ∀ a, Φ (σ.asAlgebraHom a) = ρ.asAlgebraHom a := by
    intro a
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a) =
        Ideal.Quotient.mk _ a := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    change Ideal.Quotient.liftₐ _ _ hker ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (σ.asAlgebraHom a)) = _
    rw [this]
    rfl
  refine ⟨Φ, fun h => ?_, fun T hT A => ?_⟩
  · have := hΦ (MonoidAlgebra.single h 1)
    simpa [Representation.asAlgebraHom_single] using this
  · obtain ⟨a, rfl⟩ := hsurj A
    rw [hΦ]
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
    | single g c =>
      rw [Representation.asAlgebraHom_single]
      exact (hT g).smul_right c

end GlobalTheory.FinPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwinersStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_endomorphism_of_span_intertwiners : ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧ ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  first | exact @GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | exact GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | (intros; apply GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners <;> assumption)
end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (H : ι → Type) [∀ v, Group (H v)] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v)), Nontrivial V → (∀ v, (σ v).IsIrreducible) → (∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b)) → (∀ v, (⨆ f : (σ v).IntertwiningMap (ρ.comp (s v)), LinearMap.range f.toLinearMap) = ⊤) → ∃ F : MultilinearMap (RingHom.id ℂ) Wv V, F ≠ 0 ∧ ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))) := by
  intro ι _ _ G V _ _ _ H _ Wv _ _ _ ρ s σ hV hirr hcomm hspan
  have hfac : ∀ v, ∃ Φ : Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V,
      (∀ h, Φ (σ v h) = ρ (s v h)) ∧
        ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ (s v h))) → ∀ A, Commute T (Φ A) :=
    fun v => GlobalTheory.T.exists_algHom_endomorphism_of_span_intertwiners
      (H v) (Wv v) V (σ v) (ρ.comp (s v)) (hirr v) (hspan v)
  choose Φ hΦσ hΦc using hfac
  have hΦcomm : ∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B) := by
    intro u v huv A B
    have h1 : ∀ b, Commute (ρ (s v b)) (Φ u A) := by
      intro b
      exact hΦc u _ (fun a => (hcomm v u (Ne.symm huv) b a).map ρ) A
    exact hΦc v (Φ u A) (fun b => (h1 b).symm) B
  have hnt : ∀ v, Nontrivial (Wv v) :=
    fun v => ((GlobalTheory.CuspRep.isIrreducible_iff _).1 (hirr v)).1
  have hw : ∀ v, ∃ w : Wv v, w ≠ 0 := fun v => exists_ne 0
  choose w hw0 using hw
  have hl : ∀ v, ∃ ℓ : Module.Dual ℂ (Wv v), ℓ (w v) = 1 := by
    intro v
    have hn : w v ∉ (⊥ : Submodule ℂ (Wv v)) := by simpa using hw0 v
    obtain ⟨f, hf, -⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    exact ⟨(f (w v))⁻¹ • f, by simp [hf]⟩
  choose ℓ hℓ using hl
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images
    ι Wv V Φ w ℓ hV hℓ hΦcomm
  obtain ⟨F, hFw, hF⟩ := GlobalTheory.exists_multilinear_of_commuting_endAlgHom
    ι Wv V Φ w ℓ y hΦcomm hy
  refine ⟨F, fun h0 => hy0 ?_, fun v h x => ?_⟩
  · rw [← hFw, h0]
    rfl
  · rw [← hΦσ v h]
    exact hF v (σ v h) x
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlaces
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem UA_ext_cEmb {a b : UA E n}
    (hfin : GeneralLinearGroup.map (pFin E) a.1 = GeneralLinearGroup.map (pFin E) b.1)
    (hinf : ∀ τ : E →+* ℂ, cEmb τ a = cEmb τ b) : a = b := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply Prod.ext
  · have key : pInf E (a.1.1 i j) = pInf E (b.1.1 i j) := by
      funext w
      have h := congrArg (fun g : GL (Fin n) ℂ => g.1 i j) (hinf w.embedding)
      simp only [cEmb, cInf, MonoidHom.comp_apply, GeneralLinearGroup.map, Subgroup.coe_subtype] at h
      change coord w.embedding (pInf E (a.1.1 i j)) = coord w.embedding (pInf E (b.1.1 i j)) at h
      have hw : InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding w
      unfold coord at h
      rw [if_pos (by rw [hw])] at h
      simpa [hw] using h
    exact (infEq E).symm.injective key
  · have h := congrArg (fun g : GL (Fin n) (Af E) => g.1 i j) hfin
    exact h

theorem embU_commute (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ)
    (hne : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') : ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  intro x hx y hy
  simp only [embU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx hy
  obtain ⟨hxf, hxi⟩ := hx
  obtain ⟨hyf, hyi⟩ := hy
  rw [infU, MonoidHom.mem_ker] at hxf hyf
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at hxf hyf
  apply UA_ext_cEmb
  · simp only [Subgroup.coe_mul, map_mul, hxf, hyf]
  · intro σ
    simp only [map_mul]
    by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
    · have : InfinitePlace.mk σ ≠ InfinitePlace.mk τ' := h ▸ hne
      rw [hyi σ this, one_mul, mul_one]
    · rw [hxi σ h, one_mul, mul_one]

end GlobalTheory.UnitaryBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteUnitaryArchimedeanPointsDistinctPlacesStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ), InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  first | exact @GlobalTheory.UnitaryBC.embU_commute | exact GlobalTheory.UnitaryBC.embU_commute | (intros; apply GlobalTheory.UnitaryBC.embU_commute <;> assumption)
end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU

theorem prod_list_apply_multilinear {ι G V : Type} [DecidableEq ι] [Group G] [AddCommGroup V] [Module ℂ V]
    {H : ι → Type} [∀ v, Group (H v)] {Wv : ι → Type} [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)]
    (ρ : Representation ℂ G V) (s : ∀ v, H v →* G) (σ : ∀ v, Representation ℂ (H v) (Wv v))
    (F : (∀ v, Wv v) →ₘₗ[ℂ] V)
    (hF : ∀ v (h : H v) (x : ∀ u, Wv u), ρ (s v h) (F x) = F (Function.update x v (σ v h (x v))))
    (y : ∀ v, H v) (u : ∀ v, Wv v) :
    ∀ L : List ι, L.Nodup →
      ρ (L.map fun v => s v (y v)).prod (F u) = F fun v => if v ∈ L then σ v (y v) (u v) else u v := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, map_mul, mul_apply_eq_comp, ih hL.2, hF]
    congr 1
    funext v
    by_cases hv : v = a
    · rw [hv, Function.update_self]
      simp [hL.1]
    · rw [Function.update_of_ne hv]
      simp [hv]

theorem AutSub.finPart_wt_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n),
    π.finPart (AU.mk π).wt ≠ ⊥ := by
  intro E _ _ _ n π
  classical
  have hW' : ∀ v : InfinitePlace E, HasWeightAt π.V v.embedding ((AU.mk π).wt v) := fun v => by
    obtain ⟨lam, hlam, -⟩ := GlobalTheory.T.existsUnique_weight_definiteUnitary_at E n (AU.mk π) v.embedding
    have h := hlam.wt
    rw [Wt.at_embedding] at h
    exact (AU.hasWt_mk π _ _).1 h
  generalize (AU.mk π).wt = W at hW' ⊢
  have hW := hW'
  clear hW'
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (W v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (W v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (W v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (W v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π v.embedding (W v) (hW v)
  have hV : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (W v)) π.rep s σ hV hirr hcomm hspan
  let B := Formalism.L2.DIV.bVV ℂ W
  let b := fun v => GlobalTheory.CoefIrred.ssBasis ℂ (W v)
  have hB : ∀ i, B i = GlobalTheory.CoefIrred.tenMul W (fun v => b v (i v)) := by
    intro i
    apply Subtype.ext
    rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.bVVfun]
    simp only [b, GlobalTheory.CoefIrred.ssBasis_coe]
  let f0 : W.Sp →ₗ[ℂ] π.V := B.constr ℂ (fun i => F (fun v => b v (i v)))
  have hf0 : ∀ u, f0 (GlobalTheory.CoefIrred.tenMul W u) = F u := by
    have hComp : f0.compMultilinearMap (GlobalTheory.CoefIrred.tenMul W) = F := by
      apply Module.Basis.ext_multilinear b
      intro i
      simp only [LinearMap.compMultilinearMap_apply, ← hB, f0, Module.Basis.constr_basis]
    intro u
    exact congrArg (fun m => m u) hComp
  let f : W.Sp →ₗ[ℂ] (UA E n → ℂ) := π.V.subtype ∘ₗ f0
  have hten : ∀ (g : InfinitePlace E → GL (Fin n) ℂ) (u : ∀ v, nablaSq ℂ n (W v)),
      Formalism.L2.DIV.rhoK W g (GlobalTheory.CoefIrred.tenMul (K := ℂ) W u) =
        GlobalTheory.CoefIrred.tenMul (K := ℂ) W fun v => GlobalTheory.Branching.sqRep ℂ n (W v) (g v) (u v) := fun g u => by
    apply Subtype.ext
    rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen, GlobalTheory.CoefIrred.tenMul_coe]
    rfl
  have hint : ∀ (x : infU E n) (w : W.Sp), f (W.rep x w) = RU E n x (f w) := by
    intro x w
    obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x.1 x.2
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, f (W.rep x (GlobalTheory.CoefIrred.tenMul W u)) = RU E n x (f (GlobalTheory.CoefIrred.tenMul W u)) := by
      intro u
      have h1 := prod_list_apply_multilinear π.rep s σ F hF y' u Finset.univ.toList (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x.1 := hprod
      rw [h2] at h1
      have h3 : W.rep x (GlobalTheory.CoefIrred.tenMul W u) = GlobalTheory.CoefIrred.tenMul W fun v => σ v (y' v) (u v) := by
        change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
        rw [hten]
        refine congrArg (GlobalTheory.CoefIrred.tenMul W) (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
        rfl
      show (f0 (W.rep x (GlobalTheory.CoefIrred.tenMul W u))).1 = RU E n x (f0 (GlobalTheory.CoefIrred.tenMul W u)).1
      rw [h3, hf0, hf0, ← AutSub.rep_val, h1]
      simp only [Finset.mem_toList, Finset.mem_univ, ite_true]
    have heq : f ∘ₗ W.rep x = RU E n x ∘ₗ f := by
      apply B.ext
      intro i
      rw [hB]
      exact key _
    exact LinearMap.congr_fun heq w
  have hmem : f ∈ algForms W := ⟨fun w => π.le_autU (f0 w).2, hint⟩
  have hfin : (⟨f, hmem⟩ : algForms W) ∈ π.finPart W := AutSub.mem_finPart.2 fun w => (f0 w).2
  obtain ⟨u, hu⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (MultilinearMap.ext h)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨f, hmem⟩, hfin, fun h => hu ?_⟩
  have := LinearMap.congr_fun (congrArg Subtype.val h) (GlobalTheory.CoefIrred.tenMul W u)
  rw [← hf0]
  exact Subtype.ext this

end GlobalTheory.DefU

end
