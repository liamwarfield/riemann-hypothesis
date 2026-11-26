module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  let x' : m := ⟨x, hx⟩
  let v0 : CotangentSpace R := m.toCotangent x'
  have hx0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  let L : Submodule (ResidueField R) (CotangentSpace R) := Submodule.span _ {v0}
  have hL : Module.finrank (ResidueField R) L = 1 := finrank_span_singleton hx0
  set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq
  have hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [hq, ← hL, L.finrank_quotient_add_finrank]
  let bW := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)
  have hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i := by
    intro i
    obtain ⟨v, hv⟩ := L.mkQ_surjective (bW i)
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective v
    exact ⟨y, hv⟩
  choose t ht using hlift
  let s : Set m := insert x' (Set.range t)
  have hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤ := by
    set S := Submodule.span (ResidueField R) (m.toCotangent '' s)
    have hLS : L ≤ S := Submodule.span_le.mpr (by
      rintro _ rfl
      exact Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)
    have hmap : S.map L.mkQ = ⊤ := by
      rw [eq_top_iff, ← bW.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩,
        ht i⟩
    rw [Submodule.map_mkQ_eq_top] at hmap
    rwa [sup_eq_right.mpr hLS] at hmap
  have hspanR : Submodule.span R s = ⊤ := CotangentSpace.span_image_eq_top_iff.mp hspan
  have hmspan : m = Ideal.span (Subtype.val '' s) := by
    have := Submodule.map_span m.subtype s
    rw [hspanR, Submodule.map_subtype_top] at this
    exact this
  have hmax : maximalIdeal (R ⧸ span {x}) =
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm,
      congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]
    have : (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) =
        insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
      simp only [s, Set.image_insert_eq, ← Set.range_comp]
      congr 1
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [this, Ideal.span_insert_zero]
  have hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q := by
    rw [hmax]
    have hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) =
        ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) :
          Finset (R ⧸ span {x})) : Set (R ⧸ span {x})) := by simp
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [hfin, Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  have hmr : m.spanFinrank = q + 1 := by
    rw [hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
    exact hdim.symm
  omega

private lemma exists_nat_of_le_add_one {d : WithBot ℕ∞} {n b : ℕ} (h2 : (n : WithBot ℕ∞) ≤ d + 1)
    (h3 : d ≤ b) : ∃ k : ℕ, d = k := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) := h3
      rw [WithBot.coe_le_coe, top_le_iff] at h4
      exact ENat.natCast_ne_top b h4
    | coe k => exact ⟨k, rfl⟩

theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp inferInstance).symm
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact (span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})
  rw [hR] at h2
  obtain ⟨k, hk⟩ := exists_nat_of_le_add_one h2 h3
  rw [hk] at h2 h3 ⊢
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  have hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k := by omega
  refine ⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩
  rw [hR]
  exact_mod_cast (by omega : k + 1 = (maximalIdeal R).spanFinrank)

theorem IsRegularLocalRing.isDomain [IsRegularLocalRing R] : IsDomain R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → IsDomain S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (hn.trans h0)
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have hdim : ringKrullDim S = (n : WithBot ℕ∞) := by
      rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hmin : ∀ P ∈ minimalPrimes S, ¬ maximalIdeal S ≤ P := by
      intro P hP hle
      have hPm : P = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.1.1.ne_top) hle
      have : (maximalIdeal S).height = 0 := by
        rw [Ideal.height_eq_zero_iff, ← hPm]; exact hP
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, this] at hdim
      exact h0 (by exact_mod_cast hdim.symm)
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      exact h0 (by rw [← hn, this]; simp)
    classical
    have hfin := minimalPrimes.finite_of_isNoetherianRing S
    obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
        x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
      by_contra! hcon
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
        (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h h1
          · exact ((Set.Finite.mem_toFinset _).mp h).1.1)).mp hcon
      rcases Finset.mem_insert.mp hi with h | h
      · exact hsq (h ▸ hle)
      · exact hmin i ((Set.Finite.mem_toFinset _).mp h) hle
    simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
      Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
    obtain ⟨hx2, hxP⟩ := hxn
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have := ih _ (by omega) (S ⧸ span {x}) rfl
    have hprime : (span {x} : Ideal S).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le
    have hxP' : x ∉ P := hxP P hP
    have hPsmul : P ≤ maximalIdeal S • P := by
      intro y hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp (hPle hy)
      have hz : z ∈ P := (hP.1.1.mem_or_mem hy).resolve_right hxP'
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hz
    have hPbot : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsmul hjac
    have : (⊥ : Ideal S).IsPrime := hPbot ▸ hP.1.1
    exact IsDomain.of_bot_isPrime S

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Limits Opposite Abelian

universe w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section ExtIso

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w'} 𝒜]

noncomputable def extAddEquivOfIsoLeft {X X' : 𝒜} (e : X ≅ X') (Y : 𝒜) (n : ℕ) :
    Ext X Y n ≃+ Ext X' Y n where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add n)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp [Ext.comp_add]

end ExtIso

section Terminal

variable [HasSheafify J AddCommGrpCat.{v}]

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

end Terminal

section Zero

noncomputable def freeYonedaHomAddEquiv (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) ≃+ P.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P).trans yonedaEquiv
  map_add' _ _ := rfl

lemma freeYonedaHomAddEquiv_apply (U : C) (P : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (g : yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ P) :
    freeYonedaHomAddEquiv U P g = g.app (op U) (FreeAbelianGroup.of (𝟙 U)) := rfl

variable [HasSheafify J AddCommGrpCat.{v}]

noncomputable abbrev freeSheaf (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

noncomputable def freeSheafHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    (freeSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homAddEquiv _ F).trans
    (freeYonedaHomAddEquiv U F.obj)

lemma freeSheafHomAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (g : freeSheaf J U ⟶ F) (φ : F ⟶ G) :
    freeSheafHomAddEquiv U G (g ≫ φ) = φ.hom.app (op U) (freeSheafHomAddEquiv U F g) := by
  simp only [freeSheafHomAddEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    freeYonedaHomAddEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

noncomputable def H'.equiv₀ (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).trans (freeSheafHomAddEquiv U F)

lemma cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (n : ℕ) (U : C) (x : F.H' n U) :
    ((Sheaf.cohomologyPresheafFunctor J n).map φ).app (op U) x =
      (show Ext (freeSheaf J U) F n from x).comp (Ext.mk₀ φ) (add_zero n) := rfl

lemma H'.equiv₀_naturality {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H'.equiv₀ G U (((Sheaf.cohomologyPresheafFunctor J 0).map φ).app (op U) x) =
      φ.hom.app (op U) (H'.equiv₀ F U x) := by
  rw [cohomologyPresheafFunctor_map_app_apply]
  obtain ⟨g, rfl⟩ := (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).symm.surjective x
  change freeSheafHomAddEquiv U G (Ext.addEquiv₀ ((Ext.addEquiv₀.symm g).comp (Ext.mk₀ φ)
      (add_zero 0))) = φ.hom.app (op U) (freeSheafHomAddEquiv U F
        (Ext.addEquiv₀ (Ext.addEquiv₀.symm g)))
  rw [AddEquiv.apply_symm_apply, ← freeSheafHomAddEquiv_naturality, Ext.addEquiv₀_symm_apply,
    Ext.mk₀_comp_mk₀]
  congr 1
  apply (Ext.mk₀_bijective _ _).injective
  simp

end Zero

section Injective

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

lemma H.eq_zero_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] {n : ℕ}
    (x : Sheaf.H F (n + 1)) : x = 0 :=
  Ext.eq_zero_of_injective x

instance H'.subsingleton_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F] (n : ℕ)
    (U : C) : Subsingleton (F.H' (n + 1) U) :=
  subsingleton_of_forall_eq 0 fun x =>
    Ext.eq_zero_of_injective (show Ext (freeSheaf J U) F (n + 1) from x)

end Injective

section LongExact

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

noncomputable def H.δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Sheaf.H S.X₃ n₀ →+ Sheaf.H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

lemma H.δ_apply (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl


include hS in
theorem H.exact₂ {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y :=
  Ext.covariant_sequence_exact₂ _ hS y hy

theorem H.exact₃ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (y : Sheaf.H S.X₃ n₀)
    (hy : H.δ hS n₀ n₁ h y = 0) : ∃ x : Sheaf.H S.X₂ n₀, Sheaf.H.map S.g n₀ x = y :=
  Ext.covariant_sequence_exact₃ _ hS y h hy

theorem H.exact₁ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₁ n₁)
    (hx : Sheaf.H.map S.f n₁ x = 0) : ∃ y : Sheaf.H S.X₃ n₀, H.δ hS n₀ n₁ h y = x :=
  Ext.covariant_sequence_exact₁ _ hS x hx h

lemma H.map_g_map_f {n : ℕ} (x : Sheaf.H S.X₁ n) :
    Sheaf.H.map S.g n (Sheaf.H.map S.f n x) = 0 := by
  rw [← Sheaf.H.map_comp_apply, S.zero, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

lemma H.δ_map_g {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₂ n₀) :
    H.δ hS n₀ n₁ h (Sheaf.H.map S.g n₀ x) = 0 := by
  rw [H.δ_apply, Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
    Ext.comp_zero]

lemma H.map_f_δ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (H.δ hS n₀ n₁ h x) = 0 := by
  rw [H.δ_apply, Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp,
    Ext.comp_zero]

end LongExact

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory Opposite TopologicalSpace

universe w u v

variable {X : TopCat.{u}} {ι : Type w}

def inter (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) : Opens X := ⨅ a, U (i a)

lemma inter_le_comp (U : ι → Opens X) {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) :
    inter U i ≤ inter U (i ∘ θ) :=
  le_iInf fun a => iInf_le (fun b => U (i b)) (θ a)

lemma inter_le (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) (a : Fin n) : inter U i ≤ U (i a) :=
  iInf_le (fun b => U (i b)) a

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

abbrev Cochain (n : ℕ) : Type (max w u) := ∀ i : Fin (n + 1) → ι, P.obj (op (inter U i))

def res {V W : Opens X} (h : V ≤ W) : P.obj (op W) →+ P.obj (op V) :=
  (P.map (homOfLE h).op).hom

@[simp] lemma res_res {V W Z : Opens X} (h₁ : V ≤ W) (h₂ : W ≤ Z) (x : P.obj (op Z)) :
    res P h₁ (res P h₂ x) = res P (h₁.trans h₂) x := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

@[simp] lemma res_refl {V : Opens X} (h : V ≤ V) (x : P.obj (op V)) : res P h x = x := by
  simp only [res]
  have : (homOfLE h).op = 𝟙 (op V) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

def cochainMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Cochain P U m →+ Cochain P U n where
  toFun σ i := res P (inter_le_comp U i θ) (σ (i ∘ θ))
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp

noncomputable def cechCosimplicial : CosimplicialObject AddCommGrpCat.{max w u} where
  obj n := AddCommGrpCat.of (Cochain P U n.len)
  map θ := AddCommGrpCat.ofHom (cochainMap P U θ.toOrderHom)
  map_id n := by
    ext σ i
    simp only [cochainMap]
    exact res_refl P _ _
  map_comp θ θ' := by
    ext σ i
    simp [cochainMap]
    rfl

lemma hom_finset_sum_apply {M N : AddCommGrpCat.{v}} {α : Type*} (s : Finset α)
    (f : α → (M ⟶ N)) (x : M) : (∑ a ∈ s, f a).hom x = ∑ a ∈ s, (f a).hom x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add, AddMonoidHom.add_apply, ih]

noncomputable def d (n : ℕ) : Cochain P U n →+ Cochain P U (n + 1) :=
  (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial P U) n).hom

lemma d_apply (n : ℕ) (σ : Cochain P U n) (i : Fin (n + 2) → ι) :
    d P U n σ i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      res P (inter_le_comp U i k.succAbove) (σ (i ∘ k.succAbove)) := by
  have h := hom_finset_sum_apply Finset.univ
    (fun k : Fin (n + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (cechCosimplicial P U).δ k) σ
  refine (congrFun h i).trans ((Finset.sum_apply i _ _).trans ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

lemma d_d (n : ℕ) (σ : Cochain P U n) : d P U (n + 1) (d P U n σ) = 0 := by
  have := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cechCosimplicial P U) n
  have h2 := congrArg (fun f => f.hom σ) this
  exact h2


variable {P} in
def push {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) :
    Cochain P U n →+ Cochain P' U n where
  toFun σ i := φ.app _ (σ i)
  map_zero' := by ext i; simp
  map_add' σ τ := by ext i; simp

variable {P} in
lemma app_res {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') {V W : Opens X} (h : V ≤ W)
    (x : P.obj (op W)) : φ.app (op V) (res P h x) = res P' h (φ.app (op W) x) := by
  simp only [res, ← ConcreteCategory.comp_apply, φ.naturality]

variable {P} in
lemma push_d {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) (σ : Cochain P U n) :
    push U φ (n + 1) (d P U n σ) = d P' U n (push U φ n σ) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [push, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul, app_res]

variable {P} in
lemma push_comp {P' P'' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (ψ : P' ⟶ P'')
    (n : ℕ) (σ : Cochain P U n) : push U ψ n (push U φ n σ) = push U (φ ≫ ψ) n σ := by
  funext i
  simp [push]

variable {P} in
lemma push_id (n : ℕ) (σ : Cochain P U n) : push U (𝟙 P) n σ = σ := by
  funext i
  simp [push]

def CechAcyclic : Prop :=
  ∀ (n : ℕ) (σ : Cochain P U (n + 1)), d P U (n + 1) σ = 0 → ∃ τ, d P U n τ = σ

variable {P} in
lemma push_zero' {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (n : ℕ) (σ : Cochain P U n) :
    push U (0 : P ⟶ P') n σ = 0 := by
  funext i
  simp [push]

variable {P} in
lemma push_injective {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ)
    (h : ∀ i : Fin (n + 1) → ι, Function.Injective (φ.app (op (inter U i)))) :
    Function.Injective (push U φ n) := fun _ _ hστ =>
  funext fun i => h i (congrFun hστ i)


variable {P} in
lemma CechAcyclic.of_retract {G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (ι' : P ⟶ G) (r : G ⟶ P)
    (hr : ι' ≫ r = 𝟙 P) (hG : CechAcyclic G U) : CechAcyclic P U := by
  intro n σ hσ
  obtain ⟨τ, hτ⟩ := hG n (push U ι' (n + 1) σ) (by rw [← push_d, hσ, map_zero])
  refine ⟨push U r n τ, ?_⟩
  rw [← push_d, hτ, push_comp, hr, push_id]


def discPresheaf (A : X → AddCommGrpCat.{u}) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (∀ x : W.unop, A x.1)
  map h := AddCommGrpCat.ofHom
    { toFun := fun s x => s ⟨x.1, h.unop.le x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

variable (A : X → AddCommGrpCat.{u})

def ev {W : Opens X} (x : X) (hx : x ∈ W) : (discPresheaf A).obj (op W) →+ A x :=
  Pi.evalAddMonoidHom (fun y : W => A y.1) ⟨x, hx⟩

lemma ev_res {V W : Opens X} (h : V ≤ W) (s : (discPresheaf A).obj (op W)) (x : X) (hx : x ∈ V) :
    ev A x hx (res (discPresheaf A) h s) = ev A x (h hx) s := rfl

variable {U} in
lemma ev_congr {n : ℕ} (σ : Cochain (discPresheaf A) U n) {j₁ j₂ : Fin (n + 1) → ι}
    (h : j₁ = j₂) (x : X) (h₁ : x ∈ inter U j₁) (h₂ : x ∈ inter U j₂) :
    ev A x h₁ (σ j₁) = ev A x h₂ (σ j₂) := by
  subst h
  rfl

lemma ev_d {n : ℕ} (σ : Cochain (discPresheaf A) U n) (i : Fin (n + 2) → ι) (x : X)
    (hx : x ∈ inter U i) :
    ev A x hx (d (discPresheaf A) U n σ i) = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      ev A x (inter_le_comp U i k.succAbove hx) (σ (i ∘ k.succAbove)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, ev_res]

lemma mem_inter_iff {n : ℕ} (i : Fin n → ι) (x : X) : x ∈ inter U i ↔ ∀ a, x ∈ U (i a) := by
  rw [inter, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

attribute [irreducible] inter

lemma cons_comp_succAbove_zero {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext a
  simp

lemma cons_comp_succAbove_succ {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons c (i ∘ k.succAbove) := by
  funext a
  cases a using Fin.cases with
  | zero => simp
  | succ a => simp

noncomputable def chosenIdx (x : X) (h : ∃ a, x ∈ U a) : ι := h.choose

lemma mem_chosenIdx (x : X) (h : ∃ a, x ∈ U a) : x ∈ U (chosenIdx U x h) := h.choose_spec

lemma exists_mem_of_mem_inter {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    ∃ a, x ∈ U a :=
  ⟨j 0, (mem_inter_iff U j x).1 hx 0⟩

lemma mem_inter_cons {m : ℕ} (j : Fin (m + 1) → ι) {x : X} (hx : x ∈ inter U j) :
    x ∈ inter U (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j :
      Fin (m + 2) → ι) := by
  rw [mem_inter_iff]
  intro a
  cases a using Fin.cases with
  | zero => simpa using mem_chosenIdx U x _
  | succ a => simpa using (mem_inter_iff U j x).1 hx a

noncomputable def homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) :
    Cochain (discPresheaf A) U n :=
  fun j y => ev A y.1 (mem_inter_cons U j y.2)
    (σ (Fin.cons (chosenIdx U y.1 (exists_mem_of_mem_inter U j y.2)) j))

lemma ev_homotopy {n : ℕ} (σ : Cochain (discPresheaf A) U (n + 1)) (j : Fin (n + 1) → ι)
    (x : X) (hx : x ∈ inter U j) :
    ev A x hx (homotopy U A σ j) = ev A x (mem_inter_cons U j hx)
      (σ (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U j hx)) j)) := rfl

theorem cechAcyclic_discPresheaf : CechAcyclic (discPresheaf A) U := by
  intro n σ hσ
  refine ⟨homotopy U A σ, funext fun i => funext fun y => ?_⟩
  obtain ⟨x, hx⟩ := y
  have hJ := mem_inter_cons U i hx
  have hcoc : ev A x hJ (d (discPresheaf A) U (n + 1) σ
      (Fin.cons (chosenIdx U x (exists_mem_of_mem_inter U i hx)) i)) = 0 := by
    rw [hσ]
    rfl
  rw [ev_d, Fin.sum_univ_succ] at hcoc
  change ev A x hx (d (discPresheaf A) U n (homotopy U A σ) i) = ev A x hx (σ i)
  rw [ev_d]
  rw [Fin.val_zero, pow_zero, one_smul,
    ev_congr A σ (cons_comp_succAbove_zero _ i) x _ hx] at hcoc
  rw [eq_neg_of_add_eq_zero_left hcoc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg, ev_homotopy]
  exact congrArg _ (ev_congr A σ (cons_comp_succAbove_succ _ i k).symm x _ _)

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

def PrimeDivisor (X : Scheme.{u}) : Type u :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}

abbrev WeilDivisor (X : Scheme.{u}) : Type u := PrimeDivisor X →₀ ℤ

variable {X : Scheme.{u}}

namespace PrimeDivisor

def point (x : PrimeDivisor X) : X := x.1

lemma ringKrullDim_stalk (x : PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk x.point) = 1 := x.2

lemma coheight_point (x : PrimeDivisor X) : Order.coheight x.point = 1 := by
  have h := x.ringKrullDim_stalk
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

lemma point_injective : Function.Injective (point (X := X)) := fun _ _ h => Subtype.ext h

lemma maximalIdeal_ne_bot (x : PrimeDivisor X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) ≠ ⊥ := by
  intro h
  have hf : IsField (X.presheaf.stalk x.point) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  have := x.ringKrullDim_stalk
  rw [ringKrullDim_eq_zero_of_isField hf] at this
  exact zero_ne_one this

variable [IsIntegral X]

lemma dimensionLEOne_stalk (x : PrimeDivisor X) :
    Ring.DimensionLEOne (X.presheaf.stalk x.point) := by
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point) := by
    rw [Ring.krullDimLE_iff, x.ringKrullDim_stalk]
    norm_num
  refine ⟨fun {p} hp hprime => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
  · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
    exact absurd h hp
  · exact h

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma isDedekindDomain_stalk (x : PrimeDivisor X) :
    IsDedekindDomain (X.presheaf.stalk x.point) := by
  have := x.dimensionLEOne_stalk
  have := IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point
  exact (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩

noncomputable def heightOneSpectrum (x : PrimeDivisor X) :
    HeightOneSpectrum (X.presheaf.stalk x.point) :=
  ⟨IsLocalRing.maximalIdeal _, (IsLocalRing.maximalIdeal.isMaximal _).isPrime,
    x.maximalIdeal_ne_bot⟩

noncomputable def valuation (x : PrimeDivisor X) : Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
  @HeightOneSpectrum.valuation _ _ x.isDedekindDomain_stalk _ _ _ _ x.heightOneSpectrum

noncomputable def ord (x : PrimeDivisor X) (f : X.functionField) : ℤ :=
  - WithZero.log (x.valuation f)

lemma ord_mul (x : PrimeDivisor X) {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    x.ord (f * g) = x.ord f + x.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]
  ring

end PrimeDivisor

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma ord_algebraMap_of_isUnit (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsUnit a) : x.ord (algebraMap _ X.functionField a) = 0 := by
  have := x.isDedekindDomain_stalk
  have h1 : x.valuation (algebraMap _ X.functionField a) = 1 := by
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha
  simp [ord, h1]

lemma ord_germToFunctionField_of_isUnit (x : PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (hx : x.point ∈ U) {g : Γ(X, U)} (hg : IsUnit g) :
    x.ord (X.germToFunctionField U g) = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact x.ord_algebraMap_of_isUnit (hg.map _)

end PrimeDivisor

lemma PrimeDivisor.eq_genericPoint_of_mem [IsIntegral X] (x : PrimeDivisor X) {T : Set X}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hgen : genericPoint X ∉ T) (hx : x.point ∈ T) :
    x.point = hT.genericPoint := by
  set c := hT.genericPoint
  have hc : IsGenericPoint c T := by
    have := hT.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  have hcx : c ⤳ x.point := hc.specializes hx
  have hcT : c ∈ T := hc.mem
  have hηc : genericPoint X ⤳ c := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hηne : genericPoint X ≠ c := fun h => hgen (h ▸ hcT)
  have hlt1 : c < genericPoint X := by
    refine ⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩
  by_contra hne
  have hlt2 : x.point < c := ⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h2 := Order.coheight_add_one_le hlt2
  rw [x.coheight_point] at h2
  have h4 : (1 : ℕ∞) ≤ Order.coheight c := le_trans le_add_self h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h4 1) h2
  norm_num at h5

section Finite

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]

theorem PrimeDivisor.finite_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : PrimeDivisor X | x.ord f ≠ 0}.Finite := by
  obtain ⟨U, -, g, hne, hgf, hgu⟩ := exists_isUnit_germ_eq X f hf
  set Z : Set X := (U : Set X)ᶜ with hZ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have hgenU : genericPoint X ∈ U := by
    obtain ⟨⟨y, hy⟩⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z} := by
    intro x hx
    by_contra hxU
    simp only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU
    exact hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)
  refine Set.Finite.subset ?_ hsub
  have key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z),
      C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C →
      ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint := by
    intro x hx C hC hxC
    have hT : IsIrreducible (closure (Subtype.val '' C)) :=
      (hC.1.image _ continuous_subtype_val.continuousOn).closure
    refine ⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩
    · intro hg
      have : closure (Subtype.val '' C) ⊆ Z :=
        closure_minimal (Subtype.coe_image_subset _ _) hZc
      exact this hg hgenU
    · exact subset_closure ⟨_, hxC, rfl⟩
  have hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z,
      {(⟨x.1.point, x.2⟩ : Z)} ⊆ C := fun x =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton
  let φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z := fun x =>
    ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := (hcomp x).choose_spec
    have hy := (hcomp y).choose_spec
    have hC : (hcomp x).choose = (hcomp y).choose := congrArg Subtype.val hxy
    obtain ⟨hT, hxT⟩ := key x.1 x.2 _ hx.1 (hx.2 rfl)
    obtain ⟨hT', hyT⟩ := key y.1 y.2 _ hy.1 (hy.2 rfl)
    apply Subtype.ext
    apply PrimeDivisor.point_injective
    rw [hxT, hyT]
    simp only [hC]
  have : Finite {x : PrimeDivisor X | x.point ∈ Z} := Finite.of_injective φ hφ
  exact Set.toFinite _

end Finite

section Divisor

variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]



end Divisor

end GroundTheory.Arith.SchemeCoh
end
