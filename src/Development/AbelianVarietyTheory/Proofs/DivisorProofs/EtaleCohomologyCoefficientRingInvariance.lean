module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicResolutionComputesEtaleCohomology
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingleton
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

def coneSES {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : ShortComplex (Shv R) :=
  ShortComplex.mk ((mappingCone.inr u).f t) ((mappingCone.fst u).1.v t (t + 1) rfl) (by simp)

def coneSESSplitting {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).Splitting where
  r := (mappingCone.snd u).v t t (add_zero t)
  s := (mappingCone.inl u).v (t + 1) t (by omega)
  f_r := by simp [coneSES]
  s_g := by simp [coneSES]
  id := by
    rw [add_comm]
    exact mappingCone.id_X u t (t + 1) rfl

theorem coneSES_shortExact {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).ShortExact :=
  (coneSESSplitting u t).shortExact

theorem sgl_isKInjective {R : Type} [CommRing R] (I : Shv R) [Injective I] : (sgl I).IsKInjective := by
  haveI : ∀ n, Injective ((sgl I).X n) := by
    intro n
    by_cases h : n = 0
    · subst h
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n h).injective
  exact CochainComplex.isKInjective_of_injective _ 0

theorem sgl_cohomologyClass_subsingleton {R : Type} [CommRing R] (G I : Shv R) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (sgl I) i) := by
  have hc : ∀ a b : Cochain (sgl G) (sgl I) i, a = b := by
    intro a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I q hq).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G p hp).eq_of_src _ _
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := x.mk_surjective
  obtain ⟨b, rfl⟩ := y.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (hc _ _))

theorem ext_injective_subsingleton {R : Type} [CommRing R] (G I : Shv R) [Injective I] (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (res R I) i) := by
  obtain ⟨hK, -, -, hq, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R I
  haveI := hK
  haveI := hq
  haveI := sgl_isKInjective I
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (resAug I)).1 hq
  have h63 := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have hsurj : Function.Surjective (cpush (sgl G) (resAug I) i) := by
    intro y
    refine ⟨cpush (sgl G) e.inv i y, ?_⟩
    rw [← h63.2.2.1 (sgl G) e.inv (resAug I) i y, ← he,
      (h63.2.2.2.2 _ _ ⟨e.homotopyInvHomId⟩ (sgl G) i).2, (h63.1 (sgl G) _ i y).2]
  haveI := sgl_cohomologyClass_subsingleton G I i hi
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

theorem cone_terms_ext_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J),
    (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) →
    ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  intro R _ G C J u hJ hC t i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R (coneSES u t) (coneSES_shortExact u t)
  have hex := (hz (sgl G) i).1
  haveI := hJ t
  haveI hsJ : Subsingleton (CohomologyClass (sgl G) (res R (J.X t)) i) := ext_injective_subsingleton G (J.X t) i hi.ne'
  haveI hsC : Subsingleton (CohomologyClass (sgl G) (res R (C.X (t + 1))) i) := hC (t + 1) i hi
  constructor
  intro x y
  obtain ⟨w, hw⟩ := (hex x).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  obtain ⟨w', hw'⟩ := (hex y).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  rw [← hw, ← hw', @Subsingleton.elim _ hsJ w w']

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J), (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) → ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  first | (exact @GlobalTheory.cone_terms_ext_subsingleton) | (exact GlobalTheory.cone_terms_ext_subsingleton) | (intros; apply GlobalTheory.cone_terms_ext_subsingleton  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBounded
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.AcycResLevel

theorem res_lift {R : Type} [CommRing R] (F : Shv R) {W : Shv R} (φ : W ⟶ (res R F).X 0)
    (hφ : φ ≫ (res R F).d 0 1 = 0) : ∃ g : W ⟶ F, g ≫ resι R F = φ := by
  let I := injectiveResolution F
  let e0 : (res R F).X 0 ≅ I.cocomplex.X 0 := I.cochainComplexXIso 0 0 rfl
  let e1 : (res R F).X 1 ≅ I.cocomplex.X 1 := I.cochainComplexXIso 1 1 rfl
  have hd : (res R F).d 0 1 = e0.hom ≫ I.cocomplex.d 0 1 ≫ e1.inv := I.cochainComplex_d 0 1 0 1 rfl rfl
  have hψ : (φ ≫ e0.hom) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [← cancel_mono e1.inv, zero_comp]
    rw [hd] at hφ
    simpa only [Category.assoc] using hφ
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' I.isLimitKernelFork (φ ≫ e0.hom) hψ
  let l' : W ⟶ F := l
  refine ⟨l', ?_⟩
  let ι0 : F ⟶ I.cocomplex.X 0 := I.ι.f 0
  have h1 : resι R F = ι0 ≫ e0.inv := by
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ I.ι'.f 0 = _
    rw [InjectiveResolution.ι'_f_zero]
    simp [e0, ι0]
    rfl
  rw [h1]
  have h2 : l' ≫ ι0 = φ ≫ e0.hom := hl
  rw [← Category.assoc, h2, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem cocycle0_v_eq_zero {R : Type} [CommRing R] (G F : Shv R) (a : Cochain (sgl G) (res R F) 0)
    (h : ∃ m, ∃ _ : m + 1 = 0, ∃ b : Cochain (sgl G) (res R F) m, δ m 0 b = a) : a.v 0 0 (add_zero 0) = 0 := by
  obtain ⟨m, hm, b, rfl⟩ := h
  have hz : IsZero ((res R F).X m) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 m (by omega)
  have hsd : (sgl G).d 0 1 = 0 :=
    (HomologicalComplex.isZero_single_obj_X _ 0 G 1 (by simp)).eq_of_tgt _ _
  rw [δ_v m 0 (by omega) b 0 0 (add_zero 0) m 1 (by omega) rfl, hsd, zero_comp, smul_zero, add_zero]
  rw [hz.eq_of_tgt (b.v 0 m (by omega)) 0, zero_comp]

theorem ext_subsingleton_of_isZero : ∀ (R : Type) [CommRing R] (G Z : Shv R), IsZero Z → ∀ i : ℤ, Subsingleton (CohomologyClass (sgl G) (res R Z) i) := by
  intro R _ G Z hZ i
  haveI : (res R Z).IsKInjective := inferInstanceAs ((injectiveResolution Z).cochainComplex.IsKInjective)
  haveI : QuasiIso (resAug Z) := inferInstanceAs (QuasiIso (injectiveResolution Z).ι')
  have h0 : (sgl Z).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ ((CochainComplex.singleFunctor (Shv R) 0).map_isZero hZ)
  have h1 : (res R Z).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro j
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h2 := (h0 j)
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h2
    exact h2.of_iso (asIso (HomologicalComplex.homologyMap (resAug Z) j)).symm
  obtain ⟨H⟩ := IsKInjective.nonempty_homotopy_zero (𝟙 (res R Z)) h1
  have gen : ∀ a : Cochain (sgl G) (res R Z) i, δ i (i + 1) a = 0 →
      δ (i - 1) i (a.comp (Cochain.ofHomotopy H) (by omega)) = a := by
    intro a ha
    rw [δ_comp a (Cochain.ofHomotopy H) (by omega) (i + 1) 0 i (by omega) rfl (by omega), δ_ofHomotopy, ha,
      Cochain.zero_comp, smul_zero, add_zero, Cochain.ofHom_zero, sub_zero, Cochain.comp_id]
  have key : ∀ x : CohomologyClass (sgl G) (res R Z) i, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨i - 1, by omega, _, gen α.1 (Cocycle.δ_eq_zero α (i + 1))⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem cycles_shortExact : ∀ (R : Type) [CommRing R] (M : Cx R) (k j : ℤ), k + 1 = j → M.ExactAt j → ∃ h : M.iCycles k ≫ M.toCycles k j = 0, (ShortComplex.mk _ _ h).ShortExact := by
  intro R _ M k j hkj hj
  have hw : M.iCycles k ≫ M.toCycles k j = 0 := by
    rw [← cancel_mono (M.iCycles j)]; simp
  refine ⟨hw, ?_⟩
  have hp : (ComplexShape.up ℤ).prev j = k := by simp; omega
  have he : Epi (M.toCycles k j) := by
    subst hp
    exact hj.epi_toCycles
  have hlim : IsLimit (KernelFork.ofι (M.iCycles k) hw) :=
    KernelFork.IsLimit.ofι _ _ (fun φ hφ => M.liftCycles φ j (by simp; omega) (by
        have := congrArg (· ≫ M.iCycles j) hφ
        simpa using this))
      (fun φ hφ => by simp) (fun φ hφ m hm => by rw [← cancel_mono (M.iCycles k)]; simpa using hm)
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hlim) (by dsimp; infer_instance) he


set_option backward.isDefEq.respectTransparency false in
theorem lift_of_ext_one_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) 1) → ∀ f : G ⟶ S.X₃, ∃ g : G ⟶ S.X₂, g ≫ S.g = f := by
  intro R _ G S hS h1 f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have hI3 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₃
  have hI2 := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R S.X₂
  have hmono : Mono (resι R S.X₃) := hI3.2.2.2.2.2.1
  have hd3 : resι R S.X₃ ≫ (res R S.X₃).d 0 1 = 0 := hI3.2.2.2.2.2.2.1
  have hnat : resι R S.X₂ ≫ (resMap R S.g).f 0 = S.g ≫ resι R S.X₃ := (hI2.2.2.2.2.2.2.2 S.X₃ S.g).2
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have hz0 : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hsd : (sgl G).d 0 1 = 0 := (hz0 1 (by simp)).eq_of_tgt _ _
  let a3 : Cochain (sgl G) (res R S.X₃) 0 := Cochain.single (p := 0) (q := 0) (e.hom ≫ f ≫ resι R S.X₃) 0
  have ha3 : δ 0 1 a3 = 0 := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = 1 := by omega
      rw [δ_v 0 1 rfl a3 0 1 hpq 0 1 (by omega) rfl, Cochain.single_v, hsd, zero_comp, smul_zero, add_zero,
        Cochain.zero_v, Category.assoc, Category.assoc, hd3, comp_zero, comp_zero]
    · exact (hz0 p hp).eq_of_src _ _
  let c3 : CohomologyClass (sgl G) (res R S.X₃) 0 := CohomologyClass.mk (Cocycle.mk a3 1 rfl ha3)
  have hc3 : HK.ext R (sgl G) z 0 (0 + 1) rfl c3 = 0 := h1.elim _ _
  obtain ⟨w, hw⟩ := ((hz (sgl G) 0).2.1 c3).1 hc3
  obtain ⟨β, rfl⟩ := w.mk_surjective
  have hw' : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0)) = c3 := hw
  have hdiff : CohomologyClass.mk (zcomp β (Cocycle.ofHom (resMap R S.g)) (add_zero 0) - Cocycle.mk a3 1 rfl ha3) = 0 := by
    rw [CohomologyClass.mk_sub, hw', sub_self]
  rw [CohomologyClass.mk_eq_zero_iff] at hdiff
  have hv := GlobalTheory.AcycResLevel.cocycle0_v_eq_zero G S.X₃ _ hdiff
  have hv' : β.1.v 0 0 (add_zero 0) ≫ (resMap R S.g).f 0 = e.hom ≫ f ≫ resι R S.X₃ := by
    have h := hv
    simp [zcomp, a3, Cochain.comp_zero_cochain_v, sub_eq_zero] at h
    exact h
  have hb : β.1.v 0 0 (add_zero 0) ≫ (res R S.X₂).d 0 1 = 0 := by
    have h := congrArg (fun c => c.v 0 1 (by simp)) (Cocycle.δ_eq_zero β 1)
    rw [δ_v 0 1 rfl _ 0 1 (by simp) 0 1 (by simp) (by simp)] at h
    rw [hsd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    exact h
  obtain ⟨g', hg'⟩ := GlobalTheory.AcycResLevel.res_lift S.X₂ (e.inv ≫ β.1.v 0 0 (add_zero 0))
    (by rw [Category.assoc, hb, comp_zero])
  refine ⟨g', ?_⟩
  rw [← cancel_mono (resι R S.X₃), ← cancel_epi e.hom, Category.assoc, ← hnat, ← Category.assoc g', hg', ← hv']
  simp

theorem ext_pos_subsingleton_of_shortExact : ∀ (R : Type) [CommRing R] (G : Shv R) (S : ShortComplex (Shv R)), S.ShortExact → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₂) i)) → (∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₁) i)) → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R S.X₃) i) := by
  intro R _ G S hS h2 h1 i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R S hS
  have key : ∀ x : CohomologyClass (sgl G) (res R S.X₃) i, x = 0 := by
    intro x
    have e := (hz (sgl G) i).2.1
    have h0 : HK.ext R (sgl G) z i (i + 1) rfl x = 0 := (h1 (i + 1) (by omega)).elim _ _
    obtain ⟨w, hw⟩ := (e x).1 h0
    rw [← hw, (h2 i hi).elim w 0, map_zero]
  exact ⟨fun x y => (key x).trans (key y).symm⟩

theorem subsingleton_of_lifts : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (n : ℤ), (∀ f : G ⟶ M.X n, f ≫ M.d n (n + 1) = 0 → ∃ g : G ⟶ M.X (n - 1), g ≫ M.d (n - 1) n = f) → Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M n hlift
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl G).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ 0 G p hp
  have hd : (sgl G).d 0 1 = 0 := (hz 1 (by simp)).eq_of_tgt _ _
  let e : (sgl G).X 0 ≅ G := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G
  have gen : ∀ a : Cochain (sgl G) M n, δ n (n + 1) a = 0 → ∃ b : Cochain (sgl G) M (n - 1), δ (n - 1) n b = a := by
    intro a ha
    have h := congrArg (fun c => c.v 0 (n + 1) (by simp)) ha
    rw [δ_v n (n + 1) rfl _ 0 (n + 1) (by simp) n 1 (by simp) (by simp)] at h
    rw [hd, zero_comp, smul_zero, add_zero, Cochain.zero_v] at h
    have hf : (e.inv ≫ a.v 0 n (by simp)) ≫ M.d n (n + 1) = 0 := by
      rw [Category.assoc, h, comp_zero]
    obtain ⟨g, hg⟩ := hlift _ hf
    refine ⟨Cochain.single (p := 0) (q := n - 1) (e.hom ≫ g) (n - 1), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : n = q := by omega
      rw [δ_v (n - 1) n (by omega) _ 0 n hpq (n - 1) 1 (by omega) rfl, Cochain.single_v, hd, zero_comp,
        smul_zero, add_zero, Category.assoc, hg, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · exact (hz p hp).eq_of_src _ _
  have key : ∀ x : CohomologyClass (sgl G) M n, x = 0 := by
    intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨b, hb⟩ := gen α.1 (Cocycle.δ_eq_zero α (n + 1))
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, b, hb⟩
  exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.AcycResLevel

theorem GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  intro R _ G M a _ hM hExt n
  have hZ0 : ∀ k, k ≤ a → IsZero (M.cycles k) := by
    intro k hk
    obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (k - 1) k (by omega) (hM k)
    have : Epi (M.toCycles (k - 1) k) := hS.epi_g
    exact IsZero.of_epi (M.toCycles (k - 1) k) (M.isZero_of_isStrictlyGE a (k - 1))
  have hge : ∀ k, a ≤ k → ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k hk
    induction k, hk using Int.leInduction with
    | base => intro i _; exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 a le_rfl) i
    | succ k hak ih =>
      obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M k (k + 1) rfl (hM (k + 1))
      exact GlobalTheory.AcycResLevel.ext_pos_subsingleton_of_shortExact R G _ hS (hExt k) ih
  have hZ : ∀ k, ∀ i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.cycles k)) i) := by
    intro k
    rcases le_or_gt k a with hk | hk
    · intro i _
      exact GlobalTheory.AcycResLevel.ext_subsingleton_of_isZero R G _ (hZ0 k hk) i
    · exact hge k hk.le
  refine GlobalTheory.AcycResLevel.subsingleton_of_lifts R G M n fun f hf => ?_
  obtain ⟨h, hS⟩ := GlobalTheory.AcycResLevel.cycles_shortExact R M (n - 1) n (by omega) (hM n)
  obtain ⟨g, hg⟩ := GlobalTheory.AcycResLevel.lift_of_ext_one_subsingleton R G _ hS ((hZ (n - 1) 1 one_pos)) (M.liftCycles f (n + 1) (by simp) hf)
  refine ⟨g, ?_⟩
  have := congrArg (· ≫ M.iCycles n) hg
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBoundedStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (exact GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (intros; apply GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NullHtpyStair

variable {R : Type} [CommRing R]

theorem lift_of_subsingleton {A : Shv R} {M : Cx R} {m' m : ℤ} (hm : m' + 1 = m)
    (hA : Subsingleton (CohomologyClass (sgl A) M m)) (f : A ⟶ M.X m) (hf : f ≫ M.d m (m + 1) = 0) :
    ∃ g : A ⟶ M.X m', g ≫ M.d m' m = f := by
  have h0 : CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add m) (m + 1) rfl hf) = 0 := Subsingleton.elim _ _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m' hm] at h0
  obtain ⟨β, hβ⟩ := h0
  refine ⟨sglι A ≫ β.v 0 m' (by omega), ?_⟩
  have := congrArg (fun c => c.v 0 m (zero_add m)) hβ
  beta_reduce at this
  rw [δ_v m' m hm β 0 m (zero_add m) m' 1 (by omega) (by omega), Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v] at this
  have hd : (sgl A).d 0 1 = 0 := (HomologicalComplex.isZero_single_obj_X _ _ _ 1 (by omega)).eq_of_tgt _ _
  rw [hd, zero_comp, smul_zero, add_zero] at this
  rw [Category.assoc, this]
  exact Iso.inv_hom_id_assoc _ _

theorem comp_d_eq_zero {K M : Cx R} {n : ℤ} (c : Cochain K M n) (hc : δ n (n + 1) c = 0) (p : ℤ)
    (h1 : ∀ q hq, c.v (p + 1) q hq = 0) : c.v p (p + n) rfl ≫ M.d (p + n) (p + n + 1) = 0 := by
  have := congrArg (fun c' => c'.v p (p + n + 1) (by omega)) hc
  simp only [Cochain.zero_v] at this
  rw [δ_v n (n + 1) rfl c p (p + n + 1) (by omega) (p + n) (p + 1) (by omega) rfl, h1, comp_zero, smul_zero,
    add_zero] at this
  exact this

def Good {K M : Cx R} {n : ℤ} (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) : Prop :=
  ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n y).v p q hpq = (z : Cochain K M n).v p q hpq

theorem step {K M : Cx R} {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) (y : Cochain K M (n - 1)) (hy : Good z k y) :
    ∃ g : K.X (-(k : ℤ)) ⟶ M.X (-(k : ℤ) + (n - 1)), Good z (k + 1) (y + Cochain.single g (n - 1)) := by
  let c : Cochain K M n := (z : Cochain K M n) - δ (n - 1) n y
  have hc : δ n (n + 1) c = 0 := by
    simp only [c, δ_sub, δ_δ, Cocycle.δ_eq_zero, sub_zero]
  have h1 : ∀ q hq, c.v (-(k : ℤ) + 1) q hq = 0 := fun q hq => by
    simp only [c, Cochain.sub_v, hy (-(k : ℤ) + 1) q hq (by omega), sub_self]
  obtain ⟨g, hg⟩ := hK (-(k : ℤ)) (-(k : ℤ) + (n - 1)) (-(k : ℤ) + n) (by omega) (by omega)
    (c.v (-(k : ℤ)) (-(k : ℤ) + n) rfl) (comp_d_eq_zero c hc _ h1)
  refine ⟨g, fun p q hpq hp => ?_⟩
  rw [δ_add, Cochain.add_v]
  by_cases hpp : p = -(k : ℤ)
  · subst hpp
    obtain rfl : q = -(k : ℤ) + n := by omega
    rw [δ_v (n - 1) n (by omega) (Cochain.single g (n - 1)) _ _ hpq (-(k : ℤ) + (n - 1)) (-(k : ℤ) + 1) (by omega) rfl,
      Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero, smul_zero, add_zero, hg]
    simp only [c, Cochain.sub_v]
    abel
  · rw [hy p q hpq (by omega), δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega), Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
    simp

def seq {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k : ℕ) : {y : Cochain K M (n - 1) // Good z k y} :=
  Nat.rec (motive := fun k => {y : Cochain K M (n - 1) // Good z k y})
    (⟨0, fun p q hpq hp => (K.isZero_of_isStrictlyLE 0 p (by omega)).eq_of_src _ _⟩ : {y : Cochain K M (n - 1) // Good z 0 y})
    (fun k ih => ⟨ih.1 + Cochain.single (step hK z k _ ih.2).choose (n - 1), (step hK z k _ ih.2).choose_spec⟩) k

theorem seq_agree {K M : Cx R} [K.IsStrictlyLE 0] {n : ℤ}
    (hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f)
    (z : Cocycle K M n) (k j : ℕ) (hkj : k ≤ j) (p q : ℤ) (hpq : p + (n - 1) = q) (hp : -(k : ℤ) < p) :
    (seq hK z j).1.v p q hpq = (seq hK z k).1.v p q hpq := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [← ih]
    show ((seq hK z j).1 + Cochain.single _ (n - 1)).v p q hpq = _
    rw [Cochain.add_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), add_zero]

end GlobalTheory.NullHtpyStair


open GlobalTheory.NullHtpyStair in
theorem GlobalTheory.nullHtpy_stair : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0],
    (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ,
    Subsingleton (CohomologyClass K M n) := by
  intro R _ K M _ hA n
  have hK : ∀ (p m' m : ℤ), p ≤ 0 → m' + 1 = m → ∀ f : K.X p ⟶ M.X m, f ≫ M.d m (m + 1) = 0 →
      ∃ g : K.X p ⟶ M.X m', g ≫ M.d m' m = f :=
    fun p m' m hp hm f hf => GlobalTheory.NullHtpyStair.lift_of_subsingleton hm (hA p m hp) f hf
  suffices h : ∀ x : CohomologyClass K M n, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨Cochain.mk (fun p q hpq => (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).1.v p q hpq), ?_⟩
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl, Cochain.mk_v, Cochain.mk_v,
    ← GlobalTheory.NullHtpyStair.seq_agree hK z ((-(p + 1)).toNat + 1) ((-p).toNat + 1)
      (by omega) (p + 1) q _ (by omega),
    ← δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) (by omega) rfl]
  exact (GlobalTheory.NullHtpyStair.seq hK z ((-p).toNat + 1)).2 p q hpq (by omega)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0], (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ, Subsingleton (CohomologyClass K M n) := by
  first | exact @GlobalTheory.nullHtpy_stair | exact GlobalTheory.nullHtpy_stair | (intros; apply GlobalTheory.nullHtpy_stair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicResolutionComputesEtaleCohomology
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AcycRes

theorem coneBij {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J)
    (h : ∀ m, Subsingleton (CohomologyClass K (mappingCone f) m)) (n : ℤ) : Function.Bijective (cpush K f n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f m
  obtain ⟨h1, -, -⟩ := GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact R K f (m + 1)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (h3 x).1 hx
    rw [(h m).elim y 0, map_zero]
  · intro y
    exact (h1 y).1 ((h (m + 1)).elim _ _)

theorem subOfIso {R : Type} [CommRing R] {A B : Shv R} (e : A ≅ B) (M : Cx R) (n : ℤ)
    (h : Subsingleton (CohomologyClass (sgl B) M n)) : Subsingleton (CohomologyClass (sgl A) M n) := by
  obtain ⟨hid, hcomp, -, -, -⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.hom) M n
      (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n z) = z := by
    intro z
    rw [← hcomp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull ((CochainComplex.singleFunctor (Shv R) 0).map e.inv) M n x)]

theorem discFree {R : Type} [CommRing R] (P : PSh) (X : Shv R) (i : ℤ) (h : Subsingleton (H R (disc.obj P) X i)) :
    Subsingleton (CohomologyClass (sgl ((free R).obj P)) (res R X) i) := by
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨hid, hcomp, -, -, hhtpy⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have key : ∀ z, cpull (e P).hom (res R X) i (cpull (e P).inv (res R X) i z) = z := by
    intro z
    rw [← hcomp, (hhtpy _ _ ⟨(e P).homotopyHomInvId⟩ (res R X) i).1]
    exact (hid _ _ _ z).1
  refine ⟨fun x y => ?_⟩
  rw [← key x, ← key y, h.elim (cpull (e P).inv (res R X) i x)]

end GlobalTheory.EtC.AcycRes


open GlobalTheory.EtC.AcycRes in
theorem GlobalTheory.EtC.acycRes_computes : ∀ (R : Type) [CommRing R] (F : Shv R) (C : Cx R) [C.IsStrictlyGE 0] (ε : sgl F ⟶ C) [QuasiIso ε] (u : C ⟶ res R F), ε ≫ u = resAug F → (∀ (t : ℤ) (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) (C.X t) n)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains R).obj E) u n) := by
  intro R _ F C _ ε _ u hu hC E n
  obtain ⟨-, hinj, hge, hqa, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  have : QuasiIso (ε ≫ u) := by rw [hu]; exact hqa
  have : QuasiIso u := quasiIso_of_comp_left ε u
  have : ((chains R).obj E).IsStrictlyLE 0 := (GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R).1 E
  have : (mappingCone u).IsStrictlyGE (-1) := isStrictlyGE_mappingCone u 0 0 (-1)
  apply coneBij
  intro m
  apply GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero R _ _ _ m
  intro p k hp
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
  apply subOfIso (chainsXIso R E q)
  apply GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow R _ _ (-1) (GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso R u)
  intro t i hi
  apply GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton R _ u hinj _ t i hi
  intro t' i' hi'
  exact discFree _ _ _ (hC t' _ i' hi')
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicResolutionComputesEtaleCohomologyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_resolution_computes_etale_cohomology : ∀ (R : Type) [CommRing R] (F : Shv R) (C : Cx R) [C.IsStrictlyGE 0] (ε : sgl F ⟶ C) [QuasiIso ε] (u : C ⟶ res R F), ε ≫ u = resAug F → (∀ (t : ℤ) (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) (C.X t) n)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains R).obj E) u n) := by
  first
  | exact @GlobalTheory.EtC.acycRes_computes
  | exact GlobalTheory.EtC.acycRes_computes
  | (intros; apply GlobalTheory.EtC.acycRes_computes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKill
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKill
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem rAug_comp_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) :
    rAug (Int.castRingHom S) (resAug F) ≫ δ.toZ = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  apply Sheaf.hom_ext
  ext U b
  obtain ⟨-, -, -, -, h5, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((restr (Int.castRingHom S)).obj F)
  let a : Sec ((restr (Int.castRingHom S)).obj F) U.unop := Sec.map e.hom b
  have hb : b = Sec.map (sglι ((restr (Int.castRingHom S)).obj F)) a := by
    change b = Sec.map (e.hom ≫ e.inv) b
    rw [Iso.hom_inv_id]; rfl
  have h1 := rAug_f_zero (Int.castRingHom S) (resAug F) U.unop a
  change Sec.map (δ.toZ.f 0) (Sec.map ((rAug (Int.castRingHom S) (resAug F)).f 0) b) = 0
  rw [hb]
  have key : δ.app U.unop 0 (Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a))) = 0 := by
    have h6 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) (show Sec F U.unop from a)) = Sec.map (resι S F) a := by
      rw [← h5]; rfl
    rw [h6]; exact hδ _ _
  exact (congrArg (δ.app U.unop 0) h1).trans key

theorem cpush_zero_hom {R : Type} [CommRing R] (K : Cx R) {I J : Cx R} (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (0 : I ⟶ J) n x = 0 := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  rw [cpost_mk]
  have : zcomp z (Cocycle.ofHom (0 : I ⟶ J)) (add_zero n) = 0 := by
    ext1; simp [zcomp]
  rw [this, CohomologyClass.mk_zero]

theorem cpush_toZ_eq_zero_of_kill (S : Type) [CommRing S] (F : Shv S) (R : Type) [CommRing R] (G : Shv R) (δ : SemiMap (res S F) (res R G))
    (hδ : ∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) (E : Spc) (n : ℤ)
    (y : CohomologyClass ((chains ℤ).obj E) ((rcx (Int.castRingHom S)).obj (res S F)) n) :
    cpush ((chains ℤ).obj E) δ.toZ n y = 0 := by
  obtain ⟨-, -, -, hqF, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  obtain ⟨-, hinjG, hgeG, hqG, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  let G' := (restr (Int.castRingHom R)).obj G
  obtain ⟨hKI', -, hGE', -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G'
  haveI := hqF; haveI := hqG; haveI := hgeG; haveI := hKI'; haveI := hGE'
  haveI : QuasiIso (rAug (Int.castRingHom S) (resAug F)) := rAug_quasiIso _ _
  haveI : QuasiIso (rAug (Int.castRingHom R) (resAug G)) := rAug_quasiIso _ _
  obtain ⟨v, hv⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (res ℤ G')
    (rAug (Int.castRingHom R) (resAug G))).1 (resAug G')
  have hacyc : ∀ (t : ℤ) (P : PSh) (m : ℤ), 0 < m →
      Subsingleton (H ℤ (disc.obj P) (((rcx (Int.castRingHom R)).obj (res R G)).X t) m) :=
    fun t P m hm => GlobalTheory.T.restrictScalars_injective_sheaf_acyclic ℤ R (Int.castRingHom R) ((res R G).X t) P m hm
  have hbij := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology ℤ G' ((rcx (Int.castRingHom R)).obj (res R G)) (rAug (Int.castRingHom R) (resAug G)) v hv
    hacyc E n
  have hzero := rAug_comp_toZ_eq_zero_of_kill S F R G δ hδ
  obtain ⟨hom⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective ℤ ((restr (Int.castRingHom S)).obj F) ((rcx (Int.castRingHom S)).obj (res S F)) (res ℤ G')
    (rAug (Int.castRingHom S) (resAug F))).2 (δ.toZ ≫ v) 0 (by rw [← Category.assoc, hzero]; simp)
  have h1 := ((GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.2.2 _ _ ⟨hom⟩ ((chains ℤ).obj E) n).2
  have h2 : cpush ((chains ℤ).obj E) v n (cpush ((chains ℤ).obj E) δ.toZ n y) = cpush ((chains ℤ).obj E) v n 0 := by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial ℤ).2.2.1, h1, cpush_zero_hom, map_zero]
  exact hbij.1 h2

theorem semiMap_op_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R)
    (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) →
    ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  intro S R _ _ F G δ hδ E n x
  let ιA := idSemi (Int.castRingHom S) (res S F)
  let ιB := idSemi (Int.castRingHom R) (res R G)
  let ρ' : SemiMap (res S F) ((rcx (Int.castRingHom R)).obj (res R G)) :=
    { app := fun U s => δ.app U s
      nat := fun g s a => δ.nat g s a
      comm := fun U s t a => δ.comm U s t a }
  have hA := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S ℤ ιA ρ' δ.toZ (fun _ _ _ => rfl)).1 E n x
  have hB := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective R ℤ ιB ιB (𝟙 _) (fun _ _ _ => rfl)).2
    (fun _ _ => ⟨fun _ _ h => h, fun b => ⟨b, rfl⟩⟩) E n
  have hcomp : ρ'.op.app E n x = ιB.op.app E n (δ.op.app E n x) := by
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).1 E n α
    obtain ⟨γ, hγ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).1 E n β
    rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R δ).2 E n α β hβ, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap R ℤ ιB).2 E n β γ hγ,
      (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S ℤ ρ').2 E n α γ ?_]
    intro p s h U y
    rw [hγ p s h U y, hβ p s h U y]
    rfl
  apply hB.1
  rw [map_zero, ← hcomp, hA, cpush_toZ_eq_zero_of_kill S F R G δ hδ E n]

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearResolutionMapCohomologyEqZeroOfKillStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill : ∀ (S R : Type) [CommRing S] [CommRing R] (F : Shv S) (G : Shv R) (δ : SemiMap (res S F) (res R G)), (∀ (U : Scheme.{0}) (a : Sec F U), δ.app U 0 (Sec.map (resι S F) a) = 0) → ∀ (E : Spc) (n : ℤ) (x : H S E F n), δ.op.app E n x = 0 := by
  first
  | exact @GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | exact GlobalTheory.EtC.semiMap_op_eq_zero_of_kill
  | (intros; apply GlobalTheory.EtC.semiMap_op_eq_zero_of_kill <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparison
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem restrRes_strictlyGE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) [K.IsStrictlyGE 0] :
    ((rcx φ).obj K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (restr φ).map_isZero (K.isZero_of_isStrictlyGE 0 i hi)

def semiOfRestr {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R} (u : (rcx φ).obj K ⟶ J) :
    SemiMap K J where
  app U s := (((u.f s).hom.app (op U)).hom.toAddMonoidHom).comp ((idSemi φ K).app U s)
  nat {V U} g s a := by
    have h := congrArg (fun m => ModuleCat.Hom.hom m (show Sec (((rcx φ).obj K).X s) U from a))
      ((u.f s).hom.naturality g.op)
    exact h.symm
  comm U s t a := by
    have h := congrArg (fun m => (m.hom.app (op U)).hom (show Sec (((rcx φ).obj K).X s) U from a)) (u.comm s t)
    exact h

theorem semiOfRestr_app {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (K : Cx S) {J : Cx R}
    (u : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ) (a : Sec (K.X s) U) :
    (semiOfRestr φ K u).app U s a = Sec.map (u.f s) ((idSemi φ K).app U s a) := rfl

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem restrRes_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
      (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧
      ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  intro R S _ _ φ F
  obtain ⟨_, hinjS, hgeS, hqS, hιS, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  obtain ⟨hKR, -, hgeR, -, hιR, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R ((restr φ).obj F)
  haveI := hgeS; haveI := hqS; haveI := hKR; haveI := hgeR
  haveI : ((rcx φ).obj (res S F)).IsStrictlyGE 0 := restrRes_strictlyGE φ (res S F)
  haveI : QuasiIso (rAug φ (resAug F)) := rAug_quasiIso φ (resAug F)
  obtain ⟨u, hu⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug _)
  refine ⟨semiOfRestr φ (res S F) u, ?_, ?_⟩
  · intro U a
    have h0 := rAug_f_zero φ (resAug F) U a
    have h1 : Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) = Sec.map (resι S F) a := by
      rw [← hιS]; rfl
    have h2 : Sec.map ((rAug φ (resAug F) ≫ u).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
        Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
      rw [hu, ← hιR]; rfl
    rw [← h2, semiOfRestr_app]
    change _ = Sec.map (u.f 0) (Sec.map ((rAug φ (resAug F)).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)))
    rw [h0, h1]
    rfl
  · intro E n
    have hc := GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (semiOfRestr φ (res S F) u) u
      (fun U s a => semiOfRestr_app φ (res S F) u U s a)
    have hid := (GlobalTheory.T.sheafComplexSemilinearMap_comp_bijective S R (idSemi φ (res S F)) (idSemi φ (res S F)) (𝟙 _) (fun U s a => rfl)).2
      (fun U s => Function.bijective_id) E n
    have hpush := GlobalTheory.T.acyclic_resolution_computes_etale_cohomology R ((restr φ).obj F) ((rcx φ).obj (res S F)) (rAug φ (resAug F)) u hu
      (fun t P m hm => by
        haveI := hinjS t
        exact GlobalTheory.T.restrictScalars_injective_sheaf_acyclic R S φ ((res S F).X t) P m hm) E n
    have heq : (semiOfRestr φ (res S F) u).op.app E n =
        fun x => cpush _ u n ((idSemi φ (res S F)).op.app E n x) := funext (hc.1 E n)
    rw [heq]
    exact hpush.comp hid

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionComparisonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalars_resolution_comparison : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) ∧ ∀ (E : Spc) (n : ℤ), Function.Bijective (ρ.op.app E n) := by
  first
  | exact @GlobalTheory.EtC.restrRes_comparison
  | exact GlobalTheory.EtC.restrRes_comparison
  | (intros; apply GlobalTheory.EtC.restrRes_comparison <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvariance
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

theorem SemiMap.sub_op {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J)
    (E : Spc) (n : ℤ) (x : CohomologyClass ((chains S).obj E) I n) :
    (ρ.sub ρ').op.app E n x = ρ.op.app E n x - ρ'.op.app E n x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).1 E n α
  obtain ⟨β', hβ'⟩ := (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').1 E n α
  have hsub : (ρ.sub ρ').IsImage α.1 (β - β').1 := by
    intro p s h U x
    rw [show (β - β').1 = β.1 - β'.1 from rfl, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 β.1 β'.1 p s h U x).2.1, hβ p s h U x,
      hβ' p s h U x]
    rfl
  rw [(GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R _).2 E n α _ hsub, (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ).2 E n α β hβ,
    (GlobalTheory.T.exists_image_cocycle_semilinearSheafComplexMap S R ρ').2 E n α β' hβ', CohomologyClass.mk_sub]

theorem a8 : A8 := by
  intro R S _ _ φ E F n
  obtain ⟨ρ₀, h₀, hb⟩ := GlobalTheory.T.restrictScalars_resolution_comparison R S φ F
  have hz := GlobalTheory.T.semilinearResolutionMap_cohomology_eq_zero_of_kill S R F ((restr φ).obj F) ((restrMap φ F).sub ρ₀) (fun U a => by
    change (restrMap φ F).app U 0 _ - ρ₀.app U 0 _ = 0
    rw [GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec R S φ F U a, h₀ U a, sub_self])
  have he : restrH φ E F n = ρ₀.op.app E n := by
    ext x
    have := hz E n x
    rw [SemiMap.sub_op] at this
    exact sub_eq_zero.mp this
  rw [he]
  exact hb E n

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficientRing_invariance : GlobalTheory.EtC.A8 := by
  first
  | exact @GlobalTheory.EtC.a8
  | exact GlobalTheory.EtC.a8
  | (intros; apply GlobalTheory.EtC.a8 <;> assumption)
end
