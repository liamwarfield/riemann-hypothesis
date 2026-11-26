module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocycles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.JoinedTwoProof

universe a b

theorem main : JoinedTwo.{a, b} := by
  intro C _ C' _ K K' m m' θ j c
  obtain ⟨⟨⟨z, w, η⟩, hc⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨h1, h2, h3, -⟩ := hc
  dsimp only at h1 h2 h3
  refine QuotientAddGroup.eq.2 ⟨(fun T T' φ ↦ m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T')),
    fun T ↦ m'.a1 T (w _ _ (θ.app T))), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · change K'.M0.map ψ (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) -
        m'.a0 T'' (z _ _ _ (θ.app T) (m'.G.map (φ ≫ ψ)) - z _ _ _ (m.G.map (φ ≫ ψ)) (θ.app T'')) +
        m'.a0 T'' (z _ _ _ (θ.app T') (m'.G.map ψ) - z _ _ _ (m.G.map ψ) (θ.app T'')) =
      -m.a0 T'' (z _ _ _ (m.G.map φ) (m.G.map ψ)) + m'.a0 T'' (z _ _ _ (m'.G.map φ) (m'.G.map ψ))
    have e1 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.a0 T'') (h1 _ _ _ _ (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.a0 T'') (h1 _ _ _ _ (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    rw [← m.G.map_comp] at e1
    rw [← m'.G.map_comp] at e3
    simp only [map_add (f := _), j.e0, m'.compDegreeZero_natural] at e1 e2 e3
    simp only [map_sub, m'.compDegreeZero_natural]
    linear_combination (norm := abel1) e1 - e2 + e3
  · change m'.a1 T' (w _ _ (θ.app T')) - K'.M1.map φ (m'.a1 T (w _ _ (θ.app T))) -
        K'.d0 T' (m'.a0 T' (z _ _ _ (θ.app T) (m'.G.map φ) - z _ _ _ (m.G.map φ) (θ.app T'))) =
      -m.a1 T' (w _ _ (m.G.map φ)) + m'.a1 T' (w _ _ (m'.G.map φ))
    have e := congrArg (m'.a1 T') ((h2 _ _ _ (m.G.map φ) (θ.app T')).symm.trans
      ((congrArg (w _ _) (θ.naturality φ)).trans (h2 _ _ _ (θ.app T) (m'.G.map φ))))
    simp only [map_add (f := _), j.e1, m'.compDegreeOne_natural, m'.comp_commutes_diffZero] at e
    simp only [map_sub]
    linear_combination (norm := abel1) e
  · change K'.d1 T (m'.a1 T (w _ _ (θ.app T))) = -m.a2 T (η _) + m'.a2 T (η _)
    rw [h3 _ _ (θ.app T), map_add (f := _), j.e2, m'.comp_commutes_diffOne]; abel

theorem joinedTwo_inst : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := ⟨main, main, main⟩

end GlobalTheory.CxCoh.JoinedTwoProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstancesStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyTwo_instances : JoinedTwo.{1,1} ∧ JoinedTwo.{1,0} ∧ JoinedTwo.{0,0} := by
  first | exact @GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | exact GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst | (intros; apply GlobalTheory.CxCoh.JoinedTwoProof.joinedTwo_inst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ExtQis

theorem quasiIso_of_mappingCone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

theorem flatS_cone (Q : ℕ) [NeZero Q] (F : Shv (ZMod Q)) (hF : FlatS F) (n : ℤ) :
    FlatS ((mappingCone (resAug F)).X n) := by
  obtain ⟨hiso, hzero⟩ := GlobalTheory.T.isLocallyFlatEtaleSheaf_iso_and_zero (ZMod Q)
  refine hiso (HomologicalComplex.homotopyCofiber.XIsoBiprod (resAug F) n (n + 1) rfl).symm
    (GlobalTheory.T.isLocallyFlatEtaleSheaf_biprod _ _ _ ?_ ?_)
  · by_cases h : n + 1 = 0
    · exact hiso (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 F (n + 1) h).symm hF
    · exact hzero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)
  · haveI : Injective ((res (ZMod Q) F).X n) :=
      (inferInstance : Injective ((injectiveResolution F).cochainComplex.X n))
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf Q _).2

theorem quasiIso_extAug : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ),
    QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  intro Q q _ hq i
  have hq' : QuasiIso (resAug (tw Q i)) := (inferInstance : QuasiIso (injectiveResolution (tw Q i)).ι')
  have hK : (mappingCone (resAug (tw Q i))).Acyclic := GlobalTheory.mappingCone_acyclic_of_quasiIso _
  haveI : (res (ZMod Q) (tw Q i)).IsStrictlyGE 0 :=
    (inferInstance : (injectiveResolution (tw Q i)).cochainComplex.IsStrictlyGE 0)
  haveI : (mappingCone (resAug (tw Q i))).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
  have hE := GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow Q q hq (mappingCone (resAug (tw Q i))) (-1)
    (flatS_cone Q (tw Q i) (GlobalTheory.T.tateTwistSheaf_isLocallyFlat Q i)) hK
  have hC : (mappingCone (((extSh (ZMod.castHom hq (ZMod q))).mapHomologicalComplex _).map
      (resAug (tw Q i)))).Acyclic := fun n =>
    (hE n).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso (resAug (tw Q i))
      (extSh (ZMod.castHom hq (ZMod q))))
  have h1 := quasiIso_of_mappingCone_acyclic _ hC
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (extSh (ZMod.castHom hq (ZMod q)))
      (ComplexShape.up ℤ) 0).inv.app (tw Q i)) := quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end GlobalTheory.EtC.ExtQis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentationStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ), QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  first | exact @GlobalTheory.EtC.ExtQis.quasiIso_extAug | exact GlobalTheory.EtC.ExtQis.quasiIso_extAug | (intros; apply GlobalTheory.EtC.ExtQis.quasiIso_extAug <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

namespace CxMap

universe a b

variable {C : Type a} [Category.{0} C] {C' : Type b} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

theorem h0_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H0) :
    m.h0 c = m'.h0 c := by
  obtain ⟨g, hg⟩ := c
  have hg' : K.D0 g = 0 := hg
  have hc : ∀ T T' (φ : T ⟶ T'), g T' = K.M0.map φ (g T) := fun T T' φ => by
    have h := congrArg (fun c => c.1 T T' φ) hg'
    change g T' - K.M0.map φ (g T) = 0 at h
    exact sub_eq_zero.mp h
  apply Subtype.ext
  funext T
  change m.a0 T (g _) = m'.a0 T (g _)
  rw [hc _ _ (θ.app T), hj.e0]

theorem p1_eq_add_D0_of_joined_of_cocycle (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.T1)
    (hc : K.D1 c = 0) :
    m'.p1 c = m.p1 c + K'.D0 (fun T => m'.a0 T (c.1 _ _ (θ.app T))) := by
  have e1 : ∀ A A' A'' (α : A ⟶ A') (β : A' ⟶ A''),
      c.1 A A'' (α ≫ β) = K.M0.map β (c.1 A A' α) + c.1 A' A'' β := by
    intro A A' A'' α β
    have h := congrArg (fun x => x.1 A A' A'' α β) hc
    change K.M0.map β (c.1 A A' α) - c.1 A A'' (α ≫ β) + c.1 A' A'' β = 0 at h
    linear_combination (norm := abel1) -h
  have e2 : ∀ A A' (α : A ⟶ A'), c.2 A' = K.M1.map α (c.2 A) + K.d0 A' (c.1 A A' α) := by
    intro A A' α
    have h := congrArg (fun x => x.2.1 A A' α) hc
    change c.2 A' - K.M1.map α (c.2 A) - K.d0 A' (c.1 A A' α) = 0 at h
    linear_combination (norm := abel1) h
  refine Prod.ext ?_ ?_
  · funext T T' φ
    change m'.a0 T' (c.1 _ _ (m'.G.map φ)) = m.a0 T' (c.1 _ _ (m.G.map φ)) +
      (m'.a0 T' (c.1 _ _ (θ.app T')) - K'.M0.map φ (m'.a0 T (c.1 _ _ (θ.app T))))
    have k1 := e1 _ _ _ (m.G.map φ) (θ.app T')
    have k2 := e1 _ _ _ (θ.app T) (m'.G.map φ)
    rw [θ.naturality φ] at k1
    have k := congrArg (m'.a0 T') (k1.symm.trans k2)
    rw [map_add (f := _), map_add (f := _), hj.e0, m'.compDegreeZero_natural] at k
    linear_combination (norm := abel1) -k
  · funext T
    change m'.a1 T (c.2 _) = m.a1 T (c.2 _) + K'.d0 T (m'.a0 T (c.1 _ _ (θ.app T)))
    rw [e2 _ _ (θ.app T), map_add (f := _), hj.e1, m'.comp_commutes_diffZero]

theorem h1_eq_of_joined (m m' : CxMap K K') (θ : m.G ⟶ m'.G) (hj : m.Joined m' θ) (c : K.H1) :
    m.h1 c = m'.h1 c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  change (QuotientAddGroup.mk (m.z1 ⟨x, hx⟩) : K'.H1) = QuotientAddGroup.mk (m'.z1 ⟨x, hx⟩)
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine ⟨fun T => m'.a0 T (x.1 _ _ (θ.app T)), ?_⟩
  have h := p1_eq_add_D0_of_joined_of_cocycle m m' θ hj x (AddMonoidHom.mem_ker.mp hx)
  change _ = -(m.p1 x) + m'.p1 x
  rw [h]; abel

end CxMap

theorem joinedOne_cohomology.{a, b} : JoinedOne.{a, b} := fun m m' θ hj =>
  ⟨CxMap.h0_eq_of_joined m m' θ hj, CxMap.h1_eq_of_joined m m' θ hj⟩

theorem joinedOne_inst : JoinedOne.{1, 1} ∧ JoinedOne.{1, 0} ∧ JoinedOne.{0, 0} :=
  ⟨joinedOne_cohomology, joinedOne_cohomology, joinedOne_cohomology⟩

end GlobalTheory.CxCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstancesStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances : JoinedOne.{1,1} ∧ JoinedOne.{1,0} ∧ JoinedOne.{0,0} := by
  first | exact @GlobalTheory.CxCoh.joinedOne_inst | exact GlobalTheory.CxCoh.joinedOne_inst | (intros; apply GlobalTheory.CxCoh.joinedOne_inst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
set_option autoImplicit false

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.QAtFormal

universe u

variable {C : Type u} [Category.{0} C] (K : Cx C)

theorem qAt_ident (T : C) : K.QAt (𝟙 T) := by
  refine ⟨fun x _ h => ?_, fun y hy => ⟨y, hy, ?_⟩, fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩,
    fun x y _ h => ⟨y, ?_⟩, fun y hy => ⟨y, 0, hy, ?_⟩⟩
  · rwa [K.M0.map_id] at h
  · exact K.M0.map_id T y
  · rw [K.M1.map_id] at h; exact h.symm
  · rw [K.M1.map_id, map_zero, add_zero]
  · rw [K.M2.map_id] at h; exact h.symm
  · rw [K.M2.map_id, map_zero, add_zero]

theorem qAt_comp {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (ha : K.QAt a) (hb : K.QAt b) :
    K.QAt (a ≫ b) := by
  refine ⟨fun x hx h => ?_, fun y hy => ?_, fun x y hx h => ?_, fun y hy => ?_,
    fun x y hx h => ?_, fun y hy => ?_⟩
  · rw [K.M0.map_comp] at h
    exact ha.inj0 x hx (hb.inj0 _ (by rw [K.diffZero_natural, hx, map_zero]) h)
  · obtain ⟨x', hx', rfl⟩ := hb.surj0 y hy
    obtain ⟨x, hx, rfl⟩ := ha.surj0 x' hx'
    exact ⟨x, hx, K.M0.map_comp a b x⟩
  · rw [K.M1.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj1 _ y (by rw [K.diffOne_natural, hx, map_zero]) h
    exact ha.inj1 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj1 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj1 x' hx'
    refine ⟨x, K.M0.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M1.map_comp, K.diffZero_natural]
    abel
  · rw [K.M2.map_comp] at h
    obtain ⟨w', hw'⟩ := hb.inj2 _ y (by rw [K.diffTwo_natural, hx, map_zero]) h
    exact ha.inj2 x w' hx hw'.symm
  · obtain ⟨x', w', hx', rfl⟩ := hb.surj2 y hy
    obtain ⟨x, w, hx, rfl⟩ := ha.surj2 x' hx'
    refine ⟨x, K.M1.map b w + w', hx, ?_⟩
    simp only [map_add (f := _), K.M2.map_comp, K.diffOne_natural]
    abel

theorem qAt_of_comp_retract {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T')
    (hbc : b ≫ c = 𝟙 T') (h : K.QAt (a ≫ b)) : K.QAt a := by
  have e0 : ∀ y, K.M0.map c (K.M0.map b y) = y := fun y => by
    rw [← K.M0.map_comp, hbc, K.M0.map_id]
  have e1 : ∀ y, K.M1.map c (K.M1.map b y) = y := fun y => by
    rw [← K.M1.map_comp, hbc, K.M1.map_id]
  have e2 : ∀ y, K.M2.map c (K.M2.map b y) = y := fun y => by
    rw [← K.M2.map_comp, hbc, K.M2.map_id]
  refine ⟨fun x hx hax => ?_, fun y hy => ?_, fun x y hx hxy => ?_, fun y hy => ?_,
    fun x y hx hxy => ?_, fun y hy => ?_⟩
  · exact h.inj0 x hx (by rw [K.M0.map_comp, hax, map_zero])
  · obtain ⟨x, hx, hxy⟩ := h.surj0 (K.M0.map b y) (by rw [K.diffZero_natural, hy, map_zero])
    refine ⟨x, hx, ?_⟩
    rw [K.M0.map_comp] at hxy
    simpa only [e0] using congrArg (K.M0.map c) hxy
  · exact h.inj1 x (K.M0.map b y) hx (by rw [K.M1.map_comp, hxy, K.diffZero_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj1 (K.M1.map b y) (by rw [K.diffOne_natural, hy, map_zero])
    refine ⟨x, K.M0.map c w, hx, ?_⟩
    have := congrArg (K.M1.map c) hw
    rw [map_add (f := _), K.M1.map_comp, e1, e1, ← K.diffZero_natural] at this
    exact this
  · exact h.inj2 x (K.M1.map b y) hx (by rw [K.M2.map_comp, hxy, K.diffOne_natural])
  · obtain ⟨x, w, hx, hw⟩ := h.surj2 (K.M2.map b y) (by rw [K.diffTwo_natural, hy, map_zero])
    refine ⟨x, K.M1.map c w, hx, ?_⟩
    have := congrArg (K.M2.map c) hw
    rw [map_add (f := _), K.M2.map_comp, e2, e2, ← K.diffOne_natural] at this
    exact this

theorem qAt_of_isIso {T T' : C} (a : T ⟶ T') [IsIso a] : K.QAt a :=
  qAt_of_comp_retract K a (inv a) a (IsIso.inv_hom_id a) (by rw [IsIso.hom_inv_id]; exact qAt_ident K T)

theorem qAt_formal : ∀ (C : Type 1) [Category.{0} C] (K : Cx C),
    (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧
    (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧
    ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a :=
  fun _ _ K => ⟨fun _ _ a _ => qAt_of_isIso K a, fun _ _ _ a b => qAt_comp K a b,
    fun _ _ _ a b c => qAt_of_comp_retract K a b c⟩

end GlobalTheory.CxCoh.QAtFormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalPropertiesStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourTermComplex_quasiIsoAt_formal_properties : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧ (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a := by
  first | exact @GlobalTheory.CxCoh.QAtFormal.qAt_formal | exact GlobalTheory.CxCoh.QAtFormal.qAt_formal | (intros; apply GlobalTheory.CxCoh.QAtFormal.qAt_formal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

lemma isIso_mapCechNerve_app_of_mono {A B C : PSh} (π : A ⟶ B) (ι : B ⟶ C) [Mono ι] (φ : A ⟶ C)
    (h : π ≫ ι = φ) (n : SimplexCategoryᵒᵖ) :
    IsIso ((Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp [h]) : Arrow.mk π ⟶ Arrow.mk φ)).app n) := by
  subst h
  have e : (Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp) : Arrow.mk π ⟶ Arrow.mk (π ≫ ι))).app n =
      WidePullback.lift (WidePullback.base (fun _ : Fin (n.unop.len + 1) => π) ≫ ι)
        (fun i => WidePullback.π (fun _ : Fin (n.unop.len + 1) => π) i)
        (fun j => by
          show _ ≫ (π ≫ ι) = _
          rw [← Category.assoc, WidePullback.π_arrow]) := by
    apply WidePullback.hom_ext
    · intro j
      erw [WidePullback.lift_π]
    · erw [WidePullback.lift_base]
  rw [e]
  refine ⟨WidePullback.lift (WidePullback.π _ 0 ≫ π) (fun i => WidePullback.π _ i) ?_, ?_, ?_⟩
  · intro i
    rw [← cancel_mono ι]
    simp only [Category.assoc]
    exact (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) i).trans
      (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0).symm
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_π]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π) 0
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_base]
      rw [Category.assoc]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_locSurj (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q)
    (hφ : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) :
    QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
      (Arrow.mk φ).augmentedCechNerve.hom)) := by
  let aφ : (Arrow.mk φ).cechNerve ⟶ disc.obj Q := (Arrow.mk φ).augmentedCechNerve.hom
  change QuasiIso ((chains R).map aφ)
  have hπι : Subfunctor.toRange φ ≫ (Subfunctor.range φ).ι = φ := Subfunctor.toRange_ι φ
  set π := Subfunctor.toRange φ with hπ
  set ι := (Subfunctor.range φ).ι with hι
  let F : Arrow.mk π ⟶ Arrow.mk φ := Arrow.homMk (𝟙 P) ι (by simp [hπι])
  let aπ : (Arrow.mk π).cechNerve ⟶ disc.obj _ := (Arrow.mk π).augmentedCechNerve.hom
  have sq : Arrow.mapCechNerve F ≫ aφ = aπ ≫ disc.map ι := by
    ext n : 1
    erw [NatTrans.comp_app, NatTrans.comp_app]
    erw [Arrow.augmentedCechNerve_hom_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
    rfl
  have hsurj : ∀ U, Function.Surjective (π.app U) := fun U =>
    (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 (inferInstance : Epi π) U)
  have h1 : QuasiIso ((chains R).map aπ) := GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R π hsurj
  have hιfree : IsIso ((free R).map ι) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R ι).2.2 ?_ ?_
    · intro U y
      exact GlobalTheory.EtC.loc_calculus.2.1 U _ _ (hφ U y) fun V g ⟨x, hx⟩ => ⟨π.app (op V) x, hx⟩
    · intro U x x' hxx
      have : x = x' := Subtype.ext hxx
      subst this
      exact GlobalTheory.EtC.loc_calculus.1 U _ fun _ _ => rfl
  have h2 : IsIso ((chains R).map (disc.map ι)) :=
    isIso_chains_map_of_isIso_free R _ fun n => hιfree
  have h3 : IsIso ((chains R).map (Arrow.mapCechNerve F)) :=
    isIso_chains_map_of_isIso_free R _ fun n => by
      have := isIso_mapCechNerve_app_of_mono π ι φ hπι n
      exact Functor.map_isIso _ _
  have key : (chains R).map (Arrow.mapCechNerve F) ≫ (chains R).map aφ =
      (chains R).map aπ ≫ (chains R).map (disc.map ι) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq]
  rw [← quasiIso_iff_comp_left ((chains R).map (Arrow.mapCechNerve F)), key]
  haveI := h1
  haveI := h2
  have h2' : QuasiIso ((chains R).map (disc.map ι)) := inferInstance
  exact quasiIso_comp ((chains R).map aπ) ((chains R).map (disc.map ι)) (hφ := h1) (hφ' := h2')

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q), (∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) → QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom)) := by
  first | (exact @GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj) | (exact GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj) | (intros; apply GlobalTheory.EtC.quasiIso_chains_cech_of_locSurj  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.LaurentFinite

theorem spMap_comp_eq_id {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (h : g.comp f = RingHom.id A) : spMap g ≫ spMap f = 𝟙 (sp A) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
  simp

theorem subsingleton_of_retract (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (h : g.comp f = RingHom.id A)
    (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q (sp A) n i, pull _ (spMap g) _ _ (pull _ (spMap f) _ _ z) = z := by
    intro z
    rw [← pull_comp, spMap_comp_eq_id f g h, pull_id]
  rw [← key x, ← key y, Subsingleton.elim (pull _ (spMap f) _ _ x) (pull _ (spMap f) _ _ y)]

theorem subsingleton_of_ringEquiv (q : ℕ) (n i : ℤ) {A B : Type} [CommRing A] [CommRing B]
    (e : A ≃+* B) (hB : Subsingleton (Ht q (sp B) n i)) : Subsingleton (Ht q (sp A) n i) :=
  subsingleton_of_retract q n i e.toRingHom e.symm.toRingHom (by ext x; simp) hB

theorem subsingleton_of_subsingleton (q : ℕ) (n i : ℤ) (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (Ht q (sp T) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q T T n i).2 (a, b)
  simp only [Prod.mk.injEq] at hx
  rw [← hx.1, ← hx.2, hfs]

instance laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] :
    Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_one (LaurentPolynomial.C (R := T)), Subsingleton.elim (1 : T) 0, map_zero]

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

noncomputable def laurentProd (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    LaurentPolynomial (T₁ × T₂) →+* LaurentPolynomial T₁ × LaurentPolynomial T₂ :=
  RingHom.prod (AddMonoidAlgebra.mapRingHom ℤ (RingHom.fst T₁ T₂))
    (AddMonoidAlgebra.mapRingHom ℤ (RingHom.snd T₁ T₂))

theorem laurentProd_C_mul_T (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] (c : T₁ × T₂) (n : ℤ) :
    laurentProd T₁ T₂ (LaurentPolynomial.C c * LaurentPolynomial.T n) =
      (LaurentPolynomial.C c.1 * LaurentPolynomial.T n, LaurentPolynomial.C c.2 * LaurentPolynomial.T n) := by
  simp only [← LaurentPolynomial.single_eq_C_mul_T, laurentProd, RingHom.prod_apply,
    AddMonoidAlgebra.mapRingHom_single, RingHom.coe_fst, RingHom.coe_snd]

theorem laurentProd_injective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Injective (laurentProd T₁ T₂) := by
  intro x y h
  simp only [laurentProd, RingHom.prod_apply, Prod.mk.injEq] at h
  ext m
  all_goals
    have h1 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.1
    have h2 := congrArg (fun z => AddMonoidAlgebra.coeff z m) h.2
    simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.coe_fst, RingHom.coe_snd] at h1 h2
    assumption

end GlobalTheory.EtC.LaurentFinite

namespace GlobalTheory.EtC.LaurentFinite

theorem laurentProd_surjective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Surjective (laurentProd T₁ T₂) := by
  have hl : ∀ f : LaurentPolynomial T₁, (f, 0) ∈ (laurentProd T₁ T₂).range := by
    intro f
    induction f using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (a, 0) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  have hr : ∀ g : LaurentPolynomial T₂, (0, g) ∈ (laurentProd T₁ T₂).range := by
    intro g
    induction g using LaurentPolynomial.induction_on' with
    | add p q hp hq => simpa using add_mem hp hq
    | C_mul_T n a =>
      refine ⟨LaurentPolynomial.C (0, a) * LaurentPolynomial.T n, ?_⟩
      rw [laurentProd_C_mul_T]; simp
  rintro ⟨f, g⟩
  have := add_mem (hl f) (hr g)
  simpa using this

theorem subsingleton_laurent_prod (q : ℕ) (n i : ℤ) (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (h₁ : Subsingleton (Ht q (sp (LaurentPolynomial T₁)) n i))
    (h₂ : Subsingleton (Ht q (sp (LaurentPolynomial T₂)) n i)) :
    Subsingleton (Ht q (sp (LaurentPolynomial (T₁ × T₂))) n i) := by
  let e := RingEquiv.ofBijective (laurentProd T₁ T₂)
    ⟨laurentProd_injective T₁ T₂, laurentProd_surjective T₁ T₂⟩
  refine subsingleton_of_ringEquiv q n i e ⟨fun x y => ?_⟩
  exact (GlobalTheory.EtC.ProdCoh.ht_prod_bijective q _ _ n i).1 (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end GlobalTheory.EtC.LaurentFinite


open GlobalTheory.EtC.LaurentFinite in
theorem GlobalTheory.EtC.laurent_vanishing_finite : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  intro q _ n hyp A _ _ hA hq
  refine GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun T _ _ => ∀ s i : ℤ, 2 ≤ s → s < n →
      Subsingleton (Ht q (sp (LaurentPolynomial T)) s i)) ?_ ?_ ?_ ?_
  · intro T T' _ _ _ _ e hT s i h2 hs
    exact subsingleton_of_ringEquiv q s i
      (AddMonoidAlgebra.mapRingEquiv ℤ e.symm.toRingEquiv) (hT s i h2 hs)
  · intro T _ _ _ s i _ _
    exact subsingleton_of_subsingleton q s i _
  · intro T₁ T₂ _ _ _ _ _ _ h₁ h₂ s i h2 hs
    exact subsingleton_laurent_prod q s i T₁ T₂ (h₁ s i h2 hs) (h₂ s i h2 hs)
  · intro T _ _ hfin hT s i h2 hs
    haveI : IsNoetherian A T := isNoetherian_of_isNoetherianRing_of_finite A T
    haveI : IsNoetherianRing T := isNoetherian_of_tower A inferInstance
    have hqT : IsUnit (q : T) := by
      simpa using hq.map (algebraMap A T)
    exact hyp T hT hqT s i h2 hs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebraStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_finite) | (exact GlobalTheory.EtC.laurent_vanishing_finite) | (intros; apply GlobalTheory.EtC.laurent_vanishing_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem cup_supp_chainsMap_mono (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) :
    Mono (((chains R).map f).f p) := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hnat := ((GlobalTheory.EtC.chains_basic R).2.1 f N)
    have hm : Mono ((free R).map (f.app (op (SimplexCategory.mk N)))) :=
      ((GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (f.app (op (SimplexCategory.mk N)))).1 inferInstance)
    have : ((chains R).map f).f (-(N : ℤ)) =
        ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom ≫ (chainsXIso R E N).inv := by simp
    rw [this, ← Category.assoc, hnat, Category.assoc]
    infer_instance
  · haveI := (GlobalTheory.EtC.chains_basic R).1 U
    exact IsZero.mono (isZero_of_isStrictlyLE _ 0 p hp) _

theorem cup_supp_extend (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (β : Cochain ((chains R).obj U) I n) :
    ∃ β' : Cochain ((chains R).obj E) I n, (Cochain.ofHom ((chains R).map f)).comp β' (zero_add n) = β := by
  refine ⟨Cochain.mk fun p q h => by
    haveI := cup_supp_chainsMap_mono R f p
    haveI := hI q
    exact Injective.factorThru (β.v p q h) (((chains R).map f).f p), ?_⟩
  refine Cochain.ext _ _ fun p q h => ?_
  haveI := cup_supp_chainsMap_mono R f p
  haveI := hI q
  rw [Cochain.comp_v _ _ (zero_add n) p p q (add_zero p) h, Cochain.ofHom_v, Cochain.mk_v]
  exact Injective.comp_factorThru (J := I.X q) (β.v p q h) (((chains R).map f).f p)

theorem cup_supp_vanish (R : Type) [CommRing R] {K : Cx R} {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g)
    {k : ℤ} (γ : Cochain ((chains R).obj E) K k)
    (hf : (Cochain.ofHom ((chains R).map f)).comp γ (zero_add k) = 0)
    (hg : (Cochain.ofHom ((chains R).map g)).comp γ (zero_add k) = 0) : γ = 0 := by
  refine Cochain.ext _ _ fun p q h => ?_
  rw [Cochain.zero_v]
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
    have hf' := congrArg (fun z => z.v (-(N : ℤ)) q h) hf
    have hg' := congrArg (fun z => z.v (-(N : ℤ)) q h) hg
    simp only [Cochain.comp_v _ _ (zero_add k) (-(N : ℤ)) (-(N : ℤ)) q (add_zero _) h, Cochain.ofHom_v,
      Cochain.zero_v] at hf' hg'
    have nf := (GlobalTheory.EtC.chains_basic R).2.1 f N
    have ng := (GlobalTheory.EtC.chains_basic R).2.1 g N
    haveI := hc.2.2 (op (SimplexCategory.mk N))
    have key : biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N)))) ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_desc_assoc, comp_zero]
        have : (free R).map (f.app (op (SimplexCategory.mk N))) =
            (chainsXIso R U N).inv ≫ ((chains R).map f).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [nf]; simp
        rw [this]; simp [hf']
      · rw [biprod.inr_desc_assoc, comp_zero]
        have : (free R).map (g.app (op (SimplexCategory.mk N))) =
            (chainsXIso R V N).inv ≫ ((chains R).map g).f (-(N : ℤ)) ≫ (chainsXIso R E N).hom := by
          rw [ng]; simp
        rw [this]; simp [hg']
    have h0 : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h = 0 := by
      rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
        ((free R).map (g.app (op (SimplexCategory.mk N))))), key, comp_zero]
    have : γ.v (-(N : ℤ)) q h = (chainsXIso R E N).hom ≫ ((chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q h) := by simp
    rw [this, h0, comp_zero]
  · haveI := (GlobalTheory.EtC.chains_basic R).1 E
    exact (isZero_of_isStrictlyLE _ 0 p hp).eq_of_src _ _

theorem cup_supp_rep (R : Type) [CommRing R] {I : Cx R} (hI : ∀ s, Injective (I.X s)) {U E : Spc} (f : U ⟶ E) [Mono f]
    {n : ℤ} (a : CohomologyClass ((chains R).obj E) I n) (ha : cpull ((chains R).map f) I n a = 0) :
    ∃ α : Cocycle ((chains R).obj E) I n, CohomologyClass.mk α = a ∧
      (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) = 0 := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 at ha
  rw [CohomologyClass.mk_eq_zero_iff] at ha
  obtain ⟨n', hn', β, hβ⟩ := ha
  have hβ2 : δ n' n β = (Cochain.ofHom ((chains R).map f)).comp α.1 (zero_add n) := hβ
  obtain ⟨β', hβ'⟩ := cup_supp_extend R hI f β
  let c : Cocycle ((chains R).obj E) I n := Cocycle.mk (δ n' n β') (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff]
    exact ⟨n', hn', β', rfl⟩
  · change (Cochain.ofHom ((chains R).map f)).comp (α.1 - δ n' n β') (zero_add n) = 0
    rw [Cochain.comp_sub, ← δ_ofHom_comp, hβ', hβ2, sub_self]

theorem cup_supp (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (hI : ∀ s, Injective (I.X s))
    (hJ : ∀ s, Injective (J.X s)) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) {n m k : ℤ}
    (hk : n + m = k) (a : CohomologyClass ((chains R).obj E) I n) (b : CohomologyClass ((chains R).obj E) J m)
    (ha : cpull ((chains R).map f) I n a = 0) (hb : cpull ((chains R).map g) J m b = 0) : μ.cup E hk a b = 0 := by
  haveI := hc.1
  haveI := hc.2.1
  obtain ⟨α, rfl, hα⟩ := cup_supp_rep R hI f a ha
  obtain ⟨β, rfl, hβ⟩ := cup_supp_rep R hJ g b hb
  obtain ⟨γ, hγ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ hk).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ hk).2 α β γ hγ, CohomologyClass.mk_eq_zero_iff]
  have evK := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := K) (n := k)
  have evI := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := I) (n := n)
  have evJ := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := J) (n := m)
  have h1 : (Cochain.ofHom ((chains R).map f)).comp γ.1 (zero_add k) = 0 := by
    have evKU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := K) (n := k)
    have evIU := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := U) (I := I) (n := n)
    apply evKU.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 f γ.1 N w h U' x, (evKU.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map f)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 0 i (by omega)).2.1 f,
      ← evI.2.2.2.1 f α.1, hα, (evIU.1 0 0 _ _ rfl U' (x.sub 0 i (by omega))).2.2.1]
    simp
  have h2 : (Cochain.ofHom ((chains R).map g)).comp γ.1 (zero_add k) = 0 := by
    have evKV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := K) (n := k)
    have evJV := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := V) (I := J) (n := m)
    apply evKV.2.2.1
    intro N w h U' x
    rw [evK.2.2.2.1 g γ.1 N w h U' x, (evKV.1 0 0 N w h U' x).2.2.1, hγ N w h U' (x.map g)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [((GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite x).2.2.1 i (N - i) (by omega)).2.1 g,
      ← evJ.2.2.2.1 g β.1, hβ, (evJV.1 0 0 _ _ rfl U' (x.sub i (N - i) (by omega))).2.2.1]
    simp
  have h0 : γ = 0 := Cocycle.ext (cup_supp_vanish R f g hc γ.1 h1 h2)
  rw [h0]
  exact zero_mem _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCoverStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover : ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), (∀ s, Injective (I.X s)) → (∀ s, Injective (J.X s)) → ∀ {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∀ {n m k : ℤ} (hk : n + m = k) a b, cpull ((chains R).map f) I n a = 0 → cpull ((chains R).map g) J m b = 0 → μ.cup E hk a b = 0 := by
  first | (exact @GlobalTheory.EtC.cup_supp) | (exact GlobalTheory.EtC.cup_supp) | (intros; apply GlobalTheory.EtC.cup_supp  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LerayInj

theorem peel (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hH : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (N : ℤ) (hN : (n : ℤ) + 1 = N)
    (c : Cochain ((chains R).obj E) (res R F) N)
    (hc : ∀ (p q : ℤ) (hpq : p + N = q), p ≠ -N → c.v p q hpq = 0)
    (β₀ : Cochain ((chains R).obj E) (res R F) n) (h₀ : δ n N β₀ = c) :
    ∀ k : ℕ, k ≤ n → ∃ β : Cochain ((chains R).obj E) (res R F) n, δ n N β = c ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(k : ℤ) < p → β.v p q hpq = 0 := by
  obtain ⟨cl, -, hcl, hcl0, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  obtain ⟨-, -, -, -, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨β₀, h₀, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, hβ, hv⟩ := ih (by omega)
    have hqk : (((n - k : ℕ) : ℤ)) = (n : ℤ) - k := by omega
    let t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X ((n - k : ℕ) : ℤ) :=
      (chainsXIso R E k).inv ≫ β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) (by omega)
    have ht : t ≫ (res R F).d ((n - k : ℕ) : ℤ) (((n - k : ℕ) : ℤ) + 1) = 0 := by
      have e := Cochain.congr_v hβ (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega)
      rw [δ_v n N hN β (-(k : ℤ)) (((n - k : ℕ) : ℤ) + 1) (by omega) ((n - k : ℕ) : ℤ) (-(k : ℤ) + 1)
        (by omega) rfl, hc _ _ _ (by omega), hv (-(k : ℤ) + 1) (((n - k : ℕ) : ℤ) + 1) (by omega) (by omega),
        comp_zero, smul_zero, add_zero] at e
      simp only [t, Category.assoc, e, comp_zero]
    have h0 : cl _ _ t ht = cl _ _ 0 zero_comp :=
      (hH k (n - k) (by omega) (by omega) _).trans (hcl0 _ _).symm
    obtain ⟨y, hy⟩ := ((hcl _ _ _ _ _ _).1 h0)
    rw [zero_add] at hy
    let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
      Cochain.single (p := -(k : ℤ)) (q := ((n - k : ℕ) : ℤ) - 1) ((chainsXIso R E k).hom ≫ y) ((n : ℤ) - 1)
    refine ⟨β - δ ((n : ℤ) - 1) n γ, ?_, ?_⟩
    · rw [δ_sub, δ_δ, sub_zero, hβ]
    · intro p q hpq hp
      rw [Cochain.sub_v, Cochain.δ_single _ ((n : ℤ) - 1) n (by omega) (-(k : ℤ) - 1) ((n - k : ℕ) : ℤ) (by omega) (by omega),
        Cochain.add_v, Cochain.units_smul_v]
      by_cases hpk : p = -(k : ℤ)
      · subst hpk
        obtain rfl : q = ((n - k : ℕ) : ℤ) := by omega
        rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero]
        have hb : β.v (-(k : ℤ)) ((n - k : ℕ) : ℤ) hpq = (chainsXIso R E k).hom ≫ t := by
          simp only [t, Iso.hom_inv_id_assoc]
        rw [hb, hy, Category.assoc, sub_self]
      · rw [hv p q hpq (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpk,
          Cochain.single_v_eq_zero _ _ _ _ _ (by omega), smul_zero, add_zero, sub_zero]

end GlobalTheory.EtC.LerayInj

namespace GlobalTheory.EtC

theorem leray_inj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) →
    (∀ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls (R := R) (E := E) (n := 0) s 0 → s = 0) ∧
    ∀ s : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ F, IsCls (R := R) (E := E) (n := n + 1) s 0 →
      ∃ t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd (R := R) (E := E) (n := n) t = s := by
  intro R _ F E n hH
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  constructor
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β, hβ⟩ := hz0
    have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) 0 (by simp)
    have h1 : β.v (-((0 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    have h2 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 := (hpos E 1 (by norm_num)).eq_of_tgt _ _
    rw [δ_v m _ hm β _ 0 _ (-1) 1 (by omega) (by omega), h1, h2, zero_comp, zero_comp, smul_zero,
      add_zero] at e
    have e' : (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).hom ≫ s ≫ resι R F := by
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((0 : ℕ) : ℤ)) = z.1 from rfl, hz, Cochain.single_v]
    rw [e'] at e
    have e2 : s ≫ resι R F = 0 ≫ resι R F := by
      rw [zero_comp]
      exact (cancel_epi (chainsXIso R E 0).hom).1 (by rw [← e, comp_zero])
    exact (cancel_mono (resι R F)).1 e2
  · rintro s ⟨z, hz0, hz⟩
    rw [CohomologyClass.mk_eq_zero_iff] at hz0
    obtain ⟨m, hm, β₀, hβ₀⟩ := hz0
    obtain rfl : m = (n : ℤ) := by push_cast at hm; omega
    have hzv : ∀ (p q : ℤ) (hpq : p + ((n + 1 : ℕ) : ℤ) = q),
        (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)).v p q hpq =
          (Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
            ((chainsXIso R E (n + 1)).hom ≫ s ≫ resι R F) ((n + 1 : ℕ) : ℤ)).v p q hpq := by
      intro p q hpq
      rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((n + 1 : ℕ) : ℤ)) = z.1 from rfl, hz]
    obtain ⟨β, hβ, hv⟩ := LerayInj.peel R F E n hH ((n + 1 : ℕ) : ℤ) (by push_cast; rfl) z
      (fun p q hpq hp => by rw [hzv, Cochain.single_v_eq_zero _ _ _ _ _ hp]) β₀ hβ₀ n le_rfl

    let b := β.v (-(n : ℤ)) 0 (by omega)
    have hb : b ≫ (res R F).d 0 1 = 0 := by
      have e := Cochain.congr_v hβ (-(n : ℤ)) 1 (by push_cast; omega)
      rw [δ_v (n : ℤ) _ (by push_cast; rfl) β (-(n : ℤ)) 1 _ 0 (-(n : ℤ) + 1) (by omega) rfl,
        hv (-(n : ℤ) + 1) 1 (by omega) (by omega), comp_zero, smul_zero, add_zero, hzv,
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
      exact e
    haveI : Mono (ShortComplex.mk _ _ w).f := hmono
    let t' : ((chains R).obj E).X (-(n : ℤ)) ⟶ F := hex.lift b hb
    have ht' : t' ≫ resι R F = b := hex.lift_f b hb

    have e := Cochain.congr_v hβ (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    have h1 : β.v (-((n + 1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
    rw [δ_v (n : ℤ) _ (by push_cast; rfl) β _ 0 _ (-1) (-(n : ℤ)) (by omega) (by push_cast; omega), h1,
      zero_comp, zero_add, hzv, Cochain.single_v] at e
    rw [show β.v (-(n : ℤ)) 0 (by omega) = b from rfl, ← ht'] at e
    have hD : ((chainsN R).obj E).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i) :=
      AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
    let D : (free R).obj (E.obj (op ⦋n + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋n⦌)) :=
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
    have hd : ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
        (chainsXIso R E (n + 1)).hom ≫ D ≫ (chainsXIso R E n).inv :=
      (HomologicalComplex.extend_d_eq _ _ rfl rfl).trans
        (congrArg (fun D' => (chainsXIso R E (n + 1)).hom ≫ D' ≫ (chainsXIso R E n).inv) hD)
    rw [hd] at e
    have hs : s = (((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E n).inv ≫ t') := by
      apply (cancel_epi (chainsXIso R E (n + 1)).hom).1
      apply (cancel_mono (resι R F)).1
      rw [Category.assoc, ← e]
      simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    refine ⟨(((n + 1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E n).inv ≫ t'), ?_⟩
    rw [hs]
    simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
      smul_smul, Category.assoc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevelsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leray_simplicialCocycle_coboundary_of_acyclicLevels : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk (k))))) F m, y = 0) → (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (0)))) ⟶ F, IsCls s 0 → s = 0) ∧ ∀ s : (free R).obj (E.obj (op (SimplexCategory.mk (n + 1)))) ⟶ F, IsCls s 0 → ∃ t : (free R).obj (E.obj (op (SimplexCategory.mk (n)))) ⟶ F, cobd t = s := by
  first | (exact @GlobalTheory.EtC.leray_inj) | (exact GlobalTheory.EtC.leray_inj) | (intros; apply GlobalTheory.EtC.leray_inj <;> assumption)
end
end
