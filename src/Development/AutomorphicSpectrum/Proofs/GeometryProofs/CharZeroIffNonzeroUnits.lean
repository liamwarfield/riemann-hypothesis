module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericMap
theorem UpperTheory.Reformulated.B.GenericMap.aux1 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing Ω (@CommSemiring.toSemiring Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst))) := by
  intro Ω inst
  infer_instance

noncomputable def UpperTheory.Reformulated.B.GenericMap.genPt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          @Quiver.Hom AlgebraicGeometry.Scheme
              (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
              (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X →
            ↥X :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) ↦
      ξ
        (@IsLocalRing.closedPoint Ω (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst))
          (@UpperTheory.Reformulated.B.GenericMap.aux1 Ω inst))

noncomputable def UpperTheory.Reformulated.B.GenericMap.Cpt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          @Quiver.Hom AlgebraicGeometry.Scheme
              (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
              (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X →
            Type :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) ↦
      @Subtype ↥X fun (p : ↥X) ↦
        @Specializes (↥X)
          (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
            X.toSheafedSpace)
          (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p

theorem UpperTheory.Reformulated.B.GenericMap.aux4 :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      (ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
      (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ),
      @Specializes (↥X)
        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
          X.toSheafedSpace)
        (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ)
        (@Subtype.val (↥X)
          (fun (p : ↥X) ↦
            @Specializes (↥X)
              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                X.toSheafedSpace)
              (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
          p) := by
  intro X Ω inst ξ p
  exact p.2

theorem UpperTheory.Reformulated.B.GenericMap.aux5 :
    ∀ {Ω : Type} [inst : Field Ω],
      @IsLocalRing (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
        (@CommSemiring.toSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
          (@CommRing.toCommSemiring (↑(@CommRingCat.of Ω (@Field.toCommRing Ω inst)) : Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier (@CommRingCat.of Ω (@Field.toCommRing Ω inst))))) := by
  intro Ω inst
  infer_instance

noncomputable def UpperTheory.Reformulated.B.GenericMap.genMap :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) →
              @RingHom
                (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                      (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                        (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                          X.toSheafedSpace))
                      (@Subtype.val (↥X)
                        (fun (p : ↥X) ↦
                          @Specializes (↥X)
                            (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                              CommRingCat.instCategory X.toSheafedSpace)
                            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                        p)) :
                  Type)
                Ω
                (@Semiring.toNonAssocSemiring
                  (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                        CommRingCat.Colimits.hasColimits_commRingCat
                        (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                          (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                            X.toSheafedSpace))
                        (@Subtype.val (↥X)
                          (fun (p : ↥X) ↦
                            @Specializes (↥X)
                              (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                CommRingCat.instCategory X.toSheafedSpace)
                              (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                          p)) :
                    Type)
                  (@CommSemiring.toSemiring
                    (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                            p)) :
                      Type)
                    (@CommRing.toCommSemiring
                      (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                            CommRingCat.Colimits.hasColimits_commRingCat
                            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                                X.toSheafedSpace))
                            (@Subtype.val (↥X)
                              (fun (p : ↥X) ↦
                                @Specializes (↥X)
                                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                    CommRingCat.instCategory X.toSheafedSpace)
                                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                              p)) :
                        Type)
                      (@CommRingCat.instCommRingObjForgetRingHomCarrier
                        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory
                          CommRingCat.Colimits.hasColimits_commRingCat
                          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                              X.toSheafedSpace))
                          (@Subtype.val (↥X)
                            (fun (p : ↥X) ↦
                              @Specializes (↥X)
                                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                                  CommRingCat.instCategory X.toSheafedSpace)
                                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                            p))))))
                (@Semiring.toNonAssocSemiring Ω
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst)))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      @CommRingCat.Hom.hom
        (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
          (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
            (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
          (@Subtype.val (↥X)
            (fun (p : ↥X) ↦
              @Specializes (↥X)
                (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                  X.toSheafedSpace)
                (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
            p))
        (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
        (@CategoryTheory.CategoryStruct.comp CommRingCat
          (@CategoryTheory.Category.toCategoryStruct CommRingCat CommRingCat.instCategory)
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
              p))
          (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ))
          (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
          (@TopCat.Presheaf.stalkSpecializes CommRingCat CommRingCat.instCategory
            CommRingCat.Colimits.hasColimits_commRingCat
            (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
              (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
            (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ)
            (@Subtype.val (↥X)
              (fun (p : ↥X) ↦
                @Specializes (↥X)
                  (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                    X.toSheafedSpace)
                  (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
              p)
            (@UpperTheory.Reformulated.B.GenericMap.aux4 X Ω inst ξ p))
          (@AlgebraicGeometry.Scheme.stalkClosedPointTo X (@CommRingCat.of Ω (@Field.toCommRing Ω inst))
            (@UpperTheory.Reformulated.B.GenericMap.aux5 Ω inst) ξ))

noncomputable def UpperTheory.Reformulated.B.GenericMap.regAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ →
              @Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))) :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      @RingHom.range
        (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
              (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
              (@Subtype.val (↥X)
                (fun (p : ↥X) ↦
                  @Specializes (↥X)
                    (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace)
                    (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                p)) :
          Type)
        Ω
        (@NonAssocCommRing.toNonAssocRing
          (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                  p)) :
            Type)
          (@CommRing.toNonAssocCommRing
            (↑(@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                  (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                    (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory
                      X.toSheafedSpace))
                  (@Subtype.val (↥X)
                    (fun (p : ↥X) ↦
                      @Specializes (↥X)
                        (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                          CommRingCat.instCategory X.toSheafedSpace)
                        (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                    p)) :
              Type)
            (@CommRingCat.instCommRingObjForgetRingHomCarrier
              (@TopCat.Presheaf.stalk CommRingCat CommRingCat.instCategory CommRingCat.Colimits.hasColimits_commRingCat
                (@AlgebraicGeometry.PresheafedSpace.carrier CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@AlgebraicGeometry.PresheafedSpace.presheaf CommRingCat CommRingCat.instCategory
                  (@AlgebraicGeometry.SheafedSpace.toPresheafedSpace CommRingCat CommRingCat.instCategory X.toSheafedSpace))
                (@Subtype.val (↥X)
                  (fun (p : ↥X) ↦
                    @Specializes (↥X)
                      (@AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier CommRingCat
                        CommRingCat.instCategory X.toSheafedSpace)
                      (@UpperTheory.Reformulated.B.GenericMap.genPt X Ω inst ξ) p)
                  p)))))
        (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))
        (@UpperTheory.Reformulated.B.GenericMap.genMap X Ω inst ξ p)

noncomputable def UpperTheory.Reformulated.B.GenericMap.unitAt :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ → Ω → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) (a : Ω) ↦
      And
        (@Ne Ω a
          (@OfNat.ofNat Ω (nat_lit 0)
            (@Zero.toOfNat0 Ω
              (@MulZeroClass.toZero Ω
                (@instMulZeroClassOfSemiring Ω
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst))))))))
        (And
          (@Membership.mem Ω
            (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
            (@SetLike.instMembership
              (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
              Ω
              (@Subring.instSetLike Ω
                (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))))
            (@UpperTheory.Reformulated.B.GenericMap.regAt X Ω inst ξ p) a)
          (@Membership.mem Ω
            (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
            (@SetLike.instMembership
              (@Subring Ω (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst))))
              Ω
              (@Subring.instSetLike Ω
                (@NonAssocCommRing.toNonAssocRing Ω (@CommRing.toNonAssocCommRing Ω (@Field.toCommRing Ω inst)))))
            (@UpperTheory.Reformulated.B.GenericMap.regAt X Ω inst ξ p)
            (@Inv.inv Ω
              (@InvOneClass.toInv Ω
                (@DivInvOneMonoid.toInvOneClass Ω
                  (@DivisionMonoid.toDivInvOneMonoid Ω
                    (@DivisionCommMonoid.toDivisionMonoid Ω
                      (@CommGroupWithZero.toDivisionCommMonoid Ω
                        (@Semifield.toCommGroupWithZero Ω (@Field.toSemifield Ω inst)))))))
              a)))

noncomputable def UpperTheory.Reformulated.B.GenericMap.InFibre :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            Nat → @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : Nat) (q : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      Not
        (@UpperTheory.Reformulated.B.GenericMap.unitAt X Ω inst ξ q
          (@Nat.cast Ω
            (@AddMonoidWithOne.toNatCast Ω
              (@AddGroupWithOne.toAddMonoidWithOne Ω
                (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst)))))
            p))

noncomputable def UpperTheory.Reformulated.B.GenericMap.Char0 :
    {X : AlgebraicGeometry.Scheme} →
      {Ω : Type} →
        [inst : Field Ω] →
          (ξ :
              @Quiver.Hom AlgebraicGeometry.Scheme
                (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
                  (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
                (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X) →
            @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ → Prop :=
    fun {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
        (ξ :
          @Quiver.Hom AlgebraicGeometry.Scheme
            (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
              (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
            (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X)
        (p : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ) ↦
      ∀ (r : Nat), Nat.Prime r → Not (@UpperTheory.Reformulated.B.GenericMap.InFibre X Ω inst ξ r p)

namespace UpperTheory.Reformulated.B.GenericMap.Hlp
private theorem units_nat {Ω : Type} [Field Ω] (S : Subring Ω)
    (hp : ∀ r : ℕ, r.Prime → ((r : Ω) ≠ 0 ∧ (r : Ω) ∈ S ∧ (r : Ω)⁻¹ ∈ S)) :
    ∀ n : ℕ, n ≠ 0 → ((n : Ω) ≠ 0 ∧ (n : Ω) ∈ S ∧ (n : Ω)⁻¹ ∈ S) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [S.one_mem]
  | prime p hpp => intro _; exact hp p hpp
  | mul a b ha hb =>
    intro hab
    have ha0 : a ≠ 0 := fun h => hab (by simp [h])
    have hb0 : b ≠ 0 := fun h => hab (by simp [h])
    obtain ⟨a1, a2, a3⟩ := ha ha0
    obtain ⟨b1, b2, b3⟩ := hb hb0
    refine ⟨by push_cast; exact mul_ne_zero a1 b1, by push_cast; exact S.mul_mem a2 b2, ?_⟩
    push_cast; rw [mul_inv]; exact S.mul_mem a3 b3
end UpperTheory.Reformulated.B.GenericMap.Hlp

theorem UpperTheory.Reformulated.B.GenericMap.main :
    ∀ {X : AlgebraicGeometry.Scheme} {Ω : Type} [inst : Field Ω]
      {ξ :
        @Quiver.Hom AlgebraicGeometry.Scheme
          (@CategoryTheory.ReflQuiver.toQuiver AlgebraicGeometry.Scheme
            (@CategoryTheory.catToReflQuiver AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.instCategory))
          (AlgebraicGeometry.Spec (@CommRingCat.of Ω (@Field.toCommRing Ω inst))) X}
      {q : @UpperTheory.Reformulated.B.GenericMap.Cpt X Ω inst ξ},
      @UpperTheory.Reformulated.B.GenericMap.Char0 X Ω inst ξ q →
        ∀ (n : Nat),
          @Ne Nat n (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @UpperTheory.Reformulated.B.GenericMap.unitAt X Ω inst ξ q
              (@Nat.cast Ω
                (@AddMonoidWithOne.toNatCast Ω
                  (@AddGroupWithOne.toAddMonoidWithOne Ω
                    (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst)))))
                n) := by
  intro X Ω inst ξ q hq n hn
  have key := UpperTheory.Reformulated.B.GenericMap.Hlp.units_nat (UpperTheory.Reformulated.B.GenericMap.regAt ξ q)
    (fun r hr => by
      have := hq r hr
      unfold UpperTheory.Reformulated.B.GenericMap.InFibre at this
      exact not_not.mp this) n hn
  exact key
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CharTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

theorem unit_natCast (h : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.GenericMap.main h n hn

theorem char_zero_iff_integers_units (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω]
    (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω) (ht : CoordTie (𝓞 F) ξ t) (p : Cpt ξ) :
    Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  constructor
  · intro h d hd
    have hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p := by
      intro b
      obtain ⟨c, hc⟩ := ht.cover p
      exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc
    have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
    have hu := unit_natCast h _ hn
    have e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d' := by
      rw [← map_mul, ← hd', map_natCast]
    rw [e] at hu
    have ha : algebraMap (𝓞 F) Ω d ≠ 0 := left_ne_zero_of_mul hu.1
    have hb : algebraMap (𝓞 F) Ω d' ≠ 0 := right_ne_zero_of_mul hu.1
    refine ⟨ha, hreg d, ?_⟩
    have e2 : (algebraMap (𝓞 F) Ω d)⁻¹ =
        algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹ := by
      field_simp
    rw [e2]
    exact mul_mem (hreg d') hu.2.2
  · intro h r hr hf
    have hr0 : (r : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    have := h _ hr0
    rw [map_natCast] at this
    exact hf this

end GlobalTheory.CompanionTheory.Ar.SncBase.CharTie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_zero_iff_nonzero_units : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω), CoordTie (𝓞 F) ξ t → ∀ p : Cpt ξ, Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | exact GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units <;> assumption)
end
