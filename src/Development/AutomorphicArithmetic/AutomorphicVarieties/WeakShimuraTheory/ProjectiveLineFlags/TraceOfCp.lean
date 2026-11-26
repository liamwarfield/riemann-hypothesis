module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPairAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrMap
noncomputable def UpperTheory.Reformulated.B.Qi38.Irr :
    {R : Type} →
      [inst : CommRing R] →
        {H : Type} →
          [inst_1 : Group H] →
            {n : Type} →
              [inst_2 : Fintype n] →
                [inst_3 : DecidableEq n] →
                  @MonoidHom H (Matrix n n R)
                      (@MulOneClass.toMulOne H
                        (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                      (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                        (@MulOneClass.toMulOne R
                          (@MulZeroOneClass.toMulOneClass R
                            (@instMulZeroOneClassOfSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                    Prop :=
    fun {R : Type} [inst : CommRing R] {H : Type} [inst_1 : Group H] {n : Type} [inst_2 : Fintype n]
        [inst_3 : DecidableEq n]
        (r :
          @MonoidHom H (Matrix n n R)
            (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
              (@MulOneClass.toMulOne R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))) ↦
      @Eq
        (@Submodule R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@Matrix.addCommMonoid n n R
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
        (@Submodule.span R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@Matrix.addCommMonoid n n R
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.range (Matrix n n R) H
            (@DFunLike.coe
              (@MonoidHom H (Matrix n n R)
                (@MulOneClass.toMulOne H
                  (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                  (@MulOneClass.toMulOne R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              H (fun (x : H) ↦ Matrix n n R)
              (@MonoidHom.instFunLike H (Matrix n n R)
                (@MulOneClass.toMulOne H
                  (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_1))))
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_2 inst_3
                  (@MulOneClass.toMulOne R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              r)))
        (@Top.top
          (@Submodule R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Matrix.addCommMonoid n n R
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
          (@Submodule.instTop R (Matrix n n R) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@Matrix.addCommMonoid n n R
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Matrix.module n n R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Semiring.toModule R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi38.modFun :
    {O M ι : Type} →
      [inst : CommRing O] →
        [inst_1 : AddCommGroup M] →
          [@_root_.Module O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
                (@AddCommGroup.toAddCommMonoid M inst_1)] →
            @_root_.Module O (ι → M) (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
              (@Pi.addCommMonoid ι (fun (a : ι) ↦ M) fun (i : ι) ↦ @AddCommGroup.toAddCommMonoid M inst_1) :=
    fun {O M ι : Type} [inst : CommRing O] [inst_1 : AddCommGroup M]
        [inst_2 :
          @_root_.Module O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
            (@AddCommGroup.toAddCommMonoid M inst_1)] ↦
      @Pi.Function.module ι O M (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst))
        (@AddCommGroup.toAddCommMonoid M inst_1) inst_2
attribute [local instance] UpperTheory.Reformulated.B.Qi38.modFun

noncomputable def UpperTheory.Reformulated.B.Qi38.mapRep :
    {R R' : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing R'] →
          {H : Type} →
            [inst_2 : Group H] →
              {n : Type} →
                [inst_3 : Fintype n] →
                  [inst_4 : DecidableEq n] →
                    @RingHom R R'
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring R'
                          (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) →
                      @MonoidHom H (Matrix n n R)
                          (@MulOneClass.toMulOne H
                            (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
                          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_3 inst_4
                            (@MulOneClass.toMulOne R
                              (@MulZeroOneClass.toMulOneClass R
                                (@instMulZeroOneClassOfSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                            (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                        @MonoidHom H (Matrix n n R')
                          (@MulOneClass.toMulOne H
                            (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
                          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R' inst_3 inst_4
                            (@MulOneClass.toMulOne R'
                              (@MulZeroOneClass.toMulOneClass R'
                                (@instMulZeroOneClassOfSemiring R'
                                  (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1)))))
                            (@Semiring.toAddCommMonoid R'
                              (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1)))) :=
    fun {R R' : Type} [inst : CommRing R] [inst_1 : CommRing R'] {H : Type} [inst_2 : Group H] {n : Type}
        [inst_3 : Fintype n] [inst_4 : DecidableEq n]
        (f :
          @RingHom R R' (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))))
        (r :
          @MonoidHom H (Matrix n n R)
            (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid n R inst_3 inst_4
              (@MulOneClass.toMulOne R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              (@Semiring.toAddCommMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))) ↦
      @MonoidHom.comp H (Matrix n n R) (Matrix n n R')
        (@MulOneClass.toMulOne H (@Monoid.toMulOneClass H (@DivInvMonoid.toMonoid H (@Group.toDivInvMonoid H inst_2))))
        (@MulOneClass.toMulOne (Matrix n n R)
          (@MulZeroOneClass.toMulOneClass (Matrix n n R)
            (@NonAssocSemiring.toMulZeroOneClass (Matrix n n R)
              (@Matrix.nonAssocSemiring n R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) inst_3
                inst_4))))
        (@MulOneClass.toMulOne (Matrix n n R')
          (@MulZeroOneClass.toMulOneClass (Matrix n n R')
            (@NonAssocSemiring.toMulZeroOneClass (Matrix n n R')
              (@Matrix.nonAssocSemiring n R'
                (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) inst_3
                inst_4))))
        (@RingHom.toMonoidHom (Matrix n n R) (Matrix n n R')
          (@Matrix.nonAssocSemiring n R
            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) inst_3 inst_4)
          (@Matrix.nonAssocSemiring n R'
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) inst_3
            inst_4)
          (@RingHom.mapMatrix n R R' inst_3 inst_4
            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@Semiring.toNonAssocSemiring R' (@CommSemiring.toSemiring R' (@CommRing.toCommSemiring R' inst_1))) f))
        r

private theorem UpperTheory.Reformulated.B.Qi38.aux {Γ E E' : Type} [Field E] [Field E'] (f : E →+* E') {n : Nat}
    (r : Γ → Matrix (Fin n) (Fin n) E) (hr : Submodule.span E (Set.range r) = ⊤)
    (N : Submodule E' (Fin n → E'))
    (hN : ∀ g v, v ∈ N → ((r g).map f).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  have key : ∀ A : Matrix (Fin n) (Fin n) E, ∀ v ∈ N, (A.map f).mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span E (Set.range r) := by rw [hr]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero =>
      rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]
      exact N.zero_mem
    | add x y _ _ hx hy =>
      rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]
      exact N.add_mem hx hy
    | smul a x _ hx =>
      have h : (a • x).map f = f a • x.map f := by
        ext i j
        simp
      rw [h, Matrix.smul_mulVec]
      exact N.smul_mem _ hx
  refine or_iff_not_imp_left.2 fun hne => ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  have hj' : v j ≠ 0 := hj
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  refine N.sum_mem fun i _ => ?_
  have h1 := N.smul_mem (w i * (v j)⁻¹) (key (Matrix.single i j 1) v hv)
  have h2 : (w i * (v j)⁻¹) • ((Matrix.single i j (1 : E)).map f).mulVec v = Pi.single i (w i) := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hj']
    · simp [hk]
  rwa [h2] at h1

theorem UpperTheory.Reformulated.B.Qi38.irr_map :
    ∀ {Γ E E' : Type} [inst : Group Γ] [inst_1 : Field E] [inst_2 : Field E']
      (f :
        @RingHom E E'
          (@Semiring.toNonAssocSemiring E
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))
          (@Semiring.toNonAssocSemiring E'
            (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))))
      {n : Nat}
      (r :
        @MonoidHom Γ (Matrix (Fin n) (Fin n) E)
          (@MulOneClass.toMulOne Γ (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
          (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E (Fin.fintype n) (instDecidableEqFin n)
            (@MulOneClass.toMulOne E
              (@MulZeroOneClass.toMulOneClass E
                (@instMulZeroOneClassOfSemiring E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1))))))
            (@Semiring.toAddCommMonoid E
              (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))))),
      @UpperTheory.Reformulated.B.Qi38.Irr E (@Field.toCommRing E inst_1) Γ inst (Fin n) (Fin.fintype n) (instDecidableEqFin n) r →
        ∀
          (N :
            @Submodule E' (Fin n → E')
              (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid E'
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
              (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                (@Semiring.toModule E'
                  (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))),
          (∀ (g : Γ) (v : Fin n → E'),
              @Membership.mem (Fin n → E')
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@SetLike.instMembership
                    (@Submodule E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                    (Fin n → E')
                    (@Submodule.setLike E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))
                  N v →
                @Membership.mem (Fin n → E')
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@SetLike.instMembership
                    (@Submodule E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                    (Fin n → E')
                    (@Submodule.setLike E' (Fin n → E')
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                      (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                        @Semiring.toAddCommMonoid E'
                          (@DivisionSemiring.toSemiring E'
                            (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                      (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                        (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                        (@Semiring.toModule E'
                          (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))
                  N
                  (@Matrix.mulVec (Fin n) (Fin n) E'
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring E'
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing E'
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing E'
                          (@CommRing.toNonUnitalCommRing E' (@Field.toCommRing E' inst_2)))))
                    (Fin.fintype n)
                    (@DFunLike.coe
                      (@MonoidHom Γ (Matrix (Fin n) (Fin n) E')
                        (@MulOneClass.toMulOne Γ
                          (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
                        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E' (Fin.fintype n)
                          (instDecidableEqFin n)
                          (@MulOneClass.toMulOne E'
                            (@MulZeroOneClass.toMulOneClass E'
                              (@instMulZeroOneClassOfSemiring E'
                                (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                          (@Semiring.toAddCommMonoid E'
                            (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                      Γ (fun (x : Γ) ↦ Matrix (Fin n) (Fin n) E')
                      (@MonoidHom.instFunLike Γ (Matrix (Fin n) (Fin n) E')
                        (@MulOneClass.toMulOne Γ
                          (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst))))
                        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) E' (Fin.fintype n)
                          (instDecidableEqFin n)
                          (@MulOneClass.toMulOne E'
                            (@MulZeroOneClass.toMulOneClass E'
                              (@instMulZeroOneClassOfSemiring E'
                                (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                          (@Semiring.toAddCommMonoid E'
                            (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                      (@UpperTheory.Reformulated.B.Qi38.mapRep E E' (@Field.toCommRing E inst_1) (@Field.toCommRing E' inst_2) Γ inst
                        (Fin n) (Fin.fintype n) (instDecidableEqFin n) f r)
                      g)
                    v)) →
            Or
              (@Eq
                (@Submodule E' (Fin n → E')
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid E'
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                  (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                    (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                    (@Semiring.toModule E'
                      (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                N
                (@Bot.bot
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@Submodule.instBot E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))))
              (@Eq
                (@Submodule E' (Fin n → E')
                  (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid E'
                      (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                  (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                    (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                    (@Semiring.toModule E'
                      (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                N
                (@Top.top
                  (@Submodule E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2))))))
                  (@Submodule.instTop E' (Fin n → E')
                    (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2)))
                    (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ E') fun (i : Fin n) ↦
                      @Semiring.toAddCommMonoid E'
                        (@DivisionSemiring.toSemiring E' (@Semifield.toDivisionSemiring E' (@Field.toSemifield E' inst_2))))
                    (@UpperTheory.Reformulated.B.Qi38.modFun E' E' (Fin n) (@Field.toCommRing E' inst_2)
                      (@Ring.toAddCommGroup E' (@DivisionRing.toRing E' (@Field.toDivisionRing E' inst_2)))
                      (@Semiring.toModule E'
                        (@CommSemiring.toSemiring E' (@CommRing.toCommSemiring E' (@Field.toCommRing E' inst_2)))))))) := by
  intro Γ E E' _ _ _ f n r hr N hN
  exact UpperTheory.Reformulated.B.Qi38.aux f (fun g => r g) hr N hN
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TrNe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.trNe :
    ∀ {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H : Subgroup Γ) (χ : Fin (n + 1) → Γ →* kˣ), (Function.Injective fun i => (χ i).comp H.subtype) →
          H = ⊤ ∨ ∃ g, g ∉ H ∧ ∑ i, (χ i g : k) ≠ 0 := by
  intro Γ k _ _ n H χ hinj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hH, hz⟩ := hcon
  have hz' : ∀ g, g ∉ H → ∑ i, (χ i g : k) = 0 := by
    intro g hg
    by_contra h
    exact hz ⟨g, hg, h⟩
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 ∉ H := by
    by_contra h
    apply hH
    rw [eq_top_iff]
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let ψ : Fin (n + 1) → (H →* k) := fun i => (Units.coeHom k).comp ((χ i).comp H.subtype)
  have hψ : Function.Injective ψ := by
    intro i j hij
    apply hinj
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom H k).comp ψ hψ
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (fun i => (χ i g0 : k)) (by
    funext h
    have hm : g0 * (h : Γ) ∉ H := fun hm => hg0 ((H.mul_mem_cancel_right h.2).1 hm)
    have := hz' _ hm
    simp only [map_mul, Units.val_mul] at this
    simpa [ψ, Finset.sum_apply] using this) 0
  exact (χ 0 g0).ne_zero h0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceSwap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Matrix

private theorem irr_map {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ}
    (r : Γ →* Matrix (Fin n) (Fin n) E) (hr : Irr r) (N : Submodule E' (Fin n → E'))
    (hN : ∀ g, ∀ v ∈ N, (mapRep f r g) *ᵥ v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qi38.irr_map f r hr N hN

private theorem trace_swap {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (N M : Submodule K V) (hc : IsCompl N M) (T : Module.End K V)
    (h1 : ∀ v ∈ N, T v ∈ M) (h2 : ∀ v ∈ M, T v ∈ N) : LinearMap.trace K V T = 0 := by
  obtain ⟨p, hpN, hpM⟩ : ∃ p : Module.End K V, (∀ v ∈ N, p v = v) ∧ (∀ v ∈ M, p v = 0) :=
    ⟨N.subtype ∘ₗ N.linearProjOfIsCompl M hc, fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩),
      fun v hv =>
      congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨v, hv⟩)⟩
  have key : T = (p * T) * (1 - p) + ((1 - p) * T) * p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb, hpN _ (h2 b hb), hpM _ (h1 a ha), add_comm]
  have hpp : p * p = p := by
    ext v
    have hv : v ∈ N ⊔ M := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    simp [hpN a ha, hpM b hb]
  rw [key, map_add (f := _), LinearMap.trace_mul_comm K (p * T), LinearMap.trace_mul_comm K ((1 - p) * T),
    ← mul_assoc, ← mul_assoc, sub_mul, mul_sub, hpp]
  simp

theorem UpperTheory.V.Ws.P1.irrTr :
    ∀ {Γ E E' : Type} [Group Γ] [Field E] [Field E'] (f : E →+* E') {n : ℕ} (H : Subgroup Γ) (r : Γ →* Matrix (Fin n) (Fin n) E), (2 : E) ≠ 0 → Irr r →
          (∀ a b, a ∉ H → b ∉ H → a * b ∈ H) → (H = ⊤ ∨ ∃ g, g ∉ H ∧ (r g).trace ≠ 0) → U3.MatIrr H (mapRep f r) := by
  intro Γ E E' _ _ _ f n H r _ hr hH hg N hN
  rcases hg with rfl | ⟨g, hg, ht⟩
  · exact irr_map f r hr N fun g => hN g trivial
  set ρ := mapRep f r with hρ
  let M : Submodule E' (Fin n → E') := N.map (Matrix.mulVecLin (ρ g))
  have hNM : ∀ a, a ∉ H → ∀ v ∈ N, ρ a *ᵥ v ∈ M := by
    intro a ha v hv
    have : g⁻¹ * a ∈ H := hH _ _ (fun h => hg (H.inv_mem_iff.1 h)) ha
    refine ⟨_, hN _ this v hv, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel_left]
  have hMN : ∀ a, a ∉ H → ∀ v ∈ M, ρ a *ᵥ v ∈ N := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hN _ (hH _ _ ha hg) v hv
  have hMM : ∀ a ∈ H, ∀ v ∈ M, ρ a *ᵥ v ∈ M := by
    rintro a ha _ ⟨v, hv, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← map_mul]
    exact hNM _ (fun h => hg ((H.mul_mem_cancel_left ha).1 h)) v hv
  by_contra hcon
  obtain ⟨hb, htop⟩ := not_or.1 hcon
  have hinf : N ⊓ M = ⊥ := by
    refine (irr_map f r hr (N ⊓ M) fun a v hv => ?_).resolve_right fun h => htop (top_le_iff.1 (h ▸ inf_le_left))
    by_cases ha : a ∈ H
    · exact ⟨hN a ha v hv.1, hMM a ha v hv.2⟩
    · exact ⟨hMN a ha v hv.2, hNM a ha v hv.1⟩
  have hsup : N ⊔ M = ⊤ := by
    refine (irr_map f r hr (N ⊔ M) fun a v hv => ?_).resolve_left fun h => hb (le_bot_iff.1 (h ▸ le_sup_left))
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    by_cases ha : a ∈ H
    · exact Submodule.add_mem_sup (hN a ha x hx) (hMM a ha y hy)
    · rw [add_comm]
      exact Submodule.add_mem_sup (hMN a ha y hy) (hNM a ha x hx)
  have hc : IsCompl N M := ⟨disjoint_iff.2 hinf, codisjoint_iff.2 hsup⟩
  have h0 := trace_swap N M hc (Matrix.toLin' (ρ g)) (fun v hv => hNM g hg v hv) (fun v hv => hMN g hg v hv)
  rw [Matrix.trace_toLin'_eq] at h0
  apply ht
  apply f.injective
  rw [map_zero, ← h0]
  simp [Matrix.trace, hρ]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_of_cp {R k : Type} [CommRing R] [Field k] (f : R →+* k) (M : Matrix (Fin 4) (Fin 4) R) (a : Fin 4 → k)
    (h : M.charpoly.map f = ∏ i, (X - C (a i))) : f M.trace = ∑ i, a i := by
  have h1 := Matrix.trace_eq_neg_charpoly_nextCoeff (M.map f)
  rw [Matrix.charpoly_map, h, Polynomial.prod_X_sub_C_nextCoeff, neg_neg] at h1
  rw [← h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem UpperTheory.V.Ws.P1.irrL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (x : W.Point K.r) (Q : PD T.ι (G T.F Ω) x.A), T.PsPair h x.K Q → K.IsRho x.ρ Q → Irr (mapRep (algebraMap x.A x.Fr) Q.r) →
          U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) := by
  intro Ω _ _ _ l hl c D T c' h K x Q hP hρ hI
  obtain ⟨hrange, -, -, hidx, hres, -⟩ := UpperTheory.V.Ws.P1.towerGal D T
  have hsurj := (UpperTheory.V.Ws.phiKer K.V).1
  have htow : ∀ a : c'.O, algebraMap (ResidueField c'.O) x.K (residue c'.O a) = algebraMap c'.O x.K a :=
    fun a => (IsScalarTower.algebraMap_apply c'.O (ResidueField c'.O) x.K a).symm
  have hinj : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective x.A x.Fr
  have h2 : (2 : x.Fr) ≠ 0 := by
    haveI := (UpperTheory.V.Ws.P1.coefRes c').2.1
    intro h0
    have h1 : (2 : x.A) = 0 := hinj (by rw [map_ofNat, map_zero]; exact h0)
    have h3 : (2 : x.K) = 0 := by
      have := congrArg (PowerSeries.constantCoeff : PowerSeries x.K →+* x.K) h1
      rwa [map_ofNat, map_zero] at this
    have h4 : ((2 : ℕ) : ResidueField c'.O) = 0 :=
      (algebraMap (ResidueField c'.O) x.K).injective (by rw [map_natCast, map_zero]; exact_mod_cast h3)
    exact K.s.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff _ l 2).1 h4))
  let χ : Fin (3 + 1) → G T.F Ω →* x.Kˣ := fun i =>
    W.pushCh ((algebraMap c'.O x.K).comp (inc h)) ((chi D T.pr i).comp (resQ T.F))
  have hχ : Function.Injective fun i => (χ i).comp T.GalL.subtype := by
    intro i j hij
    refine K.r.chib_inj (MonoidHom.ext fun y => ?_)
    obtain ⟨g, rfl⟩ := hsurj y
    have hg : resLe T.F_le g ∈ T.GalL := hrange ▸ ⟨g, rfl⟩
    have e : algebraMap c'.O x.K (inc h (chi D T.pr i (resQ T.L g))) =
        algebraMap c'.O x.K (inc h (chi D T.pr j (resQ T.L g))) := by
      have e1 := congrArg Units.val (DFunLike.congr_fun hij ⟨_, hg⟩)
      rw [← (hres g).1]
      exact e1
    apply Units.ext
    apply (algebraMap (ResidueField c'.O) x.K).injective
    rw [K.chib, K.chib, htow, htow, map_mul, map_mul, e]
  have htr : T.GalL = ⊤ ∨ ∃ g, g ∉ T.GalL ∧ (mapRep (algebraMap x.A x.Fr) Q.r g).trace ≠ 0 := by
    refine (UpperTheory.V.Ws.P1.trNe T.GalL χ hχ).imp id fun ⟨g, hg, hs⟩ => ⟨g, hg, fun h0 => hs ?_⟩
    have e1 : (Q.r g).trace = 0 := hinj (by
      rw [map_zero, ← h0]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum])
    have e2 := trace_of_cp _ _ _ (hP.cp g)
    rw [e1, map_zero] at e2
    exact e2.symm
  have hM := UpperTheory.V.Ws.P1.irrTr (algebraMap x.Fr x.Fb) T.GalL _ h2 hI hidx htr
  intro U hW
  refine hM U fun y hy v hv => ?_
  rw [← hrange] at hy
  obtain ⟨g, rfl⟩ := hy
  have h5 := hW (K.V.pr g) trivial v hv
  let u : x.Fbˣ := Units.map (((algebraMap x.Fr x.Fb).comp ((algebraMap x.A x.Fr).comp (algebraMap c'.O x.A)) : c'.O →+* x.Fb) : c'.O →* x.Fb) (K.κ g)
  have e : W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF) (K.V.pr g) =
      (u : x.Fb) • mapRep (algebraMap x.Fr x.Fb) (mapRep (algebraMap x.A x.Fr) Q.r) (resLe T.F_le g) := by
    ext i j
    have e0 := congrFun (congrFun (hρ g) i) j
    show algebraMap x.Fr x.Fb (algebraMap x.A x.Fr (W.mat x.ρ (K.V.pr g) i j)) = _
    rw [e0, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
    rfl
  rw [e, Matrix.smul_mulVec] at h5
  exact (U.smul_mem_iff u.ne_zero).1 h5
