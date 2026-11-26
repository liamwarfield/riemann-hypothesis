module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalInv

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr0B
noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


set_option maxHeartbeats 2000000 in
theorem locTr0_B (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : ↥(H0 (ρ.comp (locFam S Av v))) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0)
    (hE : ∀ (z : ↥(H0 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0),
      (∀ s, cochainOf _ (cocycleι _ 0 x) s = d.eM z.1) → E z = cohomologyπ _ 0 x)
    (E' : H2 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2)
    (hE' : ∀ (z : ↥(Z2 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
      (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eD (z.1 (d.ev v (s 0), d.ev v (s 1)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 2 x)
    (a : ↥(H0 (ρ.comp (locFam S Av v)))) (b : H2 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH0H2TwistedDual μ ρ (locFam S Av v) a b)) =
      - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 0 + 2 = 2) (E a) (E' b)) := by
  classical
  induction b using Submodule.Quotient.induction_on with
  | H z => ?_
  have hc1 : Continuous (d.ev v).toMonoidHom := (d.hev_cont v).1
  have heA := hloc2 ρ (locFam S Av v) (d.ev v) (fun g => d.e g) d.A d.eM d.hM (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have heB := hloc2 (twDual μ ρ) (locFam S Av v) (d.ev v) (fun g => d.e g)
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have hbμ : ∀ (x : M) (y : TDual (ZMod (l ^ r)) M),
      ((((Additive.toMul ((ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩).hom
          (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
        ζ ^ (evalPair x y).val := fun x y => d.hDζ y x
  have hJ : ∀ (W : ↥(Z2 ((charRep μ).comp (locFam S Av v))))
      (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) 2),
      (∀ s, ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
          ζ ^ (W.1 (d.ev v (s 0), d.ev v (s 1))).val) →
      ((zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom) (Submodule.Quotient.mk W) =
        - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cohomologyπ _ 2 x) := fun W x h =>
    @invCmp Kf ‹_› ‹_› (S : Set (HeightOneSpectrum (𝓞 Kf.1))) inferInstance l r ‹_› hr (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ
      inv hinv d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ (Av v) (hAv v) (d.ev v) (d.hιs v) (d.hev_cont v).1
      (cocycles2Map ((charRep μ).comp (locFam S Av v)) (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  exact transfer_cup_degree_zero_two (d.ev v) hc1 (ρ.comp (locFam S Av v)) ((twDual μ ρ).comp (locFam S Av v))
    ((charRep μ).comp (locFam S Av v)) evalPair continuous_of_discreteTopology
    (fun g x y => evalPair_equiv μ ρ (locFam S Av v g) x y)
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) d.eM d.eD heA heB
    (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩)
    (fun c y => ((((Additive.toMul y :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ ^ c.val)
    hbμ E hE E' hE' _ _ hJ a z

end PositivityTheory.Lit1.PTN
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr1C
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.RestrictionSquareDegreeOne
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem cupPairing_swap_degree_one {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {A B C : Rep.{0} (ULift.{0} ℤ) Γ} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (μ : A ⊗ B ⟶ C) (x : cohomology A 1) (y : cohomology B 1) :
    cupPairing μ (rfl : 1 + 1 = 2) x y = - cupPairing ((β_ B A).hom ≫ μ) (rfl : 1 + 1 = 2) y x := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp, ConcreteCategory.comp_apply,
    cohomologyMap_braiding_cup (rfl : 1 + 1 = 2) (rfl : 1 + 1 = 2) y x]
  have h1 : ((-1 : ULift.{0} ℤ) ^ (1 * 1)) = -1 := by simp
  rw [h1, neg_one_smul, map_neg, neg_neg]

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_one_one {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z1 rho)) (z' : ↥(Z1 rho')) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z')) =
      - J (cupPairing μ (rfl : 1 + 1 = 2) (E (Submodule.Quotient.mk z)) (E' (Submodule.Quotient.mk z'))) := by
  obtain ⟨e1, he1a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x, hx⟩ := he1a (restrictCocycles1 rho ev.toMonoidHom hevc z)
  obtain ⟨e1', he1b, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 Hv R M' (rho'.comp ev.toMonoidHom) B eB heB
  obtain ⟨x', hx'⟩ := he1b (restrictCocycles1 rho' ev.toMonoidHom hevc z')
  have hEa : E (Submodule.Quotient.mk z) = cohomologyπ A 1 x := hE z x (fun s => hx s)
  have hEb : E' (Submodule.Quotient.mk z') = cohomologyπ B 1 x' := hE' z' x' (fun s => hx' s)
  have hcup : cupProductH1H1 rho rho' rhoP b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.Quotient.mk (cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z') := rfl
  rw [hEa, hEb, cupPairing_cohomologyπ, hcup]
  refine hJ _ _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx']
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  have := hbμ (z.1 (ev (s 0))) (rho' (ev (s 0)) (z'.1 (ev (s 1))))
  rw [heB] at this
  exact this

theorem transfer_cup_one_one_general {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] [CompactSpace Hv]
    [TotallyDisconnectedSpace Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ' : B ⊗ A ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ y x, rel (b x y) (μ'.hom (eB y ⊗ₜ[ULift.{0} ℤ] eA x)))
    (E : H1 rho ≃+ cohomology A 1)
    (hE : ∀ (z : ↥(Z1 rho)) (x : cocycles A 1),
      (∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (ev (s 0)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 1 x)
    (E' : H1 rho' ≃+ cohomology B 1)
    (hE' : ∀ (z : ↥(Z1 rho')) (x : cocycles B 1),
      (∀ s, cochainOf B (cocycleι B 1 x) s = eB (z.1 (ev (s 0)))) →
        E' (Submodule.Quotient.mk z) = cohomologyπ B 1 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (a : H1 rho') (b' : H1 rho) :
    jp (cupProductH1H1 rho rho' rhoP b hb hbe hc b' a) = J (cupPairing μ' (rfl : 1 + 1 = 2) (E' a) (E b')) := by
  induction a using Submodule.Quotient.induction_on with
  | H z' => ?_
  induction b' using Submodule.Quotient.induction_on with
  | H z => ?_
  have hbμ' : ∀ x y, rel (b x y) (((β_ A B).hom ≫ μ').hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)) :=
    fun x y => hbμ y x
  rw [cupPairing_swap_degree_one μ', map_neg,
    transfer_cup_degree_one_one ev hevc rho rho' rhoP b hb hbe hc A B C eA eB heA heB ((β_ A B).hom ≫ μ') rel hbμ'
      E hE E' hE' jp J hJ z z']

end PositivityTheory.Lit1.PTN
end
end

noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


set_option maxHeartbeats 2000000 in
theorem locTr1_C (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H1 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1)
    (hE : ∀ (z : ↥(Z1 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eM (z.1 (d.ev v (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (E' : H1 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1)
    (hE' : ∀ (z : ↥(Z1 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
      (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eD (z.1 (d.ev v (s 0)))) → E' (Submodule.Quotient.mk z) = cohomologyπ _ 1 x)
    (a : H1 (ρ.comp (locFam S Av v))) (b : H1 ((twDual μ ρ).comp (locFam S Av v))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v)) b a)) =
      gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 1 + 1 = 2) (E a) (E' b)) := by
  classical
  have hc1 : Continuous (d.ev v).toMonoidHom := (d.hev_cont v).1
  have heM := hloc2 ρ (locFam S Av v) (d.ev v) (fun g => d.e g) d.A d.eM d.hM (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have heD := hloc2 (twDual μ ρ) (locFam S Av v) (d.ev v) (fun g => d.e g)
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have hbμ : ∀ (x : M) (y : TDual (ZMod (l ^ r)) M),
      ((((Additive.toMul ((ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩).hom
          (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
        ζ ^ (evalPair x y).val := fun x y => d.hDζ y x
  have hJ : ∀ (W : ↥(Z2 ((charRep μ).comp (locFam S Av v))))
      (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) 2),
      (∀ s, ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
          ζ ^ (W.1 (d.ev v (s 0), d.ev v (s 1))).val) →
      ((zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom) (Submodule.Quotient.mk W) =
        - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cohomologyπ _ 2 x) := fun W x h =>
    @invCmp Kf ‹_› ‹_› (S : Set (HeightOneSpectrum (𝓞 Kf.1))) inferInstance l r ‹_› hr (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ
      inv hinv d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ (Av v) (hAv v) (d.ev v) (d.hιs v) (d.hev_cont v).1
      (cocycles2Map ((charRep μ).comp (locFam S Av v)) (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  exact transfer_cup_one_one_general (d.ev v) hc1 ((twDual μ ρ).comp (locFam S Av v)) (ρ.comp (locFam S Av v))
    ((charRep μ).comp (locFam S Av v)) evalPair.flip continuous_of_discreteTopology
    (fun g y x => evalPair_equiv μ ρ (locFam S Av v g) x y) (hρ.comp' (continuous_locFam S Av v))
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A)
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) d.eD d.eM heD heM
    (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩)
    (fun c y => ((((Additive.toMul y :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ ^ c.val)
    hbμ E' hE' E hE _ _ hJ a b

end PositivityTheory.Lit1.PTN
end
end
