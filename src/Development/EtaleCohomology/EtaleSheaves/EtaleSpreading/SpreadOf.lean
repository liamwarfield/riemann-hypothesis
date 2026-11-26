module

public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.FPProof
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.LiftPolys
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreadsOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreads
noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf

def EtSpreads : Prop := MorphismProperty.PreIndSpreads.{0} Et

theorem Spread_of (hE : EtSpreads) : LateralTheory.E.DescendPf.Spread := by
  intro A O f hf C _ _ _
  obtain ⟨J, _, _, D, t, s, hc, hJ⟩ := hf
  have hC : Et (CommRingCat.ofHom (algebraMap O C) : O ⟶ CommRingCat.of C) := by
    change (algebraMap O C).Etale
    exact RingHom.etale_algebraMap.mpr inferInstance
  obtain ⟨j, T', f', g', hP, hf'⟩ := hE.exists_isPushout hc _ hC
  exact ⟨D.obj j, t.app j, s.app j, T', f', g'.hom, (hJ j).1, hf', (hJ j).2, hP.flip⟩

end LateralTheory.E.SpreadPf
end
end

noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.SpreadPf.Cut

def FP : MorphismProperty CommRingCat.{0} := fun _ _ f => f.hom.FinitePresentation

def FPSpreads : Prop := MorphismProperty.PreIndSpreads.{0} FP

def EtStage : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
  (_ : IsColimit c) (j : J) {T' T : CommRingCat.{0}} (f' : D.obj j ⟶ T') (f : c.pt ⟶ T) (g : T' ⟶ T),
  FP f' → IsPushout (c.ι.app j) f' f g → Et f →
  ∃ (k : J) (T'' : CommRingCat.{0}) (f'' : D.obj k ⟶ T'') (g'' : T'' ⟶ T),
    IsPushout (c.ι.app k) f'' f g'' ∧ Et f''

theorem EtSpreads_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.SpreadPf.EtSpreads where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    have hfp : FP f := by
      change f.hom.FinitePresentation
      let := f.hom.toAlgebra
      have h : Algebra.Etale c.pt T := hf
      exact h.finitePresentation
    obtain ⟨j, T', f', g, hP, hf'⟩ := hF.exists_isPushout hc f hfp
    exact hS hc j f' f g hf' hP hf

theorem Spread_of (hF : FPSpreads) (hS : EtStage) : LateralTheory.E.DescendPf.Spread :=
  LateralTheory.E.SpreadPf.Spread_of (EtSpreads_of hF hS)

end LateralTheory.E.SpreadPf.Cut
end
end

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SpreadPf.Lift

variable {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}

theorem lift_elem (hc : IsColimit c) (a : c.pt) : ∃ (j : J) (x : D.obj j), c.ι.app j x = a := by
  have hc' := isColimitOfPreserves (forget CommRingCat.{0}) hc
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc' a
  exact ⟨j, x, hx⟩

theorem map_ι_map {σ : Type} {j k : J} (u : j ⟶ k) (q : MvPolynomial σ (D.obj j)) :
    MvPolynomial.map (c.ι.app k).hom (MvPolynomial.map (D.map u).hom q) = MvPolynomial.map (c.ι.app j).hom q := by
  rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, c.w]

theorem lift_poly (hc : IsColimit c) {σ : Type} (p : MvPolynomial σ c.pt) :
    ∃ (j : J) (q : MvPolynomial σ (D.obj j)), MvPolynomial.map (c.ι.app j).hom q = p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨j, x, hx⟩ := lift_elem hc a
    exact ⟨j, MvPolynomial.C x, by simp [hx]⟩
  | add p q hp hq =>
    obtain ⟨j₁, q₁, h₁⟩ := hp
    obtain ⟨j₂, q₂, h₂⟩ := hq
    refine ⟨IsFiltered.max j₁ j₂, MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom q₁ +
      MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂, ?_⟩
    rw [map_add (f := _), map_ι_map, map_ι_map, h₁, h₂]
  | mul_X p i hp =>
    obtain ⟨j, q, h⟩ := hp
    exact ⟨j, q * MvPolynomial.X i, by simp [h]⟩

theorem lift_polys (hc : IsColimit c) {σ : Type} : ∀ (m : ℕ) (p : Fin m → MvPolynomial σ c.pt),
    ∃ (j : J) (q : Fin m → MvPolynomial σ (D.obj j)), ∀ i, MvPolynomial.map (c.ι.app j).hom (q i) = p i := by
  intro m
  induction m with
  | zero =>
    intro p
    exact ⟨IsFiltered.nonempty.some, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro p
    obtain ⟨j₁, q₁, h₁⟩ := ih (fun i => p i.succ)
    obtain ⟨j₂, q₂, h₂⟩ := lift_poly hc (p 0)
    refine ⟨IsFiltered.max j₁ j₂, Fin.cons (MvPolynomial.map (D.map (IsFiltered.rightToMax j₁ j₂)).hom q₂)
      (fun i => MvPolynomial.map (D.map (IsFiltered.leftToMax j₁ j₂)).hom (q₁ i)), ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; rw [map_ι_map, h₂]
    · simp only [Fin.cons_succ]; rw [map_ι_map, h₁]

end LateralTheory.E.SpreadPf.Lift
end
end

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SpreadPf.FPProof

theorem finite_presentation_ring_maps_pre_ind_spread : LateralTheory.E.SpreadPf.Cut.FPSpreads where
  exists_isPushout {J} _ _ {D} {c} hc {T} f hf := by
    classical
    let _ := f.hom.toAlgebra
    obtain ⟨n, π, hπ, hker⟩ := (hf : Algebra.FinitePresentation c.pt T).out
    obtain ⟨s, hs⟩ := hker
    let p : Fin s.card → MvPolynomial (Fin n) c.pt := fun i => (s.equivFin.symm i).1
    obtain ⟨j, q, hq⟩ := LateralTheory.E.SpreadPf.Lift.lift_polys hc s.card p
    let I : Ideal (MvPolynomial (Fin n) (D.obj j)) := Ideal.span (Set.range q)
    have hpker : ∀ i, π (p i) = 0 := by
      intro i
      have : p i ∈ RingHom.ker π.toRingHom := by
        rw [← hs]; exact Ideal.subset_span (s.equivFin.symm i).2
      simpa using this
    let φ : MvPolynomial (Fin n) (D.obj j) →+* T := π.toRingHom.comp (MvPolynomial.map (c.ι.app j).hom)
    have hφ : ∀ a ∈ I, φ a = 0 := by
      intro a ha
      have : I ≤ RingHom.ker φ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp [φ, hq i, hpker i]
      simpa using this ha
    let T' : CommRingCat.{0} := CommRingCat.of (MvPolynomial (Fin n) (D.obj j) ⧸ I)
    let f' : D.obj j ⟶ T' := CommRingCat.ofHom ((Ideal.Quotient.mk I).comp MvPolynomial.C)
    let g : T' ⟶ T := CommRingCat.ofHom (Ideal.Quotient.lift I φ hφ)
    have hfa : ∀ a : c.pt, f a = π (MvPolynomial.C a) := fun a => (π.commutes a).symm
    have hw : c.ι.app j ≫ f = f' ≫ g := by
      ext x
      change f.hom (c.ι.app j x) = Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.C x))
      rw [Ideal.Quotient.lift_mk, hfa]
      simp [φ]
    have hfp : LateralTheory.E.SpreadPf.Cut.FP f' := by
      have hI : I.FG := ⟨(Set.finite_range q).toFinset, by simp [I]⟩
      have : Algebra.FinitePresentation (D.obj j) (MvPolynomial (Fin n) (D.obj j) ⧸ I) :=
        Algebra.FinitePresentation.quotient hI
      exact RingHom.finitePresentation_algebraMap.mpr this
    refine ⟨j, T', f', g, IsPushout.of_isColimit (c := PushoutCocone.mk f g hw) ?_, hfp⟩
    let e := Ideal.quotientKerAlgEquivOfSurjective hπ
    have he : ∀ y, e.symm (π y) = Ideal.Quotient.mk _ y := fun y => by
      rw [AlgEquiv.symm_apply_eq]; rfl
    let Ψ : ∀ S : PushoutCocone (c.ι.app j) f', MvPolynomial (Fin n) c.pt →+* S.pt := fun S =>
      MvPolynomial.eval₂Hom S.inl.hom (fun i => S.inr (Ideal.Quotient.mk I (MvPolynomial.X i)))
    have key : ∀ S : PushoutCocone (c.ι.app j) f',
        (Ψ S).comp (MvPolynomial.map (c.ι.app j).hom) = S.inr.hom.comp (Ideal.Quotient.mk I) := by
      intro S
      apply MvPolynomial.ringHom_ext
      · intro x
        have := congrArg (fun h => h.hom x) S.condition
        simpa [Ψ, f'] using this
      · intro i
        simp [Ψ]
    have hΨ : ∀ S : PushoutCocone (c.ι.app j) f', ∀ a ∈ RingHom.ker π, Ψ S a = 0 := by
      intro S a ha
      have : RingHom.ker π.toRingHom ≤ RingHom.ker (Ψ S) := by
        rw [← hs, Ideal.span_le]
        intro x hx
        have hx' : x = p (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s})) := by simp [p]
        rw [SetLike.mem_coe, RingHom.mem_ker, hx', ← hq, ← RingHom.comp_apply, key S]
        simp only [RingHom.coe_comp, Function.comp_apply]
        have hmem : q (s.equivFin (⟨x, Finset.mem_coe.mp hx⟩ : {y // y ∈ s})) ∈ I :=
          Ideal.subset_span (Set.mem_range_self _)
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
      exact this (RingHom.mem_ker.mpr (by simpa using RingHom.mem_ker.mp ha))
    let desc : ∀ S : PushoutCocone (c.ι.app j) f', T ⟶ S.pt := fun S =>
      CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker π) (Ψ S) (hΨ S)).comp e.symm.toRingHom)
    have hdesc : ∀ S y, desc S (π y) = Ψ S y := by
      intro S y
      change Ideal.Quotient.lift _ (Ψ S) (hΨ S) (e.symm (π y)) = _
      rw [he, Ideal.Quotient.lift_mk]
    refine PushoutCocone.IsColimit.mk _ desc ?_ ?_ ?_
    · intro S
      ext a
      change desc S (f.hom a) = S.inl a
      rw [hfa, hdesc]
      simp [Ψ]
    · intro S
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_))
      change desc S (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I y)) = S.inr (Ideal.Quotient.mk I y)
      rw [Ideal.Quotient.lift_mk]
      change desc S (π _) = _
      rw [hdesc, ← RingHom.comp_apply, key S]
      rfl
    · intro S m h1 h2
      ext t
      obtain ⟨y, rfl⟩ := hπ t
      rw [show (desc S).hom (π y) = Ψ S y from hdesc S y]
      have : m.hom.comp π.toRingHom = Ψ S := by
        apply MvPolynomial.ringHom_ext
        · intro a
          have := congrArg (fun h => h.hom a) h1
          simpa [Ψ, hfa] using this
        · intro i
          have := congrArg (fun h => h.hom (Ideal.Quotient.mk I (MvPolynomial.X i))) h2
          change m.hom (Ideal.Quotient.lift I φ hφ (Ideal.Quotient.mk I (MvPolynomial.X i))) =
            S.inr.hom (Ideal.Quotient.mk I (MvPolynomial.X i)) at this
          rw [Ideal.Quotient.lift_mk] at this
          simpa [Ψ, φ] using this
      exact congrArg (fun h => h y) this

end LateralTheory.E.SpreadPf.FPProof
end
end

namespace LateralTheory.E.SpreadPf.Main

theorem Spread_of (hS : LateralTheory.E.SpreadPf.Cut.EtStage) : LateralTheory.E.DescendPf.Spread :=
  LateralTheory.E.SpreadPf.Cut.Spread_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread hS

end LateralTheory.E.SpreadPf.Main
