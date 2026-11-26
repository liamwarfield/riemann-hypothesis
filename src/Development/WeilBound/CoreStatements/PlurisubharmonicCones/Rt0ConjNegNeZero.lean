module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemSpan

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisation
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisation
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_comp_eq {h : GenFrEx Xo c} {Z : Comp Xo c} (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] Om Z)
    (z : FrPt Xo c (Om Z)) (t : Ix Dw → (Om Z)ˣ) (hz : FrMap ψ C.y z) (ht : FrBor t z (genFr h Z)) :
    C.Z = Z := by
  by_contra hne
  let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
  rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have he : spMap C.R.val.toRingHom sC = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
    rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
      Scheme.Hom.comp_apply, he] at hgen
    exact hgen
  have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
    (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
    (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη

attribute [local instance 1100] Subalgebra.algebra in
theorem comp_eq_of_algClosedAt (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
    (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
    (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
    (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
    (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ),
      FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
  have hCZ : C.Z = Z := chart_comp_eq C ψ z t hz ht
  have : Algebra.Smooth c.F C.R := C.sm
  have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
      (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
      ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
    rintro k x ⟨φ, y', t', hy', ht'⟩
    obtain ⟨w, hw⟩ := hL.bc _ _ φ z
    exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
      hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
  obtain ⟨f, hf⟩ := hread k x hk
  obtain ⟨f', hf'⟩ := hread k' x' hk'
  refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
  have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
    rw [hCZ]; exact hac
  exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ

end GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp

theorem GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.CompanionTheory.Ar.Rec.PeriodComp.comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Comp Xo c) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), 1 ≤ r → IsUnf U → (∀ b : Om Z, IsAlgebraic c.F b → b ∈ (algebraMap c.F (Om Z)).range) → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → (Set.range y ⊆ (Z : Set (Xo.XF c)) ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) := by
  intro E _ _ _ H D l Xo c Z r U h1 hU hac
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨-, -, hcov, -, -, g, e, F, ik, φ, hEF, hP⟩ := id hU
  have hty : IsTypeFn H D.p D.q (fun j => relab c c.F.val.toRingHom (e j).1) :=
    (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 D g e
  have hinj := (GlobalTheory.CompBij.ik_bijective E H D l Xo c _ r U h1 hσ hU g e F ik φ hEF
    fun k x => (hP k x).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩).1
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
  choose q hq using GlobalTheory.UnifComp.exists_liesOn (Formalism.L2.PjFree.Unf.ofPj U) hU
  obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model (Formalism.L2.PjFree.Unf.ofPj U) hU hG Z
  have hqk : q k = Z := GlobalTheory.UnifComp.eq_of_carries hk (hq k)
  have comp_eq_of_algClosedAt {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (h : GenFrEx Xo c)
      (Z : Comp Xo c) (hac : ∀ a : Om Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range)
      (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom)
      (hk : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y')
      (hk' : ∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k' x') y') : k = k' := by
    obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c
    obtain ⟨-, hmul, hinv, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
    obtain ⟨C, ψ, z, t, hz, ht⟩ := hA h (Om Z) (genFr h Z)
    let : Algebra c.F C.R := C.R.algebra
    have hCZ : C.Z = Z := by
      by_contra hne
      let s₀ : Sp (Om Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om Z))
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c C.Z Z hne) ?_ (GlobalTheory.AllWt.liesOn_genFr h Z s₀)
      rw [GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap hz, Scheme.Hom.comp_apply]
      let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
      let sC : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
      have he : spMap C.R.val.toRingHom sC = η :=
        PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
      have hη : GlobalTheory.AllWt.ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
        have hgen := GlobalTheory.AllWt.liesOn_genFr h C.Z sC
        rw [← GlobalTheory.UnifComp.ptF_frBor C.bor, GlobalTheory.UnifComp.ptF_frMap C.gen,
          Scheme.Hom.comp_apply, he] at hgen
        exact hgen
      have hspec : η ⤳ spMap ψ.toRingHom s₀ :=
        (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
      exact (hspec.map (GlobalTheory.AllWt.ptF C.y).continuous).mem_closed
        (isClosed_of_mem_irreducibleComponents _ C.Z.2) hη
    have : Algebra.Smooth c.F C.R := C.sm
    have hread : ∀ (k : U.Comp) (x : (U.X k).dom), (∃ (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ))
        (t : Ix D → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y') →
        ∃ f : C.R → ℂ, GlobalTheory.GeomConn.ReadOn (Formalism.L2.PjFree.Unf.ofPj U) C.y f k := by
      rintro k x ⟨φ, y', t', hy', ht'⟩
      obtain ⟨w, hw⟩ := hL.bc _ _ φ z
      exact ⟨_, φ.comp ψ, w, x, _, fun _ => rfl, PullbackSections.frMap_trans _ _ hz hw,
        hmul _ _ _ _ _ ht' (hinv _ _ _ (GlobalTheory.SupGeneric.frBor_of_frMap φ ht hw hy'))⟩
    obtain ⟨f, hf⟩ := hread k x hk
    obtain ⟨f', hf'⟩ := hread k' x' hk'
    refine GlobalTheory.GeomConn.ReadOn.eq_of_isPreconnected (U := Formalism.L2.PjFree.Unf.ofPj U) hσ hU ?_ hf hf'
    have hac' : ∀ a : Om C.Z, IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om C.Z)).range := by
      rw [hCZ]; exact hac
    exact GlobalTheory.GeomConn.isPreconnected_points_over C.R.val Subtype.val_injective hac' σ
  have huniq : ∀ k', q k' = Z → k' = k := by
    intro k' hk'
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp (Formalism.L2.PjFree.Unf.ofPj U) hσ hU hG k'
    obtain rfl : Z' = Z := (GlobalTheory.UnifComp.eq_of_carries hZ' (hq k')).symm.trans hk'
    obtain ⟨P, w, x, t, hw, ht⟩ := hk
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact comp_eq_of_algClosedAt U hσ hU hG Z' hac k' k x' x
      ⟨P', w', t', hw', ht'⟩ ⟨P, w, t, hw, ht⟩
  have hfr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      ∃ (k' : U.Comp) (x : (U.X k').dom) (t : Ix D → (CAt c.F.val.toRingHom)ˣ)
        (z : FrPt Xo c (CAt c.F.val.toRingHom)),
        FrBor t (U.un k' x) z ∧ z.x = under y ∧ GlobalTheory.AllWt.ptF z = y := by
    intro y hy
    have hover : under y ≫ Xo.s = sOf c ℂ := by
      show (y ≫ pullback.fst _ _) ≫ Xo.s = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, sOf, ← Spec.map_comp]
      rfl
    obtain ⟨z, hz⟩ := Formalism.L2.Pj.exists_frPt_local (Xo := Xo) (c := c) (L := ℂ)
      GlobalTheory.firstFiveLaws.2.1.secTwist (under y) hover
    obtain ⟨k', x, t, hb⟩ := hcov z
    refine ⟨k', x, t, z, hb, hz, ?_⟩
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact (pullback.lift_snd _ _ _).trans hy.symm
  refine ⟨g, _, F, ik k, hty, fun y hy => ⟨fun hZ => ?_, fun ⟨P, hP', hPy⟩ => ?_⟩⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    have hk' : q k' = Z := by
      by_contra hne
      let s₀ : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
      refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c _ _ hne) ?_ (hZ ⟨s₀, rfl⟩)
      have := hq k' x s₀
      change GlobalTheory.AllWt.ptF (U.un k' x) s₀ ∈ _ at this
      rwa [← GlobalTheory.UnifComp.ptF_frBor hb, hzy] at this
    obtain rfl := huniq k' hk'
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    exact ⟨Pm, hPm, hzx.symm.trans (hb.1.trans hx)⟩
  · obtain ⟨k', x, t, z, hb, hzx, hzy⟩ := hfr y hy
    obtain ⟨Pm, -, hPm, hx, -⟩ := hP k' x
    have e1 : ik k' = ik k := F.disj _ _ Pm P hPm hP' (hx.symm.trans (hb.1.symm.trans (hzx.trans hPy)))
    obtain rfl := hinj e1
    rintro _ ⟨s, rfl⟩
    rw [← hqk, ← hzy, GlobalTheory.UnifComp.ptF_frBor hb]
    exact hq k' x s
end
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LogOmBound
open NumberField GlobalTheory.CompanionTheory.Ar

namespace LevelTowerAlt

theorem logOm_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), ∃ (_ : NeZero H.d) (χ : DirichletCharacter ℂ H.d),
      GlobalTheory.IsKroneckerChar χ ∧ |(GlobalTheory.CM.logOm E χ).re| ≤ C * (1 + Real.log (hostRd E) + |hostLval H|) := by
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  refine ⟨1 + Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|, by positivity, ?_⟩
  intro E _ _ _ H
  haveI : Fact (Nat.Prime H.d) := ⟨H.d_prime⟩
  refine ⟨⟨H.d_prime.ne_zero⟩, (quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ),
    GlobalTheory.isKroneckerChar_quadraticChar (by have := H.d_mod; omega), ?_⟩
  have hL : (GlobalTheory.CM.logOm E ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ))).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) - hostLval H := by
    simp only [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]
    rfl
  have hrd : rootDiscr E = hostRd E := by
    unfold hostRd
    rw [NumberField.rootDiscr_def, Int.cast_abs, one_div]
  have h1 : 1 ≤ hostRd E := by
    unfold hostRd
    apply Real.one_le_rpow
    · have := Int.one_le_abs (NumberField.discr_ne_zero E)
      rw [← Int.cast_abs]
      exact_mod_cast this
    · positivity
  have hb0 : 0 ≤ Real.log (hostRd E) := Real.log_nonneg h1
  have hlogdiv : Real.log (2 * Real.pi / rootDiscr E) = Real.log (2 * Real.pi) - Real.log (hostRd E) := by
    rw [hrd, Real.log_div (by positivity) (by linarith)]
  rw [hL, hlogdiv]
  have ha1 := le_abs_self (Real.log (2 * Real.pi))
  have ha2 := neg_abs_le (Real.log (2 * Real.pi))
  have hl1 := le_abs_self (hostLval H)
  have hl2 := neg_abs_le (hostLval H)
  have hb : |Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log (hostRd E)) - hostLval H| ≤
      Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)| + Real.log (hostRd E) + |hostLval H| :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have hm : 0 ≤ (Real.eulerMascheroniConstant + |Real.log (2 * Real.pi)|) *
      (Real.log (hostRd E) + |hostLval H|) := by positivity
  nlinarith

end LevelTowerAlt
end

section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCoordLattice
noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

section Local

variable {L : Type} [Field L] [NumberField L]

theorem exists_max_det {n : ℕ} (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hD : detIdeal E ≠ ⊥) (p : Nat.Primes)
    (j : L →+* ℂ_[p]) :
    ∃ (v : Fin n → Fin n → 𝓞 L) (u : 𝓞 L), (∀ i, v i ∈ E) ∧ (Matrix.of v).det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) = Real.log ‖j (((Matrix.of v).det : 𝓞 L) : L)‖ ∧
      ‖j (u : L)‖ = 1 ∧ ∀ w ∈ E, ∃ t : Fin n → 𝓞 L, u • w = ∑ k, t k • v k := by
  classical
  have hj'inj : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  obtain ⟨V, -, hV, hVO, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring L p j
  have hle1 : ∀ r : 𝓞 L, ‖(j.comp (algebraMap (𝓞 L) L)) r‖ ≤ 1 := fun r => (hV _).2 (hVO r)
  obtain ⟨a, haI, ha0, hamax, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ (detIdeal E) hj'inj hD
  have hapos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    norm_pos_iff.2 (fun h => ha0 (hj'inj (by rw [h, map_zero])))
  obtain ⟨v, hvE, hv⟩ : ∃ v : Fin n → Fin n → 𝓞 L, (∀ i, v i ∈ E) ∧
      ‖(j.comp (algebraMap (𝓞 L) L)) a‖ ≤ ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ x ∈ detIdeal E, ‖(j.comp (algebraMap (𝓞 L) L)) x‖ < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        exact hcon v hv
      | zero => simpa using hapos
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hle1 r)) hx
    exact lt_irrefl _ (hall a haI)
  have hdI : (Matrix.of v).det ∈ detIdeal E := det_mem_detIdeal E v hvE
  have hdeq : ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ = ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    le_antisymm (hamax _ hdI) hv
  have hd0 : (Matrix.of v).det ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hdeq
    linarith
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hdI)
  have hspan0 : Ideal.span {(Matrix.of v).det} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  obtain ⟨hmul, hsing, -⟩ := GlobalTheory.T.log_ideal_mul_span_map L p _ hj'inj
  have hJlog : logIdeal (j.comp (algebraMap (𝓞 L) L)) J = 0 := by
    have := hmul _ J hD hJ0
    rw [← hJ, hsing, hdeq, hlog] at this
    linarith
  obtain ⟨u, huJ, hu0, -, hulog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ J hj'inj hJ0
  have hu1 : ‖(j.comp (algebraMap (𝓞 L) L)) u‖ = 1 := by
    have hpos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) u‖ :=
      norm_pos_iff.2 (fun h => hu0 (hj'inj (by rw [h, map_zero])))
    rw [hJlog] at hulog
    rw [← Real.exp_log hpos, ← hulog, Real.exp_zero]
  refine ⟨v, u, hvE, hd0, ?_, hu1, ?_⟩
  · rw [hlog, ← hdeq]
    rfl
  · intro w hw
    have hc : ∀ k, u * (Matrix.of (Function.update v k w)).det ∈ Ideal.span {(Matrix.of v).det} := by
      intro k
      rw [hJ, mul_comm u]
      refine Ideal.mul_mem_mul (det_mem_detIdeal E _ fun i => ?_) huJ
      by_cases h : i = k
      · subst h
        simpa using hw
      · simpa [h] using hvE i
    choose t ht using fun k => Ideal.mem_span_singleton'.1 (hc k)
    refine ⟨t, ?_⟩
    have hcr := Matrix.mulVec_cramer (Matrix.transpose (Matrix.of v)) w
    have hcr_apply : ∀ k, Matrix.cramer (Matrix.transpose (Matrix.of v)) w k = (Matrix.of (Function.update v k w)).det := by
      intro k
      rw [Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
      rfl
    apply smul_right_injective (Fin n → 𝓞 L) hd0
    funext i
    have hi := congrFun hcr i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, hcr_apply,
      Matrix.det_transpose, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.mul_sum]
    calc (Matrix.of v).det * (u * w i) = u * ((Matrix.of v).det * w i) := by ring
      _ = u * ∑ k, v k i * (Matrix.of (Function.update v k w)).det := by rw [hi]
      _ = ∑ k, (Matrix.of v).det * (t k * v k i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        linear_combination (-(v k i)) * ht k

theorem exists_coord_lattice {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x)) :
    ∃ E : Submodule (𝓞 L) (Fin n → 𝓞 L), (∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) ∧ detIdeal E ≠ ⊥ ∧
      Ideal.absNorm (Ideal.span {c ^ n}) =
        (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup * Ideal.absNorm (detIdeal E) := by
  set Φ : (Fin n → 𝓞 L) →ₗ[𝓞 L] M := Fintype.linearCombination (𝓞 L) x with hΦ
  have hΦa : ∀ w, Φ w = ∑ k, w k • x k := fun w => Fintype.linearCombination_apply _ _ _
  have hΦi : Function.Injective Φ := by
    intro a b h
    have h' := Fintype.linearIndependent_iff.1 hli (a - b) (by
      rw [← hΦa, map_sub, h, sub_self])
    funext i
    exact sub_eq_zero.1 (h' i)
  have hrange : Submodule.span (𝓞 L) (Set.range x) = LinearMap.range Φ := by
    rw [hΦ, Fintype.range_linearCombination]
  set ψ : M →ₗ[𝓞 L] M := c • LinearMap.id with hψ
  have hψa : ∀ z, ψ z = c • z := fun z => rfl
  have hψi : Function.Injective ψ := by
    intro a b h
    rw [hψa, hψa] at h
    exact smul_right_injective M hc h
  set E : Submodule (𝓞 L) (Fin n → 𝓞 L) := (F.map ψ).comap Φ with hE
  have hmem : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k := by
    intro w
    simp only [hE, Submodule.mem_comap, Submodule.mem_map, hψa, hΦa]
  set A : Submodule (𝓞 L) (Fin n → 𝓞 L) :=
    LinearMap.range (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))).mulVecLin with hA
  have hAmem : ∀ w, w ∈ A ↔ ∃ v, c • v = w := by
    intro w
    simp [hA, Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAE : A ≤ E := by
    intro w hw
    obtain ⟨v, rfl⟩ := (hAmem w).1 hw
    rw [hmem]
    refine ⟨Φ v, ?_, ?_⟩
    · rw [hΦa]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)
    · rw [hΦa, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
  have hdet : detIdeal E ≠ ⊥ := by
    intro hb
    have h1 := det_mem_detIdeal E (fun i => c • Pi.single i (1 : 𝓞 L)) (fun i => hAE ((hAmem _).2 ⟨_, rfl⟩))
    rw [hb, Ideal.mem_bot] at h1
    have e1 : Matrix.of (fun i => c • Pi.single i (1 : 𝓞 L)) = c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact pow_ne_zero n hc h1
  refine ⟨E, hmem, hdet, ?_⟩
  have iA : A.toAddSubgroup.index = Ideal.absNorm (Ideal.span {c ^ n}) := by
    rw [Ideal.absNorm_span_singleton]
    have := card_quotient_mulVecLin (K := L) (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero n hc)
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  have iE : E.toAddSubgroup.index = Ideal.absNorm (detIdeal E) := card_quotient_eq_absNorm_detIdeal n E
  have m1 : A.toAddSubgroup.map Φ.toAddMonoidHom =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, rfl⟩ := (hAmem w).1 hw
      exact ⟨Φ v, by rw [hrange]; exact ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hrange] at hy
      obtain ⟨v, rfl⟩ := hy
      exact ⟨c • v, (hAmem _).2 ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
  have m2 : E.toAddSubgroup.map Φ.toAddMonoidHom = F.toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hw)
      exact ⟨y, hy, he⟩
    · rintro ⟨y, hy, rfl⟩
      have h2 := hF y hy
      rw [hrange] at h2
      obtain ⟨w, hw⟩ := h2
      refine ⟨w, ?_, by rw [hw, hψa]⟩
      exact Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨y, hy, by rw [hw, hψa]⟩)
  have hrel : A.toAddSubgroup.relIndex E.toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := Φ.toAddMonoidHom) _ _ hΦi, m1, m2,
      AddSubgroup.relIndex_map_map_of_injective _ _ hψi]
  rw [← iA, ← AddSubgroup.relIndex_mul_index (show A.toAddSubgroup ≤ E.toAddSubgroup from hAE), hrel, iE]

theorem exists_local_frame {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x))
    (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hE : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) (hD : detIdeal E ≠ ⊥)
    (p : Nat.Primes) (j : L →+* ℂ_[p]) :
    ∃ (y : Fin n → M) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)), (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
      (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
      (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) - logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) =
        Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨v, u, hvE, hdet, hlog, hu, hspan⟩ := exists_max_det E hD p j
  have hz : ∀ i, ∃ z ∈ F, c • z = ∑ k, v i k • x k := fun i => (hE (v i)).1 (hvE i)
  choose y hyF hy using hz
  have hinj : Function.Injective (fun z : M => c • z) := smul_right_injective M hc
  have key : ∀ z ∈ F, ∃ t : Fin n → 𝓞 L, u • z = ∑ k, t k • y k := by
    intro z hz
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 (hF z hz)
    have hwE : w ∈ E := (hE w).2 ⟨z, hz, hw.symm⟩
    obtain ⟨t, ht⟩ := hspan w hwE
    refine ⟨t, hinj ?_⟩
    have e1 : c • (u • z) = ∑ l, (u • w) l • x l := by
      rw [smul_comm, ← hw, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    have e2 : ∑ l, (u • w) l • x l = ∑ k, t k • (c • y k) := by
      rw [ht]
      simp only [hy, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_smul]
      exact Finset.sum_comm
    show c • (u • z) = c • ∑ k, t k • y k
    rw [e1, e2, Finset.smul_sum]
    simp only [smul_comm (t _) c]
  choose T0 hT using fun i => key (x i) (hx i)
  set T : Matrix (Fin n) (Fin n) (𝓞 L) := Matrix.of T0 with hTdef
  have hTV : T * Matrix.of v = (u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
    refine Matrix.ext fun i l => ?_
    have h0 := (Fintype.linearIndependent_iff.1 hli)
      (fun l => (T * Matrix.of v) i l - ((u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L))) i l) ?_ l
    · exact sub_eq_zero.1 h0
    · simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_smul, smul_smul]
      rw [sub_eq_zero, Finset.sum_comm]
      calc ∑ k, ∑ l, (T i k * v k l) • x l = ∑ k, T0 i k • (c • y k) := by
            simp only [hy, Finset.smul_sum, smul_smul, hTdef, Matrix.of_apply]
        _ = c • (u • x i) := by
            rw [hT i, Finset.smul_sum]
            simp only [smul_comm c]
        _ = (u * c) • x i := by rw [smul_smul, mul_comm]
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hdetT : T.det * (Matrix.of v).det = (u * c) ^ n := by
    rw [← Matrix.det_mul, hTV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hTne : T.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetT
    exact pow_ne_zero n (mul_ne_zero hu0 hc) hdetT.symm
  have hji : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  have hc' : logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) = Real.log ‖j ((c : L))‖ * n := by
    rw [(GlobalTheory.T.log_ideal_mul_span_map L p _ hji).2.1]
    simp [map_pow, norm_pow, Real.log_pow, mul_comm]
  have hnorm : ‖j (T.det : L)‖ * ‖j ((Matrix.of v).det : L)‖ = ‖j (c : L)‖ ^ n := by
    have := congrArg (fun a : 𝓞 L => ‖j (a : L)‖) hdetT
    simpa [map_pow, map_mul, norm_pow, norm_mul, hu] using this
  have hpos1 : ‖j (T.det : L)‖ ≠ 0 := by
    simpa using hTne
  have hpos2 : ‖j ((Matrix.of v).det : L)‖ ≠ 0 := by
    simpa using hdet
  refine ⟨y, u, T, hyF, ?_, fun z hz => ?_, hu, fun i => by simpa [hTdef] using hT i, hTne, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : Matrix.vecMul g (Matrix.of v) = 0 := by
      rw [Fintype.linearIndependent_iff] at hli
      funext l
      refine hli (Matrix.vecMul g (Matrix.of v)) ?_ l
      have := congrArg (fun z => c • z) hg
      simp only [Finset.smul_sum, smul_comm c (g _), hy, smul_zero, Finset.smul_sum, smul_smul] at this
      rw [Finset.sum_comm] at this
      simpa [Matrix.vecMul, dotProduct, Finset.sum_smul] using this
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet h1)
  · obtain ⟨t, ht⟩ := key z hz
    refine ⟨u, hu, ?_⟩
    rw [ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [hc', hlog]
    have := congrArg Real.log hnorm
    rw [Real.log_mul hpos1 hpos2, Real.log_pow] at this
    linarith

end Local

private theorem exists_logNorms_lemma {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} (x : Fin n → B.carrier) :
    Real.log (gramDet B.metric σ x) = Real.log ‖B.gramDet σ x‖ := by
  have heq : B.gramDet σ x = (Matrix.gram ℂ fun i => fibreVec B.metric σ (x i)).det := by
    unfold HermitianBundle.gramDet
    congr 1
  have hnn := (Matrix.posSemidef_gram ℂ (fun i => fibreVec B.metric σ (x i))).det_nonneg
  obtain ⟨r, hr, hz⟩ := RCLike.nonneg_iff_exists_ofReal.1 hnn
  unfold gramDet
  rw [heq, ← hz]
  simp [RCLike.norm_ofReal, abs_of_nonneg hr]

private theorem exists_logNorms_lemma_2 {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x) := by
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  let S := Submodule.span (𝓞 L) (Set.range s)
  have hF : Module.rank (𝓞 L) F = n := by
    rw [← hn, HermitianBundle.rank]
    exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm
  have hS : Module.rank (𝓞 L) S = n := by
    rw [rank_span hsli, Cardinal.mk_range_eq s hsli.injective, Cardinal.mk_fin]
  have hQ := rank_quotient_add_rank_of_isDomain S
  rw [hS, hF] at hQ
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 (𝓞 L) (F ⧸ S))
  rw [hk] at hQ
  have hk0 : k = 0 := by
    have : ((k + n : ℕ) : Cardinal) = (n : Cardinal) := by rw [Nat.cast_add]; exact hQ
    have := Nat.cast_injective this
    omega
  have hr : Module.rank (𝓞 L) (F ⧸ S) = 0 := by rw [hk, hk0, Nat.cast_zero]
  have htor := rank_eq_zero_iff.1 hr
  choose a ha0 hav using htor
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 L) (M := F ⧸ S)
  refine ⟨∏ i, a (g i), Finset.prod_ne_zero_iff.2 fun i _ => ha0 _, fun z hz => ?_⟩
  have key : ∀ q : F ⧸ S, (∏ i, a (g i)) • q = 0 := by
    intro q
    have hq : q ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun i => a (g i)) (Finset.mem_univ i)
      rw [hd, mul_comm, mul_smul, hav, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  have h1 := key (Submodule.Quotient.mk ⟨z, hz⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := F.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

theorem exists_logNorms {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ N : Fl.LogNorms L, N.IsAdelic ∧ N.deg = B.normDegree F ∧ (∀ σ, N.inf σ = Real.log ‖B.gramDet σ x‖ / 2) ∧
      ∀ (p : Nat.Primes) (j : L →+* ℂ_[p]), ∃ (y : Fin n → B.carrier) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)),
        (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
        (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
        (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧ N.fin p j = Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨c, hc, hF⟩ := exists_logNorms_lemma_2 B F x hx hli hn
  obtain ⟨E, hE, hD, hidx⟩ := exists_coord_lattice F x hx hli c hc hF
  have hcn : Ideal.span {c ^ n} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hc
  let N : Fl.LogNorms L := ⟨fun σ => Real.log ‖B.gramDet σ x‖ / 2,
    fun p j => logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)⟩
  set idx := (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup with hidx_def
  have hprod : Ideal.absNorm (Ideal.span {c ^ n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcn
  rw [hidx] at hprod
  have hi0 : idx ≠ 0 := left_ne_zero_of_mul hprod
  have hd0 : Ideal.absNorm (detIdeal E) ≠ 0 := right_ne_zero_of_mul hprod
  have hfs : N.finSum = fun p : Nat.Primes => Real.log ‖((idx : ℚ) : ℂ_[p])‖ := by
    funext p
    have e1 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hcn p
    have e2 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hD p
    have hne1 : ‖((idx : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hi0)
    have hne2 : ‖((Ideal.absNorm (detIdeal E) : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hd0)
    show ∑ j : L →+* ℂ_[p], (logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)) = _
    rw [Finset.sum_sub_distrib, e1, e2, hidx, Nat.cast_mul, norm_mul, Real.log_mul hne1 hne2, Rat.cast_natCast]
    ring
  have hpf := (GlobalTheory.T.rat_product_formula (idx : ℚ) (Nat.cast_ne_zero.2 hi0)).2
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  have hsub : (Submodule.span (𝓞 L) (Set.range s)).toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.addSubgroupOf F.toAddSubgroup := by
    ext ⟨z, hz⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simp only [Submodule.mem_toAddSubgroup,
      Submodule.mem_span_range_iff_exists_fun, Subtype.ext_iff, Submodule.coe_sum, Submodule.coe_smul, s]
  have hcard : Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range s)) = idx := by
    rw [hidx_def, AddSubgroup.relIndex, AddSubgroup.index, ← hsub]
    rfl
  have hdeg := HermitianBundle.degree_eq_of_linearIndependent B F hsli (by rw [Fintype.card_fin, hn])
  refine ⟨N, ?_, ?_, fun σ => rfl, fun p j => ?_⟩
  · refine ((GlobalTheory.T.logIdeal_support_finite L _ hcn).union (GlobalTheory.T.logIdeal_support_finite L _ hD)).subset ?_
    rintro p ⟨j, hj⟩
    by_contra hc'
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hc'
    exact hj (by show _ - _ = (0 : ℝ); rw [hc'.1, hc'.2, sub_zero])
  · unfold Fl.LogNorms.deg HermitianBundle.normDegree
    rw [hfs, hdeg, hcard]
    simp only [exists_logNorms_lemma]
    have hq : ‖((idx : ℚ) : ℂ)‖ = (idx : ℝ) := by simp
    rw [hq] at hpf
    have hsum : ∑ σ : L →+* ℂ, N.inf σ = (∑ σ : L →+* ℂ, Real.log ‖B.gramDet σ x‖) / 2 := by
      rw [Finset.sum_div]
    rw [hsum]
    congr 1
    linarith
  · obtain ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩ := exists_local_frame F x hx hli c hc hF E hE hD p j
    exact ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩

theorem finite_finSum {k : Type} [Field k] [NumberField k] {N : Fl.LogNorms k} (h : N.IsAdelic) :
    (Function.support N.finSum).Finite := by
  refine h.subset fun p hp => ?_
  by_contra h0
  simp only [Set.mem_setOf_eq, not_exists, not_not] at h0
  exact hp (Finset.sum_eq_zero fun j _ => h0 j)

theorem deg_eq_sub {k L L' : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Field L'] [NumberField L']
    (β : k →+* L') (e : L →+* L') (N : Fl.LogNorms k) (N₁ N₂ : Fl.LogNorms L) (a : L') (ha : a ≠ 0)
    (hN : N.IsAdelic) (h₁ : N₁.IsAdelic) (h₂ : N₂.IsAdelic)
    (hinf : ∀ s : L' →+* ℂ, N.inf (s.comp β) = Real.log ‖s a‖ + N₁.inf (s.comp e) - N₂.inf (s.comp e))
    (hfin : ∀ (p : Nat.Primes) (j : L' →+* ℂ_[p]),
      N.fin p (j.comp β) = Real.log ‖j a‖ + N₁.fin p (j.comp e) - N₂.fin p (j.comp e)) :
    N.deg = N₁.deg - N₂.deg := by
  obtain ⟨hd, _⟩ := GlobalTheory.T.logNorms_ext_degree_adelic k L' β N
  obtain ⟨hd₁, ha₁⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₁
  obtain ⟨hd₂, ha₂⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₂
  obtain ⟨_, hpf⟩ := GlobalTheory.T.product_formula_log_norms L' a ha
  have f0 := finite_finSum (GlobalTheory.T.log_norms_of_nonzero_adelic L' a ha)
  have f1 := finite_finSum (ha₁.2 h₁)
  have f2 := finite_finSum (ha₂.2 h₂)
  rw [← hd, ← hd₁, ← hd₂]
  have hs : (LogNorms.ext β N).finSum = fun p => (LogNorms.ofElt a).finSum p +
      (LogNorms.ext e N₁).finSum p - (LogNorms.ext e N₂).finSum p := by
    funext p
    simp only [LogNorms.finSum, LogNorms.ext, LogNorms.ofElt, hfin, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  have hfs : ∑ᶠ p, (LogNorms.ext β N).finSum p = ∑ᶠ p, (LogNorms.ofElt a).finSum p +
      ∑ᶠ p, (LogNorms.ext e N₁).finSum p - ∑ᶠ p, (LogNorms.ext e N₂).finSum p := by
    rw [hs, finsum_sub_distrib ((f0.union f1).subset (Function.support_add _ _)) f2,
      finsum_add_distrib f0 f1]
  have hi : ∑ s, (LogNorms.ext β N).inf s = ∑ s : L' →+* ℂ, Real.log ‖s a‖ +
      ∑ s, (LogNorms.ext e N₁).inf s - ∑ s, (LogNorms.ext e N₂).inf s := by
    simp only [LogNorms.ext, hinf, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold LogNorms.deg
  rw [hi, hfs, ← sub_div]
  congr 1
  linarith [hpf]

end LevelTowerAlt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_im] using this
  have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_re] using this
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h2
      nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

end LevelTowerAlt
