module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.NmEq
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.nmEq :
    UpperTheory.Gal.GamX.NmEq := by
  intro K L _ _ _ _ _ v w
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.SplitSuppOf
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.splitSuppOf :
    UpperTheory.Gal.GamX.SplitSuppOf := by
  unfold UpperTheory.Gal.GamX.SplitSuppOf
  intro hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  rcases GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩
  · exfalso
    refine hw fun u => ?_
    haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2
    have hu : u.1.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm
    obtain ⟨-, -, -, h⟩ := hc
    exact Subtype.ext (h u.1 hu)
  · obtain ⟨hi', hN⟩ := GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf
    set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef
    have hi : Continuous i := GroundTheory.Global.continuous_adicCompletionMap v w.1
    have hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) :=
      GroundTheory.Global.adicCompletionMap_algebraMap v w.1
    refine ⟨i, hi', hi, hcomp, ?_, ?_⟩
    · rw [hNm K L v w]
      exact MonoidHom.ext fun y => Units.ext (hN y)
    · rintro s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩
      haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
      obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat := hW
      obtain ⟨e, he'⟩ := hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'
      have hg : ∀ g : GL (Fin n) (w.1.adicCompletion L),
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) τ'.ρ :=
        Representation.Equiv.mk e fun g => LinearMap.ext fun x => by
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]
          exact (he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))
      have h2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ
      exact (hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsConsSome
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem chs_cons_some (ξ : kˣ →* ℂˣ) (hξ) (s : Multiset (IrrGL (k := k))) :
    chs (IrrGL.ofChar ξ hξ ::ₘ s) = ξ ::ₘ chs s := by
  have h : ∃ η : kˣ →* ℂˣ, ∃ hη : IsSmoothChar η, IrrGL.ofChar ξ hξ = IrrGL.ofChar η hη := ⟨ξ, hξ, rfl⟩
  have hc : h.choose = ξ := by
    obtain ⟨hη, he⟩ := h.choose_spec
    exact (IrrGL.ofChar_inj.mp he).symm
  unfold chs
  rw [Multiset.filterMap_cons_some _ _ _ (by rw [dite_eq_left h])]
  rw [hc]

private theorem chs_cons_not {y : IrrGL (k := k)} (hy : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (s : Multiset (IrrGL (k := k))) : chs (y ::ₘ s) = chs s := by
  unfold chs
  rw [Multiset.filterMap_cons_none _ _ (by rw [dite_eq_right hy])]

end Loc

theorem UpperTheory.Gal.GamX.chsTr :
    UpperTheory.Gal.GamX.ChsTr := by
  intro k k' _ _ _ _ _ _ _ _ i hi' s
  induction s using Multiset.induction_on with
  | empty => simp [chs_zero]
  | cons y s ih =>
    rw [Multiset.map_cons]
    by_cases hy : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := hy
      have hξ' : IsSmoothChar (ξ.comp (Units.map (i.symm : k' →* k))) :=
        hξ.comp _ (Units.continuous_map hi')
      rw [GlobalTheory.CharLiftStep.trGL_ofChar i hi' ξ hξ _ hξ' (fun _ => rfl), chs_cons_some, chs_cons_some,
        Multiset.map_cons, ih]
    · have hy' : ¬ ∃ ξ : k'ˣ →* ℂˣ, ∃ hξ, GlobalTheory.SuppIne.trGL i hi' y = IrrGL.ofChar ξ hξ := by
        rintro ⟨ξ, hξ, he⟩
        have h1 : y.fst = 1 := congrArg Sigma.fst he
        exact hy (GlobalTheory.RoadU.PlainChars.exists_eq_ofChar y h1)
      rw [chs_cons_not hy', chs_cons_not hy, ih]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkLiftOf
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem loc_one_of' {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

private theorem eq_of_ae {L : Type} [Field L] [NumberField L] (a b : HChar L)
    (h : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, a.UnrAt u ∧ b.UnrAt u ∧ a.val u = b.val u) : a = b := by
  let ρ : HChar L := a * b⁻¹
  have hl : ∀ u x, ρ.loc u x = a.loc u x * (b.loc u x)⁻¹ := fun _ _ => rfl
  have hev : ∀ᶠ u : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ρ.UnrAt u ∧ ρ.val u = 1 := by
    filter_upwards [h] with u hu
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [hl, hu.1 x hx, hu.2.1 x hx]; simp
    · have e : ρ.val u = a.val u * (b.val u)⁻¹ := rfl
      rw [e, hu.2.2, mul_inv_cancel]
  have h1 : ρ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ρ.1 ρ.2.1 ρ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of' ρ w this.1 this.2 y
  have h2 : ρ = 1 := Subtype.ext h1
  exact mul_inv_eq_one.1 h2

theorem UpperTheory.Gal.GamX.rkLiftOf :
    UpperTheory.Gal.GamX.RkLiftOf := by
  unfold RkLiftOf RkLift
  intro hN K L _ _ _ _ _ _ _ ψ ψ' hW v w
  obtain ⟨ξ, hξ⟩ := hN K L ψ
  suffices e : ψ' = ξ by rw [e]; exact (hξ v w).1
  refine eq_of_ae _ _ ?_
  filter_upwards [hW, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified ψ')] with u h1 h2 h3
  have h2' : ψ.UnrAt (u.under (𝓞 K)) := h2
  have h3' : ψ'.UnrAt u := h3
  have hl : u.asIdeal.LiesOver (u.under (𝓞 K)).asIdeal := ⟨rfl⟩
  obtain ⟨-, hu, d⟩ := hξ (u.under (𝓞 K)) ⟨u, hl⟩
  obtain ⟨b, c⟩ := hu h2'
  have hnv : ∀ {F : Type} [Field F] [NumberField F] (x : HeightOneSpectrum (𝓞 F)), normV x = Ideal.absNorm x.asIdeal :=
    fun x => by rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hf : normV u = normV (u.under (𝓞 K)) ^ fdeg (⟨u, hl⟩ : PlacesOver L (u.under (𝓞 K))) := by
    rw [hnv, hnv]; exact d
  obtain ⟨B, hB, hB'⟩ := h1 _ hf
  obtain rfl := CG.HasSat.unique hB (CG.hasSat_ofChar h2')
  have e := CG.HasSat.unique hB' (CG.hasSat_ofChar h3')
  rw [Multiset.map_singleton, Multiset.singleton_inj] at e
  exact ⟨h3', b, e.symm.trans c.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeOf
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.Gal.GamX

def CharSupp : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub L n),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]
      (τ : SmIrr (GL (Fin n) (v.adicCompletion K))) (T : SmIrr (GL (Fin n) (u.adicCompletion L))), π.IsLocComp v τ → P.IsLocComp u T →
      ∀ (ξ : Fin n → ((v.adicCompletion K)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport τ.ρ (GlobalTheory.RoadU.chars ξ hξ) →
        HasSupport T.ρ (GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
          fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j))

def CharLiftPrime : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] [Algebra K L]
    [IsGalois K L], (Module.finrank K L).Prime → ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub L a),
    GlobalTheory.GalCut.IsLift π P → GlobalTheory.RoadU.CharLift π P

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chs_cons (ξ : kˣ →* ℂˣ) (h : IsSmoothChar ξ) (s : Multiset (IrrGL (k := k))) : chs (IrrGL.ofChar ξ h ::ₘ s) = ξ ::ₘ chs s := by
  have e : ∃ ζ : kˣ →* ℂˣ, ∃ hζ, IrrGL.ofChar ξ h = IrrGL.ofChar ζ hζ := ⟨ξ, h, rfl⟩
  refine Multiset.filterMap_cons_some _ _ _ ?_
  rw [dite_eq_left e]
  obtain ⟨_, h2⟩ := e.choose_spec
  exact congrArg some (IrrGL.ofChar_inj.1 h2).symm

theorem chs_cons_of_not {y : IrrGL (k := k)} (h : ¬ ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (s : Multiset (IrrGL (k := k))) :
    chs (y ::ₘ s) = chs s := Multiset.filterMap_cons_none _ _ (dif_neg h)

theorem chs_map {ι : Type} (t : Multiset ι) (ξ : ι → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) :
    chs (t.map fun j => IrrGL.ofChar (ξ j) (hξ j)) = t.map ξ := by
  induction t using Multiset.induction with
  | empty => rfl
  | cons a t ih => rw [Multiset.map_cons, chs_cons, ih, Multiset.map_cons]

theorem card_chs_le (s : Multiset (IrrGL (k := k))) (h : ∀ y ∈ s, 0 < y.1) :
    Multiset.card (chs s) ≤ (s.map Sigma.fst).sum ∧
      (Multiset.card (chs s) = (s.map Sigma.fst).sum → ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) := by
  induction s using Multiset.induction with
  | empty => exact ⟨le_rfl, fun _ y hy => absurd hy (Multiset.notMem_zero _)⟩
  | cons a s ih =>
    obtain ⟨h1, h2⟩ := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    have ha := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.sum_cons]
    by_cases c : ∃ ξ : kˣ →* ℂˣ, ∃ hξ, a = IrrGL.ofChar ξ hξ
    · obtain ⟨ξ, hξ, rfl⟩ := c
      have e : (IrrGL.ofChar ξ hξ).1 = 1 := rfl
      rw [chs_cons, Multiset.card_cons, e]
      refine ⟨by omega, fun H y hy => ?_⟩
      rcases Multiset.mem_cons.1 hy with rfl | hy
      · exact ⟨ξ, hξ, rfl⟩
      · exact h2 (by omega) y hy
    · rw [chs_cons_of_not c]
      exact ⟨by omega, fun H => by omega⟩

theorem eq_of_chs {s t : Multiset (IrrGL (k := k))} (hs : ∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ)
    (ht : ∀ y ∈ t, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) (h : chs s = chs t) : s = t := by
  have key : ∀ s : Multiset (IrrGL (k := k)), (∀ y ∈ s, ∃ ξ : kˣ →* ℂˣ, ∃ hξ, y = IrrGL.ofChar ξ hξ) →
      s = (chs s).map fun ξ => if h : IsSmoothChar ξ then IrrGL.ofChar ξ h else IrrGL.ofChar 1 isSmoothChar_one := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; rfl
    | cons a s ih =>
      intro H
      obtain ⟨ξ, hξ, rfl⟩ := H a (Multiset.mem_cons_self _ _)
      rw [chs_cons, Multiset.map_cons, dite_eq_left hξ, ← ih fun y hy => H y (Multiset.mem_cons_of_mem hy)]
  rw [key s hs, key t ht, h]

end

theorem charSupp_of (h1 : GamMixed) (h2 : NmEq) (h3 : SuppFacts) : CharSupp := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hW v u hu τ T hτ hT ξ hξ hs
  obtain ⟨⟨s', hs'⟩, huniq, hdeg, -⟩ := h3 L n hn P u
  have H := h1 K L hp n hn π P hW v ⟨u, hu⟩ _ s' ⟨τ, hτ, hs⟩ hs'
  obtain ⟨-, hsum, hpos⟩ := hdeg s' hs'
  obtain ⟨c1, c2⟩ := card_chs_le s' hpos
  rw [up, GlobalTheory.RoadU.chars, chs_map, h2 K L v ⟨u, hu⟩, Multiset.map_map] at H
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc : Multiset.card ((chs s').filter (Thru (v := v) ⟨u, hu⟩)) = n := by rw [H]; simp
  have hle := Multiset.filter_le (Thru (v := v) ⟨u, hu⟩) (chs s')
  have hc' := Multiset.card_le_card hle
  have e := Multiset.eq_of_le_of_card_le hle (by omega)
  have es : s' = GlobalTheory.RoadU.chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u))
      fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    refine eq_of_chs (c2 (by omega)) (fun y hy => ?_) ?_
    · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨_, _, rfl⟩
    · rw [← e, H, GlobalTheory.RoadU.chars, chs_map]; rfl
  obtain ⟨T', hT', hs''⟩ := hs'
  have h1 : (CG.mk P).IsLoc u (Quotient.mk _ T) := hT
  have h2 : (CG.mk P).IsLoc u (Quotient.mk _ T') := hT'
  obtain ⟨φ⟩ := Quotient.exact (CG.IsLoc.unique L n _ u _ _ h2 h1)
  exact es ▸ hs''.of_equiv φ

theorem charLiftPrime_of (h : CharSupp) : CharLiftPrime := by
  intro K L _ _ _ _ _ _ _ _ hp a ha π P hL
  refine ⟨hL, fun v u _ => h K L hp a ha π P ?_ v u⟩
  unfold WeakBC
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L).eventually
    (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL K a π)] with w hw
  obtain ⟨B, hB⟩ := hw
  exact fun f hf => ⟨B, hB, hL.sat w f B hf hB⟩

end UpperTheory.Gal.GamX
end
end
