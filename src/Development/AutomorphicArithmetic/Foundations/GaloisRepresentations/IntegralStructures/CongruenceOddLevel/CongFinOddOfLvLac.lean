module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.WtDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelAwayAdapted
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SphericalOperatorsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFreeSurjZmod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentSimulEigen

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.NotApartOfOverPair
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsTestOp
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GroundTheory.Automorphic.Spherical

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_zero (t : UA E a →₀ ℂ) : opOf (RU E a) t (0 : UA E a → ℂ) = 0 := by simp [opOf]

theorem exists_op {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (Kw : Subgroup (GL (Fin a) (w.adicCompletion E)))
    (ho : IsOpen (Kw : Set (GL (Fin a) (w.adicCompletion E)))) (hc : IsCompact (Kw : Set (GL (Fin a) (w.adicCompletion E))))
    (f : GL (Fin a) (w.adicCompletion E) →₀ ℂ) (z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ)
    (act : ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ GlobalTheory.PRep.fixed σ.ρ Kw, opOf σ.ρ f v = z σ • v) :
    ∃ (t : UA E a →₀ ℂ) (e : Submodule ℂ (UA E a → ℂ) → ℂ), (∀ g ∈ t.support, g ∈ locU a w ∧ t g = f (cLoc w g)) ∧
      (∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) → opOf (RU E a) t φ = e U • φ) ∧
      ∀ U, IsAutRepU U → (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → e U = z σ := by
  classical
  obtain ⟨t, ht, hact⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw Kw hc ho f z act
  let e : Submodule ℂ (UA E a → ℂ) → ℂ := fun U =>
    if h : IsAutRepU U then z (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U h w hw).1.choose else 0
  have he : ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) →
      opOf (RU E a) t φ = e U • φ := fun U hU φ hφ hx => by
    simp only [e, dif_pos hU]
    exact hact U hU _ (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1.choose_spec φ hφ hx
  refine ⟨t, e, ht, he, ?_⟩
  rintro U hU ⟨φ, hφ, h0, hx⟩ σ hσ
  exact smul_left_injective ℂ h0 ((he U hU φ hφ hx).symm.trans (hact U hU σ hσ φ hφ hx))

theorem fixed_ne_bot {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {Kw : Subgroup (GL (Fin a) (w.adicCompletion E))}
    (h : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw → RU E a x φ = φ) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hσ : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ) : GlobalTheory.PRep.fixed σ.ρ Kw ≠ ⊥ := by
  obtain ⟨φ, hφ, h0, hx⟩ := h
  have e : (locU a w ⊓ Kw.comap (cLoc w)).map (cLoc w) = Kw := by
    refine le_antisymm ?_ fun g hg => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
      have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
      exact ⟨(e.symm g).1, ⟨(e.symm g).2, show cLoc w _ ∈ Kw from h1.symm ▸ hg⟩, h1⟩
  rw [← e]
  exact GlobalTheory.Cong.AdaptLev.fixed_ne_bot_of_fix hU hw σ hσ inf_le_left hφ h0 fun x hx' => hx x hx'.1 hx'.2

theorem exists_satU {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (h : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) → RU E a x φ = φ) : ∃ B, SatU U w B := by
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU w hw).1
  obtain ⟨B, hB⟩ := (UpperTheory.Cb.spherical_operators_exist E w a).1 σ (fixed_ne_bot hU hw h σ hσ)
  exact ⟨B, σ, hσ, hB⟩

theorem exists_powOp {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (n : ℤ) :
    ∃ t : UA E a →₀ ℂ, (∀ g ∈ t.support, g ∈ locU a w) ∧ ∀ U, IsAutRepU U → ∀ φ ∈ U,
      (∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) → RU E a x φ = φ) → opOf (RU E a) t φ = PowSatU U w n • φ := by
  classical
  obtain ⟨h1, h2⟩ := UpperTheory.Cb.spherical_operators_exist E w a
  obtain ⟨f, -, hf⟩ := h2 n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  let z : SmIrr (GL (Fin a) (w.adicCompletion E)) → ℂ := fun σ =>
    if h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B then ((UpperTheory.V.Af.algSat a (normV w) h.choose).map (· ^ n)).sum else 0
  have hz : ∀ σ B, GlobalTheory.LFun.HasSatGL w σ.ρ B → z σ = ((UpperTheory.V.Af.algSat a (normV w) B).map (· ^ n)).sum := fun σ B hB => by
    have h : ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B := ⟨B, hB⟩
    simp only [z, dif_pos h]
    rw [GlobalTheory.LFun.HasSatGL.unique h.choose_spec hB]
  obtain ⟨t, ht, hact⟩ := GlobalTheory.T.localOperator_acts_by_localComponentScalar E a w hw _ hc ho f z fun σ v hv => by
    by_cases h0 : v = 0
    · simp [h0, opOf]
    · obtain ⟨B, hB⟩ := h1 σ ((Submodule.ne_bot_iff _).2 ⟨v, hv, h0⟩)
      rw [hz σ B hB]
      exact hf σ B hB v hv
  refine ⟨t, fun g hg => (ht g hg).1, fun U hU φ hφ hx => ?_⟩
  by_cases h0 : φ = 0
  · rw [h0, opOf_zero, smul_zero]
  · have h := exists_satU hU hw ⟨φ, hφ, h0, hx⟩
    obtain ⟨σ, hσ, hB⟩ := h.choose_spec
    rw [PowSatU, dif_pos h, ← hz σ _ hB]
    exact hact U hU σ hσ φ hφ hx


open UpperTheory.Gal.Gen in
theorem exists_testOp (K : Subgroup (UA E a)) {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (hK : HypAt K w)
    (Φ : MvPolynomial (Fin a) ℂ) : ∃ (f : UA E a →₀ ℂ) (η : Submodule ℂ (UA E a → ℂ) → ℂ),
      (∀ g ∈ f.support, g ∈ locU a w) ∧ ∀ U, IsAutRepU U →
        (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) f φ = η U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (η U ≠ 0 ↔ UpperTheory.Gal.Gen.GenAt w Φ U)) := by
  have hX := satEx_holds
  obtain ⟨p, hp, hpe, -⟩ := symEx_holds a Φ
  obtain ⟨C, hC⟩ := globOp_holds E a K w hw hK
  obtain ⟨f, hloc, -, -, hact⟩ := hC p hp
  classical
  obtain ⟨η, hη⟩ : ∃ η : Submodule ℂ (UA E a → ℂ) → ℂ,
      ∀ U (h : ∃ z, SatAt U w z), η U = evalAt h.choose p :=
    ⟨fun U => if h : ∃ z, SatAt U w z then evalAt h.choose p else 0, fun U h => dif_pos h⟩
  refine ⟨f, η, hloc, fun U hU => ⟨?_, ?_⟩⟩
  · intro φ hφ hfix
    by_cases h0 : φ = 0
    · subst h0
      simp [opOf]
    · have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
      rw [hη U hz]
      exact hact U hU _ hz.choose_spec φ hφ hfix
  · rintro ⟨φ, hφ, h0, hfix⟩
    have hz := hX E a K w hw hK U hU ⟨φ, hφ, h0, hfix⟩
    have key : ∀ z, SatAt U w z → evalAt z p = η U := by
      intro z hzz
      have h1 := hact U hU z hzz φ hφ hfix
      have h2 := hact U hU _ hz.choose_spec φ hφ hfix
      rw [hη U hz]
      exact smul_left_injective ℂ h0 (h1.symm.trans h2)
    constructor
    · intro hne z hzz
      rw [← key z hzz, hpe z] at hne
      simpa using Finset.prod_ne_zero_iff.1 hne 1 (Finset.mem_univ _)
    · intro hgen
      obtain ⟨z, hzz⟩ := hz
      rw [← key z hzz, hpe z]
      refine Finset.prod_ne_zero_iff.2 fun σ _ => ?_
      have hs : SatAt U w (z ∘ σ) := by
        obtain ⟨τ, h1, h2⟩ := hzz
        refine ⟨τ, h1, ?_⟩
        have hm : Finset.univ.val.map (z ∘ σ) = Finset.univ.val.map z := by
          rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
        rw [hm]
        exact h2
      exact hgen _ hs


open UpperTheory.Gal.Gen in
theorem exists_scale {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (f : UA E a →₀ ℂ)
    (hf : ∀ g ∈ f.support, g ∈ finU (E := E) (n := a)) : ∃ c : ℂ, c ≠ 0 ∧ IntW ι lam (c • f) ∧ Loc.IntL ι lam (c • f) := by
  have hl : Nat.Prime l := Fact.out
  obtain ⟨d, hd⟩ := denomBdd_holds E l hl a (f.support : Set (UA E a)) f.support.finite_toSet.isCompact
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
  have hq0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  set S : ℝ := ∑ g ∈ f.support, ‖ι.symm (f g)‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let r : UA E a → ℕ := fun g => a * d *
    ∑ᶠ (u : HeightOneSpectrum (𝓞 E)) (_ : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ cLoc u g ≠ 1), wtSizeOver ι lam u
  set B : ℝ := ((l : ℝ)⁻¹) ^ (a * d * wtSize lam + ∑ g ∈ f.support, r g) with hB
  have hB0 : 0 < B := pow_pos hq0 _
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hB0 (by linarith : (0 : ℝ) < S + 1)) hq1
  have hk' : ((l : ℝ)⁻¹) ^ k * (S + 1) ≤ B := ((lt_div_iff₀ (by linarith : (0 : ℝ) < S + 1)).mp hk).le
  have hnorm : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
    have h1 : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have := PadicAlgCl.norm_extends l (l : ℚ_[l])
      simpa [map_natCast, Padic.norm_p] using this
    rw [map_pow, map_natCast, norm_pow, h1]
  have key : ∀ g ∈ f.support, ‖ι.symm ((((l : ℂ) ^ k) • f) g)‖ ≤ B := fun g hgf => by
    rw [Finsupp.smul_apply, smul_eq_mul, map_mul, norm_mul, hnorm]
    have hle : ‖ι.symm (f g)‖ ≤ S + 1 := by
      have := Finset.single_le_sum (f := fun g => ‖ι.symm (f g)‖) (fun _ _ => norm_nonneg _) hgf
      linarith
    exact (mul_le_mul_of_nonneg_left hle (pow_pos hq0 k).le).trans hk'
  refine ⟨(l : ℂ) ^ k, pow_ne_zero _ (by exact_mod_cast hl.ne_zero), fun g hg => ?_, fun g hg => ?_⟩
  · have hgf : g ∈ f.support := Finsupp.support_smul hg
    exact ⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_add_right _ _))⟩
  · have hgf : g ∈ f.support := Finsupp.support_smul hg
    exact ⟨hf g hgf, d, hd g hgf, (key g hgf).trans (pow_le_pow_of_le_one hq0.le hq1.le
      ((Finset.single_le_sum (f := r) (fun _ _ => Nat.zero_le _) hgf).trans (Nat.le_add_left _ _)))⟩

end UpperTheory.Gal.Int.Cong

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.OpenCompactMap
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GlobalTheory.Cong.AdaptLev

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem exists_locLev {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (w₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a), (∀ w, H w ≤ intU a w) ∧
      (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) ∧ (∀ w u, ¬ Apart w u → H w = H u) ∧
      (∀ w, ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ H w, RU E a x φ = φ) ∧
      (∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w) ∧
      ∀ᶠ w in Filter.cofinite, H w = intU a w := by
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀0⟩ := (Submodule.ne_bot_iff U).1 hU.ne_bot
  have hφ₀aut : IsAutFormU φ₀ := hU.aut φ₀ hφ₀U
  let stab : Subgroup (UA E a) :=
    { carrier := {x | RU E a x φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at hx hy ⊢
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        calc RU E a x⁻¹ φ₀ = RU E a x⁻¹ (RU E a x φ₀) := by rw [hx]
          _ = φ₀ := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun r =>
    if ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a r, RU E a x φ = φ then intU a r else intU a r ⊓ stab
  have hint : ∀ w, (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ intU a w, RU E a x φ = φ) → H w = intU a w := fun w h => if_pos h
  refine ⟨H, fun r => ?_, fun r => ?_, fun w u h => ?_, fun r => ?_, hint, ?_⟩
  · simp only [H]
    split_ifs
    exacts [le_rfl, inf_le_left]
  · simp only [H]
    split_ifs
    · exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2
    · have e : (((intU a r ⊓ stab).subgroupOf (locU a r)) : Set (locU a r)) =
          (((intU a r).subgroupOf (locU a r)) : Set (locU a r)) ∩
            (fun x : locU a r => (⟨x.1, ((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 x.2).1⟩ : finU (E := E) (n := a))) ⁻¹'
              {k : finU (E := E) (n := a) | RU E a k φ₀ = φ₀} := by
        ext x; exact Iff.rfl
      rw [e]
      exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a r).2.inter (hφ₀aut.level.preimage (Continuous.subtype_mk continuous_subtype_val _))
  · simp only [H, intU_congr h]
  · simp only [H]
    split_ifs with h1
    · exact h1
    · exact ⟨φ₀, hφ₀U, hφ₀0, fun x hx => (Subgroup.mem_inf.1 hx).2⟩
  · filter_upwards [GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces E a φ₀ hφ₀aut] with w hw
    exact hint w ⟨φ₀, hφ₀U, hφ₀0, hw⟩

theorem map_intU {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) : (intU a w).map (cLoc w) = GlobalTheory.LFun.KGL w (n := a) := by
  refine le_antisymm ?_ (KGL_le_map hw)
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_intU.1 hx).2 w (not_apart_self w)

theorem open_compact_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) {L : Subgroup (UA E a)} (hL : L ≤ intU a w)
    (ho : IsOpen ((L.subgroupOf (locU a w)) : Set (locU a w))) :
    IsOpen ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) ∧
      IsCompact ((L.map (cLoc w) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hle := hL.trans (intU_le_locU w)
  rw [map_eq_image hle e he]
  refine ⟨e.toHomeomorph.isOpenMap _ ho, IsCompact.image ?_ e.continuous⟩
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  convert isCompact_of_le hL ho (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1 using 1
  exact coe_subgroupOf_image hle

theorem exists_level {T : Finset (HeightOneSpectrum (𝓞 E))} {U : Submodule ℂ (UA E a → ℂ)} (hU : AutOffT T U)
    {w₀ v' : HeightOneSpectrum (𝓞 E)} (hw₀ : IsSplitAt w₀) (hv' : IsSplitAt v') (hap : Apart v' w₀) :
    ∃ (K : Subgroup (UA E a)) (Kw : Levels E a) (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))),
      IsLevelAway w₀ K ∧ IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) ∧
      (∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K ⊓ Kv.comap (cLoc v'), RU E a x φ = φ) ∧ Kw v' = GlobalTheory.LFun.KGL v' (n := a) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → ∀ x ∈ locU a w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) → x ∈ K) ∧
      ∀ w, IsSplitAt w → Apart w w₀ → ∀ x ∈ locU a w, x ∈ K ↔ cLoc w x ∈ Kw w := by
  classical
  obtain ⟨H, hleI, hopen, hfib, hfix, hint, hae⟩ := exists_locLev hU.1 w₀
  have hle : ∀ w, H w ≤ locU a w := fun w => (hleI w).trans (intU_le_locU w)
  have hcpt : ∀ w, IsCompact (H w : Set (UA E a)) := fun w => isCompact_of_le (hleI w) (hopen w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  obtain ⟨φ, hφU, hφ0, hφH⟩ := GlobalTheory.T.exists_vector_fixed_by_product_localLevels E a U hU.1 w₀ H hle hfib hcpt
    (hae.mono fun w hw x hx => by rw [hw] at hx; exact (mem_intU.1 hx).2 w (not_apart_self w)) hopen (fun w _ => hfix w)
  have hφ := GlobalTheory.T.fixed_of_fixed_by_local_levels E a w₀ H hle hfib hcpt hopen hae φ (hU.1.aut φ hφU) hφH
  let H' : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a) := fun w => if Apart w v' then H w else intU a w
  have h1 : ∀ w, Apart w v' → H' w = H w := fun w h => if_pos h
  have h2 : ∀ w, ¬ Apart w v' → H' w = intU a w := fun w h => if_neg h
  have hleI' : ∀ w, H' w ≤ intU a w := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hleI w
    · rw [h2 w h]
  have hle' : ∀ w, H' w ≤ locU a w := fun w => (hleI' w).trans (intU_le_locU w)
  have hopen' : ∀ w, IsOpen (((H' w).subgroupOf (locU a w)) : Set (locU a w)) := fun w => by
    by_cases h : Apart w v'
    · rw [h1 w h]; exact hopen w
    · rw [h2 w h]; exact (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).2
  have hcpt' : ∀ w, IsCompact (H' w : Set (UA E a)) := fun w => isCompact_of_le (hleI' w) (hopen' w) (GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open E a w).1
  have hfib' : ∀ w u, ¬ Apart w u → H' w = H' u := fun w u h => by
    by_cases hw : Apart w v'
    · have hu : Apart u v' := by
        by_contra hu
        exact not_apart_trans h hu hw
      rw [h1 w hw, h1 u hu, hfib w u h]
    · rw [h2 w hw, h2 u (not_apart_trans (not_apart_symm h) hw), intU_congr h]
  have hint' : ∀ w, H w = intU a w → H' w = intU a w := fun w h => by
    by_cases hw : Apart w v'
    · rw [h1 w hw, h]
    · exact h2 w hw
  refine ⟨levelOf a w₀ H', fun w => (H' w).map (cLoc w), (H v').map (cLoc v'),
    GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels E a w₀ H' hle' hfib' hcpt' hopen' (hae.mono hint'), (open_compact_map hv' (hleI v') (hopen v')).1,
    ⟨φ, hφU, hφ0, fun x hx => hφ x ?_⟩, ?_, fun w hw _ => open_compact_map hw (hleI' w) (hopen' w), ?_, ?_, ?_⟩
  · obtain ⟨hx1, y, hy, e⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨g1, g2, g3⟩ := mem_levelOf.1 hx1
    refine mem_levelOf.2 ⟨g1, g2, fun w hw => ?_⟩
    by_cases h : Apart w v'
    · rw [← h1 w h]; exact g3 w hw
    · refine ⟨y, by rw [hfib w v' h]; exact hy, ?_⟩
      have := GlobalTheory.Cong.LevelExt.one_of_cLoc hv' (y * x⁻¹) (by rw [map_mul, map_inv, e, mul_inv_cancel]) w h
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
  · show (H' v').map (cLoc v') = _
    rw [h2 v' (not_apart_self v'), map_intU hv']
  · rintro w hw - ⟨B, σ, hσ, hB⟩
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := fix_of_fixed hw σ hσ hB.1
    show (H' w).map (cLoc w) = _
    rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun x hx =>
      hφ' x (mem_intU.1 hx).1 ((mem_intU.1 hx).2 w (not_apart_self w))⟩), map_intU hw]
  · intro w hw hT x hx hk
    have hap : Apart w w₀ := by
      unfold Apart
      intro h
      have := eq_of_not_apart_of_not_split hw (show ¬ Apart w₀ w from fun h' => h' h.symm)
      exact hw (this ▸ hw₀)
    obtain ⟨φ', hφ'U, hφ'0, hφ'⟩ := hU.2 w hw hT
    exact (mem_levelOf_iff_of_locU hle' hfib' hap hx).2 (by
      rw [hint' w (hint w ⟨φ', hφ'U, hφ'0, fun y hy =>
        hφ' y (mem_intU.1 hy).1 ((mem_intU.1 hy).2 w (not_apart_self w))⟩)]
      exact mem_intU_of hx hk)
  · intro w hw hap x hx
    rw [mem_levelOf_iff_of_locU hle' hfib' hap hx]
    show x ∈ H' w ↔ cLoc w x ∈ (H' w).map (cLoc w)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      rw [← eq_of_cLoc_eq (hle' w hy) hx e]
      exact hy

theorem isLevelAway_inf {w₀ : HeightOneSpectrum (𝓞 E)} {K : Subgroup (UA E a)} (hK : IsLevelAway w₀ K)
    (v' : HeightOneSpectrum (𝓞 E)) {Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))}
    (ho : IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E)))) : IsLevelAway w₀ (K ⊓ Kv.comap (cLoc v')) := by
  have hc := GlobalTheory.BCT.GlobLev.continuous_cLoc (n := a) v'
  obtain ⟨N, hN, h1, hNK⟩ := hK.isOpen
  refine ⟨inf_le_left.trans hK.fin, fun x hx => hK.one x hx.1, hK.compact.inter_right ((Kv.isClosed_of_isOpen ho).preimage hc),
    N ∩ cLoc v' ⁻¹' Kv, hN.inter (ho.preimage hc), ⟨h1, by simp⟩, fun x hx hf h => ⟨hNK x hx.1 hf h, hx.2⟩⟩

end UpperTheory.Gal.Int.Cong

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ApartOfNotMem
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

def CongUWG (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    IsSplitAt v' → Apart v' w₀ →
    ∃ Kw : Levels E a, HasLevelOff w₀ v' Kw U ∧
      (∀ w, IsSplitAt w → Apart w w₀ → IsOpen (Kw w : Set (GL (Fin a) (w.adicCompletion E))) ∧
        IsCompact (Kw w : Set (GL (Fin a) (w.adicCompletion E)))) ∧
      (∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → Kw w = GlobalTheory.LFun.KGL w (n := a)) ∧
      ∀ (Z W : Finset (HeightOneSpectrum (𝓞 E))),
        (∀ z ∈ Z, IsSplitAt z ∧ Apart z w₀ ∧ Apart z v' ∧ ∃ B, SatU U z B) →
        (∀ w ∈ W, IsSplitAt w ∧ Apart w w₀ ∧ Apart w v' ∧ ∃ B, SatU U w B) →
      ∃ c : HeightOneSpectrum (𝓞 E) → ℤ → ℂ, (∀ w n, c w n ≠ 0) ∧
      ∀ (J : Type) (O : LocOps l ι Kw J) (θ : J → Qbar l), IsSysU O U θ →
        PolyApprox (Sum.elim θ (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U p.1 p.2)))
          {ϑ | ∃ U' θ', AutOffT T U' ∧ HasLevelOff w₀ v' Kw U' ∧ (∃ B, SatU U' v' B) ∧ SameWtOff ι w₀ v' U U' ∧
            Wt E l a ι w₀ v' U U' ∧ Ty E l a w₀ U' ∧ (∀ z ∈ Z, GenAtU Gen U' z) ∧ IsSysU O U' θ' ∧
            ϑ = Sum.elim θ' (fun p : ↥W × ℤ => ι.symm (c p.1 p.2 * PowSatU U' p.1 p.2))} ∧
        ((∀ j g, ∃ q : ℚ, O.f j g = q) → ∃ L : FinExt l, ∀ j, θ j ∈ L.1)

theorem apart_of_not_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ}
    {u w : HeightOneSpectrum (𝓞 E)} (hu : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w u := by
  intro h
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    change _ ∈ Ideal.comap _ _
    simpa using hu
  rw [← h] at h1
  apply hw
  have h2 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) w.asIdeal := h1
  simpa using h2

def CongFinG : Prop := CongUWG TyEll (GenOf DGen) WtLac

end UpperTheory.Gal.Int.Cong

end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW
open GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Cong

def EllSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∀ N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E)), ∀ m₀ : ℕ,
    ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧
      (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
      Function.Surjective θ ∧ ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 →
        ∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
          (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ


open UpperTheory.Gal.Gen in
def StepSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' (n := a) → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IntW ι lam (t j) ∧ Loc.IntL ι lam (t j)) →
      (∀ j, ∀ g ∈ (t j).support, (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧ ∀ u, ¬ Apart u v' → cLoc u g = 1) →
      ActsBy (K ⊓ Kv.comap (cLoc v')) t η →
    ∀ τ₀ : E →+* ℂ, OverPl ι τ₀ v' → ∀ U, OfType lam (K ⊓ Kv.comap (cLoc v')) U →
      PolyApprox (fun j => ι.symm (η U j)) {ϑ | ∃ (U' : Submodule ℂ (UA E a → ℂ)) (mu : (E →+* ℂ) → DomWeight a),
        (∀ τ, mu τ ≠ lam τ → OverPair ι v' τ) ∧ GapWt a (mu τ₀) ∧ OfType mu K U' ∧ TyEll E l a w₀ U' ∧
        ϑ = fun j => ι.symm (η U' j)}

theorem not_apart_of_overPair {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {u v : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hu : OverPair ι u τ) (hv : OverPair ι v τ) : ¬ Apart u v := by
  obtain ⟨x, hx, hxu⟩ := exists_of_overPair ι hu
  obtain ⟨y, hy, hyv⟩ := exists_of_overPair ι hv
  have key : ∀ z : HeightOneSpectrum (𝓞 E), OverPl ι τ z → z.asIdeal = PlaceEmb.smallIdeal (ι.symm.toRingHom.comp τ) :=
    fun z hz => z.isMaximal.eq_of_le (PlaceEmb.smallIdeal_isPrime _).ne_top fun b hb => hz b hb
  obtain rfl : x = y := HeightOneSpectrum.ext ((key x hx).trans (key y hy).symm)
  exact GlobalTheory.Cong.AdaptLev.not_apart_trans (GlobalTheory.Cong.AdaptLev.not_apart_symm hxu) hyv


open UpperTheory.Gal.Gen in
theorem intL_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {v' : HeightOneSpectrum (𝓞 E)} {lam mu : (E →+* ℂ) → DomWeight a} (h : ∀ τ, mu τ ≠ lam τ → OverPair ι v' τ)
    {f : UA E a →₀ ℂ} (hv : ∀ g ∈ f.support, ∀ u, ¬ Apart u v' → cLoc u g = 1) (hf : Loc.IntL ι lam f) : Loc.IntL ι mu f := by
  classical
  intro g hg
  obtain ⟨h1, d, h2, h3⟩ := hf g hg
  refine ⟨h1, d, h2, h3.trans_eq ?_⟩
  congr 2
  refine finsum_congr fun u => finsum_congr fun hu => Finset.sum_congr rfl fun τ hτ => ?_
  have : mu τ = lam τ := by
    by_contra hne
    exact hu.2 (hv g hg u (not_apart_of_overPair ι (Finset.mem_filter.1 hτ).2 (h τ hne)))
  rw [this]

open UpperTheory.Gal.Gen in
theorem stepSt_of_ex (hEll : EllSt) (H : WtLacEx) : StepSt := by
  intro E _ _ _ l _ ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η ht htv hη τ₀ hτ₀ U hU
  have h1 := H E l ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η (fun j => (ht j).2) htv hη τ₀ hτ₀ U hU
  refine (combine_holds (Qbar l) _ _ _ _ 1 h1 ?_).mono fun _ h => h.1
  rintro _ ⟨U₁, mu, g1, g2, g3, rfl⟩
  refine ⟨by simp, ?_⟩
  have hmu : (Wt.ofFam mu).at = mu := by
    obtain ⟨W', -, hW', -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a mu K U₁ hK.fin g3 w₀
    obtain rfl : mu = W'.at := (funext hW').symm
    have : Wt.ofFam W'.at = W' := funext fun v => W'.at_embedding v
    rw [this]
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := PlaceEmb.norm_p_lt_one
  have hD : Dense ι (Wt.ofFam mu) K fun U' => TyEll E l a w₀ U' := by
    intro f hf ε hε
    obtain ⟨N, hN, hfN⟩ := smoothAt_holds E a w₀ hs₀ _ f
    obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨m, J, θ, hm, hJN, hJo, hJc, hJt, hθ, hsc⟩ := hEll E l a ha w₀ hw₀ N hN m₀
    have hfJ : f ∈ fixedBy (Wt.ofFam mu) (lev K w₀ J) := by
      intro c hc v g
      obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := ((levFacts_holds E a w₀ hs₀ K hK J hJo hJc).2.1 c).1 hc
      rw [← mul_assoc, hfN x hx (hJN hxJ), hf k hk]
    obtain ⟨G, hG, e, he, hGe⟩ := tyStep_holds E l ι a w₀ hs₀ K hK _ J hJo hJc hJt m θ f hfJ
    refine ⟨G, part_mono _ _ ?_ hG, e, fun g => (he g).trans
      ((pow_le_pow_of_le_one (norm_nonneg _) hl1.le hm).trans hm₀.le), hGe⟩
    rintro U' ⟨χ, hχ, φ, hφ, hφ0, -, hφJ⟩
    exact ⟨m, J, θ, χ, hJo, hJc, hJt, hθ, hχ, hsc χ hχ, φ, hφ, hφ0, hφJ⟩
  refine (toPolyX_holds E l ι a w₀ K hK.fin mu _ hD Jx t η
    (Loc.frame denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds ι _ _ fun j => Or.inr (by
      rw [hmu]
      exact intL_congr ι g1 (fun g hg => (htv j g hg).2) (ht j).2))
    (fun V hV φ hφ hx j => hη V hV φ hφ (fun x h => hx x h.1) j) U₁ g3).mono ?_
  rintro _ ⟨U', k1, k2, rfl⟩
  exact ⟨U', mu, g1, g2, k1, k2, rfl⟩

open UpperTheory.Gal.Gen in
theorem congUWG_of (H : StepSt) (hFin : FinU) (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) (hD : ∀ a, D a ≠ 0) :
    CongUWG TyEll (GenOf D) WtLac := by
  classical
  intro E _ _ _ l _ ι a ha T _ U hU w₀ v' hw₀ hs₀ hv' hsv hap
  obtain ⟨K, Kw, Kv, hK, hKvo, hfix, hKwv, hoc, hsph, hns, hKs⟩ := exists_level hU hs₀ hsv hap
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU.1
  set K' := K ⊓ Kv.comap (cLoc v') with hK'def
  have hK' : IsLevelAway w₀ K' := isLevelAway_inf hK v' hKvo
  have hOf : OfType lam K' U := ⟨hU.1, hlam, hfix⟩
  have hone : ∀ {w u : HeightOneSpectrum (𝓞 E)}, Apart w u → ∀ x ∈ locU a w, ∀ u', ¬ Apart u' u → cLoc u' x = 1 := fun hwu x hx u' hu' =>
    ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u' (GlobalTheory.Cong.AdaptLev.apart_of_apart_not_apart hwu hu')
  have hKs' : ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → ∀ x ∈ locU a w, x ∈ K' ↔ cLoc w x ∈ Kw w := fun w h1 h2 h3 x hx => by
    rw [← hKs w h1 h2 x hx]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show cLoc v' x ∈ Kv
    rw [hone h3 x hx v' (not_apart_self v')]
    exact one_mem _
  have hloc : ∀ U' : Submodule ℂ (UA E a → ℂ), (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → ∀ w, IsSplitAt w → Apart w w₀ →
      Apart w v' → ∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ Kw w → RU E a x φ = φ :=
    fun U' ⟨φ, g1, g2, g3⟩ w h1 h2 h3 => ⟨φ, g1, g2, fun x hx h => g3 x ((hKs' w h1 h2 h3 x hx).2 h)⟩
  have hlev : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → HasLevelOff w₀ v' Kw U' :=
    fun U' h1 h2 w g1 g2 g3 σ hσ => fixed_ne_bot h1 g1 (hloc U' h2 w g1 g2 g3) σ hσ
  refine ⟨Kw, hlev U hU.1 hfix, hoc, fun w h1 _ h3 h4 => hsph w h1 h3 h4, fun Z W hZ hW => ?_⟩
  have hfin : ∀ {w} {f : UA E a →₀ ℂ}, (∀ g ∈ f.support, g ∈ locU a w) → ∀ g ∈ f.support, g ∈ finU (E := E) (n := a) :=
    fun h g hg => (Subgroup.mem_inf.1 (h g hg)).1
  have hhyp : ∀ w, IsSplitAt w → Apart w w₀ → Apart w v' → (∃ B, SatU U w B) → HypAt K' w := fun w h1 h2 h3 h4 x hx => by
    rw [hKs' w h1 h2 h3 x hx, hsph w h1 h3 h4]
  choose tp htp hpact using fun p : W × ℤ => exists_powOp (a := a) (hW p.1.1 p.1.2).1 p.2
  choose cp hcp0 hcp using fun p : W × ℤ => exists_scale ι lam (tp p) (hfin (htp p))
  let Φ : MvPolynomial (Fin a) ℂ := MvPolynomial.map (Int.castRingHom ℂ) (D a)
  choose tz ez htz hzact using fun z : Z => exists_testOp K' (hZ z.1 z.2).1
    (hhyp z.1 (hZ z.1 z.2).1 (hZ z.1 z.2).2.1 (hZ z.1 z.2).2.2.1 (hZ z.1 z.2).2.2.2) Φ
  choose cz hcz0 hcz using fun z : Z => exists_scale ι lam (tz z) (hfin (htz z))
  refine ⟨fun w n => if h : w ∈ W then cp (⟨w, h⟩, n) else 1, fun w n => by
    dsimp only
    split_ifs
    exacts [hcp0 _, one_ne_zero], fun J O θ hθ => ?_⟩
  have hO₀ : ∀ j, Apart (O.pl j) w₀ := fun j => apart_of_not_mem hw₀ (O.away j)
  have hOv : ∀ j, Apart (O.pl j) v' := fun j => apart_of_not_mem hv' (O.away j)
  choose tj ej htj hjact hje using fun j => exists_op (O.split j) (Kw (O.pl j)) (hoc _ (O.split j) (hO₀ j)).1
    (hoc _ (O.split j) (hO₀ j)).2 (O.f j) (O.z j) (O.act j)
  have hsys : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) → IsSysU O U' fun j => ι.symm (ej j U') :=
    fun U' h1 h2 j σ hσ => congrArg ι.symm (hje j U' h1 (hloc U' h2 _ (O.split j) (hO₀ j) (hOv j)) σ hσ)
  have hθeq : θ = fun j => ι.symm (ej j U) := funext fun j => by
    obtain ⟨σ, hσ⟩ := (GlobalTheory.T.exists_unique_splitPlaceComponent_definiteUnitary E a U hU.1 _ (O.split j)).1
    rw [hθ j σ hσ]
    exact (hsys U hU.1 hfix j σ hσ).symm
  have hactJ : ActsBy K' tj fun U' j => ej j U' := fun U' hU' φ hφ hx j =>
    hjact j U' hU' φ hφ fun x h1 h2 => hx x ((hKs' _ (O.split j) (hO₀ j) (hOv j) x h1).2 h2)
  subst hθeq
  refine ⟨?_, fun hq => hFin E l ι a ha w₀ K' hK' lam J tj (fun U' j => ej j U')
    (fun j g hg => ⟨(Subgroup.mem_inf.1 (htj j g hg).1).1, by rw [(htj j g hg).2]; exact hq j _⟩) hactJ U hOf⟩
  let t : (J ⊕ W × ℤ) ⊕ Z → (UA E a →₀ ℂ) := Sum.elim (Sum.elim tj fun p => cp p • tp p) fun z => cz z • tz z
  let η : Submodule ℂ (UA E a → ℂ) → (J ⊕ W × ℤ) ⊕ Z → ℂ := fun U' =>
    Sum.elim (Sum.elim (fun j => ej j U') fun p => cp p * PowSatU U' p.1 p.2) fun z => cz z * ez z U'
  have hact : ActsBy K' t η := by
    rintro U' hU' φ hφ hx ((j | p) | z)
    · exact hactJ U' hU' φ hφ hx j
    · obtain ⟨h1, h2, h3, h4⟩ := hW p.1.1 p.1.2
      show opOf (RU E a) (cp p • tp p) φ = (cp p * PowSatU U' p.1 p.2) • φ
      rw [opOf_smul', hpact p U' hU' φ hφ fun x g1 g2 => hx x ((hhyp _ h1 h2 h3 h4 x g1).2 g2), smul_smul]
    · show opOf (RU E a) (cz z • tz z) φ = (cz z * ez z U') • φ
      rw [opOf_smul', (hzact z U' hU').1 φ hφ hx, smul_smul]
  have hsupp : ∀ j, ∃ w, Apart w w₀ ∧ Apart w v' ∧ ∀ g ∈ (t j).support, g ∈ locU a w := by
    rintro ((j | p) | z)
    · exact ⟨_, hO₀ j, hOv j, fun g hg => (htj j g hg).1⟩
    · exact ⟨_, (hW p.1.1 p.1.2).2.1, (hW p.1.1 p.1.2).2.2.1, fun g hg => htp p g (Finsupp.support_smul hg)⟩
    · exact ⟨_, (hZ z.1 z.2).2.1, (hZ z.1 z.2).2.2.1, fun g hg => htz z g (Finsupp.support_smul hg)⟩
  have hint : ∀ j, IntW ι lam (t j) ∧ Loc.IntL ι lam (t j) := by
    rintro ((j | p) | z)
    · have key : ∀ g ∈ (tj j).support, g ∈ finU (E := E) (n := a) ∧ DenomLe l 0 g ∧ ‖ι.symm (tj j g)‖ ≤ 1 := fun g hg => by
        obtain ⟨h1, h2⟩ := htj j g hg
        refine ⟨(Subgroup.mem_inf.1 h1).1, fun u hu => ?_, by rw [h2]; exact O.int j _⟩
        have h3 : cLoc u g = 1 := hone (apart_of_not_mem hu (O.away j)) g h1 u (not_apart_self u)
        rw [h3, inv_one, pow_zero, one_smul, Units.val_one]
        refine ⟨fun i k => ?_, fun i k => ?_⟩ <;>
        · rw [Matrix.one_apply]
          split_ifs
          exacts [one_mem _, zero_mem _]
      exact ⟨fun g hg => ⟨(key g hg).1, 0, (key g hg).2.1, (key g hg).2.2.trans_eq (by simp)⟩,
        fun g hg => ⟨(key g hg).1, 0, (key g hg).2.1, (key g hg).2.2.trans_eq (by simp)⟩⟩
    · exact hcp p
    · exact hcz z
  have hlam' : (Wt.ofFam lam).at = lam := by
    obtain ⟨W', -, hW', -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K' U hK'.fin hOf w₀
    obtain rfl : lam = W'.at := (funext hW').symm
    have : Wt.ofFam W'.at = W' := funext fun v => W'.at_embedding v
    rw [this]
  have hd : GenData w₀ K' Z fun _ => Φ :=
    ⟨fun w hw => (hZ w hw).1, fun w hw => (hZ w hw).2.1,
      fun w hw => hhyp w (hZ w hw).1 (hZ w hw).2.1 (hZ w hw).2.2.1 (hZ w hw).2.2.2,
      fun _ _ h => hD a (MvPolynomial.map_injective _ Int.cast_injective (h.trans (map_zero _).symm))⟩
  have h1 := toPolyX_holds E l ι a w₀ K' hK'.fin lam _ (denseGen_holds E l ι a ha w₀ hw₀ hs₀ K' hK' (Wt.ofFam lam) Z _ hd) _ t η
    (frameW_holds E l ι a _ _ t fun j => by rw [hlam']; exact (hint j).1) hact U hOf
  let Q : MvPolynomial ((J ⊕ W × ℤ) ⊕ Z) ℤ := ∏ z : Z, MvPolynomial.X (Sum.inr z)
  have hQ : ∀ U', IsAutRepU U' → (∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ) →
      (MvPolynomial.aeval (fun j => ι.symm (η U' j)) Q ≠ 0 ↔ ∀ z ∈ Z, UpperTheory.Gal.Gen.GenAt z Φ U') := by
    intro U' g1 g2
    simp only [Q, map_prod, MvPolynomial.aeval_X, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff, Subtype.forall]
    refine forall₂_congr fun z hz => ?_
    rw [← (hzact ⟨z, hz⟩ U' g1).2 g2, map_ne_zero_iff _ ι.symm.injective]
    show cz ⟨z, hz⟩ * ez ⟨z, hz⟩ U' ≠ 0 ↔ _
    simp [hcz0]
  obtain ⟨τ₀, hτ₀⟩ := exists_overPl ι v' hv'
  have hKv : ∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' (n := a) → x ∈ K := fun x hx h => (hKs v' hsv hap x hx).2 (hKwv ▸ h)
  have h2 := combine_holds (Qbar l) _ _ _ _ Q h1 (by
    rintro _ ⟨U₁, g1, g2, rfl⟩
    exact ⟨(hQ U₁ g1.aut g1.fix).2 g2, H E l ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam _ t η hint
      (fun j g hg => by
        obtain ⟨w, k1, k2, k3⟩ := hsupp j
        exact ⟨hone k1 g (k3 g hg), hone k2 g (k3 g hg)⟩) hact τ₀ hτ₀ U₁ g1⟩)
  have h3 := restrict_holds (Qbar l) _ _ Sum.inl _ _ h2
  have hval : ∀ U' : Submodule ℂ (UA E a → ℂ), (fun j => ι.symm (η U' j)) ∘ Sum.inl = Sum.elim (fun j => ι.symm (ej j U'))
      fun p : W × ℤ => ι.symm ((if h : p.1.1 ∈ W then cp (⟨p.1.1, h⟩, p.2) else 1) * PowSatU U' p.1 p.2) := fun U' => by
    funext j
    rcases j with j | p
    · rfl
    · simp only [Function.comp, η, Sum.elim_inl, Sum.elim_inr, dif_pos p.1.2]
  rw [hval] at h3
  refine h3.mono ?_
  rintro _ ⟨_, ⟨⟨U', mu, g1, g2, g3, g4, rfl⟩, hq⟩, rfl⟩
  obtain ⟨φ, hφ, hφ0, hφK⟩ := g3.fix
  have hfix' : ∃ φ ∈ U', φ ≠ 0 ∧ ∀ x ∈ K', RU E a x φ = φ := ⟨φ, hφ, hφ0, fun x hx => hφK x hx.1⟩
  have huniq : ∀ {V : Submodule ℂ (UA E a → ℂ)}, IsAutRepU V → ∀ {τ x y}, HasWeightAt V τ x → HasWeightAt V τ y → x = y :=
    fun hV _ _ _ hx hy => hasWeightAt_unique ⟨_, hV⟩ _ hx hy
  have hsame : SameWtOff ι w₀ v' U U' := fun τ hτ x => by
    have e : mu τ = lam τ := by
      by_contra hne
      obtain ⟨u, k1, k2⟩ := exists_of_overPair ι (g1 τ hne)
      exact k2 (hτ u k1).2
    exact ⟨fun h => by rw [huniq hU.1 h (hlam τ), ← e]; exact g3.wt τ, fun h => by rw [huniq g3.aut h (g3.wt τ), e]; exact hlam τ⟩
  refine ⟨U', _, ⟨g3.aut, fun w hw hT => ⟨φ, hφ, hφ0, fun x hx h => hφK x (hns w hw hT x hx h)⟩⟩, hlev U' g3.aut hfix',
    exists_satU g3.aut hsv ⟨φ, hφ, hφ0, fun x hx h => hφK x (hKv x hx h)⟩, hsame,
    ⟨hsame, τ₀, hτ₀, fun x hx => by rw [huniq g3.aut hx (g3.wt τ₀)]; exact g2⟩, g4, fun z hz B hB α hα => ?_,
    hsys U' g3.aut hfix', hval U'⟩
  obtain ⟨σ, hσ, hB⟩ := hB
  have := (hQ U' g3.aut hfix').1 hq z hz α ⟨σ, hσ, hα ▸ hB⟩
  rw [MvPolynomial.eval_map] at this
  rw [MvPolynomial.aeval_def]
  exact this

theorem CongUWG.congUW4 {Ty : UnitaryAutomorphicTypeClass} {Gen : ℕ → ℕ → Multiset ℂˣ → Prop} {Wt : SeedWtU} (h : CongUWG Ty Gen Wt)
    (Rk : ℕ → Prop) : CongUW4 Rk Ty Gen Wt := by
  classical
  intro E _ _ _ l _ ι a ha _ T hT U hU w₀ v' h1 h2 h3 h4 h5
  obtain ⟨Kw, g1, g2, g3, g4⟩ := h E l ι a ha T hT U hU w₀ v' h1 h2 h3 h4 h5
  refine ⟨Kw, g1, g2, g3, fun Z W hZ hW => ?_⟩
  obtain ⟨c, hc, g5⟩ := g4 (Z ∪ W) W (fun z hz => (Finset.mem_union.1 hz).elim (hZ z) fun hw => ⟨(hW z hw).1, (hW z hw).2.2⟩)
    fun w hw => ⟨(hW w hw).1, (hW w hw).2.2⟩
  refine ⟨c, hc, fun J O θ hθ => ⟨(g5 J O θ hθ).1.mono ?_, (g5 J O θ hθ).2⟩⟩
  rintro _ ⟨U', θ', k1, k2, k3, k4, k5, k6, k7, k8⟩
  exact ⟨U', θ', k1, k2, k3, k4, k5, k6, fun z hz => k7 z (Finset.mem_union_left _ hz),
    fun z hz => k7 z (Finset.mem_union_right _ hz), k8⟩

end UpperTheory.Gal.Int.Cong

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.ExistsEllType
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {l : ℕ} [Fact l.Prime]

theorem exists_ellType (ha : 1 ≤ a) (w₀ : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (N : Set (GL (Fin a) (w₀.adicCompletion E))) (hN : N ∈ nhds (1 : GL (Fin a) (w₀.adicCompletion E))) (m₀ : ℕ) :
    ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m))), m₀ ≤ m ∧
      (J : Set (GL (Fin a) (w₀.adicCompletion E))) ⊆ N ∧ IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧
      Function.Surjective θ ∧ ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 →
        ∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
          (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ := by
  classical
  have hlp : l.Prime := Fact.out
  have hchar : ∀ {M : ℕ} [NeZero M] (χ : Multiplicative (ZMod M) →* ℂˣ) (z : Multiplicative (ZMod M)),
      χ z = χ (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd z).val := by
    intro M _ χ z
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rcases Nat.lt_or_ge a 2 with ha1 | ha2
  · obtain rfl : a = 1 := by omega
    obtain ⟨N', hN'N, hN'o, h1N'⟩ := mem_nhds_iff.1 hN
    obtain ⟨J, θ, hJN, hJo, hJc, hJtf, hθ⟩ :=
      TypeExists.exists_congruence_surj (E := E) (l := l) (a := 1) le_rfl w₀ hl m₀ N' hN'o h1N'
    refine ⟨m₀, J, θ, le_rfl, hJN.trans hN'N, hJo, hJc, hJtf, hθ, fun χ _ σ _ _ _ => ⟨σ.smooth, fun s d e he => absurd ?_ he⟩⟩
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain rfl : i = j := Subsingleton.elim _ _
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
    have h := (GlobalTheory.SmGL.mem_unipRad.1 hu).2 b i i
    rw [Matrix.one_apply_eq] at h
    rw [h, Units.val_one, Matrix.one_apply_eq]
  · obtain ⟨m, hmm, J, lam, hJo, hJc, hJN, hJtf, hsurj, hsc⟩ :=
      TypeExists.exists_type_surj E w₀ a l hlp hl ha2 N hN m₀
    refine ⟨m, J, lam, hmm, hJN, hJo, hJc,
      fun x hx k hk hxk => hJtf x hx (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, hxk⟩), hsurj, fun χ hχ σ v hv0 hv => ?_⟩
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    refine hsc (χ (Multiplicative.ofAdd 1)) ?_ (fun h => hχ (MonoidHom.ext fun z => ?_)) σ v hv0 fun g => ?_
    · rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]
    · rw [hchar χ z, h, one_pow, MonoidHom.one_apply]
    · rw [hv g, hchar χ (lam g)]

end UpperTheory.Gal.Int.Cong

end
end

open GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

theorem ellSt_holds : EllSt := fun _ _ _ _ _ _ _ ha w₀ hl N hN m₀ => exists_ellType ha w₀ hl N hN m₀

theorem congFinG_of_step (H : StepSt) : CongFinG := congUWG_of H finU_holds DGen dGen_ne_zero

theorem congFinG_of_ex (H : WtLacEx) : CongFinG := congFinG_of_step (stepSt_of_ex ellSt_holds H)

theorem congFinOdd_of_ex (H : WtLacEx) : CongFinOdd := CongUWG.congUW4 (congFinG_of_ex H) Odd

end UpperTheory.Gal.Int.Cong
