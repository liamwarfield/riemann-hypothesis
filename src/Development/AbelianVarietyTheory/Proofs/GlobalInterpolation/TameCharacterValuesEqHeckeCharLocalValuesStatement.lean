module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValuesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.DIV hiding unifVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_values_eq_heckeChar_local_values : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (K : Type) [Field K] (σ : K →+* ℂ) (μ : Chr F E K) (ξ : Formalism.L2.Host.HChar E), GlobalTheory.Mem.Col2.Reads σ μ ξ → (∀ P, ξ.TameAt P) → ∀ P : HeightOneSpectrum (𝓞 E), (ξ.UnrAt P → σ ((unifVal μ P : Kˣ) : K) = ((ξ.val P : ℂˣ) : ℂ)) ∧ (((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ ((qVal μ P : Kˣ) : K) = ((ξ.locK P q : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.TwistVal.main | exact GlobalTheory.TwistVal.main | (intros; apply GlobalTheory.TwistVal.main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqAndAlg
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomEq

theorem eq_and_alg : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) ∧ (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) :=
  ⟨fun _ _ _ B χ hcc hδ hχ => Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ,
   fun D cc δ B χ hcc hδ hχ => GlobalTheory.ThLoc.algTAll D cc δ B χ hcc hδ hχ⟩

end GlobalTheory.MomEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Formalism.L2.Host (HChar atFin upF aboveF IsUnitAt ordF)
open GlobalTheory.CharVal (valuation_conjP conjP_conjP')
open GlobalTheory.NormOneUnit (locK_unr locK_tame exists_of_star_eq under_eq_iff)

namespace GlobalTheory.NormOneProd

variable {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]


omit [StarRing E] in
theorem exists_val_eq {P : HeightOneSpectrum (𝓞 E)}
    (hu : ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) (x : Eˣ) :
    ∃ k : Fˣ, P.valuation E ((x / upF F k : Eˣ) : E) = 1 := by
  obtain ⟨k, hk⟩ := (P.under (𝓞 F)).valuation_surjective F (P.valuation E (x : E))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hk
    exact x.ne_zero hk
  refine ⟨Units.mk0 k hk0, ?_⟩
  have hy' : ((x / upF F (Units.mk0 k hk0) : Eˣ) : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  rw [hy', map_div₀, GlobalTheory.MuConj.valuation_up P hu, hk, div_self (by simp)]

theorem split_unit (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P : HeightOneSpectrum (𝓞 E)}
    (hP : P ≠ conjPrime₂ P) {y y' : Eˣ} (hy : (y' : E) = star (y : E))
    (h2 : (conjPrime₂ P).valuation E (y : E) = 1) : χ.locK P y' * χ.locK (conjPrime₂ P) y = 1 := by
  classical
  obtain ⟨e, he, e', he', hee⟩ := exists_coprime hP
  have he1 : P.valuation E (e : E) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 he
  have hy0 : P.valuation E (y : E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ he1 (Units.mk0 _ hy0)⁻¹
  have hn' : P.valuation E ((e : E) ^ n * y) < 1 := by
    rw [map_mul, map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hn
    rwa [← lt_div_iff₀ (zero_lt_iff.2 hy0), one_div]
  have hm : e ^ n - 1 ∈ (conjPrime₂ P).asIdeal := by
    refine Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one e n) ?_
    have : e - 1 = -e' := by rw [← hee]; ring
    rw [this]
    exact neg_mem he'
  obtain ⟨k, hk⟩ := exists_of_star_eq hF hr hc (x := (e : E) ^ n * y + star ((e : E) ^ n * y : E))
    (by rw [star_add, star_star, add_comm])
  have v1 : (conjPrime₂ P).valuation E (algebraMap F E k - y) < 1 := by
    have e1 : algebraMap F E k - y = ((e ^ n - 1 : 𝓞 E) : E) * y + star ((e : E) ^ n * y : E) := by
      rw [hk]; push_cast; ring
    rw [e1]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, h2, mul_one]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hm
    · rw [valuation_conjP, star_star]
      exact hn'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_sub, Valuation.map_neg, h2] at v1
    exact lt_irrefl _ v1
  have a1 : χ.locK (conjPrime₂ P) (upF F (Units.mk0 k hk0)) = χ.locK (conjPrime₂ P) y := locK_tame (ht _) h2 v1
  have a2 : χ.locK P (upF F (Units.mk0 k hk0)) = χ.locK P y' := by
    refine locK_tame (ht _) (hy ▸ (valuation_conjP P _).symm.trans h2) ?_
    rw [valuation_conjP, star_sub, hF, ← hy] at v1
    exact v1
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  have h := hχ.1 (P.under (𝓞 F)) (Units.mk0 k hk0)
  rwa [HChar.resFin_apply, hab, Finset.prod_pair hP, a1, a2] at h


open Classical in
theorem place_prod (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E),
      ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2)
    {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) (hun : ∀ P, conjPrime₂ P = P → χ.UnrAt P)
    {x z : Eˣ} (hxz : (x : E) = z * star (x : E)) (P : HeightOneSpectrum (𝓞 E)) :
    ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = χ.locK P z := by
  obtain ⟨k, hk⟩ := exists_val_eq (hu (conjPrime₂ P)) x
  set y : Eˣ := x / upF F k with hy
  have hy' : (y : E) = x / algebraMap F E k := Units.val_div_eq_div_val _ _
  have hyz : (y : E) = z * star (y : E) := by
    rw [hy', star_div₀, hF, ← mul_div_assoc, ← hxz]
  have h := hχ.1 (P.under (𝓞 F)) k
  rw [HChar.resFin_apply] at h
  have e1 : ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q x = ∏ Q ∈ aboveF (L := E) F (P.under (𝓞 F)), χ.locK Q y := by
    simp only [hy, map_div, Finset.prod_div_distrib, h, div_one]
  have hab : aboveF (L := E) F (P.under (𝓞 F)) = {P, conjPrime₂ P} := by
    ext Q
    rw [GlobalTheory.Mem.ReadTwist.mem_above, Finset.mem_insert, Finset.mem_singleton]
    exact under_eq_iff hF hr hc P Q
  rw [e1, hab]
  by_cases hP : P = conjPrime₂ P
  · have h1 : P.valuation E (y : E) = 1 := hP ▸ hk
    have h2 : P.valuation E (z : E) = 1 := by
      have h3 := congrArg (P.valuation E) hyz
      rw [map_mul, ← valuation_conjP, hk, h1, mul_one] at h3
      exact h3.symm
    rw [← hP, Finset.pair_eq_singleton, Finset.prod_singleton, locK_unr (hun P hP.symm) h1, locK_unr (hun P hP.symm) h2]
  · have hs0 : star (y : E) ≠ 0 := star_ne_zero.2 y.ne_zero
    have h3 := split_unit hF hr hc hχ ht hP (y' := Units.mk0 _ hs0) rfl hk
    have e2 : y = z * Units.mk0 _ hs0 := Units.ext hyz
    rw [Finset.prod_pair hP, congrArg (χ.locK P) e2, map_mul, mul_assoc, h3, mul_one]

theorem inf_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  intro F E _ _ _ _ _ _ χ rep V x z hF hr hc hu hχ ht hun hrep hxz hV
  classical
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), P ∈ V.biUnion (aboveF (L := E) F) ↔ P.under (𝓞 F) ∈ V := fun P => by
    simp only [Finset.mem_biUnion, GlobalTheory.Mem.ReadTwist.mem_above, exists_eq_right']
  have h := GlobalTheory.HeckeProduct.productRule χ (V.biUnion (aboveF (L := E) F)) (fun P hP => (hV P fun e => hP ((hm P).2 e)).1) x
  have hfp : (∏ᶠ (P : HeightOneSpectrum (𝓞 E)) (_ : P ∉ V.biUnion (aboveF (L := E) F)), χ.val P ^ ordF P x) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun P => ?_
    by_cases hP : P ∈ V.biUnion (aboveF (L := E) F)
    · rw [finprod_eq_if, if_neg (not_not.2 hP)]
    rw [finprod_eq_if, if_pos hP, ordF, (hV P fun e => hP ((hm P).2 e)).2, WithZero.log_one, neg_zero, zpow_zero]
  have hpl : ∀ v ∈ V, ∏ Q ∈ aboveF (L := E) F v, χ.locK Q x = χ.locK (rep v) z := fun v _ => by
    have := place_prod hF hr hc hu hχ ht hun hxz (rep v)
    rwa [hrep] at this
  rw [hfp, mul_one, Finset.prod_biUnion, Finset.prod_congr rfl hpl] at h
  · exact h
  · intro v _ w _ hvw
    exact Finset.disjoint_left.2 fun P h1 h2 =>
      hvw ((GlobalTheory.Mem.ReadTwist.mem_above.1 h1).symm.trans (GlobalTheory.Mem.ReadTwist.mem_above.1 h2))

end GlobalTheory.NormOneProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker
open Formalism.L2.DIV hiding unifVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_productFormula_normOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (χ : Formalism.L2.Host.HChar E) (rep : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E)) (V : Finset (HeightOneSpectrum (𝓞 F))) (x z : Eˣ), (∀ y : F, star (algebraMap F E y) = algebraMap F E y) → Module.finrank F E = 2 → (∃ a : E, star a ≠ a) → (∀ P : HeightOneSpectrum (𝓞 E), ¬ (P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))).map (algebraMap (𝓞 F) (𝓞 E)) ≤ P.asIdeal ^ 2) → χ.TrivOn F → (∀ P, χ.TameAt P) → (∀ P, conjPrime₂ P = P → χ.UnrAt P) → (∀ v, (rep v).under (𝓞 F) = v) → (x : E) = z * star (x : E) → (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∉ V → χ.UnrAt P ∧ P.valuation E (x : E) = 1) → χ.inf x * ∏ v ∈ V, χ.locK (rep v) z = 1 := by
  first | exact @GlobalTheory.NormOneProd.inf_mul_prod | exact GlobalTheory.NormOneProd.inf_mul_prod | (intros; apply GlobalTheory.NormOneProd.inf_mul_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerp
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerpAllIff
noncomputable section

namespace GlobalTheory.UnitVectorPerpCompare

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem selfDual_iff (W : HSpace E) (L : Submodule (𝓞 E) W.V) :
    UnitVectorOrthogonal.IsSelfDualLat W L ↔ SelfDualLatticeComplements.IsSelfDualLattice W L := Iff.rfl

theorem ofKind_iff (W : HSpace E) (M P Q : ℕ) :
    UnitVectorOrthogonal.OfKind W M P Q ↔ SelfDualLatticeComplements.OfKind W M P Q :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem hasComplement_iff (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) :
    UnitVectorOrthogonal.HasComplement W x M' P' Q' ↔ SelfDualLatticeComplements.HasComplement W x M' P' Q' := by
  constructor
  · rintro ⟨L, hL, hx, hs, W', ι, hk, hi, hr, hm⟩
    exact ⟨L, W', ι, (selfDual_iff W L).1 hL, hx, (ofKind_iff _ _ _ _).1 hk, hi, hr, hm, hs⟩
  · rintro ⟨L, W', ι, hL, hx, hk, hi, hr, hm, hs⟩
    exact ⟨L, (selfDual_iff W L).2 hL, hx, hs, W', ι, (ofKind_iff _ _ _ _).2 hk, hi, hr, hm⟩


omit [NumberField E] [StarRing E] in
theorem forall_step_iff (P Q : ℕ) (C : E → ℕ → ℕ → Prop) :
    (∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' → C β P' Q') ↔
      (1 ≤ P → C 1 (P - 1) Q) ∧ (1 ≤ Q → C (-1) P (Q - 1)) := by
  constructor
  · intro h
    exact ⟨fun hP => h _ _ _ (Or.inl ⟨rfl, hP, rfl, rfl⟩),
      fun hQ => h _ _ _ (Or.inr ⟨rfl, hQ, rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ β P' Q' (⟨rfl, hP, rfl, rfl⟩ | ⟨rfl, hQ, rfl, rfl⟩)
    · exact h1 hP
    · exact h2 hQ

theorem conclusion_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

theorem over_iff : UnitVectorOrthogonal.UnitVectorPerpOver E ↔ SelfDualLatticeComplements.ExistsPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusion_iff W M P Q

end General

theorem unitVectorPerp_iff (D : D7) : UnitVectorOrthogonal.UnitVectorPerp D ↔ SelfDualLatticeComplements.UnitVectorPerp D :=
  @over_iff D.host.E _ _ D.host.cmStar

end GlobalTheory.UnitVectorPerpCompare

end
end

namespace GlobalTheory.UnitPerpObj

theorem unitVectorPerp (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements.UnitVectorPerp D :=
  (GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)

end GlobalTheory.UnitPerpObj
end
