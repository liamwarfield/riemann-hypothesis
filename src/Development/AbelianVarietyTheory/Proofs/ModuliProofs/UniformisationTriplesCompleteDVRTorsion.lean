module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.isAdmissible_of_complete_DVR_charZero (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : LN.CDvr V) :
    LN.admitted V (IsLocalRing.maximalIdeal V) := by
  have := hV.1
  have := hV.2.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hV.2.1, hV.2.2, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  infer_instance

theorem LN.uDvrSt_holds : GlobalTheory.LN.UDvrSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  intro E _ _ _ H V _ _ _ hV t hp hs
  have := hV.1
  exact GlobalTheory.T.exists_uniformisation_complete_local_normal_prime L L2 L3 L4 L5 LN.ega_holds GlobalTheory.T.uniformisation_completeDVR GlobalTheory.T.linearUniformisation_triples_torsion E H V _ (LN.isAdmissible_of_complete_DVR_charZero V hV)
    (by letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V); infer_instance) t hp hs
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt L L2 E H V t hp)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_triples_complete_DVR_torsion : GlobalTheory.LN.UDvrSt := by
  first | exact @GlobalTheory.LN.uDvrSt_holds | exact GlobalTheory.LN.uDvrSt_holds | (intros; apply GlobalTheory.LN.uDvrSt_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeL
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeL
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelUniversal

theorem isAlgebraic_of_injective {p M : ℕ} (hM : M ≠ 0) {o : Type} [CommRing o] (i : o →+* ZP p M)
    (hi : Function.Injective i) : Algebra.IsAlgebraic ℤ o := by
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  refine ⟨fun x => ?_⟩
  rw [← isAlgebraic_algHom_iff ((ZP p M).subtype.comp i).toIntAlgHom (Subtype.val_injective.comp hi),
    IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  exact hle (i x).2

theorem exists_siegelFamily_siegRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp.symm (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst
    (isAlgebraic_of_injective (by omega) i hinj) F
  obtain ⟨F', -⟩ := F.exists_baseChange i hinj hζ
  obtain ⟨Ag', -, H⟩ := F'.exists_sRep_siegRep (by omega) Ag hAg
  exact ⟨Ag', H⟩

end GlobalTheory.ZM.SiegelUniversal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalQuasiProjectiveSiegelFamilyLargeLStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  first | exact @GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | exact GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep | (intros; apply GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep <;> assumption)
end
end
