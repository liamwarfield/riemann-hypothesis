module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem coh_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  intro R _ F U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F (sch.obj U) ι (fun i => sch.obj (V i)) (fun i => sch.map (j i)) ?_ n
  intro k
  exact GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U ι V j hc (yoneda.obj U) (𝟙 _) (fun i => yoneda.obj (V i)) (fun i => yoneda.map (j i))
    (fun _ => 𝟙 _) (fun i => IsPullback.of_vert_isIso (by simp))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  first | (exact @GlobalTheory.coh_coprod_bijective) | (exact GlobalTheory.coh_coprod_bijective) | (intros; apply GlobalTheory.coh_coprod_bijective  <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem acycF_of_pi_sh : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type)
    [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) →
    AcycF R (sp B) F := by
  intro R _ F ι _ T _ B _ ⟨e⟩ hT n hn
  obtain ⟨hc⟩ := GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv ι T B e
  have hbij := GlobalTheory.T.etaleSpaceCohomology_coprod_schemes_bijective R F (Spec (CommRingCat.of B)) ι (fun i => Spec (CommRingCat.of (T i)))
    (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))) hc n
  have hsub : ∀ i, Subsingleton (H R (sch.obj (Spec (CommRingCat.of (T i)))) F n) :=
    fun i => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf R (T i) (hT i) F n hn
  refine ⟨fun x y => hbij.1 ?_⟩
  funext i
  exact Subsingleton.elim _ _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRi
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_complete_dvr_of_finite_fractionRing_hom :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
      IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'),
      σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'),
        IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  intro V _ _ _ _ hV K' _ σ hσ
  letI : Algebra (FractionRing V) K' := σ.toAlgebra
  letI : Algebra V K' := (σ.comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional (FractionRing V) K' := hσ
  haveI := hV
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  let B := integralClosure V K'
  haveI : Module.Finite V B := IsIntegralClosure.finite V (FractionRing V) K' B
  haveI hBd : IsDiscreteValuationRing B := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) K'
  haveI : IsFractionRing B K' := integralClosure.isFractionRing_of_finite_extension (FractionRing V) K'
  have hinj : Function.Injective (algebraMap V B) := by
    intro x y h
    have h2 := congrArg (algebraMap B K') h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h2
    exact (σ.injective.comp (IsFractionRing.injective V (FractionRing V))) h2
  haveI : CharZero B := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul V B := (faithfulSMul_iff_algebraMap_injective V B).2 hinj
  haveI : Algebra.IsIntegral V B := IsIntegralClosure.isIntegral_algebra V K'
  haveI : IsLocalHom (algebraMap V B) := Algebra.IsIntegral.isLocalHom _ _
  let e : FractionRing B ≃ₐ[B] K' := IsLocalization.algEquiv (nonZeroDivisors B) (FractionRing B) K'
  refine ⟨B, inferInstance, inferInstance, hBd, inferInstance, algebraMap V B, e.symm.toRingHom,
    CompleteFiniteExtension.isAdicComplete_of_finite_local V B, hinj, inferInstance, ?_, fun a => ?_⟩
  · exact (inferInstance : Module.Finite V B)
  · change e.symm (algebraMap B K' (algebraMap V B a)) = _
    exact e.symm.commutes _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRiStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'), σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  first | exact @GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | exact GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | (intros; apply GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat
open NumberField IsDedekindDomain

namespace GlobalTheory.CommonValuation

theorem exists_eq_pow {R F : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
    (P : HeightOneSpectrum R) (u : Valuation F (WithZero (Multiplicative ℤ)))
    (h1 : ∀ r : R, u (algebraMap R F r) ≤ 1) (h2 : ∀ r : R, u (algebraMap R F r) < 1 ↔ r ∈ P.asIdeal) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : F, u x = P.valuation F x ^ e := by
  have hu : ∀ r : R, r ∉ P.asIdeal → u (algebraMap R F r) = 1 := fun r hr =>
    le_antisymm (h1 r) (not_lt.1 fun h => hr ((h2 r).1 h))
  have hone : ∀ x : F, P.valuation F x = 1 → u x = 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx.le
    have hn : n ∉ P.asIdeal := by
      rw [← P.valuation_eq_one_iff_notMem (K := F), ← h, map_mul, hx, one_mul]
      exact (P.valuation_eq_one_iff_notMem (K := F)).2 d.2
    have := congrArg u h
    rwa [map_mul, hu _ d.2, hu _ hn, mul_one] at this
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ' : P.valuation F (algebraMap R F π) = WithZero.exp (-1) := (P.valuation_of_algebraMap π).trans hπ
  have l1 : (WithZero.exp (-1) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπ0 : algebraMap R F π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ'
    exact WithZero.exp_ne_zero hπ'.symm
  have hlt : u (algebraMap R F π) < 1 := (h2 π).2 ((P.valuation_lt_one_iff_mem (K := F) π).1 (hπ' ▸ l1))
  have hu0 : u (algebraMap R F π) ≠ 0 := by simpa using hπ0
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (u (algebraMap R F π)) = -(e : ℤ) ∧ 0 < e := by
    rw [← WithZero.exp_log hu0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    exact ⟨(-WithZero.log (u (algebraMap R F π))).toNat, by omega, by omega⟩
  refine ⟨e, he.2, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [he.2.ne']
  have h0 : P.valuation F x ≠ 0 := by simpa using hx
  have h3 := hone (x * algebraMap R F π ^ WithZero.log (P.valuation F x)) (by
    rw [map_mul, map_zpow₀, hπ', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add]; simp)
  rw [map_mul, map_zpow₀, ← WithZero.exp_log hu0, he.1, ← WithZero.exp_zsmul,
    mul_eq_one_iff_eq_inv₀ WithZero.exp_ne_zero, ← WithZero.exp_neg] at h3
  rw [h3]
  nth_rewrite 2 [← WithZero.exp_log h0]
  rw [← WithZero.exp_nsmul]
  congr 1
  simp [mul_comm]

theorem le_one_of_ringOfIntegers {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ)
    (r : 𝓞 F) : u (algebraMap (𝓞 F) F r) ≤ 1 :=
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.1 r.isIntegral_coe.tower_top

theorem exists_centre {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (u : Valuation F Γ) :
    ∃ Q : Ideal (𝓞 F), Q.IsPrime ∧ ∀ r, r ∈ Q ↔ u (algebraMap (𝓞 F) F r) < 1 := by
  refine ⟨{ carrier := {r | u (algebraMap (𝓞 F) F r) < 1}
            add_mem' := fun {a b} ha hb => ?_
            zero_mem' := by simp
            smul_mem' := fun c r hr => ?_ }, ⟨?_, fun {a b} h => ?_⟩, fun _ => Iff.rfl⟩
  · change u _ < 1
    rw [map_add (f := _)]
    exact u.map_add_lt ha hb
  · change u _ < 1
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (le_one_of_ringOfIntegers u c)).trans_lt hr
  · rw [Ideal.ne_top_iff_one]
    change ¬ u _ < 1
    simp
  · by_contra! hn
    have ha : u (algebraMap _ F a) = 1 := le_antisymm (le_one_of_ringOfIntegers u a) (not_lt.1 hn.1)
    have hb : u (algebraMap _ F b) = 1 := le_antisymm (le_one_of_ringOfIntegers u b) (not_lt.1 hn.2)
    change u _ < 1 at h
    rw [map_mul, map_mul, ha, hb, mul_one] at h
    exact lt_irrefl _ h

end GlobalTheory.CommonValuation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OToSAlgebraMap
noncomputable section

open IsDedekindDomain NumberField Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.AdeleIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_tmul_mem {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    (1 : E) ⊗ₜ[F] y ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)

theorem oToS_algebraMap (r : 𝓞 F) :
    ((oToS F E (algebraMap (𝓞 F) (𝓞 E) r) : Formalism.L2.Herm.intAf F E) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      (1 : E) ⊗ₜ[F] (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) := by
  rw [oToS_coe]
  have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) r) = algebraMap F E (algebraMap (𝓞 F) F r) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    ← IsScalarTower.algebraMap_apply]

theorem resS_eq_zero (w : Pl E) (v : HeightOneSpectrum (𝓞 F))
    (hw : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal)
    {b : FiniteAdeleRing (𝓞 F) F} (hb : b ∈ intAd F) (hv : b v = 0) :
    resS F w ⟨_, one_tmul_mem hb⟩ = 0 := by
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  obtain ⟨r, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F d hd0 b hb
  have ev : b v = algebraMap (𝓞 F) (v.adicCompletion F) r + algebraMap (𝓞 F) (v.adicCompletion F) d * y v := by
    rw [e]; rfl
  have hr : r ∈ v.asIdeal := by
    rw [hv] at ev
    have e1 : algebraMap (𝓞 F) (v.adicCompletion F) r = -(algebraMap (𝓞 F) (v.adicCompletion F) d * y v) :=
      eq_neg_of_add_eq_zero_left ev.symm
    have e2 := congrArg Valued.v e1
    rw [Valuation.map_neg, Valuation.map_mul, Formalism.UG.P.csApprox_val_int, Formalism.UG.P.csApprox_val_int] at e2
    rw [← v.intValuation_lt_one_iff_mem] at hd ⊢
    rw [e2]
    have hy1 : Valued.v (y v) ≤ 1 := hy v
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hy1) hd
  have hz : ∀ x ∈ v.asIdeal, resS F w (oToS F E (algebraMap (𝓞 F) (𝓞 E) x)) = 0 := by
    intro x hx
    rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hw] at hx
    exact hx
  have key : (⟨_, one_tmul_mem hb⟩ : Formalism.L2.Herm.intAf F E) =
      oToS F E (algebraMap (𝓞 F) (𝓞 E) r) + oToS F E (algebraMap (𝓞 F) (𝓞 E) d) * ⟨_, one_tmul_mem hy⟩ := by
    apply Subtype.ext
    rw [Subring.coe_add, Subring.coe_mul, oToS_algebraMap, oToS_algebraMap]
    show (1 : E) ⊗ₜ[F] b = _ + _ * (1 : E) ⊗ₜ[F] y
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  rw [key, map_add (f := _), map_mul, hz r hr, hz d hd, zero_mul, add_zero]


open Classical in
def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => by
    show (if v ∈ S then 1 else 0) ∈ v.adicCompletionIntegers F
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem ind_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ind S v = if v ∈ S then 1 else 0 := rfl

theorem ind_mem (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S ∈ intAd F := by
  intro v
  show ind S v ∈ v.adicCompletionIntegers F
  rw [ind_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.AdeleIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdeal
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.FrameCong

theorem coord_mem_idS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (I : Ideal (𝓞 E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) :
    ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F) := by
  refine Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I,
    (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I,
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_
    · intro a ha u hu i
      have hu' : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨u, hu, rfl⟩
      have t := (hβ _).1 hu' i
      refine ⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have e : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k)) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by
        funext k
        show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · intro m1 m2 h1 h2 i
      obtain ⟨s1, hs1, e1⟩ := h1 i
      obtain ⟨s2, hs2, e2⟩ := h2 i
      refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
      have : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) =
          (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) +
            (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by
        funext k; simp [map_add (f := _)]
      rw [this, Matrix.mulVec_add, Pi.add_apply, e1, e2]
      rfl
  · intro i
    exact ⟨0, zero_mem _, by simp⟩
  · intro a b _ _ ha hb i
    obtain ⟨s1, hs1, e1⟩ := ha i
    obtain ⟨s2, hs2, e2⟩ := hb i
    refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply, e1, e2]
    rfl
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]
    rfl

theorem redFn_eq_one_of_congr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ →
    x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) →
    ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  intro F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP
  classical
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  apply Units.ext
  ext i j
  have hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine (hβ _).2 fun k => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  obtain ⟨s, hs, es⟩ := coord_mem_idS β Λ hβ I _ (hcong _ hv) i
  have hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) -
        β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) = (Y - 1) *ᵥ Pi.single j 1 := by
    have hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hcomp, Matrix.mulVec_single_one, Matrix.col_apply] at es
  have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hs' : (y.1 - 1) i j = s := Subtype.ext (e5.trans es)
  have hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal := hs' ▸ Ideal.map_mono hPP hs
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FrameCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameReductionEqOneOfCongruentModIdealStatement
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) → ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  first | exact @GlobalTheory.FrameCong.redFn_eq_one_of_congr | exact GlobalTheory.FrameCong.redFn_eq_one_of_congr | (intros; apply GlobalTheory.FrameCong.redFn_eq_one_of_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleOfEtaleAtPrime
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IndEtaleAtPrime

theorem isIndEtale_of_etale_atPrime (R C : Type) [CommRing R] [CommRing C] (P : Ideal R) [P.IsPrime]
    [Algebra (Localization.AtPrime P) C] [Algebra.Etale (Localization.AtPrime P) C] :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap (Localization.AtPrime P) C).comp
      (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let M := P.primeCompl
  let D0 := (Functor.const (Discrete PUnit.{1})).obj (CommRingCat.of R)
  let s0 : D0 ⟶ (Functor.const _).obj (CommRingCat.of R) := 𝟙 _
  have hs0 : IsColimit (Cocone.mk _ s0) := GlobalTheory.IndEtFactorLoc.constColim R
  obtain ⟨j, Aj, _, instA, hAj, ⟨e⟩⟩ := GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit
    (GlobalTheory.IndEtaleLoc.Idx D0 s0 M) (GlobalTheory.IndEtaleLoc.diag D0 s0 M)
    (Cocone.mk _ (GlobalTheory.IndEtaleLoc.toLoc (s := s0) (M := M) L))
    (GlobalTheory.IndEtaleLoc.isColimitToLoc L hs0) C
  let Re : Type := Localization.Away j.e
  letI : Algebra R Re := (inferInstance : Algebra (D0.obj j.j) (Localization.Away j.e))
  letI : Algebra Re L := (GlobalTheory.IndEtaleLoc.leg L j).toAlgebra
  letI : Algebra Re Aj := instA
  haveI : Algebra.Etale Re Aj := hAj
  let e0 : R := j.e
  have he0 : e0 ∈ M := j.mem
  haveI : IsLocalization (Submonoid.powers e0) Re :=
    (inferInstance : IsLocalization (Submonoid.powers j.e) (Localization.Away j.e))
  haveI : IsScalarTower R Re L := IsScalarTower.of_algebraMap_eq (fun r =>
    (GlobalTheory.IndEtaleLoc.leg_algebraMap (s := s0) (M := M) L j r).symm)
  haveI hLoc : IsLocalization (M.map (algebraMap R Re)) L :=
    IsLocalization.isLocalization_of_submonoid_le Re L (Submonoid.powers e0) M
      (Submonoid.powers_le.2 he0)
  let e' : L ⊗[Re] Aj ≃ₐ[L] C := e
  letI rA : Algebra Aj (L ⊗[Re] Aj) := Algebra.TensorProduct.rightAlgebra
  haveI hT : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re)))
      (L ⊗[Re] Aj) := IsLocalization.tensorRight _ _
  letI : Algebra Aj C := (e'.toRingHom.comp (algebraMap Aj (L ⊗[Re] Aj))).toAlgebra
  let eA : L ⊗[Re] Aj ≃ₐ[Aj] C := AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun _ => rfl)
  haveI hCloc : IsLocalization (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) C :=
    IsLocalization.isLocalization_of_algEquiv _ eA
  letI : Algebra R Aj := ((algebraMap Re Aj).comp (algebraMap R Re)).toAlgebra
  haveI : IsScalarTower R Re Aj := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale R Re :=
    (Algebra.Etale.of_isLocalizationAway j.e : Algebra.Etale (D0.obj j.j) (Localization.Away j.e))
  haveI : Algebra.Etale R Aj := Algebra.Etale.comp R Re Aj
  letI : Algebra R C := ((algebraMap L C).comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R Aj C := IsScalarTower.of_algebraMap_eq (fun r => by
    have key : ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r)) =
        algebraMap L (L ⊗[Re] Aj) (algebraMap R L r) := by
      rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply R Re L]
      generalize algebraMap R Re r = c
      rw [Algebra.algebraMap_eq_smul_one (A := Aj) c, Algebra.algebraMap_eq_smul_one (A := L) c,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl
    show algebraMap L C (algebraMap R L r) = e' ((1 : L) ⊗ₜ[Re] algebraMap Re Aj (algebraMap R Re r))
    rw [key, AlgEquiv.commutes])
  exact GlobalTheory.IndEtaleLoc.isIndEtale_of_isLocalization R Aj C
      (Algebra.algebraMapSubmonoid Aj (M.map (algebraMap R Re))) (GlobalTheory.EtC.indEt_of_etale R Aj)

theorem indEt_of_indEt_atPrime : ∀ (B O : Type) [CommRing B] [CommRing O] (P : Ideal B) [P.IsPrime]
    [Algebra (Localization.AtPrime P) O] [Algebra B O] [IsScalarTower B (Localization.AtPrime P) O],
    IndEt (Localization.AtPrime P) O → IndEt B O := by
  intro B O _ _ P _ _ _ _ h
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  unfold IndEt GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  obtain ⟨J, _, _, D, t, s, hs, hj⟩ := h
  refine ⟨J, inferInstance, inferInstance, D,
    (Functor.const J).map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime P))) ≫ t, s, hs,
    fun i => ⟨?_, ?_⟩⟩
  · letI : Algebra (Localization.AtPrime P) (D.obj i) := (t.app i).hom.toAlgebra
    haveI : Algebra.Etale (Localization.AtPrime P) (D.obj i) := (hj i).1
    exact isIndEtale_of_etale_atPrime B (D.obj i) P
  · have h2 := (hj i).2
    show CommRingCat.ofHom (algebraMap B (Localization.AtPrime P)) ≫ t.app i ≫ s.app i = _
    rw [h2]
    ext x
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime P) O x).symm

end GlobalTheory.IndEtaleAtPrime

end
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.StrictHensPrime

theorem exists_sh_indEt (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime] :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧
      (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  classical
  obtain ⟨S, _, _, hH, hloc, hsep, -, -, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime p)
      (SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p)))
  let _ : Algebra A S := ((algebraMap (Localization.AtPrime p) S).comp
    (algebraMap A (Localization.AtPrime p))).toAlgebra
  have _ : IsScalarTower A (Localization.AtPrime p) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hI : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime p) S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ B q.primeCompl)
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⟨hH, hsep⟩, ?_, ?_⟩
  · exact IndEtaleAtPrime.indEt_of_indEt_atPrime A S p hI
  · rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.StrictHensPrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.FerrandPush

section One
variable {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]

theorem isHomeomorph : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

def upOpen (U : Y₀.Opens) : Y₁.Opens := ⟨i '' (U : Set Y₀), (isHomeomorph i).isOpenMap _ U.2⟩

theorem preimage_upOpen (U : Y₀.Opens) : i ⁻¹ᵁ upOpen i U = U := by
  ext x
  change i x ∈ i '' (U : Set Y₀) ↔ x ∈ U
  exact (isHomeomorph i).injective.mem_set_image

theorem upOpen_preimage (V : Y₁.Opens) : upOpen i (i ⁻¹ᵁ V) = V := by
  ext y
  change y ∈ i '' (i ⁻¹' (V : Set Y₁)) ↔ y ∈ V
  rw [Set.image_preimage_eq _ i.surjective]
  rfl

theorem upOpen_mono : Monotone (upOpen i) := fun _ _ h ↦ Set.image_mono h

def res (U : Y₀.Opens) : Γ(Y₁, upOpen i U) ⟶ Γ(Y₀, U) :=
  i.appLE (upOpen i U) U (preimage_upOpen i U).ge

theorem res_naturality {U V : Y₀.Opens} (h : U ≤ V) :
    Y₁.presheaf.map (homOfLE (upOpen_mono i h)).op ≫ res i U =
      res i V ≫ Y₀.presheaf.map (homOfLE h).op := by
  simp only [res, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end One

section Two
variable {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁]
  [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂]

abbrev cone (U : Y₀.Opens) : PullbackCone (res i₁ U) (res i₂ U) :=
  CommRingCat.pullbackCone (res i₁ U) (res i₂ U)

def coneIsLimit (U : Y₀.Opens) : IsLimit (cone i₁ i₂ U) :=
  CommRingCat.pullbackConeIsLimit _ _

def fibMap {U V : Y₀.Opens} (h : U ≤ V) : (cone i₁ i₂ V).pt ⟶ (cone i₁ i₂ U).pt :=
  PullbackCone.IsLimit.lift (coneIsLimit i₁ i₂ U)
    ((cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op)
    ((cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op)
    (by rw [Category.assoc, Category.assoc, res_naturality i₁ h, res_naturality i₂ h,
      (cone i₁ i₂ V).condition_assoc])

@[reassoc (attr := simp)]
theorem fibMap_fst {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).fst =
    (cone i₁ i₂ V).fst ≫ Y₁.presheaf.map (homOfLE (upOpen_mono i₁ h)).op :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

@[reassoc (attr := simp)]
theorem fibMap_snd {U V : Y₀.Opens} (h : U ≤ V) : fibMap i₁ i₂ h ≫ (cone i₁ i₂ U).snd =
    (cone i₁ i₂ V).snd ≫ Y₂.presheaf.map (homOfLE (upOpen_mono i₂ h)).op :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

def fib : Y₀.Opensᵒᵖ ⥤ CommRingCat.{0} where
  obj U := (cone i₁ i₂ U.unop).pt
  map f := fibMap i₁ i₂ f.unop.le
  map_id U := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ U.unop)
    (by simp [homOfLE_refl]) (by simp [homOfLE_refl])
  map_comp f g := PullbackCone.IsLimit.hom_ext (coneIsLimit i₁ i₂ _)
    (by simp [← Functor.map_comp]; rfl) (by simp [← Functor.map_comp]; rfl)

def fibπ : fib i₁ i₂ ⟶ Y₀.presheaf where
  app U := (cone i₁ i₂ U.unop).fst ≫ res i₁ U.unop
  naturality U V f := by
    change fibMap i₁ i₂ f.unop.le ≫ _ ≫ _ = _
    rw [fibMap_fst_assoc, res_naturality]
    rfl

def good : Set Y₀.Opens :=
  {U | IsAffineOpen U ∧ IsAffineOpen (upOpen i₁ U) ∧ IsAffineOpen (upOpen i₂ U)}

end Two

end GlobalTheory.FerrandPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNeighbourhoodKillsClass
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IndEtaleComp
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GroupActionHaarScalingContinuous
open CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.IndEtaleComp

theorem isIndEtale_of_model (X E Y G F : Type) [CommRing X] [CommRing E] [CommRing Y] [CommRing G]
    [CommRing F] [Algebra X E] [Algebra X Y] [Algebra E Y] [IsScalarTower X E Y]
    [Algebra.Etale X E] [Algebra E G] [Algebra.Etale E G] [Algebra Y F]
    (e : Y ⊗[E] G ≃ₐ[Y] F) (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap X Y)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale ((algebraMap Y F).comp (algebraMap X Y)) := by
  have h1 := GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale X E Y h
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left E Y G h1
  letI : Algebra G F :=
    ((e : Y ⊗[E] G →+* F).comp (Algebra.TensorProduct.includeRight : G →ₐ[E] Y ⊗[E] G).toRingHom).toAlgebra
  let e' : G ⊗[E] Y ≃ₐ[G] F :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm E G Y).toRingEquiv.trans e.toRingEquiv)
      (fun g => rfl)
  have h3 := GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e' h2
  have h4 : RingHom.Etale ((algebraMap E G).comp (algebraMap X E)) :=
    RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 inferInstance)
      (RingHom.etale_algebraMap.2 inferInstance)
  have h5 := GlobalTheory.EtC.isIndEtale_comp_etale _ h4 _ h3
  have h6 : (algebraMap Y F).comp (algebraMap X Y) =
      (algebraMap G F).comp ((algebraMap E G).comp (algebraMap X E)) := by
    ext x
    change _ = e ((1 : Y) ⊗ₜ[E] algebraMap E G (algebraMap X E x))
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply E Y (Y ⊗[E] G),
      e.commutes, ← IsScalarTower.algebraMap_apply X E Y]
    rfl
  rw [h6]
  exact h5

theorem isIndEtale_etale_comp {X Y F : Type} [CommRing X] [CommRing Y] [CommRing F]
    (f : X →+* Y) (g : Y →+* F) (hf : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f) (hg : g.Etale) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  have hf' := hf
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hf'
  letI : Algebra Y F := g.toAlgebra
  haveI : Algebra.Etale Y F := hg
  obtain ⟨i, G, _, _, hG, ⟨e⟩⟩ :=
    GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D (Cocone.mk (CommRingCat.of Y) t) hs F
  letI : Algebra (D.obj i) Y := (t.app i).hom.toAlgebra
  letI : Algebra X (D.obj i) := (s.app i).hom.toAlgebra
  letI : Algebra X Y := f.toAlgebra
  haveI : Algebra.Etale X (D.obj i) := (hj i).1
  haveI : IsScalarTower X (D.obj i) Y := IsScalarTower.of_algebraMap_eq (fun x =>
    (congrArg (fun φ : CommRingCat.of X ⟶ CommRingCat.of Y => φ.hom x) (hj i).2).symm)
  exact isIndEtale_of_model X (D.obj i) Y G F e hf

theorem isIndEtale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  intro X Y Z _ _ _ f g hf hg
  have hp : RingHom.toMorphismProperty @RingHom.Etale ≤
      MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0} := by
    intro X Y f hf
    refine CommRingCat.isFinitelyPresentable_hom f ?_
    letI := f.hom.toAlgebra
    haveI : Algebra.Etale X Y := hf
    exact RingHom.finitePresentation_algebraMap.2 inferInstance
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale
  rw [← MorphismProperty.ind_ind hp]
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom f) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · exact isIndEtale_etale_comp (F := D.obj j) f (s.app j).hom hf (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom f ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp f)
    rw [h2]
    rfl

end GlobalTheory.IndEtaleComp
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  first | (exact @GlobalTheory.IndEtaleComp.isIndEtale_comp) | (exact GlobalTheory.IndEtaleComp.isIndEtale_comp) | (intros; apply GlobalTheory.IndEtaleComp.isIndEtale_comp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIntegerRingAlmostAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximal
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.HensMax

open IsLocalRing

theorem comap_maximalIdeal_of_localHom {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : (maximalIdeal S).comap f = maximalIdeal R := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h hx => h (hx.map f), fun h hx => h (isUnit_of_map_unit f x hx)⟩

theorem isSepClosed_of_ringEquiv {K L : Type} [Field K] [Field L] [IsSepClosed K] (e : K ≃+* L) : IsSepClosed L := by
  refine IsSepClosed.of_exists_root L fun p hm hirr hsep => ?_
  have hq : (p.map e.symm.toRingHom).Separable := hsep.map
  have hdeg : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg hq
  refine ⟨e x, ?_⟩
  have := congrArg (e : K →+* L) hx
  rw [Polynomial.eval_map, map_zero, Polynomial.hom_eval₂] at this
  have h2 : (e : K →+* L).comp e.symm.toRingHom = RingHom.id L := by ext; simp
  rw [h2, Polynomial.eval₂_id] at this
  exact this

end GlobalTheory.HensMax


open IsLocalRing in
theorem GlobalTheory.HensMax.exists_strictHens_of_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal],
    IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O),
    SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  intro B _ P _ hsep
  obtain ⟨S, _, _, hH, hloc, -, -, hbij, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.Henselisation.exists_henselisation (Localization.AtPrime P)
  letI : Algebra B S := ((algebraMap (Localization.AtPrime P) S).comp (algebraMap B (Localization.AtPrime P))).toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime P) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨S, inferInstance, inferInstance, ⟨hH, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.HensMax.isSepClosed_of_ringEquiv (RingEquiv.ofBijective _ hbij)
  · have hRS : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime P) S) := by
      refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
      obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hSi i
      exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
        (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ A q.primeCompl)
    have hBR : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap B (Localization.AtPrime P)) :=
      GlobalTheory.StrictHensUnion.indEtale_localization_of_etale B B P.primeCompl
    show GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap B S)
    rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime P) S]
    exact GlobalTheory.T.ind_etale_comp _ _ _ _ _ hBR hRS
  · intro Q hQ
    obtain rfl : Q = maximalIdeal S := IsLocalRing.eq_maximalIdeal hQ
    refine ⟨?_, fun o => ?_⟩
    · rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime P) S, ← Ideal.comap_comap,
        GlobalTheory.HensMax.comap_maximalIdeal_of_localHom]
      exact Localization.AtPrime.under_maximalIdeal (I := P)
    · obtain ⟨y, hy⟩ := hbij.2 (residue S o)
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨b, hb⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).surjective
        (Ideal.Quotient.mk _ r)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, Ideal.Quotient.eq] at hb
      refine ⟨b, ?_⟩
      have h1 : residue _ (algebraMap B (Localization.AtPrime P) b) = residue _ r := by
        rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
        exact hb
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hy, IsScalarTower.algebraMap_apply B (Localization.AtPrime P) S,
        ← ResidueField.map_residue, h1, sub_self]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximalStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictHenselization_at_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O), SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  first | (exact @GlobalTheory.HensMax.exists_strictHens_of_maximal) | (exact GlobalTheory.HensMax.exists_strictHens_of_maximal) | (intros; apply GlobalTheory.HensMax.exists_strictHens_of_maximal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesOnEtaleNeighbourhood
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittExtensionDiagonalGramTuples
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_kill_of_indEt : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  intro q B O _ _ _ hq hO n i y hy
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt B O hO
  have hc' : IsColimit ((Under.forget (CommRingCat.of B)).mapCocone (Cocone.mk _ ι)) :=
    isColimitOfPreserves (Under.forget _) hc
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have hqj : IsUnit ((q : ((D ⋙ Under.forget _).obj j))) := by
    have := hq.map (D.obj j).hom.hom
    rw [map_natCast] at this
    exact this
  have hyj : pull _ (spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom) _ _
      (pull _ (spMap (D.obj j).hom.hom) _ _ y) = 0 := by
    erw [← pull_comp]
    have hw : (D.obj j).hom ≫ (ι.app j).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app j)
    have : spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B O) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hw
    erw [this]; exact hy
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ Under.forget _) _ hc' n i).2 j _ hqj hyj
  erw [← pull_comp] at hk
  have hwk : (D.obj j).hom ≫ (D.map f).right = (D.obj k).hom := by simpa using Under.w (D.map f)
  letI : Algebra B (D.obj k).right := (D.obj k).hom.hom.toAlgebra
  refine ⟨(D.obj k).right, inferInstance, this, het k, ⟨(ι.app k).right.hom, fun b => ?_⟩, ?_⟩
  · have hw : (D.obj k).hom ≫ (ι.app k).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app k)
    exact congrArg (fun g => g.hom b) hw
  · have : spMap ((D ⋙ Under.forget _).map f).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B (D.obj k).right) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hwk
    erw [this] at hk; exact hk

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishes_on_etale_neighbourhood : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.exists_etale_kill_of_indEt) | (exact GlobalTheory.EtC.exists_etale_kill_of_indEt) | (intros; apply GlobalTheory.EtC.exists_etale_kill_of_indEt  <;> assumption)
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.OneCoh

theorem dies_on_etale_with_point (q : ℕ) [NeZero q] (B : Type) [CommRing B] (hq : IsUnit (q : B))
    (P : Ideal B) [P.IsMaximal] (hsep : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (m i : ℤ) (hm : 0 < m) (y : Ht q (sp B) m i) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D),
      Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧
      pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  obtain ⟨O, _, _, hSH, hInd, hO⟩ := GlobalTheory.T.exists_strictHenselization_at_maximal B P hsep
  have hsub : Subsingleton (Ht q (sp O) m i) := GlobalTheory.EtC.b2 (ZMod q) O hSH (tw q i) m hm
  have h0 : pull _ (spMap (algebraMap B O)) _ _ y = 0 := Subsingleton.elim _ _
  obtain ⟨D, _, _, _, φ, hD⟩ := GlobalTheory.T.vanishes_on_etale_neighbourhood q B O hq hInd m i y h0
  obtain ⟨hH, -⟩ := hSH
  haveI : IsLocalRing O := hH.toIsLocalRing
  obtain ⟨hP, hres⟩ := hO (IsLocalRing.maximalIdeal O) inferInstance
  refine ⟨D, inferInstance, inferInstance, inferInstance, (IsLocalRing.maximalIdeal O).comap φ, ?_, ?_, ?_, hD⟩
  · exact Ideal.comap_isPrime _ _
  · rw [← hP]
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
  · intro d
    obtain ⟨b, hb⟩ := hres (φ d)
    refine ⟨b, ?_⟩
    rw [Ideal.mem_comap, map_sub, AlgHom.commutes]
    exact hb

end GlobalTheory.EtC.OneCoh

theorem GlobalTheory.EtC.oneCoh_main : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 :=
  fun q _ B _ hq P _ hsep m i hm y => GlobalTheory.EtC.OneCoh.dies_on_etale_with_point q B hq P hsep m i hm y
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_neighbourhood_kills_class : ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) → ∀ (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∀ (m i : ℤ), 0 < m → ∀ y : Ht q (sp B) m i, ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (Q : Ideal D), Q.IsPrime ∧ Q.comap (algebraMap B D) = P ∧ (∀ d : D, ∃ b : B, d - algebraMap B D b ∈ Q) ∧ pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.oneCoh_main) | (exact GlobalTheory.EtC.oneCoh_main) | (intros; apply GlobalTheory.EtC.oneCoh_main <;> assumption)
end
