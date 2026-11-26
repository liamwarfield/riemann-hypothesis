module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsTwistedDefiniteFormsRational
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalRowSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumsConjugateTwistsConjugateExpansions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeFockPolysSpanIntegralForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem exists_extend_fractionRing {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (e : FractionRing A →+* ℂ) :
    ∃ ε : FractionRing B →+* ℂ, ε.comp (algebraMap A (FractionRing B)) = e.comp (algebraMap A (FractionRing A)) := by
  letI : Algebra A ℂ := (e.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2
    (e.injective.comp (IsFractionRing.injective A (FractionRing A)))
  haveI : FaithfulSMul A (FractionRing B) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B _
  let φ : FractionRing B →ₐ[A] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem exists_extends_and_emb : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  intro D c w ρ hρ
  haveI := c.Oe_fin w
  refine ⟨exists_extend_fractionRing (c.Oe_inj w) (ρ.ek (c.twI w) (c.sd w) (c.k' w)), fun hT ε hε x => ?_⟩
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w))
    ((if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have h0 : (if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x * algebraMap _ _ z = algebraMap _ _ y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have h1 := congrArg ε (hT.embedding_baseField_condition w x y z hz0 h0)
  have key : ∀ t : D.ntw.O (c.twI w), ε (algebraMap (c.Oe w) (FractionRing (c.Oe w))
      (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap _ (D.ntw.Ok (c.twI w) (c.k' w)) t))) =
      ρ.eO (c.twI w) (c.sd w) t := fun t => by
    rw [← IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), hε.apply, hρ.ek_e]
  rw [map_mul, key, key] at h1
  rw [← hρ.e_LL0 (c.twI w) (c.sd w) x]
  let m : FractionRing (D.ntw.O0 (c.twI w)) →+* FractionRing (D.ntw.O (c.twI w)) := IsFractionRing.map (D.ntw.O_inj (c.twI w))
  have hm : ∀ t, ρ.e (c.twI w) (c.sd w) (m (algebraMap _ _ t)) =
      ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) t) := fun t =>
    congrArg (ρ.e (c.twI w) (c.sd w)) (IsLocalization.map_eq _ t)
  have h2 := congrArg (fun t => ρ.e (c.twI w) (c.sd w) (m t)) h0
  simp only [map_mul, hm] at h2
  have hne : ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) ≠ 0 := by
    rw [← hm]
    exact (map_ne_zero _).2 ((map_ne_zero m).2 hz1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end GlobalTheory.PlaceRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtensionComplexDataEmbeddingRestrictCoeffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  first | exact @GlobalTheory.PlaceRead.exists_extends_and_emb | exact GlobalTheory.PlaceRead.exists_extends_and_emb | (intros; apply GlobalTheory.PlaceRead.exists_extends_and_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenFieldFormsProportionalOfReadings
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugationScaledCoordsIntegralFormsTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugationScaledCoordsIntegralFormsTwist
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceConj

theorem conj_lat : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  intro D j B hB hlam Φ κ hκ0 hval hκ τ hτ ψ ψ' hψ hψ' hcc hf
  have huq := GlobalTheory.CoefLatConj.existsUnique_eq Φ hB hlam hκ0 hval hκ
  have hinj : Function.Injective Φ := fun x y hxy => (huq (Φ x) (hval x)).unique rfl hxy
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hinj)
  have hπx : ∀ x, π (Φ x) = x := fun x => LinearMap.congr_fun hπ x
  have hπv : ∀ P ∈ B.valSpace, Φ (π P) = P := fun P hP => by
    obtain ⟨x, rfl, -⟩ := huq P hP
    rw [hπx]
  let C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j :=
    { toFun := fun F h => Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)))
      map_add' := fun F G => by
        funext h
        simp only [Pi.add_apply, map_add (f := _), smul_add]
      map_smul' := fun a F => by
        funext h
        simp only [Pi.smul_apply, map_smul, map_smulₛₗ, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hC : ∀ F h, C F h = Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h))) := fun _ _ => rfl
  have hconjAt : ∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) := fun F hF h =>
    ⟨π (F h), GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j) (π (F h)), rfl, (hπv _ (hF h)).symm, hC F h⟩
  refine ⟨C, fun F hF => ⟨hconjAt F hF, fun h0 => ?_⟩, fun O hO => ?_⟩
  · funext h
    have e := congrFun h0 h
    rw [hC, Pi.zero_apply, ← map_zero Φ] at e
    have e1 := hinj e
    have hc : τ κ / κ ≠ 0 := div_ne_zero ((map_ne_zero _).2 hκ0) hκ0
    rw [smul_eq_zero] at e1
    have e2 : π (F h) = 0 := by
      rcases e1 with e1 | e1
      · exact absurd e1 hc
      · have := congrArg (GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j)) e1
        rwa [GlobalTheory.CoefLatConj.mapVV_symm_mapVV, map_zero] at this
    rw [Pi.zero_apply, ← hπv _ (hF h), e2, map_zero]
  · have hτ' : ∀ a, τ.symm (embLL0 D a) = embLL0 D a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hO' : IsCoefRing (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) :=
      ⟨hO.emb, fun a => Subring.mem_map.2 ⟨_, hO.int a, hτ _⟩⟩
    have hOO : (O.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = O := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    ext F'
    constructor
    · rintro ⟨F, hF, rfl⟩
      have hFv : ∀ h, F h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF).1).1
      exact GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) O hO τ hτ ψ ψ' hψ hψ' hcc hf
        F (C F) (hconjAt F hFv) hF
    · intro hF'
      have hF'v : ∀ h, F' h ∈ B.valSpace := ((Base.mem_formsC B).1 ((Base.mem_mtLat B _ _ _).1 hF').1).1
      let F : Amb D j := fun h => Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))
      have hFm : F ∈ B.mtLat (embLL0 D) (labLL0 D) O ψ := by
        have key := GlobalTheory.MtLatConj.mtLat_conj D j B hB hlam Φ κ hκ0 hval hκ _ (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) hO'
          τ.symm hτ' ψ' ψ hψ' hψ hcc.symm hf.symm F' F
          (fun h => ⟨π (F' h), GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)), rfl, (hπv _ (hF'v h)).symm, rfl⟩) hF'
        rwa [hOO] at key
      refine ⟨F, hFm, funext fun h => ?_⟩
      rw [hC]
      change Φ ((τ κ / κ) • GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j)
        (π (Φ ((τ.symm κ / κ) • GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D j) (π (F' h)))))) = F' h
      rw [hπx, map_smulₛₗ (GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D j))]
      have e3 := GlobalTheory.CoefLatConj.mapVV_symm_mapVV (lamV D j) τ.symm (π (F' h))
      rw [RingEquiv.symm_symm] at e3
      rw [e3, smul_smul]
      have : τ κ / κ * (τ (τ.symm κ / κ)) = 1 := by
        rw [map_div₀, RingEquiv.apply_symm_apply]
        have : τ κ ≠ 0 := (map_ne_zero _).2 hκ0
        field_simp
      rw [RingHom.coe_coe, this, one_smul, hπv _ (hF'v h)]

end GlobalTheory.PlaceConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugationScaledCoordsIntegralFormsTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist : ∀ (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → B.w.lam = lamV D j → ∀ (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) →
  (∀ x : VsV D j ℂ, harmFn (Wc D j).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) →
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ →
  ∃ C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j, (∀ F, (∀ h, F h ∈ B.valSpace) → ConjAt Φ κ τ F (C F) ∧ (C F = 0 → F = 0)) ∧
    ∀ O : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → C '' (B.mtLat (embLL0 D) (labLL0 D) O ψ : Set (Amb D j)) = (B.mtLat (embLL0 D) (labLL0 D) (O.map (τ : ℂ →+* ℂ)) ψ' : Set (Amb D j)) := by
  first | exact @GlobalTheory.PlaceConj.conj_lat | exact GlobalTheory.PlaceConj.conj_lat | (intros; apply GlobalTheory.PlaceConj.conj_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceUnit

theorem card_residueField_ne_zero {E : Type} [Field E] [NumberField E] (P : Pl E) : Nat.card (kP P) ≠ 0 := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  exact Nat.card_pos.ne'

theorem card_residueField_mem {E : Type} [Field E] [NumberField E] (P : Pl E) : ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := P.asIdeal.finiteQuotientOfFreeOfNeBot P.ne_bot
  letI : Fintype (kP P) := Fintype.ofFinite _
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] (P : Pl E) {q l : ℕ} (h : Nat.Coprime q l)
    (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hl
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((l : ℕ) : 𝓞 E)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hl)

theorem not_mem_of_pD {D : D7} (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  have h : P ∈ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← D.ntw.pD_eq i]; exact hP
  have hl : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  refine not_mem_of_coprime P ?_ h
  split_ifs with e
  · exact (Nat.coprime_primes D.host.pde'_prime hl).2 (e ▸ D.host.pde_ne.symm)
  · exact (Nat.coprime_primes D.host.pde_prime hl).2 (Ne.symm e)

theorem isUnit_card_residueField_Oe {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) {P : Pl D.host.E}
    (hl : ((D.ntw.l (c.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) : IsUnit ((Nat.card (kP P) : ℕ) : c.Oe w) := by
  haveI := D.ntw.Ok_fin (c.twI w) (c.k' w)
  have h : IsUnit ((Nat.card (kP P) : ℕ) : D.ntw.Ok (c.twI w) (c.k' w)) :=
    GlobalTheory.ResidueUnit.isUnit_of_coprime _ _ (GlobalTheory.ResidueUnit.card_residueField_coprime P _ (D.ntw.lPrime _).out hl)
      (GlobalTheory.ResidueUnit.natCast_mem_maximalIdeal_of_finite (O := D.ntw.O (c.twI w)) _ (D.ntw.O_l _))
  simpa using h.map (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w))

theorem tupPrime_isUnit : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι
  have hQ := (H.tup ι hι).2
  refine ⟨?_, fun P hP => ?_, ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hq
    exact card_residueField_ne_zero P
  · obtain ⟨m, hm⟩ : Nat.card (kP P) ∣ GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) :=
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hP)
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (card_residueField_mem P)
  · rw [GlobalTheory.TwistField.tupPrime, Nat.cast_prod]
    refine IsUnit.prod_iff.2 fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine isUnit_card_residueField_Oe c w ?_
    rw [hQ, Finset.mem_union] at hP
    rcases hP with hP | hP
    · rw [Z.good.delta] at hP
      exact not_mem_of_pD _ (mem_half.1 hP).1
    · exact fun h => Finset.disjoint_left.1 H.ok.2.1 (mem_half.1 hP).1 (D.ntw.twistExcludedPlaces_contains_residueChar _ h)

end GlobalTheory.PlaceUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitPrimeProductOfTwistedPlaceTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) ≠ 0 ∧ (∀ P ∈ X.R.Q (Y.tupT (D.what₂.muTw w)), ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) ∧
  IsUnit ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : c.Oe w) := by
  first | exact @GlobalTheory.PlaceUnit.tupPrime_isUnit | exact GlobalTheory.PlaceUnit.tupPrime_isUnit | (intros; apply GlobalTheory.PlaceUnit.tupPrime_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientLatticeEqSmallCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientLatticeEqSmallCoefficientField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceSmall

section BaseChange

variable {E K₀ K ι : Type} [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Fintype ι]
  {n : ℕ}

theorem map_mem_nabAtr (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : Submodule.IsFullLattice E M) {x : VV K₀ lam} (hx : x ∈ nabAtr emb lam M) :
    (⟨MvPolynomial.map f x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV f lam _ x.2⟩ : VV K lam) ∈
      nabAtr (fun τ => f.comp (emb τ)) lam M := by
  classical
  unfold nabAtr nabK at hx ⊢
  rw [Submodule.mem_comap] at hx ⊢
  change MvPolynomial.map f x.1 ∈ nabP lam fun τ => dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)
  change x.1 ∈ nabP lam (fun τ => dualFr (tauLat emb τ M)) at hx
  refine GlobalTheory.TransLattice.mem_of_forall_mem_locP _ fun w => ?_
  obtain ⟨w₀, hw₀⟩ : ∃ Q : HeightOneSpectrum (𝓞 K₀),
      ∀ r : 𝓞 K₀, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom f r ∈ w.asIdeal := by
    refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, fun h => ?_⟩, fun _ => Iff.rfl⟩
    have h1 : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K₀) ∈ w.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact w.ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))
  have hw : ∀ t : 𝓞 K₀, t ∉ w₀.asIdeal → RingOfIntegers.mapRingHom f t ∉ w.asIdeal :=
    fun t ht h => ht ((hw₀ t).2 h)
  obtain ⟨hLoc, -, -⟩ := GlobalTheory.TransLoc.nabDelLoc_free_leVV
  have hT : ∀ τ, Submodule.IsFullLattice K₀ (tauLat emb τ M) := fun τ => tauLatLattice E K₀ ι n emb τ M hM
  choose C hC using fun τ => basisAtEx K₀ n (tauLat emb τ M) (hT τ) w₀
  let B₀ : ι → GL (Fin n) K₀ := fun τ => inside₂ K₀ n (C τ)
  have hB₀ : ∀ τ, IsBasisAt w₀ (dualFr (tauLat emb τ M)) (B₀ τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w₀ (hT τ).fg (hC τ)
  have hB : ∀ τ, IsBasisAt w (dualFr (tauLat (fun τ => f.comp (emb τ)) τ M)) (Formalism.UG.bc f (B₀ τ)) := fun τ =>
    GlobalTheory.NabBC.isBasisAt_dualFr_tauLat_comp f emb τ M hM w₀ w hw (C τ) (hC τ)
  have L1 := (hLoc K ι n lam _ (fun τ => dualFr_tauLat_isLattice (fun τ => f.comp (emb τ)) τ M hM) w _ hB).1
  have L0 := (hLoc K₀ ι n lam _ (fun τ => dualFr_tauLat_isLattice emb τ M hM) w₀ B₀ hB₀).1
  have hx0 : x.1 ∈ Formalism.HermitianLatticesTheory.localization₂ w₀.asIdeal (nabP lam fun τ => dualFr (tauLat emb τ M)) :=
    GlobalTheory.NabBC.mem_localization_of_mem' _ hx
  rw [L0] at hx0
  obtain ⟨g, ⟨s, hs, hsg⟩, hg⟩ := hx0
  rw [L1]
  refine ⟨MvPolynomial.map f g, ⟨RingOfIntegers.mapRingHom f s, hw s hs, ?_⟩, ?_⟩
  · refine (congrArg (· ∈ nabStd K lam) (GlobalTheory.NabBC.map_smul_int f s g)).mpr ?_
    have h1 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K₀ ι f (RingOfIntegers.mapRingHom f) (fun r => rfl) n lam).1
    have h2 := (GlobalTheory.StdBaseChange.std_baseChange (𝓞 K) K K ι (RingHom.id K) (RingHom.id _) (fun r => rfl) n lam).1
    have h3 : MvPolynomial.map f (s • g) ∈ Submodule.span (𝓞 K) (MvPolynomial.map f '' (nabStd K₀ lam : Set (Pol K₀ ι n))) :=
      Submodule.subset_span ⟨_, hsg, rfl⟩
    rw [h1, ← h2] at h3
    have h4 : (MvPolynomial.map (RingHom.id K) '' (nabStd K lam : Set (Pol K ι n))) = (nabStd K lam : Set (Pol K ι n)) := by
      ext y
      simp [MvPolynomial.map_id]
    rw [h4, Submodule.span_eq] at h3
    exact h3
  · change actP lam (fun τ => Formalism.UG.bc f (B₀ τ)) (MvPolynomial.map f g) = MvPolynomial.map f x.1
    rw [← GlobalTheory.ValCmp.use₂]
    exact congrArg (MvPolynomial.map f) hg

end BaseChange

theorem harmLat_le {D : D7} {m n : ℕ} {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K)
    (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O : Subring ℂ) (w : GlobalTheory.ExportSeries.Weight D n) (B : GLR D n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    harmLat (σ.comp f) emb O m w B M ≤ harmLat σ (fun τ => f.comp (emb τ)) O m w B M := by
  refine inf_le_inf_left _ (Submodule.comap_mono (Submodule.span_mono ?_))
  rintro _ ⟨F, hF, rfl⟩
  refine ⟨_, map_mem_nabAtr f emb w.lam M hM hF, funext fun y => ?_⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom]

theorem coefLat_eq_small : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  intro D S T B hB O hO h
  have hm : ∀ τ, B.w.p τ + B.w.q τ ≤ T.rank := fun τ => by
    have h1 := hB.sig τ
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
    rw [← h1] at h2
    exact h2.le
  have hS := Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S B.F.ΛS hB.frame.sdS
  have hM : Submodule.IsFullLattice D.host.E (B.latAt h) :=
    Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hS.fg) hS.span_eq_top _
  refine le_antisymm (fun P hP => ?_)
    (harmLat_le D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O B.w B.F.BS hM)
  have h1 := GlobalTheory.SmallSpan.harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O (fun a => hO ⟨a, rfl⟩)
    B.w B.F.BS hB.wt hm hM hP
  rw [Submodule.span_eq] at h1
  exact h1

end GlobalTheory.PlaceSmall

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientLatticeEqSmallCoefficientFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_lattice_eq_small_coefficient_field : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ O : Subring ℂ, intLL D ≤ O → ∀ h, B.coefLat D.what₂.embLL (labLL D) O h = B.coefLat (embLL0 D) (labLL0 D) O h := by
  first | exact @GlobalTheory.PlaceSmall.coefLat_eq_small | exact GlobalTheory.PlaceSmall.coefLat_eq_small | (intros; apply GlobalTheory.PlaceSmall.coefLat_eq_small <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem image_span {R V A : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup A] [Module ℂ A] (φ : R →+* ℂ)
    (O : Subring ℂ) (hO : O = φ.range) (f : V →+ A) (hf : ∀ r v, f (r • v) = φ r • f v) (s : Set V) :
    f '' (Submodule.span R s : Set V) = (Submodule.span O (f '' s) : Set A) := by
  subst hO
  refine Set.Subset.antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [hf]; exact Submodule.smul_mem _ (⟨φ r, r, rfl⟩ : φ.range) hx
  · induction hy using Submodule.span_induction with
    | mem x hx => exact Set.image_mono Submodule.subset_span hx
    | zero => exact ⟨0, zero_mem _, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, map_add f x y⟩
    | smul r x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨_, r, rfl⟩ := r
      exact ⟨r • x, Submodule.smul_mem _ r hx, hf r x⟩

theorem span_span_sub {A : Type} [AddCommGroup A] [Module ℂ A] {O₁ O₂ : Subring ℂ} (h : O₁ ≤ O₂) (s : Set A) :
    Submodule.span O₂ (Submodule.span O₁ s : Set A) = Submodule.span O₂ s := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_mem _ (⟨r.1, h r.2⟩ : O₂) hx

theorem isIntegral_of_root {ζ : ℂ} (h : IsRoot1 ζ) : IsIntegral ℤ ζ ∧ IsIntegral ℤ ζ⁻¹ ∧ ζ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one), IsIntegral.of_pow hn (by rw [inv_pow, h, inv_one]; exact isIntegral_one), ?_⟩
  rintro rfl
  rw [zero_pow hn.ne'] at h
  exact zero_ne_one h

theorem unitOff_conj {N : ℕ} {a ζ ξ : ℂ} (τ : ℂ ≃+* ℂ) (ha : UnitOff N a) (hζ : IsRoot1 ζ) (hξ : IsRoot1 ξ) :
    UnitOff N (ξ * ζ * (τ a)⁻¹) := by
  obtain ⟨h0, n, h1, h2⟩ := ha
  obtain ⟨z1, z2, z0⟩ := isIntegral_of_root hζ
  obtain ⟨x1, x2, x0⟩ := isIntegral_of_root hξ
  have k1 := h1.map (τ : ℂ →+* ℂ).toIntAlgHom
  have k2 := h2.map (τ : ℂ →+* ℂ).toIntAlgHom
  simp only [map_mul, map_pow, map_natCast, map_inv₀] at k1 k2
  have t0 : τ a ≠ 0 := by simpa using h0
  refine ⟨mul_ne_zero (mul_ne_zero x0 z0) (inv_ne_zero t0), n, ?_, ?_⟩
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹) = ξ * ζ * ((N : ℂ) ^ n * (τ a)⁻¹) := by ring
    rw [e]
    exact (x1.mul z1).mul k2
  · have e : (N : ℂ) ^ n * (ξ * ζ * (τ a)⁻¹)⁻¹ = ξ⁻¹ * ζ⁻¹ * ((N : ℂ) ^ n * τ a) := by rw [mul_inv, mul_inv, inv_inv]; ring
    rw [e]
    exact (x2.mul z2).mul k1

variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}

theorem mem_ringOf (ι : KE c w →+* ℂ) {y : D.what₂.LL} (hy : IsIntegral ℤ y) : ι (c.embW w y) ∈ ringOf ι := by
  obtain ⟨p, pm, hp⟩ := hy
  have h := congrArg (c.embW w) hp
  rw [Polynomial.hom_eval₂, map_zero] at h
  have hi : IsIntegral (c.Oe w) (c.embW w y) := ⟨p.map (Int.castRingHom _), pm.map _, by
    rw [Polynomial.eval₂_map, ← h]
    congr 1
    exact RingHom.ext_int _ _⟩
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, congrArg ι ho⟩

theorem intLL_le {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) : intLL D ≤ ringOf ι := by
  rintro _ ⟨a, rfl⟩
  change D.what₂.embLL (a : D.what₂.LL) ∈ _
  rw [← hι]
  exact mem_ringOf ι a.isIntegral_coe

theorem coefRing_LL {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing D.what₂.embLL (labLL D) O :=
  ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => h ⟨a, rfl⟩⟩

theorem coefficient_ring_of_integral_le {O : Subring ℂ} (h : intLL D ≤ O) : IsCoefRing (embLL0 D) (labLL0 D) O :=
  ⟨embLL0_labLL0, fun a => h ⟨⟨((a : D.LL0) : D.what₂.LL), a.isIntegral_coe.map D.LL0.val.toRingHom.toIntAlgHom⟩, rfl⟩⟩

theorem span_latT (j : ℕ) : Submodule.span (KE c w) (latT c w j : Set (Tgt c w j)) = ⊤ := by
  refine top_unique fun y _ => ?_
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem (hx trivial) (hy trivial)
  | tmul a f =>
    have hf : f ∈ Submodule.span (FractionRing (D.ntw.Ok (c.twI w) (c.k' w)))
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) : Set _) := by
      rw [D.nexp.MtLat_span]; trivial
    induction hf using Submodule.span_induction generalizing a with
    | mem f hf =>
      have e : (a ⊗ₜ f : Tgt c w j) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Submodule.subset_span ⟨f, hf, rfl⟩))
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [TensorProduct.tmul_add]; exact add_mem (hf a trivial) (hg a trivial)
    | smul r f _ hf =>
      obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := D.ntw.Ok (c.twI w) (c.k' w)) r
      have hq0 := nonZeroDivisors.ne_zero hq
      have hq1 : algebraMap _ (KE c w) q ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply _ (c.Oe w) (KE c w)]
        exact fun h => hq0 (c.Oe_inj w ((IsFractionRing.injective (c.Oe w) (KE c w) (h.trans (map_zero _).symm)).trans (map_zero _).symm))
      have e : (a ⊗ₜ ((algebraMap _ (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p / algebraMap _ _ q) • f) : Tgt c w j) =
          (p • (a / algebraMap _ (KE c w) q)) ⊗ₜ f := by
        conv_lhs => rw [← div_mul_cancel₀ a hq1, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
        rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) q,
          ← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) p f, smul_smul,
          mul_div_cancel₀ _ (by simpa using hq0)]
      rw [e]
      exact hf _ trivial

theorem span_smul_latT (j : ℕ) (o : (c.Oe w)ˣ) :
    Submodule.span (c.Oe w) ((fun y => algebraMap (c.Oe w) (KE c w) o • y) '' (latT c w j : Set (Tgt c w j))) = latT c w j := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun y hy => Submodule.subset_span ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w) • y, Submodule.smul_mem _ _ hy, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    beta_reduce
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  · beta_reduce
    rw [algebraMap_smul, smul_smul, Units.mul_inv, one_smul]

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

theorem rdF_thPe (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (hok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w))
    (hr : ∀ f, ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (T.rdV (c.k' w) (c.Q w) (chr c w) f) ∈ Set.range (rdK rd hρ (c.k' w)))
    (y : Tgt c w (j.1 + 1)) :
    rdF rd hρ hε (NChoice.thPe D c w (j.1 + 1) y) = ρ.sum (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (rdE T hε y) := by
  have key : ∀ m, rdF rd hρ hε (((Algebra.linearMap (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w)).restrictScalars (D.ntw.O (c.twI w))).rTensor
      (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) m) = rdK rd hρ (c.k' w) m := fun m => by
    induction m using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | tmul a f =>
      rw [LinearMap.rTensor_tmul, rdF_tmul, rdK_tmul, ← hε.apply]
      rfl
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | tmul a f =>
    have e : (a ⊗ₜ f : Tgt c w (j.1 + 1)) = a • ((1 : KE c w) ⊗ₜ f) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [rdE_tmul, map_smul, e, map_smul, LinearMap.map_smulₛₗ, NChoice.thPe_one, key, T.thP_eq _ _ _ hok f (hr f)]

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem levJ_congr {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (h : ψ'.Q = ψ.Q) : B.levJ ψ' = B.levJ ψ := by
  obtain ⟨Q, a, b⟩ := ψ
  obtain ⟨Q', a', b'⟩ := ψ'
  dsimp only at h
  subst h
  rfl

theorem span_translate (H : AtPlace Y Z c w j) {ι : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x)
    {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0) (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ)
    {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z) :
    ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) =
      Submodule.span (ringOf ι) ((fun x h => (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (h * finPt (Vc D j) z)) '' latS w (j.1 + 1)) := by
  have hB := Z.good.base (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  have hle := intLL_le hι
  obtain ⟨hN0, hNP, o, ho⟩ := GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι
  have hNi : ((GlobalTheory.TwistField.tupPrime X.R.toRealDat (Y.tupT (D.what₂.muTw w)) : ℕ) : ℂ)⁻¹ ∈ ringOf ι := by
    refine ⟨((o⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← map_natCast (ι.comp (algebraMap (c.Oe w) (KE c w))), ← ho, ← map_mul, Units.inv_mul, map_one]
  have h1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
      Submodule.span (ringOf ι) ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) ''
        latS w (j.1 + 1)) := by
    have e1 : (baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) =
        (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (ringOf ι) (twVia Z.ρ ι) := by
      unfold Base.mtLat
      rw [funext (GlobalTheory.T.coefficient_lattice_eq_small_coefficient_field D _ _ _ hB _ hle)]
    have e2 := GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing D _ _ _ hB _ hg ha _ D.what₂.embLL (labLL D) (𝓞 D.what₂.LL) (D.what₂.embLL.comp (algebraMap _ _))
      (D.what₂.embLL.injective.comp RingOfIntegers.coe_injective) (coefRing_LL le_rfl) (GlobalTheory.T.level_twist_character_mem_coefficientIntegers D X X0 Y S YS Z c w j H ι hι) _ hle
    have e3 := GlobalTheory.T.rational_lattice_fock_polys_span_integral_forms D X X0 Y S YS Z c w j H ι hι u hu κ hκ hs
    rw [e1, e2]
    exact (congrArg (fun M : Submodule (intLL D) (Amb D j) => Submodule.span (ringOf ι) (M : Set (Amb D j))) e3).trans
      (span_span_sub hle _)
  have hc := GlobalTheory.T.integral_forms_central_translate_iff D j _ hB (twVia Z.ρ ι) _ (embLL0 D) (labLL0 D) _ (coefficient_ring_of_integral_le hle) _ z hz _ hN0 hNP hNi
  let Tz : Amb D j →ₗ[ℂ] Amb D j := LinearMap.funLeft ℂ _ fun h => h * finPt (Vc D j) z
  have h2 := image_span (ringOf ι).subtype (ringOf ι) (Subring.range_subtype _).symm Tz.toAddMonoidHom
    (fun r v => Tz.map_smul (r : ℂ) v)
    ((fun x => κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image, ← h1] at h2
  refine Eq.trans (Set.Subset.antisymm (fun F hF => ?_) ?_) h2
  · have e : (fun h => (fun h => F (h * (finPt (Vc D j) z)⁻¹)) (h * finPt (Vc D j) z)) = F :=
      funext fun h => by beta_reduce; rw [mul_inv_cancel_right]
    exact ⟨fun h => F (h * (finPt (Vc D j) z)⁻¹), (hc _).2 (by rw [e]; exact hF), e⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact (hc F).1 hF

noncomputable def trOf (H : AtPlace Y Z c w j) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (κ : ℂ) (z : GA D (Vc D j)) :
    D.what₂.Mt (D.what₂.muTw w) (j.1 + 1) →ₗ[ℂ] Amb D j :=
  LinearMap.funLeft ℂ _ (fun h => h * finPt (Vc D j) z) ∘ₗ (κ⁻¹ • fockOf Y (used_of_tw H.tw) j u)

theorem trOf_apply (H : AtPlace Y Z c w j) (u κ z y h) :
    trOf H u κ z y h = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u y (h * finPt (Vc D j) z) := rfl

theorem trOf_eq_zero (H : AtPlace Y Z c w j) {u κ z} (hκ : κ ≠ 0) (hinj : Function.Injective (fockOf Y (used_of_tw H.tw) j u)) (y)
    (hy : trOf H u κ z y = 0) : y = 0 := by
  refine hinj (Eq.trans (funext fun h => ?_) (map_zero _).symm)
  have := congrFun hy (h * (finPt (Vc D j) z)⁻¹)
  rw [trOf_apply, inv_mul_cancel_right] at this
  exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero hκ)

theorem indep_conj {M A I : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) (Φ : M →ₗ[ℂ] A)
    (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (h : ∀ y, C (Φ y) = 0 → y = 0) {b : I → M} (hb : LinearIndependent ℂ b) :
    LinearIndependent ℂ fun k => C (Φ (b k)) := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : C (Φ (∑ i ∈ s, τ.symm (g i) • b i)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (τ.apply_symm_apply _)
  simpa using linearIndependent_iff'.1 hb s _ (h _ h1) k hk

noncomputable def semiComp {L V M A : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
    [Module ℂ A] (τ : ℂ ≃+* ℂ) {σ : L →+* ℂ} (J : V →ₛₗ[σ] M) (Φ : M →ₗ[ℂ] A) (C : A →ₛₗ[(τ : ℂ →+* ℂ)] A) (σ' : L →+* ℂ)
    (h : ∀ r, τ (σ r) = σ' r) : V →ₛₗ[σ'] A where
  toFun x := C (Φ (J x))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' r x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ]
    exact congrArg (· • _) (h r)

theorem rescale_conj {A : Type} [AddCommGroup A] [Module ℂ A] (τ : ℂ ≃+* ℂ) {n : ℕ} {κ ν ζ a₀ : ℂ} (hκ : κ ≠ 0) (hν : ν ≠ 0)
    {g : Fin n → A} {a a' : Fin n → ℂ} (ha : ∀ k, τ (a k) = a' k) {s : A} (h : κ • s = ζ • ∑ k, τ (a₀⁻¹ * a k) • g k) :
    s = (ν / κ * ζ * (τ a₀)⁻¹) • ν⁻¹ • ∑ k, a' k • g k := by
  rw [← inv_smul_smul₀ hκ s, h]
  simp only [map_mul, map_inv₀, ha, mul_smul]
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  congr 1
  field_simp

theorem expansion_eq (H : AtPlace Y Z c w j) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    {z : GA D (Vc D j)} {a₀ : ℂ} (ha₀ : a₀ ≠ 0) (L : Amb D j →ₗ[ℂ] (GA D (Wc D j) → ℂ)) {x} (hx : x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1))
    (hth : X.R.thF j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))
        (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) =
      a₀ • L (fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z)))
    {n : ℕ} {a : Fin n → D.what₂.LL} {f : Fin n → NX.FmK S (j.1 + 1)}
    (hf : (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
      Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) :
    κ • L (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) =
      ∑ k, (a₀⁻¹ * D.what₂.embLL (a k)) • evW YS X.geo.v₀ j (f k).val := by
  have k1 := GlobalTheory.T.liftForm_at_evaluationVector_eq_realisationLift D X X0 Y S YS Z c w j H x hx
  have k0 : (fun τ => (u τ : ↥((X.R.MW j (sg0 D X.A3.A)).sm τ))) = X.geo.v₀ j (sg0 D X.A3.A) := funext hu
  have k3 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = ∑ k, D.what₂.embLL (a k) • evW YS X.geo.v₀ j (f k).val := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => evW_smul YS X.geo.v₀ j _ _
  have k4 : evW YS X.geo.v₀ j (∑ k, a k • (f k).val) = _ :=
    (congrArg (fun y => (X.R.HW j (sg0 D X.A3.A)).e y (X.geo.v₀ j (sg0 D X.A3.A))) hf).trans (k1.trans (k0 ▸ hth))
  have k5 : κ • trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) =
      fun h => fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x) (h * finPt (Vc D j) z) :=
    funext fun h => by rw [Pi.smul_apply, trOf_apply, smul_inv_smul₀ hκ]
  rw [← map_smul, k5]
  simp only [mul_smul]
  rw [← Finset.smul_sum, ← k3, k4, inv_smul_smul₀ ha₀]

theorem span_conj (H : AtPlace Y Z c w j) {ι ε : KE c w →+* ℂ} (hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x) {τ : ℂ ≃+* ℂ}
    (hιε : (τ : ℂ →+* ℂ).comp ι = ε) {u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ} (hu : IsLow X j u) {κ : ℂ} (hκ : κ ≠ 0)
    (hs : IsScale X.R X.geo.v₀ (baseOf Z c w j) κ) {z : GA D (Vc D j)} (hz : IsCentAt j (X.R.Q (Y.tupT (D.what₂.muTw w))) z)
    (C : Amb D j →ₛₗ[(τ : ℂ →+* ℂ)] Amb D j) (M : Set (Amb D j))
    (hC : C '' ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ι) (twVia Z.ρ ι) : Set (Amb D j)) = M) :
    M = Submodule.span (ringOf ε) ((fun x => C (trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) '' latS w (j.1 + 1)) := by
  have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
    rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
  have e3 := image_span ((τ : ℂ →+* ℂ).comp (ringOf ι).subtype) (ringOf ε)
    (by rw [← RingHom.map_range, Subring.range_subtype, e1]) C.toAddMonoidHom (fun r v => C.map_smulₛₗ (r : ℂ) v)
    ((fun x => trOf H u κ z (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) '' latS w (j.1 + 1))
  rw [Set.image_image] at e3
  rw [← hC, span_translate H hι hu hκ hs hz]
  exact e3

theorem exists_lift {L K V W A : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W] [AddCommGroup A]
    [Module ℂ A] (φ : L →+* K) (ε : K →+* ℂ) (r : W →ₛₗ[ε] A) (hr : Function.Injective r) (Ψ : V →ₛₗ[ε.comp φ] A) {s : Set V}
    (hs : Submodule.span L s = ⊤) (h : ∀ x ∈ s, ∃ y, r y = Ψ x) : ∃ e : V →ₛₗ[φ] W, ∀ x, r (e x) = Ψ x := by
  have key : ∀ x, ∃ y, r y = Ψ x := fun x => by
    have hx : x ∈ Submodule.span L s := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx⟩ := hx
      obtain ⟨y', hy⟩ := hy
      exact ⟨x' + y', by rw [map_add (f := _), map_add (f := _), hx, hy]⟩
    | smul a x _ hx =>
      obtain ⟨x', hx⟩ := hx
      exact ⟨φ a • x', by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx]; rfl⟩
  choose e he using key
  exact ⟨⟨⟨e, fun x y => hr (by rw [map_add (f := _), he, he, he, map_add (f := _)])⟩,
    fun a x => hr (by
      change r (e (a • x)) = r (φ a • e x)
      rw [LinearMap.map_smulₛₗ, he, he, LinearMap.map_smulₛₗ]; rfl)⟩, he⟩

theorem indep_of_read {K W A I : Type} [Field K] [AddCommGroup W] [Module K W] [AddCommGroup A] [Module ℂ A] (ε : K →+* ℂ)
    (r : W →ₛₗ[ε] A) {b : I → W} (h : LinearIndependent ℂ fun k => r (b k)) : LinearIndependent K b := by
  refine linearIndependent_iff'.2 fun s g hg k hk => ?_
  have h1 : ∑ i ∈ s, ε (g i) • r (b i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_zero r, ← hg, map_sum]
    exact Finset.sum_congr rfl fun i _ => (r.map_smulₛₗ _ _).symm
  simpa using linearIndependent_iff'.1 h s _ h1 k hk

theorem mem_span_basis {L K V W I : Type} [Field L] [Field K] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module K W]
    {φ : L →+* K} (e : V →ₛₗ[φ] W) (b : Module.Basis I L V) (x : V) : e x ∈ Submodule.span K (Set.range fun i => e (b i)) := by
  have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

end GlobalTheory.PlaceRead

namespace GlobalTheory.PlaceRead

open Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

end GlobalTheory.PlaceRead
