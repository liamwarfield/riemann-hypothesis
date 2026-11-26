module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewformAOfEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewform2A
open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV

namespace UpperTheory.V.Z.Win.RR

theorem gd : GdOf := fun E Ω _ _ _ _ _ A w h rc hrc a σ hp => Gu.plainGd E Ω A w h rc hrc a σ hp

end UpperTheory.V.Z.Win.RR
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewformAOfEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV UpperTheory.V.Z.Win.RR
open scoped Matrix Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.RR
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
private theorem alg0 (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (m : ℤ) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ m) := by
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hfinite : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
    have : NeZero M := ⟨by omega⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω M
    refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
    rw [← map_pow]
    refine hχ _ fun ζ h => ?_
    have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
    rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
    rw [map_pow, ← h1]
  obtain ⟨k, hk, hpow⟩ := hfinite
  refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ ?_ fun w _ => ?_
  · have hcyc : Continuous (cycBar ℚ Ω l) :=
      (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
        ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)
    have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ m :=
      (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp hcyc)
    exact h1
  · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, m, k, hk, fun s _ => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, hθ, hpow]
private theorem alg_det (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := alg0 P ι W hW hdet _
private theorem flag_all {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) {B : ValuationSubring Ω}
    (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∃ N : Subgroup (G ℚ Ω), IsOpen (N : Set (G ℚ Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∃ s ∈ N ⊓ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1) ∧
        ∃ κ, IsFlagOn W (Dec (F := ℚ) A) κ ∧ ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ N ⊓ Ine (F := ℚ) A →
          κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.normalCore, hH', fun w hw A hA => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 w hA).2 hw
  have hcyc : ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
    have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
    obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hAl hu.unit
    refine ⟨s, hs, fun k hk h => ?_⟩
    have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [he, hu.unit_spec, map_natCast, map_natCast]
    have h3 := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
    have := hl.out.pos
    omega
  obtain ⟨s, hs, hs'⟩ := hcyc
  have hs0 : s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) A :=
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hinf : ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l (s ^ H.normalCore.index) ^ k ≠ 1 := fun k hk0 h => by
    rw [map_pow, ← pow_mul] at h
    exact hs' _ (mul_ne_zero hk hk0) h
  refine ⟨⟨_, hs0, hinf⟩, ?_⟩
  have hBw : IsPlaceOver B w := by
    obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
    obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hB
    have hpr : Prime (l : 𝓞 ℚ) := by
      have e : (l : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) := by simp
      rw [e]
      exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hl.out)
    have hm : (Ideal.span {(l : 𝓞 ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
    have e : v = w := HeightOneSpectrum.ext
      ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hB))).symm.trans
        (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
    exact e ▸ hv
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hBw hA
  have hfl' : IsFlagOn W (H.normalCore ⊓ Ine (F := ℚ) (g • B))
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H.normalCore ⊓ Ine (F := ℚ) (g • B)).subtype) := by
    obtain ⟨p, hp⟩ := hfl
    refine ⟨p * (W g)⁻¹, fun t => ?_⟩
    have hm : g⁻¹ * (t : G ℚ Ω) * g ∈ H ⊓ Ine (F := ℚ) B :=
      ⟨H.normalCore_le (hn.conj_mem' _ t.2.1 g), GlobalTheory.PointIrredCompare.conj_mem_Ine_of_smul t.2.2⟩
    have e1 : p * (W g)⁻¹ * W t * (p * (W g)⁻¹)⁻¹ = p * W (g⁻¹ * (t : G ℚ Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    obtain ⟨h1, h2⟩ := hp ⟨_, hm⟩
    rw [e1]
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    congr 1
    change ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (g⁻¹ * (t : G ℚ Ω) * g) = ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) t
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  let D := Dec (F := ℚ) (g • B)
  let N := H.normalCore ⊓ Ine (F := ℚ) (g • B)
  let χ : Fin 2 → G ℚ Ω →* (Qbar l)ˣ := fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)
  have hc : ∀ d ∈ D, ∀ t ∈ N, d⁻¹ * t * d ∈ N := fun d hd t ht =>
    ⟨hn.conj_mem' t ht.1 d, by simpa using conj_mem_Ine (D.inv_mem hd) ht.2⟩
  have hne : ∃ t ∈ N, χ 0 t ≠ χ 1 t := by
    refine ⟨_, hs0, fun h1 => hinf (e + e) (by omega) ?_⟩
    change ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] 0)) (s ^ H.normalCore.index) =
      ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] 1)) (s ^ H.normalCore.index) at h1
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
    rw [pow_add]
    exact mul_eq_one_iff_eq_inv.2 h1
  obtain ⟨p, hp⟩ := hfl'
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj p).toMonoidHom.comp W
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hp ⟨s, hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hp ⟨s, hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : Qbar l) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨p, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)
private theorem zpow_ne {C : Type} [Group C] {x : C} (h : ∀ k : ℕ, k ≠ 0 → x ^ k ≠ 1) {a b : ℤ} (e : x ^ a = x ^ b) : a = b := by
  by_contra hne
  have h1 : x ^ (a - b) = 1 := by rw [zpow_sub, e, mul_inv_cancel]
  refine h (a - b).natAbs (by omega) ?_
  rcases Int.natAbs_eq (a - b) with h2 | h2
  · rw [← zpow_natCast, ← h2, h1]
  · rw [← zpow_natCast, ← inv_inj, ← zpow_neg, ← h2, h1, inv_one]
private theorem inf_char (P : _root_.UpperTheory.V.Af.HypothesesH') (hC : CompatT) (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hW : Continuous W) (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π) (hU : WitUp ι W)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  intro v
  obtain ⟨hdet, L, _, _, _, _, _, hirr, ⟨η, σ₀, hσ₀, hησ, hηL⟩, ka, hka, hWit⟩ := hU
  have : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  have : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  obtain ⟨K, hK, hKC⟩ := Z.Bc.exists_quad L Ω η σ₀ hσ₀ hησ hηL
  have : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  have : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  have : Group.IsSolvable (L ≃ₐ[K] L) := Group.isSolvable_of_comm a.is_comm.comm
  have ec : W.comp (galEmb ℚ L Ω) = (W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) := MonoidHom.ext fun _ => rfl
  have hirr' : IsIrr ((W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω)) := ec ▸ hirr
  obtain ⟨P₁, a1, a2, a3⟩ := _root_.UpperTheory.V.Z.Bc.upQuadI_of_alt P.toClassicalTheorems (Z.Bc.quadLiftRealToComplex_of_base_change P.bc) ℚ K Ω l ι hK W π hW hreg hatt
    ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr')
  obtain ⟨Q, b1, b2, b3⟩ := _root_.UpperTheory.V.Z.Bc.upSolI_of_alt P.toClassicalTheorems (Z.Bc.cyclicLiftRankTwo_of_cyclic_base_change P.cyc) K L Ω l ι _ P₁
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) a1 a2 hirr'
  rw [← ec] at b2
  have hWL : Continuous (W.comp (galEmb ℚ L Ω)) := hW.comp (continuous_restrictScalarsHom ℚ L Ω)
  have hpol : Sol.Pol ι W := by
    have halg := alg0 P ι W hW hdet 0
    rw [zpow_zero, mul_one] at halg
    obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
    rw [zpow_zero, one_mul] at hθ
    have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
      have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      let : Algebra Ω ℂ := j.toRingHom.toAlgebra
      have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
      let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
      exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
    obtain ⟨c, hc⟩ := hconj
    have hpair : ∃ P, IsPairing c W ((Matrix.GeneralLinearGroup.det.comp W).comp (resG ℚ ℚ Ω)) P := by
      let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
      refine ⟨J * W c⁻¹, fun s s' h => ?_⟩
      have h' : s' = c * s * c⁻¹ := h
      have e : W c⁻¹ * W s' = W s * W c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
      have e' : (W c⁻¹).val * (W s').val = (W s).val * (W c⁻¹).val := congrArg Units.val e
      have hp : (W s).valᵀ * J.val * (W s).val = (W s).val.det • J.val := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
      have hd : (((Matrix.GeneralLinearGroup.det.comp W).comp (resG ℚ ℚ Ω) s : (Qbar l)ˣ) : Qbar l) = (W s).val.det := rfl
      rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
      simp only [Matrix.mul_assoc, e']
    obtain ⟨J, hJ⟩ := hpair
    refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J, halg,
      ?_, hc, hJ⟩
    intro c c' h h'
    rw [hθ]
    have hroot {d : G ℚ Ω} (hd : IsConjEl d) {ζ : Ω} (hz : ζ ^ M = 1) : d ζ = ζ⁻¹ := by
      obtain ⟨j, hj⟩ := hd
      apply j.injective
      have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, hz, map_one]
      rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
    have heq := hχ (c⁻¹ * c') fun ζ hz => by
      rw [AlgEquiv.mul_apply, hroot h' hz, ← hroot h hz]
      exact c.symm_apply_apply ζ
    rwa [map_mul, map_inv, inv_mul_eq_one] at heq
  have hQ := _root_.UpperTheory.V.Z.Win.polarized_pair_of_attached P one_le_two (UpperTheory.solvable_polarized_restriction ℚ L Ω l ι 2 W hpol) b2
  have hka' : IsAlgChar ι ka := by
    obtain ⟨h1, art, χ, a, h2, h3, h4⟩ := hka
    exact ⟨χ, h1, art, a, h2, h3, h4⟩
  have hWA : WitA ι (W.comp (galEmb ℚ L Ω)) := by
    have := (_root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw P.toClassicalTheorems L Ω l ι 2 _ hWit).2 ka⁻¹ ((_root_.UpperTheory.V.Af.algOfCyc_s P L Ω l ι).2.1 ka ka hka' hka').2
    have htw : tw (tw (W.comp (galEmb ℚ L Ω)) ka) ka⁻¹ = W.comp (galEmb ℚ L Ω) := by
      refine MonoidHom.ext fun s => Units.ext ?_
      rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
        inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rwa [htw] at this
  obtain ⟨N, hN, hall⟩ := flag_all he W hB H hH hfl
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places L Ω l B
  obtain ⟨w, h⟩ := p1 fun h0 => (p2 h0).2 hB
  have hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := (p3 w h).1 hB
  have hw0 : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]; exact hw
  have hpot : PotUnl W (w.under (𝓞 ℚ)) := fun A hA => by
    obtain ⟨⟨s, hs, hs'⟩, κ, hκ, hI⟩ := hall _ hw0 A hA
    refine ⟨κ, hκ, fun i j m hm e0 => ?_⟩
    have e1 := DFunLike.congr_fun e0 ⟨s, Ine_le_Dec A hs.2⟩
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.mul_apply, hI i _ hs, hI j _ hs] at e1
    change (cycBar ℚ Ω l s ^ _) ^ m = (cycBar ℚ Ω l s ^ _ * cycBar ℚ Ω l s) ^ m at e1
    rw [← zpow_add_one, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at e1
    have e2 := mul_right_cancel₀ (show (m : ℤ) ≠ 0 by omega) (zpow_ne hs' e1)
    fin_cases i <;> fin_cases j <;> simp at e2 <;> omega
  have hpotL : PotUnl (W.comp (galEmb ℚ L Ω)) w := (((flagLaws ℚ Ω l 2 W).2.2.2 L).2.2 w hw).1 hpot
  obtain ⟨HT, hwt, hloc⟩ := hC L Ω l ι 2 one_le_two _ Q hWL b1 hQ b2
  obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P.toClassicalTheorems L 2 Q w
  obtain ⟨rc, hrc⟩ := recTExists L Ω B w h
  have hpl := (guard_of plainRec b1 b2 hWA (Or.inr (Or.inr hpotL)) hrc hσ).1
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l L Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := ((hloc w σ hσ).2 hpl B h _ Bw hInd).2 (Bw.j.comp (algebraMap L Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl
  have hB0 : IsPlaceOver B (w.under (𝓞 ℚ)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ L Ω]
    exact h (algebraMap (𝓞 ℚ) (𝓞 L) x)
  obtain ⟨-, κ, ⟨g, hg⟩, hI⟩ := hall _ hw0 B hB0
  let ρ : ↥(Dec (F := L) B) →* ↥(Dec (F := ℚ) B) :=
    ((galEmb ℚ L Ω).comp (Dec (F := L) B).subtype).codRestrict _ fun s => s.2
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] _ hWL B Bw hInd (fun i => (κ i).comp ρ) (N.comap (galEmb ℚ L Ω))
    (hN.preimage (continuous_restrictScalarsHom ℚ L Ω)) ⟨g, fun s => hg (ρ s)⟩ (fun i s hs => hI i (ρ s) ⟨hs.1, hs.2⟩) _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hμQ : Q.HasInfChar (ι.toRingHom.comp (Bw.j.comp (algebraMap L Ω))) μ :=
    b3 _ μ (a3 _ μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v]))
  have hW2 := hwt (Bw.j.comp (algebraMap L Ω))
  rw [hH2, CG.HasInfChar.infChar_eq (π := CG.mk Q) hμQ] at hW2
  have hμeq : infOf ![(e : ℤ), -(e : ℤ)] = μ := by
    have hmap := congrArg (Multiset.map fun z : ℂ => (((2 : ℕ) : ℂ) - 1) / 2 - z) hW2
    simpa only [infOf, Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id',
      Int.cast_neg, sub_neg_eq_add] using hmap
  rwa [← hμeq] at hμ
end UpperTheory.V.Z.Win.RR
theorem UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (hX : ExRS) (hC : CompatT) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Br.RepNewAE → AutNewformA := by
  rintro P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ hU B hB H hH hfl
  have hinf := UpperTheory.V.Z.Win.RR.inf_char P hC ι he W hW π hreg hatt hU hB H hH hfl
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Z.Win.RR.alg_det P ι W hW hU.1
  have hdual : DualTw W (Matrix.GeneralLinearGroup.det.comp W) := by
    refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring
  have hsd := (_root_.UpperTheory.V.Af.self_dual_real_of_printed_hida P ℚ Ω l ι 2 (by omega) W π hatt _ χ hdual hχ).1
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩
  have hG := hall W hW hatt
  obtain ⟨f, hf⟩ := hN (2 * e + 1) (by omega) e π fun v => by
    convert hinf v using 1
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    congr 2 <;> push_cast <;> ring
  have hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι W w (algSat 2 (normV w) B) := hG.frob
  let ψ := cycBar ℚ Ω l ^ (-(e : ℤ))
  have hss : IsSSRep (tw W ψ) := by
    have hinv (U : Submodule (Qbar l) (Fin 2 → Qbar l)) : IsInv (tw W ψ) U ↔ IsInv W U := by
      constructor
      · intro hW g v hv
        have hsmul := U.smul_mem ((ψ g : Qbar l)⁻¹) (hW g v hv)
        rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hsmul
      · intro hW g v hv
        rw [tw_val, Matrix.smul_mulVec]
        exact U.smul_mem _ (hW g v hv)
    intro U hU
    obtain ⟨W', hW', hcompl⟩ := hatt.1 U ((hinv U).1 hU)
    exact ⟨W', (hinv W').2 hW', hcompl⟩
  refine ⟨f, hss, ?_⟩
  have hl' : ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, (l : 𝓞 ℚ) ∉ w.asIdeal := by
    have h0 : Ideal.span {(l : 𝓞 ℚ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr hl.out.ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
    simp only [Set.mem_ofPred_eq, not_not] at hw
    exact Ideal.dvd_span_singleton.2 hw
  filter_upwards [hl', hf] with w hwl hfw A hA
  obtain ⟨S, hS, hpoly⟩ := hfw
  obtain ⟨h1, h2⟩ := hfrob w hwl S hS A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h3 : cycZ ℚ Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq (v := w) (σ := s) hwl hA (q := 1)
        (fun x hx => by simpa only [pow_one] using hs.2 x hx) n]
      simp
    apply Units.ext
    rw [tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]
  · have h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
    have h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
      rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀,
        map_inv₀, map_natCast, inv_zpow', neg_neg]
    let M : Matrix (Fin 2) (Fin 2) (Qbar l) := (W σ⁻¹).val
    let c : Qbar l := (ψ σ⁻¹ : (Qbar l)ˣ)
    have hscale (T : Multiset ℂ) (heig : M.charpoly.map ι.toRingHom = (T.map fun b => X - C b).prod) :
        (c • M).charpoly.map ι.toRingHom = (T.map fun b => X - C (ι.toRingHom c * b)).prod := by
      have hcard : T.card = 2 := by
        simpa only [natDegree_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
          natDegree_multiset_prod_X_sub_C_eq_card] using (congrArg natDegree heig).symm
      obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
      rw [Matrix.charpoly_fin_two] at heig ⊢
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
        Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        map_X, map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at heig ⊢
      have hzero := congrArg (eval 0) heig
      have hone := congrArg (eval 1) heig
      simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hzero hone
      have hdet : ι.toRingHom M.det = x * y := by linear_combination hzero
      have htrace : ι.toRingHom M.trace = x + y := by linear_combination hzero - hone
      rw [hdet, htrace]
      simp only [C_mul, C_add]
      ring
    rw [tw_val, hscale _ (h2 σ hσ)]
    rw [show ι.toRingHom c = _ from h4, hpoly]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAway
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Hi
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAway_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAway := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H A hA
  have P := PH.toClassicalTheorems
  obtain ⟨p1, p2, p3, p4⟩ := UpperTheory.V.Base.places F Ω l A
  have triv : (∀ g ∈ Ine (F := F) A, r g = 1) → Ine (F := F) A ≤ ξ.ker → IsDiagOn r (Ine (F := F) A) ![1, ξ] :=
    fun h1 h2 => ⟨1, fun g hg => by
      have h3 : ξ g = 1 := h2 hg
      rw [h1 g hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h3]⟩
  by_cases hT : A = ⊤
  · rw [(p2 hT).1] at triv ⊢
    exact triv (fun g hg => by rw [Subgroup.mem_bot.1 hg, map_one]) bot_le
  obtain ⟨w, h⟩ := p1 hT
  have hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := fun e => hA ((p3 w h).2 e)
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  have mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
      [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
      ∃ T : M →ₗ[R] S, T x ≠ 0 := by
    have htop : isotypicComponent R M S = ⊤ := top_le_iff.1 (h ▸ iSup_le fun f => by
      rcases f.injective_or_eq_zero with hi | rfl
      · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
      · simp)
    have : IsSemisimpleModule R M :=
      IsSemisimpleModule.congr (M := isotypicComponent R M S) (LinearEquiv.ofTop _ htop).symm
    have hiso := IsIsotypicOfType.of_isotypicComponent_eq_top htop
    obtain ⟨m, hm, hxm⟩ : ∃ m : Submodule R M, IsCoatom m ∧ x ∉ m := by
      by_contra hn
      push Not at hn
      refine hx ((Submodule.mem_bot R).1 ?_)
      rw [← IsSemisimpleModule.jacobson_eq_bot R M]
      exact Submodule.mem_sInf.2 hn
    obtain ⟨W, hc⟩ := exists_isCompl m
    have : IsSimpleModule R W := isSimpleModule_iff_isAtom.2 (hc.isCoatom_iff_isAtom.1 hm)
    obtain ⟨e⟩ := hiso W
    refine ⟨e.toLinearMap ∘ₗ W.projectionOnto m hc.symm, fun h0 => hxm ?_⟩
    simpa using h0
  have rep_retr {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
      (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
      ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
    have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
        refine top_le_iff.1 fun y _ => ?_
        have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
        rw [← h] at hy
        rw [← τ.asModuleEquiv.symm_apply_apply y]
        refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
        · rintro f _ ⟨v, rfl⟩
          exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
            ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
        · simp
        · intro a b ha hb
          rw [map_add (f := _)]
          exact add_mem ha hb)
    obtain ⟨T, h2⟩ := key x hx
    let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
    exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    have iwahori_level_zero_eq : K1 w 0 = GlobalTheory.LFun.KGL w (n := 2) := by
      ext g
      constructor
      · rintro ⟨k, -, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        have : Subsingleton
            (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
          Ideal.Quotient.subsingleton_iff.2 (by simp)
        exact Subsingleton.elim (α := Fin 2 → _) _ _
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).1
      ⟨T v, hTv, fun u hu => by rw [← hT, hf u (iwahori_level_zero_eq ▸ hu)]⟩
    have hB' : π.HasSat w B := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB
    exact triv (hG.frob w hl B hB' A h).1
      ((H.ram w A h).2 (Or.inl hc))
  obtain ⟨lam, ⟨v, hv, hf, hU⟩, hlam⟩ := H.away w hc hl
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  have map_dc {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
      (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
      T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
    let Q := MulAction.orbit K (a : Γ ⧸ K)
    rcases finite_or_infinite Q with hfinite | hinfinite
    · let _ := Fintype.ofFinite Q
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
    · have sum_eq_zero {W : Type} [AddCommGroup W] [Module ℂ W]
          (ρ : Representation ℂ Γ W) (y : W) (hy : y ≠ 0) :
          (∑ᶠ q : Q, ρ (q : Γ ⧸ K).out) = 0 := by
        apply finsum_of_infinite_support
        rw [Function.support_eq_univ]
        · exact Set.infinite_univ
        · intro q hρ
          let g := (q : Γ ⧸ K).out
          have hgy : ρ g⁻¹ (ρ g y) = y := by
            rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
          exact hy (by rw [← hgy, show ρ g = 0 from hρ, LinearMap.zero_apply, map_zero])
      have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
      rw [Hi.dc, Hi.dc, sum_eq_zero τ x hx0, sum_eq_zero σ (T x) hx]
      simp
  obtain ⟨μ₁, μ₂, L, hL, hμ, -, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ (c w) (Units.mk0 lam hl0) hc
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hU, map_smul, Units.val_mk0]⟩
  have exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
      (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
      (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
        ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
      ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
        ∀ x : kˣ, valuation k (x : k) = 1 → ψ 0 x = μ₁ x := by
    set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
    let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
    have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, v, rfl⟩
      obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
      have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
      have := H 1 1 (u.1.val 0 1) v
      rw [← e] at this
      simp [this]
    let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hL (LinearMap.ext hn)
    have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
      rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
      change _ * L _ = _ * L y
      rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
      simp [χ, torusChar_apply, hδ]
    have hs : IsSmoothChar χ := by
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
        ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
      intro g hg
      have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
      have h := hle g (Submodule.Quotient.mk v)
      rw [hg'] at h
      exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
    have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
      MonoidHom.ext fun t => by
        rw [torusChar_apply]
        conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
        rfl
    refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x hx => ?_⟩
    · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
        (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
      rw [← htc] at key
      exact key
    · have h1 : δ (Pi.mulSingle 0 x) = 1 := UnramFixed.deltaHalf_torusO k (t := (Pi.mulSingle 0 x : Fin 2 → kˣ)) fun j => by
        fin_cases j <;> simp [hx]
      change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
      rw [h1]
      simp [torusChar_apply]
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hx := (((hG.loc w σ hσ hpl).1 A h rc hrc).1 hl).isWDOf (hGd F Ω A w h rc hrc 2 σ hpl)
  have off_diag {K : Type} [Field K] {Y : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1)
      (h : Matrix.diagonal ![1, x] * Y = Y * Matrix.diagonal ![1, x]) : Y 0 1 = 0 ∧ Y 1 0 = 0 := by
    have h1 := congrFun (congrFun h 0) 1
    have h2 := congrFun (congrFun h 1) 0
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    have hx' : x - 1 ≠ 0 := sub_ne_zero.2 hx
    exact ⟨(mul_eq_zero.1 (by linear_combination -h1)).resolve_left hx',
      (mul_eq_zero.1 (by linear_combination h2)).resolve_left hx'⟩
  have nil_zero {K : Type} [Field K] {N : Matrix (Fin 2) (Fin 2) K} {x : K} (hx : x ≠ 1) (hN : IsNilpotent N)
      (h : Matrix.diagonal ![1, x] * N = N * Matrix.diagonal ![1, x]) : N = 0 := by
    obtain ⟨h1, h2⟩ := off_diag hx h
    have e : N = Matrix.diagonal fun i => N i i := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2]
    obtain ⟨k, hk⟩ := hN
    rw [e, Matrix.diagonal_pow] at hk
    rw [e]
    ext i j
    by_cases hij : i = j
    · subst hij
      have := congrFun (congrFun hk i) i
      simp at this
      simp [this.1]
    · simp [hij]
  have unip_one {K : Type} [Field K] [CharZero K] {M : Matrix (Fin 2) (Fin 2) K} (ht : M.trace = 1 + 1) (hd : M.det = 1) {d : ℕ}
      (h0 : 0 < d) (h : M ^ d = 1) : M = 1 := by
    have h2 : (M - 1) * (M - 1) = 0 := by
      rw [Matrix.trace_fin_two] at ht
      rw [Matrix.det_fin_two] at hd
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination M 0 0 * ht - hd
      · linear_combination M 0 1 * ht
      · linear_combination M 1 0 * ht
      · linear_combination M 1 1 * ht - hd
    have h3 : ∀ n : ℕ, M ^ n = 1 + (n : K) • (M - 1) := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        have : (M - 1) * M = M - 1 := by
          rw [← sub_eq_zero, ← h2, mul_sub (M - 1), mul_one]
        rw [pow_succ, ih, add_mul, smul_mul_assoc, this, Nat.cast_succ, add_smul, one_mul, one_smul]
        abel
    rw [h3, add_eq_left, smul_eq_zero, sub_eq_zero] at h
    exact h.resolve_left (Nat.cast_ne_zero.2 h0.ne')
  have diag_all {K : Type} [Field K] [CharZero K] {H : Type} [Group H] (r : H →* GL (Fin 2) K) (ξ : H →* Kˣ)
      (ht : ∀ s, (r s).val.trace = 1 + ξ s) (hd : ∀ s, (r s).val.det = ξ s) (hf : ∀ s, ∃ d, 0 < d ∧ r s ^ d = 1)
      {s₀ : H} (h0 : (ξ s₀ : K) ≠ 1) (e0 : (r s₀).val = Matrix.diagonal ![1, (ξ s₀ : K)]) (s : H) :
      (r s).val = Matrix.diagonal ![1, (ξ s : K)] := by
    have hc : ξ (s₀ * s * (s * s₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (ξ s₀), mul_inv_cancel]
    obtain ⟨d, hd0, h⟩ := hf (s₀ * s * (s * s₀)⁻¹)
    have h1 : r (s₀ * s * (s * s₀)⁻¹) = 1 := Units.ext (unip_one (by rw [ht, hc, Units.val_one]) (by rw [hd, hc, Units.val_one]) hd0
      (by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]))
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h1
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul, e0] at h2
    obtain ⟨h3, h4⟩ := off_diag h0 h2
    have t1 := ht s
    have t2 := ht (s₀ * s)
    rw [map_mul, Units.val_mul, e0, map_mul, Units.val_mul] at t2
    rw [Matrix.trace_fin_two] at t1 t2
    simp only [Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at t2
    have h5 : (r s).val 1 1 = ξ s := by
      refine sub_eq_zero.1 ((mul_eq_zero.1 (?_ : ((ξ s₀ : K) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 h0))
      linear_combination t2 - t1
    have h6 : (r s).val 0 0 = 1 := by linear_combination t1 - h5
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h3, h4, h5, h6]
  have diag_of_wd (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l))
      (ξ : G F Ω →* (Qbar l)ˣ) {x : WD h} (hx : IsWDOf ι r x)
      (hc : ∀ g : Ine (F := F) A, ∃ y : ℂ, x.charPol (ineIncl h g) = (X - C 1) * (X - C y))
      (hd : ∀ g ∈ Ine (F := F) A, (r g).val.det = ξ g) (hr : ¬ Ine (F := F) A ≤ ξ.ker) :
      IsDiagOn r (Ine (F := F) A) ![1, ξ] := by
    have ht : ∀ g ∈ Ine (F := F) A, (r g).val.trace = 1 + ξ g := fun g hg => by
      obtain ⟨y, hy⟩ := hc ⟨g, hg⟩
      have e := hx.wdOf_eq hl
      obtain ⟨t, ht, φ, hφ, N, a, hN, -⟩ := hx
      rw [← e, hN.charPol_wdOf hl ht ι, coe_ineIncl] at hy
      have h1 := congrArg (Polynomial.eval 1) hy
      rw [Matrix.charpoly_fin_two, hd g hg] at h1
      apply ι.injective
      simp at h1
      simp only [map_add (f := _), map_one]
      linear_combination -h1
    obtain ⟨s₀, hs₀, h0⟩ := IsConcreteLE.not_le_iff_exists.1 hr
    have h0' : (ξ s₀ : Qbar l) ≠ 1 := fun e => h0 (Units.ext e)
    obtain ⟨p, hp⟩ := UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag (r s₀) h0' (ht _ hs₀) (hd _ hs₀)
    let r' : G F Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj p).toMonoidHom.comp r
    have hr' : ∀ s, r' s = p * r s * p⁻¹ := fun s => rfl
    obtain ⟨t, htt, φ, hφ, N, a, hN, -⟩ : IsWDOf ι r' x := hx.of_conj hl p fun s => by rw [hr', inv_mul_cancel_right]
    obtain rfl : N = 0 := nil_zero h0' hN.1 (by
      have := hN.comm hl htt (ineIncl h ⟨s₀, hs₀⟩)
      rwa [deg_ineIncl, zpow_zero, one_smul, coe_ineIncl, hr', hp] at this)
    obtain ⟨-, U, hU, H⟩ := hN
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ U) := Subgroup.quotient_finite_of_isOpen _ hU
    refine ⟨p, fun s hs => ?_⟩
    refine (diag_all (r'.comp (Ine (F := F) A).subtype) (ξ.comp (Ine (F := F) A).subtype) (fun g => ?_) (fun g => ?_)
      (fun g => ?_) (s₀ := ⟨s₀, hs₀⟩) h0' hp ⟨s, hs⟩).trans ?_
    · exact (Matrix.trace_units_conj p _).trans (ht g g.2)
    · exact (Matrix.det_units_conj p _).trans (hd g g.2)
    · obtain ⟨d, hd, -, hg⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := U)) g
      refine ⟨d, hd, ?_⟩
      rw [← map_pow]
      exact Units.ext (by simpa using H _ hg)
    · congr 1
      ext i
      fin_cases i <;> rfl
  refine diag_of_wd hl ι r ξ hx (fun g => ?_) (fun g hg => ?_)
    fun e => ((H.ram w A h).1 e).elim hc hl
  · obtain ⟨b, hb, ε, hL⟩ := toV' hrc
    obtain ⟨e1, e2⟩ := RR.ps_cls hL σ ψ hψ hs
    have charPol_lpTw (x : WD h) (s : ℝ) (g : Ine (F := F) A) :
        (x.lpTw s).charPol (ineIncl h g) = x.charPol (ineIncl h g) := by
      obtain ⟨n, a, rfl⟩ := x.exists_rep
      rw [WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk]
      congr 1
      ext v
      simp
    rw [e1, charPol_lpTw]
    have h1 := e2 (ineIncl h g)
    have h2 : valuation (w.adicCompletion F) (b (ineIncl h g) : w.adicCompletion F) = 1 :=
      ord_eq_zero_iff.1 (by rw [hb.ord_eq, deg_ineIncl, neg_zero])
    have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Fin.prod_univ_two, hψ0 _ h2, hμ _ ((isEquiv (valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1 h2)] at h1
    exact ⟨_, h1⟩
  · have h1 := DFunLike.congr_fun H.det g
    have h2 : cycZ F Ω l g = 1 := p4 hA hg
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, cycBar, h2, map_one, one_zpow,
      one_mul] at h1
    exact congrArg Units.val h1
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV
namespace UpperTheory.V.Z.Win.RR
theorem ordAway_a_alt : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAway := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAway_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem ordAbove_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAbove := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem autNewformA_of_printsH_of_repNewAE : _root_.UpperTheory.V.Af.HypothesesH' → Br.RepNewAE → AutNewformA := fun P =>
  _root_.UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) (compatTOf (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) plainRec) P
end UpperTheory.V.Z.Win.RR
end
