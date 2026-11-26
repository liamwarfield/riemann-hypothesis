module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittCoefficients.CoeffEqOfSubMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.CoordPowEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationGluing.ValbLeOfCoeffEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem BK.X_pow_natDegree_mem {K : FinExt l} (bk : BK K) :
    (X : bk.S) ^ bk.Ep.natDegree ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_X] at h
  have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i ∈
      Ideal.span {(l : bk.S)} := by
    refine Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    rw [hc, map_mul, map_natCast, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have e : (X : bk.S) ^ bk.Ep.natDegree =
      bk.E - ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * (X : bk.S) ^ i := by
    rw [BK.E, h]; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hs)


set_option maxHeartbeats 1000000 in
theorem BK.hom_eq_of_X_C {K : FinExt l} (bk : BK K) {B : Obj l ↥(OL K)} (f g : Hom bk.prism B)
    (hX : BK.hf f X = BK.hf g X) (hC : ∀ w, BK.hf f (C w) = BK.hf g (C w)) : f = g := by
  have hpoly : ∀ p : Polynomial (Wq l bk.a), BK.hf f (p : bk.S) = BK.hf g (p : bk.S) := by
    have e : (BK.hf f).comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
        (BK.hf g).comp Polynomial.coeToPowerSeries.ringHom :=
      Polynomial.ringHom_ext (fun a => by simpa using hC a) (by simpa using hX)
    exact fun p => RingHom.congr_fun e p
  have hle : Ideal.span {(l : bk.S)} ⊔ Ideal.span {bk.E} ≤
      (Ideal.span {(l : B.A)} ⊔ B.I).comap (BK.hf f) := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_sup_right (f.f_I _ (Ideal.mem_span_singleton_self _))
  have hXe : BK.hf f X ^ bk.Ep.natDegree ∈ Ideal.span {(l : B.A)} ⊔ B.I := by
    rw [← map_pow]; exact hle bk.X_pow_natDegree_mem
  refine Hom.ext' (RingHom.ext fun (s : bk.S) => ?_)
  show BK.hf f s = BK.hf g s
  haveI : IsAdicComplete (Ideal.span {(l : B.A)} ⊔ B.I) B.A := B.complete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : B.A)} ⊔ B.I) B.A) _ fun n => ?_
  rw [SModEq.zero]
  obtain ⟨r, hr⟩ : (X : bk.S) ^ (bk.Ep.natDegree * n) ∣ s - (trunc (bk.Ep.natDegree * n) s : bk.S) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, coeff_trunc, hm]
  have e : s = (trunc (bk.Ep.natDegree * n) s : bk.S) + X ^ (bk.Ep.natDegree * n) * r := by
    rw [← hr]; ring
  have hd : BK.hf f s - BK.hf g s = BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) := by
    rw [e]
    simp only [map_add (f := _), map_mul, map_pow]
    rw [hpoly (trunc (bk.Ep.natDegree * n) s), ← hX]; ring
  have h2 : BK.hf f X ^ (bk.Ep.natDegree * n) * (BK.hf f r - BK.hf g r) ∈
      (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by
    rw [pow_mul]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hXe n)
  have h3 : BK.hf f s - BK.hf g s ∈ (Ideal.span {(l : B.A)} ⊔ B.I) ^ n := by rw [hd]; exact h2
  rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact h3

theorem BK.galHom_comp_ι_of_fixFlat {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (hg : bk.FixFlat g) :
    (ainfHom K g).comp bk.ι = bk.ι := by
  refine BK.hom_eq_of_X_C bk _ _ ?_ ?_
  · change Per.σA (g : GQ l) (bk.ev X) = bk.ev X
    rw [bk.ev_X]
    exact (GlobalTheory.RingIface.sigA_teich l _ _).trans (congrArg _ hg)
  · intro w
    change Per.σA (g : GQ l) (bk.ev (C w)) = bk.ev (C w)
    rw [bk.ev_C, bk.gal_w]

theorem MReal.gal_of_fixFlat {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} {T : Matrix (Fin d) (Fin d) (WCb l)} (h : MReal S ρ T)
    (g : ↥(GK K)) (hg : bk.FixFlat g) : zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
  have e := h.gal g
  rw [BK.galHom_comp_ι_of_fixFlat bk g hg, S.ε_refl] at e
  exact e.trans ((congrArg (T * ·) (Matrix.map_one (inclW l) (map_zero _) (map_one _))).trans (Matrix.mul_one T))

theorem MReal.exists_fixed_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧
      (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧
      bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨u, hu⟩ := hT'.unit
  have cancel : ∀ M N : Matrix (Fin d') (Fin d) (WCb l), T' * M = T' * N → M = N := by
    intro M N h
    have h2 := congrArg (fun Z => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * Z) h
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  set Xm : Matrix (Fin d') (Fin d) (WCb l) := (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * (zW f * T) with hXm
  have hX : T' * Xm = zW f * T := by
    rw [hXm, ← hu, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨Xm, hX, fun g hg => ?_, ?_⟩
  · let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
    have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M :=
      fun M => Matrix.ext fun i j => (galW l (g : GQ l)).commutes _
    have a1 : zW (ρ' g) * T'.map G = T' := hT'.gal_of_fixFlat g hg
    have a2 : zW (ρ g) * T.map G = T := hT.gal_of_fixFlat g hg
    change Xm.map G = Xm
    apply cancel
    have h1 := congrArg (fun M => M.map G) hX
    simp only [Matrix.map_mul, hzG] at h1
    calc T' * Xm.map G = zW (ρ' g) * (T'.map G * Xm.map G) := by
          rw [← Matrix.mul_assoc, a1]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = T' * Xm := by rw [a2, hX]
  · let F : WCb l →+* WCb l := (frobW l).toRingHom
    have hzF : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map F = zW M :=
      fun M => Matrix.ext fun i j => (frobW l).commutes _
    have b1 : bk.evW bk.E ^ S.a • T.map F = T * S.A.map bk.evW := hT.φ
    have b2 : bk.evW bk.E ^ S'.a • T'.map F = T' * S'.A.map bk.evW := hT'.φ
    change bk.evW bk.E ^ S.a • (S'.A.map bk.evW * Xm.map F) = bk.evW bk.E ^ S'.a • (Xm * S.A.map bk.evW)
    apply cancel
    have h1 := congrArg (fun M => M.map F) hX
    simp only [Matrix.map_mul, hzF] at h1
    rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, ← b2, Matrix.smul_mul, h1, smul_smul,
      ← Matrix.mul_assoc, hX, Matrix.mul_assoc, ← b1, Matrix.mul_smul, smul_smul, mul_comm]

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolutionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratPeriodMatrix_exists_fixed_frobenius_solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ X : Matrix (Fin d') (Fin d) (WCb l), T' * X = zW f * T ∧ (∀ g : ↥(GK K), bk.FixFlat g → X.map (galW l (g : GQ l)) = X) ∧ bk.evW bk.E ^ S.a • (S'.A.map bk.evW * X.map (frobW l)) = bk.evW bk.E ^ S'.a • (X * S.A.map bk.evW) := by
  first | exact @GlobalTheory.BSP.MReal.exists_fixed_frob | exact GlobalTheory.BSP.MReal.exists_fixed_frob | (intros; apply GlobalTheory.BSP.MReal.exists_fixed_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystems
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnRootsOfPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnRootsOfPrime
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem galois_transitive_on_roots_of_prime (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Prime π) (n : ℕ) (y z : Om l) (hy : y ^ n = ((π : ↥K.1) : Om l))
    (hz : z ^ n = ((π : ↥K.1) : Om l)) (hn : 0 < n) : ∃ g : ↥(GK K), (g : GQ l) y = z := by
  classical

  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : IsFractionRing ↥(OL K) ↥K.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥K.1
  have : IsIntegrallyClosed ↥(OL K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ℚ_[l]
  have hn0 : n ≠ 0 := hn.ne'
  have hmon : (Polynomial.X ^ n - Polynomial.C π).Monic := Polynomial.monic_X_pow_sub_C π hn0

  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C π) := by
    refine Polynomial.irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]
      intro h
      exact hπ.not_isUnit (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 h))
    · intro m hm
      rw [Polynomial.degree_X_pow_sub_C hn π, Nat.cast_lt] at hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hm.ne]
      split_ifs
      · exact Ideal.sub_mem _ (Ideal.zero_mem _) (Ideal.mem_span_singleton_self π)
      · simp
    · rw [Polynomial.degree_X_pow_sub_C hn π]
      exact_mod_cast hn
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hn0.symm,
        if_pos rfl, zero_sub, Ideal.span_singleton_pow, Ideal.neg_mem_iff, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hπ.not_isUnit
      have h1 : π * 1 = π * (π * c) := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc
      exact isUnit_of_dvd_one ⟨c, mul_left_cancel₀ hπ.ne_zero h1⟩

  have hirrF : Irreducible (Polynomial.X ^ n - Polynomial.C ((π : ↥K.1))) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥K.1)).1 hirr
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  have hmin : ∀ w : Om l, w ^ n = ((π : ↥K.1) : Om l) →
      minpoly (↥K.1) w = Polynomial.X ^ n - Polynomial.C ((π : ↥K.1)) := by
    intro w hw
    refine (minpoly.eq_of_irreducible_of_monic hirrF ?_ (Polynomial.monic_X_pow_sub_C _ hn0)).symm
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.algebraMap_apply, hw, sub_self]

  have : Normal (↥K.1) (Om l) := Normal.tower_top_of_normal ℚ_[l] (↥K.1) (Om l)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥K.1) (E := Om l)).1
    ((hmin z hz).trans (hmin y hy).symm)
  refine ⟨⟨σ.restrictScalars ℚ_[l], ?_⟩, hσ⟩
  show σ.restrictScalars ℚ_[l] ∈ IntermediateField.fixingSubgroup K.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnRootsOfPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ (n : ℕ) (y z : Om l), y ^ n = ((π : ↥K.1) : Om l) → z ^ n = ((π : ↥K.1) : Om l) → 0 < n → ∃ g : ↥(GK K), (g : GQ l) y = z := by
  first | exact @GlobalTheory.galois_transitive_on_roots_of_prime | exact GlobalTheory.galois_transitive_on_roots_of_prime | (intros; apply GlobalTheory.galois_transitive_on_roots_of_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystems
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isClosed_setOf_gal_apply_eq_padic (l : ℕ) [Fact l.Prime] (a b : Om l) :
    IsClosed {g : GQ l | g a = b} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (MulAction.stabilizer (GQ l) a : Set (GQ l)), ?_,
    (stabilizer_isOpen_of_isIntegral a).preimage (continuous_const.mul continuous_id), ?_⟩
  · intro h hh
    have hs : (g⁻¹ * h) a = a := hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg ⊢
    intro hb
    apply hg
    rw [AlgEquiv.mul_apply] at hs
    have hga := congrArg g hs
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hga
    rw [← hga, hb]
  · show (g⁻¹ * g) a = a
    rw [inv_mul_cancel, AlgEquiv.one_apply]

theorem galois_transitive_on_root_systems_of_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  intro l _ K π hπ y z hy hz hy' hz'
  have hGK : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) := by
    unfold GK
    exact InfiniteGalois.fixingSubgroup_isClosed _

  have hpow : ∀ w : ℕ → Om l, (∀ n, w (n + 1) ^ l = w n) → ∀ m k, w (m + k) ^ (l ^ k) = w m := by
    intro w hw m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul', ← add_assoc, hw, ih]

  let T : ℕ → Set (GQ l) := fun n =>
    (GK K : Set (GQ l)) ∩ ⋂ m, ⋂ (_ : m ≤ n), {g : GQ l | g (y m) = z m}
  have hcl : ∀ n, IsClosed (T n) := fun n =>
    hGK.inter (isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_setOf_gal_apply_eq_padic l (y m) (z m))
  have hdec : ∀ n, T (n + 1) ⊆ T n := by
    rintro n g ⟨h1, h2⟩
    refine ⟨h1, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h2 m) (Nat.le_succ_of_le hm)
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    have hyn : y n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow y hy' 0 n
      rw [zero_add] at h
      rw [h, hy]
    have hzn : z n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow z hz' 0 n
      rw [zero_add] at h
      rw [h, hz]
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime l K π hπ (l ^ n) (y n) (z n) hyn hzn
      (pow_pos (Fact.out : l.Prime).pos n)
    refine ⟨(g : GQ l), g.2, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    show (g : GQ l) (y m) = z m
    rw [← hpow y hy' m k, ← hpow z hz' m k, map_pow, hg]

  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  refine ⟨⟨g, (Set.mem_iInter.1 hg 0).1⟩, fun n => ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hg n).2 n) le_rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystemsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_transitive_on_prime_power_root_systems : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  first | exact @GlobalTheory.galois_transitive_on_root_systems_of_prime | exact GlobalTheory.galois_transitive_on_root_systems_of_prime | (intros; apply GlobalTheory.galois_transitive_on_root_systems_of_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopData
namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc

def InWin (typ : Bool) (h η : ℕ) (u : ℤ) : Prop :=
  if typ then u ≤ (η : ℤ) else (h : ℤ) - η ≤ u

instance (typ : Bool) (h η : ℕ) : DecidablePred (InWin typ h η) := fun u => by
  unfold InWin; infer_instance

theorem count_block (w : ℤ) (t : ℕ) (a : ℤ) :
    (block w t).count a = if w ≤ a ∧ a < w + t then 1 else 0 := by
  split_ifs with ha
  · exact Multiset.count_eq_one_of_mem (Finset.Ico _ _).nodup (mem_block.2 ha)
  · exact Multiset.count_eq_zero.2 fun hm => ha (mem_block.1 hm)

def ofWindow {n r : ℕ} (t : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β) : TopData n r where
  h := h
  η := η
  ty := fun i => if typ i then LType.G else LType.Bd
  w := w
  t := t
  lows := fun i => (U i).filter (InWin (typ i) (h i) (η i))
  cloud := fun i => (U i).filter fun u => ¬ InWin (typ i) (h i) (η i) u
  two_le_h := hh
  one_le_η := hη
  one_le_letterBlockLength := ht
  card_eq := fun i => by rw [Multiset.filter_add_not, hc]
  range := fun i u hu => by
    rw [Multiset.filter_add_not, Multiset.mem_add, mem_block] at hu
    rcases hu with hu | hu
    · exact hU i u hu
    · exact ⟨(hB i u hu.1 hu.2).1, (hB i u hu.1 hu.2).2.1⟩
  lowG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨(hU i u hu.1).1, by simpa [InWin, hi'] using hu.2⟩
    · exact ⟨(hB i u hu.1 hu.2).1, by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2⟩
  cloudG := fun i hi u hu => by
    have hi' : typ i = true := by by_contra hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    simpa [InWin, hi'] using hu.2
  lowBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_add, mem_block, Multiset.mem_filter] at hu
    rcases hu with hu | hu
    · exact ⟨by simpa [InWin, hi'] using hu.2, (hU i u hu.1).2⟩
    · exact ⟨by simpa [InWin, hi'] using (hB i u hu.1 hu.2).2.2, (hB i u hu.1 hu.2).2.1⟩
  cloudBd := fun i hi u hu => by
    have hi' : typ i = false := by by_contra hn; simp at hn; simp [hn] at hi
    rw [Multiset.mem_filter] at hu
    have := hu.2
    simp only [InWin, hi', Bool.false_eq_true, if_false, not_le] at this
    exact this

theorem exists_topData (l n t r : ℕ) (h η : ZMod n → ℕ) (typ : ZMod n → Bool) (w : ZMod n → ℤ)
    (U : ZMod n → Multiset ℤ) (hh : ∀ i, 2 ≤ h i) (hη : ∀ i, 1 ≤ η i) (ht : 1 ≤ t)
    (hc : ∀ i, Multiset.card (U i) = r) (hU : ∀ i, ∀ u ∈ U i, 1 ≤ u ∧ u ≤ (h i : ℤ) - 1)
    (hB : ∀ i (β : ℤ), w i ≤ β → β < w i + t →
      1 ≤ β ∧ β ≤ (h i : ℤ) - 1 ∧ InWin (typ i) (h i) (η i) β)
    (h1 : ∀ i, η i + 4 * GlobalTheory.PhiGam.sg l h i + 6 < l)
    (h2 : ∀ i, ∀ u ∈ U i, InWin (typ i) (h i) (η i) u → ∀ β : ℤ, w i ≤ β → β < w i + t →
      (GlobalTheory.PhiGam.sg l h i : ℤ) + 2 < |u - β|)
    (h3 : ∀ i, ∀ u ∈ U i, ¬ InWin (typ i) (h i) (η i) u → ∀ y : ℤ,
      -2 * (GlobalTheory.PhiGam.sg l h i : ℤ) - 2 ≤ y → y ≤ (η i : ℤ) + 2 * GlobalTheory.PhiGam.sg l h i + 3 →
        ¬ (if typ i then u else (h i : ℤ) - u) ≡ y [ZMOD l]) :
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) =
        ((U i).count a : ℤ) + if w i ≤ a ∧ a < w i + t then 1 else 0) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  have hUeq : ∀ i, (ofWindow t h η typ w U hh hη ht hc hU hB).U i = U i := fun i =>
    Multiset.filter_add_not _ _
  refine ⟨ofWindow t h η typ w U hh hη ht hc hU hB, rfl, fun i => ⟨rfl, hUeq i, fun a => ?_⟩,
    h1, fun i u hu β hβ => ?_, fun i u hu y hy1 hy2 => ?_⟩
  · rw [TopData.Ut, hUeq, Multiset.count_add]
    change (((U i).count a + (block (w i) t).count a : ℕ) : ℤ) = _
    rw [count_block]
    push_cast
    rfl
  · have hu' := Multiset.mem_filter.1 hu
    have hβ' := mem_block.1 hβ
    exact h2 i u hu'.1 hu'.2 β hβ'.1 hβ'.2
  · have hu' := Multiset.mem_filter.1 hu
    have := h3 i u hu'.1 hu'.2 y hy1 hy2
    have he : (ofWindow t h η typ w U hh hη ht hc hU hB).cloudRes i u =
        if typ i then u else (h i : ℤ) - u := by
      cases hi : typ i <;> simp [TopData.cloudRes, ofWindow, hi]
    rw [he]
    exact this

end GlobalTheory.TopWindow
end

namespace GlobalTheory.TopWindow

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem sg_cast_eq (l n : ℕ) (h : ZMod n → ℕ) (i : ZMod n) :
    (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := by
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  simp only [GlobalTheory.PhiGam.sg, tableLineDegreeTwo.sg, Formalism.WachCohomologyFacts.V2.sgN]
  exact Int.natCast_floor_eq_floor h0

theorem inWin_iff (typ : Bool) (h η : ℕ) (u : ℤ) (h1 : 1 ≤ u) (h2 : u ≤ (h : ℤ) - 1) :
    InWin typ h η u ↔ Formalism.WachCohomologyFacts.V2.InWinN typ h η u := by
  unfold InWin Formalism.WachCohomologyFacts.V2.InWinN
  cases typ <;> simp [h1, h2]

theorem exists_topData_of_positionHyps : ∀ (l n t r : ℕ) [NeZero n] (h w η : ZMod n → ℕ)
    (typ : ZMod n → Bool) (U : ZMod n → Multiset ℤ), 2 ≤ l → 1 ≤ t →
    (∀ i, Multiset.card (U i) = r) → tableLineDegreeTwo.PositionHyps l n t h w η typ U →
    ∃ Dt : TopData n r, Dt.t = t ∧
      (∀ i, Dt.w i = w i ∧ Dt.U i = U i ∧ ∀ a, ((Dt.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
      Dt.T1 l ∧ Dt.T2 l ∧ Dt.T3 l := by
  intro l n t r _ h w η typ U _ ht hc hS
  unfold tableLineDegreeTwo.PositionHyps at hS
  have hsg : ∀ i, (GlobalTheory.PhiGam.sg l h i : ℤ) = tableLineDegreeTwo.sg n l h i := fun i => sg_cast_eq l n h i
  obtain ⟨Dt, hDt, hw, h1, h2, h3⟩ := exists_topData l n t r h η typ (fun i => (w i : ℤ)) U
    (fun i => by obtain ⟨-, hw1, hw2, -⟩ := hS i; omega)
    (fun i => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      by_cases hc : typ i = true
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    ht hc (fun i => (hS i).1)
    (fun i β hβ1 hβ2 => by
      obtain ⟨-, hw1, hw2, hG, hB, -⟩ := hS i
      refine ⟨by omega, by omega, ?_⟩
      unfold InWin
      split_ifs with hc
      · have := hG hc; omega
      · have := hB (by simpa using hc); omega)
    (fun i => by have := (hS i).2.2.2.2.2.1; have := hsg i; omega)
    (fun i u hu hin β hβ1 hβ2 => by
      have hr := (hS i).1 u hu
      have hlow := (hS i).2.2.2.2.2.2.1 u
        (by
          classical
          unfold tableLineDegreeTwo.lows
          exact Multiset.mem_filter.2 ⟨hu, (inWin_iff _ _ _ _ hr.1 hr.2).1 hin⟩) β
        (by rw [Formalism.WachCohomologyFacts.Top.GlobalTheory, Finset.mem_Icc]; omega)
      rw [hsg i]
      exact hlow)
    (fun i u hu hin y hy1 hy2 => by
      have hr := (hS i).1 u hu
      have hT := (hS i).2.2.2.2.2.2.2 u
        (by
          classical
          unfold Formalism.WachCohomologyFacts.V2.ClN
          exact Multiset.mem_filter.2 ⟨hu, fun h' => hin ((inWin_iff _ _ _ _ hr.1 hr.2).2 h')⟩) y
        (by have := hsg i; omega) (by have := hsg i; omega)
      intro hmod
      exact hT ((ZMod.intCast_eq_intCast_iff _ _ _).2 hmod))
  refine ⟨Dt, hDt, fun i => ⟨(hw i).1, (hw i).2.1, fun a => ?_⟩, h1, h2, h3⟩
  rw [(hw i).2.2 a]
  unfold tableLineDegreeTwo.jTil
  split_ifs <;> omega

end GlobalTheory.TopWindow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfMemCcAt
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.CutFam

theorem exists_of_mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X)
    {c : O} (hc : c ∈ ccAt T Z π) : ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = c := by
  unfold ccAt Ideal.map at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨f, hf, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, add_mem hf hg, rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨algebraMap O T r * f, Ideal.mul_mem_left _ _ hf, ?_⟩
    simp [smul_eq_mul]

theorem mem_ccIdeal_iff {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (f : T) :
    f ∈ ccIdeal T Z ↔ ∀ y, y ∉ Z → (f : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa using this
  · intro h
    funext y
    simpa using h y.1 y.2

theorem exists_ne_zero {O X : Type} [CommRing O] [IsDomain O] [Fintype X] (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X) (hπ : π ∈ Z) :
    ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π ≠ 0 := by
  classical
  have h : ∀ x : {x // x ∉ Z}, ∃ f : T, (f : X → O) x.1 ≠ (f : X → O) π := by
    intro x
    obtain ⟨f, hfT, hf⟩ := hsep x.1 π (fun h => x.2 (h ▸ hπ))
    exact ⟨⟨f, hfT⟩, hf⟩
  choose g hg using h
  refine ⟨∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)), ?_, ?_⟩
  · rw [mem_ccIdeal_iff]
    intro y hy
    change (T.val.toMonoidHom (∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)))) _ = _
    rw [map_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) ?_
    simp
  · change (T.val.toMonoidHom (∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)))) _ ≠ _
    rw [map_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun x _ => ?_
    have e : ∀ c : O, ((algebraMap O T c : T) : X → O) π = c := fun c => by simp
    change ((g x - algebraMap O T ((g x : X → O) x.1) : T) : X → O) π ≠ 0
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, e]
    exact sub_ne_zero.mpr (hg x).symm

theorem length_span {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) = IsDiscreteValuationRing.addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem lenUnit_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) {a b : O}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    lenUnit (O := O) l (O ⧸ Ideal.span {a * b}) =
      lenUnit (O := O) l (O ⧸ Ideal.span {a}) + lenUnit (O := O) l (O ⧸ Ideal.span {b}) := by
  unfold lenUnit
  rw [length_span _ (mul_ne_zero ha hb), length_span _ ha, length_span _ hb,
    IsDiscreteValuationRing.addVal_mul]
  have h1 : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have h2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  rw [ENat.toNat_add h1 h2]
  push_cast
  rw [add_div]

variable {D : D7}

theorem act_bc_eig (i : D.nd.Loc) (f : D.nd.T i) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u = ((f : D.nd.X i → D.nd.O i) x) • u := by
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h
  rw [h, algebraMap_smul]

theorem bc_mem_eig (i : D.nd.Loc) (β : Module.End (D.nd.O i) (D.nd.Mt i))
    (hβ : ∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    β.baseChange (FractionRing (D.nd.O i)) u ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  refine (Submodule.mem_iInf _).mpr fun f => ?_
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  have e : (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) (β.baseChange (FractionRing (D.nd.O i)) u) =
      β.baseChange (FractionRing (D.nd.O i)) ((D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u) := by
    rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← hβ f, LinearMap.baseChange_mul,
      Module.End.mul_apply]
  rw [e, h, map_smul]

theorem perPoint (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) (h : CutAt i k π Xs β b) :
    ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i Xs π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard := by
  classical
  obtain ⟨_, hπZ, hXZ, hcomm, hb0, hbπ, hbout, hblen⟩ := h
  have hπc : π ∈ cutLocus i Xs := by simp [cutLocus, hπZ]
  obtain ⟨f0, hf0, hf0π⟩ := exists_ne_zero (D.nd.T i) (D.nd.T_sep i) _ π hπc
  obtain ⟨c, hc⟩ : ∃ c, ccAt (D.nd.T i) (cutLocus i Xs) π = Ideal.span {c} :=
    ⟨Submodule.IsPrincipal.generator _, (Ideal.span_singleton_generator _).symm⟩
  have hcI : c ∈ ccAt (D.nd.T i) (cutLocus i Xs) π := hc ▸ Ideal.mem_span_singleton_self c
  obtain ⟨g, hg, hgπ⟩ := exists_of_mem_ccAt _ _ _ hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hm : ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) π).comp (D.nd.T i).val.toRingHom) f0 ∈
        ccAt (D.nd.T i) (cutLocus i Xs) π := Ideal.mem_map_of_mem _ hf0
    rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hm
    exact hf0π hm
  refine ⟨D.nd.act i g * β, c * b, ?_, ?_, mul_ne_zero hc0 hb0, ?_, ?_⟩
  · intro f
    rw [mul_assoc, hcomm f, ← mul_assoc, ← map_mul, mul_comm g f, map_mul, mul_assoc]
  · intro x hx u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply]
    by_cases hxs : x ∈ Xs
    · have hxZ : x ∉ D.nd.Z i := fun hz => hx (hXZ x hxs hz)
      have hxc : x ∉ cutLocus i Xs := by simp [cutLocus, hxZ, hxs]
      rw [act_bc_eig i g x (bc_mem_eig i β hcomm x hu), (mem_ccIdeal_iff _ _ g).mp hg x hxc, zero_smul]
    · rw [hbout x hxs u hu, map_zero]
  · intro u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply, hbπ u hu, LinearMap.map_smul_of_tower,
      act_bc_eig i g π hu, hgπ, smul_smul, mul_comm]
  · unfold vccCut
    rw [lenUnit_mul _ hc0 hb0, ← hc]
    linarith

theorem fam_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ),
    CongruenceLocalDecomposition CT i k ρ eta → CongruenceFamilyEndomorphisms CT i k ρ eta := by
  intro D CT i k ρ eta hcut
  classical
  obtain ⟨Xs, β, b, h⟩ := hcut
  have hp : ∀ π ∈ D.nd.Zgood i, ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i (Xs π) π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard :=
    fun π hπ => perPoint i k π (Xs π) (β π) (b π) (h π hπ).1
  choose! α a hα using hp
  refine ⟨α '' ((D.nd.Zgood i : Finset (D.nd.X i)) : Set (D.nd.X i)), a, fun π => vccCut i (Xs π) π, ?_, ?_⟩
  · rintro _ ⟨π, hπ, rfl⟩
    exact ⟨(hα π hπ).1, (hα π hπ).2.1⟩
  · intro π hπ
    obtain ⟨_, _, h3, h4, h5⟩ := hα π hπ
    exact ⟨h3, ⟨α π, ⟨π, hπ, rfl⟩, h4⟩, h5, (h π hπ).2⟩

end GlobalTheory.CutFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTilt
namespace GlobalTheory.ArtinSchreierTilt

open Formalism.BasicNotions.Loc

namespace Div

open scoped NNReal
open _root_.Ideal

section General

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))] [IsAdicComplete (span {(p : O)}) O]

noncomputable def lift (u : PreTilt O p) (m : ℕ) : O :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[m]) u)

theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

theorem dvd_of_val_le (x y : PreTilt O p)
    (h : PreTilt.val K v O hv p x ≤ PreTilt.val K v O hv p y) : y ∣ x := by
  by_cases hx : x = 0
  · exact hx ▸ dvd_zero y
  by_cases hy : y = 0
  · exfalso
    apply hx
    rw [← PreTilt.map_eq_zero hv]
    rw [hy, map_zero] at h
    exact le_antisymm h zero_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (algebraMap O K) := hv.hom_inj
  rw [val_eq_untilt hv x hx, val_eq_untilt hv y hy] at h
  have hY : ∀ m, lift y m ≠ 0 := by
    intro m h0
    apply hy
    rw [← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0,
      zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]
  have hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m)) := by
    intro m
    have h' := h
    rw [← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow] at h'
    exact (pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'
  choose q hq using fun m => hv.dvd_of_le (hle m)
  have hqs : ∀ m, q (m + 1) ^ p = q m := by
    intro m
    have h1 : lift y m * q (m + 1) ^ p = lift y m * q m := by
      rw [← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]
    have hK : algebraMap O K (lift y m) ≠ 0 := fun h0 => hY m (hinj (h0.trans (map_zero _).symm))
    apply hinj
    have h2 := congrArg (algebraMap O K) h1
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel₀ hK h2
  let e : PreTilt O p :=
    (⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by
      simp only
      rw [← map_pow, hqs]⟩ : Perfection (ModP O p) p)
  refine ⟨e, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n x = PreTilt.coeff n (y * e)
  rw [map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]
  rfl

end General

end Div

section Complete

open scoped NNReal
open _root_.Ideal

variable {p : ℕ} [Fact p.Prime]

theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominatorsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) → ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  first | exact @GlobalTheory.BSP.BddDen.main | exact GlobalTheory.BSP.BddDen.main | (intros; apply GlobalTheory.BSP.BddDen.main <;> assumption)
end
end
