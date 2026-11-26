module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.LogExist

variable {l : ℕ} [Fact l.Prime]

def logSum (w : Per.AinfP l) (n : ℕ) : Per.AinfP l :=
  ∑ k ∈ Finset.range n, (-1) ^ k * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) * w ^ (k + 1)

theorem logSum_succ (w : Per.AinfP l) (n : ℕ) :
    logSum w (n + 1) = logSum w n + (-1) ^ n * Ring.inverse (((n + 1 : ℕ) : Per.AinfP l)) * w ^ (n + 1) := by
  simp only [logSum, Finset.sum_range_succ]

theorem logSum_cauchy {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    logSum w n ≡ logSum w (n + 1) [SMOD (Per.kerP l ^ n • ⊤ : Submodule (Per.AinfP l) (Per.AinfP l))] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, logSum_succ, sub_add_cancel_left]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hw _)

def logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : Per.BdRp l :=
  (GlobalTheory.RingIface.exists_bdRp_equiv l).choose.symm (AdicCompletion.mk (Per.kerP l) (Per.AinfP l)
    (AdicCompletion.AdicCauchySequence.mk (Per.kerP l) (Per.AinfP l) (logSum w) (logSum_cauchy hw)))

theorem ev_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    Per.ev l n (logP hw) = Ideal.Quotient.mk _ (logSum w n) := by
  rw [← (GlobalTheory.RingIface.exists_bdRp_equiv l).choose_spec.2, logP, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk]
  rfl

theorem factorial_mul_logSum (w : Per.AinfP l) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l) * logSum w n =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) := by
  rw [logSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : n.factorial / (k + 1) * (k + 1) = n.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (Nat.succ_pos k) hkn)
  have hu : ((k + 1 : ℕ) : Per.AinfP l) * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) = 1 :=
    Ring.mul_inverse_cancel _ (GlobalTheory.RingBasics.isUnit_nat l _ (Nat.succ_ne_zero k))
  have hc : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * ((k + 1 : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, hd]
  rw [hc]
  linear_combination (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) * hu

theorem isLogP_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : IsLogP w (logP hw) := by
  intro n
  rw [ev_logP, ← factorial_mul_logSum, map_mul, map_natCast]

theorem exists_isLogP : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u :=
  fun _ _ _ hw => ⟨logP hw, isLogP_logP hw⟩

end GlobalTheory.Pst.LogExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u := by
  first | exact @GlobalTheory.Pst.LogExist.exists_isLogP | exact GlobalTheory.Pst.LogExist.exists_isLogP | (intros; apply GlobalTheory.Pst.LogExist.exists_isLogP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummer
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

variable {l : ℕ} [Fact l.Prime]

theorem map_linv (f : Per.AinfP l →+* Per.AinfP l) : f (linv l) = linv l := by
  have h := congrArg f (mul_linv (l := l))
  rw [map_mul, map_natCast, map_one] at h
  have h2 := mul_linv (l := l)
  linear_combination (linv l) * h - f (linv l) * h2

theorem beta_mem_kerP (ϖ : Per.Fl l) (hu : ϖ.untilt = ((l : ℕ) : Per.OC l)) : beta ϖ ∈ Per.kerP l := by
  rw [← ThetaD.fontaineTheta_eq_zero]
  have h := congrArg (Per.θP l) (l_mul_beta ϖ)
  rw [map_mul, map_sub, map_natCast, ThetaD.fontaineTheta_algebraMap₂, WittVector.fontaineTheta_teichmuller, hu] at h
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (mul_eq_zero.1 (h.trans ?_)).resolve_left hl
  simp

theorem gal_beta (g : GQ l) (ϖ e : Per.Fl l) (h : Per.σF g ϖ = ϖ * e) :
    Per.extP (Per.σA g) (beta ϖ) = beta ϖ + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) +
      beta ϖ * algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) := by
  have e1 : Per.σA g (Per.tm ϖ) = Per.tm ϖ * Per.tm e := by
    have h1 := gal_quot g ϖ e h 1
    simp only [map_one, mul_one, map_sub] at h1
    exact sub_left_injective h1
  rw [beta, map_sub, map_mul, map_one, map_linv, GlobalTheory.RingBasics.awayMap_algebraMap₂, e1, map_mul]
  simp only [GlobalTheory.MemLoc.mu, map_sub, map_one]
  ring

theorem isLogP_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) :
    IsLogP (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) (j t) := by
  intro n
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      LogFun.partial_eq u hu _ _ _ (hf _) hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ (LogFun.mu_mem he) (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

theorem gal_log : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  intro l _ P Co hζ ϖ hr hu u hlog g
  have hd : ∀ m, g (lRoot l m) = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val * lRoot l m := fun m => by
    rw [hζ]; exact isKummer_kummer P g m
  have hd' : ∀ m, g (lRoot l m) / lRoot l m = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (lRoot_ne_zero l m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, lRoot_succ]) 1 (by simp [Co.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [Co.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : Per.σF g ϖ = ϖ * e := gal_eq_mul g ϖ e fun m => by
    rw [hr, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq Co e (kummer P g) y he hy]
  refine IsLogP.add (beta_mem_kerP ϖ hu) (LogFun.mu_mem he1) hlog (isLogP_map he1 hy Co.j_cris) ?_
  have h := IsLogP.gal hlog g
  rwa [gal_beta g ϖ e hxe] at h

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  first | exact @GlobalTheory.Pst.StLat.gal_log | exact GlobalTheory.Pst.StLat.gal_log | (intros; apply GlobalTheory.Pst.StLat.gal_log <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwap
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwap
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp

theorem adjugate_transvection_of_ne {A : Type} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (c : A) :
    (Matrix.transvection a b c).adjugate = Matrix.transvection a b (-c) := by
  have h1 : Matrix.transvection a b c * Matrix.transvection a b (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same a b hab, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection a b c).adjugate
      = (Matrix.transvection a b c).adjugate * (Matrix.transvection a b c * Matrix.transvection a b (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection a b (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne a b hab, one_smul,
          Matrix.one_mul]

theorem rowGen_map_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) :
    (rowGen R (n := n) b a).toRingHom.mapMatrix (genM R n) =
      Matrix.transvection a b Polynomial.X * (Polynomial.C (R := MP R n)).mapMatrix (genM R n) := by
  ext1 i s
  by_cases hi : i = a
  · subst hi
    rw [Matrix.transvection_mul_apply_same]
    simp [genM, rowGen]
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [genM, rowGen, hi]

theorem rowGen_det_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    rowGen R (n := n) b a (genM R n).det = Polynomial.C (genM R n).det := by
  have h := RingHom.map_det (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab, one_mul,
    ← RingHom.map_det] at h
  exact h

theorem rowGen_adjugate_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (t i : Fin n) :
    rowGen R (n := n) b a ((genM R n).adjugate t i) =
      Polynomial.C ((genM R n).adjugate t i) +
        (if i = b then -Polynomial.X * Polynomial.C ((genM R n).adjugate t a) else 0) := by
  have h := RingHom.map_adjugate (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.adjugate_mul_distrib, adjugate_transvection_of_ne a b hab,
    ← RingHom.map_adjugate] at h
  have h2 := congrFun (congrFun h t) i
  refine Eq.trans h2 ?_
  by_cases hi : i = b
  · subst hi
    rw [Matrix.mul_transvection_apply_same]
    simp
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hi]
    simp [hi]

theorem rowGen_cofAct (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MP R n) :
    rowGen R (n := n) b a (cofAct R n f) =
      ((rowGen R (n := n) a b f).map (cofAct R n).toRingHom).comp (Polynomial.C (-1) * Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C x =>
    have e1 : (C x : MP R n) = algebraMap R _ x := rfl
    rw [e1, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
      Polynomial.map_C, Polynomial.C_comp]
    exact congrArg Polynomial.C ((cofAct R n).commutes x).symm
  | add p q hp hq => simp only [map_add (f := _), hp, hq, Polynomial.map_add (f := _), Polynomial.add_comp]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.map_mul, Polynomial.mul_comp]
    refine congrArg₂ (· * ·) rfl ?_
    have e1 : ∀ w : Fin n × Fin n, cofAct R n (X w) = (genM R n).adjugate w.2.rev w.1 := fun w => by
      simp [cofAct]
    rw [e1, rowGen_adjugate_genM R n a b hab]
    by_cases hv : v.1 = b
    · simp [rowGen, hv, e1]
    · simp [rowGen, hv, e1]

theorem cofRel_rowDiv (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ)
    (f g : MP R (m + 1)) (hab : a ≠ b) (h : CofRel R m ν f g) :
    CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  unfold CofRel at h ⊢
  have h1 := congrArg (fun p => (rowGen R (n := m + 1) b a p).coeff k) h
  simp only [map_mul, map_pow, rowGen_det_genM R _ a b hab, rowGen_cofAct R _ a b hab,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h1
  rw [← map_pow, Polynomial.coeff_C_mul] at h1
  have h2 : ((-1 : MP R (m + 1)) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  unfold rowDiv
  rw [zsmul_eq_mul, mul_left_comm, h1]
  push_cast
  rw [mul_left_comm, h2, mul_one]
  rfl

end GlobalTheory.ValCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDual
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem applyWord_hw_cofRel (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (h0 : ν (Fin.last m) = 0) (w : List (Fin (m + 1) × Fin (m + 1) × ℕ)) :
    (∃ μ : Fin (m + 1) → ℕ, IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (applyWord R w (hw R le_rfl ν)) μ) ∧
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (applyWord R w (hw R le_rfl ν)) g := by
  induction w with
  | nil => exact ⟨⟨_, hwRowWeight R _ _ le_rfl ν hν⟩, GlobalTheory.T.exists_cofactorTwist_highestWeight R m ν hν h0⟩
  | cons x w ih =>
    obtain ⟨a, b, k⟩ := x
    obtain ⟨⟨μ, hμ⟩, g, hg, hrel⟩ := ih
    have hstep : applyWord R ((a, b, k) :: w) (hw R le_rfl ν) =
        rowDiv R a b k (applyWord R w (hw R le_rfl ν)) := rfl
    rw [hstep]
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isWeightedHomogeneous_div_and_diag_eq_choose_smul R _ _ μ _ hμ
    refine ⟨h1 a b k, ?_⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨((μ a).choose k) • g, nsmul_mem hg _, ?_⟩
      rw [h2 a k]
      unfold CofRel at hrel ⊢
      rw [map_nsmul, ← hrel, mul_smul_comm]
    · exact ⟨_, zsmul_mem (weylRowDivStable R _ _ le_rfl _ b a k g hg) _, GlobalTheory.T.cofactorTwistRelation_rowDiv_swap R m ν a b k _ g hab hrel⟩

theorem weyl_exists_cofRel : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν,
      ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν hν h0 f hf
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact (applyWord_hw_cofRel R m ν hν h0 w).2
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g, hg, hr⟩ := hx
    obtain ⟨g', hg', hr'⟩ := hy
    refine ⟨g + g', add_mem hg hg', ?_⟩
    unfold CofRel at hr hr' ⊢
    rw [map_add (f := _), ← hr, ← hr', mul_add]
  | smul c x _ hx =>
    obtain ⟨g, hg, hr⟩ := hx
    refine ⟨c • g, Submodule.smul_mem _ c hg, ?_⟩
    unfold CofRel at hr ⊢
    rw [map_smul, ← hr, mul_smul_comm]

end GlobalTheory.ValCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylLatticeExistsCofactorTwistDualStatement
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylLattice_exists_cofactorTwist_dual : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl ν, ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν f g := by
  first | exact @GlobalTheory.ValCmp.weyl_exists_cofRel | exact GlobalTheory.ValCmp.weyl_exists_cofRel | (intros; apply GlobalTheory.ValCmp.weyl_exists_cofRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem flin_pad {K : Type} [Field K] {σ n m : Type} [Fintype n] [Fintype m] {l linv : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) (c : n ⊕ m → K) (u : m → MvPowerSeries σ K) :
    Formalism.L2.Th1.C.flin l linv c (Sum.elim (fun _ => (0 : MvPowerSeries σ K)) u) =
      Formalism.L2.Th1.C.flin l linv (fun j => c (Sum.inr j)) u := by
  unfold Formalism.L2.Th1.C.flin
  congr 1
  rw [Fintype.sum_sum_type]
  simp [hl]


open Formalism.L2.Th1.C in
theorem unitaryInv_rect {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hFr : Frame R l linv ph) (O : Type) [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hF1 : Formalism.L2.Th1.C.F1 R l linv ph)
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (γ : Matrix n m O)
    (hγ : γ.conjTranspose * γ = 1) {σ : Type} (u : m → MvPowerSeries σ K) (hu : ∀ j, IsPt R (u j)) :
    Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (γ i j)) u) ph) (∑ j, PowerSeries.subst (u j) ph) := by
  set P : Matrix n n O := 1 - γ * γ.conjTranspose with hP
  have hPh : P.conjTranspose = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPγ : P * γ = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hγ, Matrix.mul_one, sub_self]
  have hγP : γ.conjTranspose * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hγ, Matrix.one_mul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [show P * P = P * (1 - γ * γ.conjTranspose) from rfl]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPγ, Matrix.zero_mul, sub_zero]
  have hΔ : (Matrix.fromBlocks P γ γ.conjTranspose 0).conjTranspose * Matrix.fromBlocks P γ γ.conjTranspose 0 = 1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose, hPh, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, hPP, hPγ, hγP, hγ, ← Matrix.fromBlocks_one]
    congr 1
    · rw [hP]; abel
    · simp
    · simp
    · simp
  have hu' : ∀ c : n ⊕ m, IsPt R (Sum.elim (fun _ : n => (0 : MvPowerSeries σ K)) u c) := by
    rintro (c | c)
    · exact ⟨by simp, fun k => by simp⟩
    · exact hu c
  have key := unitaryInv K R l linv ph hFr O τ hE hB hF1 hN hA (n ⊕ m)
    (Matrix.fromBlocks P γ γ.conjTranspose 0) hΔ σ (Sum.elim (fun _ : n => 0) u) hu'
  have hph : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hl : PowerSeries.constantCoeff l = 0 := hFr.1.1
  have hli : PowerSeries.constantCoeff linv = 0 := hFr.1.2.2.1
  simp only [Fintype.sum_sum_type, flin_pad hl, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, map_zero] at key
  have h0 : PowerSeries.subst (flin l linv (fun _ : m => (0 : K)) u) ph = 0 := by
    unfold flin
    simp [hli, hph]
  simpa [hph, h0] using key

theorem HostLog.subst_unitary : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  intro p _ g2 g3 s2 ε σ F hD n m _ _ _ γ hγ hγo Θ hΘ
  classical
  obtain ⟨h5, hg2, hg3, hε, hθ, hU, hF, hN⟩ := hD
  obtain ⟨hFr, hF1, hall, hbin⟩ := Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension p, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (Formalism.L2.Th1.D.frobSq (MaximalUnramifiedExtension p) p σ hU).2
  let _ : StarRing (Formalism.L2.Th1.D.BrC.Osub σ) := Formalism.L2.Th1.D.BrC.starO hσ
  let τ : Formalism.L2.Th1.D.BrC.Osub σ →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (Formalism.L2.Th1.D.BrC.Osub σ).subtype
  let γO : Matrix n m (Formalism.L2.Th1.D.BrC.Osub σ) :=
    Matrix.of fun i j => ⟨γ i j, Formalism.L2.Th1.D.BrC.mem_Osub.2 (hγ i j)⟩
  have hun : γO.conjTranspose * γO = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγo a b
    have e : ((if a = b then (1 : Formalism.L2.Th1.D.BrC.Osub σ) else 0 : Formalism.L2.Th1.D.BrC.Osub σ) : MaximalUnramifiedExtension p) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl_def
  set linv := Formalism.L2.Th1.D.expF ℂ_[p] p with hlinv_def
  set ph := PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε) with hph_def
  let t : n → MvPowerSeries m ℂ_[p] := fun i =>
    Formalism.L2.Th1.C.flin l linv (fun j => τ (γO i j)) MvPowerSeries.X
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (Formalism.G.unitBall ℂ_[p]) (t i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1 (fun j => (hall _ (hγ i j).1 (hγ i j).2).1)
      (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hcc : ∀ i, MvPowerSeries.constantCoeff (t i) = 0 := fun i => (hpt i).1
  have hcong := unitaryInv_rect (Formalism.G.unitBall ℂ_[p]) l linv ph hFr (Formalism.L2.Th1.D.BrC.Osub σ) τ
    (fun α => (hall α.1 α.2.1 α.2.2).1) (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz)) hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1) (fun α => (hall α.1 α.2.1 α.2.2).2.2) γO hun
    (MvPowerSeries.X) (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hph0 : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hb0 : ∀ (k : Type) (i : k), MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries k ℂ_[p]) = 0 :=
    fun k i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hFr.1 (MvPowerSeries.constantCoeff_X i)
  set Θt : MvPowerSeries n ℂ_[p] := MvPowerSeries.subst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) Θ with hΘt
  have hΘ' : Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) := hΘ
  have hΘe : Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) = Θt := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  obtain ⟨h3, h4, h5'⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[p] n m t hcc (fun i k => (hpt i).2 k)
    (Formalism.L2.Th1.E.phSum ph) _ hPh0 hΘ'
  rw [hΘe, Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h3
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h5'
  have hid : MvPowerSeries.subst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p]))
      (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) =
      MvPowerSeries.subst t Θt := by
    have hb : MvPowerSeries.HasSubst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 m)
    have hb' : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 n)
    have hlin : MvPowerSeries.HasSubst
        (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
    have ht : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc
    rw [MvPowerSeries.subst_comp_subst_apply hlin hb, hΘt, MvPowerSeries.subst_comp_subst_apply hb' ht]
    congr 1
    funext i
    rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hcc,
      MvPowerSeries.subst_X ht]
    simp only [t, Formalism.L2.Th1.C.flin]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.L2.Th1.C.Pts.subst_l_linv hFr.1 (by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [map_mul, show PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m ℂ_[p]) l = Formalism.InvariantFactorPaths.G7.at1 j l from rfl,
          hb0, mul_zero])]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hb, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_X hb]
    rw [MvPowerSeries.subst_C]
    rfl
  unfold HostLog
  rw [hid, h3, ← mul_assoc]
  refine Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' ?_ h4
  obtain ⟨hc0, hcI⟩ := Formalism.L2.Th1.C.Calc.cong_symm hcong
  have hA0 : MvPowerSeries.constantCoeff (∑ i : m, Formalism.InvariantFactorPaths.G7.at1 i ph : MvPowerSeries m ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hB0 : MvPowerSeries.constantCoeff (-(∑ i, PowerSeries.subst (t i) ph) : MvPowerSeries m ℂ_[p]) = 0 := by
    rw [map_neg, h5', neg_zero]
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.C.mvExp_add hA0 hB0,
    ← sub_eq_add_neg]
  exact fun k => hcI k

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinatesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_unitary_logarithmic_coordinates : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  first | exact @GlobalTheory.KerStd.HostLog.subst_unitary | exact GlobalTheory.KerStd.HostLog.subst_unitary | (intros; apply GlobalTheory.KerStd.HostLog.subst_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.TieLat

section Gen

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E']

def cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : Fin n → E' := fun k => i (x k)

def cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : Sp E n := fun k => i.symm (y k)

theorem cw_cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : cw i (cwInv i y) = y := by
  funext k; simp [cw, cwInv]

theorem cwInv_cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : cwInv i (cw i x) = x := by
  funext k; simp [cw, cwInv]

theorem coe_iO_symm (i : E ≃+* E') (r : 𝓞 E') :
    (((RingOfIntegers.mapRingEquiv i).symm r : 𝓞 E) : E) = i.symm (r : E') := rfl

theorem cwInv_smul (i : E ≃+* E') {n : ℕ} (r : 𝓞 E') (y : Fin n → E') :
    cwInv i (r • y) = (RingOfIntegers.mapRingEquiv i).symm r • cwInv i y := by
  funext k
  simp only [cwInv, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

theorem mem_span_cw (i : E ≃+* E') {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) ↔ cwInv i y ∈ N := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have : cwInv i (fun k => i (x k)) = x := cwInv_cw i x
      rw [this]; exact hx
    | zero =>
      have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
      rw [this]; exact N.add_mem ha hb
    | smul r a _ ha =>
      rw [cwInv_smul]; exact N.smul_mem _ ha
  · intro h
    exact Submodule.subset_span ⟨cwInv i y, h, cw_cwInv i y⟩

theorem isSdLat_of_transport (i : E ≃+* E') (hst : ∀ x, i (star x) = star (i x)) {n : ℕ} (N : Submodule (𝓞 E) (Sp E n))
    (h : IsSDLat E' n (Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))))) :
    IsSdLat N := by
  set L := Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) with hL
  have hmem : ∀ y, y ∈ L ↔ cwInv i y ∈ N := mem_span_cw i N
  have hmem' : ∀ x, cw i x ∈ L ↔ x ∈ N := fun x => by rw [hmem, cwInv_cw]
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨S, hS⟩ := hfg
    refine ⟨S.image (cwInv i), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have : s ∈ L := hS ▸ Submodule.subset_span hs
      exact (hmem s).1 this
    · intro x hx
      have hy : cw i x ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')) := hS ▸ (hmem' x).2 hx
      have key : ∀ y ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')),
          cwInv i y ∈ Submodule.span (𝓞 E) ((S.image (cwInv i) : Finset (Sp E n)) : Set (Sp E n)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (by simpa using ⟨y, hy, rfl⟩)
        | zero =>
          have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
          rw [this]; exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
          rw [this]; exact Submodule.add_mem _ ha hb
        | smul r a _ ha =>
          rw [cwInv_smul]; exact Submodule.smul_mem _ _ ha
      have := key _ hy
      rwa [cwInv_cw] at this
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing (𝓞 E) E).mp hli
  ·
    have hform : ∀ x y : Sp E n, stdH E' n (cw i x) (cw i y) = i (hStd E n x y) := by
      intro x y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [stdH, cw, hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, hst]
    have hrange : ∀ w : E, i w ∈ (algebraMap (𝓞 E') E').range ↔ w ∈ (1 : Submodule (𝓞 E) E) := by
      intro w
      rw [Submodule.mem_one]
      constructor
      · rintro ⟨r, hr⟩
        refine ⟨(RingOfIntegers.mapRingEquiv i).symm r, ?_⟩
        have : i.symm (r : E') = w := by
          have h2 : (r : E') = i w := hr
          rw [h2]; simp
        exact this
      · rintro ⟨r, rfl⟩
        exact ⟨RingOfIntegers.mapRingEquiv i r, rfl⟩
    unfold IsUnimodular dual Formalism.E.hdual
    ext y
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [← hmem' y, hdual (cw i y)]
    constructor
    · intro hy x' hx'
      have h1 := hy (cwInv i x') ((hmem x').1 hx')
      rw [← cw_cwInv i x', hform]
      exact (hrange _).2 h1
    · intro hy x hx
      have h1 := hy (cw i x) ((hmem' x).2 hx)
      rw [hform] at h1
      exact (hrange _).1 h1

theorem span_fg_of_denom (a : 𝓞 E) (ha : a ≠ 0) (A : Set E) (hA : ∀ r ∈ A, IsIntegral ℤ ((a : E) * r)) :
    (Submodule.span (𝓞 E) A).FG := by
  have ha' : (a : E) ≠ 0 := by simpa using ha
  have hfg : (Submodule.span (𝓞 E) {(a : E)⁻¹}).FG := ⟨{(a : E)⁻¹}, by simp⟩
  have hN : IsNoetherian (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := by
    haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := Module.Finite.iff_fg.2 hfg
    infer_instance
  refine isNoetherian_submodule.1 hN _ ?_
  rw [Submodule.span_le]
  intro r hr
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (a : E) * r := ⟨⟨_, hA r hr⟩, rfl⟩
  refine ⟨z, ?_⟩
  rw [Algebra.smul_def]
  change (z : E) * (a : E)⁻¹ = r
  rw [hz]
  field_simp

end Gen

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

theorem tie_sd {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u μ i c) : IsSdLat ((t.rd u μ).N i c) := by
  letI := D.host.cmStar
  have h : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N i c)) := t.O_lat u μ i c ▸ ((t.O u μ).lat i c).2
  exact isSdLat_of_transport t.seam.iE (fun x => by rw [t.seam_ok.2 x]; exact (Examples₂.star_eq_conj _ _).symm) _ h

theorem tie_AA_fg {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : t.amb.AA.FG := by
  obtain ⟨b, hb, hfr⟩ := D.host.AA0.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : (RingOfIntegers.mapRingEquiv t.seam.iE).symm b ≠ 0 := by simpa using hb0
  refine span_fg_of_denom _ ha _ ?_
  rintro r ⟨c, hc, s, hs, rfl⟩
  obtain ⟨w, hw⟩ := hfr s hs
  have hw' : (w : D.host.E) = (b : D.host.E) * s := by
    rw [← Algebra.smul_def]; exact hw
  rw [coe_iO_symm, ← map_mul]
  have hcI : IsIntegral ℤ ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map ((IntermediateField.val D.host.K).restrictScalars ℤ)
  have e : (b : D.host.E) * ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * s) = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * w := by
    rw [hw']; ring
  rw [e]
  exact (hcI.mul (NumberField.RingOfIntegers.isIntegral_coe w)).map (t.seam.iE.symm : D.host.E →+* t.X.E).toIntAlgHom

end Comparison₂

end GlobalTheory.TieLat

theorem GlobalTheory.TieLat.tie_AA_fg_and_sd : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) :=
  fun _ _ _ _ _ _ _ _ _ t => ⟨GlobalTheory.TieLat.tie_AA_fg t, fun u μ i c => GlobalTheory.TieLat.tie_sd t u μ i c⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDualStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) := by
  first | exact @GlobalTheory.TieLat.tie_AA_fg_and_sd | exact GlobalTheory.TieLat.tie_AA_fg_and_sd | (intros; apply GlobalTheory.TieLat.tie_AA_fg_and_sd <;> assumption)
end
end
