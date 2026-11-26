module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLatticeBoundIntegers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFundamentalDomainDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisMemLatticeSubStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_mem_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ) (c : Acris l), Lat.pk l k (ACris.iota ℂ_[l] l c) ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatCris.cris_in | exact GlobalTheory.CompanionTheory.LatCris.cris_in | (intros; apply GlobalTheory.CompanionTheory.LatCris.cris_in <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC.Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem ι_lam_ainf (h : LevHyp l K M) (k : ℕ) (w : Ainf l) :
    (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) = fk l k w := by
  show pk l k (ACris.iota ℂ_[l] l (algebraMap (Ainf l) (Acris l) w)) = _
  rw [ACris.iota_algebraMap]
  rfl

theorem pk_mem_of_theta (k : ℕ) {d : BdRp l} (hd : IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l d = 0) :
    pk l k d ∈ IB (fk l k) (xi0 l) := by
  have h1 : d ∈ RingHom.ker (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l) := hd
  rw [IsPerfectoidField.ker_thetaBDeRhamPlusField, ker_thetaBDeRhamPlus ker_theta0,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem xi_and_sub_mem_I (h : LevHyp l K M) (k : ℕ) :
    (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧
      ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
        algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  refine ⟨?_, fun a w hw => ?_⟩
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    rw [ι_lam_ainf]
    exact Ideal.mem_span_singleton_self _
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    have e : (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = pk l k (kP l K (a : K)) := rfl
    have e2 : (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := ι_lam_ainf h k w
    have e3 : (lev h k).ι (algebraMap (OK l K) (lev h k).A a -
        (lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (kP l K (a : K) - wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := by
      rw [map_sub, e, e2, map_sub]
    rw [e3]
    apply pk_mem_of_theta
    rw [map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, sub_eq_zero]
    have := thetaAlgHom_algClToBdR l (K.val (a : K))
    rw [thetaAlgHom_apply] at this
    refine this.trans ?_
    show _ = ((theta0 l w : OC l) : ℂ_[l])
    rw [hw]
    rfl

end GlobalTheory.CompanionTheory.LatC.Red
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompatStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_xi_mem_ideal_and_theta_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧ ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a → algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  first | exact @GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | exact GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I | (intros; apply GlobalTheory.CompanionTheory.LatC.Red.xi_and_sub_mem_I <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphism
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatSigDP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem exists_gB_xi (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    ∃ u : Ainf l, gB h k g (fk l k (xi0 l)) = fk l k (u * xi0 l) := by
  obtain ⟨u, hu⟩ := GlobalTheory.CompanionTheory.TwFil.exists_gal_xi (toBot g.1)
  refine ⟨u, ?_⟩
  have e : galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (u * xi0 l) := by
    rw [← hu, ← gal_smul_wittToBDeRhamPlus]
    rfl
  show Ideal.Quotient.mk _ (galBdRHom (toBot g.1) (wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l))) = _
  rw [e]
  rfl

theorem sigA_isDPMorphism (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) :
    IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  obtain ⟨u, hu⟩ := exists_gB_xi h k g
  exact GlobalTheory.CompanionTheory.LatDP.isDPMorphism_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) u hu
    (h.hc k) (h.hc k)

end GlobalTheory.CompanionTheory.LatSigDP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g, IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  first | exact @GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | exact GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisA
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisA
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_gB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (x : Bk l (k + 1)) :
    dk l k (gB h (k + 1) g x) = gB h k g (dk l k x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [dk, gB, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

theorem levSys_dA_σA {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g a,
    (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  intro m g a
  apply Subtype.ext
  exact dk_gB h (m + 1) g a.1

end GlobalTheory.CompanionTheory.LatLevel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisAStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_system_transition_galois_A : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g a, (levSys h).dA m (((levSys h).L (m + 1)).σA g a) = ((levSys h).L m).σA g ((levSys h).dA m a) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | exact GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA | (intros; apply GlobalTheory.CompanionTheory.LatLevel.levSys_dA_σA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToB
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToB
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem algebraMap_pInv {l : ℕ} [Fact l.Prime] (z : ↥(algebraMap (BdRp l) (BdR l)).range) :
    algebraMap (BdRp l) (BdR l) (pInv l z) = z.1 :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply z)

theorem iota_lam_eq_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c →
      (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  intro c y hy
  have h1 : (lev h k).ι ((lev h k).lam c) = pk l k (ACris.iota ℂ_[l] l c) := rfl
  have h2 : (lev h k).toB y = pk l k (pInv l y) := rfl
  rw [h1, h2]
  congr 1
  apply IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  exact hy.symm.trans (algebraMap_pInv y).symm

end GlobalTheory.CompanionTheory.LatC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaLamEqToBStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_iota_lam_eq_toB : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c → (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | exact GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_lam_eq_toB <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem toB_on_K : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  intro l _ K M h k a y hy
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) := fun x y h =>
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h
  have key : pInv l y = kP l K a := by
    apply hinj
    have h1 : algebraMap (BdRp l) (BdR l) (pInv l y) = y.1 := by
      have := (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply y
      exact congrArg Subtype.val this
    rw [h1]
    exact hy
  show pk l k (pInv l y) = pk l k (kP l K a)
  rw [key]

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapFieldStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_algebraMap_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.toB_on_K | exact GlobalTheory.CompanionTheory.LatC.toB_on_K | (intros; apply GlobalTheory.CompanionTheory.LatC.toB_on_K <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMem
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dk_fk (l : ℕ) [Fact l.Prime] (k : ℕ) (w : Ainf l) :
    Lat.dk l k (Lat.fk l (k + 1) w) = Lat.fk l k w := by
  simp only [Lat.dk, Lat.fk, RingHom.comp_apply]
  exact Ideal.Quotient.factor_mk _ _

theorem dk_dpE (l : ℕ) [Fact l.Prime] (M k i : ℕ) :
    Lat.dk l k (Lat.dpE (Lat.fk l (k + 1)) (xi0 l) l M i) = Lat.dpE (Lat.fk l k) (xi0 l) l M i := by
  simp only [Lat.dpE, Lat.η, map_rat_smul, map_pow, dk_fk]

theorem dk_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) :
    ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  intro x hx
  have hle : Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M ≤
      (Lat.sub (Lat.fk l k) (xi0 l) l M).comap (Lat.dk l k) := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨w, rfl⟩ | ⟨i, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_fk]
      exact Subring.subset_closure (Or.inl ⟨w, rfl⟩)
    · refine Subring.mem_comap.2 ?_
      rw [dk_dpE]
      exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  exact hle hx

end GlobalTheory.CompanionTheory.LatLevel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMemStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sub_reduction_mem : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | exact GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatPdpB

variable (l : ℕ) [Fact l.Prime]

theorem span_xi_eq_span_fontaine_t :
    Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)} = Ideal.span {tBdR l} := by
  haveI : IsPerfectoidField ℂ_[l] l := IsPerfectoidField.padicComplex l
  have hg := IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  generalize IsPerfectoidField.kerThetaGenerator ℂ_[l] l = g at hg
  have hnorm : ∀ z : normInteger ℂ_[l], ‖(z : ℂ_[l])‖ ≤ 1 := fun z => mem_normInteger.1 z.2
  have hbound : ∀ w : WittVector l (PreTilt (normInteger ℂ_[l]) l),
      WittVector.fontaineTheta (normInteger ℂ_[l]) l w = 0 →
      ‖((PreTilt.untilt (WittVector.constantCoeff w) : normInteger ℂ_[l]) : ℂ_[l])‖ ≤
        ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
    intro w hw
    have h1 : Ideal.Quotient.mk (Ideal.span {(l : normInteger ℂ_[l])})
        (PreTilt.untilt (WittVector.constantCoeff w)) = 0 := by
      rw [PreTilt.mk_untilt_eq_coeff_zero]
      have h2 := WittVector.mk_fontaineTheta (R := normInteger ℂ_[l]) (p := l) w
      rw [hw, map_zero] at h2
      exact h2.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨z, hz⟩ := h1
    rw [← hz, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hnorm z)
  have hx : xi0 l ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := by
    rw [RingHom.mem_ker, CrystallineSemistableComparison.xi0, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller,
      untilt_pFlat, sub_self]
  rw [hg, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  have hg0 : WittVector.fontaineTheta (normInteger ℂ_[l]) l g = 0 := by
    rw [← RingHom.mem_ker, hg]
    exact Ideal.mem_span_singleton_self g
  have hcn : WittVector.fontaineTheta (normInteger ℂ_[l]) l c ≠ 0 := by
    intro hc0
    have hcm : c ∈ RingHom.ker (WittVector.fontaineTheta (normInteger ℂ_[l]) l) := hc0
    rw [hg, Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, hd⟩ := hcm
    have hxe : xi0 l = d * g * g := by rw [← hc, ← hd]
    have hco := congrArg WittVector.constantCoeff hxe
    have hT : WittVector.constantCoeff (WittVector.teichmuller l (pFlat l)) = pFlat l :=
      WittVector.teichmuller_coeff_zero l _
    rw [CrystallineSemistableComparison.xi0, map_sub, map_natCast, hT, map_mul, map_mul,
      CharP.cast_eq_zero (PreTilt (normInteger ℂ_[l]) l) l, zero_sub] at hco
    have hpf : pFlat l = (-WittVector.constantCoeff d) * WittVector.constantCoeff g *
        WittVector.constantCoeff g := by
      rw [neg_mul, neg_mul, ← hco, neg_neg]
    have hu := congrArg (fun y => ‖((PreTilt.untilt y : normInteger ℂ_[l]) : ℂ_[l])‖) hpf
    simp only [map_mul, Subring.coe_mul, norm_mul, untilt_pFlat] at hu
    have hb := hbound g hg0
    have hd1 := hnorm (PreTilt.untilt (-WittVector.constantCoeff d))
    have hpos : 0 < ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ := by
      rw [norm_pos_iff]; push_cast; exact natCast_p_ne_zero_cp
    have hlt : ‖((l : normInteger ℂ_[l]) : ℂ_[l])‖ < 1 :=
      IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l
    have hn0 := norm_nonneg ((PreTilt.untilt (WittVector.constantCoeff g) : normInteger ℂ_[l]) : ℂ_[l])
    have hn1 := norm_nonneg ((PreTilt.untilt (-WittVector.constantCoeff d) : normInteger ℂ_[l]) : ℂ_[l])
    nlinarith [mul_le_mul hb hb hn0 hpos.le, mul_le_mul_of_nonneg_right hd1 (mul_nonneg hn0 hn0),
      mul_lt_of_lt_one_left hpos hlt]
  have hcu : IsUnit (wittToBDeRhamPlus (normInteger ℂ_[l]) l c) := by
    by_contra hnu
    have hm : wittToBDeRhamPlus (normInteger ℂ_[l]) l c ∈
        IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker,
      IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at hm
    exact hcn (by exact_mod_cast hm)
  rw [← hc, map_mul, Ideal.span_singleton_mul_left_unit hcu,
    ← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hg, maximalIdeal_eq_span_tBdR]

theorem span_fk_pow (k r : ℕ) :
    Ideal.span {fk l k (xi0 l) ^ r} = Ideal.span {pk l k (tBdR l) ^ r} := by
  have h2 : Ideal.span {wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l) ^ r} =
      Ideal.span {tBdR l ^ r} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow, span_xi_eq_span_fontaine_t]
  have h3 := congrArg (Ideal.map (pk l k)) h2
  simp only [Ideal.map_span, Set.image_singleton, map_pow] at h3
  exact h3

theorem pInv_eq_tBdR {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (t : (per l K).P)
    (ht : (t : (per l K).B) = (per l K).tB) : pInv l t = tBdR l := by
  have hi : GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l) = tBdR l :=
    GroundTheory.PAdicHodge.ACris.iota_periodT (ε := epsilon l) untilt_epsilon
  have key : (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).rangeRestrict (tBdR l) = t := by
    apply Subtype.ext
    refine Eq.trans ?_ ht.symm
    show algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (tBdR l) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)
        (GroundTheory.PAdicHodge.ACris.iota ℂ_[l] l (Formalism.Per6.tA l))
    rw [hi]
  rw [← key]
  unfold CrystallineSemistableComparison.Pb.Lat.pInv
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (RingEquiv.symm_apply_eq _).2 rfl

end GlobalTheory.CompanionTheory.LatPdpB


open GlobalTheory.CompanionTheory.LatPdpB in
theorem GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  intro l _ K M h k r t ht
  show pdP (γB (fk l k) (xi0 l)) r = Ideal.span {(pk l k) (pInv l t) ^ r}
  rw [GlobalTheory.CompanionTheory.DPFiltration.pdP_γB, pInv_eq_tBdR l t ht, span_fk_pow]
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPowStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_filtration_span_t_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | exact GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | (intros; apply GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatible
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem existsUnique_limit_of_dvd {R : Type*} [CommRing R] (t : R)
    [IsAdicComplete (Ideal.span {t}) R] (z : ℕ → R)
    (hz : ∀ m, t ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃! x : R, ∀ m, t ^ (m + 1) ∣ x - z m := by
  have hmem : ∀ (n : ℕ) (a : R), a ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule R R) ↔ t ^ n ∣ a := by
    intro n a
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hchain : ∀ {m n : ℕ}, m ≤ n → t ^ m ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have h1 : t ^ m ∣ z (n + 1) - z n := (pow_dvd_pow t (by omega)).trans (hz n)
      have h2 := dvd_add h1 ih
      simpa using h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {t}) z (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, hmem]
    exact hchain hmn)
  refine ⟨L, fun m => ?_, fun x hx => ?_⟩
  · have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
      have := hL (m + 1)
      rw [SModEq.comm, SModEq.sub_mem, hmem] at this
      exact this
    have h2 := dvd_add h1 (hz m)
    simpa using h2
  · have hLd : ∀ m, t ^ (m + 1) ∣ L - z m := by
      intro m
      have h1 : t ^ (m + 1) ∣ L - z (m + 1) := by
        have := hL (m + 1)
        rw [SModEq.comm, SModEq.sub_mem, hmem] at this
        exact this
      have h2 := dvd_add h1 (hz m)
      simpa using h2
    refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {t}) _ fun n => ?_)
    rw [SModEq.zero, hmem]
    have h3 := dvd_sub (hx n) (hLd n)
    have h4 : t ^ (n + 1) ∣ x - L := by simpa using h3
    exact (pow_dvd_pow t (Nat.le_succ n)).trans h4

theorem isAdicComplete_span_tBdR (l : ℕ) [Fact l.Prime] :
    IsAdicComplete (Ideal.span {tBdR l}) (BdRp l) := by
  rw [← maximalIdeal_eq_span_tBdR]
  exact IsPerfectoidField.instIsAdicCompleteMaximalIdealBdR

theorem pInv_rangeRestrict (l : ℕ) [Fact l.Prime] (b : BdRp l) :
    pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b) = b :=
  RingEquiv.symm_apply_apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩) b

theorem pInv_injective (l : ℕ) [Fact l.Prime] : Function.Injective (pInv l) :=
  (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm.injective

theorem existsUnique_bdRp_of_compatible (l : ℕ) [Fact l.Prime]
    (y : ∀ m : ℕ, Bk l (m + 1)) (hy : ∀ m, dk l (m + 1) (y (m + 1)) = y m) :
    ∃! x : BdRp l, ∀ m, pk l (m + 1) x = y m := by
  haveI := isAdicComplete_span_tBdR l
  choose z hz using fun m => Ideal.Quotient.mk_surjective (y m)
  have key : ∀ (m : ℕ) (x : BdRp l), pk l (m + 1) x = y m ↔ tBdR l ^ (m + 1) ∣ x - z m := by
    intro m x
    rw [← hz m, pk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have hstep : ∀ m, tBdR l ^ (m + 1) ∣ z (m + 1) - z m := by
    intro m
    rw [← key m]
    have := hy m
    rw [← hz (m + 1)] at this
    exact this
  obtain ⟨x, hx, hu⟩ := existsUnique_limit_of_dvd (tBdR l) z hstep
  exact ⟨x, fun m => (key m x).2 (hx m), fun x' hx' => hu x' fun m => (key m x').1 (hx' m)⟩

theorem levSys_existsUnique {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    {M : ℕ} (h : LevHyp l K M) :
    ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) →
      ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  intro y hy
  obtain ⟨b, hb, hu⟩ := existsUnique_bdRp_of_compatible l y hy
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict b, fun m => ?_, fun x' hx' => ?_⟩
  · change pk l (m + 1) (pInv l ((algebraMap (BdRp l) (BdR l)).rangeRestrict b)) = y m
    rw [pInv_rangeRestrict]
    exact hb m
  · refine pInv_injective l ?_
    rw [pInv_rangeRestrict]
    exact hu _ hx'

end GlobalTheory.CompanionTheory.LatC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniquePeriodOfCompatibleStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_period_of_compatible : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ y : ∀ m, ((levSys h).L m).B, (∀ m, (levSys h).dB m (y (m + 1)) = y m) → ∃! x : (per l K).P, ∀ m, ((levSys h).L m).toB x = y m := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | exact GlobalTheory.CompanionTheory.LatC.levSys_existsUnique | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_existsUnique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesField
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem sigmaB_fixes_K {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : ∀ g (a : K),
    (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  intro g a
  have key : gP l g (kP l K a) = kP l K a := by
    have h1 : galBdRHom (toBot g.1) (algClToBdR l (a : PadicAlgCl l))
        = algClToBdR l ((toBot g.1) (a : PadicAlgCl l)) :=
      gal_smul_algClToBdR (toBot g.1) (a : PadicAlgCl l)
    have h2 : (toBot g.1) (a : PadicAlgCl l) = (a : PadicAlgCl l) := g.2 a
    rw [h2] at h1
    exact h1
  change gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  change Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = Ideal.Quotient.mk _ (kP l K a)
  rw [Ideal.quotientMap_mk, key]

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesFieldStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_fixes_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : K), (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | exact GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisB
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevel

theorem dB_sigmaB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) : ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) =
      ((levSys h).L m).σB g ((levSys h).dB m b) := by
  intro m g b
  change Bk l (m + 1 + 1) at b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  show dk l (m + 1) (gB h (m + 1 + 1) g (Ideal.Quotient.mk _ x)) =
    gB h (m + 1) g (dk l (m + 1) (Ideal.Quotient.mk _ x))
  simp only [gB, dk, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

end GlobalTheory.CompanionTheory.LatLevel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionGaloisBStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_system_transition_galois_B : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m g b, (levSys h).dB m (((levSys h).L (m + 1)).σB g b) = ((levSys h).L m).σB g ((levSys h).dB m b) := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | exact GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dB_sigmaB <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevels

theorem pInv_surjective (l : ℕ) [Fact l.Prime] : Function.Surjective (pInv l) := by
  intro x
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩
  unfold pInv
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x

theorem toB_surjective {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : Function.Surjective (lev h k).toB := by
  have h1 : Function.Surjective ((pk l k).comp (pInv l)) := by
    rw [RingHom.coe_comp]
    exact (Ideal.Quotient.mk_surjective).comp (pInv_surjective l)
  exact h1

end GlobalTheory.CompanionTheory.LatLevels
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjectiveStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_surjective : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), Function.Surjective (lev h k).toB := by
  first | exact @GlobalTheory.CompanionTheory.LatLevels.toB_surjective | exact GlobalTheory.CompanionTheory.LatLevels.toB_surjective | (intros; apply GlobalTheory.CompanionTheory.LatLevels.toB_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCSig

variable {p : ℕ} [Fact p.Prime] {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galCp_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_galCp σ) (continuous_galCp τ)) fun a => ?_
  show galCp σ (a : ℂ_[p]) = galCp τ (a : ℂ_[p])
  rw [galCp_coe, galCp_coe, h]

theorem galMap_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

theorem galAway_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt (normInteger ℂ_[p]) p)))
    (RingHom.ext fun w => by
      simp only [RingHom.comp_apply, galAway_algebraMap]
      rw [AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

theorem galQuot_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk]
    rw [galAway_congr σ τ h])

theorem galBdRHom_congr (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[K'] PadicAlgCl p)
    (h : ∀ y, σ y = τ y) : galBdRHom σ = galBdRHom τ :=
  RingHom.ext fun x => IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, galQuot_congr σ τ h]

theorem gP_iota {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (c : Acris l) :
    gP l g (ACris.iota ℂ_[l] l c) =
      ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c) := by
  have h := ACris.iota_gal_smul (IntermediateField.fixingSubgroupEquiv K g) c
  rw [ACris.gal_smul_def, gal_smul_bdR_def] at h
  rw [h]
  exact congrArg (fun f => f (ACris.iota ℂ_[l] l c))
    (galBdRHom_congr (toBot g.1) (IntermediateField.fixingSubgroupEquiv K g) fun y => rfl)

theorem sig_lam : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ), ∀ g c,
    (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  intro l _ K M h k g c
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (ACris.iota ℂ_[l] l c)) =
    pk l k (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) c))
  rw [← gP_iota]
  exact Ideal.quotientMap_mk

end GlobalTheory.CompanionTheory.LatCSig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelLamGaloisEquivariantStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_lam_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g c, (lev h k).σA g ((lev h k).lam c) = (lev h k).lam ((per l K).σA g c) := by
  first | exact @GlobalTheory.CompanionTheory.LatCSig.sig_lam | exact GlobalTheory.CompanionTheory.LatCSig.sig_lam | (intros; apply GlobalTheory.CompanionTheory.LatCSig.sig_lam <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegers
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem gP_kP {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (x : K) : gP l g (kP l K x) = kP l K x := by
  have h1 : (toBot g.1) • algClToBdR l (K.val x) = algClToBdR l ((toBot g.1) (K.val x)) :=
    gal_smul_algClToBdR _ _
  have h2 : (toBot g.1) (K.val x) = K.val x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
  rw [h2] at h1
  exact h1

theorem sigA_fix : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  intro l _ K M h k g a
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  show Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = _
  rw [Ideal.quotientMap_mk, gP_kP]
  rfl

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegersStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_fixes_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigA_fix | exact GlobalTheory.CompanionTheory.LatC.sigA_fix | (intros; apply GlobalTheory.CompanionTheory.LatC.sigA_fix <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegers
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem iota_algebraMap_OK : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  intro l _ K M h k a
  rfl

end GlobalTheory.CompanionTheory.LatC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelIotaAlgebraMapIntegersStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_iota_algebraMap_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ a : OK l K, (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = algebraMap K (lev h k).B (a : K) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | exact GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK | (intros; apply GlobalTheory.CompanionTheory.LatC.iota_algebraMap_OK <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem pInv_algebraMap (l : ℕ) [Fact l.Prime] (b : BdRp l) (hb : algebraMap (BdRp l) (BdR l) b ∈ (algebraMap (BdRp l) (BdR l)).range) :
    pInv l ⟨algebraMap (BdRp l) (BdR l) b, hb⟩ = b := by
  have : (⟨algebraMap (BdRp l) (BdR l) b, hb⟩ : ↥(algebraMap (BdRp l) (BdR l)).range) = (algebraMap (BdRp l) (BdR l)).rangeRestrict b := rfl
  rw [this]
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply b

theorem sigmaB_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y →
      (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  rintro g ⟨_, b, rfl⟩ ⟨y, hy⟩ hxy
  have hy' : y = algebraMap (BdRp l) (BdR l) (gP l g b) := by
    refine (Eq.trans hxy.symm ?_)
    exact galBdRField_algebraMap (toBot g.1) b
  subst hy'
  show gB h k g (pk l k (pInv l ⟨_, _⟩)) = pk l k (pInv l ⟨_, _⟩)
  rw [pInv_algebraMap, pInv_algebraMap]
  rfl

end GlobalTheory.CompanionTheory.LatC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariantStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_galois_equivariant : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y → (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_toB | exact GlobalTheory.CompanionTheory.LatC.sigmaB_toB | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_toB <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatFinal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open DividedPowers

namespace CrystallineSemistableComparison.Pb.Lat

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dp_ι (hc : DPClosed (ι f ξ l M) (γB f ξ)) : IsDPMorphism (γ f ξ l M hc) (γB f ξ) (ι f ξ l M) :=
  ⟨Ideal.map_le_iff_le_comap.2 fun _ hx => hx, fun {n} a ha => (ι_γ f ξ l M hc ha).symm⟩

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

end Map

end CrystallineSemistableComparison.Pb.Lat
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Lat

theorem dp_of_char {K A B A' B' : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Algebra K B']
    {I : Ideal A} {I' : Ideal A'} {J : Ideal B} {J' : Ideal B'} (δ : DividedPowers J) (δ' : DividedPowers J') (ι : A →+* B)
    (ι' : A' →+* B') (s : A →+* A') (g : B →+* B') (hJ : J = I.map ι) (hJ' : J' = I'.map ι') (hs : I.map s ≤ I')
    (h : ∀ a, g (ι a) = ι' (s a)) : IsDPMorphism δ δ' g := by
  have h1 : J.map g ≤ J' := by
    rw [hJ, hJ', Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    change g (ι a) ∈ I'.map ι'
    rw [h]
    exact Ideal.mem_map_of_mem _ (hs (Ideal.mem_map_of_mem _ ha))
  refine ⟨h1, fun {n} a ha => ?_⟩
  have hu : IsUnit (n.factorial : B') := by
    have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 n.factorial_ne_zero) : IsUnit (n.factorial : K)).map (algebraMap K B')
    rwa [map_natCast] at this
  refine hu.mul_left_cancel ?_
  rw [δ'.factorial_mul_dpow_eq_pow (h1 (Ideal.mem_map_of_mem _ ha)), ← map_natCast g, ← map_mul, δ.factorial_mul_dpow_eq_pow ha, map_pow]

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem levHyp_ex [FiniteDimensional ℚ_[l] K] : ∃ M : ℕ, LevHyp l K M :=
  (GlobalTheory.T.exists_lattice_bound_integers l K).imp fun M h => ⟨h, GlobalTheory.T.acris_mem_lattice_sub l M, GlobalTheory.T.fontaine_lattice_dpow_closed l M, GlobalTheory.T.galois_preserves_t_power_span l K,
    fun k g => GlobalTheory.T.galois_preserves_lattice_sub l K M k g _, GlobalTheory.T.lattice_sub_reduction_mem l M⟩

theorem lev_σ_ι (h : LevHyp l K M) (k : ℕ) (g : K.fixingSubgroup) (a : (lev h k).A) :
    (lev h k).ι ((lev h k).σA g a) = (lev h k).σB g ((lev h k).ι a) :=
  ι_map (fk l k) (xi0 l) (fk l k) (xi0 l) l M (gB h k g) (h.gal k g) a

theorem lev_good (h : LevHyp l K M) (k : ℕ) (hk : 1 ≤ k) : (lev h k).Good := by
  exact {
    pos := hk
    lat := GlobalTheory.T.level_lattice_base h k hk
    toB_surj := GlobalTheory.T.level_toB_surjective h k
    toB_ker := GlobalTheory.T.level_toB_eq_zero_iff_t_pow_dvd h k
    toB_K := GlobalTheory.T.level_toB_algebraMap_field h k
    ι_inj := ι_injective (fk l k) (xi0 l) l M
    ι_dp := dp_ι (fk l k) (xi0 l) l M (h.hc k)
    ι_I := rfl
    IB_eq := GlobalTheory.T.level_ideal_eq_map h k
    ι_O := GlobalTheory.T.level_iota_algebraMap_integers h k
    ι_lam := GlobalTheory.T.level_iota_lam_eq_toB h k
    σB_toB := GlobalTheory.T.level_toB_galois_equivariant h k
    σ_ι := lev_σ_ι h k
    σ_lam := GlobalTheory.T.level_lam_galois_equivariant h k
    σ_O := GlobalTheory.T.level_galois_fixes_integers h k
    σ_dp := GlobalTheory.T.level_galois_isDPMorphism h k
    σB_dp g := dp_of_char (K := K) (lev h k).γB (lev h k).γB (lev h k).ι (lev h k).ι ((lev h k).σA g) ((lev h k).σB g)
      (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_ideal_eq_map h k) (GlobalTheory.T.level_galois_isDPMorphism h k g).1 fun a => (lev_σ_ι h k g a).symm
    σB_K := GlobalTheory.T.level_galois_fixes_field h k
    pdP_B := GlobalTheory.T.level_filtration_span_t_pow h k
  }

theorem dk_pk (k : ℕ) (x : BdRp l) : dk l k (pk l (k + 1) x) = pk l k x := rfl

theorem sys_dι (h : LevHyp l K M) (m : ℕ) (a : ((levSys h).L (m + 1)).A) :
    (levSys h).dB m (((levSys h).L (m + 1)).ι a) = ((levSys h).L m).ι ((levSys h).dA m a) :=
  (ι_map (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1)) (h.dIn (m + 1)) a).symm

theorem levSys_good (h : LevHyp l K M) : (levSys h).Good := by
  exact {
    lev m := lev_good h (m + 1) (Nat.le_add_left 1 m)
    dB_toB m x := dk_pk (m + 1) (pInv l x)
    dι := sys_dι h
    dlam m c := Subtype.ext (dk_pk (m + 1) (ACris.iota ℂ_[l] l c))
    dO m a := Subtype.ext (dk_pk (m + 1) (kP l K a))
    dK m k := dk_pk (m + 1) (kP l K k)
    ddp := GlobalTheory.T.level_system_transition_isDPMorphism h
    ddpB m := dp_of_char (K := K) ((levSys h).L (m + 1)).γB ((levSys h).L m).γB ((levSys h).L (m + 1)).ι ((levSys h).L m).ι
      ((levSys h).dA m) ((levSys h).dB m) (GlobalTheory.T.level_ideal_eq_map h (m + 2)) (GlobalTheory.T.level_ideal_eq_map h (m + 1)) (GlobalTheory.T.level_system_transition_isDPMorphism h m).1 (sys_dι h m)
    dσ := GlobalTheory.T.level_system_transition_galois_A h
    dσB := GlobalTheory.T.level_system_transition_galois_B h
    cpl := GlobalTheory.T.existsUnique_period_of_compatible h
  }

theorem levSys_ex [FiniteDimensional ℚ_[l] K] : ∃ S : Kap.LevSys (per l K), S.Good ∧ ∀ m, (S.L m).CrisOK :=
  (levHyp_ex (l := l) (K := K)).elim fun _ h => ⟨levSys h, levSys_good h, fun m => GlobalTheory.T.level_xi_mem_ideal_and_theta_compat h (m + 1)⟩

end CrystallineSemistableComparison.HT
