module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinfty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMuSemidirectCyclicCoverOfMemGKinfCoeffs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizEqXiRedStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqPowFrob
noncomputable section

namespace GlobalTheory.FrobeniusPower

open Polynomial

theorem ringHom_eq_pow_frob (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F] [CharP F p]
    (φ : F →+* F) : ∃ m : ℕ, ∀ x : F, φ x = x ^ p ^ m := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let ψ : F →ₐ[ZMod p] F :=
    { φ with
      commutes' := fun r =>
        RingHom.congr_fun (RingHom.ext_zmod (φ.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r }
  have hinj : Function.Injective ψ := ψ.toRingHom.injective
  let σ : F ≃ₐ[ZMod p] F := AlgEquiv.ofBijective ψ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2 σ
  refine ⟨n, fun x => ?_⟩
  have h1 : σ x = φ x := rfl
  rw [← h1, ← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem finite_Fq (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [NeZero a] : Finite (GlobalTheory.BKReal.Fq l a) := by
  have hq : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) hl.out.one_lt
  have hp : (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]) ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f (l ^ a)) h
    simp only [coeff_sub, coeff_X_pow, coeff_X, if_true, coeff_zero, if_neg hq.ne] at h2
    simp at h2
  have hsub : ((GlobalTheory.BKReal.resSub l a : Subring (Formalism.BasicNotions.Loc.OCb l)) : Set (Formalism.BasicNotions.Loc.OCb l)) ⊆
      {x | (X ^ (l ^ a) - X : (Formalism.BasicNotions.Loc.OCb l)[X]).IsRoot x} := by
    intro x hx
    have hx' : iterateFrobenius (Formalism.BasicNotions.Loc.OCb l) l a x = x := hx
    rw [iterateFrobenius_def] at hx'
    show Polynomial.eval x (X ^ (l ^ a) - X) = 0
    rw [eval_sub, eval_pow, eval_X, hx', sub_self]
  have h : Finite ↥(GlobalTheory.BKReal.resSub l a) := ((Polynomial.finite_setOf_isRoot hp).subset hsub).to_subtype
  exact h

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : ℕ) [inst : NeZero a]
    (φ : GlobalTheory.BKReal.Fq l a →+* GlobalTheory.BKReal.Fq l a), ∃ (m : ℕ), ∀ (x : GlobalTheory.BKReal.Fq l a),
      (φ : GlobalTheory.BKReal.Fq l a → GlobalTheory.BKReal.Fq l a) x = x ^ l ^ m := by
  intro l hl a _ φ
  haveI := finite_Fq l a
  haveI : IsDomain (GlobalTheory.BKReal.Fq l a) := inferInstanceAs (IsDomain ↥(GlobalTheory.BKReal.resSub l a))
  haveI : CharP (GlobalTheory.BKReal.Fq l a) l :=
    inferInstanceAs (CharP ↥(GlobalTheory.BKReal.resSub l a) l)
  letI : Field (GlobalTheory.BKReal.Fq l a) := (Finite.isDomain_to_isField _).toField
  exact ringHom_eq_pow_frob l (GlobalTheory.BKReal.Fq l a) φ

end GlobalTheory.FrobeniusPower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable (l : ℕ) [hl : Fact l.Prime] (a : ℕ) [NeZero a]

def galFq (g : GQ l) : Fq l a →+* Fq l a :=
  ((Per.σF g).comp (Fq.val l a)).codRestrict (resSub l a) fun x => by
    rw [mem_resSub, RingHom.comp_apply, ← map_pow]
    exact congrArg (Per.σF g) (mem_resSub.1 x.2)

theorem val_galFq (g : GQ l) (x : Fq l a) : Fq.val l a (galFq l a g x) = Per.σF g (Fq.val l a x) := rfl

theorem exists_pow_eq (φ : Fq l a →+* Fq l a) : ∃ m : ℕ, ∀ x, φ x = x ^ l ^ m := by
  first
  | exact @_root_.GlobalTheory.FrobeniusPower.main
  | exact _root_.GlobalTheory.FrobeniusPower.main
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrobeniusPower.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrobeniusPower.main ..)
  | (intro h; exact _root_.GlobalTheory.FrobeniusPower.main h _ (fun _ => Iff.rfl))
  | exact _root_.GlobalTheory.FrobeniusPower.main ‹_› _ (fun _ => Iff.rfl)
  | (apply _root_.GlobalTheory.FrobeniusPower.main <;> first | assumption | exact fun _ => Iff.rfl)

theorem gal_wA_pow (g : GQ l) :
    ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  obtain ⟨m, hm⟩ := exists_pow_eq l a (galFq l a g)
  refine ⟨(m : ZMod a), fun w => ?_⟩
  rw [ZMod.val_natCast, ← pow_eq_pow_mod m (sigma_pow_eq_one l a)]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff]
  change Per.σF g (Fq.val l a (w.coeff n)) = Fq.val l a (((sigma l a ^ m) w).coeff n)
  rw [coeff_sigma_pow, ← hm, val_galFq]

end GlobalTheory.BKReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_cyclotomic_power : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  first | exact @GlobalTheory.BKReal.gal_wA_pow | exact GlobalTheory.BKReal.gal_wA_pow | (intros; apply GlobalTheory.BKReal.gal_wA_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmuller
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CoverGen

open GlobalTheory.KinfCover

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]

theorem covers_of_sigma_teich {k : GQ l} (s : ZMod a) (z : Fq l a) (hze : z ^ e = 1)
    (hs : ∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w))
    (hz : ϖ.kummer k = Fq.val l a z) : ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  let ζ : rootsOfUnity e K := rootsOfUnity.mkOfPowEq (algebraMap O K (t (WittVector.teichmuller l z))) (by
    rw [← map_pow, ← map_pow, ← map_pow, hze, map_one, map_one, map_one])
  refine ⟨⟨ζ, Multiplicative.ofAdd s⟩, fun f f' hf' => ?_⟩
  set m : ℕ := s.val with hmdef
  have hms : ((m : ℕ) : ZMod a) = s := ZMod.natCast_zmod_val s
  set c : ZMod a → O := fun τ => emb t τ (WittVector.teichmuller l z) with hc
  have hroot : ∀ τ, TameGal.root (⟨ζ, Multiplicative.ofAdd s⟩ : TameGal K l e a) τ =
      algebraMap O K (c τ) := fun τ => by
    have h1 : c τ = t (WittVector.teichmuller l z) ^ l ^ (-τ).val := by
      change t ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z)) = _
      rw [sigma_pow_teich, map_pow]
    rw [h1, map_pow]
    change (((ζ ^ l ^ (-τ).val : rootsOfUnity e K) : Kˣ) : K) = _
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.coe_mkOfPowEq]
  have hf'' : ∀ τ, f' τ = equivA O K (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := fun τ => by
    refine Subtype.ext ?_
    rw [hf' τ, ringAct_apply, hroot, coe_equivA, ← rescale_map, ← coe_equivA, AlgEquiv.apply_symm_apply, hms]
    rfl
  have hRHS : ϖ.iTot t K f' =
      ∑ τ, idem (constA t) τ * ϖ.evO O (rescale (c τ) ((equivA O K).symm (f (τ - m)))) := by
    rw [PiSys.iTot, glue_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hf'' τ, PiSys.iA_equivA]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hRHS, PiSys.iTot, glue_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (m : ZMod a)) _ _ fun σ => ?_
  rw [map_mul, galOA_idem t hs, Equiv.coe_addRight, add_sub_cancel_right]
  change _ * galOA O k (ϖ.evO O ((equivA O K).symm (f σ))) = _
  rw [galOA_evO t ϖ z hz.symm, idem_mul_glue]

end GlobalTheory.CoverGen

theorem GlobalTheory.CoverGen.exists_covers_of_sigma_teich : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ :=
  fun _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ _ _ t ϖ _ s z hze hs hz => GlobalTheory.CoverGen.covers_of_sigma_teich t ϖ K s z hze hs hz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmullerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (k : GQ l) (s : ZMod a) (z : Fq l a), z ^ e = 1 → (∀ w : Wq l a, Per.σA k (wA l a w) = wA l a ((sigma l a ^ s.val) w)) → ϖ.kummer k = Fq.val l a z → ∃ γ : TameGal K l e a, Covers K t ϖ k γ := by
  first | exact @GlobalTheory.CoverGen.exists_covers_of_sigma_teich | exact GlobalTheory.CoverGen.exists_covers_of_sigma_teich | (intros; apply GlobalTheory.CoverGen.exists_covers_of_sigma_teich <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

theorem kummer_mem_Fq_of_mem_GKinf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  intro l _ a e _ _ ϖ he k hk
  have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  have hr : ∀ n, ϖ.ratio k n ^ e = 1 := fun n => by
    have hmem : ϖ.seq n ^ e ∈ ϖ.Kinf := IntermediateField.subset_adjoin _ _ ⟨n, rfl⟩
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow, PiSys.coe_ratio, ← map_pow, div_pow, ← map_pow, hfix _ hmem,
      div_self (pow_ne_zero _ (ϖ.seq_ne_zero n)), map_one]
    rfl
  have hK : ϖ.kummer k ^ e = 1 := Perfection.ext fun n => by
    erw [map_pow, map_one]
    change Ideal.Quotient.mk _ (ϖ.ratio k n) ^ e = 1
    rw [← map_pow, hr, map_one]
  have hmem : ϖ.kummer k ∈ resSub l a := by
    rw [mem_resSub, ← he, pow_succ, hK, one_mul]
  obtain ⟨z, hz⟩ : ∃ z : Fq l a, Fq.val l a z = ϖ.kummer k := ⟨(⟨ϖ.kummer k, hmem⟩ : ↥(resSub l a)), rfl⟩
  refine ⟨z, Fq.val_injective l a ?_, hz.symm⟩
  rw [map_pow, map_one, hz, hK]

end GlobalTheory.BKReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinfStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_root_of_unity_kummer_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ k ∈ ϖ.GKinf, ∃ z : Fq l a, z ^ e = 1 ∧ ϖ.kummer k = Fq.val l a z := by
  first | exact @GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | exact GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf | (intros; apply GlobalTheory.BKReal.kummer_mem_Fq_of_mem_GKinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverAction
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : BKGal.Gl l),
    ∃ h k : BKGal.Gl l, g = h * k ∧ BKGal.sQ l h ∈ GK (ϖ.field a) ∧
      ∃ γ : BK.TameGal K l e a, BKGal.Covers K t ϖ (BKGal.sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ :=
    GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (BKGal.sQ l g)
  let h' : BKGal.Gl l :=
    ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : BKGal.sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show BKGal.sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk
  exact GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverActionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_decomp_tameCover_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : Gl l), ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ ∃ γ : TameGal K l e a, Covers K t ϖ (sQ l k) γ := by
  first | exact @GlobalTheory.TameCoverGen.main | exact GlobalTheory.TameCoverGen.main | (intros; apply GlobalTheory.TameCoverGen.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemLocalLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemLocalLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LatPow

theorem pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  have hv : v ∈ Submodule.span K (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  suffices h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by
    obtain ⟨n₀, h⟩ := h
    exact ⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ => ?_⟩
    have : (l : K) ^ n • x = ((l : O) ^ n) • x := by
      rw [← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact T.L.T.smul_mem _ hx
  | zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun n hn => by
      rw [smul_add]
      exact T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := exists_pow_mul_mem (O := O) l c
    refine ⟨a + m, fun n hn => ?_⟩
    have e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x) := by
      rw [← algebraMap_smul K b, ← hb, smul_smul, smul_smul]
      congr 1
      rw [mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    rw [e]
    exact T.L.T.smul_mem _ (ha _ (by omega))

end GlobalTheory.LatPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemLocalLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_smul_mem_localLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  first | exact @GlobalTheory.LatPow.pow_smul_mem | exact GlobalTheory.LatPow.pow_smul_mem | (intros; apply GlobalTheory.LatPow.pow_smul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TensorOneInj

theorem bcris_nontrivial (l : ℕ) [Fact l.Prime] : Nontrivial (Per.Bcris l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have : Nontrivial (Per.BdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.nontrivial
  exact C.ι.domain_nontrivial

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] :
    Function.Injective (algebraMap ℤ_[l] (Per.Bcris l)) := by
  have := bcris_nontrivial l
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  have hu : IsUnit (algebraMap ℤ_[l] (Per.Bcris l) (PadicInt.unitCoeff h0 : ℤ_[l])) :=
    (PadicInt.unitCoeff h0).isUnit.map _
  exact (hu.mul ((GlobalTheory.MemLoc.isUnit_l_Bcris l).pow _)).ne_zero hx

theorem algebraMap_OB_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Flat ℤ_[l] O] : Function.Injective (algebraMap O (OB l O)) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := O)
    (Algebra.linearMap ℤ_[l] (Per.Bcris l)) (algebraMap_injective l)
  have e : ⇑(algebraMap O (OB l O)) =
      (LinearMap.lTensor O (Algebra.linearMap ℤ_[l] (Per.Bcris l))) ∘ (TensorProduct.rid ℤ_[l] O).symm := by
    funext o
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [e]
  exact h.comp (TensorProduct.rid ℤ_[l] O).symm.injective

theorem tensor_one_injective : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O),
    Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  intro l _ O K _ _ _ _ _ _ _ _ G _ _ T
  haveI : Module.Free O ↥T.L.T := T.L.free
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T)
    (Algebra.linearMap O (OB l O)) (algebraMap_OB_injective l O)
  have e : (fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x) =
      (LinearMap.rTensor (↥T.L.T) (Algebra.linearMap O (OB l O))) ∘ (TensorProduct.lid O ↥T.L.T).symm := by
    funext x
    simp [Algebra.TensorProduct.one_def]
  rw [e]
  exact h.comp (TensorProduct.lid O ↥T.L.T).symm.injective

end GlobalTheory.TensorOneInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjectiveStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_tmul_injective_locLat : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O), Function.Injective fun x : ↥T.L.T => (1 : OB l O) ⊗ₜ[O] x := by
  first | exact @GlobalTheory.TensorOneInj.tensor_one_injective | exact GlobalTheory.TensorOneInj.tensor_one_injective | (intros; apply GlobalTheory.TensorOneInj.tensor_one_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalPot

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (d : ι → OA l O) :
    inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem isCrisVal_add {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') :
    IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, h1, h2⟩ := h
  obtain ⟨m', c', hm', h1', h2'⟩ := h'
  refine ⟨m * m', m' • c + m • c', by rw [map_mul]; exact hm.mul hm', ?_, ?_⟩
  · rw [map_add (f := _), inclL_smul, inclL_smul, ← h1, ← h1', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (inclO l O m) (inclO l O m') w]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
    rw [e1, map_add (f := _), map_smul, map_smul, ← h2, ← h2', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (toB l O m) (toB l O m') b]

theorem isCrisVal_zero {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} : IsCrisVal t ϖ P jB 0 0 :=
  ⟨1, 0, by rw [map_one]; exact isUnit_one, by rw [smul_zero, map_zero], by
    rw [smul_zero]
    have e0 : (fun i => toB l O ((0 : ι → OA l O) i)) = 0 := funext fun i => map_zero (toB l O)
    rw [e0, map_zero]⟩

theorem isCrisVal_nsmul {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (n : ℕ) : IsCrisVal t ϖ P jB (n • w) (n • b) := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; exact isCrisVal_zero
  | succ n ih => rw [succ_nsmul, succ_nsmul]; exact isCrisVal_add ih h

variable [TameDescentExponentData K l e a] {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}

theorem isPotential_add (R : GalDat t ϖ s D T) {y y' : Vec K a ι} {b b' : TW (OB l O) T}
    (h : R.IsPotential y b) (h' : R.IsPotential y' b') : R.IsPotential (y + y') (b + b') := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨add_mem hy hy', m₀ + m₀', σ + σ', b₀ + b₀', ?_, add_mem h2 h2', ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (⟨y, hy⟩ + ⟨y', hy'⟩)
    rw [map_add (f := _), map_add (f := _), ← h1, ← h1']
    abel
  · rw [Submodule.coe_add, map_add (f := _), map_add (f := _), h3, h3']
  · rw [map_add (f := _)]
    exact isCrisVal_add h4 h4'
  · rw [h5, h5', map_add (f := _), map_add (f := _)]
    abel

theorem isPotential_nsmul (R : GalDat t ϖ s D T) {y : Vec K a ι} {b : TW (OB l O) T}
    (h : R.IsPotential y b) (n : ℕ) : R.IsPotential (n • y) (n • b) := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  refine ⟨(ME D.toPhiMod).nsmul_mem hy n, n • m₀, n • σ, n • b₀, ?_, D.desc.inv.nsmul_mem h2 n, ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (n • ⟨y, hy⟩)
    rw [map_nsmul, map_nsmul, ← h1, smul_sub]
  · show D.conn (n • σ.1) = _
    rw [map_nsmul, map_nsmul, h3]
  · rw [map_nsmul]
    exact isCrisVal_nsmul h4 n
  · rw [h5, map_nsmul, map_nsmul, nsmul_sub]

theorem isCobOf_pow {b : TW (OB l O) T} {c : G → T.V} (h : IsCobOf s T b c) (k : ℕ) :
    IsCobOf s T ((l ^ k : ℕ) • b) ((l : K) ^ k • c) := by
  intro g n x hx
  have h1 := h g (n + k) x (by rw [hx, Pi.smul_apply, smul_smul, pow_add])
  rw [h1, map_nsmul, ← nsmul_sub, ← Nat.cast_smul_eq_nsmul O, smul_smul, Nat.cast_pow, pow_add]

theorem exists_isEps : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
  exact ⟨ε, h1, (frobeniusEquiv (Per.Fl l) l).symm ε, frobeniusEquiv_symm_pow_p _ _ _, h2⟩

theorem isUnit_toB_muOf {ε : OCb l} (hε : IsEps ε) (n : ℕ) :
    IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hu : IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) :=
    ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε)) ^ n) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e1]
  exact (hu.pow n).map _

theorem actB_mul (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g g' : G) (z : TW (OB l O) T) :
    actB s T (g * g') z = actB s T g (actB s T g' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul w x =>
    have hw : galOB O (s (g * g')) w = galOB O (s g) (galOB O (s g') w) := by
      rw [map_mul]
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add u v hu hv => simp only [map_add (f := _), hu, hv]
      | tmul o c =>
        simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun z : Per.Bcris l => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ c)
    have hx : T.actT (g * g') x = T.actT g (T.actT g' x) :=
      Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g g') (x : T.V))
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hw, hx]

theorem sub_mem_B1T {s : G →* GQ l} {T : LocLat G ℚ_[l] K O} {b b' ξ : TW (OB l O) T} {c c' : G → T.V}
    (x : ↥T.L.T) (hb : IsCobOf s T b c) (hb' : IsCobOf s T b' c') (hξ : ∀ g, actB s T g ξ = ξ)
    (h : b - b' = ξ - (1 : OB l O) ⊗ₜ[O] x) : c - c' ∈ latticeCoboundaries T.L := by
  refine ⟨-(x : T.V), neg_mem x.2, funext fun g => ?_⟩
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c g)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c' g)
  obtain ⟨x₁, hx₁⟩ := hn₁ (max n₁ n₂) (le_max_left _ _)
  obtain ⟨x₂, hx₂⟩ := hn₂ (max n₁ n₂) (le_max_right _ _)
  have e1 := hb g _ x₁ hx₁
  have e2 := hb' g _ x₂ hx₂
  have hact : actB s T g ((1 : OB l O) ⊗ₜ[O] x) = (1 : OB l O) ⊗ₜ[O] (T.actT g x) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hbb : b = b' + (ξ - (1 : OB l O) ⊗ₜ[O] x) := by rw [← h]; abel
  have e3 : (1 : OB l O) ⊗ₜ[O] (x₁ - x₂) =
      (1 : OB l O) ⊗ₜ[O] (((l : O) ^ max n₁ n₂) • (x - T.actT g x)) := by
    rw [TensorProduct.tmul_sub, e1, e2, ← smul_sub, TensorProduct.tmul_smul, TensorProduct.tmul_sub, ← hact,
      hbb, map_add, map_sub, hξ]
    congr 1
    abel
  have e4 := congrArg (fun z : ↥T.L.T => (z : T.V)) (GlobalTheory.T.one_tmul_injective_locLat l O K G T e3)
  simp only [Submodule.coe_sub, Submodule.coe_smul] at e4
  have eO : ∀ v : T.V, ((l : O) ^ max n₁ n₂) • v = (l : K) ^ max n₁ n₂ • v := fun v => by
    rw [← algebraMap_smul K ((l : O) ^ max n₁ n₂) v, map_pow, map_natCast]
  rw [hx₁, hx₂, ← smul_sub, eO] at e4
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have e5 := (smul_right_inj (pow_ne_zero (max n₁ n₂) hl0)).1 e4
  simp only [LinearMap.restrictScalars_apply, Pi.sub_apply]
  rw [e5]
  change T.ρ g (-(x : T.V)) - (-(x : T.V)) = (x : T.V) - T.ρ g (x : T.V)
  rw [map_neg]
  abel

section Ql

variable [TameDescentExponentData K l e a] {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat (Gl l) ℚ_[l] K O}

theorem exists_isCrisVal (R : GalDat t ϖ (sQ l) D T) {y : Vec K a ι} (hyY : y ∈ D.Y) (hy : y ∈ ME D.toPhiMod)
    (m₀ : ι → OW l O) (h : phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩) :
    ∃ b₀, IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ := by
  obtain ⟨ε, hε⟩ := exists_isEps (l := l)
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨c, hc⟩ := (GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩
    hyY.1 m₀ h).2
  obtain ⟨u, hu⟩ := isUnit_toB_muOf (O := O) hε (H + η)
  refine ⟨(↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i)), (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)), c,
    ⟨u, hu⟩, hc.symm, ?_⟩
  rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem fix_of_horiz (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (hinv : σ.1 ∈ D.desc.inv)
    (hc : D.conn σ.1 = 0) (g : Gl l) :
    actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) := by
  obtain ⟨h, k, rfl, hh, γ, hk⟩ := GlobalTheory.T.exists_galois_decomp_tameCover_action l a e O K t ϖ g
  have hx := GlobalTheory.T.eq_xi_red_of_conn_eq_zero' O K l e a ι D.toPhiMod σ.1 hc
  have hm : D.xi (red σ.1) ∈ D.MMl := by rw [← hx]; exact σ.2
  have hσ : (⟨D.xi (red σ.1), hm⟩ : D.MMl) = σ := Subtype.ext hx.symm
  have h2 := R.horiz h hh (red σ.1) hm
  rw [hσ] at h2
  have h3 := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc k γ hk σ σ (hinv γ).symm
  rw [actB_mul, h3, h2]

end Ql

theorem potential_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hyY
    have hy : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hyY
    obtain ⟨m₀, hm₀⟩ := R.I.exists_phiW_sub (toW t ϖ D.toPhiMod ⟨y, hy⟩)
    have hYl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hyY⟩
    obtain ⟨⟨σ, hσ, hinv, hconn, -⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hYl
    obtain ⟨b₀, hb₀⟩ := exists_isCrisVal R hyY hy m₀ hm₀
    exact ⟨_, hy, m₀, ⟨σ, hσ⟩, b₀, hm₀, hinv, hconn, hb₀, rfl⟩
  · rintro y c c' ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩, hc⟩ ⟨b', ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩, hc'⟩
    have hT : m₀ - m₀' ∈ Treal t ϖ D.toPhiMod := by
      rw [mem_Treal, map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.1 (h1.trans h1'.symm)
    obtain ⟨x, hx⟩ : m₀ - m₀' ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hT
    have hphi : phiW t ϖ D.toPhiMod m₀' + R.I.ofT x = phiW t ϖ D.toPhiMod m₀ := by
      rw [hx, ← mem_Treal.1 hT, map_sub]
      abel
    have hof := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.2.2.1 x
    have hsum := isCrisVal_add h4' hof
    rw [hphi] at hsum
    have hb₀ : b₀ = b₀' + (1 : OB l O) ⊗ₜ[O] x := UnitModel.isCrisVal_unique t ϖ h4 hsum
    refine sub_mem_B1T x hc hc' (fix_of_horiz R (σ - σ') (sub_mem h2 h2') ?_) ?_
    · show D.conn (σ.1 - σ'.1) = 0
      rw [map_sub, h3, h3', sub_self]
    · rw [h5, h5', hb₀, map_sub, map_sub]
      abel
  · rintro y c k ⟨b, hb, hc⟩
    refine ⟨(l ^ k : ℕ) • b, ?_, isCobOf_pow hc k⟩
    have := isPotential_nsmul R hb (l ^ k)
    rwa [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow] at this
  · rintro y c m hm ⟨b, hb, hc⟩
    exact ⟨b + 0, isPotential_add R hb (UnitModel.isPotential_phi_sub t ϖ R hm), by rwa [add_zero]⟩

end GlobalTheory.GalPot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClassStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusPotential_cocycle_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  first | exact @GlobalTheory.GalPot.potential_class | exact GlobalTheory.GalPot.potential_class | (intros; apply GlobalTheory.GalPot.potential_class <;> assumption)
end
