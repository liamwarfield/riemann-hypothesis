module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.Assembly

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAIff
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {A B P D : Type} [CommRing A] [CommRing B] [CommRing P] [CommRing D]
  [Algebra A B] [Algebra P D]

def IsCrisDRA (ι : A →+* P) (f : B →+* D) : Prop :=
  ∀ x : A, f (algebraMap A B x) = algebraMap P D (ι x)

theorem isCrisDRA_iff (cA : A ≃+* ACris.ACris ℂ_[l] l) (cBc : B ≃+* Formalism.Per6.Bcris l) (cP : P ≃+* Formalism.Per6.BdRp l)
    (cD : D ≃+* Formalism.Per6.BdR l) (ι : A →+* P)
    (hB : ∀ x : A, cBc (algebraMap A B x) = Formalism.Per6.cB l (cA x))
    (hD : ∀ y : P, cD (algebraMap P D y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP y))
    (hι : ∀ x : A, cP (ι x) = ACris.iota ℂ_[l] l (cA x)) (f : B →+* D) :
    IsCrisDRA ι f ↔ Formalism.Per6.IsCrisDR l ((cD.toRingHom.comp f).comp cBc.symm.toRingHom) := by
  constructor
  · intro hf x6
    obtain ⟨x, rfl⟩ := cA.surjective x6
    have h1 : cBc.symm (Formalism.Per6.cB l (cA x)) = algebraMap A B x := by
      rw [← hB x, RingEquiv.symm_apply_apply]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [h1, hf x, hD, hι]
  · intro hf x
    apply cD.injective
    have h2 := hf (cA x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2
    rw [← hB x, RingEquiv.symm_apply_apply] at h2
    rw [h2, hD, hι]

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZD
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

def Compat (eB : Per.Bcris l ≃+* Per6.Bcris l) (eD : Per.BdR l ≃+* Per6.BdR l) (eP : Per.BdRp l ≃+* Per6.BdRp l) :
    Prop :=
    (∀ z : ℤ_[l], eB (Per.zB l z) = Per6.zB l z) ∧
    (∀ z : ℤ_[l], eD (Per.zD l z) = Per6.zD l z) ∧
    (∀ y : Per.BdRp l, eD (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (eP y)) ∧
    (∀ y : Per.BdRp l, Per6.θD l (eP y) = Per.θD l y) ∧
    (∀ (g : GQ l) (b : Per.Bcris l), eB (Per.σB g b) = Per6.σB g (eB b)) ∧
    (∀ (g : GQ l) (x : Per.BdR l), eD (Per.σD g x) = Per6.σD g (eD x)) ∧
    (∀ b : Per.Bcris l, eB (Per.φB l b) = Per6.φB l (eB b)) ∧
    (∀ f : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l f ↔ Per6.IsCrisDR l ((eD.toRingHom.comp f).comp eB.symm.toRingHom)) ∧
    (∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ eD x ∈ Per6.FilD l a) ∧
    (∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (eP y)) ∧
    (∀ a : Ainf l, eB (Per.aB l a) = Per6.aB l a)

def Cmp : Prop :=
  ∃ (eB : Per.Bcris l ≃+* Per6.Bcris l) (eD : Per.BdR l ≃+* Per6.BdR l) (eP : Per.BdRp l ≃+* Per6.BdRp l),
    Compat l eB eD eP

variable {l} {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}

theorem Compat.zB (h : Compat l eB eD eP) :
    ∀ z : ℤ_[l], eB (Per.zB l z) = Per6.zB l z :=
  h.1

theorem Compat.zD (h : Compat l eB eD eP) :
    ∀ z : ℤ_[l], eD (Per.zD l z) = Per6.zD l z :=
  h.2.1

theorem Compat.alg (h : Compat l eB eD eP) :
    ∀ y : Per.BdRp l, eD (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (eP y) :=
  h.2.2.1

theorem Compat.θ (h : Compat l eB eD eP) :
    ∀ y : Per.BdRp l, Per6.θD l (eP y) = Per.θD l y :=
  h.2.2.2.1

theorem Compat.σB (h : Compat l eB eD eP) :
    ∀ (g : GQ l) (b : Per.Bcris l), eB (Per.σB g b) = Per6.σB g (eB b) :=
  h.2.2.2.2.1

theorem Compat.σD (h : Compat l eB eD eP) :
    ∀ (g : GQ l) (x : Per.BdR l), eD (Per.σD g x) = Per6.σD g (eD x) :=
  h.2.2.2.2.2.1

theorem Compat.φB (h : Compat l eB eD eP) :
    ∀ b : Per.Bcris l, eB (Per.φB l b) = Per6.φB l (eB b) :=
  h.2.2.2.2.2.2.1

theorem Compat.incl (h : Compat l eB eD eP) :
    ∀ f : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l f ↔ Per6.IsCrisDR l ((eD.toRingHom.comp f).comp eB.symm.toRingHom) :=
  h.2.2.2.2.2.2.2.1

theorem Compat.fil (h : Compat l eB eD eP) :
    ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ eD x ∈ Per6.FilD l a :=
  h.2.2.2.2.2.2.2.2.1

theorem Compat.log (h : Compat l eB eD eP) :
    ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (eP y) :=
  h.2.2.2.2.2.2.2.2.2.1

theorem Compat.aB (h : Compat l eB eD eP) :
    ∀ a : Ainf l, eB (Per.aB l a) = Per6.aB l a :=
  h.2.2.2.2.2.2.2.2.2.2

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFDefs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IotaBounded
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

abbrev NC : Type := ↥(normInteger ℂ_[l])

def iotaF : ACris.ACris ℂ_[l] l →+* Reformulated.AutPerF.BdRPlus l (NC l) := ACris.iota ℂ_[l] l

theorem iota_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : ACris.ACris ℂ_[l] l, ∃ a : Reformulated.AutPerF.Ainf l (NC l),
    Reformulated.AutPerF.BdRPlus.eval l (NC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N * iotaF l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) a) := by
  refine ⟨(n - 1).factorial.factorization l, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ACris.pow_mul_mem_latticeQ n _ (ACris.embedding₂ ℂ_[l] l n x).2
  refine ⟨w, ?_⟩
  have h1 : Reformulated.AutPerF.BdRPlus.eval l (NC l) n (iotaF l x) =
      ((ACris.embedding₂ ℂ_[l] l n x : ACris.acrisQ ℂ_[l] l n) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l) ⧸ ACris.kerAway ℂ_[l] l ^ n) := by
    have := ACris.evalₐ_iota (K := ℂ_[l]) (p := l) n x
    rw [ACris.iotaQ.eq_1] at this
    exact this
  rw [map_mul, map_pow, map_natCast, h1]
  exact hw.symm

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.EqToBdRPlusOfBounded
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem eq_toBdRPlus_of_bounded (j : Acris p R →+* BdRPlus p R)
    (h0 : ∀ a : AcrisZero p R, j (algebraMap (AcrisZero p R) (Acris p R) a) =
      algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
    (hb : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ a : Ainf p R,
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j x) = Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)) :
    j = Acris.toBdRPlus p R := by
  ext x
  apply BdRPlus.ext_eval
  intro n
  obtain ⟨N, hN⟩ := hb n
  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n (j x) - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨az, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : j x = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * j z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, h0 a0]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n (j z) - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n (j z))
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]
  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0' : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0'
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def iotaP : ACris.ACris ℂ_[l] l →+* Formalism.Per6.BdRp l := ACris.iota ℂ_[l] l

def jOC : Reformulated.AutPerF.Acris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) :=
  ((Cmp6.cP l).symm.toRingHom.comp (iotaP l)).comp (Cmp6.cA l).toRingHom

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAToBdRPlusIff
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (Ideal.span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem isCrisDRA_toBdRPlus_iff (f : Bcris p R →+* BdR p R) :
    IsCrisDRA (Acris.toBdRPlus p R) f ↔ f = Bcris.toBdR p R := by
  constructor
  · intro hf
    refine Bcris.hom_ext fun x => ?_
    have h := BcrisPlus.hom_ext (f := f.comp (algebraMap (BcrisPlus p R) (Bcris p R)))
      (g := (Bcris.toBdR p R).comp (algebraMap (BcrisPlus p R) (Bcris p R))) (fun y => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply, hf y, Bcris.toBdR_algebraMap_acris])
    exact RingHom.congr_fun h x
  · rintro rfl x
    exact Bcris.toBdR_algebraMap_acris x

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.InclDone
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafMain
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCZero
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZeroEquiv
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt1 (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    ((Cmp6.zeroEquiv l y : ACris.ACrisZero ℂ_[l] l) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l)) =
      ((y : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) := by
  simp only [Cmp6.zeroEquiv, AlgEquiv.coe_ringEquiv, Subalgebra.equivOfEq_apply]
end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt2
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt2 (z : Reformulated.AutPerF.AinfInv l (NC l)) :
    toBDeRhamPlus (↥(normInteger ℂ_[l])) l z = algebraMap (Reformulated.AutPerF.AinfInv l (NC l)) (Reformulated.AutPerF.BdRPlus l (NC l)) z := rfl
end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt3
noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]
set_option maxHeartbeats 200000 in
theorem zt3 (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    ((Reformulated.AutPerF.AcrisZero.map (p := l) (Cmp6.e l).toRingHom a : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) =
      Reformulated.AutPerF.AinfInv.map l (Cmp6.e l).toRingHom (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) :=
  Reformulated.AutPerF.AcrisZero.coe_map _ _
end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 200000 in
theorem jOC_zero (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    jOC l (algebraMap _ (Reformulated.AutPerF.Acris l (Cmp6.OC l)) a) =
      algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) _ (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) := by
  show (Cmp6.cP l).symm (iotaP l (Cmp6.cA l (algebraMap _ _ a))) = _
  rw [RingEquiv.symm_apply_eq, Cmp6.cA_apply, Reformulated.AutPerF.Acris.map_algebraMap_zero, Cmp6.acrisNHom_algebraMap]
  erw [ACris.iota_of]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  erw [zt1, zt2, zt3]

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCBounded
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem jOC_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l), ∃ a : Reformulated.AutPerF.Ainf l (Cmp6.OC l),
    Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * jOC l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) a) := by
  obtain ⟨N, hN⟩ := iota_bounded l n
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN (Cmp6.cA l x)
  refine ⟨Reformulated.AutPerF.Ainf.map l (Cmp6.e l).symm.toRingHom a, ?_⟩
  have hsymm : ∀ z : Formalism.Per6.BdRp l,
      (Cmp6.cP l).symm z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z)
    erw [Reformulated.AutPerF.BdRPlus.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Reformulated.AutPerF.BdRPlus.map_id]
  show Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n
      (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * (Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  erw [hsymm]
  rw [← map_natCast (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom) l, ← map_pow]
  have hm := map_mul (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom)
    (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N) (iotaF l (Cmp6.cA l x))
  erw [← hm, Reformulated.AutPerF.BdRPlus.eval_map]
  erw [ha]
  rw [Ideal.quotientMap_mk, Reformulated.AutPerF.AinfInv.map_algebraMap]

end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem comparison_toBdRPlus (x : Reformulated.AutPerF.Acris l (Cmp6.OC l)) :
    Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x) := by
  have h := eq_toBdRPlus_of_bounded (jOC l) (jOC_zero l) (jOC_bounded l)
  rw [← h]
  show Cmp6.cP l ((Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end Formalism.BasicNotions.CmpTie.Incl
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.InclAsm
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Bridge
noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

structure IsCrisDRF (f : Bcris p R →+* BdR p R) : Prop where
  on0 : ∀ a : AcrisZero p R, f (algebraMap (Acris p R) (Bcris p R) (algebraMap (AcrisZero p R) (Acris p R) a)) =
    algebraMap (BdRPlus p R) (BdR p R) (algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ (y : BdRPlus p R) (a : Ainf p R),
    f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y ∧
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * y) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)

theorem isCrisDRF_toBdR : IsCrisDRF (Bcris.toBdR p R) := by
  refine ⟨fun a => ?_, fun n => ⟨n, fun x => ?_⟩⟩
  · rw [Bcris.toBdR_algebraMap_acris, Acris.toBdRPlus_algebraMap_zero]
  · obtain ⟨b, hb⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n x)
    refine ⟨Acris.toBdRPlus p R x, b, Bcris.toBdR_algebraMap_acris x, ?_⟩
    have h1 := congrArg Subtype.val hb
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at h1
    rw [map_mul, map_pow, map_natCast, Acris.eval_toBdRPlus, h1]
    rfl

theorem eval_eq_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) (x : Acris p R) (y : BdRPlus p R)
    (hy : f (algebraMap (Acris p R) (Bcris p R) x) = algebraMap (BdRPlus p R) (BdR p R) y) (n : ℕ) :
    BdRPlus.eval p R n y = BdRPlus.eval p R n (Acris.toBdRPlus p R x) := by
  have hinj : Function.Injective (algebraMap (BdRPlus p R) (BdR p R)) := IsFractionRing.injective _ _
  obtain ⟨N, hN⟩ := hf.bdd n

  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n y - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨yz, az, hyz, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : y = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * yz := by
      apply hinj
      rw [← hy, hz]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      rw [hf.on0 a0, hyz]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * yz) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n yz - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n yz)
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]

  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0 : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

theorem eq_toBdR_of_isCrisDRF {f : Bcris p R →+* BdR p R} (hf : IsCrisDRF f) : f = Bcris.toBdR p R := by
  rw [← isCrisDRA_toBdRPlus_iff]
  intro x
  obtain ⟨N0, hN0⟩ := hf.bdd 0
  obtain ⟨y, -, hy, -⟩ := hN0 x
  rw [hy]
  congr 1
  exact BdRPlus.ext_eval fun n => eval_eq_of_isCrisDRF hf x y hy n

theorem isCrisDRF_iff (f : Bcris p R →+* BdR p R) : IsCrisDRF f ↔ f = Bcris.toBdR p R :=
  ⟨eq_toBdR_of_isCrisDRF, fun h => h ▸ isCrisDRF_toBdR⟩

end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem incl_native
    (hι : ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l),
      Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x))
    (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) := by
  rw [isCrisDRF_iff, ← isCrisDRA_toBdRPlus_iff]
  exact isCrisDRA_iff (Cmp6.cA l) (Cmp6.cBc l) (Cmp6.cP l) (Cmp6.cD l) (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l))
    (fun x => Cmp6.cBc_algebraMap l x) (fun y => Cmp6.cD_algebraMap l y) hι f

end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

variable (l : ℕ) [Fact l.Prime]

theorem incl_F (f : Reformulated.AutPerF.Bcris l (Cmp6.OC l) →+* Reformulated.AutPerF.BdR l (Cmp6.OC l)) :
    IsCrisDRF f ↔ Formalism.Per6.IsCrisDR l (((Cmp6.cD l).toRingHom.comp f).comp (Cmp6.cBc l).symm.toRingHom) :=
  incl_native l (comparison_toBdRPlus l) f

end Formalism.BasicNotions.CmpTie.Incl
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

def castCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Reformulated.AutPerF.Bcris l (Cmp6.OC l) := RingEquiv.refl _
def castDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Reformulated.AutPerF.BdR l (Cmp6.OC l) := RingEquiv.refl _
def castDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Reformulated.AutPerF.BdRPlus l (Cmp6.OC l) := RingEquiv.refl _

abbrev equivCrystalline (l : ℕ) [Fact l.Prime] : Per.Bcris l ≃+* Per6.Bcris l := (castCrystalline l).trans (Cmp6.cBc l)
abbrev equivDeRham (l : ℕ) [Fact l.Prime] : Per.BdR l ≃+* Per6.BdR l := (castDeRham l).trans (Cmp6.cD l)
abbrev equivDeRhamPlus (l : ℕ) [Fact l.Prime] : Per.BdRp l ≃+* Per6.BdRp l := (castDeRhamPlus l).trans (Cmp6.cP l)

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LogarithmCompat
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.MemKerPowIff
noncomputable section

namespace Formalism.BasicNotions.CmpTie.LogF

open Reformulated.AutPerF

variable (l : ℕ) [Fact l.Prime]

abbrev B : Type := BdRPlus l (Cmp6.OC l)

theorem mem_ker_pow_iff (x : B l) (n : ℕ) :
    x ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n ↔ BdRPlus.eval l (Cmp6.OC l) n x = 0 := by
  rw [BdRPlus.ker_thetaC, ← RingHom.mem_ker, BdRPlus.ker_eval]
  rfl

theorem truncLog_eq (N : ℕ) (x : AinfInv l (Cmp6.OC l) ⧸ AinfInv.kerTheta l (Cmp6.OC l) ^ N) :
    truncLog N x = ∑ i ∈ Finset.Ico 1 (N + 1), algebraMap ℚ _ ((-1) ^ (i + 1) / i) * x ^ i := by
  unfold truncLog
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  congr 2
  · push_cast
    ring
  · ring

abbrev u (ε : PreTilt ↥(PadicComplexInt l) l) : B l :=
  algebraMap (Ainf l (Cmp6.OC l)) (B l) (WittVector.teichmuller l ε)

abbrev sA (ε : PreTilt ↥(PadicComplexInt l) l) (n : ℕ) : B l :=
  ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (B l) ((-1) ^ (i + 1) / i) * (u l ε - 1) ^ i

theorem log_sub_mem (ε : PreTilt ↥(PadicComplexInt l) l) (h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1) (n : ℕ) :
    BdRPlus.log (u l ε) h - sA l ε n ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) ^ n := by
  have hk : u l ε - 1 ∈ RingHom.ker (BdRPlus.thetaC l (PadicComplexInt l)) := by
    rw [BdRPlus.ker_thetaC, RingHom.mem_ker, map_sub, h, map_one, sub_self]
  have hX : BdRPlus.eval l (Cmp6.OC l) n ((u l ε - 1) ^ n) = 0 :=
    (mem_ker_pow_iff l _ n).1 (Ideal.pow_mem_pow hk n)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mem_ker_pow_iff, map_sub, BdRPlus.eval_log, truncLog_eq, map_sum]
  simp only [map_mul, map_pow, RingHom.map_rat_algebraMap]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_Ico_succ_top hn, add_sub_cancel_left, ← map_pow, hX, mul_zero]

theorem isLog_iff (ε : PreTilt ↥(PadicComplexInt l) l) (y : B l) :
    (∃ h : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1, y = BdRPlus.log (u l ε) h) ↔ Cmp6.IsLogA l ε y := by
  constructor
  · rintro ⟨h, rfl⟩ n
    exact log_sub_mem l ε h n
  · intro hy
    have h1 := hy 1
    have h2 := hy 2
    have hu : BdRPlus.theta l (Cmp6.OC l) (u l ε) = 1 := by
      have h3 := sub_mem (by simpa using h1) (Ideal.pow_le_self two_ne_zero h2)
      have h4 : u l ε - 1 ∈ RingHom.ker (BdRPlus.theta l (Cmp6.OC l)) := by
        rw [← BdRPlus.ker_thetaC]
        simpa using h3
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h4
      exact h4
    refine ⟨hu, ?_⟩
    apply BdRPlus.ext_eval
    intro n
    have h5 := sub_mem (hy n) (log_sub_mem l ε hu n)
    rw [sub_sub_sub_cancel_right, mem_ker_pow_iff, map_sub, sub_eq_zero] at h5
    exact h5

end Formalism.BasicNotions.CmpTie.LogF
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem logarithm_compat : ∀ {P : LocPrime l} (AI : LocAinf l P) (y : Per.BdRp l), Per.IsLog l AI.ε y ↔ Per6.IsLog l AI.ε (equivDeRhamPlus l y) := by
  intro P AI y
  exact (LogF.isLog_iff l AI.ε y).trans (Cmp6.isLogA_iff_cP l AI.ε y)

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFPlain
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 200000 in
theorem zB_eq (z : ℤ_[l]) : Per.zB l z = algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (Cmp6.OC l)) (z : ℚ_[l]) := by
  show algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
        (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)) = _
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt]
  rfl

set_option maxHeartbeats 200000 in
theorem zD_eq (z : ℤ_[l]) : Per.zD l z = algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (Cmp6.OC l)) (z : ℚ_[l]) := by
  rw [← Reformulated.AutPerF.Bcris.toBdR_algebraMap_padic, ← zB_eq]
  show algebraMap (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) (Reformulated.AutPerF.BdR l (Cmp6.OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) (Reformulated.AutPerF.BdRPlus l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z))) =
    Reformulated.AutPerF.Bcris.toBdR l (Cmp6.OC l)
      (algebraMap (Reformulated.AutPerF.Acris l (Cmp6.OC l)) (Reformulated.AutPerF.Bcris l (Cmp6.OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.Acris l (Cmp6.OC l))
          (Reformulated.AutPerF.Ainf.ofPadicInt l (Cmp6.OC l) z)))
  rw [Reformulated.AutPerF.Bcris.toBdR_algebraMap_acris, Reformulated.AutPerF.Acris.toBdRPlus_algebraMap]
  rfl

set_option maxRecDepth 20000 in
theorem integer_to_crystalline_compat : ∀ z : ℤ_[l], equivCrystalline l (Per.zB l z) = Per6.zB l z := by
  intro z
  show Cmp6.cBc l (Per.zB l z) = _
  rw [zB_eq]
  exact (Cmp6.compat_native l).1 z
set_option maxRecDepth 20000 in
theorem integer_to_deRham_compat : ∀ z : ℤ_[l], equivDeRham l (Per.zD l z) = Per6.zD l z := by
  intro z
  show Cmp6.cD l (Per.zD l z) = _
  rw [zD_eq]
  exact (Cmp6.compat_native l).2.1 z
set_option maxRecDepth 20000 in
theorem deRham_plus_algebraMap_compat : ∀ y : Per.BdRp l, equivDeRham l (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per6.BdRp l) (Per6.BdR l) (equivDeRhamPlus l y) := by
  intro y
  exact (Cmp6.compat_native l).2.2.1 y
set_option maxRecDepth 20000 in
theorem theta_deRham_compat : ∀ y : Per.BdRp l, Per6.θD l (equivDeRhamPlus l y) = Per.θD l y := by
  intro y
  exact (Cmp6.compat_native l).2.2.2.1 y
set_option maxRecDepth 20000 in
theorem galois_action_crystalline_compat : ∀ (g : GQ l) (b : Per.Bcris l), equivCrystalline l (Per.σB g b) = Per6.σB g (equivCrystalline l b) := by
  intro g b
  exact (Cmp6.compat_native l).2.2.2.2.1 g b
set_option maxRecDepth 20000 in
theorem galois_action_deRham_compat : ∀ (g : GQ l) (x : Per.BdR l), equivDeRham l (Per.σD g x) = Per6.σD g (equivDeRham l x) := by
  intro g x
  exact (Cmp6.compat_native l).2.2.2.2.2.1 g x
set_option maxRecDepth 20000 in
theorem frobenius_crystalline_compat : ∀ b : Per.Bcris l, equivCrystalline l (Per.φB l b) = Per6.φB l (equivCrystalline l b) := by
  intro b
  exact (Cmp6.compat_native l).2.2.2.2.2.2.1 b
set_option maxRecDepth 20000 in
theorem filtration_deRham_compat : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔ equivDeRham l x ∈ Per6.FilD l a := by
  intro a x
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.1 a x
set_option maxRecDepth 20000 in
theorem ainf_to_crystalline_compat : ∀ a : Ainf l, equivCrystalline l (Per.aB l a) = Per6.aB l a := by
  intro a
  exact (Cmp6.compat_native l).2.2.2.2.2.2.2.2.2 a

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.CFIncl
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable (l : ℕ) [Fact l.Prime]

set_option maxRecDepth 20000 in
theorem crystalline_deRham_inclusion_compat : ∀ f : Per.Bcris l →+* Per.BdR l,
    Per.IsCrisDR l f ↔ Per6.IsCrisDR l (((equivDeRham l).toRingHom.comp f).comp (equivCrystalline l).symm.toRingHom) := by
  intro f
  have e : Per.IsCrisDR l f ↔ Incl.IsCrisDRF (p := l) (R := Cmp6.OC l) f :=
    ⟨fun h => ⟨h.on0, h.bdd⟩, fun h => ⟨h.on0, h.bdd⟩⟩
  rw [e]
  exact Incl.incl_F l f

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocTied6OfCmp
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def toCompanionTheory {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) : LocTied6 l P AI := by
  refine
    { eB := T.eB.trans eB
      eD := T.eD.trans eD
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, h.zB z]
  · rw [RingEquiv.trans_apply, T.zD z, h.zD z]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    exact ⟨eP y, by rw [RingEquiv.trans_apply, hy, h.alg y], by rw [h.θ y]; exact hθ⟩
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, h.σB]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, h.σD]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, h.φB]
  · have H := (h.incl _).1 T.incl
    convert H using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a]
  · obtain ⟨y, hy, he⟩ := T.t
    exact ⟨eP y, (h.log AI y).1 hy, by rw [RingEquiv.trans_apply, he, h.alg y]⟩
  · rw [RingEquiv.trans_apply, T.ιA a, h.aB a]

theorem locTied6_of_cmp (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied l P AI) → Nonempty (LocTied6 l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨toCompanionTheory h T⟩

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonOfComparison
noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def ofSix {eB : Per.Bcris l ≃+* Per6.Bcris l} {eD : Per.BdR l ≃+* Per6.BdR l} {eP : Per.BdRp l ≃+* Per6.BdRp l}
    (h : Compat l eB eD eP) {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI) : LocTied l P AI := by
  refine
    { eB := T.eB.trans eB.symm
      eD := T.eD.trans eD.symm
      zB := fun z => ?_
      zD := fun z => ?_
      om := fun x => ?_
      actB := fun g b => ?_
      actD := fun g b => ?_
      frob := fun b => ?_
      incl := ?_
      fil := fun K a x => ?_
      t := ?_
      ιA := fun a => ?_ }
  · rw [RingEquiv.trans_apply, T.zB z, ← h.zB z, RingEquiv.symm_apply_apply]
  · rw [RingEquiv.trans_apply, T.zD z, ← h.zD z, RingEquiv.symm_apply_apply]
  · obtain ⟨y, hy, hθ⟩ := T.om x
    refine ⟨eP.symm y, ?_, ?_⟩
    · rw [RingEquiv.trans_apply, hy, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
    · rw [← h.θ, RingEquiv.apply_symm_apply]; exact hθ
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actB g b, RingEquiv.symm_apply_eq, h.σB,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.actD g b, RingEquiv.symm_apply_eq, h.σD,
      RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, RingEquiv.trans_apply, T.frob b, RingEquiv.symm_apply_eq, h.φB,
      RingEquiv.apply_symm_apply]
  · refine (h.incl _).2 ?_
    convert T.incl using 1
    ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.trans_apply, RingEquiv.symm_trans_apply, RingEquiv.apply_symm_apply,
      RingEquiv.symm_symm]
  · rw [T.fil K a x, RingEquiv.trans_apply, h.fil a, RingEquiv.apply_symm_apply]
  · obtain ⟨y, hy, he⟩ := T.t
    refine ⟨eP.symm y, (h.log AI (eP.symm y)).2 (by rw [RingEquiv.apply_symm_apply]; exact hy), ?_⟩
    rw [RingEquiv.trans_apply, he, RingEquiv.symm_apply_eq, h.alg, RingEquiv.apply_symm_apply]
  · rw [RingEquiv.trans_apply, T.ιA a, ← h.aB a, RingEquiv.symm_apply_apply]

theorem local_comparison_of_comparison (hC : Cmp l) (P : LocPrime l) (AI : LocAinf l P) :
    Nonempty (LocTied6 l P AI) → Nonempty (LocTied l P AI) := by
  rintro ⟨T⟩
  obtain ⟨eB, eD, eP, h⟩ := hC
  exact ⟨ofSix h T⟩

end Formalism.BasicNotions.CmpTie
end
end

noncomputable section

namespace Formalism.BasicNotions.CmpTie

open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem compat_F (l : ℕ) [Fact l.Prime] : Compat l (equivCrystalline l) (equivDeRham l) (equivDeRhamPlus l) :=
  ⟨integer_to_crystalline_compat l, integer_to_deRham_compat l, deRham_plus_algebraMap_compat l, theta_deRham_compat l, galois_action_crystalline_compat l, galois_action_deRham_compat l, frobenius_crystalline_compat l, crystalline_deRham_inclusion_compat l, filtration_deRham_compat l, fun AI y => logarithm_compat l AI y,
    ainf_to_crystalline_compat l⟩

theorem cmp_F (l : ℕ) [Fact l.Prime] : Cmp l := ⟨_, _, _, compat_F l⟩

theorem locTied6_F : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  fun l _ P AI => locTied6_of_cmp (cmp_F l) P AI

theorem local_comparison_from_alternative : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  fun l _ P AI => local_comparison_of_comparison (cmp_F l) P AI

end Formalism.BasicNotions.CmpTie
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTied6
theorem UpperTheory.Lit.Cmp.locTied6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied l P AI) → Nonempty (Formalism.BasicNotions.LocTied6 l P AI) :=
  Formalism.BasicNotions.CmpTie.locTied6_F
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.LocalComparison.LocTiedOf6
theorem UpperTheory.Lit.Cmp.locTied_of6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  Formalism.BasicNotions.CmpTie.local_comparison_from_alternative
end
