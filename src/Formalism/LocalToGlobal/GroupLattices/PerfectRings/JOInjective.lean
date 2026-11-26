module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExistsSqEqIntCast
public import Formalism.LocalRingCardinality.SpanPowerMembership.LeOfEventuallyDown

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.PerfectRings.AlgebraMapFinite
noncomputable section

namespace Formalism.L2.G.Quad

open QuadraticAlgebra

variable {R : Type} [CommRing R] (π : R)

def toRes : QuadraticAlgebra R π 0 →+* R ⧸ Ideal.span {π} where
  toFun z := Ideal.Quotient.mk _ z.re
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by
    have h : Ideal.Quotient.mk (Ideal.span {π}) π = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π)
    simp [h]

theorem toRes_apply (z : QuadraticAlgebra R π 0) : toRes π z = Ideal.Quotient.mk _ z.re := rfl

theorem toRes_surjective : Function.Surjective (toRes π) := by
  intro q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨⟨r, 0⟩, rfl⟩

theorem mem_span_om (z : QuadraticAlgebra R π 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra R π 0)} ↔ π ∣ z.re := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.im, by simp⟩
  · rintro ⟨d, hd⟩
    refine ⟨⟨z.im, d⟩, ?_⟩
    ext <;> simp [hd]

theorem ker_toRes : RingHom.ker (toRes π) = Ideal.span {(ω : QuadraticAlgebra R π 0)} := by
  ext z
  rw [RingHom.mem_ker, toRes_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    mem_span_om]

def resEquiv : (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) ≃+* (R ⧸ Ideal.span {π}) :=
  (Ideal.quotEquivOfEq (ker_toRes π).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toRes_surjective π))

theorem card_res :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) :=
  Nat.card_congr (resEquiv π).toEquiv

theorem algebraMap_finite : (algebraMap R (QuadraticAlgebra R π 0)).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance

theorem algebraMap_injective : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by
  intro x y h
  simpa [Algebra.algebraMap_eq_smul_one] using congrArg QuadraticAlgebra.re h

end Formalism.L2.G.Quad
end
end

noncomputable section

namespace Formalism.L2.G

open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

abbrev QQ : Type := FractionRing (WQ p n)

abbrev OO : Type := QuadraticAlgebra (W2 p n) (p : W2 p n) 0

instance instDomOO : IsDomain (OO p n) := GatR.isDomain (WittVector.irreducible p)

instance instDvrOO : IsDiscreteValuationRing (OO p n) := GatR.isDVR (WittVector.irreducible p)

abbrev KO : Type := FractionRing (OO p n)

def wU : OO p n := ω

def jO : WQ p n →+* OO p n := (algebraMap (W2 p n) (OO p n)).comp (jW p n)

theorem jO_injective : Function.Injective (jO p n) :=
  (Quad.algebraMap_injective _).comp (jW_injective p n)

theorem inj_WK : Function.Injective ((algebraMap (OO p n) (KO p n)).comp (jO p n)) :=
  (IsFractionRing.injective (OO p n) (KO p n)).comp (jO_injective p n)

def iota : QQ p n →+* KO p n := IsFractionRing.lift (inj_WK p n)

theorem wU_sq : wU p n ^ 2 = (p : OO p n) := by
  unfold wU
  rw [GatR.om_sq, map_natCast]

theorem sq_OO [NeZero n] (hp2 : p ≠ 2) (z : ℤ) : ∃ y : OO p n, y ^ 2 = (z : OO p n) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hfin : FiniteMultiplicity (p : ℤ) z :=
    Int.finiteMultiplicity_iff.2 ⟨by simpa using hp.out.one_lt.ne', hz⟩
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨y, hy⟩ := exists_sq_eq_intCast_of_not_dvd_of_ne_two p n hp2 c hpc
  refine ⟨wU p n ^ multiplicity (p : ℤ) z * algebraMap (W2 p n) (OO p n) y, ?_⟩
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, wU_sq, ← map_pow, hy, map_intCast]
  conv_rhs => rw [hc]
  push_cast
  rfl

theorem settingStd (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    UnramifiedQuadraticSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, GatR.om_irreducible (WittVector.irreducible p), ?_, sq_OO p n (by omega)⟩
  · exact
    { prime := hp.out
      five_le := h5
      two_le := h2
      even := he
      frac_alt := inferInstance
      frac_O := inferInstance
      p_unif := WittVector.irreducible p
      res_card := card_quot_WQ p n
      eq_sum_herm_smul_frame_of_inW := inferInstance
      frob := fun x => by
        obtain ⟨y, hy⟩ := frob_WQ p n x
        exact ⟨y, by rw [sig_alg, hy]⟩
      period := sig_period p n
      ι_comp := fun x => IsFractionRing.lift_algebraMap (inj_WK p n) x
      finite := (Quad.algebraMap_finite _).comp (jW_finite p n)
      complete_O := GatR.isAdicComplete (WittVector.irreducible p) inferInstance
      w_sq := wU_sq p n }
  · exact (Quad.card_res _).trans (card_quotient_extRing p n)

theorem setting (h5 : 5 ≤ p) (h2 : 2 ≤ n) (he : Even n) :
    HidaSetting p n (WQ p n) (QQ p n) (OO p n) (KO p n) (iota p n) (sig p n) (jO p n) (wU p n) :=
  (settingStd p n h5 h2 he).1

end Formalism.L2.G
