module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

@[reducible] def actionOf {G B : Type*} [Monoid G] [CommRing B] (f : G → B →+* B)
    (h1 : ∀ x, f 1 x = x) (hmul : ∀ g h x, f (g * h) x = f g (f h x)) : MulSemiringAction G B where
  smul g x := f g x
  one_smul := h1
  mul_smul := hmul
  smul_zero g := map_zero (f g)
  smul_add g := map_add (f g)
  smul_one g := map_one (f g)
  smul_mul g := map_mul (f g)

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem toRingHom_one : MulSemiringAction.toRingHom G R 1 = RingHom.id R := by ext; simp

theorem toRingHom_mul (g h : G) : MulSemiringAction.toRingHom G R (g * h) =
    (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) := by
  ext; simp [mul_smul]

theorem toRingHom_injective (g : G) : Function.Injective (MulSemiringAction.toRingHom G R g) :=
  MulAction.injective g

variable [Fact ¬IsUnit (p : R)]

variable [IsAdicComplete (span {(p : R)}) R]

instance BdRPlus.mulSemiringAction : MulSemiringAction G (BdRPlus p R) :=
  actionOf (fun g => BdRPlus.map p (MulSemiringAction.toRingHom G R g))
    (fun x => by simpa only [toRingHom_one] using BdRPlus.map_id x)
    (fun g h x => by simpa only [toRingHom_mul] using (BdRPlus.map_map _ _ x).symm)

instance Bcris.mulSemiringAction : MulSemiringAction G (Bcris p R) :=
  actionOf (fun g => Bcris.map p (MulSemiringAction.toRingHom G R g) (toRingHom_injective g))
    (fun x => by
      rw [Bcris.map_congr _ Function.injective_id toRingHom_one, Bcris.map_id])
    (fun g h x => by
      have hi := (toRingHom_injective (R := R) g).comp (toRingHom_injective h)
      rw [Bcris.map_map _ _ _ _ hi, Bcris.map_congr _ hi (toRingHom_mul g h)])

instance BdR.mulSemiringAction : MulSemiringAction G (BdR p R) :=
  actionOf (fun g => (BdR.map p (MulSemiringAction.toRingEquiv G R g)).toRingHom)
    (fun x => by
      have : MulSemiringAction.toRingEquiv G R 1 = RingEquiv.refl R := by ext; simp
      simp [this])
    (fun g h x => by
      have : MulSemiringAction.toRingEquiv G R (g * h) =
          (MulSemiringAction.toRingEquiv G R h).trans (MulSemiringAction.toRingEquiv G R g) := by
        ext; simp [mul_smul]
      simp [this, BdR.map_map])


theorem BdR.smul_algebraMap (g : G) (x : BdRPlus p R) :
    g • algebraMap _ (BdR p R) x = algebraMap _ _ (g • x) := BdR.map_algebraMap _ x



end Reformulated.AutPerF
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

theorem eq_C_of_derivative_eq_zero (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) {f : Polynomial A}
    (hf : Polynomial.derivative f = 0) : f = Polynomial.C (f.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · have h1 := Polynomial.coeff_derivative f n
    rw [hf, Polynomial.coeff_zero] at h1
    rw [Polynomial.coeff_C_succ]
    exact (h n).mul_left_eq_zero.1 h1.symm

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring


theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]

variable (p R)


variable {p R}

end Good

namespace Bst

open Polynomial

variable [IsDomain R] [CharZero R] [ValuationRing R]

variable [IsAlgClosed (FractionRing R)]




variable (p R) in
def u : Bst p R := logFlat (pflat (p := p) (R := R))

end Bst

end Reformulated.AutPerF
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]

namespace AinfInv

theorem isUnit_factorial (n : ℕ) : IsUnit (n ! : AinfInv p R) :=
  IsUnit.natCast_factorial_of_algebra ℚ n


@[simp] theorem gamma_zero (x : AinfInv p R) : gamma 0 x = 1 := by simp [gamma]

@[simp] theorem gamma_one (x : AinfInv p R) : gamma 1 x = x := by simp [gamma]

end AinfInv

variable [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

theorem AinfInv.theta_gamma {n : ℕ} (hn : n ≠ 0) {x : AinfInv p R} (hx : AinfInv.theta p R x = 0) :
    AinfInv.theta p R (AinfInv.gamma n x) = 0 := by
  have h := congrArg (AinfInv.theta p R) (AinfInv.factorial_mul_gamma n x)
  rw [map_mul, map_pow, hx, zero_pow hn] at h
  exact (((AinfInv.isUnit_factorial n).map (AinfInv.theta p R)).mul_right_eq_zero).1 h

namespace AcrisZero


variable (p R) in
def pdIdeal : Ideal (AcrisZero p R) :=
  span {y | ∃ (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0), n ≠ 0 ∧ y = gamma n x hx}

theorem gamma_mem_pdIdeal {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    gamma n x hx ∈ pdIdeal p R := subset_span ⟨n, x, hx, hn, rfl⟩

theorem algebraMap_mem_pdIdeal (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap _ _ x ∈ pdIdeal p R := by
  have : algebraMap _ _ x = gamma 1 x hx := Subtype.ext (AinfInv.gamma_one _).symm
  rw [this]
  exact gamma_mem_pdIdeal one_ne_zero x hx

theorem exists_sub_mem_pdIdeal (y : AcrisZero p R) :
    ∃ a : Ainf p R, y - algebraMap _ _ a ∈ pdIdeal p R := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨1, ?_⟩
      convert (pdIdeal p R).zero_mem
      rw [sub_eq_zero, map_one]
      exact Subtype.ext (AinfInv.gamma_zero _)
    · exact ⟨0, by rw [map_zero, sub_zero]; exact gamma_mem_pdIdeal hn x hx⟩
  | algebraMap r =>
    refine ⟨r, ?_⟩
    convert (pdIdeal p R).zero_mem
    rw [sub_eq_zero]
    rfl
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    change (⟨x, hx'⟩ + ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_add (f := _)]; ring
  | mul x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    convert add_mem (Ideal.mul_mem_right ⟨y, hy'⟩ _ ha)
      (Ideal.mul_mem_left _ (algebraMap _ _ a) hb) using 1
    change (⟨x, hx'⟩ * ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_mul]; ring

theorem theta_eq_zero_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) :
    AinfInv.theta p R y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, hn, rfl⟩ := hy
    exact AinfInv.theta_gamma hn (by rw [AinfInv.theta_algebraMap, hx, map_zero])
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [AddMemClass.coe_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, hx, mul_zero]

theorem exists_theta_eq (y : AcrisZero p R) :
    ∃ r : R, algebraMap R (Localization.Away (p : R)) r = AinfInv.theta p R y := by
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h := theta_eq_zero_of_mem_pdIdeal ha
  rw [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero, Subalgebra.coe_algebraMap,
    AinfInv.theta_algebraMap] at h
  exact ⟨_, h.symm⟩

end AcrisZero

variable [IsDomain R] [CharZero R] [IsDomain S] [CharZero S]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective (M := Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

namespace AcrisZero


variable (p R) in
def theta : AcrisZero p R →+* R where
  toFun y := (exists_theta_eq y).choose
  map_one' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_mul' x y := algebraMap_away_injective (p := p) (by
    rw [map_mul, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)
  map_zero' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_add' x y := algebraMap_away_injective (p := p) (by
    rw [map_add (f := _), (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)

theorem algebraMap_theta (y : AcrisZero p R) :
    algebraMap R (Localization.Away (p : R)) (theta p R y) = AinfInv.theta p R y :=
  (exists_theta_eq y).choose_spec

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x :=
  algebraMap_away_injective (p := p) (by
    rw [algebraMap_theta, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap])

theorem theta_eq_zero_iff (y : AcrisZero p R) : theta p R y = 0 ↔ y ∈ pdIdeal p R := by
  have key : ∀ y ∈ pdIdeal p R, theta p R y = 0 := fun y hy =>
    algebraMap_away_injective (p := p) (by
      rw [algebraMap_theta, theta_eq_zero_of_mem_pdIdeal hy, map_zero])
  refine ⟨fun h => ?_, key y⟩
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h1 := key _ ha
  rw [RingHom.map_sub, h, theta_algebraMap, zero_sub, neg_eq_zero] at h1
  simpa using add_mem ha (algebraMap_mem_pdIdeal a h1)

end AcrisZero

namespace Acris


variable (p R) in
def theta : Acris p R →+* R :=
  (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm.toRingHom.comp
    (adicMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _))

@[simp] theorem theta_algebraMap_zero (a : AcrisZero p R) :
    theta p R (algebraMap _ _ a) = AcrisZero.theta p R a := by
  have h := adicMap_algebraMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _) a
  refine (congrArg (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm h).trans ?_
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), theta_algebraMap_zero,
    AcrisZero.theta_algebraMap]



end Acris

namespace BcrisPlus


variable (p R) in
def theta : BcrisPlus p R →+* Localization.Away (p : R) :=
  lift ((algebraMap R _).comp (Acris.theta p R))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : R)) (p : R))

@[simp] theorem theta_algebraMap (x : Acris p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Acris.theta p R x) := lift_algebraMap _ _ x

end BcrisPlus

end Reformulated.AutPerF
end
end
