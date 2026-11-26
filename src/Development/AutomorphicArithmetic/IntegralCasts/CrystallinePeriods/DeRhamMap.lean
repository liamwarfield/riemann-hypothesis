module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

theorem AinfInv.kerTheta_le_comap (f : R →+* S) :
    AinfInv.kerTheta p R ≤ (AinfInv.kerTheta p S).comap (AinfInv.map p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, AinfInv.theta_map, RingHom.mem_ker.1 hx, map_zero]


namespace BdRPlus

def map (f : R →+* S) : BdRPlus p R →+* BdRPlus p S :=
  adicMap _ _ (AinfInv.map p f) (AinfInv.kerTheta_le_comap p f)

variable {p}

theorem eval_map (f : R →+* S) (n : ℕ) (x : BdRPlus p R) :
    eval p S n (map p f x) = Ideal.quotientMap _ (AinfInv.map p f)
      (pow_le_comap_pow (AinfInv.kerTheta_le_comap p f) n) (eval p R n x) :=
  evalₐ_adicMap _ _ _ _ n x

@[simp] theorem map_algebraMap (f : R →+* S) (x : AinfInv p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AinfInv.map p f x) :=
  adicMap_algebraMap _ _ _ _ x

@[simp] theorem map_algebraMap_ainf (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_id (x : BdRPlus p R) : map p (RingHom.id R) x = x :=
  adicMap_eq_id _ _ _ AinfInv.map_id x

theorem map_map (f : R →+* S) (g : S →+* U) (x : BdRPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  adicMap_adicMap _ _ _ _ _ _ _ _ _ (AinfInv.map_map f g) x

theorem theta_eq_of_eval_one {x : BdRPlus p R} {a : AinfInv p R}
    (h : eval p R 1 x = Ideal.Quotient.mk _ a) : theta p R x = AinfInv.theta p R a := by
  have h1 := AdicCompletion.factorₐ_evalₐ_one (AinfInv.kerTheta p R) x
  change Ideal.Quotient.factor _ (eval p R 1 x) = _ at h1
  rw [h] at h1
  change RingHom.kerLift _ (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x) = _
  rw [← h1]
  rfl

theorem theta_map (f : R →+* S) (x : BdRPlus p R) :
    theta p S (map p f x) = awayMap p f (theta p R x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R 1 x)
  rw [theta_eq_of_eval_one ha.symm, ← AinfInv.theta_map]
  apply theta_eq_of_eval_one
  rw [eval_map, ← ha, Ideal.quotientMap_mk]


variable (p) in
def mapEquiv (e : R ≃+* S) : BdRPlus p R ≃+* BdRPlus p S :=
  RingEquiv.ofRingHom (map p e.toRingHom) (map p e.symm.toRingHom)
    (by ext x; simp [map_map]) (by ext x; simp [map_map])

end BdRPlus

namespace BdR

def map (e : R ≃+* S) : BdR p R ≃+* BdR p S :=
  IsFractionRing.ringEquivOfRingEquiv (BdRPlus.mapEquiv p e)

variable {p}

theorem hom_ext {B : Type*} [CommRing B] {f g : BdR p R →+* B}
    (h : ∀ x : BdRPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (BdRPlus p R)) (RingHom.ext h)

@[simp] theorem map_algebraMap (e : R ≃+* S) (x : BdRPlus p R) :
    map p e (algebraMap _ _ x) = algebraMap _ _ (BdRPlus.map p (e : R →+* S) x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

@[simp] theorem map_refl (x : BdR p R) : map p (RingEquiv.refl R) x = x :=
  RingHom.congr_fun (hom_ext (f := (map p (RingEquiv.refl R) : _ →+* _)) (g := RingHom.id _)
    (by simp)) x

theorem map_map (e : R ≃+* S) (e' : S ≃+* U) (x : BdR p R) :
    map p e' (map p e x) = map p (e.trans e') x :=
  RingHom.congr_fun (hom_ext (f := (map p e').toRingHom.comp (map p e).toRingHom)
    (g := (map p (e.trans e')).toRingHom) (by simp [BdRPlus.map_map])) x

end BdR

end Reformulated.AutPerF
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace Tilt

variable (p R) in
def seqEquiv : Perfection R p ≃* Tilt p R := Perfection.quotientMulEquiv p (span {(p : R)})

def seq (n : ℕ) : Tilt p R →* R :=
  (Perfection.coeffMonoidHom R p n).comp (seqEquiv p R).symm.toMonoidHom

def ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) : Tilt p R := seqEquiv p R ⟨x, h⟩

@[simp] theorem seq_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) (n : ℕ) :
    seq n (ofSeq x h : Tilt p R) = x n := by
  exact congrArg (Perfection.coeffMonoidHom R p n) ((seqEquiv p R).symm_apply_apply ⟨x, h⟩)

theorem seq_zero (y : Tilt p R) : seq 0 y = PreTilt.untilt y :=
  Perfection.coeff_zero_symm_quotientMulEquiv y

@[simp] theorem untilt_ofSeq (x : ℕ → R) (h : ∀ n, x (n + 1) ^ p = x n) :
    PreTilt.untilt (ofSeq x h : Tilt p R) = x 0 := by
  rw [← seq_zero, seq_ofSeq]

theorem seq_succ_pow (y : Tilt p R) (n : ℕ) : seq (n + 1) y ^ p = seq n y :=
  Perfection.coeffMonoidHom_pow_p' ((seqEquiv p R).symm y) n

theorem seq_add_pow (y : Tilt p R) (m n : ℕ) : seq (m + n) y ^ p ^ n = seq m y :=
  Perfection.coeffMonoidHom_pow_p_pow' ((seqEquiv p R).symm y) m n

theorem seq_pow_self (y : Tilt p R) (n : ℕ) : seq n y ^ p ^ n = PreTilt.untilt y := by
  rw [← seq_zero, ← seq_add_pow y 0 n, zero_add]

theorem ext_seq {x y : Tilt p R} (h : ∀ n, seq n x = seq n y) : x = y :=
  (seqEquiv p R).symm.injective (Perfection.extMonoid h)

theorem seq_frobeniusEquiv_symm (y : Tilt p R) (n : ℕ) :
    seq n ((frobeniusEquiv (Tilt p R) p).symm y) = seq (n + 1) y := by
  conv_rhs => rw [← frobeniusEquiv_symm_pow_p (Tilt p R) p y, map_pow, seq_succ_pow]

end Tilt

namespace tateModule

open Tilt

theorem untilt_eq_one (η : tateModule p R) : PreTilt.untilt η.1 = 1 := η.2

theorem seq_pow_eq_one (η : tateModule p R) (n : ℕ) : seq n η.1 ^ p ^ n = 1 := by
  rw [seq_pow_self, untilt_eq_one]

theorem ext_seq {x y : tateModule p R} (h : ∀ n, seq n x.1 = seq n y.1) : x = y :=
  Subtype.ext (Tilt.ext_seq h)

theorem seq_pow_congr (η : tateModule p R) {n a b : ℕ} (h : (a : ZMod (p ^ n)) = b) :
    seq n η.1 ^ a = seq n η.1 ^ b :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff _ _ _).1 h) (seq_pow_eq_one η n)

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem cast_val_toZModPow (a : ℤ_[p]) (n : ℕ) :
    (((PadicInt.toZModPow n a).val : ℕ) : ZMod (p ^ n)) = PadicInt.toZModPow n a :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  ZMod.natCast_zmod_val _

def padicPow (η : tateModule p R) (a : ℤ_[p]) : tateModule p R :=
  ⟨ofSeq (fun n => seq n η.1 ^ (PadicInt.toZModPow n a).val) (fun n => by
    rw [← pow_mul, mul_comm, pow_mul, seq_succ_pow]
    apply seq_pow_congr
    haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    rw [cast_val_toZModPow, ZMod.natCast_val, PadicInt.cast_toZModPow _ _ n.le_succ]), by
    change PreTilt.untilt _ = 1
    rw [untilt_ofSeq, seq_zero, untilt_eq_one, one_pow]⟩

theorem seq_padicPow (η : tateModule p R) (a : ℤ_[p]) (n : ℕ) :
    seq n (padicPow η a).1 = seq n η.1 ^ (PadicInt.toZModPow n a).val := seq_ofSeq _ _ n

theorem seq_padicPow_of_eq (η : tateModule p R) {a : ℤ_[p]} {n m : ℕ}
    (h : PadicInt.toZModPow n a = m) : seq n (padicPow η a).1 = seq n η.1 ^ m := by
  rw [seq_padicPow]
  exact seq_pow_congr η (by rw [cast_val_toZModPow, h])

@[simp] theorem padicPow_natCast (η : tateModule p R) (m : ℕ) : padicPow η m = η ^ m :=
  ext_seq fun n => by
    rw [seq_padicPow_of_eq η (map_natCast _ m), SubmonoidClass.coe_pow, map_pow]

@[simp] theorem padicPow_zero (η : tateModule p R) : padicPow η 0 = 1 := by
  simpa using padicPow_natCast η 0

theorem padicPow_add (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a + b) = padicPow η a * padicPow η b :=
  ext_seq fun n => by
    rw [Submonoid.coe_mul, map_mul, seq_padicPow η a, seq_padicPow η b, ← pow_add]
    apply seq_padicPow_of_eq
    rw [Nat.cast_add, cast_val_toZModPow, cast_val_toZModPow, map_add (f := _)]

theorem padicPow_mul (η : tateModule p R) (a b : ℤ_[p]) :
    padicPow η (a * b) = padicPow (padicPow η a) b :=
  ext_seq fun n => by
    rw [seq_padicPow _ b, seq_padicPow η a, ← pow_mul]
    apply seq_padicPow_of_eq
    rw [Nat.cast_mul, cast_val_toZModPow, cast_val_toZModPow, map_mul]

theorem exists_padicPow_eq (η : tateModule p R) {a : ℤ_[p]} {m k : ℕ}
    (h : (p : ℤ_[p]) ^ k ∣ a - m) : ∃ η' : tateModule p R, padicPow η a = η ^ m * η' ^ p ^ k := by
  obtain ⟨b, hb⟩ := h
  refine ⟨padicPow η b, ?_⟩
  rw [← padicPow_natCast, ← padicPow_natCast, ← padicPow_mul, ← padicPow_add]
  congr 1
  push_cast
  linear_combination hb

end tateModule

open Tilt tateModule

theorem isPrimitive_iff (ε : tateModule p R) : IsPrimitive ε ↔ seq 1 ε.1 ≠ 1 := by
  rw [IsPrimitive, ← seq_zero, seq_frobeniusEquiv_symm]

theorem IsPrimitive.isPrimitiveRoot {ε : tateModule p R} (hε : IsPrimitive ε) (n : ℕ) :
    IsPrimitiveRoot (seq n ε.1) (p ^ n) := by
  rcases n with _ | n
  · rw [seq_zero, untilt_eq_one, pow_zero]; exact IsPrimitiveRoot.one
  · rw [← orderOf_eq_prime_pow (x := seq (n + 1) ε.1) _ (seq_pow_eq_one ε _)]
    · exact IsPrimitiveRoot.orderOf _
    · rw [add_comm, seq_add_pow]; exact (isPrimitive_iff ε).1 hε

theorem IsPrimitive.padicPow_iff {ε : tateModule p R} (hε : IsPrimitive ε) (a : ℤ_[p]) :
    IsPrimitive (padicPow ε a) ↔ IsUnit a := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [isPrimitive_iff, seq_padicPow, Ne, (hε.isPrimitiveRoot 1).pow_eq_one_iff_dvd,
    ← ZMod.natCast_eq_zero_iff, cast_val_toZModPow, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]

section Domain

variable [IsDomain R]

theorem IsPrimitive.padicPow_surjective {ε : tateModule p R} (hε : IsPrimitive ε) :
    Function.Surjective (padicPow ε) := by
  intro η
  have h : ∀ n, ∃ i : ℕ, seq n ε.1 ^ i = seq n η.1 := fun n => by
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨i, -, hi⟩ := (hε.isPrimitiveRoot n).eq_pow_of_pow_eq_one (seq_pow_eq_one η n)
    exact ⟨i, hi⟩
  choose i hi using h
  have hd : ∀ n, (p : ℤ) ^ n ∣ (i (n + 1) : ℤ) - i n := fun n => by
    have h1 : seq n ε.1 ^ i n = seq n ε.1 ^ i (n + 1) := by
      rw [hi, ← seq_succ_pow η.1, ← hi, ← seq_succ_pow ε.1 n, ← pow_mul, ← pow_mul, mul_comm]
    have hf : IsOfFinOrder (seq n ε.1) :=
      (hε.isPrimitiveRoot n).isOfFinOrder (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    rw [hf.pow_eq_pow_iff_modEq, ← (hε.isPrimitiveRoot n).eq_orderOf] at h1
    exact_mod_cast h1.dvd
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun n => (i n : ℤ)) p hd), tateModule.ext_seq fun n => ?_⟩
  rw [← hi]
  apply seq_padicPow_of_eq
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hd]
  simp

theorem IsPrimitive.exists_unit {ε ε' : tateModule p R} (hε : IsPrimitive ε)
    (hε' : IsPrimitive ε') : ∃ a : ℤ_[p]ˣ, ε' = padicPow ε a := by
  obtain ⟨a, rfl⟩ := hε.padicPow_surjective ε'
  obtain ⟨a, rfl⟩ := (hε.padicPow_iff a).1 hε'
  exact ⟨a, rfl⟩

end Domain

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem exists_pow_eq (x : R) {n : ℕ} (hn : 0 < n) : ∃ y : R, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) x) hn
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) hn
    (x := z) (by rw [hz]; exact isIntegral_algebraMap)
  exact ⟨y, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩

theorem Tilt.seq_surjective (n : ℕ) : Function.Surjective (seq n : Tilt p R → R) := by
  have h0 : ∀ x : R, ∃ y : Tilt p R, seq 0 y = x := fun x => by
    choose r hr using fun z : R => exists_pow_eq z (Fact.out : p.Prime).pos
    exact ⟨ofSeq (fun n => r^[n] x) (fun n => by rw [Function.iterate_succ_apply', hr]),
      seq_ofSeq _ _ 0⟩
  intro x
  obtain ⟨y, hy⟩ := h0 x
  exact ⟨y ^ p ^ n, by rw [map_pow, ← hy, ← seq_add_pow y 0 n, zero_add]⟩

theorem Tilt.untilt_surjective_of_isAlgClosed : Function.Surjective (PreTilt.untilt : Tilt p R → R) := fun x => by
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 0 x
  exact ⟨y, by rw [← seq_zero, hy]⟩

instance : Nonempty (PFlat p R) :=
  let ⟨y, hy⟩ := Tilt.untilt_surjective_of_isAlgClosed (p := p) (p : R)
  ⟨⟨y, hy⟩⟩


variable (p R) in
def pflat : PFlat p R := Classical.arbitrary _

variable [CharZero R]

variable (p R) in
theorem exists_isPrimitive : ∃ ε : tateModule p R, IsPrimitive ε := by
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  haveI : NeZero (p : FractionRing R) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing R) p
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R)
    (Fact.out : p.Prime).pos (x := ζ) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hz := hζ.of_map_of_injective (IsFractionRing.injective R (FractionRing R))
  obtain ⟨y, hy⟩ := Tilt.seq_surjective (p := p) 1 z
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change PreTilt.untilt y = 1
    rw [← seq_zero, ← seq_succ_pow, zero_add, hy, hz.pow_eq_one]
  · rw [isPrimitive_iff]
    change seq 1 y ≠ 1
    rw [hy]
    exact hz.ne_one (Fact.out : p.Prime).one_lt

variable (p R) in
def eps : tateModule p R := (exists_isPrimitive p R).choose

variable (p R) in
theorem isPrimitive_eps : IsPrimitive (eps p R) := (exists_isPrimitive p R).choose_spec

end Good

namespace PFlat

variable [IsDomain R] [CharZero R]

variable [ValuationRing R]

end PFlat

end Reformulated.AutPerF
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]

section Witt

variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]












end Witt

section FracWitt

variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]





end FracWitt

variable [IsAdicComplete (span {(p : R)}) R]



namespace BdRPlus

variable {p}

variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]

theorem exists_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) :
    ∃ s : L →+* BdRPlus p R, (∀ x, theta p R (s x) = j x) ∧
      ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by
  letI : Algebra F (AinfInv p R) := ι.toAlgebra
  let e := RingHom.quotientKerEquivOfSurjective hθ
  let f : L →ₐ[F] AinfInv p R ⧸ AinfInv.kerTheta p R :=
    { e.symm.toRingHom.comp j with
      commutes' := fun a => by
        change e.symm (j (algebraMap F L a)) = Ideal.Quotient.mk _ (ι a)
        rw [RingEquiv.symm_apply_eq, hj]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq f
  refine ⟨g.toRingHom, fun x => ?_, fun a => g.commutes a⟩
  have h1 : AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x) = e.symm (j x) :=
    AlgHom.congr_fun hg x
  change e (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) (g x)) = j x
  rw [h1, RingEquiv.apply_symm_apply]

def «section» [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) : L →+* BdRPlus p R :=
  (exists_section hθ ι j hj).choose

end BdRPlus

end Reformulated.AutPerF
end
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

theorem evalₐ_eq_zero_iff_dvd (a : A) (n : ℕ) (x : AdicCompletion (span {a}) A) :
    AdicCompletion.evalₐ (span {a}) n x = 0 ↔
      algebraMap A (AdicCompletion (span {a}) A) a ^ n ∣ x := by
  constructor
  · intro h
    have h1 : AdicCompletion.eval (span {a}) A n x = 0 := by
      rw [← AdicCompletion.factor_evalₐ_eq_eval (span {a}) x (by simp), h, map_zero]
    have h2 : x ∈ (span {a} ^ n • ⊤ : Submodule A (AdicCompletion (span {a}) A)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton a)]
      exact h1
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, -, rfl⟩ := h2
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (mem_span_singleton_self _) _), zero_mul]

theorem descFactorial_pred_modEq {m k : ℕ} (hk : k < m) :
    ∃ c : ℤ, ((m - 1).descFactorial k : ℤ) = (-1) ^ k * (k ! : ℤ) + m * c := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    have h : ((m - 1 - k : ℕ) : ℤ) = m - (k + 1) := by omega
    refine ⟨(-1) ^ k * (k ! : ℤ) + (m - (k + 1)) * c, ?_⟩
    rw [Nat.descFactorial_succ, Nat.cast_mul, h, hc, Nat.factorial_succ]
    push_cast
    ring

theorem mul_sum_descFactorial {B : Type*} [CommRing B] [Algebra ℚ B] (m : ℕ) (x : B) :
    (m : B) * ∑ k ∈ Finset.range m,
      ((m - 1).descFactorial k : B) * ((((k + 1) ! : ℕ) : ℚ)⁻¹ • x ^ (k + 1)) = (x + 1) ^ m - 1 := by
  rw [add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := Finset.mem_range.1 hk; omega⟩
  rw [← mul_assoc, ← Nat.cast_mul, Nat.add_sub_cancel, ← Nat.succ_descFactorial_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Algebra.smul_def,
    ← map_natCast (algebraMap ℚ B) (k + 1)!]
  have : algebraMap ℚ B ((k + 1)! : ℕ) * algebraMap ℚ B (((k + 1)! : ℕ) : ℚ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one]
  linear_combination (((m + 1).choose (k + 1) : ℕ) : B) * x ^ (k + 1) * this

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace AcrisZero

@[simp] theorem coe_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (gamma n x hx : AinfInv p R) = AinfInv.gamma n (algebraMap _ _ x) := rfl

theorem p_pow_mul_cancel (n : ℕ) {x y : AcrisZero p R} (h : (p : AcrisZero p R) ^ n * x = p ^ n * y) :
    x = y := by
  apply Subtype.ext
  have h' := congrArg (Subtype.val) h
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h'
  exact ((AinfInv.isUnit_p p).pow n).mul_left_cancel h'

theorem p_mul_cancel {x y : AcrisZero p R} (h : (p : AcrisZero p R) * x = p * y) : x = y :=
  p_pow_mul_cancel 1 (by simpa using h)

theorem mem_span_pow_iff (n : ℕ) (x : AcrisZero p R) :
    x ∈ span {(p : AcrisZero p R)} ^ n ↔ (p : AcrisZero p R) ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem factorial_mul_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : AcrisZero p R) * gamma n x hx = algebraMap (Ainf p R) _ x ^ n := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma,
    AinfInv.gamma, Subalgebra.coe_algebraMap]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]

end AcrisZero

namespace Acris

theorem factorPow_eval {m n : ℕ} (hle : m ≤ n) (x : Acris p R) :
    Ideal.Quotient.factorPow _ hle (eval p R n x) = eval p R m x :=
  factorPow_evalₐ _ hle x

theorem eval_eq_zero_iff (n : ℕ) (x : Acris p R) : eval p R n x = 0 ↔ (p : Acris p R) ^ n ∣ x := by
  have := evalₐ_eq_zero_iff_dvd (p : AcrisZero p R) n x
  rw [map_natCast] at this
  exact this

theorem exists_eq_add (n : ℕ) (x : Acris p R) :
    ∃ (a : AcrisZero p R) (y : Acris p R), x = algebraMap _ _ a + (p : Acris p R) ^ n * y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R n x)
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (x - algebraMap _ _ a)).1
    (by rw [map_sub, eval_algebraMap, ha, sub_self])
  exact ⟨a, y, by rw [← hy]; ring⟩

theorem eq_zero_of_forall_dvd {x : Acris p R} (h : ∀ n, (p : Acris p R) ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [(eval_eq_zero_iff n x).2 (h n), map_zero]

instance isAdicComplete : IsAdicComplete (span {(p : Acris p R)}) (Acris p R) := by
  have := AdicCompletion.isAdicComplete_self (span {(p : AcrisZero p R)})
    (Submodule.fg_span_singleton _)
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
  exact this

theorem eq_zero_of_p_mul_eq_zero {x : Acris p R} (h : (p : Acris p R) * x = 0) : x = 0 := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R (n + 1) x)
  have h1 := congrArg (eval p R (n + 1)) h
  rw [map_mul, map_zero, map_natCast, ← ha,
    ← map_natCast (Ideal.Quotient.mk (span {(p : AcrisZero p R)} ^ (n + 1))), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff] at h1
  obtain ⟨b, hb⟩ := h1
  have hab : a = p ^ n * b := AcrisZero.p_mul_cancel (by rw [hb]; ring)
  rw [← factorPow_eval (Nat.le_succ n), ← ha, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff]
  exact ⟨b, hab⟩

theorem p_mul_cancel {x y : Acris p R} (h : (p : Acris p R) * x = p * y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero (by rw [mul_sub, h, sub_self]))

theorem p_mem_nonZeroDivisors : (p : Acris p R) ∈ nonZeroDivisors (Acris p R) :=
  mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_p_mul_eq_zero h

theorem p_pow_mul_cancel (n : ℕ) {x y : Acris p R} (h : (p : Acris p R) ^ n * x = p ^ n * y) :
    x = y :=
  sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 (pow_mem p_mem_nonZeroDivisors n) _
    (by rw [mul_sub, h, sub_self]))

theorem hom_ext {B : Type*} [CommRing B] [IsHausdorff (span {(p : B)}) B] {f g : Acris p R →+* B}
    (h : ∀ a : AcrisZero p R, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]
  intro n
  obtain ⟨a, y, rfl⟩ := exists_eq_add n x
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, h]
  ring

theorem exists_quot (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) :
    ∃ l : AcrisZero p R, (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1 ∧
      eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  refine ⟨∑ k ∈ Finset.range (p ^ n), ((p ^ n - 1).descFactorial k : AcrisZero p R) *
    AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]), ?_, ?_⟩
  · apply Subtype.ext
    have := mul_sum_descFactorial (p ^ n) (algebraMap (Ainf p R) (AinfInv p R) (u - 1))
    rw [← map_one (algebraMap (Ainf p R) (AinfInv p R)), ← map_add (f := _), sub_add_cancel, map_one,
      Nat.cast_pow] at this
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AddSubmonoidClass.coe_finsetSum, AcrisZero.coe_gamma, AinfInv.gamma,
      AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subalgebra.coe_algebraMap]
    exact this
  · rw [eval_log u hu le_rfl, Ideal.Quotient.eq, logPartial, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨c, hc⟩ := descFactorial_pred_modEq (Finset.mem_range.1 hk)
    have hc' := congrArg (Int.cast : ℤ → AcrisZero p R) hc
    push_cast at hc'
    rw [AcrisZero.mem_span_pow_iff, hc']
    exact ⟨-c, by ring⟩

theorem eval_log_of_mul_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) (l : AcrisZero p R)
    (hl : (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  obtain ⟨l', h1, h2⟩ := exists_quot u hu n
  rw [h2, AcrisZero.p_pow_mul_cancel n (h1.trans hl.symm)]

theorem log_congr {u v : Ainf p R} (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (h : u = v) : log u hu = log v hv := by subst h; rfl

theorem log_mul (u v : Ainf p R) (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (huv : Ainf.theta p R (u * v) = 1) : log (u * v) huv = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha, ha'⟩ := exists_quot u hu n
  obtain ⟨b, hb, hb'⟩ := exists_quot v hv n
  rw [map_add (f := eval p R n), ha', hb', eval_log_of_mul_eq _ huv n (a + b + p ^ n * a * b),
    ← (Ideal.Quotient.mk (span {(p : AcrisZero p R)} ^ n)).map_add,
    Ideal.Quotient.eq, AcrisZero.mem_span_pow_iff]
  · exact ⟨a * b, by ring⟩
  · rw [map_mul, mul_pow, eq_add_of_sub_eq ha.symm, eq_add_of_sub_eq hb.symm]
    ring

@[simp] theorem log_one (h : Ainf.theta p R 1 = 1) : log (1 : Ainf p R) h = 0 :=
  ext_eval fun n => by rw [eval_log_of_mul_eq _ h n 0 (by simp), map_zero, map_zero]

theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  unfold logTeich
  rw [← log_mul _ _ _ _ (by
    rw [map_mul, Ainf.theta_teich, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2,
      show PreTilt.untilt η'.1 = 1 from η'.2, one_mul])]
  exact log_congr _ _ (map_mul _ _ _)

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 :=
  (log_congr _ (map_one _) (map_one _)).trans (log_one _)


theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, logTeich_mul, ih]; push_cast; ring

end Acris

namespace BcrisPlus

theorem algebraMap_injective : Function.Injective (algebraMap (Acris p R) (BcrisPlus p R)) :=
  IsLocalization.injective (M := Submonoid.powers (p : Acris p R)) _
    (Submonoid.powers_le.2 Acris.p_mem_nonZeroDivisors)

end BcrisPlus

namespace Bcris

theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  simp [logTeich, Acris.logTeich_mul]

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 := by simp [logTeich]

theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  simp [logTeich, Acris.logTeich_pow]

theorem isUnit_logTeich {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) :=
  IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R)
    ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩

theorem isUnit_p : IsUnit (p : Bcris p R) := by
  simpa using (BcrisPlus.isUnit_p p R).map (algebraMap _ (Bcris p R))

end Bcris

end Reformulated.AutPerF
end
end
