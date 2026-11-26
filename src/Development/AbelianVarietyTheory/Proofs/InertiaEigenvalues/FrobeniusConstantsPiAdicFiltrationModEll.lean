module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplFrob

variable {l : ℕ} [Fact l.Prime]

theorem frobW_inclW (a : Ainf l) :
    frobW l (inclW l a) = inclW l (WittVector.map (frobenius (OCb l) l) a) := by
  ext n
  rw [coeff_frobW, coeff_inclW, coeff_inclW, WittVector.map_coeff, frobenius_def, map_pow]

theorem frob_inclR (LL : FinExt l) (a : RA LL) :
    ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a' := by
  refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]]
    WittVector.map (frobenius (OCb l) l) (crd (basisO LL) j a), ext_crd (basisO LL) fun i => ?_⟩
  rw [crd_φRW, crd_inclR, crd_inclR, crd_sum, frobW_inclW]

theorem nearPi_frob {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m n : ℕ)
    (h : n ≤ m * l) (x : RW LL) (hx : NearPi AI LL s m x) : NearPi AI LL s n (φRW LL x) := by
  rw [nearPi_iff_crd] at hx ⊢
  intro i
  obtain ⟨c, hc⟩ := hx i
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(AI.εroot s - 1) ^ k * c ^ l, ?_⟩
  rw [crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, hk, pow_add, mul_assoc]

theorem near_self {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R) :
    Near ι p t 1 t := ⟨1, 0, by simp⟩

theorem not_isUnit_root_sub_one {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) := fun h =>
  one_ne_zero ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 1
    fun m => (h.pow m).dvd)

theorem dvd_of_coeff {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) (z : ℤ_[l]) (c : OCb l)
    (h : (z • (1 : WCb l)).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ 1 * c)) :
    (l : ℤ_[l]) ∣ z := by
  by_contra hz
  have hu : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    rw [← PadicInt.norm_lt_one_iff_dvd] at hz
    exact le_antisymm z.2 (not_lt.1 hz)
  have h1 : z • (1 : WCb l) = inclW l (zlW l (OCb l) z) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (map_zlW l (algebraMap (OCb l) (Cb l)) z).symm
  rw [h1, coeff_inclW, pow_one] at h
  have h2 := IsFractionRing.injective (OCb l) (Cb l) h
  have h3 : IsUnit ((zlW l (OCb l) z).coeff 0) :=
    (hu.map (zlW l (OCb l))).map (WittVector.constantCoeff : Ainf l →+* OCb l)
  rw [h2] at h3
  exact not_isUnit_root_sub_one AI s (isUnit_of_mul_isUnit_left h3)

theorem const_dvd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (o : ↥(OL LL))
    (h : NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o)) :
    ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  rw [nearPi_iff_crd] at h
  have h1 : ∀ i, (l : ℤ_[l]) ∣ (basisO LL).repr o i := fun i => by
    obtain ⟨c, hc⟩ := h i
    exact dvd_of_coeff AI s _ c hc
  choose d hd using h1
  refine ⟨∑ i, d i • basisO LL i, ?_⟩
  rw [Finset.mul_sum]
  refine ((basisO LL).sum_repr o).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hd, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem frobenius_and_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ),
    (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧
    NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧
    (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧
    ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) →
      ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  intro l hl P AI LL s
  refine ⟨frob_inclR LL, ?_, fun m x hx => ?_, const_dvd AI LL s⟩
  · exact nearPi_frob AI LL s 1 2 (by rw [one_mul]; exact hl.out.two_le) _ (near_self _ _ _)
  · exact nearPi_frob AI LL s m m (Nat.le_mul_of_pos_right m hl.out.pos) x hx

end GlobalTheory.DecomplFrob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEllStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧ NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧ (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧ ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) → ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  first | exact @GlobalTheory.DecomplFrob.frobenius_and_constants | exact GlobalTheory.DecomplFrob.frobenius_and_constants | (intros; apply GlobalTheory.DecomplFrob.frobenius_and_constants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionActionOnFixK1
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem _root_.GlobalTheory.GLp.red_surjective (g : ℕ) [Fact g.Prime] (n : ℕ) :
    Function.Surjective (_root_.GlobalTheory.GLp.red g n) :=
  _root_.GlobalTheory.GLp.Model.red_surjective n

theorem _root_.GlobalTheory.GLp.red_invFun (x : _root_.GlobalTheory.GLq.Gn g n) :
    _root_.GlobalTheory.GLp.red g n (Function.invFun (_root_.GlobalTheory.GLp.red g n) x) = x :=
  Function.invFun_eq (_root_.GlobalTheory.GLp.red_surjective g n x)

theorem _root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (v : V) :
    v ∈ _root_.GlobalTheory.GLp.fixK1 π ↔ ∀ k : GL (Fin n) ℤ_[g],
      _root_.GlobalTheory.GLp.red g n k = 1 → π (_root_.GlobalTheory.GLp.inc g n k) v = v :=
  _root_.GlobalTheory.GLp.Model.mem_principalCongruenceFixedVectors_iff π v

theorem _root_.GlobalTheory.GLp.padicIntGL_smul_mem_principalCongruenceFixed (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    {v : V} (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) (a : GL (Fin n) ℤ_[g]) :
    π (_root_.GlobalTheory.GLp.inc g n a) v ∈ _root_.GlobalTheory.GLp.fixK1 π := by
  rw [_root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff] at hv ⊢
  intro k hk
  have hconj : _root_.GlobalTheory.GLp.red g n (a⁻¹ * k * a) = 1 := by simp [hk]
  have h : k * a = a * (a⁻¹ * k * a) := by group
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, h, map_mul, map_mul, Module.End.mul_apply,
    hv _ hconj]

theorem _root_.GlobalTheory.GLp.inc_eq_of_red_eq (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    {v : V} (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) {a b : GL (Fin n) ℤ_[g]}
    (hab : _root_.GlobalTheory.GLp.red g n a = _root_.GlobalTheory.GLp.red g n b) :
    π (_root_.GlobalTheory.GLp.inc g n a) v = π (_root_.GlobalTheory.GLp.inc g n b) v := by
  have hk : _root_.GlobalTheory.GLp.red g n (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab, inv_mul_cancel]
  have hb : b = a * (a⁻¹ * b) := by group
  conv_rhs => rw [hb]
  rw [map_mul, map_mul, Module.End.mul_apply,
    (_root_.GlobalTheory.GLp.mem_principalCongruenceFixedVectors_iff π v).1 hv _ hk]

theorem _root_.GlobalTheory.GLp.lift_mul_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V}
    (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) (x y : _root_.GlobalTheory.GLq.Gn g n) :
    π (_root_.GlobalTheory.GLp.lift g n (x * y)) v =
      π (_root_.GlobalTheory.GLp.lift g n x) (π (_root_.GlobalTheory.GLp.lift g n y) v) := by
  obtain ⟨a, rfl⟩ := _root_.GlobalTheory.GLp.red_surjective g n x
  obtain ⟨b, rfl⟩ := _root_.GlobalTheory.GLp.red_surjective g n y
  rw [← map_mul, _root_.GlobalTheory.GLp.Model.lift_red π hv,
    _root_.GlobalTheory.GLp.Model.lift_red π hv b,
    _root_.GlobalTheory.GLp.Model.lift_red π
      (_root_.GlobalTheory.GLp.padicIntGL_smul_mem_principalCongruenceFixed π hv b) a,
    map_mul, map_mul, Module.End.mul_apply]

theorem _root_.GlobalTheory.GLp.lift_one_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V}
    (hv : v ∈ _root_.GlobalTheory.GLp.fixK1 π) :
    π (_root_.GlobalTheory.GLp.lift g n 1) v = v := by
  rw [← map_one (_root_.GlobalTheory.GLp.red g n), _root_.GlobalTheory.GLp.Model.lift_red π hv,
    map_one, map_one, Module.End.one_apply]

theorem actK_zero (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : actK π 0 = 0 := by
  simp [actK]

theorem actK_add (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : MonoidAlgebra ℂ (Gn g n)) :
    actK π (a + b) = actK π a + actK π b := by
  simp [actK, add_smul, Finset.sum_add_distrib]

theorem actK_single (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (x : Gn g n) (c : ℂ) :
    actK π (MonoidAlgebra.single x c) = c • π (lift g n x) := by
  unfold actK
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Finsupp.single_eq_of_ne hy]
  · simp

theorem actK_mul_apply (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {v : V} (hv : v ∈ fixK1 π)
    (a b : MonoidAlgebra ℂ (Gn g n)) : actK π (a * b) v = actK π a (actK π b v) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp [actK_zero]
  | add a a' ha ha' => simp [add_mul, actK_add, ha, ha']
  | single x c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp [actK_zero]
    | add b b' hb hb' => simp only [mul_add, actK_add, hb, hb', LinearMap.add_apply, map_add (f := _)]
    | single y d =>
      rw [MonoidAlgebra.single_mul_single, actK_single, actK_single, actK_single]
      simp only [LinearMap.smul_apply, map_smul, lift_mul_apply π hv, smul_smul, mul_comm]

theorem finite_group_acts_on_fixK1 :
    ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V), Function.Surjective (red g n) ∧ ∀ v ∈ fixK1 π, (∀ x, π (lift g n x) v ∈ fixK1 π) ∧ (∀ k, π (inc g n k) v = π (lift g n (red g n k)) v) ∧ (∀ x y, π (lift g n (x * y)) v = π (lift g n x) (π (lift g n y) v)) ∧ (∀ a b, actK π (a * b) v = actK π a (actK π b v)) ∧ actK π 1 v = v := by
  intro g _ n V _ _ π
  refine ⟨red_surjective g n, fun v hv => ⟨fun x => padicIntGL_smul_mem_principalCongruenceFixed π hv _,
    fun k => inc_eq_of_red_eq π hv (red_invFun _).symm, lift_mul_apply π hv, actK_mul_apply π hv, ?_⟩⟩
  rw [MonoidAlgebra.one_def, actK_single]
  simp [lift_one_apply π hv]

end GlobalTheory.GLp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.EigenDegree

theorem abstract {B D : Type} [CommRing B] [CommRing D] [IsDomain D] (ι : B →+* D)
    (hι : Function.Injective ι) (φ : B →+* B) (F : ℤ → D → Prop) (h1 : F 0 1)
    (hmul : ∀ a b x y, F a x → F b y → F (a + b) (x * y)) (p t : B) (hp : IsUnit p) (ht : IsUnit t)
    (hφt : φ t = p * t) (ht2 : ¬ F 2 (ι t)) (hsucc : ∀ y, F 1 y → ∃ z, F 0 z ∧ y = ι t * z)
    (hfund : ∀ b, φ b = b → F 0 (ι b) → b ≠ 0 → ∃ c, c * b = 1 ∧ F 0 (ι c))
    (n : ℕ) (hn : 0 < n) (x : B) (hx : (⇑φ)^[n] x = p * x) (hx0 : x ≠ 0) (hx1 : F 1 (ι x))
    (hj0 : ∀ j, j < n → F 0 (ι ((⇑φ)^[j] x))) :
    IsUnit x ∧ ¬ F 2 (ι x) ∧ ∀ j, 0 < j → j < n → ¬ F 1 (ι ((⇑φ)^[j] x)) := by
  haveI : IsDomain B := hι.isDomain ι
  have hprod : ∀ (d : ℕ → ℤ) (f : ℕ → D) (s : Finset ℕ), (∀ i ∈ s, F (d i) (f i)) →
      F (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
    intro d f s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact hmul _ _ _ _ (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hne : ∀ j, j < n → (⇑φ)^[j] x ≠ 0 := by
    intro j hj h
    have e : (⇑φ)^[n] x = 0 := by
      rw [← Nat.sub_add_cancel hj.le, Function.iterate_add_apply, h, iterate_map_zero]
    rw [hx] at e
    exact mul_ne_zero hp.ne_zero hx0 e
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ j ∈ Finset.range n, (⇑φ)^[j] x := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun j hj => hne j (Finset.mem_range.1 hj)
  have hφN : φ N = p * N := by
    apply mul_right_cancel₀ hx0
    have e1 := Finset.prod_range_succ (fun j => (⇑φ)^[j] x) n
    have e2 := Finset.prod_range_succ' (fun j => (⇑φ)^[j] x) n
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e2
    rw [← map_prod, ← hN, e1, ← hN, hx] at e2
    rw [← e2]
    ring
  have hN1 : F 1 (ι N) := by
    have := hprod (fun i => if i = 0 then 1 else 0) (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      split_ifs with h
      · subst h; exact hx1
      · exact hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN] at this
    simpa [hn] using this
  obtain ⟨s, hs⟩ := ht.exists_right_inv
  obtain ⟨z, hz, hz'⟩ := hsucc _ hN1
  have hb : t * (s * N) = N := by rw [← mul_assoc, hs, one_mul]
  have hφb : φ (s * N) = s * N := by
    apply (hp.mul ht).mul_left_cancel
    rw [← hφt, ← map_mul, hb, hφN, hφt, mul_assoc, hb]
  have hbz : ι (s * N) = z := by
    rw [map_mul, hz', ← mul_assoc, ← map_mul, mul_comm s, hs, map_one, one_mul]
  obtain ⟨c, hc, hc0⟩ := hfund _ hφb (hbz ▸ hz) (fun h => hN0 (by rw [← hb, h, mul_zero]))
  have htc : t = c * N := by
    calc t = t * (c * (s * N)) := by rw [hc, mul_one]
      _ = c * (t * (s * N)) := by ring
      _ = c * N := by rw [hb]
  have hNu : IsUnit N := isUnit_of_mul_isUnit_right (htc ▸ ht)
  have hN2 : ¬ F 2 (ι N) := by
    intro h
    apply ht2
    have := hmul _ _ _ _ hc0 h
    rwa [zero_add, ← map_mul, ← htc] at this
  have key : ∀ j, j < n → ¬ F ((if j = 0 then 1 else 0) + 1) (ι ((⇑φ)^[j] x)) := by
    intro j hj h
    apply hN2
    have := hprod (fun i => (if i = 0 then 1 else 0) + (if i = j then 1 else 0))
      (fun i => ι ((⇑φ)^[i] x)) (Finset.range n) (by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simpa using h
      · by_cases h0 : i = 0
        · subst h0
          simpa [hij] using hx1
        · simpa [hij, h0] using hj0 i (Finset.mem_range.1 hi))
    rw [← map_prod, ← hN, Finset.sum_add_distrib] at this
    simpa [hn, hj, one_add_one_eq_two] using this
  refine ⟨?_, ?_, fun j h0 hj => ?_⟩
  · refine isUnit_of_dvd_unit ?_ hNu
    rw [hN]
    exact Finset.dvd_prod_of_mem (fun j => (⇑φ)^[j] x) (Finset.mem_range.2 hn)
  · simpa [one_add_one_eq_two] using key 0 hn
  · simpa [h0.ne'] using key j hj

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem main : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l,
    (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 →
    (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) →
    IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧
      ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  intro l _ C n hn x hx hx0 hx1 hj0
  obtain ⟨-, h1, hmul, -, -, -, hP⟩ := filD_laws l
  obtain ⟨htu, -, ht2, hlu⟩ := core_t_unit_fil l C
  have he := core_isEps l C
  have hlog := (LogFun.log_fun l C.ε C.t he.1 C.t_log).2.2.2 C.j C.j_cris
  haveI : IsDomain (Per.BdR l) := (BdRField.bdR_isField l).2.2.1.isDomain
  refine abstract C.ι (ULaws.u_laws l C).2.2.2.1 (Per.φB l) (fun a y => y ∈ Per.FilD l a) h1 hmul
    (l : Per.Bcris l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) hlu htu ?_ ?_ ?_ ?_ n hn x hx hx0 hx1 hj0
  · rw [fund_phiB_alg, TPhi.t_phi l C, map_mul, map_natCast]
  · intro h
    rw [C.ι_j] at h
    exact ht2 ((hP 2 _).1 h)
  · intro y hy
    obtain ⟨z, hz, e⟩ := (TiedUnif.filD_succ he hlog 0 y).1 (by rwa [zero_add])
    exact ⟨z, hz, by rw [C.ι_j]; exact e⟩
  · intro b hb hb0 hne
    obtain ⟨c, rfl⟩ := fundamental_exact l C b hb hb0
    have hc : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [map_zero, map_zero])
    refine ⟨C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c⁻¹), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    · show C.ι _ ∈ _
      rw [C.ι_u]
      exact TiedUnif.alg_mem_FilD_zero _

end GlobalTheory.MemLoc.EigenDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegreeStatement
open Formalism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusEigen_fil_one_isUnit_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (n : ℕ), 0 < n → ∀ x : Per.Bcris l, (⇑(Per.φB l))^[n] x = (l : Per.Bcris l) * x → x ≠ 0 → C.ι x ∈ Per.FilD l 1 → (∀ j : ℕ, j < n → C.ι ((⇑(Per.φB l))^[j] x) ∈ Per.FilD l 0) → IsUnit x ∧ C.ι x ∉ Per.FilD l 2 ∧ ∀ j : ℕ, 0 < j → j < n → C.ι ((⇑(Per.φB l))^[j] x) ∉ Per.FilD l 1 := by
  first | exact @GlobalTheory.MemLoc.EigenDegree.main | exact GlobalTheory.MemLoc.EigenDegree.main | (intros; apply GlobalTheory.MemLoc.EigenDegree.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.GenSpan

open GlobalTheory.TateTop ReciprocityTheory.Gal

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

theorem gen_zmod {χ : G →* ℤ_[l]ˣ} {r : ℕ} {c : G × G → ℤ_[l]} (h : Gen χ r c) :
    (IsLocallyConstant (fun p => PadicInt.toZModPow r (c p)) ∧
      ∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * PadicInt.toZModPow r (c (k, m))
        - PadicInt.toZModPow r (c (g * k, m)) + PadicInt.toZModPow r (c (g, k * m))
        - PadicInt.toZModPow r (c (g, k)) = 0) ∧
    (∀ z : G × G → ZMod (l ^ r), IsLocallyConstant z →
      (∀ g k m, PadicInt.toZModPow r (χ g : ℤ_[l]) * z (k, m) - z (g * k, m) + z (g, k * m)
        - z (g, k) = 0) →
      ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
        z p = PadicInt.toZModPow r (c p) * x +
          (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1)) ∧
    (∀ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b →
      (∀ p, PadicInt.toZModPow r (c p) * x =
          PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) → x = 0) := by
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let : Module ℤ_[l] (ZMod (l ^ r)) := Module.compHom _ (PadicInt.toZModPow r)
  have hs : ∀ (a : ℤ_[l]) (m : ZMod (l ^ r)), a • m = PadicInt.toZModPow r a * m := fun _ _ => rfl
  have h0 : PadicInt.toZModPow r ((l : ℤ_[l]) ^ r) = 0 := (dvd_iff_toZModPow _).1 dvd_rfl
  have hM : ∀ m : ZMod (l ^ r), (l : ℤ_[l]) ^ r • m = 0 := fun m => by rw [hs, h0, zero_mul]
  obtain ⟨h1, h2, h3⟩ := h _ hM
  refine ⟨?_, fun z hz hz' => ?_, fun x b hb hx => h3 x b hb fun p => ?_⟩
  · obtain ⟨a1, a2⟩ := h1 1
    simp only [hs, mul_one] at a1 a2
    exact ⟨a1, a2⟩
  · obtain ⟨x, b, hb, e⟩ := h2 z ⟨hz, fun g k m => by simpa only [hs] using hz' g k m⟩
    exact ⟨x, b, hb, fun p => by simpa only [GlobalTheory.TateTop.cob, hs] using e p⟩
  · simpa only [GlobalTheory.TateTop.cob, hs] using hx p

open GlobalTheory.PadicH2Separated in
theorem span : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  intro l _ G _ _ _ _ χ c hχ hgen hfin
  have hl : l.Prime := Fact.out
  have hG := fun r => gen_zmod (hgen r)
  have hcc : Continuous c := GlobalTheory.PadicH2Separated.continuous_of_reductions c fun s =>
    (hG (s + 1)).1.1.continuous
  have hcoc : ∀ g h k, (χ g : ℤ_[l]) * c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0 := by
    intro g h k
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    simpa only [map_sub, map_add (f := _), map_mul, map_zero] using (hG n).1.2 g h k
  refine ⟨⟨continuous_subtype_val.comp hcc, fun g h k => ?_⟩, fun z hz hzc => ?_⟩
  · have e := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) (hcoc g h k)
    push_cast at e
    exact e
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hz.continuousOn
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C (by exact_mod_cast hl.one_lt : (1 : ℝ) < l)
  have hnorm : ∀ p, ‖(l : ℚ_[l]) ^ m * z p‖ ≤ 1 := fun p => by
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hp : (0 : ℝ) < (l : ℝ) ^ m := by have := hl.pos; positivity
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact (hC p trivial).trans hm.le
  let w : G × G → ℤ_[l] := fun p => ⟨(l : ℚ_[l]) ^ m * z p, hnorm p⟩
  have hw : ∀ p, (w p : ℚ_[l]) = (l : ℚ_[l]) ^ m * z p := fun _ => rfl
  have hwc : Continuous w := (continuous_const.mul hz).subtype_mk _
  have hwcoc : ∀ g h k, (χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) = 0 := by
    intro g h k
    have e : (((χ g : ℤ_[l]) * w (h, k) - w (g * h, k) + w (g, h * k) - w (g, h) : ℤ_[l]) :
        ℚ_[l]) = 0 := by
      push_cast [hw]
      linear_combination (l : ℚ_[l]) ^ m * hzc g h k
    exact PadicInt.coe_eq_zero.1 e
  have hlev : ∀ r, ∃ (x : ZMod (l ^ r)) (b : G → ZMod (l ^ r)), IsLocallyConstant b ∧ ∀ p,
      PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * x +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * b p.2 - b (p.1 * p.2) + b p.1) := fun r =>
    (hG r).2.1 _ ((IsLocallyConstant.iff_continuous _).2
      ((GlobalTheory.PadicH2Separated.continuous_reduction r).comp hwc))
      fun g k m => by
        simpa only [map_sub, map_add (f := _), map_mul, map_zero] using
          congrArg (PadicInt.toZModPow r) (hwcoc g k m)
  choose X B hB hXB using hlev
  have hred : ∀ r, PadicInt.toZModPow r (((X r).val : ℕ) : ℤ_[l]) = X r := fun r => by
    have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hcomp : ∀ r, ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) (X (r + 1)) = X r := by
    intro r
    set ψ := ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))
    have hψ : ∀ a : ℤ_[l], ψ (PadicInt.toZModPow (r + 1) a) = PadicInt.toZModPow r a := fun a => by
      rw [ZMod.castHom_apply]
      exact PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r) a
    rw [← sub_eq_zero]
    refine (hG r).2.2 _ (fun g => B r g - ψ (B (r + 1) g)) ((hB r).sub ((hB (r + 1)).comp ψ))
      fun p => ?_
    have e1 : PadicInt.toZModPow r (w p) = PadicInt.toZModPow r (c p) * ψ (X (r + 1)) +
        (PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * ψ (B (r + 1) p.2) - ψ (B (r + 1) (p.1 * p.2)) +
          ψ (B (r + 1) p.1)) := by
      have := congrArg ψ (hXB (r + 1) p)
      simpa only [map_add (f := _), map_sub, map_mul, hψ] using this
    have e2 := hXB r p
    show PadicInt.toZModPow r (c p) * (ψ (X (r + 1)) - X r) =
      PadicInt.toZModPow r (χ p.1 : ℤ_[l]) * (B r p.2 - ψ (B (r + 1) p.2)) -
        (B r (p.1 * p.2) - ψ (B (r + 1) (p.1 * p.2))) + (B r p.1 - ψ (B (r + 1) p.1))
    linear_combination e2 - e1
  obtain ⟨x, hx⟩ := exists_lim (fun r => (((X r).val : ℕ) : ℤ_[l])) fun r => by
    rw [dvd_iff_toZModPow, map_sub, hred, ← PadicInt.cast_toZModPow r (r + 1) (Nat.le_succ r),
      hred]
    exact sub_eq_zero.2 (hcomp r)
  have hxr : ∀ r, PadicInt.toZModPow r x = X r := fun r => by
    have := (dvd_iff_toZModPow _).1 (hx r)
    rwa [map_sub, hred, sub_eq_zero] at this
  have hcont : ContAction (charRep χ) := by
    show Continuous fun p : G × ℤ_[l] => charRep χ p.1 p.2
    simp only [charRep_apply]
    exact (hχ.comp continuous_fst).mul continuous_snd
  have hcompat : ∀ (r : ℕ) (g : G) (a : ℤ_[l]), PadicInt.toZModPow r (charRep χ g a) =
      charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) g
        (PadicInt.toZModPow r a) := fun r g a => by
    simp [charRep_apply]
  have hyZ : (fun p => w p - x * c p) ∈ Z2 (charRep χ) := by
    refine (mem_cocycles2 _ _).2 ⟨hwc.sub (continuous_const.mul hcc), fun g h k => ?_⟩
    simp only [charRep_apply]
    linear_combination hwcoc g h k - x * hcoc g h k
  have hyB : ∀ r, (fun p => PadicInt.toZModPow r (w p - x * c p)) ∈
      B2 (charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)) := by
    intro r
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨B r, (hB r).continuous, funext fun p => ?_⟩
    obtain ⟨g, h⟩ := p
    simp only [d1_apply, charRep_apply, MonoidHom.comp_apply, Units.coe_map, map_sub, map_mul, hxr]
    have e := hXB r (g, h)
    simp only at e
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    linear_combination -e
  have hker : ∀ r : ℕ, ∃ w' ∈ Z2 (charRep χ), (fun p => w p - x * c p) - (l : ℤ_[l]) ^ r • w' ∈
      B2 (charRep χ) := fun r =>
    GlobalTheory.padicInt_two_cocycle_eq_pow_smul_of_reduction_coboundary l G (charRep χ) hcont r _
      (hcompat r) _ hyZ (hyB r)
  obtain ⟨f, hf, hfd⟩ := (separated_dvr_second_cohomology_mem _ _).1
    (GlobalTheory.PadicH2Separated.mem_coboundaries_of_forall_pow l G (charRep χ) _ hcompat hfin _ hyZ hker)
  have hl0 : (l : ℚ_[l]) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  refine ⟨(x : ℚ_[l]) / (l : ℚ_[l]) ^ m, fun g => (f g : ℚ_[l]) / (l : ℚ_[l]) ^ m,
    (continuous_subtype_val.comp hf).div_const _, fun g h => ?_⟩
  have e := congrFun hfd (g, h)
  simp only [d1_apply, charRep_apply] at e
  have e' := congrArg (fun a : ℤ_[l] => (a : ℚ_[l])) e
  push_cast [hw] at e'
  field_simp
  linear_combination e'

end GlobalTheory.GenSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamentalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_twoCocycle_multiple_of_fundamental : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (χ : G →* ℤ_[l]ˣ) (c : G × G → ℤ_[l]), Continuous (fun g => (χ g : ℤ_[l])) → (∀ r, GlobalTheory.TateTop.Gen χ r c) → (∀ r : ℕ, 0 < r → Finite (ReciprocityTheory.Gal.H1 (ReciprocityTheory.Gal.charRep ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ)))) → (Continuous (fun p => (c p : ℚ_[l])) ∧ ∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * (c (h, k) : ℚ_[l]) - (c (g * h, k) : ℚ_[l]) + (c (g, h * k) : ℚ_[l]) - (c (g, h) : ℚ_[l]) = 0) ∧ ∀ z : G × G → ℚ_[l], Continuous z → (∀ g h k, ((χ g : ℤ_[l]) : ℚ_[l]) * z (h, k) - z (g * h, k) + z (g, h * k) - z (g, h) = 0) → ∃ (x : ℚ_[l]) (f : G → ℚ_[l]), Continuous f ∧ ∀ g h, ((χ g : ℤ_[l]) : ℚ_[l]) * f h - f (g * h) + f g = z (g, h) - x * (c (g, h) : ℚ_[l]) := by
  first | exact @GlobalTheory.GenSpan.span | exact GlobalTheory.GenSpan.span | (intros; apply GlobalTheory.GenSpan.span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisDD
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R] {M M' M'' : Type}
    [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] [AddCommGroup M''] [Module O M'']

theorem map_smul_alg (f : R →ₐ[O] R) (a : M →ₗ[O] M) (r : R) (x : R ⊗[O] M) :
    TensorProduct.map f.toLinearMap a (r • x) = f r • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add (f := _), hx, hx']
  | tmul r' u => simp [TensorProduct.smul_tmul']

end Ext

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

def Descends : Prop :=
  ∀ (ι : Type) [Fintype ι] (M : ι → ι → W.EE) (w : ι → RW),
    (∀ g : G, W.resΓ g = 1 → ∀ i, gR g (w i) = w i) →
    (∀ i, w i = ∑ j, E.ioE (M i j) * φR (w j)) → ∀ i, ∃ e : W.EE, E.ioE e = w i

theorem nontrivial_EE (W : LocWach PD LL O v n) : Nontrivial W.EE :=
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  W.EE_inj.nontrivial

theorem exists_basis_jD (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    ∃ c : Module.Basis ι RW (TW RW T), ∀ i, c i = E.jD T (e i) := by
  classical
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  haveI := nontrivial_EE W
  haveI : Nontrivial RW := (ioE_injective E).nontrivial
  haveI := T.L.free
  have hsp : ⊤ ≤ Submodule.span RW (Set.range fun i => E.jD T (e i)) := by
    rw [← E.jD_span T, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [E.jD_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨basisOfTopLeSpanOfCardEqFinrank (fun i => E.jD T (e i)) hsp ?_,
    fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i⟩
  rw [Module.finrank_baseChange, ← (W.DD_free T).2, Module.finrank_eq_card_basis e]

include E in
theorem exists_basis_DD (T : LocLat G Qp LL O) :
    Nonempty (Module.Basis (Fin (Module.finrank O ↥T.L.T)) W.EE (W.DD T)) := by
  haveI := nontrivial_EE W
  haveI := (W.DD_free T).1
  haveI := finite_DD E T
  exact ⟨Module.finBasisOfFinrankEq _ _ (W.DD_free T).2⟩

theorem jD_fixed (T : LocLat G Qp LL O) (g : G) (hg : W.resΓ g = 1) (x : W.DD T) :
    TWact (gR g) T g (E.jD T x) = E.jD T x := by
  rw [← E.jD_act, hg, W.γD_one]

theorem exists_frob_inv (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hφ : Function.Surjective φR) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (e : Module.Basis ι W.EE (W.DD T)) :
    Submodule.span W.EE (Set.range fun i => W.φD T (e i)) = ⊤ := by
  refine eq_top_DD E hm T _ ?_
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ : ∃ x, TWmap φR T x = y :=
    TensorProduct.map_surjective (g := φR.toLinearMap) hφ Function.surjective_id y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← c.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [TWmap, map_smul_alg]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨W.φD T (e i),
    Submodule.subset_span ⟨i, rfl⟩, ?_⟩)
  rw [E.jD_φ, hc]
  rfl

theorem mem_range_jD (hd : Descends E) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (U : ι → ι → W.EE) (z : ι → TW RW T)
    (hz : ∀ g : G, W.resΓ g = 1 → ∀ a, TWact (gR g) T g (z a) = z a)
    (hU : ∀ a, z a = ∑ b, E.ioE (U a b) • TWmap φR T (z b)) (a : ι) :
    ∃ x, E.jD T x = z a := by
  classical
  obtain ⟨e⟩ := exists_basis_DD E T
  obtain ⟨c, hc⟩ := exists_basis_jD E T e
  have h := hd (ι × Fin (Module.finrank O ↥T.L.T))
    (fun p q => U p.1 q.1 * e.repr (W.φD T (e q.2)) p.2) (fun p => c.repr (z p.1) p.2) ?_ ?_
  · choose u hu using h
    refine ⟨∑ k, u (a, k) • e k, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← c.sum_repr (z a)]
    exact Finset.sum_congr rfl fun k _ => by rw [E.jD_smul, hu, hc]
  · rintro g hg ⟨a, k⟩
    have h1 := hz g hg a
    conv_lhs at h1 => rw [← c.sum_repr (z a), map_sum]
    simp only [GlobalTheory.Cyc.Decomp.TWact_smul, hc, jD_fixed E T g hg] at h1
    simp only [← hc] at h1
    conv_rhs => rw [← h1]
    simp [Finsupp.single_apply]
  · rintro ⟨a, k⟩
    have h2 : ∀ q, TWmap φR T (c q) = ∑ r, E.ioE (e.repr (W.φD T (e q)) r) • c r := by
      intro q
      rw [hc, ← E.jD_φ]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← e.sum_repr (W.φD T (e q)), map_sum]
      simp only [E.jD_smul, hc]
    have h3 : ∀ b, c.repr (TWmap φR T (z b)) k =
        ∑ q, E.ioE (e.repr (W.φD T (e q)) k) * φR (c.repr (z b) q) := by
      intro b
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← c.sum_repr (z b), map_sum, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [TWmap, map_smul_alg]
      change c.repr (_ • TWmap φR T (c q)) k = _
      rw [h2, map_smul, Finsupp.smul_apply, c.repr_sum_self, smul_eq_mul, mul_comm]
    change c.repr (z a) k = _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [hU a, map_sum, Finsupp.finsetSum_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Finsupp.smul_apply, h3, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_assoc]

theorem ioE_φE (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have h1 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have h2 := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, hj, h1, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

theorem ioE_γE (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, GlobalTheory.Cyc.Decomp.TWact_smul, h1,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic

end GlobalTheory.WachTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BridgeTie

theorem localCoefficientCompatibility : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i :=
  fun D i => coefficient_compatibility_of D i (fun w hw => GlobalTheory.bridge_degW D.nbr i w hw)

end GlobalTheory.BridgeTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOverStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_comparison_admissible_every_place_over : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i := by
  first | exact @GlobalTheory.BridgeTie.localCoefficientCompatibility | exact GlobalTheory.BridgeTie.localCoefficientCompatibility | (intros; apply GlobalTheory.BridgeTie.localCoefficientCompatibility <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariant
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LTensorSemistableToDeRhamEquivariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lTensor_semistable_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  first | exact @GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | exact GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant | (intros; apply GlobalTheory.InertiaEigenvalues.lTensor_iota_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSst
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem finiteDimensional_Dst_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type)
    [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
    IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  intro l _ P K V _ _ _ ρ h
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  by_cases hV : 0 < finrank ℚ_[l] V
  · have hK : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
    have hpos : 0 < finrank ℚ_[l] ↥(Dst P ρ) := by
      unfold IsSst at h
      rw [h]
      exact Nat.mul_pos hK hV
    exact Module.finite_of_finrank_pos hpos
  · have h0 : finrank ℚ_[l] V = 0 := Nat.eq_zero_of_not_pos hV
    haveI : Subsingleton V := Module.finrank_zero_iff.mp h0
    haveI : Subsingleton (V ⊗[ℚ_[l]] Bst P) := by
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : V ⊗[ℚ_[l]] Bst P, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul v b => rw [Subsingleton.elim v 0, zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      rw [hx x, hx y]
    infer_instance

end GlobalTheory.Pst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZero
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem acris_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  intro l _ x y hxy
  have hl : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hρ0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr hl0
  have hG := isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1
  have hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹ := by
    rw [hG.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ0.le
  have h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0 := by
    have h := hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))
    rw [zero_mul, hc] at h
    have : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · linarith
  by_contra h
  push_neg at h
  have hx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x h.1 (l : ℝ)⁻¹ le_rfl hρ1
  have hy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y h.2 (l : ℝ)⁻¹ le_rfl hρ1
  have hm := hG.2.2.2.1 x y
  rw [hxy, h0] at hm
  have := mul_pos hx hy
  linarith

end GlobalTheory.PMon.Gauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZeroStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  first | exact @GlobalTheory.PMon.Gauss.acris_mul_eq_zero | exact GlobalTheory.PMon.Gauss.acris_mul_eq_zero | (intros; apply GlobalTheory.PMon.Gauss.acris_mul_eq_zero <;> assumption)
end
end
