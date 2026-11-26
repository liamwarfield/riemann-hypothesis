module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAuxiliaryPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SepFil

variable {l : ℕ} [Fact l.Prime]

theorem ev_eq_zero_iff_pt {e : Per.Fl l} (he : GlobalTheory.MemLoc.IsEps e) (m : ℕ) (y : Per.BdRp l) :
    Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y := by
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hfil := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1 1
  have hx : GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e)) := by
    rw [GlobalTheory.MemLoc.aDp, RingHom.comp_apply]
  have hmem : ∀ (n : ℕ) (a : Per.AinfP l), a ∈ Per.kerP l ^ n ↔
      algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n ∣ a := by
    intro n a
    rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hback : ∀ (n : ℕ) (w : Per.BdRp l), GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n ∣ w → Per.ev l n w = 0 := by
    rintro n w ⟨z, rfl⟩
    rw [map_mul, hx, ← map_pow (algebraMap (Per.AinfP l) (Per.BdRp l)), GlobalTheory.MemLoc.CrisUnique.ev_alg,
      Ideal.Quotient.eq_zero_iff_mem.2 ((hmem n _).2 dvd_rfl), zero_mul]
  have hnu : ¬ IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e)) := by
    intro h
    have h1 := (hθ _).2 ((hfil (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e))).2 (by rw [pow_one]))
    exact (h.map (Per.θD l)).ne_zero h1
  have hone : ∀ w : Per.BdRp l, Per.ev l 1 w = 0 → GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ∣ w := by
    intro w hw
    by_cases h0 : Per.θD l w = 0
    · have h1 := (hfil w).1 ((hθ w).1 h0)
      rwa [pow_one] at h1
    · exfalso
      have h1 := (hu w h0).map (Per.ev l 1)
      rw [hw, isUnit_zero_iff, eq_comm, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)),
        Ideal.Quotient.eq_zero_iff_mem, hmem, pow_one] at h1
      apply hnu
      rw [hx]
      exact (isUnit_of_dvd_one h1).map _
  have hdense : ∀ (n : ℕ) (w : Per.BdRp l), ∃ (a : Per.AinfP l) (z : Per.BdRp l),
      w = algebraMap (Per.AinfP l) (Per.BdRp l) a + GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n * z := by
    intro n w
    induction n with
    | zero => exact ⟨0, w, by rw [map_zero, pow_zero, one_mul, zero_add]⟩
    | succ n ih =>
      obtain ⟨a, z, hz⟩ := ih
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 z)
      obtain ⟨z', hz'⟩ := hone (z - algebraMap (Per.AinfP l) (Per.BdRp l) b) (by
        rw [map_sub, GlobalTheory.MemLoc.CrisUnique.ev_alg, hb, sub_self])
      refine ⟨a + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n * b, z', ?_⟩
      rw [map_add (f := _), map_mul, map_pow, ← hx, pow_succ, mul_assoc, ← hz', hz]
      ring
  refine ⟨fun hy ↦ ?_, hback m y⟩
  obtain ⟨a, z, hz⟩ := hdense m y
  have h1 := hback m _ (dvd_mul_right (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m) z)
  rw [hz, map_add (f := _), h1, add_zero, GlobalTheory.MemLoc.CrisUnique.ev_alg, Ideal.Quotient.eq_zero_iff_mem, hmem] at hy
  rw [hz]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [hx, ← map_pow]
  exact map_dvd _ hy

theorem dvd_of_forall_near {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ)
    (c : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (a : Ainf l) (z : Per.BdRp l),
      c - (l : Per.BdRp l) ^ r * GlobalTheory.MemLoc.aDp l a = GlobalTheory.MemLoc.aDp l d ^ m * z) :
    GlobalTheory.MemLoc.aDp l d ^ m ∣ c := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.CrisUnique.exists_isEps l
  have hk := GlobalTheory.MemLoc.ker_theta_eq_span_xi he
  have hxd : GlobalTheory.MemLoc.xi e ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hk, ← hd]
    exact Ideal.mem_span_singleton_self d
  have hdx : d ∣ GlobalTheory.MemLoc.xi e := by
    rw [← Ideal.mem_span_singleton, hd, hk]
    exact Ideal.mem_span_singleton_self _
  have hev : ∀ y : Per.BdRp l, Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y :=
    ev_eq_zero_iff_pt he m
  have h0 : Per.ev l m c = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r ↦ ?_
    obtain ⟨a, z, hz⟩ := h r
    refine ⟨a, ?_⟩
    have h1 : Per.ev l m (GlobalTheory.MemLoc.aDp l d ^ m * z) = 0 :=
      (hev _).2 (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (map_dvd _ hxd) m) z)
    rw [← hz, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast,
      GlobalTheory.MemLoc.CrisUnique.ev_aDp] at h1
    exact h1
  exact (pow_dvd_pow_of_dvd (map_dvd _ hdx) m).trans ((hev c).1 h0)

end GlobalTheory.BKReal.SepFil

namespace GlobalTheory.BKReal.SepFil

theorem dvd_of_forall_near_OD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O),
    (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) →
    ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m w h
  have hE : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  set d := ϖ.ev 1 (eis l 1 e) with hd_def
  have hd : Ideal.span {d} = RingHom.ker (Per.θ l) := ϖ.span_ev_eis 1
  have hξ : ϖ.iAl O K (EIn l e _) ^ m = (1 : O) ⊗ₜ[ℤ_[l]] (GlobalTheory.MemLoc.aDp l d ^ m) := by
    rw [hE, Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  rw [hξ] at h ⊢
  let b := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ i, GlobalTheory.MemLoc.aDp l d ^ m ∣ GlobalTheory.Decompl.crd b i w := by
    intro i
    refine dvd_of_forall_near hd m _ fun r ↦ ?_
    obtain ⟨y, z, hz⟩ := h r
    refine ⟨GlobalTheory.Decompl.crd b i y, GlobalTheory.Decompl.crd b i z, ?_⟩
    have h1 := congrArg (GlobalTheory.Decompl.crd b i) hz
    have h2 : GlobalTheory.Decompl.crd b i (toOD l O y) = GlobalTheory.MemLoc.aDp l (GlobalTheory.Decompl.crd b i y) :=
      GlobalTheory.Decompl.crd_map b (ainfToBdRp l) i y
    rw [LinearMap.map_sub, ← Nat.cast_pow, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_mul, h2,
      Nat.cast_pow] at h1
    exact h1
  choose c hc using key
  refine ⟨∑ j, b j ⊗ₜ[ℤ_[l]] c j, GlobalTheory.Decompl.ext_crd b fun i ↦ ?_⟩
  rw [GlobalTheory.Decompl.crd_mul, GlobalTheory.Decompl.crd_sum, ← hc i]

end GlobalTheory.BKReal.SepFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearODStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_approx_toOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O), (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) → ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  first | exact @GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | exact GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | (intros; apply GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime]

theorem aDp_ev_eis_mul_eq_zero {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Per.BdRp l)
    (hy : GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) * y = 0) : y = 0 := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
    rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxi
  refine (GlobalTheory.MemLoc.filtration_eq_xi_pow l ε hE).2.1 y ?_
  rw [← hc, map_mul, mul_assoc, hy, mul_zero]

theorem eis_pow_dvd_of_aDp_mem {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ)
    (x : (Wq l a)⟦X⟧)
    (h : GlobalTheory.MemLoc.aDp l (ϖ.ev a x) ∈ Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n}) :
    eis l a e ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have h1 : Per.θ l (ϖ.ev a x) = 0 := by
      have h2 := congrArg (Per.θD l) hc
      rw [map_mul, map_pow, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1,
        (ϖ.theta_ev_eq_zero_iff a _).2 dvd_rfl] at h2
      exact Subtype.ext (h2.symm.trans (by simp))
    obtain ⟨x', rfl⟩ := (ϖ.theta_ev_eq_zero_iff a x).1 h1
    have h2 : GlobalTheory.MemLoc.aDp l (ϖ.ev a x') ∈
        Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨c, ?_⟩
      rw [← sub_eq_zero]
      apply aDp_ev_eis_mul_eq_zero (a := a) ϖ
      rw [map_mul, map_mul] at hc
      rw [mul_sub, ← hc]
      ring
    obtain ⟨z, hz⟩ := ih x' h2
    exact ⟨z, by rw [hz, pow_succ']; ring⟩

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def crdB {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) : OD l O →ₗ[ℤ_[l]] Per.BdRp l :=
  TensorProduct.lid ℤ_[l] (Per.BdRp l) ∘ₗ (b.coord j).rTensor (Per.BdRp l)

theorem crdB_tmul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (o : O) (β : Per.BdRp l) :
    crdB b j (o ⊗ₜ β) = b.coord j o • β := rfl

theorem crdB_mul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (c : Per.BdRp l) (z : OD l O) :
    crdB b j (z * (1 ⊗ₜ c)) = crdB b j z * c := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o β =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, crdB_tmul, crdB_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add (f := _), map_add (f := _), hx, hy, add_mul]

theorem crdB_sum {J : Type} [Fintype J] [DecidableEq J] (b : Module.Basis J ℤ_[l] O) (j : J)
    (β : J → Per.BdRp l) : crdB b j (∑ k, b k ⊗ₜ β k) = β j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single j (fun k _ hk => by
    rw [crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply, hk])
    (by simp), crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

variable {a e : ℕ} [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem toAc_eis (t : Wq l a →ₐ[ℤ_[l]] O) : toAc t K (eis l a e) = fun _ => EIn l e (A O K) := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  have hE : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [eis, map_add (f := _), map_pow, hX, map_natCast, hE]
  rfl

theorem exists_of_toOD_iTot_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (f : ZMod a → A O K)
    (h : toOD l O (ϖ.iTot t K f) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n}) :
    ∃ g : ZMod a → A O K, f = (fun _ => EIn l e (A O K)) ^ n * g := by
  classical
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K b f
  have hT : toOD l O (ϖ.iTot t K (∑ j, b j • toAc t K (x j))) =
      ∑ j, b j ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, PiSys.iTot_toAc]
    refine Finset.sum_congr rfl fun j _ => ?_
    show b j • ((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j))) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have hx : ∀ j, eis l a e ^ n ∣ x j := fun j => by
    apply eis_pow_dvd_of_aDp_mem ϖ n
    rw [Ideal.mem_span_singleton']
    refine ⟨crdB b j z, ?_⟩
    have := congrArg (crdB b j) (hz.trans hT)
    rw [crdB_sum, Algebra.TensorProduct.tmul_pow, one_pow, crdB_mul] at this
    exact this
  choose y hy using hx
  refine ⟨∑ j, b j • toAc t K (y j), ?_⟩
  simp only [hy, map_mul, map_pow, toAc_eis, Finset.mul_sum, mul_smul_comm]

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.PiSys

open GlobalTheory.BKReal.HatDescent

theorem eq_Ehat_pow_mul_of_iD_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e),
    ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} →
      ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ n x hx
  have hd : ϖ.iD t K (fun _ => Ehat O K l e) =
      (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
    rw [iD, glue_const, Ehat, iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  choose g x' hg using fun τ => exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) n (x τ)
  have hsplit : x = (fun τ => ofAl O K l e (g τ)) + (fun _ => Ehat O K l e) ^ n * x' :=
    funext fun τ => hg τ
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (l : A O K)) (S := invL l (A O K)) g
  choose r hr using hm

  have h1 : ϖ.iD t K (fun τ => ofAl O K l e (g τ)) ∈
      Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} := by
    rw [hsplit, map_add (f := _), map_mul, map_pow] at hx
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hx
  have h2 : (fun τ => ofA O K l e (r τ)) =
      (fun _ => ofA O K l e ((l : A O K) ^ m)) * fun τ => ofAl O K l e (g τ) := by
    funext τ
    rw [Pi.mul_apply, ofA, RingHom.comp_apply, RingHom.comp_apply, hr τ, Algebra.smul_def, map_mul]
  have h3 : toOD l O (ϖ.iTot t K r) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n} := by
    rw [← iD_ofA, h2, map_mul, ← hd]
    exact Ideal.mul_mem_left _ _ h1
  obtain ⟨h, hh⟩ := exists_of_toOD_iTot_mem t ϖ n r h3
  have hu : IsUnit (algebraMap (A O K) (invL l (A O K)) (l : A O K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hEA : algebraMap (A O K) (invL l (A O K)) (EIn l e (A O K)) = EIn l e (invL l (A O K)) := rfl
  have hgτ : ∀ τ, g τ = EIn l e (invL l (A O K)) ^ n *
      (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) := fun τ => by
    have h4 : algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m * g τ =
        EIn l e (invL l (A O K)) ^ n * algebraMap (A O K) (invL l (A O K)) (h τ) := by
      have h5 := (hr τ).symm
      rw [Algebra.smul_def, hh, Pi.mul_apply, Pi.pow_apply] at h5
      simp only [map_mul, map_pow, hEA] at h5
      exact h5
    have hone : (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val, ← mul_pow, hu.val_inv_mul, one_pow]
    linear_combination (-(g τ)) * hone + (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * h4
  refine ⟨fun τ => ofAl O K l e (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) + x' τ, ?_⟩
  funext τ
  rw [hg τ, Pi.mul_apply, Pi.pow_apply, hgτ τ, map_mul, map_pow, mul_add]
  rfl

end GlobalTheory.BKReal.PiSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisibleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_membership_divisible : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e), ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} → ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  first | exact @GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | exact GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem | (intros; apply GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_of_dvd_restrict_discS : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  intro l _ K bk ρ h0 h1 R hR y hy
  obtain ⟨q, k, r, hr, e⟩ := GlobalTheory.T.weierstrass_division_closedDisc_breuilKisin l K bk ρ h0 h1 y
  have e' := congrArg R e
  rw [map_mul, map_add (f := _), map_mul, hR.ext, hR.ext, RingHom.id_apply, RingHom.id_apply] at e'
  have hd : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) := by
    have h2 := hy.mul_left (R (((l : ℕ) : bk.DS ρ) ^ k))
    rw [e'] at h2
    exact (dvd_add_right (dvd_mul_right _ _)).1 h2
  have hr0 := GlobalTheory.T.breuilKisin_poly_eq_zero_of_disc_dvd l K bk r hr hd
  rw [hr0, Polynomial.coe_zero, map_zero, add_zero] at e
  exact ((isUnit_l_disc l (X : bk.S) ρ).pow k).dvd_mul_left.1 ⟨q, e⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  first | exact @GlobalTheory.BSP.dvd_of_dvd_restrict_discS | exact GlobalTheory.BSP.dvd_of_dvd_restrict_discS | (intros; apply GlobalTheory.BSP.dvd_of_dvd_restrict_discS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.exists_Ep_eq_X_pow_add {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : Polynomial (Wq l bk.a),
      bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos hi, hi, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

theorem BK.norm_toDisc_E_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 →
    ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  intro l _ K bk ρ h0 h1 y
  obtain ⟨_, _, ⟨hρ0, _, hρe⟩, _⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hρ : 0 < ρ := hρ0.trans_le h0
  rw [GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative l K bk ρ hρ h1]
  congr 1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  apply le_antisymm
  · obtain ⟨q, hq⟩ := bk.exists_Ep_eq_X_pow_add
    have hE : bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (q : bk.S) := by
      simp only [BK.E]
      conv_lhs => rw [hq]
      rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C,
        map_natCast]
    have hl' : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ ≤ (l : ℝ)⁻¹ :=
      gauge_le l (X : bk.S) ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0,
        by rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], by simp⟩)
    have hX : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) ((X : bk.S) ^ bk.Ep.natDegree)‖ ≤
        (ρ : ℝ) ^ bk.Ep.natDegree :=
      (norm_ofPre l (X : bk.S) ρ _).symm.trans_le (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) _ hρ)
    have hup : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) bk.E‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
      rw [hE, map_add (f := _), map_mul, norm_preDisc]
      refine (gauge_add_le_max l (X : bk.S) ρ _ _).trans (max_le ?_ ?_)
      · rw [← norm_preDisc]; exact hX
      · rw [← norm_preDisc]
        calc _ ≤ ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ *
              ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (q : bk.S)‖ := norm_mul_le _ _
          _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hl' (norm_algebraMap_le _) (norm_nonneg _) (by positivity)
          _ = ((bk.ρ₀ ^ bk.Ep.natDegree : ℝ≥0) : ℝ) := by rw [hρe]; simp
          _ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
            rw [NNReal.coe_pow]; exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast h0) _
    exact (norm_ofPre l (X : bk.S) ρ _).trans_le hup
  · obtain ⟨a, ha1, ha2, -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ h1
    obtain ⟨-, -, -, hk⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
    have hc : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]
    have h := ha2 bk.Ep.natDegree (toDisc l (X : bk.S) ρ bk.E)
    rw [ha1, hc, hk 1 isUnit_one, one_mul] at h
    exact h

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  first | exact @GlobalTheory.BSP.BK.norm_toDisc_E_mul | exact GlobalTheory.BSP.BK.norm_toDisc_E_mul | (intros; apply GlobalTheory.BSP.BK.norm_toDisc_E_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_map_eq (l : ℕ) [Fact l.Prime] {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (u : A) (u' : A') (ρ ρ' : ℝ≥0) (h0 : 0 < ρ') (hu : f u = u') (h : ρ' ≤ ρ) :
    ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  have h1 : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    have := norm_toDisc_pow_le (l := l) (u := u') 1 h0
    rw [pow_one, pow_one] at this
    rw [hu]
    exact this.trans (by exact_mod_cast h)
  exact ⟨_, isDiscMap_map f h1⟩

theorem BK.rho_zero_pos {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

theorem norm_E_mul_of_topBasis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (y : Disc l (s X) ρ) :
    ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  have hρ : 0 < ρ := bk.rho_zero_pos.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨cD, -, hmul, hle, -, -, hsup, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  have key : ∀ i, ‖cD i (toDisc l (s X) ρ (s bk.E) * y)‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖cD i y‖ := fun i => by
    rw [← hj.ext, hmul, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1]
  refine le_antisymm (hsup _ _ (by positivity) fun i => ?_) ?_
  · rw [key]
    exact mul_le_mul_of_nonneg_left (hle i y) hρ'.le
  · rw [← le_div_iff₀' hρ']
    refine hsup _ _ (by positivity) fun i => ?_
    rw [le_div_iff₀' hρ', ← key]
    exact hle _ _

theorem E_dvd_of_topBasis (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (hR : IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R) (y : Disc l (s X) ρ)
    (hy : toDisc l (s X) bk.ρ₀ (s bk.E) ∣ R y) : toDisc l (s X) ρ (s bk.E) ∣ y := by
  have hρ₀ := bk.rho_zero_pos
  have hρ : 0 < ρ := hρ₀.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨j₀, hj₀⟩ := exists_discMap_of_map_eq l s X (s X) bk.ρ₀ bk.ρ₀ hρ₀ rfl le_rfl
  obtain ⟨RS, hRS⟩ := exists_discMap_of_map_eq l (RingHom.id bk.S) X X ρ bk.ρ₀ hρ₀ rfl h0
  obtain ⟨cD, hc, hmul, hle, hnull, -, hsup, hex, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  obtain ⟨cD₀, hc₀, hmul₀, hle₀, -, -, -, -, -⟩ :=
    GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ hρ₀ (h0.trans_lt h1) j₀ hj₀
  have comm : ∀ i x, cD₀ i (R x) = RS (cD i x) := fun i => by
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.1 (bk.DS bk.ρ₀) (fun z hz => by
        rw [nsmul_eq_mul] at hz
        exact (isUnit_l_disc l (X : bk.S) bk.ρ₀).mul_right_eq_zero.1 hz)
      ((cD₀ i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i))
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hle₀ i (R x)).trans (hR.norm_le x)).trans (one_mul _).ge)
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hRS.norm_le (cD i x)).trans (hle i x)).trans (one_mul _).ge)
      (fun a => by
        change cD₀ i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
        rw [hR.ext, hc, hRS.ext, RingHom.id_apply, RingHom.id_apply, hc₀])
    exact fun x => DFunLike.congr_fun h x
  obtain ⟨w, hw⟩ := hy
  have hd : ∀ i, ∃ z, cD i y = toDisc l (X : bk.S) ρ bk.E * z := fun i =>
    GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc l K bk ρ h0 h1 RS hRS _ ⟨cD₀ i w, by rw [← comm, hw, ← hj₀.ext, hmul₀]⟩
  choose z hz using hd
  have hzn : Filter.Tendsto z Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_zero_iff_norm_tendsto_zero.1 (hnull y)).div_const ((ρ : ℝ) ^ bk.Ep.natDegree)
    rw [zero_div] at h
    refine h.congr fun i => ?_
    rw [hz, GlobalTheory.T.norm_eisenstein_mul_closedDisc_eq_rpow l K bk ρ h0 h1, mul_div_cancel_left₀ _ hρ'.ne']
  obtain ⟨y', hy'⟩ := hex z hzn
  refine ⟨y', ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine hsup _ 0 le_rfl fun i => ?_
  rw [map_sub, ← hj.ext, hmul, hy', hz, sub_self, norm_zero]

theorem div_E_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 →
    (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧
    ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ),
      toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  intro l _ K bk A _ s ι TB ρ h0 h1
  refine ⟨norm_E_mul_of_topBasis l K bk A s ι TB ρ h0 h1, fun R hR h => ?_⟩
  have hρ' : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast bk.rho_zero_pos) _
  induction h with
  | zero => intro y _; rw [pow_zero]; exact one_dvd _
  | succ h ih =>
    intro y hy
    obtain ⟨y', rfl⟩ := E_dvd_of_topBasis l K bk A s ι TB ρ h0 h1 R hR y
      ((dvd_pow_self _ (Nat.succ_ne_zero h)).trans hy)
    obtain ⟨w, hw⟩ := hy
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih y' ⟨w, ?_⟩)
    rw [map_mul, hR.ext, RingHom.id_apply, pow_succ', mul_assoc, ← sub_eq_zero, ← mul_sub] at hw
    have h2 := norm_E_mul_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl (h0.trans_lt h1)
      (R y' - toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * w)
    rw [hw, norm_zero] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hρ'.ne'))

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 → (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧ ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ), toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  first | exact @GlobalTheory.BSP.div_E_of_topBasis | exact GlobalTheory.BSP.div_E_of_topBasis | (intros; apply GlobalTheory.BSP.div_E_of_topBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitQuotientPrimePowEqExponent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.LenUnitPow

variable (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem _root_.GlobalTheory.LenUnitPow.natCast_ne_zero : (l : O) ≠ 0 := by
  intro h
  have hker : (RingHom.ker (algebraMap ℤ_[l] O)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) ?_
    intro hbot
    have hl : ((l : ℤ_[l])) ∈ RingHom.ker (algebraMap ℤ_[l] O) := by
      rw [RingHom.mem_ker, map_natCast]; exact h
    rw [hbot, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  have hbot : (⊥ : Ideal O).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) (⊥ : Ideal O) ?_
    change (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal
    rwa [← RingHom.ker_eq_comap_bot]
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal hbot).symm

theorem _root_.GlobalTheory.LenUnitPow.natCast_not_isUnit : ¬ IsUnit (l : O) := by
  intro h
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) (IsLocalRing.maximalIdeal O)
  have hl : (l : ℤ_[l]) ∈ Ideal.comap (algebraMap ℤ_[l] O) (IsLocalRing.maximalIdeal O) := by
    rw [IsLocalRing.eq_maximalIdeal hm, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.mem_comap, map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hl
  exact hl h

end GlobalTheory.LenUnitPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionField
noncomputable section

namespace GlobalTheory.PointRepConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem exists_gl_of_equiv {K Γ : Type} [Field K] {n : ℕ} (A B : Γ → Matrix (Fin n) (Fin n) K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ g u, e (Matrix.toLin' (A g) u) = Matrix.toLin' (B g) (e u)) :
    ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * A g = B g * (P : Matrix (Fin n) (Fin n) K) := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simpa [Matrix.toLin'_mul] using he g u

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  intro hC R H what₂ N i r r' hr hr' x
  have h₁ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r x)).1 (hr x)
  have h₂ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r' x)).1 (hr' x)
  obtain ⟨e, he⟩ := GlobalTheory.ComplementCompare.isRx_unique N hC i x _ _ h₁ h₂
  exact exists_gl_of_equiv _ _ e he

end GlobalTheory.PointRepConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionFieldStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointGaloisReps_conjugate_over_fraction_field : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  first | exact @GlobalTheory.PointRepConj.main | exact GlobalTheory.PointRepConj.main | (intros; apply GlobalTheory.PointRepConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMem
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.IntegralPowerScalar

theorem exists_pow_mul_integral {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (c : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * c ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] c := IsAlgebraic.of_finite ℚ_[l] c
  have h2 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hs := PadicInt.unitCoeff_spec hy
  have hm : y • c ∈ OL LL := hint
  have hm2 := (OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    exact (Units.inv_mul_eq_iff_eq_mul _).2 hs
  rw [smul_smul, he, Algebra.smul_def, map_pow, map_natCast] at hm2
  exact hm2

theorem smul_mem_of_mem {l : ℕ} [Fact (Nat.Prime l)] {LL : FinExt l} (T : GlobalTheory.BKGal.QLat LL)
    {c : ↥LL.1} (hc : c ∈ OL LL) {x : T.V} (hx : x ∈ T.L.T) : c • x ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx
  rw [← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x] at h
  exact h

theorem exists_pow_smul_mem {l : ℕ} [inst : Fact (Nat.Prime l)] {LL : FinExt l}
    (T : GlobalTheory.BKGal.QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  have hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL := fun k => pow_mem (natCast_mem (OL LL) l) k
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := smul_mem_of_mem T (hl n) hm
    have h2 := smul_mem_of_mem T (hl m) hn
    rw [smul_smul, ← pow_add, Nat.add_comm] at h1
    rw [smul_smul, ← pow_add] at h2
    rw [smul_add]
    exact T.L.T.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_mul_integral LL c
    refine ⟨n + m, ?_⟩
    have h := smul_mem_of_mem T hn hm
    have e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m := by ring
    have e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x :=
      (smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)
    exact Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h

end GlobalTheory.IntegralPowerScalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDegree
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedDegree

theorem exists_degree : ∀ (l : ℕ) [Fact l.Prime],
    (∀ n : ℕ, 0 < n → ∀ σ : GQ l, ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
    (∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) → a ≡ b [MOD n]) →
    ∃ z : GQ l → ℤ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
      ∀ (σ : GQ l) (a : ℕ), (∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
        z σ = (a : ℤ_[l]) := by
  intro l hl h1 h2
  have hpos : ∀ k : ℕ, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  choose a ha using fun (σ : GQ l) (k : ℕ) => h1 (l ^ k) (hpos k) σ
  have hdv : ∀ (σ : GQ l) (k : ℕ), (l : ℤ) ^ k ∣ (a σ (k + 1) : ℤ) - (a σ k : ℤ) := by
    intro σ k
    have h := h2 (l ^ k) (a σ k) (a σ (k + 1)) (hpos k) fun x hx => by
      rw [← ha σ k x hx, ← ha σ (k + 1) x (by
        rw [pow_succ l k]; exact GlobalTheory.UnramifiedCrys.pow_pow_mul hx l)]
    exact_mod_cast h.dvd
  obtain ⟨z, hz⟩ : ∃ z : GQ l → ℤ_[l], ∀ σ k, PadicInt.toZModPow k (z σ) = (a σ k : ZMod (l ^ k)) := by
    refine ⟨fun σ => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ)), fun σ k => ?_⟩
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ) k,
      Int.cast_natCast]
  have key : ∀ (σ : GQ l) (k b : ℕ), (∀ x : Om l, x ^ l ^ l ^ k = x → σ x = x ^ l ^ b) →
      PadicInt.toZModPow k (z σ) = (b : ZMod (l ^ k)) := by
    intro σ k b hb
    rw [hz, ZMod.natCast_eq_natCast_iff]
    exact h2 _ _ _ (hpos k) fun x hx => by rw [← ha σ k x hx, hb x hx]
  refine ⟨z, ?_, fun σ τ => ?_, fun σ b hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have hev : ∀ᶠ σ in 𝓝 σ₀, ∀ x ∈ {y : Om l | y ^ l ^ l ^ k = y}, σ x = σ₀ x := by
      refine (GlobalTheory.UnramifiedCrys.finite_fixedPow (p := l) (R := Om l) (hpos k)).eventually_all.2
        fun x _ => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).preimage
        (continuous_const_mul σ₀⁻¹)
      filter_upwards [ho.mem_nhds (show σ₀ ∈ _ by simp)] with σ hσ
      have h : σ₀⁻¹ (σ x) = x := hσ
      have h' := congrArg σ₀ h
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
    filter_upwards [hev] with σ hσ
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero, hz σ₀]
    exact key σ k _ fun x hx => by rw [hσ x hx, ha σ₀ k x hx]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_add (f := _), hz σ, hz τ, ← Nat.cast_add]
    refine key _ k _ fun x hx => ?_
    rw [AlgEquiv.mul_apply, ha τ k x hx, map_pow, ha σ k x hx, ← pow_mul, ← pow_add]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_natCast]
    exact key σ k b (hb _ (hpos k))

end GlobalTheory.UnramifiedDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysExt

theorem exists_ext {A B M N R T ι : Type} [CommRing A] [CommRing B] [CommRing R] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (J : T → B →+* R)
    (v : M →+ (T → ι → R)) (hv : ∀ (w : A) (x : M) τ i, v (w • x) τ i = J τ (f w) * v x τ i) :
    ∃ lam : N →+ (T → ι → R), (∀ (r : B) (y : N) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧
      ∀ x, lam (u x) = v x := by
  letI : Module B (T → ι → R) := Module.compHom (T → ι → R)
    (RingHom.pi fun τ => RingHom.pi fun _ : ι => J τ : B →+* (T → ι → R))
  let v' : M →ₛₗ[f] (T → ι → R) :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun w x => funext fun τ => funext fun i => hv w x τ i }
  obtain ⟨lam, hlam, -⟩ := h (T → ι → R) v'
  exact ⟨lam.toAddMonoidHom, fun r y τ i => congrFun (congrFun (lam.map_smul r y) τ) i, hlam⟩

theorem frob_toAc {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O)
    (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem exists_coord : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c hc PP p J g hJ
  let v : EE.M (ϖ.prism a) →+ (ZMod a → ι → K⟦X⟧⟦X⟧) :=
    { toFun := fun x τ i => g (frob K l (c x (τ - 1) i))
      map_zero' := by ext1 τ; ext1 i; simp
      map_add' := fun x y => by ext1 τ; ext1 i; simp }
  obtain ⟨lam, h1, h2⟩ := exists_ext (EE.tr_bc p) J v (fun w x τ i => by
    change g (frob K l (c (w • x) (τ - 1) i)) = J τ (p.f w) * g (frob K l (c x (τ - 1) i))
    have e1 : c (w • x) (τ - 1) i = (toAc t K w (τ - 1) : K⟦X⟧) * c x (τ - 1) i :=
      congrFun (congrFun (hc w x) (τ - 1)) i
    have e2 := hJ τ w
    have e3 := frob_toAc (K := K) t w τ
    rw [e1, map_mul, map_mul]
    exact congrArg (· * _) ((congrArg g e3).trans e2.symm))
  exact ⟨lam, h1, fun x τ i => congrFun (congrFun (h2 x) τ) i⟩

end GlobalTheory.CrysExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystal_coordinates_over_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  first | exact @GlobalTheory.CrysExt.exists_coord | exact GlobalTheory.CrysExt.exists_coord | (intros; apply GlobalTheory.CrysExt.exists_coord <;> assumption)
end
end
