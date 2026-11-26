module

public import ReciprocityTheory.DualLattices.HasLenCokerDet
public import ReciprocityTheory.DualLattices.PowMemCarrier
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.TowerZeroSurjective
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]

structure Dat (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw)
    [Algebra ℤ_[p] (Tw.O : Type)] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe)
    (cp : (Tw.O : Type)) where
  K : LAlg R₀
  ρO : LHom Tw.O K
  ch : FormalChartAtZero B K g
  wd : WData Tw K

  ρO_eq : wd.ρ1.comp (Tw.q 0) = ρO
  sm : SM B K wd.W wd.ρW
  fin : FIN B Tw.O p
  A : OAct B Tw.O p Oe
  H : HodgeTateData p g (Tw.O : Type) Oe σ cp
  L : Link B Tw Dt H ch.gb A

  tower_zero_surjective : Function.Surjective (Tw.q 0).1

  tower_zero_ker : RingHom.ker (Tw.q 0).1 = Ideal.span {((p : ℕ) : (Tw.O : Type))}

  zeta0 : p = 2 → ((Tw.ζ 0 : (Tw.O : Type)ˣ) : (Tw.O : Type)) = -1

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

namespace Dat

variable (D : Dat p g B Tw Dt Oe σ cp)

lemma pt_p (t : Nb p g) : p • ptOf B D.L.τ t = 0 := by
  have h0 : ∀ j, p • D.L.τ j 0 = 0 := fun j => by simpa using D.L.τ_tors j 0
  simp only [ptOf, Finset.smul_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [smul_comm, h0, smul_zero]

def ptIdx (t : Nb p g) : D.fin.ι :=
  Classical.choose (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t))

def ptMap (t : Nb p g) : LHom (D.fin.AAx (D.ptIdx t)) Tw.O :=
  Classical.choose (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ t) (D.pt_p t)))

def evAll (C : Type) [Field C] [Algebra (Tw.O : Type) C] (F : ∀ i, (D.fin.AAx i : Type)) :
    Nb p g → C :=
  fun t => algebraMap (Tw.O : Type) C ((D.ptMap t).1 (F (D.ptIdx t)))

def evImg (C : Type) [Field C] [Algebra (Tw.O : Type) C] : Submodule (Tw.O : Type) (Nb p g → C) :=
  Submodule.span (Tw.O : Type) (Set.range (D.evAll C))

end Dat

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.DualPairInh
noncomputable section

open Polynomial

namespace ReciprocityTheory.PGsh

namespace DualNum

variable {R₀ : Type} [CommRing R₀] (R : LAlg R₀)

abbrev DN := (R : Type)[X] ⧸ Ideal.span {(X : (R : Type)[X]) ^ 2}

def ev : DN R →+* (R : Type) :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp)

lemma ev_mk (f : (R : Type)[X]) : ev R (Ideal.Quotient.mk _ f) = f.eval 0 := rfl

lemma ev_surj : Function.Surjective (ev R) := fun r => ⟨Ideal.Quotient.mk _ (C r), by rw [ev_mk, eval_C]⟩

def eta : DN R := Ideal.Quotient.mk _ X

lemma eta_sq : eta R * eta R = 0 := by
  unfold eta
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.mem_span_singleton_self _

lemma ker_ev : RingHom.ker (ev R) = Ideal.span {eta R} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker, ev_mk] at hy
    have hX : (X : (R : Type)[X]) ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact hy
    obtain ⟨g, rfl⟩ := hX
    rw [map_mul]
    exact Ideal.mem_span_singleton.2 (dvd_mul_right (eta R) _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show ev R (eta R) = 0
    rw [eta, ev_mk, eval_X]

lemma isLocal : IsLocalRing (DN R) := by
  have hnt : Nontrivial (DN R) := (ev R).domain_nontrivial
  have hunit : ∀ y : DN R, IsUnit (ev R y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ : ∃ u : DN R, u = Ideal.Quotient.mk _ (C (ev R y)) := ⟨_, rfl⟩
    have hev : ev R u = ev R y := by rw [hu, ev_mk, eval_C]
    have hk : y - u ∈ RingHom.ker (ev R) := by rw [RingHom.mem_ker, map_sub, hev, sub_self]
    rw [ker_ev, Ideal.mem_span_singleton] at hk
    obtain ⟨c, hc⟩ := hk
    have hn : IsNilpotent (y - u) := ⟨2, by rw [hc, mul_pow, pow_two (eta R), eta_sq, zero_mul]⟩
    have hu' : IsUnit u := by
      have e : u = ((Ideal.Quotient.mk _).comp Polynomial.C) (ev R y) := hu
      rw [e]
      exact hy.map _
    have h := hn.isUnit_add_left_of_commute hu' (Commute.all _ _)
    rwa [add_sub_cancel] at h
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (ev R a)).imp (hunit a)
      fun h => hunit (1 - a) (by rwa [map_sub, map_one])

lemma ev_algebraMap (r : (R : Type)) : ev R (algebraMap (R : Type) (DN R) r) = r := by
  rw [← Ideal.Quotient.mk_algebraMap, ev_mk]
  simp

def evAlg : DN R →ₐ[R₀] (R : Type) :=
  { ev R with
    commutes' := fun r => by
      show ev R (algebraMap R₀ (DN R) r) = _
      rw [← Ideal.Quotient.mk_algebraMap, ev_mk, Polynomial.algebraMap_apply, eval_C] }

def D : LAlg R₀ := { carrier := DN R, loc := isLocal R }

def dualPair : DualPair R where
  D := D R
  π := ⟨evAlg R, TowerExample.isLocalHom_of_surj _ (ev_surj R)⟩
  σ := ⟨IsScalarTower.toAlgHom R₀ (R : Type) (DN R),
    ⟨fun r hr => by
      have h := hr.map (ev R)
      have e : ev R ((IsScalarTower.toAlgHom R₀ (R : Type) (DN R) : (R : Type) →+* DN R) r) = r :=
        ev_algebraMap R r
      convert h using 1
      exact e.symm⟩⟩
  η := eta R
  sect r := ev_algebraMap R r
  η_sq := eta_sq R
  ker_eq := ker_ev R
  free r h := by
    change algebraMap (R : Type) (DN R) r * eta R = 0 at h
    rw [← Ideal.Quotient.mk_algebraMap, eta, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, X_pow_dvd_iff] at h
    have h1 := h 1 (by norm_num)
    simpa [Polynomial.algebraMap_apply] using h1

end DualNum

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def uR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R :=
  (hv.exists_of_le_one (D.u_int j y)).choose

theorem uR_spec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    algebraMap R C (uR hv D j y) = D.u j y :=
  (hv.exists_of_le_one (D.u_int j y)).choose_spec

def MuR (hv : v.Integers R) (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) R :=
  Matrix.of fun y α => ∏ j, uR hv D j y ^ (α j).val

theorem det_map' {S : Type} [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := by
  exact (f.map_det M).symm

theorem mem_max_of_lt (hv : v.Integers R) [IsLocalRing R] {x : R} (hx : v (algebraMap R C x) < 1) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [hv.isUnit_iff_valuation_eq_one.mp hu] at hx
  exact lt_irrefl _ hx

theorem residue_p (hv : v.Integers R) [IsLocalRing R] (hp1 : v (algebraMap R C (p : R)) < 1) :
    ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
  rw [← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact mem_max_of_lt hv hp1

theorem residue_uR (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by
  have h := D.u_cong j y
  rw [← uR_spec hv D j y, ← map_sub] at h
  have hm := mem_max_of_lt hv h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
  rw [hm, lam]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_natCast, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xc, ZMod.castHom_apply, ZMod.natCast_val]

theorem isUnit_det_MuR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1)
    (D : Lifts H U X) : IsUnit (MuR hv D).det := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1 := fun x hx =>
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)
  letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hu
    have h2 : v (algebraMap R C (a + b)) < 1 := by
      rw [map_add (f := _)]; exact v.map_add_lt (hlt a ha) (hlt b hb)
    rw [h1] at h2
    exact lt_irrefl _ h2
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) =
      Matrix.of fun (x α : Nb p g) => monF (p := p) (D.Λ.map (IsLocalRing.residue R)) α x := by
    ext y α
    simp [MuR, monF, residue_uR hv D]
  rw [hM]
  refine det_monF_ne_zero _ ?_
  rw [det_map']
  exact D.Λ_det.map _

theorem valM_eq (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by
  ext y α
  simp only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply,
    map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]
  ring

theorem det_valM_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X) :
    (valM D).det ≠ 0 := by
  rw [valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]
  refine mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_
  refine Finset.prod_ne_zero_iff.mpr fun α _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [map_pow]
  exact pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))

end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

namespace ReciprocityTheory.PGsh.Up

theorem liftMonomialDeterminantStatement_holds : LiftMonomialDeterminantStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D
  exact FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EigenLiftsFrobenius
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobA

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

private theorem hasLen_of_linearEquiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {x : NNReal} (e : M ≃ₗ[R] M') (h : HasLen v R M' x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨φ⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans φ⟩, hx⟩

lemma coefX_int (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

lemma xL_pow_mem (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩

def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl

end FrobA

theorem frob_of (h1 : LiftMonomialDeterminantStatement) (h2 : FrobeniusBlockStatement) (h3 : FrobeniusLengthBoundStatement) :
    EigenLiftsFrobeniusStatement := by
  unfold EigenLiftsFrobeniusStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i
  have hv := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdet := h1 p g C v R O σ cp hS H U X D
  obtain ⟨h2a, h2b⟩ := h2 p g C v R O σ cp hp2 hS H U X D
  have hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact H.AA.mul_mem _ _ hf.1 hf'.1
  have hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) :=
    fun j => xL_pow_mem D hp j
  have hrex : ∀ j : Ix g, ∃ r : Nb p g → R,
      coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r :=
    fun j => coefX_int D hdet hbasis (hsq (hfS j))
  choose r hr using hrex
  let c : Ix g → Ix g → R := fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0
  have hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k := by
    intro j hj k
    by_cases hk : D.κ k = U.φ i
    · simp only [c, if_pos hk, linX, hr j, Function.comp_apply]
    · simp only [c, if_neg hk, map_zero]
      exact (h2a j k (by rw [hj]; exact hk)).symm
  have hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]
  let e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i} := Fintype.equivOfCardEq hcard
  let eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i}) := Fintype.equivFin _
  let σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i} := eτ.symm.trans e''.symm
  let Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R :=
    fun a b => c (σE b).1 (eτ.symm a).1
  let Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R) :=
    (blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)
  let N : Submodule R (Ix g → R) :=
    ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype
  have hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap :=
    Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _
  have hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin :=
    Submodule.map_comap_eq_of_surjective Ψ.surjective _
  have hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype)
      (v (algebraMap R C Y.det)) := by
    rw [hcomap]
    exact hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)
  have hNle : N ≤ blockL D (U.φ i) := Submodule.map_subtype_le _ _
  have hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier),
      ∀ k, algebraMap R C (x k) = linX D f k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
    refine ⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩
    intro k
    have hyΨ : y = Ψ.symm (Y.mulVecLin w) := by rw [hw]; exact (Ψ.symm_apply_apply y).symm
    have hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b := by
      rw [hyΨ]
      by_cases h : D.κ k = U.φ i
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_left h]
        show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _
        simp only [Y, Equiv.symm_apply_apply]
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dite_eq_right h]
        simp [c, h]
    show algebraMap R C ((y : Ix g → R) k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hyk, map_sum]
    simp only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_comm]
    congr 1
    exact hc (σE b).1 (σE b).2 k
  have hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i) := by
    rw [RingHom.map_det]
    have hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE := by
      ext a b
      show algebraMap R C (c (σE b).1 (eτ.symm a).1) =
        linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1
      rw [hc (σE b).1 (σE b).2]
      simp [σE]
    rw [hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact h2b i e''
  have hz := h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen
  rw [hYdet] at hz
  have hXne : X (U.φ i) ≠ 0 := by
    rw [← D.ε_prod (U.φ i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))
  rw [div_le_iff₀ (pos_iff_ne_zero.mpr hXne)] at hz
  exact hz.trans_eq (mul_comm _ _)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.AinfTower
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev R0 (ε : PreTilt O p) := A p O ⧸ span {xi p O ε ^ 2}

abbrev Rn (n : ℕ) := O ⧸ span {(p : O) ^ (n + 1)}

abbrev R'n (ε : PreTilt O p) (n : ℕ) := R0 p O ε ⧸ span {(p : R0 p O ε) ^ (n + 1)}

lemma hpRn (n : ℕ) : (p : Rn p O n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma hpR' (ε : PreTilt O p) (n : ℕ) : (p : R'n p O ε n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

lemma Rn_local (hv : v.Integers O) (n : ℕ) : IsLocalRing (Rn p O n) := by
  haveI := O_local O hv
  haveI : Nontrivial (Rn p O n) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : O) ∈ span {(p : O) ^ (n + 1)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    exact (Fact.out : ¬IsUnit (p : O))
      ((isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.of_mul_eq_one_right a ha))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma one_add_unit {S : Type} [CommRing S] (a b : S) (hb : b * b = 0) : IsUnit (1 + a * b) := by
  exact IsUnit.of_mul_eq_one (1 - a * b) (by linear_combination (-a ^ 2) * hb)

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

def thetaBar : R0 p O ε →+* O :=
  Ideal.Quotient.lift _ (fontaineTheta O p) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, theta_xi p O hv ε hε, zero_pow two_ne_zero, mul_zero])

def algO : Algebra (R0 p O ε) O := (thetaBar p O hv ε hε).toAlgebra

def algRn (n : ℕ) : Algebra (R0 p O ε) (Rn p O n) :=
  ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp (thetaBar p O hv ε hε)).toAlgebra

def piRing (n : ℕ) : R'n p O ε n →+* Rn p O n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp
    (thetaBar p O hv ε hε)) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast, hpRn, mul_zero])

lemma piRing_mk (n : ℕ) (a : A p O) :
    piRing p O hv ε hε n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl

lemma piRing_surj (n : ℕ) : Function.Surjective (piRing p O hv ε hε n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := theta_surj p O hv x
  exact ⟨_, piRing_mk p O hv ε hε n a⟩

def xiR (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)}) (Ideal.Quotient.mk (span {xi p O ε ^ 2}) (xi p O ε))

lemma ker_pi (n : ℕ) : RingHom.ker (piRing p O hv ε hε n) = span {xiR p O ε n} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [piRing_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨o, ho⟩ := hx
    obtain ⟨b, rfl⟩ := theta_surj p O hv o
    have hk : a - b * (p : A p O) ^ (n + 1) ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, ho, sub_self]
    rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    have ha : a = c * xi p O ε + b * (p : A p O) ^ (n + 1) := by rw [hc]; ring
    rw [Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c), ?_⟩
    rw [ha]
    simp only [xiR, map_add (f := _), map_mul, map_pow, map_natCast, hpR', mul_zero, add_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, xiR, piRing_mk,
      theta_xi p O hv ε hε, map_zero]

lemma xi_sq' (n : ℕ) : xiR p O ε n * xiR p O ε n = 0 := by
  unfold xiR
  rw [← map_mul, ← map_mul]
  have h : (Ideal.Quotient.mk (span {xi p O ε ^ 2})) (xi p O ε * xi p O ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨1, by ring⟩)
  rw [h, map_zero]

lemma R'n_local (n : ℕ) : IsLocalRing (R'n p O ε n) := by
  haveI := Rn_local p O hv n
  haveI : Nontrivial (R'n p O ε n) := (piRing p O hv ε hε n).domain_nontrivial
  have key : ∀ a : R'n p O ε n, IsUnit (piRing p O hv ε hε n a) → IsUnit a := by
    intro a ha
    obtain ⟨u, hu⟩ := ha.exists_right_inv
    obtain ⟨u', rfl⟩ := piRing_surj p O hv ε hε n u
    have hk : a * u' - 1 ∈ RingHom.ker (piRing p O hv ε hε n) := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hu, map_one, sub_self]
    rw [ker_pi, Ideal.mem_span_singleton'] at hk
    obtain ⟨k, hk⟩ := hk
    have h1 : a * u' = 1 + k * xiR p O ε n := by rw [hk]; ring
    have h2 := one_add_unit k (xiR p O ε n) (xi_sq' p O hv ε hε n)
    rw [← h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  have h : piRing p O hv ε hε n a + piRing p O hv ε hε n (1 - a) = 1 := by
    change (piRing p O hv ε hε n) a + (piRing p O hv ε hε n) (1 - a) = 1
    rw [← (piRing p O hv ε hε n).map_add, add_sub_cancel, (piRing p O hv ε hε n).map_one]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key _ h)

lemma ann' (n : ℕ) (a : R'n p O ε n) (ha : a * xiR p O ε n = 0) :
    a ∈ span {xiR p O ε n} := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  unfold xiR at ha
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨d0, hd0⟩ := ha
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d0
  rw [← map_natCast (Ideal.Quotient.mk (span {xi p O ε ^ 2})) p, ← map_pow, ← map_mul,
    Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd0
  obtain ⟨c, hc⟩ := hd0
  have h1 : fontaineTheta O p d * (p : O) ^ (n + 1) = 0 := by
    have h' := congrArg (fontaineTheta O p) hc
    simp only [map_mul, map_sub, map_pow, map_natCast, theta_xi p O hv ε hε] at h'
    linear_combination -h'
  have h2 : fontaineTheta O p d = 0 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hp0)
  have h3 : d ∈ RingHom.ker (fontaineTheta O p) := h2
  rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at h3
  obtain ⟨e0, rfl⟩ := h3
  have h4 : (y - (e0 * (p : A p O) ^ (n + 1) - c * xi p O ε)) * xi p O ε = 0 := by
    linear_combination hc
  have h5 := xi_nzd p O hv ε hε _ h4
  rw [sub_eq_zero] at h5
  rw [h5, Ideal.mem_span_singleton']
  refine ⟨-(Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c)), ?_⟩
  simp only [xiR, RingHom.map_sub, map_mul, map_pow, map_natCast, hpR', mul_zero, zero_sub, neg_mul]

def zv (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (teichmuller p (root p O ε (n + 1))))

def nuR (n : ℕ) : R'n p O ε n := Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (nu p O ε))

lemma zv_pow (n : ℕ) :
    zv p O ε n ^ p ^ (n + 1) = 1 + nuR p O ε n * xiR p O ε n := by
  unfold zv nuR xiR
  rw [← map_pow, ← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add (f := _), map_add (f := _), map_one,
    map_one, map_mul, map_mul]

lemma zv_unit (n : ℕ) : IsUnit (zv p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  refine (isUnit_pow_iff hne).1 ?_
  rw [zv_pow p O hv ε hε n]
  exact one_add_unit _ _ (xi_sq' p O hv ε hε n)

def zetaV (n : ℕ) : O := fontaineTheta O p (teichmuller p (root p O ε (n + 1)))

lemma zeta_unit (n : ℕ) : IsUnit (zetaV p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    unfold zetaV
    rw [← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add (f := _), map_one, map_mul,
      theta_xi p O hv ε hε, mul_zero, add_zero]
  refine IsUnit.of_mul_eq_one (zetaV p O ε n ^ (p ^ (n + 1) - 1)) ?_
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne), h]

def LO : LAlg (R0 p O ε) := { carrier := O, alg := algO p O hv ε hε, loc := O_local O hv }

def LR (n : ℕ) : LAlg (R0 p O ε) :=
  { carrier := Rn p O n, alg := algRn p O hv ε hε n, loc := Rn_local p O hv n }

def LR' (n : ℕ) : LAlg (R0 p O ε) := { carrier := R'n p O ε n, loc := R'n_local p O hv ε hε n }

lemma q_surj (n : ℕ) : Function.Surjective (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) := by
  exact Ideal.Quotient.mk_surjective

def ainfTower : ATower (R0 p O ε) p where
  O := LO p O hv ε hε
  R' n := LR' p O hv ε hε n
  R n := LR p O hv ε hε n
  π n := ⟨{ toRingHom := piRing p O hv ε hε n, commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (piRing_surj p O hv ε hε n)⟩
  q n := ⟨{ toRingHom := Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}), commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (q_surj p O hv ε hε n)⟩
  ξ n := xiR p O ε n
  surj n := piRing_surj p O hv ε hε n
  ker_eq n := ker_pi p O hv ε hε n
  ξ_sq n := xi_sq' p O hv ε hε n
  ann n a ha := ann' p O hv ε hε n a ha
  char n := by rw [Nat.cast_pow]; exact hpR' p O ε n
  sep a ha := sepO p O a fun n =>
    (Ideal.Quotient.eq_zero_iff_mem (I := span {(p : O) ^ (n + 1)})).1 (ha n)
  c := fontaineTheta O p (nu p O ε)
  cp n := nuR p O ε n
  cp_spec n := rfl
  zh n := (zv_unit p O hv ε hε n).unit
  zh_pow n := by rw [IsUnit.unit_spec]; exact zv_pow p O hv ε hε n
  ζ n := (zeta_unit p O hv ε hε n).unit
  ζ_spec n := by rw [IsUnit.unit_spec, IsUnit.unit_spec]; rfl

theorem ainfTower_isDomain : IsDomain ((ainfTower p O hv ε hε).O : Type) := by
  show IsDomain O
  exact Function.Injective.isDomain (algebraMap O C) hv.hom_inj

end Ainf

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.ExistsReductionOfCoordinateCombination
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y

lemma red_mulVec (H : HodgeTateDatum p g v R O σ cp) (a : O) (t : TT p g) :
    red p g (H.ρ a *ᵥ t) = nbAct H a (red p g t) := by
  funext i
  exact RingHom.map_mulVec PadicInt.toZMod (H.ρ a) t i

lemma red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma comp_mem (H : HodgeTateDatum p g v R O σ cp) (a : O) {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    (fun y => f (nbAct H a y)) ∈ H.AA.carrier := by
  obtain ⟨f', hf', hf'e⟩ := H.h3 a f hf
  have hfun : (fun y => f (nbAct H a y)) = f' := by
    funext y
    obtain ⟨t, rfl⟩ := red_surj y
    rw [hf'e, red_mulVec]
  rw [hfun]
  exact hf'

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

end Lift

end ReciprocityTheory.PGsh.Up
end
end
