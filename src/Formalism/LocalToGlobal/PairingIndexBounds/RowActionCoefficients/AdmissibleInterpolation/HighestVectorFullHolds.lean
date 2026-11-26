module

public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.CoefProd
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.EvalIdFrameRowAct
public import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.InterpolationHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.UnitColsZero
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

def UnitCols : Prop :=
  ∀ (n l : ℕ), l ≤ n → ∀ I : Fin (n - l) → Fin n, Function.Injective I →
    ∃ (J : Fin l → Fin n) (ε : ℤ), Function.Injective J ∧ (∀ i q, J i ≠ I q) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ (A : Type) [CommRing A] (z : Fin n → ℕ → A),
        (catM l (unitM A I) z).det = (ε : A) * (Matrix.of fun i i' : Fin l => z (J i') i.val).det

def MinorZero : Prop :=
  ∀ (A : Type) [CommRing A] (r n s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r), ¬ Function.Injective I → initMinor A I hs = 0

def HvFull : Prop :=
  ∀ (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c e : ℕ, (∀ t, μ t ≤ c) → (∀ t, e ≤ μ t) →
    (∀ t : Fin n, t.val + 1 = n → μ t = e) → 0 < n →
    ∀ (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A),
      hvE x y c (fun k => colH μ k.val) (fun k => colH_le μ k.val) =
        ((Matrix.of fun a i : Fin n => x a i.val).det * y.det) ^ e *
          hvE x y c (fun k => colH (fun t => μ t - e) k.val) (fun k => colH_le _ k.val)

def HvMemE : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ c : ℕ, (∀ t, ν t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvE (fun a i => C (x a i)) (yV K n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val) ∈ dualWeyl K n n ν

def HvMemO : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (μ : Fin n → ℕ), Antitone μ → ∀ c : ℕ, (∀ t, μ t ≤ c) → ∀ x : Fin n → ℕ → K,
    hvO (fun a i => C (x a i)) (yV K n) c (fun k => colH μ k.val) ∈ dualWeyl K n n fun t => c - μ t.rev

end Formalism.L2.PairingIndexBounds.Ent
end
end

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

namespace UnitColumnMinors

theorem minor_zero (A : Type) [CommRing A] (r n s : ℕ) (hs : s ≤ n) (I : Fin s → Fin r)
    (hI : ¬ Function.Injective I) : initMinor A I hs = 0 := by
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨a, b, hab, hne⟩ := hI
  unfold initMinor
  exact Matrix.det_zero_of_row_eq hne (by funext q; simp only [Matrix.of_apply, hab])

open Classical in
theorem unit_cols (n l : ℕ) (hl : l ≤ n) (I : Fin (n - l) → Fin n) (hI : Function.Injective I) :
    ∃ (J : Fin l → Fin n) (ε : ℤ), Function.Injective J ∧ (∀ i q, J i ≠ I q) ∧ (ε = 1 ∨ ε = -1) ∧
      ∀ (A : Type) [CommRing A] (z : Fin n → ℕ → A),
        (catM l (unitM A I) z).det = (ε : A) * (Matrix.of fun i i' : Fin l => z (J i') i.val).det := by
  have hm : n - l ≤ n := Nat.sub_le n l
  let e0 : {a : Fin n // a.val < n - l} ≃ {b : Fin n // b ∈ Set.range I} :=
    Equiv.ofBijective (fun a => ⟨I ⟨a.1.val, a.2⟩, ⟨_, rfl⟩⟩)
      ⟨fun a b h => by
        have := hI (congrArg Subtype.val h)
        exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val this)),
       fun b => by
        obtain ⟨b, ⟨q, rfl⟩⟩ := b
        exact ⟨⟨Fin.castLE hm q, q.isLt⟩, rfl⟩⟩
  let π : Equiv.Perm (Fin n) := e0.extendSubtype
  have hπ : ∀ q : Fin (n - l), π (Fin.castLE hm q) = I q := fun q =>
    e0.extendSubtype_apply_of_mem (Fin.castLE hm q) q.isLt
  let J : Fin l → Fin n := fun i => π ⟨n - l + i.val, by have := i.isLt; omega⟩
  refine ⟨J, ((Equiv.Perm.sign π : ℤˣ) : ℤ), ?_, ?_, ?_, ?_⟩
  · intro i i' h
    have h1 := Fin.mk.inj (π.injective h)
    exact Fin.ext (by omega)
  · intro i q h
    have h1 : J i = π (Fin.castLE hm q) := by rw [hπ]; exact h
    have h2 := congrArg Fin.val (π.injective h1)
    simp only [Fin.val_castLE] at h2
    have := q.isLt
    omega
  · rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  · intro A _ z
    have key : (catM l (unitM A I) z).submatrix π id =
        catM l ((1 : A) • (1 : Matrix (Fin n) (Fin n) A)) (fun a i => z (π a) i) := by
      ext a t
      simp only [Matrix.submatrix_apply, id, catM]
      split_ifs with ht
      · simp only [unitM, dif_pos ht, one_smul, Matrix.one_apply]
        rw [← hπ ⟨t.val, ht⟩]
        have : Fin.castLE hm ⟨t.val, ht⟩ = t := Fin.ext rfl
        simp only [Equiv.apply_eq_iff_eq, this]
      · rfl
    have h1 := Matrix.det_permute π (catM l (unitM A I) z)
    rw [key, det_catM_smul_one l hl, one_pow, one_mul] at h1
    have h2 : (Matrix.of fun i i' : Fin l => z (J i') i.val).det = lastMinor l hl (fun a i => z (π a) i) := by
      unfold lastMinor
      rw [← Matrix.det_transpose]
      rfl
    have hs : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : A) * (((Equiv.Perm.sign π : ℤˣ) : ℤ) : A) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    rw [h2, h1, ← mul_assoc, hs, one_mul]

theorem hv_full (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (c e : ℕ) (hc : ∀ t, μ t ≤ c)
    (he : ∀ t, e ≤ μ t) (hl : ∀ t : Fin n, t.val + 1 = n → μ t = e) (hn : 0 < n) (x : Fin n → ℕ → A)
    (y : Matrix (Fin n) (Fin n) A) :
    hvE x y c (fun k => colH μ k.val) (fun k => colH_le μ k.val) =
      ((Matrix.of fun a i : Fin n => x a i.val).det * y.det) ^ e *
        hvE x y c (fun k => colH (fun t => μ t - e) k.val) (fun k => colH_le _ k.val) := by
  let F : ℕ → A := fun m =>
    if h : m ≤ n then (Matrix.of fun i t : Fin m => ∑ a, x a i.val * y a (Fin.castLE h t)).det else 1
  have hF : F 0 = 1 := by
    simp only [F, Nat.zero_le, dif_pos]
    exact Matrix.det_isEmpty
  have hE : ∀ ν : Fin n → ℕ, hvE x y c (fun k => colH ν k.val) (fun k => colH_le ν k.val) =
      ∏ k : Fin c, F (colH ν k.val) := by
    intro ν
    unfold hvE
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [F, dif_pos (colH_le ν k.val)]
  have hμ' : Antitone fun t => μ t - e := fun a b h => by
    have := hμ h
    simp only
    omega
  have hc' : ∀ t, μ t - e ≤ c := fun t => (Nat.sub_le _ _).trans (hc t)
  rw [hE, hE, BidetPairing.prod_colH hμ c hc F hF, BidetPairing.prod_colH hμ' c hc' F hF]
  have hFn : F n = (Matrix.of fun a i : Fin n => x a i.val).det * y.det := by
    simp only [F]
    rw [dif_pos le_rfl, ← Matrix.det_transpose (Matrix.of fun a i : Fin n => x a i.val), ← Matrix.det_mul]
    congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hlast : μ (Fin.last m) = e := hl _ (by simp)
  have hn1 : ∀ ν : Fin (m + 1) → ℕ, nuNext ν (Fin.last m) = 0 := fun ν => by
    unfold nuNext
    simp
  have hn2 : ∀ (ν : Fin (m + 1) → ℕ) (i : Fin m), nuNext ν i.castSucc = ν i.succ := fun ν i => by
    unfold nuNext
    rw [dif_pos (by simp)]
    rfl
  have hexp : ∀ i : Fin m, (μ i.castSucc - e) - (μ i.succ - e) = μ i.castSucc - μ i.succ := fun i => by
    have := he i.castSucc
    have := he i.succ
    omega
  simp only [hn1, hn2, hexp, hlast, Nat.sub_zero, Nat.sub_self, pow_zero, mul_one, Fin.val_last]
  rw [hFn]
  ring

theorem mem_dualWeyl_of_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    {r n : ℕ} {ν : Fin n → ℕ} (f : MvPolynomial (Fin r × Fin n) R) (h : map φ f ∈ dualWeyl S r n ν) :
    f ∈ dualWeyl R r n ν := by
  rw [lsat_mem_dualWeyl] at h ⊢
  obtain ⟨hh, hk⟩ := h
  refine ⟨?_, ?_⟩
  · intro d hd
    apply hh
    rw [coeff_map]
    exact (map_ne_zero_iff φ hφ).2 hd
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [lsat_map_colAddGen, hk l j hlj, map_rename]

end UnitColumnMinors

open UnitColumnMinors

theorem minor_zero_holds : MinorZero := fun A _ r n s hs I hI => minor_zero A r n s hs I hI

theorem unit_columns_holds : UnitCols := fun n l hl I hI => unit_cols n l hl I hI

theorem highest_vector_full_holds : HvFull := fun A _ n μ hμ c e hc he hl hn x y => hv_full A n μ hμ c e hc he hl hn x y

theorem highest_vector_mem_even : HvMemE := by
  intro K _ _ n ν hν c hc x
  rw [BidetPairing.hvE_eq K n ν hν c hc x]
  exact dualWeylRowStable K n n ν _ _ (hwMem K n n le_rfl ν hν)

theorem highest_vector_mem_odd : HvMemO := by
  intro K _ _ n μ hμ c hc x
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K))) :=
    IsFractionRing.injective _ _

  let xg : Fin n → ℕ → MvPolynomial (Fin n × Fin n) K :=
    fun a i => if h : i < n then X (a, ⟨n - 1 - i, by omega⟩) else 0
  have hXg : (Matrix.of fun a t : Fin n => xg a (n - 1 - t.val)) = Matrix.mvPolynomialX (Fin n) (Fin n) K := by
    ext a t
    have := t.isLt
    simp only [Matrix.of_apply, xg, Matrix.mvPolynomialX_apply, dif_pos (show n - 1 - t.val < n by omega)]
    apply congrArg (fun p : Fin n × Fin n => (X p : MvPolynomial (Fin n × Fin n) K).coeff _)
    refine Prod.ext rfl (Fin.ext ?_)
    show n - 1 - (n - 1 - t.val) = t.val
    omega
  let XL : Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin n × Fin n) K)) :=
    Matrix.of fun a t : Fin n => algebraMap _ _ (xg a (n - 1 - t.val))
  have hdet : XL.det ≠ 0 := by
    have hXL : XL = (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
        (algebraMap (MvPolynomial (Fin n × Fin n) K) (FractionRing (MvPolynomial (Fin n × Fin n) K))) := by
      rw [← hXg]
      rfl
    rw [hXL, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h0
    exact Matrix.det_mvPolynomialX_ne_zero (Fin n) K (hι (by rw [h0, map_zero]))
  have hU : IsUnit XL.det := isUnit_iff_ne_zero.2 hdet
  have hgen : hvO (fun a i => C (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K)) (xg a i)))
        (yV (FractionRing (MvPolynomial (Fin n × Fin n) K)) n) c (fun k => colH μ k.val) ∈
      dualWeyl (FractionRing (MvPolynomial (Fin n × Fin n) K)) n n (fun t : Fin n => c - μ t.rev) := by
    rw [BidetPairing.hvO_eq_inv (FractionRing (MvPolynomial (Fin n × Fin n) K)) n μ hμ c hc
      (fun a i => algebraMap _ _ (xg a i)) XL⁻¹ (Matrix.nonsing_inv_mul XL hU) (Matrix.mul_nonsing_inv XL hU), C_mul']
    exact Submodule.smul_mem _ _
      (dualWeylRowStable _ n n _ _ _ (hwMem _ n n le_rfl _ (BidetPairing.kap_antitone hμ c)))
  rw [← BidetPairing.map_hvO' (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K))) xg c (fun k => colH μ k.val)] at hgen
  have hS := mem_dualWeyl_of_map _ hι _ hgen
  have hK := dualWeylMap (MvPolynomial (Fin n × Fin n) K) K (eval fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val))
    n n _ _ hS
  rw [BidetPairing.map_hvO'] at hK
  have hx : ∀ a i, i < n → (fun a i => C (x a i) : Fin n → ℕ → MvPolynomial (Fin n × Fin n) K) a i =
      (fun a i => C (eval (fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val)) (xg a i))) a i := by
    intro a i hi
    simp only [xg, dif_pos hi, eval_X]
    congr 2
    omega
  convert hK using 1
  unfold hvO
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [BidetPairing.catM_congr _ _ _ _ hx]

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.CoefficientProductHolds
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.L2.G.Model.TS

section disjointProducts

variable {R B σ τ : Type*} [CommRing R] [Fintype B]

def dGlue (em : B → σ → τ) (p : B → σ →₀ ℕ) : τ →₀ ℕ :=
  ∑ b, (p b).mapDomain (em b)

lemma dGlue_apply (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) (b : B) (s : σ) : dGlue em p (em b s) = p b s := by
  classical
  unfold dGlue
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply_of_injective (fun x y h => congrArg Prod.snd (hem (a₁ := (b, x)) (a₂ := (b, y)) h)) _ _
  · intro b' _ hb
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hb (congrArg Prod.fst (hem (a₁ := (b', w)) (a₂ := (b, s)) hw))
  · simp

lemma dGlue_injective (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2) :
    Function.Injective (dGlue em) := fun p q h =>
  funext fun b => Finsupp.ext fun s => by rw [← dGlue_apply em hem p, h, dGlue_apply em hem]

lemma dGlue_fact (em : B → σ → τ) (hem : Function.Injective fun x : B × σ => em x.1 x.2)
    (p : B → σ →₀ ℕ) :
    ∏ x ∈ (dGlue em p).support, (dGlue em p x).factorial = ∏ b, ∏ v ∈ (p b).support, (p b v).factorial := by
  classical
  have key : ∀ t : Finset B, (∑ b ∈ t, (p b).mapDomain (em b)).prod (fun _ k => k.factorial) =
      ∏ b ∈ t, (p b).prod (fun _ k => k.factorial) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      have hinj : Function.Injective (em a) := fun x y h =>
        congrArg Prod.snd (hem (a₁ := (a, x)) (a₂ := (a, y)) h)
      have hd : Disjoint ((p a).mapDomain (em a)).support (∑ b ∈ t, (p b).mapDomain (em b)).support := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finsupp.mem_support_iff] at hx1 hx2
        obtain ⟨s, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hx1
        apply hx2
        rw [Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun b hb => ?_
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨w, hw⟩
        have hba : b = a := congrArg Prod.fst (hem (a₁ := (b, w)) (a₂ := (a, s)) hw)
        exact ha (hba ▸ hb)
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finsupp.prod_add_index_of_disjoint hd, ih,
        Finsupp.prod_mapDomain_index_inj hinj]
  exact key Finset.univ

lemma rename_prod_expand [DecidableEq B] (em : B → σ → τ) (F : B → MvPolynomial σ R) :
    ∏ b, rename (em b) (F b) = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
      monomial (dGlue em p) (∏ b, AddMonoidAlgebra.coeff (F b) (p b)) := by
  calc ∏ b, rename (em b) (F b)
      = ∏ b, ∑ m ∈ (F b).support, rename (em b) (monomial m (AddMonoidAlgebra.coeff (F b) m)) := by
        refine Finset.prod_congr rfl fun b _ => ?_
        conv_lhs => rw [(F b).as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
    _ = ∑ p ∈ Fintype.piFinset (fun b => (F b).support),
          ∏ b, rename (em b) (monomial (p b) (AddMonoidAlgebra.coeff (F b) (p b))) := Finset.prod_univ_sum _ _
    _ = _ := Finset.sum_congr rfl fun p _ => by
        simp only [rename_monomial]
        exact prod_monomial_eq _ _ _

end disjointProducts

theorem fock_product_holds : FockProd := by
  intro K B σ τ _ _ em hem F G
  classical
  rw [rename_prod_expand em F, rename_prod_expand em G, fockR_sum_left]
  simp_rw [fockR_sum_right, fockR_expand (F _) (G _)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [fockR_monomial]
  by_cases h : p = q
  · subst h
    simp only [if_true, dGlue_fact em hem, Finset.prod_mul_distrib, Nat.cast_prod]
  · have h' : dGlue em p ≠ dGlue em q := fun e => h (dGlue_injective em hem e)
    rw [if_neg h']
    obtain ⟨s, hs⟩ := Function.ne_iff.mp h
    exact (Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)).symm

theorem coefficient_product_holds : CoefProd := by
  intro R B σ τ _ _ xm hxm H p
  classical
  rw [show (∑ b, (p b).mapDomain (xm b)) = dGlue xm p from rfl, rename_prod_expand xm H, coeff_sum]
  by_cases hp : p ∈ Fintype.piFinset fun b => (H b).support
  · rw [Finset.sum_eq_single p]
    · rw [coeff_monomial, if_pos rfl]
    · intro q _ hq
      rw [coeff_monomial, if_neg (fun e => hq (dGlue_injective xm hxm e))]
    · intro h; exact absurd hp h
  · rw [Finset.sum_eq_zero]
    · rw [Fintype.mem_piFinset] at hp
      push Not at hp
      obtain ⟨b, hb⟩ := hp
      exact (Finset.prod_eq_zero (Finset.mem_univ b) (notMem_support_iff.mp hb)).symm
    · intro q hq
      rw [coeff_monomial, if_neg]
      intro e
      exact hp (dGlue_injective xm hxm e ▸ hq)

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.ShapeEvenHolds
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS

namespace ConjugatePartitionShape

section Heights

variable {n : ℕ} {ν : Fin n → ℕ}

theorem colH_ge (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : k < ν t) : t.val + 1 ≤ colH ν k := by
  unfold colH
  rw [← Fin.card_Iic t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_Iic] at hs
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, lt_of_lt_of_le h (hν hs)⟩

theorem colH_le_of (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : ν t ≤ k) : colH ν k ≤ t.val := by
  unfold colH
  rw [← Fin.card_Iio t]
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs
  rw [Finset.mem_Iio]
  by_contra hst
  push_neg at hst
  exact absurd (lt_of_lt_of_le hs.2 (hν hst)) (not_lt.mpr h)

theorem lt_colH_iff (hν : Antitone ν) (k : ℕ) (t : Fin n) : t.val < colH ν k ↔ k < ν t := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    exact absurd (colH_le_of hν t h') (not_le.mpr h)
  · intro h
    exact Nat.lt_of_succ_le (colH_ge hν t h)

end Heights

theorem card_fin_lt (c m : ℕ) (hm : m ≤ c) : (Finset.univ.filter fun k : Fin c => k.val < m).card = m := by
  have e : (Finset.univ.filter fun k : Fin c => k.val < m).map Fin.valEmbedding = Finset.range m := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, Finset.card_range]

theorem kap_antitone {n : ℕ} {μ : Fin n → ℕ} (hμ : Antitone μ) (c : ℕ) : Antitone fun t : Fin n => c - μ t.rev := by
  intro s t hst
  exact Nat.sub_le_sub_left (hμ (Fin.rev_le_rev.mpr hst)) c

theorem colH_kap {n : ℕ} {μ : Fin n → ℕ} (c : ℕ) (hc : ∀ t, μ t ≤ c) (k : Fin c) :
    n - colH μ k.val = colH (fun t : Fin n => c - μ t.rev) (Fin.rev k).val := by
  simp only [colH]
  have e1 : (Finset.univ.filter fun t : Fin n => (Fin.rev k).val < c - μ t.rev).card =
      (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s).card := by
    refine Finset.card_bij (fun t _ => t.rev) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev] at ht ⊢
      have := hc t.rev
      have := k.isLt
      omega
    · intro a _ b _ h
      exact Fin.rev_injective h
    · intro s hs
      refine ⟨s.rev, ?_, Fin.rev_rev s⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_rev, Fin.rev_rev] at hs ⊢
      have := hc s
      have := k.isLt
      omega
  have hsub : (Finset.univ.filter fun s : Fin n => k.val < μ s) ⊆ Finset.univ := Finset.subset_univ _
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun s : Fin n => ¬ k.val < μ s) =
      Finset.univ \ (Finset.univ.filter fun s : Fin n => k.val < μ s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h3] at e1
  omega

theorem card_ge_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    (Finset.univ.filter fun k => l ≤ sz k).card = (Finset.univ.filter fun k => l ≤ sz' k).card := by
  by_cases hln : l ≤ n
  · have e := congrFun h ⟨l - 1, by omega⟩
    simp only [shapeDeg] at e
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = (Finset.univ.filter fun k => l - 1 < sz k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = (Finset.univ.filter fun k => l - 1 < sz' k) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> intro <;> omega
    rw [e1, e2]
    exact e
  · push_neg at hln
    have e1 : (Finset.univ.filter fun k => l ≤ sz k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz k; omega
    have e2 : (Finset.univ.filter fun k => l ≤ sz' k) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun k _ => by have := hsz' k; omega
    rw [e1, e2, Finset.card_empty, Finset.card_empty]

theorem card_eq_sub {K : ℕ} (sz : Fin K → ℕ) (l : ℕ) :
    (Finset.univ.filter fun k => sz k = l).card =
      (Finset.univ.filter fun k => l ≤ sz k).card - (Finset.univ.filter fun k => l + 1 ≤ sz k).card := by
  have hsub : (Finset.univ.filter fun k => l + 1 ≤ sz k) ⊆ (Finset.univ.filter fun k => l ≤ sz k) := by
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 : (Finset.univ.filter fun k => sz k = l) =
      (Finset.univ.filter fun k => l ≤ sz k) \ (Finset.univ.filter fun k => l + 1 ≤ sz k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor <;> intro <;> omega
  rw [h3]
  omega

theorem card_eq_eq {n K K' : ℕ} (sz : Fin K → ℕ) (sz' : Fin K' → ℕ) (hsz : ∀ k, sz k ≤ n) (hsz' : ∀ k, sz' k ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg sz') (l : ℕ) (hl : 0 < l) :
    Fintype.card {k' // sz' k' = l} = Fintype.card {k // sz k = l} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, card_eq_sub, card_eq_sub,
    card_ge_eq sz sz' hsz hsz' h l hl, card_ge_eq sz sz' hsz hsz' h (l + 1) (Nat.succ_pos l)]

theorem initMinor_cast (B : Type) [CommRing B] {r n s s' : ℕ} (e : s = s') (J : Fin s → Fin r) (hs : s ≤ n)
    (hs' : s' ≤ n) : initMinor B (n := n) (fun j : Fin s' => J (Fin.cast e.symm j)) hs' = initMinor B J hs := by
  subst e
  rfl

theorem initMinor_zero (B : Type) [CommRing B] {r n : ℕ} (J : Fin 0 → Fin r) (hs : 0 ≤ n) :
    initMinor B (n := n) J hs = 1 := by
  rw [initMinor]
  exact Matrix.det_isEmpty

theorem initMinor_eq_one (B : Type) [CommRing B] {r n s : ℕ} (J : Fin s → Fin r) (hs : s ≤ n) (h0 : s = 0) :
    initMinor B (n := n) J hs = 1 := by
  subst h0
  exact initMinor_zero B J hs

end ConjugatePartitionShape

open ConjugatePartitionShape

theorem shape_even_holds : ShapeE := by
  intro n ν hν c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (ν t) (hc t)]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_colH_iff hν k.val t

theorem shape_odd_holds : ShapeO := by
  intro n μ hμ c hc
  funext t
  simp only [shapeDeg]
  rw [← card_fin_lt c (c - μ t.rev) (Nat.sub_le c _)]
  refine Finset.card_bij (fun k _ => Fin.rev k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) k] at hk
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mp hk
  · intro a _ b _ h
    exact Fin.rev_injective h
  · intro k hk
    refine ⟨Fin.rev k, ?_, Fin.rev_rev k⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [colH_kap c (fun s => hc s) (Fin.rev k), Fin.rev_rev]
    exact (lt_colH_iff (kap_antitone hμ c) _ t).mpr hk

theorem reorder_holds : Reorder := by
  intro B _ r n K K' sz sz' hsz hsz' h I
  classical
  have hE : ∀ l, 0 < l → Nonempty ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl =>
    ⟨Fintype.equivOfCardEq (card_eq_eq sz sz' hsz hsz' h l hl)⟩
  let e : ∀ l, 0 < l → ({k' // sz' k' = l} ≃ {k // sz k = l}) := fun l hl => Classical.choice (hE l hl)
  let I' : ∀ k', Fin (sz' k') → Fin r := fun k' =>
    if hk : 0 < sz' k' then
      fun j => I (e (sz' k') hk ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hk ⟨k', rfl⟩).2.symm j)
    else fun j => absurd j.2 (by omega)
  refine ⟨I', ?_⟩
  unfold bideterminant
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin K)), sz k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz k))
  have hmaps' : ∀ k ∈ (Finset.univ : Finset (Fin K')), sz' k ∈ Finset.range (n + 1) :=
    fun k _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz' k))
  rw [← Finset.prod_fiberwise_of_maps_to hmaps, ← Finset.prod_fiberwise_of_maps_to hmaps']
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rw [Finset.prod_eq_one, Finset.prod_eq_one]
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact initMinor_eq_one B _ _ hk
  · rw [Finset.prod_subtype _ (p := fun k => sz k = l) (by simp),
      Finset.prod_subtype _ (p := fun k' => sz' k' = l) (by simp)]
    symm
    refine Fintype.prod_equiv (e l hl) _ _ fun x' => ?_
    obtain ⟨k', hk'⟩ := x'
    subst hk'
    have hI : I' k' = fun j => I (e (sz' k') hl ⟨k', rfl⟩).1 (Fin.cast (e (sz' k') hl ⟨k', rfl⟩).2.symm j) :=
      dif_pos hl
    simp only
    rw [hI]
    exact initMinor_cast B (e (sz' k') hl ⟨k', rfl⟩).2 _ _ _

end Formalism.L2.PairingIndexBounds.Ent
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.FockRSmulLeft
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.MainNotions.G

def cN (K : Type) [CommRing K] {n : ℕ} (ν : Fin n → ℕ) : K := fockR (hw K le_rfl ν) (hw K le_rfl ν)

theorem cN_ne (K : Type) [Field K] [CharZero K] {n : ℕ} (ν : Fin n → ℕ) : cN K ν ≠ 0 := by
  obtain ⟨N, hN, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K]
  exact_mod_cast hN.ne'

theorem map_cN (K Kc : Type) [CommRing K] [CommRing Kc] (φ : K →+* Kc) {n : ℕ} (ν : Fin n → ℕ) : φ (cN K ν) = cN Kc ν := by
  obtain ⟨N, _, h⟩ := Top.hWNorm n n le_rfl ν
  unfold cN
  rw [h K, h Kc, map_natCast]

theorem fockR_add_left {σ R : Type} [CommRing R] (f f' g : MvPolynomial σ R) : fockR (f + f') g = fockR f g + fockR f' g :=
  (Top.fockRBilin σ R f f' g 0).1

theorem fockR_smul_left {σ R : Type} [CommRing R] (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g :=
  (Top.fockRBilin σ R f 0 g a).2.1

theorem fockR_comm {σ R : Type} [CommRing R] (f g : MvPolynomial σ R) : fockR f g = fockR g f :=
  (Top.fockRBilin σ R f 0 g 0).2.2

theorem fockR_zero_left {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : fockR 0 g = 0 := by
  have := fockR_smul_left (0 : R) (0 : MvPolynomial σ R) g
  rwa [zero_smul, zero_mul] at this

theorem fockR_sum_left {σ R ι : Type} [CommRing R] (s : Finset ι) (f : ι → MvPolynomial σ R) (g : MvPolynomial σ R) :
    fockR (∑ i ∈ s, f i) g = ∑ i ∈ s, fockR (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fockR_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fockR_add_left, ih]

def fockL {σ R : Type} [CommRing R] (g : MvPolynomial σ R) : MvPolynomial σ R →ₗ[R] R where
  toFun f := fockR f g
  map_add' f f' := fockR_add_left f f' g
  map_smul' a f := by rw [fockR_smul_left]; rfl

theorem rowAct_rowAct {R : Type} [CommRing R] {k n : ℕ} (g h : Matrix (Fin k) (Fin k) R) (F : MvPolynomial (Fin k × Fin n) R) :
    rowAct R g (rowAct R h F) = rowAct R (h * g) F :=
  congrArg (fun φ : MvPolynomial (Fin k × Fin n) R →ₐ[R] MvPolynomial (Fin k × Fin n) R => φ F) (rowActMul R k n g h)

theorem rowAct_one {R : Type} [CommRing R] {k n : ℕ} (F : MvPolynomial (Fin k × Fin n) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) F = F := by
  have : rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [this]; rfl

theorem mem_deltaL' {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} {ν : Fin n → ℕ} {g : Matrix (Fin n) (Fin n) K}
    {F : MvPolynomial (Fin n × Fin n) K} :
    F ∈ deltaL O K n ν g ↔ rowAct K g F ∈ (weyl O n n le_rfl ν).map (toK O K) := Iff.rfl

section Tgt

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)
  (ι : B → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
  (e e' : ∀ b, ι b → MvPolynomial (Fin n × Fin n) K)

def Ei (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (hi b) (e b (i b)))

def Ei' (i : ∀ b, ι b) : MvPolynomial τ K := ∏ b, rename (em b) (rowAct K (h b).transpose (e' b (i b)))

include hh in
theorem tgt1 (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b)))
    (F : B → MvPolynomial (Fin n × Fin n) K) (hF : ∀ b, F b ∈ dualWeyl K n n (ν b)) :
    ∏ b, rename (em b) (F b) ∈ Submodule.span K (Set.range (Ei em hi ι e)) := by
  have hh' : ∀ b, h b * hi b = 1 := fun b => mul_eq_one_comm.1 (hh b)
  refine prod_span (R := K) (fun b => Set.range fun i : ι b => rename (em b) (rowAct K (hi b) (e b i))) _ ?_ _ ?_
  · intro f hf
    choose i hi' using hf
    refine Submodule.subset_span ⟨i, ?_⟩
    exact Finset.prod_congr rfl fun b _ => hi' b
  · intro b
    have h2 : rowAct K (h b) (F b) ∈ Submodule.span K (Set.range (e b)) :=
      hsp b (dualWeylRowStable K n n (ν b) (h b) (F b) (hF b))
    have h3 : F b = rowAct K (hi b) (rowAct K (h b) (F b)) := by rw [rowAct_rowAct, hh' b, rowAct_one]
    rw [h3]
    have h4 := Submodule.mem_map_of_mem (f := ((rename (em b) : MvPolynomial (Fin n × Fin n) K →ₐ[K] MvPolynomial τ K).comp
      (rowAct K (hi b))).toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

theorem tgt2 {ι' : Type} (E : ι' → MvPolynomial τ K) (t : MvPolynomial τ K) (ht : t ∈ Submodule.span K (Set.range E)) :
    map (algebraMap K Kc) t ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (E i)) := by
  induction ht using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

include hem hh in
theorem tgt3 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (i k : ∀ b, ι b) : fockR (Ei em hi ι e i) (Ei' em h ι e' k) = if i = k then ∏ b, cN K (ν b) else 0 := by
  unfold Ei Ei'
  rw [hFP K B (Fin n × Fin n) τ em hem]
  have h4 : ∀ b, fockR (rowAct K (hi b) (e b (i b))) (rowAct K (h b).transpose (e' b (k b))) =
      if i b = k b then cN K (ν b) else 0 := by
    intro b
    rw [Top.fockRRowAct, rowAct_rowAct, ← Matrix.transpose_mul, hh b, Matrix.transpose_one, rowAct_one]
    exact hee b (i b) (k b)
  rw [Finset.prod_congr rfl fun b _ => h4 b]
  by_cases hik : i = k
  · subst hik; simp
  · rw [if_neg hik]
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hik
    exact Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)

include hem hh in
theorem tgt5 (hFP : FockProd)
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (a : (∀ b, ι b) → Kc) (k : ∀ b, ι b) :
    fockR (∑ i, a i • map (algebraMap K Kc) (Ei em hi ι e i)) (map (algebraMap K Kc) (Ei' em h ι e' k)) =
      a k * ∏ b, cN Kc (ν b) := by
  rw [fockR_sum_left, Finset.sum_eq_single k]
  · rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_pos rfl, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun b _ => map_cN K Kc _ _
  · intro i _ hik
    rw [fockR_smul_left, Top.fockRMap, tgt3 em hem ν h hi hh ι e e' hFP hee, if_neg hik, map_zero, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk


include hem hh in
theorem tgt_core (hFP : FockProd)
    (he : ∀ b i, e b i ∈ (weyl O n n le_rfl (ν b)).map (toK O K)) (he' : ∀ b i, e' b i ∈ (dualWeyl O n n (ν b)).map (toK O K))
    (hee : ∀ b i k, fockR (e b i) (e' b k) = if i = k then fockR (hw K le_rfl (ν b)) (hw K le_rfl (ν b)) else 0)
    (hsp : ∀ b, dualWeyl K n n (ν b) ≤ Submodule.span K (Set.range (e b))) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap K Kc).injective
  have h2 : y ∈ Submodule.span Kc (Set.range fun i => map (algebraMap K Kc) (Ei em hi ι e i)) := by
    refine (Submodule.span_le.2 ?_) hy
    rintro _ ⟨F, hF, rfl⟩
    exact tgt2 _ _ (tgt1 em ν h hi hh ι e hsp F hF)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Kc).1 h2
  have hc : (∏ b, cN Kc (ν b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => cN_ne Kc (ν b)
  have h6 : ∀ k, a k ∈ M := by
    intro k
    obtain ⟨a', ha', h7⟩ := hp (fun b => e' b (k b)) fun b => he' b (k b)
    have h5 := tgt5 (Kc := Kc) em hem ν h hi hh ι e e' hFP hee a k
    rw [ha] at h5
    have : a k = a' := mul_right_cancel₀ hc (h5.symm.trans h7)
    rw [this]; exact ha'
  rw [← ha]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  refine ⟨a i, h6 i, fun b => rowAct K (hi b) (e b (i b)), fun b => ?_, ?_⟩
  · rw [mem_deltaL', rowAct_rowAct, hh b, rowAct_one]
    exact he b (i b)
  · unfold Ei
    rfl

end Tgt

section Tgt'

variable {O K Kc : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [CharZero K] [Field Kc] [Algebra K Kc]
  {B τ : Type} [Fintype B] [DecidableEq B] {n : ℕ} (em : B → Fin n × Fin n → τ)
  (hem : Function.Injective fun x : B × (Fin n × Fin n) => em x.1 x.2)
  (ν : B → Fin n → ℕ) (hν : ∀ b, Antitone (ν b))
  (h hi : B → Matrix (Fin n) (Fin n) K) (hh : ∀ b, hi b * h b = 1)
  (M : AddSubgroup Kc)

include hem hν hh in
theorem tgt_abs (hDB : DualBases) (hFP : FockProd) (y : MvPolynomial τ Kc)
    (hy : y ∈ Submodule.span Kc {z | ∃ F : B → MvPolynomial (Fin n × Fin n) K, (∀ b, F b ∈ dualWeyl K n n (ν b)) ∧
      z = map (algebraMap K Kc) (∏ b, rename (em b) (F b))})
    (hp : ∀ Q : B → MvPolynomial (Fin n × Fin n) K, (∀ b, Q b ∈ (dualWeyl O n n (ν b)).map (toK O K)) →
      ∃ a ∈ M, fockR y (map (algebraMap K Kc) (∏ b, rename (em b) (rowAct K (h b).transpose (Q b)))) =
        a * ∏ b, cN Kc (ν b)) :
    y ∈ AddSubgroup.closure {z | ∃ a ∈ M, ∃ F : B → MvPolynomial (Fin n × Fin n) K,
      (∀ b, F b ∈ deltaL O K n (ν b) (h b)) ∧ z = a • map (algebraMap K Kc) (∏ b, rename (em b) (F b))} := by
  choose ι fι dι e e' he he' hee hsp using fun b => hDB O K n (ν b) (hν b)
  exact @tgt_core O K Kc _ _ _ _ _ _ _ _ _ B τ _ _ n em hem ν h hi hh M ι fι dι e e' hFP he he' hee hsp y hy hp

end Tgt'

end Formalism.L2.PairingIndexBounds.Ent
end
end
