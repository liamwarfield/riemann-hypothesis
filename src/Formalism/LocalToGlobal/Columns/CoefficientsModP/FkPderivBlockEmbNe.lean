module

public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
public import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Ten

variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}

omit [StarRing K] in
theorem fk_blockEmb_X (τ : ι) (v : Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockEmb K τ (X v) = (X (τ, v) : MvPolynomial (ι × Fin n × Fin n) K) := by
  simp [Formalism.GradedWeylDivisibility.blockEmb]

omit [StarRing K] in
theorem fk_blockEmb_C (τ : ι) (a : K) :
    Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ (C a) = (C a : MvPolynomial (ι × Fin n × Fin n) K) := by
  simp [Formalism.GradedWeylDivisibility.blockEmb]

omit [StarRing K] in
theorem fk_pderiv_blockEmb (τ : ι) (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ g) = Formalism.GradedWeylDivisibility.blockEmb K τ (pderiv v g) := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  exact pderiv_rename (fun a b hab => by simpa using hab) v g

omit [StarRing K] in
theorem fk_pderiv_blockEmb_ne {τ τ' : ι} (h : τ ≠ τ') (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ' g) = 0 := by
  classical
  unfold Formalism.GradedWeylDivisibility.blockEmb
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp => simp [Derivation.leibniz, hp, pderiv_X, Prod.ext_iff, Ne.symm h]

theorem fk_fock_right (τ : ι) (P Q : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (g : MvPolynomial (Fin n × Fin n) K) :
    fockL P (Formalism.GradedWeylDivisibility.blockEmb K τ g * Q) = constantCoeff g * fockL P Q := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => rw [fk_blockEmb_C, ← smul_eq_C_mul, map_smul, smul_eq_mul, constantCoeff_C]
  | add p q hp hq => rw [map_add (f := _), add_mul, map_add (f := _), hp, hq, map_add (f := _), add_mul]
  | mul_X p v _ =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, ← fockL_pderiv_X, hP, map_zero,
      LinearMap.zero_apply, map_mul constantCoeff, constantCoeff_X, mul_zero, zero_mul]

theorem fk_fock_mul (τ : ι) (P P' : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (hP' : ∀ v, pderiv (τ, v) P' = 0) (f g : MvPolynomial (Fin n × Fin n) K) :
    fockL (Formalism.GradedWeylDivisibility.blockEmb K τ f * P) (Formalism.GradedWeylDivisibility.blockEmb K τ g * P') = fockL f g * fockL P P' := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    rw [fk_blockEmb_C, ← smul_eq_C_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, fk_fock_right τ P P' hP,
      fockL_C_left, smul_eq_mul, starRingEnd_apply, mul_assoc]
  | add p q hp hq =>
    rw [map_add (f := _), add_mul, map_add (f := _), LinearMap.add_apply, hp, hq, map_add (f := _), LinearMap.add_apply, add_mul]
  | mul_X p v hp =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, fockL_X_pderiv, Derivation.leibniz, hP',
      smul_zero, zero_add, fk_pderiv_blockEmb, smul_eq_mul, mul_comm P', hp, mul_comm p, fockL_X_pderiv]

theorem fk_fock_prod (s : Finset ι) (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockL (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (g τ)) =
      ∏ τ ∈ s, fockL (f τ) (g τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← C_1, fockL_C_left]
    simp
  | insert τ s hτ ih =>
    have hz : ∀ (h : ι → MvPolynomial (Fin n × Fin n) K) (v : Fin n × Fin n),
        pderiv (τ, v) (∏ τ' ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ' (h τ')) = 0 := by
      intro h v
      refine Finset.prod_induction _ (fun P => pderiv (τ, v) P = 0) ?_ ?_ ?_
      · intro a b ha hb
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      · exact (pderiv (τ, v)).map_one_eq_zero
      · intro τ' hτ'
        exact fk_pderiv_blockEmb_ne (fun e : τ = τ' => hτ (by rw [e]; exact hτ')) v _
    rw [Finset.prod_insert hτ, Finset.prod_insert hτ, Finset.prod_insert hτ, fk_fock_mul τ _ _ (hz f) (hz g), ih]

end Ten

theorem fockSymTensor_holds : FockSTen := by
  intro K _ _ ι _ n f g
  exact fk_fock_prod Finset.univ f g

theorem pairingExtremal_holds : PairExtremal := pairExtremal_of fockSymTensor_holds extNormPos

section Rat

variable {K : Type} [Field K] (K0 : Subfield K)

theorem fk_coeff_mem {σ : Type} {P : MvPolynomial σ K} (hP : P ∈ (map (σ := σ) K0.subtype).range) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff P m ∈ K0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [MvPolynomial.coeff_map]
  exact (AddMonoidAlgebra.coeff Q m).2

theorem fk_int_mem {σ : Type} (P : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) P ∈ (map (σ := σ) K0.subtype).range := by
  refine ⟨map (Int.castRingHom K0) P, ?_⟩
  rw [MvPolynomial.map_map, RingHom.ext_int (K0.subtype.comp (Int.castRingHom K0)) (Int.castRingHom K)]

theorem fk_C_mem {σ : Type} {a : K} (ha : a ∈ K0) : (C a : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range :=
  ⟨C ⟨a, ha⟩, by simp⟩

theorem fk_X_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range :=
  ⟨X v, map_X _ _⟩

theorem fk_blockAct_mem {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K0)
    {P : MvPolynomial (ι × Fin n × Fin n) K} (hP : P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact fk_C_mem K0 a.2
  | add p q hp hq =>
    rw [map_add (map K0.subtype), map_add (f := _)]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (map K0.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (fk_C_mem K0 (hU _ _ _)) (fk_X_mem K0 _))

theorem fk_det_mem {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (hG : ∀ a b, G a b ∈ K0) : G.det ∈ K0 := by
  let G0 : Matrix (Fin n) (Fin n) K0 := fun a b => ⟨G a b, hG a b⟩
  have hG0 : G = G0.map K0.subtype := by
    ext a b
    rfl
  rw [hG0, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (G0.det).2

theorem fk_fock_mem [StarRing K] {σ : Type} (P : MvPolynomial σ ℤ) {Q : MvPolynomial σ K}
    (hQ : Q ∈ (map (σ := σ) K0.subtype).range) : fockS (map (Int.castRingHom K) P) Q ∈ K0 := by
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (fk_coeff_mem K0 hQ m)) (natCast_mem K0 _)
  rw [coeff_map, eq_intCast, star_intCast]
  exact intCast_mem K0 _

theorem fk_extNorm_mem [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : extNorm K lam ∈ K0 := by
  unfold extNorm
  refine prod_mem fun τ _ => ?_
  rw [← map_extremal (Int.castRingHom K)]
  exact fk_fock_mem K0 _ (fk_int_mem K0 _)

theorem fk_gramTw_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (hG : ∀ τ a b, G τ a b ∈ K0) : gramTw lam G ∈ K0 := by
  unfold gramTw
  exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hG τ)) _

theorem fk_descent {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v)
    (hv0 : ∀ i, v i ∈ (map (σ := σ) K0.subtype).range) (c : κ → K)
    (hx : ∑ i, c i • v i ∈ (map (σ := σ) K0.subtype).range) (i : κ) : c i ∈ K0 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K0 K)
    (LinearMap.ker_eq_bot.mpr (algebraMap K0 K).injective)
  have hπ' : ∀ a : K0, π (a : K) = a := fun a => congrArg (fun φ : K0 →ₗ[K0] K0 => φ a) hπ
  have hmul : ∀ (a : K0) (z : K), π (z * (a : K)) = π z * a := by
    intro a z
    have : z * (a : K) = a • z := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have key : ∑ i, (c i - (π (c i) : K)) • v i = 0 := by
    ext m
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : AddMonoidAlgebra.coeff (∑ i, c i • v i) m = ∑ i, c i * AddMonoidAlgebra.coeff (v i) m := by
      rw [coeff_sum]
      simp only [coeff_smul, smul_eq_mul]
    have h2 : ((π (AddMonoidAlgebra.coeff (∑ i, c i • v i) m) : K0) : K) = AddMonoidAlgebra.coeff (∑ i, c i • v i) m :=
      congrArg (fun a : K0 => (a : K)) (hπ' ⟨_, fk_coeff_mem K0 hx m⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, ← h2, h1, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hmul ⟨_, fk_coeff_mem K0 (hv0 i) m⟩ (c i)
    simp only at this
    rw [this]
    rfl
  have := (Fintype.linearIndependent_iff.mp hv) _ key i
  rw [sub_eq_zero] at this
  rw [this]
  exact (π (c i)).2

end Rat

theorem pairingRational_holds : PairRat := by
  intro K _ _ ι _ n lam K0 G hG i j
  obtain ⟨Pi, hPi⟩ := bVVfun_int K lam i
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  rw [pairK_apply, pairP_apply, bVV_coe, bVV_coe, fockL_apply, hPi, hPj]
  refine mul_mem (div_mem (fk_gramTw_mem K0 lam G hG) (fk_extNorm_mem K0 lam)) (fk_fock_mem K0 _ ?_)
  exact fk_blockAct_mem K0 _ (fun τ a b => hG τ b a) (fk_int_mem K0 _)

theorem actionRational_holds : ActRat := by
  intro K _ ι _ n lam K0 g hg i j
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  refine fk_descent K0 (bVVfun K lam) (bVVfun_spec K lam).1 (fun k => ?_)
    (fun k => (bVV K lam).repr (rhoK lam g (bVV K lam j)) k) ?_ i
  · obtain ⟨Pk, hPk⟩ := bVVfun_int K lam k
    rw [hPk]
    exact fk_int_mem K0 _
  · have h1 : ∑ k, (bVV K lam).repr (rhoK lam g (bVV K lam j)) k • bVVfun K lam k =
        actP lam g (bVVfun K lam j) := by
      have h := congrArg (fun x : VV K lam => (x : Pol K ι n)) ((bVV K lam).sum_repr (rhoK lam g (bVV K lam j)))
      simp only [rhoK_coe, bVV_coe, Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [h1, hPj, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul]
    refine mul_mem (fk_C_mem K0 ?_) (fk_blockAct_mem K0 _ (fun τ a b => hg τ b a) (fk_int_mem K0 _))
    rw [detTw_eq]
    exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hg τ)) _

end Formalism.L2.DIV
end
end

section -- merged from Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
open MvPolynomial

noncomputable section

namespace Formalism.L2.DIV

open Formalism.GradedWeylDivisibility

theorem we_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl

theorem we_applyWord_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact rowDivStable R r n ν _ _ _ _ ih

theorem we_fock_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := (fockQPos σ f g).1

theorem we_fock_add_left {σ : Type} (f f' g : MvPolynomial σ ℚ) : fockQ (f + f') g = fockQ f g + fockQ f' g :=
  (fockQBilin σ f f' g 0).1

theorem we_fock_smul_left {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ (c • f) g = c * fockQ f g :=
  (fockQBilin σ f 0 g c).2

theorem we_fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [we_fock_symm, we_fock_add_left, we_fock_symm g, we_fock_symm g']

theorem we_fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [we_fock_symm, we_fock_smul_left, we_fock_symm g]

theorem we_fock_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  have := we_fock_smul_right 0 f 0
  simpa using this

theorem we_hw_norm_ne {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : fockQ (hw ℚ hn ν) (hw ℚ hn ν) ≠ 0 :=
  ne_of_gt ((fockQPos _ (hw ℚ hn ν) (hw ℚ hn ν)).2 (hwNe ℚ r n hn ν))

theorem we_eval_idFrame_map {r n : ℕ} (G : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (MvPolynomial.map (Int.castRingHom ℚ) G) = ((eval (idFrame ℤ r n) G : ℤ) : ℚ) := by
  have h : idFrame ℚ r n = fun v => (Int.castRingHom ℚ) (idFrame ℤ r n v) := by
    funext v
    unfold idFrame
    split_ifs <;> simp
  rw [h, eval_map, ← eval₂_id]
  exact (eval₂_comp_left (Int.castRingHom ℚ) (RingHom.id ℤ) (idFrame ℤ r n) G).symm

theorem we_intQ_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ)) :
    intQ r n (applyWord ℤ w (hw ℤ hn ν)) = applyWord ℚ w (hw ℚ hn ν) := by
  rw [we_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]

theorem we_fock_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) (hP : P ∈ dualWeyl ℚ r n ν) :
    fockQ P (applyWord ℚ w (hw ℚ hn ν)) =
      eval (idFrame ℚ r n) (applyWord ℚ (transposeWord w) P) * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  rw [we_fock_symm, fock_space_word_adjoint r n w,
    fock_space_highest_weight r n hn ν hν _ (we_applyWord_mem ℚ r n ν _ P hP)]

theorem we_transposeWord_transposeWord {r : ℕ} (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (transposeWord w) = w := by
  unfold transposeWord
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  simp [Function.comp_def]

theorem nabla_eq_dual_weyl_holds : NablaEqDualWeyl := by
  intro r n hn ν hν
  ext P
  constructor
  · rintro ⟨P0, hP0, rfl⟩
    have hPQ : intQ r n P0 ∈ dualWeyl ℚ r n ν := dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν P0 hP0
    refine ⟨hPQ, ?_⟩
    rintro _ ⟨Q0, hQ0, rfl⟩
    replace hQ0 : Q0 ∈ weyl ℤ r n hn ν := hQ0
    unfold weyl at hQ0
    induction hQ0 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      refine ⟨eval (idFrame ℤ r n) (applyWord ℤ (transposeWord w) P0), ?_⟩
      simp only
      rw [we_intQ_word, we_fock_word hn ν hν w _ hPQ, we_intQ_apply, lclosedeq_applyWord_map, we_eval_idFrame_map]
    | zero => exact ⟨0, by rw [map_zero, we_fock_zero_right]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), we_fock_add_right, ha, hb]; push_cast; ring⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, we_fock_smul_right, ha]
      push_cast; ring
  · rintro ⟨hP, hdual⟩
    have hc := we_hw_norm_ne hn ν
    obtain ⟨Q', hQ'⟩ := Formalism.CohomologicalDescent.LR.lower_triangular_integral r n ν P hP (fun e he => by
      by_cases hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
      · have hhom : IsWeightedHomogeneous (colW r n) P ν := hP.1
        rw [Formalism.CohomologicalDescent.LR.coefficient_word ℚ r n ν P e hhom he hcol]
        obtain ⟨z, hz⟩ := hdual (intQ r n (applyWord ℤ (transposeWord (wordOf e)) (hw ℤ hn ν)))
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩))
        rw [we_intQ_word, we_fock_word hn ν hν _ P hP, we_transposeWord_transposeWord] at hz
        exact ⟨z, mul_right_cancel₀ hc hz⟩
      · refine ⟨0, ?_⟩
        rw [Int.cast_zero]
        by_contra h
        exact hcol (colSums ℚ r n ν P hP e (mem_support_iff.mpr h)))
    refine ⟨Q', (dualWeylIntRat r n ν Q').2 ?_, hQ'.symm⟩
    rw [← we_intQ_apply, ← hQ']
    exact hP

section Double

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def weForm : (dualWeyl ℚ r n ν) →ₗ⋆[ℚ] (dualWeyl ℚ r n ν) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℚ) (RingHom.id ℚ)
    (fun x y => fockQ x.1 y.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν))
    (by intro x x' y; simp only [Submodule.coe_add, we_fock_add_left, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul, mul_div_assoc])
    (by intro x y y'; simp only [Submodule.coe_add, we_fock_add_right, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_right, RingHom.id_apply, smul_eq_mul, mul_div_assoc])

theorem weForm_apply (x y : dualWeyl ℚ r n ν) :
    weForm hn ν x y = fockQ x.1 y.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν) := rfl

theorem we_form_symm : (weForm hn ν).IsSymm := by
  rw [LinearMap.isSymm_def]
  intro x y
  rw [weForm_apply, weForm_apply, starRingEnd_apply, star_trivial, we_fock_symm]

theorem we_form_self_eq_zero (x : dualWeyl ℚ r n ν) (h : weForm hn ν x x = 0) : x = 0 := by
  rw [weForm_apply, div_eq_zero_iff] at h
  have h1 := h.resolve_right (we_hw_norm_ne hn ν)
  by_contra hx
  have hx' : x.1 ≠ 0 := fun h0 => hx (Subtype.ext h0)
  exact ne_of_gt ((fockQPos _ x.1 x.1).2 hx') h1

theorem we_form_nondeg : (weForm hn ν).Nondegenerate :=
  ⟨fun x hx => we_form_self_eq_zero hn ν x (hx x), fun x hx => we_form_self_eq_zero hn ν x (hx x)⟩

theorem we_finiteDimensional (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  obtain ⟨b, hb, -⟩ := sSBasis ℚ r n ν
  have : Finite (ssIdx r n ν) := (sSIdxFinite r n ν).to_subtype
  rw [← hb.2.1]
  exact FiniteDimensional.span_of_finite ℚ (Set.finite_range b)

def weCut (r n : ℕ) (ν : Fin n → ℕ) (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (dualWeyl ℚ r n ν) :=
  S.comap ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)

theorem we_cut_inj {S S' : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)} (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν)
    (hS' : ∀ x ∈ S', x ∈ dualWeyl ℚ r n ν) (h : weCut r n ν S = weCut r n ν S') : S = S' := by
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hS x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S := hx
    rw [h] at h1
    exact h1
  · intro hx
    have h1 : (⟨x, hS' x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S' := hx
    rw [← h] at h1
    exact h1

theorem we_cut_bDual (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν) :
    weCut r n ν (bDual r n hn ν S) = Formalism.HermitianLatticesTheory.dual (weForm hn ν) (weCut r n ν S) := by
  have hc := we_hw_norm_ne hn ν
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.mem_one, weForm_apply]
  constructor
  · rintro ⟨-, h⟩ y hy
    obtain ⟨z, hz⟩ := h y.1 hy
    replace hz : fockQ x.1 y.1 = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    refine ⟨z, ?_⟩
    rw [we_fock_symm, hz, mul_div_assoc, div_self hc, mul_one]
    rfl
  · intro h
    refine ⟨x.2, fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := h ⟨Q, hS Q hQ⟩ hQ
    refine ⟨z, ?_⟩
    show fockQ x.1 Q = _
    rw [we_fock_symm]
    have hz' : (z : ℚ) = fockQ Q x.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    rw [hz', div_mul_cancel₀ _ hc]

theorem we_weyl_le (hν : Antitone ν) : ∀ x ∈ (weyl ℤ r n hn ν).map (intQ r n), x ∈ dualWeyl ℚ r n ν := by
  rintro _ ⟨f, hf, rfl⟩
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν f (weylLeDual ℤ r n hn ν hν hf)

theorem we_nabla_le : ∀ x ∈ (dualWeyl ℤ r n ν).map (intQ r n), x ∈ dualWeyl ℚ r n ν := by
  rintro _ ⟨f, hf, rfl⟩
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν f hf

theorem we_nabla_fg (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  obtain ⟨b, hb, -⟩ := sSBasis ℤ r n ν
  have : Finite (ssIdx r n ν) := (sSIdxFinite r n ν).to_subtype
  rw [← hb.2.1]
  exact Submodule.fg_span (Set.finite_range b)

theorem we_span_weyl (hν : Antitone ν) :
    Submodule.span ℚ (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) =
      dualWeyl ℚ r n ν := by
  rw [← weylEqNablaQ r n hn ν hν]
  unfold weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  exact we_intQ_word hn ν w

theorem we_weyl_lattice (hν : Antitone ν) :
    Submodule.IsFullLattice ℚ (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))) := by
  have himg : (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))).map
      ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ) = (weyl ℤ r n hn ν).map (intQ r n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, we_weyl_le hn ν hν x hx⟩, hx, rfl⟩
  refine { toIsLattice := Submodule.IsLattice.of_fg ℚ ?_, span_eq_top := ?_ }
  · refine Submodule.fg_of_fg_map_injective ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
      (dualWeyl ℚ r n ν).injective_subtype ?_
    rw [himg]
    exact (Submodule.FG.of_le (we_nabla_fg r n ν) (weylLeDual ℤ r n hn ν hν)).map _
  · apply Submodule.map_injective_of_injective (f := (dualWeyl ℚ r n ν).subtype)
      (dualWeyl ℚ r n ν).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span]
    have hspan := congrArg (fun S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ) =>
      Submodule.span ℚ (S : Set (MvPolynomial (Fin r × Fin n) ℚ))) himg
    exact hspan.trans (we_span_weyl hn ν hν)

end Double

theorem weyl_eq_dual_nabla_holds : WeylEqDualNabla := by
  intro r n hn ν hν
  have hfd := we_finiteDimensional r n ν
  have hdd := (Formalism.HermitianLatticesTheory.dualLattice ℤ ℚ (dualWeyl ℚ r n ν) (weForm hn ν) (we_form_symm hn ν) (we_form_nondeg hn ν)
    (fun z => ⟨z, by simp⟩) _ (we_weyl_lattice hn ν hν)).2.1
  refine we_cut_inj (ν := ν) (we_weyl_le hn ν hν) (fun x hx => hx.1) ?_
  rw [we_cut_bDual hn ν _ (we_nabla_le ν), nabla_eq_dual_weyl_holds r n hn ν hν,
    we_cut_bDual hn ν _ (we_weyl_le hn ν hν), hdd]

end Formalism.L2.DIV
end
end
