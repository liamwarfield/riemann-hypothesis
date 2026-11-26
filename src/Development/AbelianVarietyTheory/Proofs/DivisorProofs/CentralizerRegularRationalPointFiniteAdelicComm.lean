module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinCentComm

theorem commute_aeval {R : Type} [CommRing R] {r : ℕ} {m A : Matrix (Fin r) (Fin r) R}
    (h : Commute m A) (p : R[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

theorem aeval_mulVec_krylov {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R)
    (v c : Fin r → R) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem eq_aeval_of_cyclic {R : Type} [CommRing R] {r : ℕ} (A : Matrix (Fin r) (Fin r) R) (v : Fin r → R)
    (hKu : IsUnit (GlobalTheory.ClassParam.krylov A v).det) (n : Matrix (Fin r) (Fin r) R) (hn : Commute n A) :
    ∃ q : R[X], n = aeval A q := by
  set K := GlobalTheory.ClassParam.krylov A v with hK
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval (Commute.refl A) _).symm
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) R, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hn, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

theorem commute_of_commute_map_separable {E R : Type} [Field E] [CommRing R] (f : E →+* R) {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hA : A.charpoly.Separable) (X Y : Matrix (Fin r) (Fin r) R)
    (hX : X * A.map f = A.map f * X) (hY : Y * A.map f = A.map f * Y) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hA
  have hKu : IsUnit (GlobalTheory.ClassParam.krylov (A.map f) (f ∘ v)).det := by
    rw [← GlobalTheory.ClassParam.krylov_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (isUnit_iff_ne_zero.2 hv).map f
  obtain ⟨q, rfl⟩ := eq_aeval_of_cyclic (A.map f) (f ∘ v) hKu Y hY
  exact (commute_aeval (m := X) hX q).eq

end GlobalTheory.BCT.FinCentComm

namespace GlobalTheory.BCT.FinCentComm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_fst_eq_one (a : finU (E := E) (n := n)) : ((a : UA E n) : GA E n).val.map (FinPtLoc.fstA E) = 1 := by
  have ha : cInf (a : UA E n) = 1 := a.2
  ext i j
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => g.val i j) ha
  change (infEq E).symm (FinPtLoc.fstA E (((a : UA E n) : GA E n).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j at h
  rw [Matrix.map_apply]
  apply (infEq E).symm.injective
  rw [h]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem map_snd_finPt (γ : UE E n) :
    (((finPt γ : finU (E := E) (n := n)) : UA E n) : GA E n).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
  rw [FinPtLoc.finPt_eq]
  ext i j
  rw [Matrix.map_apply, FinPtLoc.snd_entry]
  rfl

end GlobalTheory.BCT.FinCentComm


open GlobalTheory.BCT.FinCentComm in
theorem GlobalTheory.BCT.finCent_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n),
    γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  intro E _ _ _ n γ hγ a ha b hb
  have key : ∀ c ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ),
      (((c : UA E n) : GA E n).val.map (pFin E)) * γ.1.val.map (algebraMap E (Af E)) =
        γ.1.val.map (algebraMap E (Af E)) * ((c : UA E n) : GA E n).val.map (pFin E) := by
    intro c hc
    have h : c * finPt γ = finPt γ * c := hc
    have h' := congrArg (fun z : finU (E := E) (n := n) => ((z : UA E n) : GA E n).val.map (pFin E)) h
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul] at h'
    rwa [map_snd_finPt] at h'
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  apply FinPtLoc.ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_eq_one a, map_fst_eq_one b]
  · rw [Matrix.map_mul, Matrix.map_mul]
    exact commute_of_commute_map_separable (algebraMap E (Af E)) γ.1.val hγ _ _ (key a ha) (key b hb)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicCommStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU (E := E) (n := n))) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.SignatureAddition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem coords_gram (B : HSpace E) (x y : B.V) :
    ∑ l, (∑ k, star (B.frame.repr x k) * B.gram k l) * B.frame.repr y l = B.hT x y := by
  conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

def middleSymmetricBasisVector (E : Type) [Field E] (c : ℕ) (p : Fin c) : Fin c → E :=
  Pi.single p (if 2 * p.1 + 1 ≤ c then 1 else -1 / 2) +
    Pi.single p.rev (if 2 * p.1 + 1 < c then 1 else if 2 * p.1 + 1 = c then 0 else 1 / 2)

theorem middleSymmetricBasisVectors_gram_antiDiagonal (c : ℕ) (neg : Bool) (p q : Fin c) :
    Examples₂.diagForm c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (middleSymmetricBasisVector E c p) (middleSymmetricBasisVector E c q) =
      antiDiagonalSignGramMatrix c (if neg then -1 else 1) p q := by
  have hp := p.2
  have hq := q.2
  obtain ⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2 := ⟨_, rfl⟩
  have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega
  have hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true) := by
    intro h; rw [hP]; cases neg <;> simp <;> omega
  rw [← hP]
  simp only [middleSymmetricBasisVector, map_add (f := _), LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply,
    GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]
  generalize p.1 = a at *
  generalize q.1 = b at *
  clear hP
  have e1 : (c - (a + 1) = c - (b + 1)) = (a = b) := propext (by omega)
  have e2 : (a = c - (b + 1)) = (a + b + 1 = c) := propext (by omega)
  have e3 : (c - (a + 1) = b) = (a + b + 1 = c) := propext (by omega)
  simp only [e1, e2, e3]
  by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c
  · subst h1
    have h : 2 * a + 1 = c := by omega
    simp only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]
    cases neg <;> simp
  · subst h1
    rcases (show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]
      simp
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]
      norm_num
  · rcases (show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega),
        if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]
      norm_num
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]
      norm_num
  · simp only [if_neg h1, if_neg h2, add_zero, mul_zero]

end Generic

theorem exists_hermitian_space_add_signature (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool) (hA : A.SigOK) (hs : ∀ τ, A.sig τ = (p, q)) :
    ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧
      ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by
    split_ifs <;> omega
  have hW := GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc
  set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2))
    (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd
  refine ⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩
  · refine
      { ι := LinearMap.inl _ _ _
        isom := GlobalTheory.Doubling.isIsomEmb_inl A W
        a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k
        gram := Matrix.ext fun i j => ?_
        perp := Matrix.ext fun i j => ?_
        rank := rfl }
    · refine Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_
      refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
      rw [map_zero, zero_add]
      exact middleSymmetricBasisVectors_gram_antiDiagonal c neg i j
    · refine Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)
      · have e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) =
            fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k :=
          Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i
        rw [e]
        rfl
      · refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
        rw [map_zero, map_zero, zero_add]
        rfl
  · show A.sig τ + W.sig τ = _
    rw [hs τ]
    rfl

end GlobalTheory.SignatureAddition

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_space_add_signature_exists : ∀ (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool), A.SigOK → (∀ τ, A.sig τ = (p, q)) → ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧ ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  first | exact @GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | exact GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | (intros; apply GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModel
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.SelfDualLat

theorem stdH_eq_dot (K : UQ) {n : ℕ} (a b : Fin n → K.E) :
    stdH K n a b = a ⬝ᵥ (fun k => K.c (b k)) := rfl

theorem stdH_mulVec (K : UQ) {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E)
    (hP : Pᵀ * P.map K.c = 1) (u v : Fin n → K.E) :
    stdH K n (P *ᵥ u) (P *ᵥ v) = stdH K n u v := by
  have hv : (fun k => K.c ((P *ᵥ v) k)) = P.map K.c *ᵥ (fun k => K.c (v k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) P v k
  rw [stdH_eq_dot, stdH_eq_dot, hv, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hP, vecMul_one]

theorem intVec_eq_range (K : UQ) (n : ℕ) :
    intVec K n = LinearMap.range ((Algebra.linearMap K.O K.E).compLeft (Fin n)) := by
  ext v
  constructor
  · intro hv
    have h := fun i => RingHom.mem_range.mp (hv i)
    choose o ho using h
    exact ⟨o, funext fun i => ho i⟩
  · rintro ⟨o, rfl⟩ i
    exact ⟨o i, rfl⟩

theorem intVec_fg (K : UQ) (n : ℕ) : (intVec K n).FG := by
  rw [intVec_eq_range, LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

theorem single_mem_intVec (K : UQ) {n : ℕ} (i : Fin n) : (Pi.single i (1 : K.E) : Fin n → K.E) ∈ intVec K n := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem unitLat_isLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hx hψ q
  set Qm : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  have hmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := by
    intro g hg
    simpa [UL, hns] using hg
  have hQ : cT (cj w) Qm * 1 * Qm = 1 := hmem _ (q⁻¹).2
  have h2 : (Qm.map (cj w))ᵀ * Qm = 1 := by simpa [cT] using hQ
  set P : Matrix (Fin n) (Fin n) K.E := Qm.map e.symm with hPdef
  have hPc : P.map K.c = (Qm.map (cj w)).map e.symm := by
    ext i j
    apply e.injective
    simp [hPdef, he]
  have hP1 : (P.map K.c)ᵀ * P = 1 := by
    have h3 := congrArg (e.symm.toRingHom.mapMatrix) h2
    simp only [map_mul, map_one, RingHom.mapMatrix_apply] at h3
    rw [hPc, hPdef, ← Matrix.transpose_map]
    simpa using h3
  have hPR : P * (P.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hP1
  have hPT : Pᵀ * P.map K.c = 1 := by
    have h4 := congrArg Matrix.transpose hP1
    simpa [Matrix.transpose_mul] using h4
  let G : (Fin n → K.E) →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' (P.map K.c)ᵀ
  have hGP : ∀ y, G (P *ᵥ ψ y) = y := by
    intro y
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hP1]
  have hPG : ∀ a, P *ᵥ ψ (G a) = a := by
    intro a
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hPR]
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ P *ᵥ ψ y ∈ intVec K n := fun y => Iff.rfl
  have hmap : unitLat e B ψ q = (intVec K n).map (G.restrictScalars K.O) := by
    ext y
    rw [hmemL]
    constructor
    · intro hy
      exact ⟨P *ᵥ ψ y, hy, hGP y⟩
    · rintro ⟨a, ha, rfl⟩
      rw [LinearMap.restrictScalars_apply, hPG]
      exact ha
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hmap]
    exact (intVec_fg K n).map _
  · apply top_unique
    intro y _
    rw [← hGP y, ← Finset.univ_sum_single (P *ᵥ ψ y), map_sum]
    apply Submodule.sum_mem
    intro i _
    have hi : G (Pi.single i (1 : K.E)) ∈ unitLat e B ψ q := by
      rw [hmemL, hPG]
      exact single_mem_intVec K i
    have hs : G (Pi.single i (1 : K.E)) ∈ Submodule.span K.E (unitLat e B ψ q : Set B.A) :=
      Submodule.subset_span hi
    have heq : Pi.single i ((P *ᵥ ψ y) i) = (P *ᵥ ψ y) i • Pi.single i (1 : K.E) := by
      ext j
      simp [Pi.single_apply]
    rw [heq, map_smul]
    exact Submodule.smul_mem _ _ hs
  · intro y
    rw [hmemL]
    constructor
    · intro hy z hz
      rw [hmemL] at hz
      rw [← hψ, ← stdH_mulVec K P hPT]
      unfold stdH
      apply Subring.sum_mem
      intro k _
      apply Subring.mul_mem _ (hy k)
      obtain ⟨o, ho⟩ := hz k
      obtain ⟨o', ho'⟩ := K.c_int o
      exact ⟨o', by rw [← ho, ho']⟩
    · intro h i
      have h5 := h (G (Pi.single i 1)) (by rw [hmemL, hPG]; exact single_mem_intVec K i)
      rw [← hψ, ← stdH_mulVec K P hPT, hPG] at h5
      simpa [stdH, Pi.single_apply, apply_ite] using h5

end GlobalTheory.InertUnitOrb.SelfDualLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModelStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | exact GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | (intros; apply GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFami
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFami
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.Cusp.SmoothParam

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]


omit [SecondCountableTopology G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem aestronglyMeasurable_out {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E]
    {Φ : G → E} (hΦ : Continuous Φ) (hinv : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (g : G)
    (μ : Measure (Quot (Γ.subgroupOf N))) :
    AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => Φ ((q.out : N) * g)) μ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hl : LeftInv (Γ.subgroupOf N) (fun n : N => Φ (n * g)) := fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _
  have hm : Measurable (fun n : N => Φ (n * g)) :=
    (hΦ.comp ((continuous_subtype_val).mul continuous_const)).measurable
  have hq : Measurable (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) := by
    refine measurable_from_quotient.2 ?_
    have e : (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) ∘ Quotient.mk'' = fun n : N => Φ (n * g) :=
      hl.lift_descend
    rw [e]; exact hm
  exact hq.aestronglyMeasurable


omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N] in
theorem exists_bound {T E : Type} [TopologicalSpace T] [NormedAddCommGroup E] (hc : Cocompact Γ N)
    {Ψ : G → T → E} (hΨ : Continuous fun p : G × T => Ψ p.1 p.2) (hinv : ∀ γ ∈ Γ, ∀ x t, Ψ (γ * x) t = Ψ x t)
    (g : G) {S : Set T} (hS : IsCompact S) : ∃ C, ∀ (n : N) t, t ∈ S → ‖Ψ (n * g) t‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn (f := fun p : N × T => Ψ (p.1 * g) p.2)
    (hΨ.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).continuousOn
  refine ⟨C, fun n t ht => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  have e : Ψ (((γ * n : N) : G) * g) t = Ψ (n * g) t := by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _ _
  exact e ▸ hC (γ * n, t) ⟨hk, ht⟩

theorem hasFDerivAt_param {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : Cocompact Γ N) (H : G → (Fin k → ℝ) → E)
    (hinv : ∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) (hd : ∀ x, Differentiable ℝ (H x))
    (h0 : Continuous fun p : G × (Fin k → ℝ) => H p.1 p.2)
    (h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2) (g : G) (t₀ : Fin k → ℝ) :
    HasFDerivAt (fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N)
      (∫ q, fderiv ℝ (H ((q.out : N) * g)) t₀ ∂probMeasure Γ N) t₀ := by
  have := hc.isProbabilityMeasure
  have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
    rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
  obtain ⟨C, hC⟩ := exists_bound (Ψ := fun x t => fderiv ℝ (H x) t) hc h1 hinv' g (isCompact_closedBall t₀ 1)
  obtain ⟨C0, hC0⟩ := exists_bound (Ψ := H) hc h0 hinv g (isCompact_closedBall t₀ 1)
  have hm : ∀ t, AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => H ((q.out : N) * g) t) (probMeasure Γ N) :=
    fun t => aestronglyMeasurable_out (Φ := fun x => H x t) (h0.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv γ hγ x t) g _
  have hm' : AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => fderiv ℝ (H ((q.out : N) * g)) t₀)
      (probMeasure Γ N) :=
    aestronglyMeasurable_out (Φ := fun x => fderiv ℝ (H x) t₀) (h1.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv' γ hγ x t₀) g _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ one_pos) (.of_forall hm)
    (Integrable.of_bound (hm t₀) C0 (.of_forall fun q => hC0 _ t₀ (Metric.mem_closedBall_self zero_le_one))) hm'
    (.of_forall fun q t ht => hC _ t (Metric.ball_subset_closedBall ht)) (integrable_const C)
    (.of_forall fun q t _ => (hd _ t).hasFDerivAt)


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem iteratedFDeriv_fderiv_eq {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) (m : ℕ) (t : Fin k → ℝ) :
    iteratedFDeriv ℝ m (fderiv ℝ f) t =
      (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E) (iteratedFDeriv ℝ (m + 1) f t) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_of_iteratedFDeriv_zero {X : Type} [TopologicalSpace X] {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : X → (Fin k → ℝ) → E}
    (h : Continuous fun p : X × (Fin k → ℝ) => iteratedFDeriv ℝ 0 (H p.1) p.2) :
    Continuous fun p : X × (Fin k → ℝ) => H p.1 p.2 := by
  have e : (fun p : X × (Fin k → ℝ) => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E).continuous.comp h

theorem contDiff_param (hc : Cocompact Γ N) (g : G) {k : ℕ} (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : G → (Fin k → ℝ) → E),
      (∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) → (∀ x, ContDiff ℝ ∞ (H x)) →
      (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (H p.1) p.2) →
      ContDiff ℝ n fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N := by
  induction n with
  | zero =>
    intro E _ _ _ H hinv hs hm
    have h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2 := by
      refine continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 (Fin k → ℝ) E).continuous.comp (hm 1)
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => ?_)
    exact (hasFDerivAt_param hc H hinv (fun x => (hs x).differentiable (by simp))
      (continuous_of_iteratedFDeriv_zero (hm 0)) h1 g t).continuousAt
  | succ n ih =>
    intro E _ _ _ H hinv hs hm
    have hm' : ∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2 := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E).continuous.comp (hm (m + 1))
    have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
      rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (fun x => fderiv ℝ (H x)) hinv'
      (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).2) hm', fun t => ?_⟩
    exact hasFDerivAt_param hc H hinv (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).1)
      (continuous_of_iteratedFDeriv_zero (hm 0))
      (continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) g t

end GlobalTheory.Cusp.SmoothParam

theorem GlobalTheory.Cusp.contDiff_constTermOn_param : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
    [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ),
    (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) →
    (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) →
    ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  intro G _ _ _ _ _ _ Γ N _ _ hc k F hinv hs hm g
  exact contDiff_infty.2 fun n => GlobalTheory.Cusp.SmoothParam.contDiff_param hc g n F hinv hs hm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFamiStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ), (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) → (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) → ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  first | exact @GlobalTheory.Cusp.contDiff_constTermOn_param | exact GlobalTheory.Cusp.contDiff_constTermOn_param | (intros; apply GlobalTheory.Cusp.contDiff_constTermOn_param <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensor
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

theorem exists_mul_mem_tens (E : Place (algebraMap ℂ K)) (w : K ⊗[ℂ] κ') :
    ∃ d ∈ E.ring, d ≠ 0 ∧ (d ⊗ₜ[ℂ] (1 : κ')) * w ∈ tens (κ' := κ') (placeAlg E) := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, one_ne_zero, by simpa using zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := E.ring) x
    have hb0 : (b : K) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
    have he : x * (b : K) = (a : K) := by
      rw [← e]
      exact div_mul_cancel₀ _ hb0
    refine ⟨b, b.2, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, he]
    exact tmul_mem a.2 y
  | add u v hu hv =>
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := hu
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := hv
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, mul_ne_zero hd₁0 hd₂0, ?_⟩
    have e : ((d₁ * d₂) ⊗ₜ[ℂ] (1 : κ')) * (u + v) =
        (d₂ ⊗ₜ[ℂ] (1 : κ')) * ((d₁ ⊗ₜ[ℂ] (1 : κ')) * u) +
          (d₁ ⊗ₜ[ℂ] (1 : κ')) * ((d₂ ⊗ₜ[ℂ] (1 : κ')) * v) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁, mul_add]
    rw [e]
    exact add_mem (mul_mem (tmul_mem hd₂ 1) h₁) (mul_mem (tmul_mem hd₁ 1) h₂)

theorem isLocModel_locAt : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ E 𝔭 _ hO
  obtain ⟨O', hO'⟩ := hO
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ locAt (L := L) 𝔭 := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toQ (L := L) 𝔭 (algebraMap ℂ (tens (κ' := κ') (placeAlg E)) a)).2
  refine
    { const_mem := hc
      isLocalRing := isLocalRing_locAt 𝔭 hinj
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc =
        (toQ (L := L) 𝔭).comp (algebraMap ℂ (tens (κ' := κ') (placeAlg E))) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toQ]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]

    letI : Algebra ℂ O' := ((algebraMap ℂ κ').codRestrict O' hO'.const_mem).toAlgebra
    haveI : IsScalarTower ℂ O' κ' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ O' := hO'.essFiniteType
    haveI : IsFractionRing O' κ' := IsFractionRing.of_field O' κ' fun f => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO'.frac f
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩
    haveI : Algebra.EssFiniteType O' κ' :=
      Algebra.EssFiniteType.of_isLocalization κ' (nonZeroDivisors O')
    haveI : Algebra.EssFiniteType ℂ κ' := Algebra.EssFiniteType.comp ℂ O' κ'

    haveI : Algebra.EssFiniteType ℂ (placeAlg E) := by
      let φ : E.ring →+* placeAlg E :=
        { toFun := fun x => ⟨x.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ : φ.FiniteType := RingHom.FiniteType.of_surjective φ fun y => ⟨⟨y.1, y.2⟩, rfl⟩
      have e : φ.comp ((algebraMap ℂ K).codRestrict E.ring E.const_mem) =
          algebraMap ℂ (placeAlg E) := RingHom.ext fun _ => rfl
      have h := RingHom.EssFiniteType.comp E.essFiniteType hφ.essFiniteType
      rw [e] at h
      exact RingHom.essFiniteType_algebraMap.1 h
    haveI : Algebra.EssFiniteType (placeAlg E) (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.baseChange ℂ κ' (placeAlg E)
    haveI : Algebra.EssFiniteType ℂ (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.comp ℂ (placeAlg E) (placeAlg E ⊗[ℂ] κ')
    haveI : Algebra.EssFiniteType ℂ (tens (κ' := κ') (placeAlg E)) :=
      Algebra.EssFiniteType.of_surjective (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom
        (tensEquiv (κ' := κ') (placeAlg E)).surjective
    have h1 : (algebraMap ℂ (tens (κ' := κ') (placeAlg E))).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 inferInstance

    letI : Algebra (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) := (toQ (L := L) 𝔭).toAlgebra
    haveI : IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) :=
      { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
        surj := fun x => by
          obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
          exact ⟨(a, ⟨s, hs⟩), hx⟩
        exists_of_eq := fun {x y} h => ⟨1, by
          simp only [OneMemClass.coe_one, one_mul]
          exact Subtype.ext (hinj (congrArg Subtype.val h))⟩ }
    haveI : Algebra.EssFiniteType (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) :=
      Algebra.EssFiniteType.of_isLocalization (locAt (L := L) 𝔭) 𝔭.primeCompl
    have h2 : (toQ (L := L) 𝔭).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hv0 : algebraMap (K ⊗[ℂ] κ') L v ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := exists_mul_mem_tens (κ' := κ') E u
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := exists_mul_mem_tens (κ' := κ') E v
    set D : K ⊗[ℂ] κ' := (d₁ * d₂) ⊗ₜ[ℂ] (1 : κ') with hD
    have hD1 : D = (d₂ ⊗ₜ[ℂ] (1 : κ')) * (d₁ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁]
    have hD2 : D = (d₁ ⊗ₜ[ℂ] (1 : κ')) * (d₂ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hu : D * u ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD1, mul_assoc]; exact mul_mem (tmul_mem hd₂ 1) h₁
    have hv' : D * v ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD2, mul_assoc]; exact mul_mem (tmul_mem hd₁ 1) h₂
    have hDu : IsUnit D := by
      refine IsUnit.of_mul_eq_one ((d₁ * d₂)⁻¹ ⊗ₜ[ℂ] (1 : κ')) ?_
      rw [hD, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (mul_ne_zero hd₁0 hd₂0)]
      rfl
    have hD0 : algebraMap (K ⊗[ℂ] κ') L D ≠ 0 := (hDu.map _).ne_zero
    refine ⟨_, (toQ (L := L) 𝔭 ⟨D * u, hu⟩).2, _, (toQ (L := L) 𝔭 ⟨D * v, hv'⟩).2, ?_, ?_⟩
    · show algebraMap (K ⊗[ℂ] κ') L (D * v) ≠ 0
      rw [map_mul]; exact mul_ne_zero hD0 hv0
    · show _ * algebraMap (K ⊗[ℂ] κ') L (D * v) = algebraMap (K ⊗[ℂ] κ') L (D * u)
      rw [map_mul, map_mul]
      field_simp

end GlobalTheory.GraphLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRingOfVarietyPoint_localization_placeTensor : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  first | exact @GlobalTheory.GraphLocal.isLocModel_locAt | exact GlobalTheory.GraphLocal.isLocModel_locAt | (intros; apply GlobalTheory.GraphLocal.isLocModel_locAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrix
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem nrmL_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  intro E _ _ _ _ w hw K e hec _ _ B m b u β hG hβ
  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hGc0 := GlobalTheory.GramTwistNorm.gram_map_conj B' (w.adicCompletion E) e (cj w) hec m β hβ b
  set G := gram e b β with hGdef
  set P := mulMat e b u with hP
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦ
  set s : w.adicCompletion E := (-1) ^ (m - 1) with hs
  have hGc : G.map (cj w) = s • (Gᵀ * P) := hGc0
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hΦT : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (GlobalTheory.GramTwistNorm.phi_mul_transpose m)
  have hd : (dlt e b β).val = (G⁻¹)ᵀ * Φᵀ := by
    rw [dlt, dite_eq_left hG]
    change ((hG.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ).val)ᵀ * Φᵀ = _
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have hdi : ((dlt e b β)⁻¹).val = Φ * Gᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦT, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hΦΦ : Φᵀ * Φᵀ = s • (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
    rw [← Matrix.transpose_mul, hΦ, GlobalTheory.GramTwistNorm.phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hθ : (thetaGL m (cj w) (dlt e b β)).val = Φ * (((dlt e b β)⁻¹).val.map (cj w))ᵀ * Φᵀ := rfl
  have hGG : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hss : s * s = 1 := by rw [hs, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [nrmL, if_neg hw, Units.val_mul, hθ, hdi, Matrix.map_mul, hΦ, GlobalTheory.GramTwistNorm.phi_map, ← hΦ,
    Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hGc, hd]
  calc (G⁻¹)ᵀ * Φᵀ * (Φ * (s • (Gᵀ * P) * Φᵀ) * Φᵀ)
      = s • (((G⁻¹)ᵀ * Gᵀ) * P * (Φᵀ * Φᵀ)) + (0 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
        rw [add_zero]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Φᵀ Φ, hΦT, Matrix.one_mul]
    _ = P := by
        rw [add_zero, hGG, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory.TwLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrixStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_norm_gramInverse_eq_mulMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  first | exact @GlobalTheory.TwLat.nrmL_dlt | exact GlobalTheory.TwLat.nrmL_dlt | (intros; apply GlobalTheory.TwLat.nrmL_dlt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNorm
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU.NormSwap

theorem neg_inv_ratio_norm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  intro F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add (f := _), hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  have hz := B.sum_repr t
  rw [Fin.sum_univ_two] at hz
  set p₀ := B.repr t 0
  set q₀ := B.repr t 1
  rw [← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add (f := _), ← map_mul] at hε
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective
    intro x y hxy
    apply this
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  have h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0 :=
    hinj (by rw [hε, map_zero])
  set c := algebraMap F R (f₂ / f₁)
  have hca : c * algebraMap F R (f₁ / f₂) = 1 := by
    rw [← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]
  refine ⟨c * p₀, c * q₀, ?_⟩
  rw [map_neg]
  linear_combination (-c ^ 2) * h + ε * c * hca

end GlobalTheory.PlaneSU.NormSwap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNormStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_inv_ratio_isNorm_of_neg_ratio_isNorm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  first | exact @GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm | exact GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm | (intros; apply GlobalTheory.PlaneSU.NormSwap.neg_inv_ratio_norm <;> assumption)
end
end
