module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnit
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

theorem GlobalTheory.herbrand_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  intro C _ v S _ _ a ha N Fil hFil τ
  obtain ⟨hfree, hfin, hlc, hev, hker, ⟨g, hg⟩, hann⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have hd : ev a τ (cofac a τ) ≠ 0 := by
    rw [hev]
    exact Finset.prod_ne_zero_iff.mpr fun s hs =>
      sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hs (ha h).symm
  have hid : ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x) := by
    intro x
    have : cofac a τ • x = ev a τ (cofac a τ) • x + g • (lin a τ • x) := by
      conv_lhs => rw [hg]
      rw [add_smul, algebraMap_smul, mul_comm, mul_smul]
    rw [this, add_sub_cancel_right]
  have htf : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    haveI := hfree
    haveI : Module.IsTorsionFree (Int0 v) (Fin N → RS a) :=
      (Module.Free.chooseBasis (Int0 v) (Fin N → RS a)).isTorsionFree
    exact (smul_eq_zero_iff_right hc).mp hx
  have hcomp0 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ ∀ i, ev a τ (x i) = 0 := by
    intro x
    constructor
    · intro h i; exact congrFun h i
    · intro h; funext i; exact h i
  have h2 : ∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0 := by
    intro x
    rw [hcomp0]
    constructor
    · intro h
      show cofac a τ • x = 0
      funext i
      obtain ⟨r', hr'⟩ := hker _ (h i)
      show cofac a τ * x i = 0
      rw [hr', ← mul_assoc, mul_comm (cofac a τ), hlc, zero_mul]
    · intro h i
      have hi : cofac a τ * x i = 0 := congrFun h i
      have := congrArg (ev a τ) hi
      rw [map_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hd
  have h3 : LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range, hcomp0]
    constructor
    · intro h
      choose r hr using fun i => hker _ (h i)
      exact ⟨r, funext fun i => (hr i).symm⟩
    · rintro ⟨y, rfl⟩ i
      show ev a τ (lin a τ * y i) = 0
      rw [map_mul, ev_lin, sub_self, zero_mul]
  have hcz : ∀ x : Fin N → RS a, comp a N τ x = 0 → cofac a τ • x = 0 := fun x h => (h2 x).mp h
  refine ⟨hd, h2, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htf, ⟨g, hid⟩⟩
  ·
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x ∈ Fil := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    apply hFil _ x hd
    rw [hid, hc, zero_sub]
    exact Fil.neg_mem (Fil.smul_mem g hx1')
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      refine ⟨hx', ?_⟩
      show cofac a τ • (lin a τ • x) = 0
      rw [smul_smul, mul_comm, hlc, zero_smul]
    · rintro ⟨hy1, hy2⟩
      have hy2' : mulR a N (cofac a τ) y = 0 := hy2
      have hk : y ∈ LinearMap.ker (comp a N τ) := (h2 y).mpr hy2'
      rw [h3] at hk
      obtain ⟨x, rfl⟩ := hk
      exact ⟨x, hy1, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx1' : lin a τ • x = 0 := hx1
    have hc : cofac a τ • x = 0 := hcz x hx2
    have : ev a τ (cofac a τ) • x = 0 := by rw [hid, hc, hx1', smul_zero, sub_zero]
    exact (Submodule.mem_bot _).mpr (htf _ x hd this)
  · ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and, LinearMap.lsmul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x = 0 := hx
      choose c hc using fun i => hann (x i) (congrFun hx' i)
      refine ⟨c, funext fun i => ?_⟩
      show ev a τ (cofac a τ) * c i = ev a τ (x i)
      rw [hc i, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ, ?_, ?_⟩
      · show lin a τ • (fun i => algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        funext i
        show lin a τ * (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = 0
        rw [mul_left_comm, hlc, mul_zero]
      · funext i
        show ev a τ (algebraMap (Int0 v) (RS a) (c i) * cofac a τ) = ev a τ (cofac a τ) * c i
        rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : lin a τ • x ∈ Fil := hx
      show lin a τ • Fil.mkQ x = 0
      rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx'
    · intro hq
      have hq' : lin a τ • q = 0 := hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective Fil q
      refine ⟨x, ?_, rfl⟩
      show lin a τ • x ∈ Fil
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hq'
  · intro x hx
    have hx' : lin a τ • x = 0 := hx
    show lin a τ • x ∈ Fil
    rw [hx']; exact Fil.zero_mem
  · intro x hx
    show lin a τ • x ∈ Fil
    exact Fil.smul_mem _ hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFactsStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ev a τ (cofac a τ) ≠ 0 ∧ (∀ x : Fin N → RS a, comp a N τ x = 0 ↔ mulR a N (cofac a τ) x = 0) ∧ LinearMap.ker (comp a N τ) = LinearMap.range (mulR a N (lin a τ)) ∧ preEig a Fil τ ⊓ LinearMap.ker (comp a N τ) ≤ Fil.restrictScalars (Int0 v) ∧ (preEig a Fil τ).map (mulR a N (lin a τ)) = filKer a Fil τ ∧ eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (comp a N τ) = ⊥ ∧ (eigSub a τ (Fin N → RS a)).map (comp a N τ) = (⊤ : Submodule (Int0 v) (Fin N → Int0 v)).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) (ev a τ (cofac a τ))) ∧ (preEig a Fil τ).map (proj a Fil) = eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧ eigSub a τ (Fin N → RS a) ≤ preEig a Fil τ ∧ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ ∧ (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x = 0 → x = 0) ∧ (∃ g : RS a, ∀ x : Fin N → RS a, ev a τ (cofac a τ) • x = cofac a τ • x - g • (lin a τ • x)) := by
  first | exact @GlobalTheory.herbrand_lattice_facts | exact GlobalTheory.herbrand_lattice_facts | (intros; apply GlobalTheory.herbrand_lattice_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebra
open MvPolynomial

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R]

theorem homogeneousComponent_mul_of_homogeneous_left {S : Type} [CommRing S] {k : ℕ} (n : ℕ)
    {P : MvPolynomial σ S} (hP : P.IsHomogeneous k) (Q : MvPolynomial σ S) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := S)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ S) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (T : MvPolynomial σ S),
      ((DirectSum.decompose (homogeneousSubmodule σ S) T m : homogeneousSubmodule σ S m) :
        MvPolynomial σ S) = homogeneousComponent m T :=
    fun m T => MvPolynomial.decomposition.decompose'_apply T m
  rw [e, e] at h
  exact h

noncomputable def piece (I : Ideal R) (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (((AddMonoidAlgebra.coeff F m : reesAlgebra I) : Polynomial R).coeff e)

variable {I : Ideal R}

@[simp] theorem coeff_piece (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m = (AddMonoidAlgebra.coeff F m).1.coeff e := by
  classical
  simp only [piece, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; rfl

@[simp] theorem piece_zero (e : ℕ) : piece I e (0 : MvPolynomial σ (reesAlgebra I)) = 0 := by
  ext m; simp

@[simp] theorem piece_add (e : ℕ) (F G : MvPolynomial σ (reesAlgebra I)) :
    piece I e (F + G) = piece I e F + piece I e G := by
  ext m; simp

theorem piece_X_mul (e : ℕ) (i : σ) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (X i * F) = X i * piece I e F := by
  classical
  ext m
  rw [coeff_piece, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp

theorem piece_C_mul (e : ℕ) (r : reesAlgebra I) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (C r * F) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, C ((r : Polynomial R).coeff p.1) * piece I p.2 F := by
  ext m
  simp [coeff_sum, coeff_C_mul, Polynomial.coeff_mul]

theorem piece_isHomogeneous (e : ℕ) {d : ℕ} {F : MvPolynomial σ (reesAlgebra I)}
    (hF : F.IsHomogeneous d) : (piece I e F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro h
  apply hm
  rw [coeff_piece, h]
  simp

theorem coeff_piece_mem (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (piece I e F) m ∈ I ^ e := by
  rw [coeff_piece]
  exact (mem_reesAlgebra_iff I _).1 (AddMonoidAlgebra.coeff F m).2 e

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R] {I : Ideal R}

theorem C_mul_mem_of_pow (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    ∀ (k : ℕ) (b : R), b ∈ I ^ k → ∀ (l t : ℕ) (P : MvPolynomial σ R), P.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff P m ∈ I ^ l) → P ∈ J l → C b * P ∈ J (l + k) := by
  intro k
  induction k with
  | zero =>
    intro b _ l t P _ _ hP
    simpa using (J l).mul_mem_left (C b) hP
  | succ k ih =>
    intro b hb l t P hPh hPc hP
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      have h1 := ih x hx l t P hPh hPc hP
      have h2 : ∀ m, AddMonoidAlgebra.coeff (C x * P) m ∈ I ^ (l + k) := by
        intro m
        rw [coeff_C_mul, pow_add, mul_comm (I ^ l)]
        exact Ideal.mul_mem_mul hx (hPc m)
      have h3 := H (l + k) t y (C x * P) hy (hPh.C_mul x) h2 h1
      rw [show C (x * y) * P = C y * (C x * P) by rw [C_mul]; ring]
      simpa [add_assoc] using h3
    · intro x y hx hy
      rw [C_add, add_mul]
      exact add_mem hx hy

def reesIdeal (I : Ideal R) (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    Ideal (MvPolynomial σ (reesAlgebra I)) where
  carrier := {F | ∀ d e, piece I e (homogeneousComponent d F) ∈ J e}
  zero_mem' := by intro d e; simp
  add_mem' := by
    intro F G hF hG d e
    rw [map_add (f := _), piece_add]
    exact add_mem (hF d e) (hG d e)
  smul_mem' := by
    intro c F hF
    rw [smul_eq_mul]
    revert F
    induction c using MvPolynomial.induction_on with
    | C r =>
      intro F hF d e
      rw [homogeneousComponent_C_mul, piece_C_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      have hpe : p.2 + p.1 = e := by rw [add_comm]; exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [← hpe]
      exact C_mul_mem_of_pow J H p.1 _ ((mem_reesAlgebra_iff I _).1 r.2 p.1) p.2 d _
        (piece_isHomogeneous p.2 (homogeneousComponent_isHomogeneous d F))
        (coeff_piece_mem p.2 _) (hF d p.2)
    | add p q hp hq =>
      intro F hF d e
      rw [add_mul, map_add (f := _), piece_add]
      exact add_mem (hp hF d e) (hq hF d e)
    | mul_X p i hp =>
      intro F hF
      rw [mul_assoc]
      apply hp
      intro d e
      rw [homogeneousComponent_mul_of_homogeneous_left d (isHomogeneous_X _ i)]
      split_ifs
      · rw [piece_X_mul]
        exact (J e).mul_mem_left _ (hF _ e)
      · simp

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

theorem exists_homogeneous_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G ∈ J e) := by
  intro R _ I n J H
  refine ⟨reesIdeal I J H, ?_, ?_⟩
  · intro F hF d d' e
    show piece I e (homogeneousComponent d' (homogeneousComponent d F)) ∈ J e
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d F)]
    split_ifs
    · exact hF d e
    · simp
  · intro t F hFt
    have hG : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R),
        (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G = piece I e F := by
      intro e G hG
      ext m
      rw [hG, coeff_piece]
    constructor
    · intro hF e G hGc
      rw [hG e G hGc]
      have := hF t e
      rwa [homogeneousComponent_eq_self hFt] at this
    · intro h d e
      show piece I e (homogeneousComponent d F) ∈ J e
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule t F).2 hFt)]
      split_ifs
      · exact h e _ fun m => coeff_piece e F m
      · simp

end GlobalTheory.ReesHomogeneous
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebraStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, AddMonoidAlgebra.coeff G m = (AddMonoidAlgebra.coeff F m).1.coeff e) → G ∈ J e) := by
  first | exact @GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal | exact GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal | (intros; apply GlobalTheory.ReesHomogeneous.exists_homogeneous_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomJet
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SquareLiftLemmas

open CategoryTheory GlobalTheory.AnPer GlobalTheory.AnPer.Charts

def liftSq {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) : TrivSqZeroExt O (Fin g → O) →+* C where
  toFun x := ρ x.fst + ∑ a, ρ (x.snd a) * n a
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, map_add (f := _), add_mul,
      Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have h0 : (∑ a, ρ (x.snd a) * n a) * (∑ b, ρ (y.snd b) * n b) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [mul_mul_mul_comm, hn, mul_zero]
    have h1 : ∀ a, ρ ((x * y).snd a) * n a =
        ρ x.fst * (ρ (y.snd a) * n a) + (ρ (x.snd a) * n a) * ρ y.fst := fun a ↦ by
      have : (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
        simp [TrivSqZeroExt.snd_mul, mul_comm]
      rw [this, map_add (f := _), map_mul, map_mul]; ring
    rw [add_mul, mul_add, mul_add, h0, add_zero, TrivSqZeroExt.fst_mul, map_mul]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

theorem liftSq_apply {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (x : TrivSqZeroExt O (Fin g → O)) :
    liftSq ρ n hn x = ρ x.fst + ∑ a, ρ (x.snd a) * n a := rfl

theorem liftSq_inl {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (h : O) : liftSq ρ n hn (TrivSqZeroExt.inl h) = ρ h := by
  simp [liftSq_apply]

theorem liftSq_sec {g : ℕ} {O C : Type} [CommRing O] [Algebra ℂ O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (D : Fin g → Derivation ℂ O O) (h : O) :
    liftSq ρ n hn (tszeSec D h) = ρ h + ∑ a, ρ (D a h) * n a := by
  rw [liftSq_apply, fst_tszeSec]
  simp only [snd_tszeSec]

theorem exists_hom_jet {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C)
    (hdeg : Hom.deg f₁ = Hom.deg f₂) (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (h : ∀ x : Hol (K.W k), Hom.φ f₂ x = Hom.φ f₁ x + ∑ a, Hom.φ f₁ (dw a x) * n a) :
    ∃ χ : K.jet k ⟶ T, Hom.deg χ = Hom.deg f₁ ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        Hom.φ χ x = Hom.φ f₁ x.fst + ∑ a, Hom.φ f₁ (x.snd a) * n a := by
  let ρ : Hol (K.W k) →+* T.C := (Hom.φ f₁ : (K.triv k).C →+* T.C)
  letI := (K.jet k).alg
  letI := (K.triv k).alg
  let φ : (K.jet k).C →ₐ[Hol F.V] T.C :=
    { liftSq ρ n hn with
      commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }
  have hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x := fun _ ↦ rfl
  have hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ :=
    RingHom.ext fun x ↦ liftSq_inl ρ n hn x
  let χ : K.jet k ⟶ T :=
    { φ := φ
      deg := Hom.deg f₁
      le := Hom.le f₁
      mem := fun c hc ↦ by
        have hc' : TrivSqZeroExt.fst c = 0 := hc
        rw [hφ, liftSq_apply, hc', map_zero, zero_add]
        exact T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)
      close := by rw [hcomp]; exact Hom.close f₁ }
  refine ⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩
  · change liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _
    rw [sh_refl, liftSq_inl]; rfl
  · change liftSq ρ n hn (tszeSec dw c) = _
    refine Eq.trans ?_ (h c).symm
    exact liftSq_sec ρ n hn dw c

end GlobalTheory.SquareLiftLemmas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
open IsLocalRing RingTheory.Sequence Pointwise

namespace GlobalTheory.AnnRegSeq

theorem free_of_maximalIdeal_eq_bot {B M : Type} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] (hm : maximalIdeal B = ⊥) : Module.Free B M := by
  have hF : IsField B := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  letI := hF.toField
  exact Module.Free.of_divisionRing B M

theorem maximalIdeal_eq_bot_of_le_sq {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B ≤ maximalIdeal B ^ 2) : maximalIdeal B = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B)
    (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
    (maximalIdeal_le_jacobson ⊥)

theorem exists_isSMulRegular_notMem_sq {B M : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hass : maximalIdeal B ∉ associatedPrimes B M) (hsq : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2) :
    ∃ x ∈ maximalIdeal B, x ∉ maximalIdeal B ^ 2 ∧ IsSMulRegular M x := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B) := by
    intro z hz
    rw [Set.biUnion_insert]
    by_cases h2 : z ∈ maximalIdeal B ^ 2
    · exact Or.inl h2
    · right
      have : z ∈ ({r : B | IsSMulRegular M r}ᶜ) := hcon z hz h2
      rwa [← biUnion_associatedPrimes_eq_compl_regular B M] at this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _)
    (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by
      rcases hi with rfl | hi
      · exact absurd rfl h1
      · exact hi.isPrime)).mp hsub
  rcases hp with rfl | hp
  · exact hsq hle
  · have : p = maximalIdeal B := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle
    exact hass (this ▸ hp)

theorem free_of_free_quotient {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {x : B} (hx : x ∈ maximalIdeal B)
    (reg : IsSMulRegular M x)
    [Module.Free (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))] :
    Module.Free B M := by
  set I : Ideal B := Ideal.span {x} with hI
  set P : Submodule B M := I • ⊤ with hP
  have hIj : I ≤ (⊥ : Ideal B).jacobson := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact maximalIdeal_le_jacobson _ hx
  haveI : IsLocalRing (B ⧸ I) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ I) (M ⧸ P)
  set r := Module.finrank (B ⧸ I) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  let φ : (Fin r → B) →ₗ[B] M := Fintype.linearCombination B v
  have hφ : ∀ c, φ c = ∑ i, c i • v i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) =
      ∑ i, Ideal.Quotient.mk I (c i) • b i := by
    intro c
    rw [hφ]
    change Submodule.mkQ P (∑ i, c i • v i) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)
    intro m _
    choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)
    have h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m := by
      rw [hmk]
      simp only [hc']
      exact b.sum_repr _
    rw [Submodule.Quotient.eq] at h1
    have h2 : m = φ c' - (φ c' - m) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)
  have hker : LinearMap.ker φ = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0 := by
      rw [← hmk, hk]
      rfl
    have hki : ∀ i, k i ∈ I := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)
    choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)
    have hkx : k = x • k' := by
      ext i
      simp [← hk' i, mul_comm]
    have hk'ker : k' ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply reg
      show x • φ k' = x • 0
      rw [smul_zero, ← map_smul, ← hkx, hk]
    rw [hkx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)

theorem free_of_modDepthGE (n : ℕ) : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
    ReciprocityTheory.CA.ModDepthGE B M n → (maximalIdeal B).spanFinrank ≤ n → Module.Free B M := by
  induction n with
  | zero =>
    intro B _ _ _ M _ _ _ _ hsp
    exact free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))
  | succ n ih =>
    intro B _ _ _ M _ _ _ hd hsp
    by_cases hsq : maximalIdeal B ≤ maximalIdeal B ^ 2
    · exact free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hd
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hy : y ∈ maximalIdeal B := hmem y (by simp)
    have hass := ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1
    obtain ⟨x, hx, hx2, hxreg⟩ := exists_isSMulRegular_notMem_sq hass hsq
    have hd' := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩
    haveI : IsLocalRing (B ⧸ Ideal.span {x}) :=
      ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
    haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) :=
      Module.Finite.of_restrictScalars_finite B _ _
    have hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h1 :=
        ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
      omega
    have hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n := by
      obtain ⟨zs, hzl, hzm, hzr⟩ := hd'
      let e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M) :=
        Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm
      refine ⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)
      · rw [← Ideal.Quotient.algebraMap_eq]
        exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)
    haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'
    exact free_of_free_quotient hx hxreg

end GlobalTheory.AnnRegSeq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocalStage

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤
        (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa using hx
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    simpa using hle hf
  · intro hf
    rw [← Polynomial.X_mul_divX_add f]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)

theorem comap_originIdeal {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom φ) =
      GlobalTheory.KeyOriginCut.originIdeal R := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

theorem localStage : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  intro T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα
  letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra
  letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra
  haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) :=
    Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')
  let f : Polynomial A' →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)
      commutes' := by
        intro p
        change (algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [Polynomial.map_map, hαι] }
  let g : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA))
      commutes' := by
        intro p
        change jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [← IsScalarTower.algebraMap_apply]
        exact congrArg (fun h => h p) hjA }
  let F : (Polynomial A' ⊗[Polynomial A] EA) →+* O :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hF : ∀ a b, F (a ⊗ₜ b) = f a * g b := fun a b => by
    simp [F, Algebra.TensorProduct.productMap_apply_tmul]
  let Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA) := (maximalIdeal O).comap F
  refine ⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q',
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) := by
      refine RingHom.ext fun p => ?_
      rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
      rfl
    change ((maximalIdeal O).comap F).comap _ = _
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]
  let h : EA →+* (Polynomial A' ⊗[Polynomial A] EA) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom
  have hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x) := fun x => by
    change F (1 ⊗ₜ x) = _
    rw [hF, map_one, one_mul]
    rfl
  have hy : QA.primeCompl ≤ Q'.primeCompl.comap h := by
    intro x hx
    have hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x)) :=
      (IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA
    change h x ∉ Q'
    intro hmem
    have hmem' : F (h x) ∈ maximalIdeal O := hmem
    rw [hh] at hmem'
    exact ((mem_maximalIdeal _).mp hmem') hu
  have hγ : ∀ y : Q'.primeCompl, IsUnit (F y) := by
    intro y
    by_contra hc
    exact y.2 ((mem_maximalIdeal _).mpr hc)
  let β : Localization.AtPrime QA →+* Localization.AtPrime Q' :=
    IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q')
      (g := h) (T := Q'.primeCompl) hy
  let γ : Localization.AtPrime Q' →+* O :=
    IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ
  refine ⟨β, γ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA),
      IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q')]
    change _ = β (algebraMap EA (Localization.AtPrime QA) _)
    rw [IsLocalization.map_eq]
    congr 1
    change algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) =
      (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change _ = Polynomial.map ι (Polynomial.C a)
    rw [Polynomial.map_C]
    rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    change γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, hh]
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply,
      hF, map_one, mul_one]
    change algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl

end GlobalTheory.LocalStage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOriginStatement
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localStage_tensor_polynomial_origin : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  first | (exact @GlobalTheory.LocalStage.localStage) | (exact GlobalTheory.LocalStage.localStage) | (intros; apply GlobalTheory.LocalStage.localStage  <;> assumption)
end
end
