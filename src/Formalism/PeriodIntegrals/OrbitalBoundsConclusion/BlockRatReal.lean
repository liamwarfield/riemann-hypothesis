module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SumIcoTsubTelescope
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.BlockRatReal
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def rowGen (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)

def rowDiv (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  (rowGen R a b f).coeff k

def lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s =>
    (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)).det

def nuNext {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ :=
  if h : s.val + 1 < n then ν ⟨s.val + 1, h⟩ else 0

def hw (R : Type*) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    MvPolynomial (Fin r × Fin n) R :=
  ∏ s : Fin n, (lpMinor R (s.val + 1) (by omega) (by omega)) ^ (ν s - nuNext ν s)

def applyWord (R : Type*) [CommRing R] {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) : MvPolynomial (Fin r × Fin n) R :=
  w.foldr (fun x g => rowDiv R x.1 x.2.1 x.2.2 g) f

def weyl (R : Type*) [CommRing R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  Submodule.span R (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord R w (hw R hn ν))

def detShift {N : ℕ} (w : Fin N → ℤ) : ℤ := if h : 0 < N then w ⟨N - 1, by omega⟩ else 0

def natW {N : ℕ} (w : Fin N → ℤ) : Fin N → ℕ := fun i => (w i - detShift w).toNat

def delSq (R : Type) [CommRing R] (N : ℕ) (w : Fin N → ℤ) : Submodule R (MvPolynomial (Fin N × Fin N) R) :=
  weyl R N N le_rfl (natW w)

def nuOf {m : ℕ} (lam : Fin (m + 1) → ℤ) : Fin (m + 1) → ℕ :=
  fun t => (lam t - lam (Fin.last m)).toNat

def lamAt {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') : Fin (m + 1) → ℤ :=
  if Even s.val then lam0 s else fun i => -lam0 s i.rev

def Frames {ι : Type} {n : ℕ} (_G : ι → Matrix (Fin n) (Fin n) ℂ) : Type :=
  {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}

section Blocks

variable {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} {Tau : Type} [Fintype Tau] {n : ℕ}

def reM (h : m + 1 = n) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  A.submatrix (finCongr h) (finCongr h)

def zAt (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (M y : Tau → Matrix (Fin n) (Fin n) ℂ)
    (v : Fin nV) (s : Fin (n' v)) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  if Even s.val then reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩))
  else ((reM h (M (pos ⟨v, s⟩) * y (pos ⟨v, s⟩)))⁻¹)ᵀ.submatrix id Fin.rev

def eAt (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (v : Fin nV) (s : Fin (n' v)) : ℤ :=
  lamAt (lam0 v) s (Fin.last m)

def blkMod (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (R : Type) [Field R] (v : Fin nV) (s : Fin (n' v)) :
    Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
  if Antitone (lamAt (lam0 v) s) then dualWeyl R (m + 1) (m + 1) (nuOf (lamAt (lam0 v) s)) else ⊥

def WtTie (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (i : Fin (m + 1)), lam0 v s i = lam (pos ⟨v, s⟩) (finCongr h i)

def BlockRational (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {LL : Type} [Field LL] (h : m + 1 = n)
    (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau) (G M : Tau → Matrix (Fin n) (Fin n) ℂ)
    (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ) : Prop :=
  ∀ v (s : Fin (n' v)) (f : MvPolynomial (Fin n × Fin n) ℤ), f ∈ delSq ℤ n (lam (pos ⟨v, s⟩)) →
    ∃ F ∈ blkMod lam0 LL v s, ∀ y : Frames G,
      (zAt h pos M y.1 v s).det ^ (eAt lam0 v s) *
          eval (fun x => zAt h pos M y.1 v s x.1 x.2) (MvPolynomial.map embLL F) =
        (y.1 (pos ⟨v, s⟩)).det ^ detShift (lam (pos ⟨v, s⟩)) *
          eval (fun x => y.1 (pos ⟨v, s⟩) x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

end Blocks

def Stmt : Prop :=
  ∀ {nV : ℕ} {n' : Fin nV → ℕ} {m : ℕ} (lam0 : ∀ v : Fin nV, Fin (n' v) → Fin (m + 1) → ℤ) {Tau : Type} [Fintype Tau]
    {n : ℕ} {LL : Type} [Field LL] (h : m + 1 = n) (pos : (Σ v : Fin nV, Fin (n' v)) ≃ Tau)
    (G M : Tau → Matrix (Fin n) (Fin n) ℂ) (embLL : LL →+* ℂ) (lam : Tau → Fin n → ℤ), (∀ τ, Antitone (lam τ)) →
    WtTie lam0 h pos lam → (∀ τ, ∃ M0 : GL (Fin n) LL, M τ = M0.1.map embLL) →
    BlockRational lam0 h pos G M embLL lam

end PI.BlockRatReal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bridge
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem s1 {S : Type} [CommRing S] (φ : ℤ →+* S) (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν)
    (f : MvPolynomial (Fin k × Fin k) ℤ) (hf : f ∈ PI.BlockRatReal.weyl ℤ k k le_rfl ν) :
    MvPolynomial.map φ f ∈ PI.BlockRatReal.dualWeyl S k k ν := by
  have hle := Formalism.GradedWeylDivisibility.weylLeDual_of Formalism.GradedWeylDivisibility.highestWeightVectorMem Formalism.GradedWeylDivisibility.dualWeylModuleRowDividedPowerStable
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ k k ν := hle ℤ k k le_rfl ν hν hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleMap ℤ S φ k k ν f h1

theorem s2 {R : Type} [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (g : Matrix (Fin k) (Fin k) R)
    (f : MvPolynomial (Fin k × Fin k) R) (hf : f ∈ PI.BlockRatReal.dualWeyl R k k ν) :
    Formalism.GradedWeylDivisibility.rowAct R g f ∈ PI.BlockRatReal.dualWeyl R k k ν := by
  have h1 : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R k k ν := hf
  exact Formalism.GradedWeylDivisibility.dualWeylModuleRowActionStable R k k ν g f h1

theorem eval_map_rowAct {LL : Type} [Field LL] (φ : LL →+* ℂ) {k : ℕ} (g : Matrix (Fin k) (Fin k) LL)
    (F : MvPolynomial (Fin k × Fin k) LL) (z : Matrix (Fin k) (Fin k) ℂ) :
    eval (fun x => z x.1 x.2) (MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct LL g F)) =
      eval (fun x => (g.map φ * z) x.1 x.2) (MvPolynomial.map φ F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem map_map_int {LL : Type} [Field LL] (φ : LL →+* ℂ) {σ : Type} (f : MvPolynomial σ ℤ) :
    MvPolynomial.map φ (MvPolynomial.map (Int.castRingHom LL) f) = MvPolynomial.map (Int.castRingHom ℂ) f := by
  rw [MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom LL)) (Int.castRingHom ℂ)]

end PI.BlockRatReal.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

def EvenStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf lam), ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
        (M0.1.map embLL * y).det ^ lam (Fin.last m) *
            eval (fun x => (M0.1.map embLL * y) x.1 x.2) (MvPolynomial.map embLL F) =
          y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

def OddStep : Prop :=
  ∀ (m : ℕ) (LL : Type) [Field LL] (embLL : LL →+* ℂ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    ∀ (M0 : GL (Fin (m + 1)) LL) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℤ),
      f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf lam) →
      ∃ F ∈ dualWeyl LL (m + 1) (m + 1) (nuOf fun i => -lam i.rev),
        ∀ y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, IsUnit y.det →
          (((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev).det ^ (-lam (Fin.last m).rev) *
              eval (fun x => ((M0.1.map embLL * y)⁻¹)ᵀ.submatrix id Fin.rev x.1 x.2) (MvPolynomial.map embLL F) =
            y.det ^ lam (Fin.last m) * eval (fun x => y x.1 x.2) (MvPolynomial.map (Int.castRingHom ℂ) f)

end PI.BlockRatReal
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.MapDetGenM
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula.Odd

open PI.OddDualWeyl

theorem map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R k) = genM S k := by
  ext i j; simp [genM]

theorem map_dualM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (i j : Fin k) :
    MvPolynomial.map φ (dualM R k i j) = dualM S k i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map φ) (genM R k)) (Fin.rev j)) i
  rw [map_genM] at h
  simpa [dualM, RingHom.mapMatrix_apply, Matrix.map_apply] using h

theorem map_det_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    MvPolynomial.map φ (genM R k).det = (genM S k).det := by
  rw [RingHom.map_det, map_genM]

theorem map_dualSub {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (p : MvPolynomial (Fin k × Fin k) R) :
    MvPolynomial.map φ (dualSub R k p) = dualSub S k (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [dualSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [dualSub, aeval_X]
    exact map_dualM φ k v.1 v.2

theorem rel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k M : ℕ)
    (f f' : MvPolynomial (Fin k × Fin k) R) (h : PI.OddDualWeyl.Rel R k M f f') :
    PI.OddDualWeyl.Rel S k M (MvPolynomial.map φ f) (MvPolynomial.map φ f') := by
  unfold PI.OddDualWeyl.Rel at *
  rw [← map_dualSub, h, map_mul, map_pow, map_det_genM]

theorem sgnK_map {LL : Type} [Field LL] (φ : LL →+* ℂ) (m : ℕ) : φ (sgnK LL m) = sgnK ℂ m := by
  simp only [sgnK]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, revCol, Matrix.submatrix_apply, id,
    Matrix.one_apply]
  split_ifs <;> simp

private theorem exists_weyl_lamStar_rel_of_mem_weyl (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R)
    (hf : f ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf lam)) :
    ∃ f' ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf (lamStar lam)),
      PI.OddDualWeyl.Rel R (m + 1) (expM lam) f f' := by
  have hgen : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ),
      PI.OddDualWeyl.MH R (PI.OddDualWeyl.applyWord R w
        (PI.OddDualWeyl.hw R le_rfl (PI.OddDualWeyl.nuOf lam))) ∧
      ∃ f' ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf (lamStar lam)),
        PI.OddDualWeyl.Rel R (m + 1) (expM lam)
          (PI.OddDualWeyl.applyWord R w (PI.OddDualWeyl.hw R le_rfl (PI.OddDualWeyl.nuOf lam))) f' := by
    intro w
    induction w with
    | nil =>
      rw [PI.OddDualWeyl.applyWord_nil]
      refine ⟨PI.OddDualWeyl.highest_weight_multiplicity R (m + 1) _, ?_⟩
      obtain ⟨u, -, hu⟩ := PI.OddDualWeyl.highestWeightDual_of PI.OddDualWeyl.jacobiMinorReverse R m lam hlam
      refine ⟨C u * PI.OddDualWeyl.low R (PI.OddDualWeyl.nuOf (lamStar lam)), ?_, hu⟩
      rw [MvPolynomial.C_mul']
      exact Submodule.smul_mem _ u (PI.OddDualWeyl.lowestWeightMem R (m + 1) _)
    | cons x w ih =>
      obtain ⟨hMH, f', hf', hrel⟩ := ih
      rw [PI.OddDualWeyl.applyWord_cons]
      refine ⟨PI.OddDualWeyl.highest_weight_divisibility R (m + 1) _ _ _ _ hMH, ?_⟩
      by_cases hab : x.1 = x.2.1
      · obtain ⟨d, hd⟩ := hMH x.1
        have hdiag := PI.OddDualWeyl.hermitianDiagonalization R (m + 1) x.1 x.2.2 d _ hd
        rw [← hab, hdiag]
        refine ⟨(d.choose x.2.2 : MvPolynomial _ R) * f', ?_, PI.OddDualWeyl.rel_natMul _ hrel⟩
        rw [← nsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ _ hf'
      · refine ⟨(-1) ^ x.2.2 * PI.OddDualWeyl.rowDiv R x.2.1 x.1 x.2.2 f', ?_,
          PI.OddDualWeyl.rowOpIntertwining R (m + 1) _ x.1 x.2.1 x.2.2 _ _ hab hrel⟩
        have hm := PI.OddDualWeyl.weyl_rowDiv x.2.1 x.1 x.2.2 hf'
        rcases neg_one_pow_eq_or (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) x.2.2 with h | h
        · rw [h, one_mul]
          exact hm
        · rw [h, neg_one_mul]
          exact Submodule.neg_mem _ hm
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w, rfl⟩ := hg
    exact (hgen w).2
  | zero => exact ⟨0, Submodule.zero_mem _, PI.OddDualWeyl.rel_zero⟩
  | add g h _ _ hg hh =>
    obtain ⟨g', hg', hrg⟩ := hg
    obtain ⟨h', hh', hrh⟩ := hh
    exact ⟨g' + h', Submodule.add_mem _ hg' hh', PI.OddDualWeyl.rel_add hrg hrh⟩
  | smul c g _ hg =>
    obtain ⟨g', hg', hrg⟩ := hg
    exact ⟨c • g', Submodule.smul_mem _ c hg', PI.OddDualWeyl.rel_smul c hrg⟩

theorem oddStep : PI.BlockRatReal.OddStep := by
  intro m LL _ embLL lam hlam M0 f hf
  have hf0 : f ∈ PI.OddDualWeyl.weyl ℤ (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf lam) := hf
  obtain ⟨f', hf', hrel⟩ := exists_weyl_lamStar_rel_of_mem_weyl ℤ m lam hlam f hf0
  have hstar : Antitone (lamStar lam) := PI.OddDualWeyl.antitone_lamStar hlam
  have hν : Antitone (PI.BlockRatReal.nuOf (fun i : Fin (m + 1) => -lam i.rev)) := by
    intro i j hij
    exact Int.toNat_le_toNat (sub_le_sub_right (hstar hij) _)
  set e' : ℤ := -lam (Fin.last m).rev with he'
  set c : LL := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' * sgnK LL m ^ e' with hc
  refine ⟨C c * Formalism.GradedWeylDivisibility.rowAct LL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ
    (MvPolynomial.map (Int.castRingHom LL) f'), ?_, ?_⟩
  · rw [MvPolynomial.C_mul']
    refine Submodule.smul_mem _ c ?_
    exact PI.BlockRatReal.UnitaryGroupMassFormula.s2 _ _ _ _
      (PI.BlockRatReal.UnitaryGroupMassFormula.s1 (Int.castRingHom LL) (m + 1) _ hν f' hf')
  · intro y hy
    have hdet0 : IsUnit (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
    set Mc := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL with hMc
    have hdetMc : Mc.det = embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have ha : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ≠ 0 :=
      (map_ne_zero embLL).mpr hdet0.ne_zero
    have hU : IsUnit Mc.det := by
      rw [hdetMc]
      exact isUnit_iff_ne_zero.mpr ha
    have hz : revCol ((Mc * y)⁻¹ᵀ) = Mc⁻¹ᵀ * revCol y⁻¹ᵀ := by
      rw [Matrix.mul_inv_rev, Matrix.transpose_mul, revCol_eq (Mc⁻¹ᵀ * y⁻¹ᵀ), revCol_eq y⁻¹ᵀ,
        Matrix.mul_assoc]
    have hz' : ((Mc * y)⁻¹ᵀ).submatrix id Fin.rev = Mc⁻¹ᵀ * revCol y⁻¹ᵀ := hz
    have hg : ((M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ).map embLL * Mc⁻¹ᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU,
        Matrix.transpose_one]
    have hev := PI.OddDualWeyl.evalDuality ℂ m (lam (Fin.last m)) e'
      (PI.OddDualWeyl.degW (PI.OddDualWeyl.nuOf (lamStar lam))) (expM lam)
      (MvPolynomial.map (Int.castRingHom ℂ) f) (MvPolynomial.map (Int.castRingHom ℂ) f')
      (PI.OddDualWeyl.degreeBalance m lam hlam)
      (rel_map (Int.castRingHom ℂ) (m + 1) _ f f' hrel)
      ((PI.OddDualWeyl.weight_homomorphism ℤ (m + 1) _ f' hf').map (Int.castRingHom ℂ)) y hy
    rw [hev]
    rw [map_mul, map_C, map_mul, eval_C, PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct, hz',
      ← Matrix.mul_assoc, hg, Matrix.one_mul, PI.BlockRatReal.UnitaryGroupMassFormula.map_map_int]
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, hdetMc, Ring.inverse_eq_inv']
    rw [hc]
    simp only [map_mul, eval_C, map_zpow₀, sgnK_map]
    rw [mul_zpow, _root_.inv_zpow]
    have hA : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' ≠ 0 := zpow_ne_zero _ ha
    calc _ = ((embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e')⁻¹ *
          embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e') *
          ((revCol y⁻¹ᵀ).det ^ e' * (sgnK ℂ m ^ e' *
            (eval fun x => revCol y⁻¹ᵀ x.1 x.2) ((MvPolynomial.map (Int.castRingHom ℂ)) f'))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_mul]

end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.NuOfAntitone
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula

theorem nuOf_antitone {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro a b hab
  have h1 := h hab
  exact Int.toNat_le_toNat (by omega)

theorem det_map_ne {LL : Type} [Field LL] (embLL : LL →+* ℂ) {k : ℕ} (M0 : GL (Fin k) LL) :
    (M0.1.map embLL).det ≠ 0 := by
  have hu : IsUnit M0.1.det := (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
  have hm := RingHom.map_det embLL M0.1
  rw [RingHom.mapMatrix_apply] at hm
  rw [← hm]
  exact (map_ne_zero embLL).mpr hu.ne_zero

theorem evenStep : EvenStep := by
  intro m LL _ embLL lam hl M0 f hf
  refine ⟨C (M0.1.det ^ (-lam (Fin.last m))) * Formalism.GradedWeylDivisibility.rowAct LL (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)
    (MvPolynomial.map (Int.castRingHom LL) f), ?_, fun y _ => ?_⟩
  · rw [MvPolynomial.C_mul']
    exact Submodule.smul_mem _ _ (s2 _ _ _ _ (s1 _ _ _ (nuOf_antitone hl) f hf))
  · have hd := det_map_ne embLL M0
    have hmul : (↑M0⁻¹ : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL * (M0.1.map embLL * y) = y := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, M0.inv_mul, Matrix.map_one embLL (map_zero _) (map_one _),
        Matrix.one_mul]
    have hc : embLL (M0.1.det ^ (-lam (Fin.last m))) = (M0.1.map embLL).det ^ (-lam (Fin.last m)) := by
      rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [map_mul, map_C, eval_mul, eval_C, eval_map_rowAct, hmul, map_map_int, hc, Matrix.det_mul, mul_zpow,
      _root_.zpow_neg]
    field_simp

end PI.BlockRatReal.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.AntitoneStar
open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal

theorem reM_rfl {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) : reM (m := m) rfl A = A := by
  ext i j
  rfl

theorem detShift_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by
  rw [detShift, dite_eq_left (Nat.succ_pos m)]
  rfl

theorem natW_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : natW w = nuOf w := by
  funext i
  rw [natW, nuOf, detShift_eq]

theorem antitone_star {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone fun i : Fin (m + 1) => -lam i.rev :=
  fun _ _ hij => neg_le_neg (h (Fin.rev_le_rev.mpr hij))

theorem stmt_of (hE : EvenStep) (hO : OddStep) : Stmt := by
  intro nV n' m lam0 Tau _ n LL _ h pos G M embLL lam hanti htie hM
  subst h
  intro v s f hf
  set τ := pos ⟨v, s⟩ with hτ
  have hl : lam0 v s = lam τ := funext fun i => by rw [htie v s i]; rfl
  obtain ⟨M0, hM0⟩ := hM τ
  have hf' : f ∈ weyl ℤ (m + 1) (m + 1) le_rfl (nuOf (lam τ)) := by
    rw [← natW_eq]; exact hf
  by_cases hs : Even s.val
  · have hla : lamAt (lam0 v) s = lam τ := by rw [lamAt, if_pos hs, hl]
    obtain ⟨F, hF, hFe⟩ := hE m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (hanti τ)]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_pos hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1
  · have hla : lamAt (lam0 v) s = fun i => -lam τ i.rev := by rw [lamAt, if_neg hs, hl]
    obtain ⟨F, hF, hFe⟩ := hO m LL embLL (lam τ) (hanti τ) M0 f hf'
    refine ⟨F, ?_, fun y => ?_⟩
    · rw [blkMod, hla, if_pos (antitone_star (hanti τ))]; exact hF
    · have h1 := hFe (y.1 τ) (y.2 τ)
      rw [zAt, if_neg hs, reM_rfl, eAt, hla, detShift_eq, hM0]
      exact h1

end PI.BlockRatReal
end
end

theorem blockRatReal : PI.BlockRatReal.Stmt :=
  PI.BlockRatReal.stmt_of PI.BlockRatReal.UnitaryGroupMassFormula.evenStep PI.BlockRatReal.UnitaryGroupMassFormula.Odd.oddStep
