module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.Count.FrameMajorant

theorem signed_cs {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ Formalism.HermitianLatticesTheory.cnorm a * Formalism.HermitianLatticesTheory.cnorm b := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have h1 : ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    simp only [Jm, Matrix.mulVec_diagonal, norm_mul, Pi.star_apply, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem cnorm_unitary {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm a := by
  have key : ∀ c : Fin n → ℂ, ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ c := by
    intro c
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have : star (u *ᵥ a) ⬝ᵥ (u *ᵥ a) = star a ⬝ᵥ a := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (this.trans (key _).symm)

theorem cnorm_inv_mul_unitary {n : ℕ} (X u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((X * u)⁻¹ *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ a) := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu, ← Matrix.mulVec_mulVec]
  apply cnorm_unitary
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hu

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  refine ⟨fun w w' h => ?_, ?_⟩
  · have hw : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases Test.embedding_cases I w with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h' : w.comap (algebraMap I.F I.E) = w'.comap (algebraMap I.F I.E) := h
    rw [hw w, hw w', h']
  · intro v
    refine ⟨InfinitePlace.mk (I.φ v), ?_⟩
    have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
    show (InfinitePlace.mk (I.φ v)).comap _ = v
    rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem frm_unit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h := congrArg (fun M => (Jm (I.ε (w.comap (algebraMap I.F I.E))) * M).det) (Test.frm_frame I x w)
  simp only [Jm_mul_self, Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at h

theorem hform_le (x : I.GA) (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤
      Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z := by
  have hc := I.cm.cmUnram.2.1
  have hX := frm_unit I x w
  have hback : ∀ y, frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => w.embedding (y i) := by
    intro y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [h1, ← hback y, ← hback z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Test.frm_frame I x w]
  exact signed_cs _ _ _

theorem normAt_mul (x : I.GA) (w : InfinitePlace I.E) (k : I.GA) (hk : ∀ v, uMat (k.1 v) ∈ Kset (I.ε v))
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  set v := w.comap (algebraMap I.F I.E) with hv
  have hu : (uMat (k.1 v))ᴴ * uMat (k.1 v) = 1 := (hk v).1.1
  have hm : uMat ((x * k).1 v) = uMat (x.1 v) * uMat (k.1 v) := rfl
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord frm
  simp only [← hv]
  split_ifs with h
  · rw [hm, ← Matrix.mul_assoc]
    exact cnorm_inv_mul_unitary _ _ hu _
  · rw [hm, ← Matrix.mul_assoc, Matrix.map_mul]
    apply cnorm_inv_mul_unitary
    have hT : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
      intro M; ext i j; simp
    rw [hT, ← Matrix.map_mul, hu]
    simp

theorem frames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  intro I x
  refine ⟨I.cm.cmUnram.1, ?_, card_places I, comap_bijective I, fun w =>
    ⟨frm_unit I x w, Test.frm_frame I x w, hform_le I x w, normAt_mul I x w⟩⟩
  rw [nPl, Fintype.card_of_bijective (comap_bijective I), card_places]

end GlobalTheory.Count.FrameMajorant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorantsStatement
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autPointMajorantFrames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  first | exact @GlobalTheory.Count.FrameMajorant.frames_give_majorants | exact GlobalTheory.Count.FrameMajorant.frames_give_majorants | (intros; apply GlobalTheory.Count.FrameMajorant.frames_give_majorants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParBasic

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem tl_apply (M : Mt g (a + b)) (i j : Fin a) : tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply (M : Mt g (a + b)) (i j : Fin b) : br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

def blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def ur (a b : ℕ) (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

theorem tl_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : tl a (blkM A B D) = A := by
  ext i j; simp [tl_apply, blkM]

theorem br_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : br a b (blkM A B D) = D := by
  ext i j; simp [br_apply, blkM]

theorem ur_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : ur a b (blkM A B D) = B := by
  ext i j; simp [ur, blkM]

theorem inPar_iff (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have := h ⟨i - a, by omega⟩ ⟨j, hj⟩
    convert this using 2 <;> ext <;> simp
    omega

theorem inPar_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : InPar a (blkM A B D) := by
  rw [inPar_iff]
  intro i j; simp [blkM]

theorem blkM_eq {M : Mt g (a + b)} (h : InPar a M) : blkM (tl a M) (ur a b M) (br a b M) = M := by
  rw [inPar_iff] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkM, tl_apply, br_apply, ur, h]

theorem det_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (blkM A B D).det = A.det * D.det := by
  rw [blkM, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem isUnit_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    IsUnit (blkM A B D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [Matrix.isUnit_iff_isUnit_det, det_blkM, IsUnit.mul_iff]

theorem blkM_mul (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    blkM A B D * blkM A' B' D' = blkM (A * A') (A * B' + B * D') (D * D') := by
  rw [blkM, blkM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [blkM]

theorem isUnit_blocks (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    IsUnit (tl a (x : Mt g (a + b))) ∧ IsUnit (br a b (x : Mt g (a + b))) := by
  rw [← isUnit_blkM _ (ur a b x.val), blkM_eq h]
  exact x.isUnit

theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := blkM_mul (tl a x) (tl a y) (ur a b x) (ur a b y) (br a b x) (br a b y)
  rw [blkM_eq hx, blkM_eq hy] at e
  rw [e]
  exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩

theorem exists_subgroup {G : Type} [Group G] [Finite G] (p : G → Prop) (h1 : p 1)
    (hm : ∀ x y, p x → p y → p (x * y)) : ∃ P : Subgroup G, ∀ x, x ∈ P ↔ p x := by
  have hp : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := fun x hx k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hm _ _ ih hx
  refine ⟨{ carrier := {x | p x}, mul_mem' := fun {x y} => hm x y, one_mem' := h1, inv_mem' := fun {x} hx => ?_ },
    fun x => Iff.rfl⟩
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    have h0 := orderOf_pos x
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  change p x⁻¹
  rw [this]
  exact hp x hx _

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j hj hi =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem card_fibre (h₁ : Gn g a) (h₂ : Gn g b) :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b)) ∧
      tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)).card = g ^ (a * b) := by
  have hc : (Finset.univ : Finset (Matrix (Fin a) (Fin b) (ZMod g))).card = g ^ (a * b) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin b → ZMod g) = _
    simp [pow_mul']
  rw [← hc]
  refine Finset.card_bij (fun x _ => ur a b x.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x hx y hy h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply Units.ext
    rw [← blkM_eq hx.1, ← blkM_eq hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, h]
  · intro B _
    have hu := (isUnit_blkM h₁.val B h₂.val).2 ⟨h₁.isUnit, h₂.isUnit⟩
    refine ⟨hu.unit, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsUnit.unit_spec]
      exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩
    · simp only [IsUnit.unit_spec, ur_blkM]

theorem toG_val {n : ℕ} {M : Mt g n} (h : IsUnit M) : (toG M).val = M := by
  rw [toG, dif_pos h, IsUnit.unit_spec]

theorem card_par :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b))).card =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Gn g a × Gn g b)))
    (f := fun x : Gn g (a + b) => (toG (tl a x.val), toG (br a b x.val))) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (g := fun _ => g ^ (a * b))]
  · simp
  · rintro ⟨h₁, h₂⟩ _
    rw [← card_fibre h₁ h₂, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => and_congr_right fun hx => ?_
    have hu := isUnit_blocks x hx
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := fun _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem isUniUp_mul {n : ℕ} (x y : Mt g n) (hx : IsUniUp x) (hy : IsUniUp y) : IsUniUp (x * y) := by
  intro i j
  refine ⟨fun h => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hx i k).1 hk, zero_mul]
    · rw [(hy k j).1 (h.trans_le (not_lt.1 hk)), mul_zero]
  · rintro rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single i, (hx i i).2 rfl, (hy i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hx i k).1 h, zero_mul]
      · rw [(hy k i).1 h, mul_zero]
    · simp

theorem par_basic : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  intro g _ a b n hn
  subst hn
  exact ⟨exists_subgroup _ (inPar_one _ _) fun x y hx hy => (blocks_mul _ _ hx hy).1,
    exists_subgroup _ (isUniUp_one _) fun x y hx hy => isUniUp_mul _ _ hx hy,
    isUnit_blocks, fun x y hx hy => (blocks_mul x y hx hy).2, card_fibre, card_par⟩

end GlobalTheory.GLm.ParBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  first | exact @GlobalTheory.GLm.ParBasic.par_basic | exact GlobalTheory.GLm.ParBasic.par_basic | (intros; apply GlobalTheory.GLm.ParBasic.par_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapFnOfEqValC
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ValueSpaceCoordinates

theorem rowAct_mem_delSq {n : ℕ} (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ delSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam := by
  have hanti : Antitone lam.natW := by
    intro i j hij
    have h := lam.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hw := Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti
  change p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp
  change Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW
  rw [← hw] at hp ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  have key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).toRingHom =
      MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
  simpa using RingHom.congr_fun key p

theorem eval_ten {ι : Type} [Fintype ι] {n : ℕ} (x : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : ι × Fin n × Fin n => x v.1 v.2.1 v.2.2) (ten f) =
      ∏ τ, MvPolynomial.eval (fun v : Fin n × Fin n => x τ v.1 v.2) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename]
  rfl

theorem fnOf_mul_ten {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A B : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fnOf G s (A * B) (ten f) =
      (∏ τ, (A τ).det ^ s τ) • fnOf G s B (ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ)) := by
  ext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [eval_ten (fun τ => (A * B) τ * y.1 τ) f,
    eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]
  simp only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow,
    Finset.prod_mul_distrib]
  ring

theorem map_fnOf_mul_le {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (A B : ι → Matrix (Fin n) (Fin n) ℂ) :
    (CSpan lam).map (fnOf G s (A * B)) ≤ (CSpan lam).map (fnOf G s B) := by
  unfold CSpan
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨q, ⟨f, hf, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, fnOf_mul_ten]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span
    ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))

theorem map_fnOf_eq_ValC :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G M : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (M τ).det) → (CSpan lam).map (fnOf G (shiftOf lam) M) = ValC G lam := by
  intro ι _ n lam G M hM
  have hinv : (fun τ => (M τ)⁻¹) * M = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.one_apply]
    exact Matrix.nonsing_inv_mul (M τ) (hM τ)
  unfold ValC
  apply le_antisymm
  · have h := map_fnOf_mul_le lam G (shiftOf lam) M 1
    rwa [mul_one] at h
  · have h := map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M
    rwa [hinv] at h

end GlobalTheory.ValueSpaceCoordinates
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff Topology

noncomputable section

namespace GlobalTheory.SmoothVecMod

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]

section Gen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (h : ∀ g, inUJ ε g → f' g = f g) : SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgJ => (h g hgJ).trans (hfF g hg hgJ)⟩

lemma smooth_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) : SmoothOnGV ε (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c), ?_⟩
  intro x hx hxJ
  show f x + c • f' x = F x + c • F' x
  rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]

lemma smooth_zero : SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) :=
  fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma rdV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) : RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact h _ (indefinite_unitary_mul_mem ε hg (exp_indefinite_unitary_holds n ε X hX t))

lemma eabV_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b f g = EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [rdV_congr h h1 hg, rdV_congr h h2 hg]

lemma eabV_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n) :
    SmoothOnGV ε (EabV ε a b f) := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  exact smooth_comb (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h1)
    (rdSmoothV_of vector_right_derivative_extends n ε E f _ hf h2) Complex.I

lemma eabV_comb {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    (hf' : SmoothOnGV ε f') (c : ℂ) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    EabV ε a b (fun g => f g + c • f' g) g = EabV ε a b f g + c • EabV ε a b f' g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [(rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h1 h1 hg).2.2,
    (rdLinV_of vector_right_derivative_extends n ε E f f' _ _ 0 c g hf hf' h2 h2 hg).2.2]
  module

lemma hasDerivAt_rdV {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) (RdV X f 1) 0 := by
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 inUJ_one
  have hγ := hasDerivAt_mul_exp_smul_zero (1 : Matrix (Fin n) (Fin n) ℂ) X
  have hγ0 : (1 : Matrix (Fin n) (Fin n) ℂ) * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F 1 (1 * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (1 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, 1 * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    rw [Matrix.one_mul] at ht ⊢
    exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)
  rw [vector_right_derivative_extends n ε E f F U 1 X hU hg inUJ_one hF hfF hX]
  exact hcomp.congr_of_eventuallyEq hev

end Gen

section Rep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma rep_rdV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    σ g (RdV X (fun x => σ x u) 1) = RdV X (fun x => σ x u) g := by
  rw [(rdVPair_of vector_right_derivative_extends n ε H H (σ g) _ X 1 hu hX inUJ_one).2,
    rdV_congr (f' := fun x => σ (g * x) u) (fun x hx => by
      rw [hσ.1.2 g hg x hx]; rfl) hX inUJ_one,
    vector_right_derivative_left_invariant n H (fun x => σ x u) X g 1, Matrix.mul_one]

lemma rep_eabV (hσ : IsURepOn (UJset ε) σ) {u : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (EabV ε a b (fun x => σ x u) 1) = EabV ε a b (fun x => σ x u) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, rep_rdV hσ hu h1 hg, rep_rdV hσ hu h2 hg]

lemma rep_inner (hσ : IsURepOn (UJset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (u v : H) : ⟪σ g u, σ g v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨(σ g : H →ₗ[ℂ] H), hσ.2.1 g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

lemma rep_skew (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ⟪RdV X (fun x => σ x u) 1, v⟫_ℂ = -⟪u, RdV X (fun x => σ x v) 1⟫_ℂ := by
  have h := (hasDerivAt_rdV hu hX).inner ℂ (hasDerivAt_rdV hv hX)
  have e : (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • X)) u,
      σ (NormedSpace.exp ((t : ℂ) • X)) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ := by
    funext t
    exact rep_inner hσ (exp_indefinite_unitary_holds n ε X hX t) u v
  rw [e] at h
  have h0 := h.unique (hasDerivAt_const _ _)
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply] at h0
  linear_combination h0

lemma rep_unit (hσ : IsURepOn (UJset ε) σ) {u v : H} (hu : SmoothOnGV ε (fun g => σ g u))
    (hv : SmoothOnGV ε (fun g => σ g v)) (a b : Fin n) :
    ⟪EabV ε a b (fun x => σ x u) 1, v⟫_ℂ =
      (sgn ε a b : ℂ) * ⟪u, EabV ε b a (fun x => σ x v) 1⟫_ℂ := by
  obtain ⟨k1, k2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [inner_add_left, inner_smul_left, rep_skew hσ hu hv k1, rep_skew hσ hu hv k2]
  have hab := p0auxiliary_theta_single ε a b
  have hba := p0auxiliary_theta_single ε b a
  have hs : sgn ε b a = sgn ε a b := by unfold sgn; by_cases h : ε a = ε b <;> simp [h, eq_comm]
  rw [hs] at hba
  by_cases h : ε a = ε b
  · have h1 : sgn ε a b = 1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = -cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; module
    have c2 : cpart2 ε (Matrix.single b a 1) = cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; simp only [Complex.ofReal_one, one_smul]; rw [add_comm]
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
  · have h1 : sgn ε a b = -1 := by simp [sgn, h]
    rw [h1] at hab hba
    have c1 : cpart1 ε (Matrix.single b a 1) = cpart1 ε (Matrix.single a b 1) := by
      unfold cpart1; rw [hab, hba]; push_cast; module
    have c2 : cpart2 ε (Matrix.single b a 1) = -cpart2 ε (Matrix.single a b 1) := by
      unfold cpart2; rw [hab, hba]; push_cast; module
    rw [c1, c2, p0auxiliary_rdV_neg, h1, inner_add_right, inner_smul_right, inner_neg_right]
    simp [Complex.conj_I]
    ring

def smoothVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := {u | SmoothOnGV ε (fun g => σ g u)}
  zero_mem' := smooth_congr smooth_zero (fun g _ => map_zero _)
  add_mem' := fun hu hv => smooth_congr (smooth_comb hu hv 1) (fun g _ => by simp)
  smul_mem' := fun c _ hu => smooth_congr (smooth_comb smooth_zero hu c) (fun g _ => by simp)

def unitAct (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) : Module.End ℂ (smoothVec ε σ) where
  toFun u := ⟨EabV ε a b (fun x => σ x u) 1,
    smooth_congr (eabV_smooth u.2 a b) (fun _ hg => rep_eabV hσ u.2 a b hg)⟩
  map_add' u v := by
    apply Subtype.ext
    have h := eabV_comb u.2 v.2 1 a b (inUJ_one (ε := ε))
    simp only [one_smul] at h
    simpa using h
  map_smul' c u := by
    apply Subtype.ext
    have h := eabV_comb smooth_zero u.2 c a b (inUJ_one (ε := ε))
    have h0 : EabV ε a b (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : H)) 1 = 0 := by
      simp [EabV, EcV, RdV]
    simp only [zero_add, h0] at h
    simpa using h

lemma unitAct_coe (hσ : IsURepOn (UJset ε) σ) (a b : Fin n) (u : smoothVec ε σ) :
    (unitAct hσ a b u : H) = EabV ε a b (fun x => σ x u) 1 := rfl

end Rep

theorem smoothVec_unitary_module : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∃ (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs), (∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g := by
  intro n ε H _ _ _ σ hσ
  have key : ∀ a b (u : smoothVec ε σ), ∀ g ∈ UJset ε,
      σ g (unitAct hσ a b u) = EabV ε a b (fun g => σ g u) g :=
    fun a b u g hg => rep_eabV hσ u.2 a b hg
  refine ⟨smoothVec ε σ, unitAct hσ, fun _ => Iff.rfl, ?_, ?_, ?_, key⟩
  · intro a b c d
    ext u
    have h := eabGlV_of (rdLinV_of vector_right_derivative_extends)
      (rdBracketV_of vector_right_derivative_extends (rdSmoothV_of vector_right_derivative_extends)) (rdSmoothV_of vector_right_derivative_extends)
      n ε H (fun g => σ g u) a b c d 1 u.2 inUJ_one
    rw [← eabV_congr (key c d u) a b inUJ_one, ← eabV_congr (key a b u) c d inUJ_one] at h
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [unitAct_coe hσ a b, unitAct_coe hσ c d (unitAct hσ a b u), h]
    split_ifs <;> simp [unitAct_coe]
  · intro a b x y
    exact rep_unit hσ x.2 y.2 a b
  · intro X hX u
    have h := ecSumV_of (rdLinV_of vector_right_derivative_extends) n ε H (fun g => σ g u) X 1 u.2 inUJ_one
    obtain ⟨c1, c2⟩ := (complex_parts_mem_lie_algebra_holds n ε X).2.2.2 hX
    have h0 : RdV (0 : Matrix (Fin n) (Fin n) ℂ) (fun g => σ g u) 1 = 0 := by simp [RdV]
    unfold EcV at h
    rw [c1, c2, h0, smul_zero, add_zero] at h
    have e : ((∑ a, ∑ b, X a b • unitAct hσ a b u : smoothVec ε σ) : H) =
        RdV X (fun g => σ g u) 1 := by
      rw [h]
      simp [unitAct_coe]
    rw [e]
    exact hasDerivAt_rdV u.2 hX

end GlobalTheory.SmoothVecMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlace
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.mem_hat_iff_forall_loc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  intro F E _ _ _ _ _ n L hL x
  haveI := hL.1
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff L x
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlaceStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  first | exact @GlobalTheory.St.G.mem_hat_iff_forall_loc | exact GlobalTheory.St.G.mem_hat_iff_forall_loc | (intros; apply GlobalTheory.St.G.mem_hat_iff_forall_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTrivialPointwise
open NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NearLowerCompare

open Formalism.MainNotions.S GlobalTheory.Count Formalism.HN

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)

end General

variable (I : AutInst)

theorem lamX_isLattice (x : I.GA) : Submodule.IsLattice I.E (lamX I x) := by
  have h := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  have e : lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
    ext y
    rw [GlobalTheory.Count.Test.mem_lamX, ← e1]
    exact Iff.rfl
  rw [e]; exact h

theorem frm_isUnit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h : ∀ v, IsUnit (I.P v * uMat (x.1 v)) := fun v => (I.P_unit v).mul (Units.isUnit _)
  rw [← Matrix.isUnit_iff_isUnit_det]
  unfold frm
  split_ifs
  · exact h _
  · exact (h _).map (starRingEnd ℂ).mapMatrix

theorem subsingleton_GA (hn : I.n = 0) : Subsingleton I.GA := by
  have : IsEmpty (Fin I.n) := by rw [hn]; infer_instance
  refine ⟨fun a b => Prod.ext (funext fun v => ?_) ?_⟩
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

end GlobalTheory.NearLowerCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpSetBaseChange
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.PerpBaseChange

private theorem dual_span_sum_eq_zero {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    ∀ ψ ∈ Submodule.span E S, ∑ j, ι (ψ (Pi.single j 1)) * u j = 0 := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [LinearMap.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

theorem mem_span_of_forms {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' {y | ∀ φ ∈ S, φ y = 0}) := by
  classical

  set D : Submodule E (Module.Dual E (Fin n → E)) := Submodule.span E S with hD
  set K : Submodule E (Fin n → E) := D.dualCoannihilator with hK
  have hKset : ∀ y, y ∈ K ↔ ∀ φ ∈ S, φ y = 0 := by
    intro y
    rw [hK, Submodule.mem_dualCoannihilator]
    constructor
    · intro h φ hφ
      exact h φ (Submodule.subset_span hφ)
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set P : (Fin n → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ g with hP
  have hPK : ∀ y, P y ∈ K := fun y => (g y).2
  have hPid : ∀ k ∈ K, P k = k := by
    intro k hk
    have h1 := LinearMap.congr_fun hg ⟨k, hk⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h1
    simp [hP, h1]

  have hrow : ∀ i, (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈ D := by
    intro i
    have hmem : (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈
        K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      simp [hPid k hk]
    rwa [hK, Subspace.dualCoannihilator_dualAnnihilator_eq] at hmem
  have hcoord : ∀ i, u i = ∑ j, ι (P (Pi.single j 1) i) * u j := by
    intro i
    have h0 := dual_span_sum_eq_zero ι S u hu _ (hrow i)
    simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, map_sub, sub_mul,
      Finset.sum_sub_distrib, sub_eq_zero] at h0
    rw [← h0]
    simp [Pi.single_apply]
  have hu' : u = ∑ j, u j • (fun i => ι (P (Pi.single j 1) i)) := by
    funext i
    rw [hcoord i]
    simp [Finset.sum_apply, mul_comm]
  rw [hu']
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨P (Pi.single j 1), ?_, rfl⟩)
  exact (hKset _).1 (hPK _)

def formRight {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w : Fin n → E) : Module.Dual E (Fin n → E) where
  toFun y := Formalism.UG.hform σ J w y
  map_add' y z := by simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem formRight_apply {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w y : Fin n → E) : formRight σ J w y = Formalism.UG.hform σ J w y := rfl

private theorem hform_add_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hform_smul_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J x (c • y) = c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem hform_add_left_flag_measures' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x x' y : Fin n → A) :
    Formalism.UG.hform s J (x + x') y = Formalism.UG.hform s J x y + Formalism.UG.hform s J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

private theorem hform_smul_left_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J (c • x) y = s c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perpSet_baseChange : ∀ (E A : Type) [Field E] [CommRing A] (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (W : Submodule E (Fin n → E)), (∀ e, s (ι e) = ι (σ e)) → perpSet s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E)))) = (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' perpSet σ J W) : Set (Fin n → A)) := by
  intro E A _ _ σ s ι n J W hs
  classical

  have key : ∀ w z : Fin n → E, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) (fun i => ι (z i)) =
      ι (Formalism.UG.hform σ J w z) := by
    intro w z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, Matrix.map_apply, hs, map_sum, map_mul]

  have pair : ∀ (w : Fin n → E) (y : Fin n → A), Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y =
      ∑ j, ι (formRight σ J w (Pi.single j 1)) * y j := by
    intro w y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [formRight_apply, Formalism.UG.hform, Matrix.map_apply, hs, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have hset : {z : Fin n → E | ∀ φ ∈ formRight σ J '' (W : Set (Fin n → E)), φ z = 0} = perpSet σ J W := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, perpSet, formRight_apply, SetLike.mem_coe]
  ext y
  constructor
  · intro hy
    rw [SetLike.mem_coe, ← hset]
    apply mem_span_of_forms ι _ y
    rintro φ ⟨w, hw, rfl⟩
    rw [← pair]
    exact hy _ (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro hy
    rw [SetLike.mem_coe] at hy
    have hgen : ∀ w ∈ W, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y = 0 := by
      intro w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        rw [key, hz w hw, map_zero]
      | zero => simp [Formalism.UG.hform]
      | add x x' _ _ hx hx' => rw [hform_add_right_flag_measures, hx, hx', add_zero]
      | smul c x _ hx => rw [hform_smul_right_flag_measures, hx, mul_zero]
    simp only [perpSet, Set.mem_setOf_eq]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp [Formalism.UG.hform]
    | add x x' _ _ hx hx' => rw [hform_add_left_flag_measures', hx, hx', add_zero]
    | smul c x _ hx => rw [hform_smul_left_flag_measures, hx, mul_zero]

end GlobalTheory.PerpBaseChange
end
