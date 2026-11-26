module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNode

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairing
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermCoord

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] {r : ℕ}

def ct (σ : E →ₐ[F] E) (b : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  (b.map σ)ᵀ

def hermF (σ : E →ₐ[F] E) (r : ℕ) : Submodule F (Matrix (Fin r) (Fin r) E) where
  carrier := {b | ct σ b = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [ct, Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    rw [Matrix.add_apply, map_add (f := _), h1, h2, Matrix.add_apply]
  zero_mem' := by
    refine Matrix.ext fun i j => ?_
    simp [ct]
  smul_mem' := by
    intro c b hb
    simp only [Set.mem_setOf_eq] at *
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hb i) j
    simp only [ct, Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    rw [Matrix.smul_apply, map_smul, h1, Matrix.smul_apply]

def tF (a b : Matrix (Fin r) (Fin r) E) : F :=
  (1 / 2) * Algebra.trace F E (Matrix.trace (a * b))

theorem tF_comm (a b : Matrix (Fin r) (Fin r) E) : (tF a b : F) = tF b a := by
  rw [tF, tF, Matrix.trace_mul_comm]

def tB (σ : E →ₐ[F] E) : LinearMap.BilinForm F (hermF σ r) :=
  LinearMap.mk₂ F (fun a b => tF a.1 b.1)
    (fun a b c => by
      simp only [tF, Submodule.coe_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _), mul_add])
    (fun c a b => by
      simp only [tF, Submodule.coe_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]
      ring)
    (fun a b c => by
      simp only [tF, Submodule.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), mul_add])
    (fun c a b => by
      simp only [tF, Submodule.coe_smul, Matrix.mul_smul, Matrix.trace_smul, map_smul, smul_eq_mul]
      ring)

theorem tB_apply (σ : E →ₐ[F] E) (a b : hermF σ r) : tB σ a b = tF a.1 b.1 := rfl

variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]

theorem exists_tF_ne (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {h : Matrix (Fin r) (Fin r) E}
    (hh : ct σ h = h) (h0 : h ≠ 0) : ∃ k ∈ hermF σ r, (tF h k : F) ≠ 0 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, h i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Matrix.ext hc)
  obtain ⟨z, hz⟩ := Algebra.trace_surjective F E 1
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs : Algebra.trace F E (σ z) = Algebra.trace F E z := Algebra.trace_eq_of_algEquiv s z
  set m : Matrix (Fin r) (Fin r) E := Matrix.single j i (z * (h i j)⁻¹) with hm
  have hct : ct σ (ct σ m) = m := by
    refine Matrix.ext fun a b => ?_
    simp [ct, hσ]
  have hk : m + ct σ m ∈ hermF σ r := by
    refine Matrix.ext fun a b => ?_
    have e : ct σ (m + ct σ m) a b = σ (m b a) + σ (ct σ m b a) := by
      simp [ct]
    rw [e, Matrix.add_apply]
    have e2 : σ (ct σ m b a) = m a b := congrFun (congrFun hct a) b
    have e3 : σ (m b a) = ct σ m a b := rfl
    rw [e2, e3, add_comm]
  refine ⟨m + ct σ m, hk, ?_⟩
  have h1 : Matrix.trace (h * m) = z := by
    rw [hm, Matrix.trace_mul_single, op_smul_eq_mul, mul_comm z, ← mul_assoc, mul_inv_cancel₀ hij, one_mul]
  have h2 : Matrix.trace (h * ct σ m) = σ z := by
    have ht : ∀ X : Matrix (Fin r) (Fin r) E, Matrix.trace (ct σ X) = σ (Matrix.trace X) := fun X => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [ct, Matrix.trace, map_sum]
    have hmul : ct σ (m * h) = ct σ h * ct σ m := by
      simp only [ct]
      rw [Matrix.map_mul, Matrix.transpose_mul]
    have h3 : h * ct σ m = ct σ (m * h) := by rw [hmul, hh]
    rw [h3, ht, Matrix.trace_mul_comm, h1]
  rw [tF, Matrix.mul_add, Matrix.trace_add, h1, h2, map_add (f := _), hs, hz]
  norm_num

theorem tB_sep (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : hermF σ r)
    (h : ∀ b : hermF σ r, (tF a.1 b.1 : F) = 0) : a = 0 := by
  by_contra h0
  obtain ⟨k, hk, hne⟩ := exists_tF_ne σ hσ (r := r) a.2 (fun e => h0 (Subtype.ext e))
  exact hne (h ⟨k, hk⟩)

theorem tB_nondegenerate (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) :
    (tB σ : LinearMap.BilinForm F (hermF σ r)).Nondegenerate :=
  ⟨fun a h => tB_sep σ hσ a h, fun a h => tB_sep σ hσ a fun b => (tF_comm _ _).trans (h b)⟩

theorem exists_dual (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (r : ℕ) :
    ∃ (n : ℕ) (e e' : Fin n → Matrix (Fin r) (Fin r) E),
    (∀ i, ct σ (e i) = e i) ∧ (∀ i, ct σ (e' i) = e' i) ∧
    (∀ i j, (tF (e i) (e' j) : F) = if i = j then 1 else 0) ∧
    (∀ h : Matrix (Fin r) (Fin r) E, ct σ h = h → ∑ i, (tF (e' i) h : F) • e i = h) ∧
    (∀ h : Matrix (Fin r) (Fin r) E, ct σ h = h → ∑ i, (tF (e i) h : F) • e' i = h) := by
  classical
  let b := Module.finBasis F (hermF σ r)
  have hB := tB_nondegenerate (r := r) σ hσ
  let b' := (tB σ : LinearMap.BilinForm F (hermF σ r)).dualBasis hB b
  have hd : ∀ i j, (tF (b' i).1 (b j).1 : F) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hB b i j
  have hrep : ∀ x : hermF σ r, ∀ i, b.repr x i = tF (b' i).1 x.1 := by
    intro x i
    conv_rhs => rw [← b.sum_repr x]
    have : (tF (b' i).1 (∑ j, b.repr x j • b j : hermF σ r).1 : F) =
        tB σ (b' i) (∑ j, b.repr x j • b j) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · have := hd i i
      rw [tB_apply, this]; simp
    · intro j _ hj
      rw [tB_apply, hd, if_neg hj, mul_zero]
    · simp
  refine ⟨_, fun i => (b i).1, fun i => (b' i).1, fun i => (b i).2, fun i => (b' i).2, ?_, ?_, ?_⟩
  · intro i j
    rw [tF_comm, hd]
  · intro h hh
    have hx : (⟨h, hh⟩ : hermF σ r) = ∑ i, (tF (b' i).1 h : F) • b i := by
      conv_lhs => rw [← b.sum_repr ⟨h, hh⟩]
      exact Finset.sum_congr rfl fun i _ => by rw [hrep]
    simpa using congrArg Subtype.val hx.symm
  · intro h hh
    have hx : (⟨h, hh⟩ : hermF σ r) = ∑ i, (tF (b i).1 h : F) • b' i := by
      conv_lhs => rw [← b'.sum_repr ⟨h, hh⟩]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, tB_apply, tF_comm]
    simpa using congrArg Subtype.val hx.symm

end Field

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem sigR_smul_gen (σ : E →ₐ[F] E) (c : R) (x : R ⊗[F] E) : sigR R σ (c • x) = c • sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add (f := _), h1, h2, map_add (f := _), smul_add]

theorem alg_smul_tmul (c : F) (e : E) :
    algebraMap F R c • ((1 : R) ⊗ₜ[F] e) = (1 : R) ⊗ₜ[F] (c • e) := by
  rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul']

theorem smul_one_tmul (a : R) (e : E) : a • ((1 : R) ⊗ₜ[F] e) = a ⊗ₜ[F] e := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem hmid_herm {r : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (m : Matrix (Fin r) (Fin r) E) :
    ct σ ((1 / 2 : E) • (m + ct σ m)) = (1 / 2 : E) • (m + ct σ m) := by
  refine Matrix.ext fun i j => ?_
  have h2 : σ (2 : E) = 2 := map_ofNat σ 2
  simp [ct, hσ, add_comm, h2, mul_add]

end Gen

section Adelic

variable {D : D7} {r : ℕ}

def halfTrL (D : D7) : AE D →ₗ[AF D.host.F] AF D.host.F :=
  (algebraMap D.host.F (AF D.host.F) (1 / 2)) • Algebra.trace (AF D.host.F) (AE D)

def uL (m : Matrix (Fin r) (Fin r) D.host.E) : Mx D r r →ₗ[AF D.host.F] AF D.host.F :=
  (halfTrL D) ∘ₗ (Matrix.traceLinearMap (Fin r) (AF D.host.F) (AE D)) ∘ₗ
    (LinearMap.mulLeft (AF D.host.F) (rat m : Mx D r r))

theorem uL_apply (m : Matrix (Fin r) (Fin r) D.host.E) (x : Mx D r r) :
    uL m x = halfTr (Matrix.trace (HMul.hMul (rat m) x : Mx D r r)) := rfl

theorem trace_rat (M : Matrix (Fin r) (Fin r) D.host.E) :
    Matrix.trace (rat M : Mx D r r) = incA D (Matrix.trace M) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem uL_rat (m h : Matrix (Fin r) (Fin r) D.host.E) :
    uL m (rat h) = algebraMap D.host.F (AF D.host.F) (tF m h) := by
  rw [uL_apply]
  rw [← rat_mul, trace_rat, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, tF]

theorem algebraMap_smul_rat (c : D.host.F) (M : Matrix (Fin r) (Fin r) D.host.E) :
    algebraMap D.host.F (AF D.host.F) c • (rat M : Mx D r r) = rat (c • M) :=
  Matrix.ext fun i j => alg_smul_tmul (R := AF D.host.F) c (M i j)

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin r) (Fin r) D.host.E) :
    (rat (∑ i ∈ s, f i) : Mx D r r) = ∑ i ∈ s, rat (f i) :=
  map_sum ((incA D).toAddMonoidHom.mapMatrix (m := Fin r) (n := Fin r)) f s

theorem adj_rsmul (a : AF D.host.F) (x : Mx D r r) : adj (a • x) = a • adj x :=
  Matrix.ext fun i j => sigR_smul_gen (R := AF D.host.F) D.sp.cm.sig a (x j i)

set_option synthInstance.maxHeartbeats 400000 in
theorem hermPart_smul (a : AF D.host.F) (x : Mx D r r) :
    GlobalTheory.CompanionTheory.HermVol.hermPart D r (a • x) = a • GlobalTheory.CompanionTheory.HermVol.hermPart D r x := by
  rw [GlobalTheory.CompanionTheory.HermVol.hermPart, GlobalTheory.CompanionTheory.HermVol.hermPart, adj_rsmul, ← smul_add]
  exact Matrix.ext fun i j => mul_smul_comm a (half D) _

theorem hermPart_ratm (m : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.CompanionTheory.HermVol.hermPart D r (rat m) = rat ((1 / 2 : D.host.E) • (m + ct D.sp.cm.sig m)) := by
  rw [GlobalTheory.CompanionTheory.HermVol.hermPart, rat_smul, rat_add]; rfl

theorem single_tmul (i j : Fin r) (a : AF D.host.F) (e : D.host.E) :
    (Matrix.single i j (a ⊗ₜ[D.host.F] e) : Mx D r r) = a • rat (Matrix.single i j e) := by
  refine Matrix.ext fun k l => ?_
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply_same]
    exact (smul_one_tmul (R := AF D.host.F) a e).symm.trans (congrArg (a • ·) (by simp [rat]; rfl))
  · show Matrix.single i j (a ⊗ₜ[D.host.F] e) k l = a • incA D (Matrix.single i j e k l)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ h, Matrix.single_apply_of_ne _ _ _ _ _ h, map_zero, smul_zero]

theorem mx_induction {P : Mx D r r → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (a : AF D.host.F) (m : Matrix (Fin r) (Fin r) D.host.E), P (a • rat m)) (x : Mx D r r) : P x := by
  have hs : ∀ {ι : Type} (s : Finset ι) (f : ι → Mx D r r), (∀ i, P (f i)) → P (∑ i ∈ s, f i) := by
    classical
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact hadd _ _ (hf a) ih
  have h1 : ∀ (i j : Fin r) (z : AE D), P (Matrix.single i j z) := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a e => rw [single_tmul]; exact hgen a _
    | add z w hz hw => rw [Matrix.single_add]; exact hadd _ _ hz hw
  rw [Matrix.matrix_eq_sum_single x]
  exact hs _ _ fun i => hs _ _ fun j => h1 i j _

theorem sum_uL_smul {n : ℕ} (m m' : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (hm : ∀ h : Matrix (Fin r) (Fin r) D.host.E, ct D.sp.cm.sig h = h → ∑ i, (tF (m' i) h : D.host.F) • m i = h)
    {x : Mx D r r} (hx : x ∈ hermA D r) : ∑ i, uL (m' i) x • (rat (m i) : Mx D r r) = x := by
  have key : ∀ y : Mx D r r, ∑ i, uL (m' i) (GlobalTheory.CompanionTheory.HermVol.hermPart D r y) • (rat (m i) : Mx D r r) =
      GlobalTheory.CompanionTheory.HermVol.hermPart D r y := by
    refine mx_induction ?_ ?_ ?_
    · have h0 : GlobalTheory.CompanionTheory.HermVol.hermPart D r (0 : Mx D r r) = 0 := by
        simp [GlobalTheory.CompanionTheory.HermVol.hermPart]
      simp [h0]
    · intro x y hx hy
      rw [GlobalTheory.CompanionTheory.HermVol.hermPart_add]
      simp only [map_add (f := _), add_smul, Finset.sum_add_distrib, hx, hy]
    · intro a g
      rw [hermPart_smul, hermPart_ratm]
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      congr 1
      simp only [uL_rat, algebraMap_smul_rat]
      rw [← rat_sum, hm _ (hmid_herm _ (fun x => star_star x) g)]
  have := key x
  rwa [GlobalTheory.CompanionTheory.HermVol.hermPart_of_mem hx] at this

end Adelic

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Main

variable {D : D7} {r : ℕ}

theorem continuous_halfTrL : Continuous (halfTrL D) :=
  IsModuleTopology.continuous_of_linearMap (R := AF D.host.F) (halfTrL D)

theorem continuous_uL (m : Matrix (Fin r) (Fin r) D.host.E) : Continuous (uL m) :=
  continuous_halfTrL.comp (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))

theorem continuous_smul_const (z : AE D) : Continuous fun a : AF D.host.F => a • z :=
  IsModuleTopology.continuous_of_linearMap (R := AF D.host.F)
    (LinearMap.toSpanSingleton (AF D.host.F) (AE D) z)

theorem continuous_smul_rat (M : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun a : AF D.host.F => a • (rat M : Mx D r r) := by
  refine continuous_matrix fun k l => ?_
  simp only [Matrix.smul_apply]
  exact continuous_smul_const _

theorem pairing_comb {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E) (v : Fin n → AF D.host.F)
    (x : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (∑ i, v i • (rat (m i) : Mx D r r)) x : Mx D r r)) =
      v ⬝ᵥ fun i => uL (m i) x := by
  let p : Mx D r r →ₗ[AF D.host.F] AF D.host.F :=
    (halfTrL D) ∘ₗ (Matrix.traceLinearMap (Fin r) (AF D.host.F) (AE D)) ∘ₗ
      (LinearMap.mulRight (AF D.host.F) x)
  have h := map_sum p (fun i => v i • (rat (m i) : Mx D r r)) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

theorem continuous_comb {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun v : Fin n → AF D.host.F => ∑ i, v i • (rat (m i) : Mx D r r) := by
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  exact continuous_finsetSum _ fun i _ => (continuous_smul_rat (m i)).comp (continuous_apply i)

theorem comb_mem {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (hm : ∀ i, ct D.sp.cm.sig (m i) = m i) (v : Fin n → AF D.host.F) :
    ∑ i, v i • (rat (m i) : Mx D r r) ∈ hermA D r := by
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  show adj (v i • (rat (m i) : Mx D r r)) = _
  rw [adj_rsmul, ← rat_conjTranspose]
  exact congrArg (fun M => v i • (rat M : Mx D r r)) (hm i)

def cEquiv {n : ℕ} (e e' : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (he' : ∀ i, ct D.sp.cm.sig (e' i) = e' i)
    (hd : ∀ i j, (tF (e i) (e' j) : D.host.F) = if i = j then 1 else 0)
    (hrec : ∀ h : Matrix (Fin r) (Fin r) D.host.E, ct D.sp.cm.sig h = h →
      ∑ i, (tF (e i) h : D.host.F) • e' i = h) :
    (Fin n → AF D.host.F) ≃ₜ+ hermA D r where
  toFun v := ⟨∑ i, v i • (rat (e' i) : Mx D r r), comb_mem e' he' v⟩
  invFun b i := uL (e i) b.1
  left_inv v := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, uL_rat, hd, smul_eq_mul]
    simp
  right_inv b := Subtype.ext (sum_uL_smul e' e hrec b.2)
  map_add' v w := Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
  continuous_toFun := (continuous_comb e').subtype_mk _
  continuous_invFun := continuous_pi fun i => (continuous_uL (e i)).comp continuous_subtype_val

end Main

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Measure

variable {D : D7} {r : ℕ}

theorem isTamagawa_map {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (h : IsCovolOneH lam 𝓖) {n : ℕ}
    (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r)
    (h1 : ∀ w : Fin n → D.host.F, (c fun i => algebraMap D.host.F (AF D.host.F) (w i)).1 ∈ ratMx D r r)
    (h2 : ∀ b : hermA D r, b.1 ∈ ratMx D r r →
      ∃ w : Fin n → D.host.F, c.symm b = fun i => algebraMap D.host.F (AF D.host.F) (w i)) :
    GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  obtain ⟨t2, -, t3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → AF D.host.F) := Pi.borelSpace
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  obtain ⟨hH, hF, hm⟩ := h
  haveI := hH
  have hc : Measurable c := c.continuous.measurable
  have hcs : Measurable c.symm := c.symm.continuous.measurable
  let me : hermA D r ≃ᵐ (Fin n → AF D.host.F) := c.symm.toHomeomorph.toMeasurableEquiv
  refine ⟨ContinuousAddEquiv.isAddHaarMeasure_map lam c.symm, c.symm '' 𝓖, ?_, ?_⟩
  · have e1 : lam.map c.symm (c.symm '' 𝓖) = lam (me ⁻¹' (c.symm '' 𝓖)) := me.map_apply _
    rw [e1, show me ⁻¹' (c.symm '' 𝓖) = 𝓖 from Set.preimage_image_eq _ c.symm.injective, hm]
  · let f : hermA D r ≃ (Fin n → AF D.host.F) := c.symm.toEquiv
    have hq : Measure.QuasiMeasurePreserving f.symm (lam.map c.symm) lam := by
      refine ⟨hc.aemeasurable, ?_⟩
      have : (lam.map c.symm).map f.symm = lam := by
        show (lam.map c.symm).map c = lam
        rw [Measure.map_map hc hcs]
        have : (c ∘ c.symm) = id := funext fun x => c.apply_symm_apply x
        rw [this, Measure.map_id]
      rw [this]
    let eq : (AddMonoidHom.compLeft (algebraMap D.host.F (AF D.host.F)).toAddMonoidHom (Fin n)).range ≃
        ratHerm D r :=
      { toFun := fun g => ⟨c g.1, by
          obtain ⟨w, hw⟩ := g.2
          rw [← hw]
          exact h1 w⟩
        invFun := fun b => ⟨c.symm b.1, by
          obtain ⟨w, hw⟩ := h2 b.1 b.2
          exact ⟨w, hw.symm⟩⟩
        left_inv := fun g => Subtype.ext (c.symm_apply_apply g.1)
        right_inv := fun b => Subtype.ext (c.apply_symm_apply b.1) }
    refine hF.image_of_equiv f hq eq fun g x => ?_
    show c.symm (c g.1 + x) = g.1 + c.symm x
    exact (c.symm.toAddEquiv.map_add (c g.1) x).trans (congrArg (· + c.symm x) (c.symm_apply_apply g.1))

end Measure

section Target

theorem finEF (D : D7) : FiniteDimensional D.host.F D.host.E :=
  Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E

theorem coords : ∀ (D : D7) (r : ℕ) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∃ (n : ℕ) (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r) (u : Mx D r r → Fin n → AF D.host.F) (R : (Fin n → AF D.host.F) → Mx D r r), Continuous u ∧ Continuous R ∧ (∀ x : Mx D r r, x ∈ hermA D r → R (u x) = x) ∧ (∀ (v : Fin n → AF D.host.F) (x : Mx D r r), halfTr (Matrix.trace (HMul.hMul (c v).1 x : Mx D r r)) = v ⬝ᵥ u x) ∧ GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  intro D r lam 𝓖 h
  haveI := finEF D
  obtain ⟨n, e, e', he, he', hd, hrec, hrec'⟩ := exists_dual (F := D.host.F) D.sp.cm.sig (fun x => star_star x) r
  refine ⟨n, cEquiv e e' he' hd hrec', fun x i => uL (e' i) x, fun w => ∑ i, w i • (rat (e i) : Mx D r r),
    continuous_pi fun i => continuous_uL (e' i), continuous_comb e, fun x hx => sum_uL_smul e e' hrec hx, ?_, ?_⟩
  · intro v x
    exact pairing_comb e' v x
  · refine isTamagawa_map h _ ?_ ?_
    · intro w
      show ∑ i, algebraMap D.host.F (AF D.host.F) (w i) • (rat (e' i) : Mx D r r) ∈ ratMx D r r
      simp only [algebraMap_smul_rat]
      rw [← rat_sum]
      exact rat_mem _
    · rintro b ⟨γ, hγ⟩
      replace hγ : rat γ = b.1 := hγ
      refine ⟨fun i => tF (e i) γ, funext fun i => ?_⟩
      show uL (e i) b.1 = _
      rw [← hγ, uL_rat]

end Target

end GlobalTheory.CompanionTheory.HermCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesTracePairingStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_coordinates_trace_pairing : ∀ (D : D7) (r : ℕ) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∃ (n : ℕ) (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r) (u : Mx D r r → Fin n → AF D.host.F) (R : (Fin n → AF D.host.F) → Mx D r r), Continuous u ∧ Continuous R ∧ (∀ x : Mx D r r, x ∈ hermA D r → R (u x) = x) ∧ (∀ (v : Fin n → AF D.host.F) (x : Mx D r r), halfTr (Matrix.trace (HMul.hMul (c v).1 x : Mx D r r)) = v ⬝ᵥ u x) ∧ GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  first | exact @GlobalTheory.CompanionTheory.HermCoord.coords | exact GlobalTheory.CompanionTheory.HermCoord.coords | (intros; apply GlobalTheory.CompanionTheory.HermCoord.coords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZero
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path

variable {F : Type} [Field F] [NumberField F]

def invInf (F : Type) [Field F] [NumberField F] (n : ℕ) : Ainf F :=
  fun w => ((n : w.Completion) + 1)⁻¹

omit [NumberField F] in
theorem norm_natCast_add_one (w : NumberField.InfinitePlace F) (n : ℕ) :
    ‖((n : w.Completion) + 1)‖ = (n : ℝ) + 1 := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) ((n : w.Completion) + 1)
  rw [← h, map_add (f := _), map_natCast, map_one]
  have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_natCast]
  push_cast; ring

theorem natCast_add_one_ne_zero (w : NumberField.InfinitePlace F) (n : ℕ) :
    ((n : w.Completion) + 1) ≠ 0 := by
  intro h
  have := norm_natCast_add_one w n
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem mul_invInf (n : ℕ) : ((n : Ainf F) + 1) * invInf F n = 1 := by
  have key : ((n : ∀ w : NumberField.InfinitePlace F, w.Completion) + 1) *
      (fun w : NumberField.InfinitePlace F => ((n : w.Completion) + 1)⁻¹) = 1 := by
    funext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (natCast_add_one_ne_zero w n)
  exact key

theorem tendsto_invInf : Filter.Tendsto (invInf F) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 fun w => ?_
  have key : Filter.Tendsto (fun n : ℕ => ((n : w.Completion) + 1)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n : ℕ, ‖((n : w.Completion) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := fun n => by
      rw [norm_inv, norm_natCast_add_one, one_div]
    simp only [e]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact key

def seqA (F : Type) [Field F] [NumberField F] (n : ℕ) : AF F := pairA F (invInf F n) 0

theorem tendsto_seqA : Filter.Tendsto (seqA F) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n => (invInf F n, (0 : Af F))) Filter.atTop (nhds ((0 : Ainf F), (0 : Af F))) :=
    tendsto_invInf.prodMk_nhds tendsto_const_nhds
  exact this

def seqE (D : D7) (r n : ℕ) : Mx D r r :=
  Matrix.diagonal fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)

theorem seqE_mem (D : D7) (r n : ℕ) : seqE D r n ∈ hermA D r := by
  show GlobalTheory.MixModel.adj (seqE D r n) = seqE D r n
  ext i j
  by_cases h : i = j
  · subst h
    simp [GlobalTheory.MixModel.adj, seqE, sigR]
  · simp [GlobalTheory.MixModel.adj, seqE, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem tendsto_seqE (D : D7) (r : ℕ) : Filter.Tendsto (seqE D r) Filter.atTop (nhds 0) := by
  have hc : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Filter.Tendsto (fun n => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) Filter.atTop (nhds (0 : AE D)) := by
    have h2 : Filter.Tendsto (fun n => seqA D.host.F n • (1 : AE D)) Filter.atTop (nhds ((0 : AF D.host.F) • (1 : AE D))) :=
      tendsto_seqA.smul_const _
    rw [zero_smul] at h2
    refine h2.congr fun n => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Filter.Tendsto (fun n => seqE D r n i j) Filter.atTop (nhds (0 : AE D))
  by_cases h : i = j
  · subst h
    refine h1.congr fun n => ?_
    exact (Matrix.diagonal_apply_eq (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) i).symm
  · refine (tendsto_const_nhds (x := (0 : AE D))).congr fun n => ?_
    exact (Matrix.diagonal_apply_ne (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) h).symm

theorem theta_seqE (D : D7) (θ : InfFam D) (ρ : D.what₂.Tau) (n : ℕ) :
    θ ρ (infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E))) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  have e1 : infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1]
  have e2 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * (invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_invInf, mul_one]; rfl
  have e3 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((n : Ainf D.host.F ⊗[D.host.F] D.host.E) + 1) := by
    rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    congr 1
  have e4 := congrArg (θ ρ) e2
  rw [e3, map_mul, map_add (f := _), map_natCast, map_one] at e4
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  linear_combination e4

theorem exists_herm_seq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro D θ _ r
  refine ⟨seqE D r, seqE_mem D r, tendsto_seqE D r, fun n ρ => ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    simp only [compAt, seqE, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    rw [theta_seqE]; simp
  · simp [compAt, seqE, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZeroStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_scalar_sequence_tends_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path.exists_herm_seq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpenStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpen
open scoped Matrix Topology

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_on_subspace_open : ∀ (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε Z S} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem gram_form_eq {m n : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (w : Fin n → ℂ) :
    star w ⬝ᵥ (y.conjTranspose * G * y).mulVec w = star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem exists_posOn_of_gram (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ)
    (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ))
    (h : PosOn ε (y.conjTranspose * G * y) S) :
    ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  have key : ∀ w ∈ S, w ≠ 0 → 0 < ε * (star (y.mulVec w) ⬝ᵥ G.mulVec (y.mulVec w)).re := by
    intro w hw hw0
    have hpos := h w hw hw0
    rwa [gram_form_eq] at hpos
  have hinj : Function.Injective ((Matrix.mulVecLin y).domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : Fin n → ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have h1 := key w w.2 hw0
    have h2 : y.mulVec (w : Fin n → ℂ) = 0 := by simpa using hw
    simp [h2] at h1
  refine ⟨S.map (Matrix.mulVecLin y), ?_, ?_⟩
  · intro v hv hv0
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hv0 (map_zero _)
    rw [Matrix.mulVecLin_apply]
    exact key w hw hw0
  · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityPullsBackToSubspaceStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positivity_pulls_back_to_subspace : ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) ℂ) (y : Matrix (Fin m) (Fin n) ℂ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (y.conjTranspose * G * y) S → ∃ T : Submodule ℂ (Fin m → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε G T ∧ Module.finrank ℂ T = Module.finrank ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_posOn_of_gram <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresented
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_ring {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (ψ : AddChar A ℂ) (hψc : Continuous ψ) (hψn : ∀ x, ‖ψ x‖ = 1) (κ : Type) [Fintype κ]
    [FirstCountableTopology (κ → A)] [MeasurableSpace (κ → A)] [OpensMeasurableSpace (κ → A)]
    (μ : Measure (κ → A)) [μ.IsOpenPosMeasure]
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (φ : Y → ℂ) (g : Y → κ → A)
    (hg : Measurable g) (N : Set (κ → A)) (hN : IsOpen N)
    (hb : Integrable φ ν → Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ →
      ∀ N' : Set (κ → A), IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : (κ → A) → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0)
    (z₀ : κ → A) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → A) × (κ → A) => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hd1 : ∀ w, Continuous fun v : κ → A => ψ (-(v ⬝ᵥ w)) := fun w =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_id continuous_const)).neg
  have hd2 : ∀ v, Continuous fun w : κ → A => ψ (-(v ⬝ᵥ w)) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id)).neg
  have hd3 : ∀ v, Continuous fun w : κ → A => ψ (v ⬝ᵥ w) := fun v =>
    hψc.comp (hdot.comp (Continuous.prodMk continuous_const continuous_id))
  by_cases hφ : Integrable φ ν
  swap
  · have h0 : ∀ v : κ → A, ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν = 0 := fun v =>
      integral_undef fun hi => hφ (integrable_of_mul_unimodular ν φ (fun y => ψ (v ⬝ᵥ g y)) hi
        ((hd3 v).measurable.comp hg).aestronglyMeasurable fun y => hψn _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) = 0
    rw [h0 v, zero_mul]
  by_cases hJ : Integrable (fun v : κ → A => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ
  swap
  · exact integral_undef fun hi => hJ (integrable_of_mul_unimodular μ _ (fun v => ψ (-(v ⬝ᵥ z₀))) hi
      (hd1 z₀).aestronglyMeasurable fun y => hψn _)
  exact vanish_abs μ (fun v z => ψ (-(v ⬝ᵥ z))) hd1 hd2 (fun _ _ => hψn _) _ hJ N hN (hb hφ hJ) z₀ hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem vanish_generic (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F)
    (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)]
    [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)) (hμ : GlobalTheory.SWLit.IsTamagawa F κ μ)
    (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F)
    (hg : Measurable g) (N : Set (κ → AF F)) (hN : IsOpen N) (hgN : ∀ y, g y ∉ N)
    (z₀ : κ → AF F) (hz : z₀ ∈ closure N) :
    ∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z₀)) ∂μ = 0 := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ.1
  refine vanish_ring ψ hψ.1 hψ.2.1 κ μ Y ν φ g hg N hN ?_ z₀ hz
  intro hφ hJ N' hN' hsub z₁ hz₁
  obtain ⟨Φ, hΦ, hΦ0, hΦN, hΦ1⟩ := GlobalTheory.T.exists_nonnegative_schwartz_bump F κ N' hN' z₁ hz₁
  obtain ⟨hΦc, -, hΦi⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  exact ⟨Φ, hΦc, hΦi μ hμ.1, hΦ0, hΦN, hΦ1,
    GlobalTheory.T.tamagawa_fourier_integrable F hF ψ hψ κ μ hμ Y ν φ g hφ hg hJ Φ hΦ (fun y => hΦN _ fun h' => hgN y (hsub h'))⟩

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

variable {D : D7}

theorem posOn_add_smul_one {n : ℕ} {ε δ : ℝ} {Z : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)}
    (hS : NonnegOn ε Z S) (hε : ε = 1 ∨ ε = -1) (hδ : 0 < δ) :
    PosOn ε (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) S := by
  intro w hw hne
  have h0 := hS w hw
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hB : 0 < (star w ⬝ᵥ w).re := by
    have e : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    rw [e]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (star w ⬝ᵥ (Z + ((ε * δ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).mulVec w).re =
      (star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      Complex.add_re, smul_eq_mul, Complex.re_ofReal_mul]
  rw [e2]
  have : ε * ((star w ⬝ᵥ Z.mulVec w).re + ε * δ * (star w ⬝ᵥ w).re) =
      ε * (star w ⬝ᵥ Z.mulVec w).re + (ε * ε) * δ * (star w ⬝ᵥ w).re := by ring
  rw [this, hεε, one_mul]
  exact add_pos_of_nonneg_of_pos h0 (mul_pos hδ hB)

theorem compAt_add' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a b : Mx D m n) :
    compAt θ ρ (a + b) = compAt θ ρ a + compAt θ ρ b := by
  exact Matrix.map_add (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_add a b

theorem compAt_neg' (θ : InfFam D) (ρ : D.what₂.Tau) {m n : ℕ} (a : Mx D m n) :
    compAt θ ρ (-a) = -compAt θ ρ a := by
  exact Matrix.map_neg (⇑((θ ρ).comp (infPart D))) ((θ ρ).comp (infPart D)).map_neg a

theorem W_eq_zero_of_obstruction (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (h : Hyp D r V ψ θ μ lam ν φ) (β : HermE D r) (ρ : D.what₂.Tau) (ε : ℝ)
    (S : Submodule ℂ (Fin r → ℂ)) (hε : ε = 1 ∨ ε = -1) (hS : NonnegOn ε (β.1.map (tauE D ρ)) S)
    (hT : ∀ T : Submodule ℂ (Fin V.rank → ℂ), PosOn ε (gramAt D V ρ) T →
      Module.finrank ℂ T < Module.finrank ℂ S) :
    W ψ V μ lam φ β = 0 := by
  obtain ⟨hr, hψ, hθ, ⟨𝓕, hF⟩, ⟨𝓖, hG⟩, -, -, -⟩ := h
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele D.host.F
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hF.1
  obtain ⟨n, c, u, R, hu, hR, hRu, hcu, hTam⟩ := GlobalTheory.T.hermitian_coordinates_trace_pairing D r lam 𝓖 hG
  have hin := GlobalTheory.T.gram_map_continuous_hermitian D θ hθ V r ρ
  let g : Mx D V.rank r → Fin n → AF D.host.F := fun y => u (inner V y y)
  have hgc : Continuous g := hu.comp hin.1
  let N : Set (Fin n → AF D.host.F) := {w | PosOn ε (compAt θ ρ (R w)) S}
  have hN : IsOpen N :=
    (GlobalTheory.T.positive_on_subspace_open r ε S).preimage ((GlobalTheory.RealWeil.continuous_compAt hθ ρ r r).comp hR)
  have hgN : ∀ y, g y ∉ N := by
    intro y hy
    have h1 : PosOn ε (compAt θ ρ (R (u (inner V y y)))) S := hy
    rw [hRu _ (hin.2 y).1, (hin.2 y).2] at h1
    obtain ⟨T, hT1, hT2⟩ := GlobalTheory.T.positivity_pulls_back_to_subspace _ _ _ _ ε S h1
    have := hT T hT1
    omega
  let z₀ : Fin n → AF D.host.F := u (rat β.1)
  have hcl : ∀ e' : ℕ → Mx D r r, (∀ k, e' k ∈ hermA D r) → Filter.Tendsto e' Filter.atTop (nhds 0) →
      (∀ k : ℕ, compAt θ ρ (e' k) = ((ε * ((1 : ℝ) / ((k : ℝ) + 1)) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) →
      z₀ ∈ closure N := by
    intro e' he' het hec
    have hlim : Filter.Tendsto (fun k => u (rat β.1 + e' k)) Filter.atTop (nhds z₀) := by
      have h2 : Filter.Tendsto (fun k => rat β.1 + e' k) Filter.atTop (nhds (rat β.1 + 0)) :=
        tendsto_const_nhds.add het
      rw [add_zero] at h2
      exact (hu.tendsto _).comp h2
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
    show PosOn ε (compAt θ ρ (R (u (rat β.1 + e' k)))) S
    have hrat : compAt θ ρ (rat β.1) = β.1.map (tauE D ρ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ ρ β.1
    rw [hRu _ ((hermA D r).add_mem (GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA β) (he' k)), compAt_add', hec k, hrat]
    exact posOn_add_smul_one hS hε (by positivity)
  obtain ⟨e, he, het, hec⟩ := GlobalTheory.T.hermitian_scalar_sequence_tends_zero D θ hθ r
  have hz : z₀ ∈ closure N := by
    rcases hε with rfl | rfl
    · refine hcl e he het fun k => ?_
      rw [hec k, one_mul]
    · refine hcl (fun k => -e k) (fun k => (hermA D r).neg_mem (he k)) ?_ fun k => ?_
      · have h3 := het.neg
        rw [neg_zero] at h3
        exact h3
      · rw [compAt_neg', hec k]
        simp
  have key := vanish_generic D.host.F D.sp.cm.totReal ψ hψ (Fin n) (lam.map c.symm) hTam _ μ φ g
    hgc.measurable N hN hgN z₀ hz
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hemb : MeasurableEmbedding (c.symm) := c.symm.toHomeomorph.measurableEmbedding
  rw [hemb.integral_map] at key
  refine Eq.trans ?_ key
  unfold W
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  have h1 : ∀ x : Mx D r r, c.symm b ⬝ᵥ u x = halfTr (Matrix.trace (HMul.hMul b.1 x : Mx D r r)) := fun x => by
    rw [← hcu]; simp
  show Jt ψ V μ φ b * _ = (∫ y, φ y * ψ (c.symm b ⬝ᵥ u (inner V y y)) ∂μ) * ψ (-(c.symm b ⬝ᵥ u (rat β.1)))
  simp only [h1]
  rw [Matrix.trace_mul_comm]
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem noFrame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ h t β hβ hno
  obtain ⟨ρ, ε, S, hε, hS, hT⟩ := GlobalTheory.T.nonrepresented_signature_obstruction D r V h.1 t β hβ hno
  rw [W_eq_zero_of_obstruction r V ψ θ μ lam ν φ h β ρ ε S hε hS hT]
  haveI hemp : IsEmpty {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} :=
    ⟨fun x => hno ⟨x.1, x.2⟩⟩
  unfold IfrB
  have h0 : (fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
      φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q) = fun _ => (0 : ℂ) := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, tsum_empty]
  rw [h0]
  simp [MeasureTheory.average]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresentedStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | exact GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame <;> assumption)
end
