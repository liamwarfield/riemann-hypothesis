module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.SdComap

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem exists_nat_mul_isIntegral' (e : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * e) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := D.host.E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  have hpos : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  refine ⟨y.natAbs * y.natAbs, Nat.mul_pos hpos hpos, ?_⟩
  have e1 : ((y.natAbs * y.natAbs : ℕ) : D.host.E) * e = (y : D.host.E) * ((y : D.host.E) * e) := by
    have h2 := Int.natAbs_mul_self' y
    rw [← mul_assoc, ← Int.cast_natCast, Nat.cast_mul, h2, Int.cast_mul]
  rw [e1]
  rw [zsmul_eq_mul] at h
  refine IsIntegral.mul ?_ h
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := y))

theorem mul_mem_intAE' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem natCast_mem_intAE (n : ℕ) : (n : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
  rw [Algebra.TensorProduct.natCast_def]
  refine AddSubgroup.subset_closure ⟨(n : Af D.host.F), fun v => ?_, 1, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ n
  · simp

theorem exists_natCast_mul_mem_intAE (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ n : ℕ, 0 < n ∧ (n : Af D.host.F ⊗[D.host.F] D.host.E) * z ∈ intAE D := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul a e =>
    obtain ⟨n, hn, he⟩ := exists_nat_mul_isIntegral' (D := D) e
    obtain ⟨d, hd, ha⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_adele (F := D.host.F) a
    refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
    have e1 : ((d * n : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (a ⊗ₜ[D.host.F] e) =
        ((d : Af D.host.F) * a) ⊗ₜ[D.host.F] ((n : D.host.E) * e) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [e1]
    exact AddSubgroup.subset_closure ⟨_, fun v => Subring.mem_iInf.1 ha v, ⟨_, he⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have e1 : ((n₁ * n₂ : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (x + y) =
        (n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * x) +
          (n₁ : Af D.host.F ⊗[D.host.F] D.host.E) * ((n₂ : Af D.host.F ⊗[D.host.F] D.host.E) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem_intAE' (natCast_mem_intAE n₂) hx) (mul_mem_intAE' (natCast_mem_intAE n₁) hy)

theorem exists_natCast_mul_mem_intAt {P : Pl D → Prop} {a : AE D} (ha : a ∈ idAt D P) :
    ∃ n : ℕ, 0 < n ∧ (n : AE D) * a ∈ intAt D P := by
  obtain ⟨n, hn, h⟩ := exists_natCast_mul_mem_intAE (D := D) (finPart D a)
  refine ⟨n, hn, Ideal.mul_mem_left _ _ ha, ?_⟩
  rw [map_mul, map_natCast]; exact h

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a * b ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact mul_mem_intAE' ha.2 hb.2⟩

theorem intAt_natCast_mul {P : Pl D → Prop} {a : AE D} (n : ℕ) (ha : a ∈ intAt D P) : (n : AE D) * a ∈ intAt D P :=
  ⟨Ideal.mul_mem_left _ _ ha.1, by rw [map_mul, map_natCast]; exact mul_mem_intAE' (natCast_mem_intAE n) ha.2⟩

theorem intAt_sum {P : Pl D → Prop} {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, f i ∈ intAt D P) :
    ∑ i ∈ s, f i ∈ intAt D P := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
  | insert a s has ih =>
    rw [Finset.sum_insert has]
    exact intAt_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cA_mulVec {n : ℕ} (M : Mx D n n) (y : Fin n → AE D) :
    (fun i => cA D ((M *ᵥ y) i)) = Matrix.vecMul (fun i => cA D (y i)) (adj M) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, adj, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = Matrix.vecMul (fun i => cA D (y i)) (gA S) ⬝ᵥ x := by
  simp only [hermAt, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem hermAt_mt (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_eq, hermAt_eq, cA_mulVec (mt S g) y, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    mt_unitary]

theorem mulVec_eq_add {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    (M *ᵥ y) i = y i + ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  have h : M *ᵥ y = y + (M - 1) *ᵥ y := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h]; rfl

theorem eq_mulVec_sub {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (i : Fin n) :
    y i = (M *ᵥ y) i - ∑ j, (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * y j := by
  rw [mulVec_eq_add, add_sub_cancel_right]

theorem smul_mulVec_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (c : R)
    (i : Fin n) : (c • (M *ᵥ y)) i = c * y i + ∑ j, (c * (M i j - (1 : Matrix (Fin n) (Fin n) R) i j)) * y j := by
  rw [Pi.smul_apply, smul_eq_mul, mulVec_eq_add, mul_add, Finset.mul_sum]
  simp only [mul_assoc]

theorem mulVec_natCast_smul {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (y : Fin n → R) (m K : ℕ) :
    M *ᵥ (((m * K : ℕ) : R) • y) = (m : R) • ((K : R) • (M *ᵥ y)) := by
  rw [Matrix.mulVec_smul, Nat.cast_mul, mul_smul]

theorem mulVec_mulVec_of_mul_eq_one {R : Type} [CommRing R] {n : ℕ} {M N : Matrix (Fin n) (Fin n) R} (h : M * N = 1)
    (x : Fin n → R) : M *ᵥ (N *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem exists_common_natCast_mul_mem_intAt {P : Pl D → Prop} {ι : Type} [Fintype ι] (a : ι → AE D)
    (ha : ∀ i, a i ∈ idAt D P) : ∃ K : ℕ, 0 < K ∧ ∀ i, (K : AE D) * a i ∈ intAt D P := by
  classical
  choose n hn hx using fun i => exists_natCast_mul_mem_intAt (ha i)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact intAt_natCast_mul _ (hx i)

theorem isSDAt_comap_of (S : HSp D) (v : Pl D) (M N : Mx D S.rank S.rank) (hMN : M * N = 1)
    (hM1 : ∀ i j, M i j - (1 : Mx D S.rank S.rank) i j ∈ idAt D (· = v))
    (hherm : ∀ x y, hermAt S (M *ᵥ x) (M *ᵥ y) = hermAt S x y)
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin M).toAddMonoidHom) := by
  obtain ⟨hsupp, ⟨m, hm, hmint⟩, hsd⟩ := hΛ
  have hmem : ∀ y, y ∈ Λ.comap (Matrix.mulVecLin M).toAddMonoidHom ↔ M *ᵥ y ∈ Λ := fun y => Iff.rfl
  refine ⟨fun y hy i => ?_, ?_, ?_⟩
  · rw [eq_mulVec_sub M y i]
    exact sub_mem (hsupp _ ((hmem y).1 hy) i) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hM1 i j))
  · obtain ⟨K, hK, hKint⟩ := exists_common_natCast_mul_mem_intAt
      (fun p : Fin S.rank × Fin S.rank => M p.1 p.2 - (1 : Mx D S.rank S.rank) p.1 p.2) fun p => hM1 p.1 p.2
    refine ⟨m * K, Nat.mul_pos hm hK, fun y hy => (hmem _).2 ?_⟩
    rw [mulVec_natCast_smul M y m K]
    refine hmint _ fun i => ?_
    rw [smul_mulVec_apply M y (K : AE D) i]
    exact intAt_add (intAt_natCast_mul K (hy i)) (intAt_sum _ _ fun j _ => intAt_mul (hKint (i, j)) (hy j))
  · intro y hy
    have key := hsd _ (mulVec_mem_idAt M hy)
    refine ⟨fun h x hx => ?_, fun h => (hmem y).2 (key.2 fun x hx => ?_)⟩
    · rw [← hherm y x]; exact key.1 ((hmem y).1 h) _ ((hmem x).1 hx)
    · have hx' : M *ᵥ (N *ᵥ x) = x := mulVec_mulVec_of_mul_eq_one hMN x
      have h3 := h (N *ᵥ x) ((hmem _).2 (by rw [hx']; exact hx))
      rwa [← hherm, hx'] at h3

theorem isSDAt_comap (D : D7) (S : HSp D) (v : Pl D) (g : GA D S) (hg : g ∈ grpAt S (· = v))
    (Λ : AddSubgroup (Fin S.rank → AE D)) (hΛ : IsSDAt S v Λ) :
    IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) :=
  isSDAt_comap_of S v (mt S g) (mt S g⁻¹) (mt_mul_inv S g) ((mem_congGrp_iff S (idAt D (· = v)) g).1 hg)
    (hermAt_mt S g) Λ hΛ

end GlobalTheory.IwaPlace.SdComap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupportedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported : ∀ (D : D7) (S : HSp D) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → ∀ Λ : AddSubgroup (Fin S.rank → AE D), IsSDAt S v Λ → IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) := by
  first | exact @GlobalTheory.IwaPlace.SdComap.isSDAt_comap | exact GlobalTheory.IwaPlace.SdComap.isSDAt_comap | (intros; apply GlobalTheory.IwaPlace.SdComap.isSDAt_comap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
noncomputable section

namespace GlobalTheory.CuspGeo.MeanValue

section Abstract

open GlobalTheory.SmoothForms

variable {L G ι : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] [Fintype ι]

theorem norm_sub_le (e : L → G) (he0 : e 0 = 1) (he : ∀ (Z : L) (s t : ℝ), e ((s + t) • Z) = e (s • Z) * e (t • Z))
    (b : Module.Basis ι ℝ L) {φ : G → ℂ} (hφ : Sm e φ) (g : G) (Z : L) (a : ℝ) (ha : ∀ i, |b.repr Z i| ≤ a) (c : ι → ℝ)
    (hc : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Der e (b i) φ (g * e (t • Z))‖ ≤ c i) :
    ‖φ (g * e Z) - φ g‖ ≤ a * ∑ i, c i := by
  have hc0 : ∀ i, 0 ≤ c i := fun i => (norm_nonneg _).trans (hc i 0 ⟨le_refl 0, zero_le_one⟩)

  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (g * e (s • Z)))
      (fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) ((t - t) • Z) Z) t := by
    intro t
    have hF : Differentiable ℝ (fun X : L => φ (g * e (t • Z) * e X)) :=
      (hφ (g * e (t • Z))).differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => (s - t) • Z) ((1 : ℝ) • Z) t :=
      ((hasDerivAt_id' t).sub_const t).smul_const Z
    rw [one_smul] at h1
    have h2 := (hF ((t - t) • Z)).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ (g * e (s • Z)) = φ (g * e (t • Z) * e ((s - t) • Z))
    rw [mul_assoc, ← he, show t + (s - t) = s by ring]

  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 Z‖ ≤ a * ∑ i, c i := by
    intro t ht
    set F' := fderiv ℝ (fun X : L => φ (g * e (t • Z) * e X)) 0 with hF'
    have hZ : F' Z = ∑ i, b.repr Z i • F' (b i) := by
      have : F' Z = F' (∑ i, b.repr Z i • b i) := by rw [b.sum_repr]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      simp only [map_smul]
    rw [hZ, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have hi : ‖F' (b i)‖ ≤ c i := by
      have := hc i t ht
      rwa [DerLinear.der_eq_fderiv hφ] at this
    exact mul_le_mul (ha i) hi (norm_nonneg _) ((abs_nonneg _).trans (ha i))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => φ (g * e (s • Z))) (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      rw [sub_self, zero_smul]
      exact key t (Set.Ico_subset_Icc_self ht))
  simpa [he0] using hmv

theorem exists_coord_bound (b : Module.Basis ι ℝ L) : ∃ K : ℝ, 0 ≤ K ∧ ∀ Z i, |b.repr Z i| ≤ K * ‖Z‖ := by
  have : FiniteDimensional ℝ L := Module.Finite.of_basis b
  let f : ι → L →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun Z i => ?_⟩
  have h1 : |b.repr Z i| = ‖f i Z‖ := by
    simp [f, Real.norm_eq_abs]
  rw [h1]
  exact ((f i).le_opNorm Z).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i)) (norm_nonneg Z))

end Abstract

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem expInf_zero (R : RealPoints θ V) : expInf θ V 0 = 1 := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE (0 : LieN V)).1 _ (GinfC V).one_mem fun τ => ?_
  rw [(hE (0 : LieN V)).2 τ, R.2.2.2.2.1 1 (GfC V).one_mem τ]
  show NormedSpace.exp (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1
  exact NormedSpace.exp_zero

theorem expInf_add (R : RealPoints θ V) (Z : LieN V) (s t : ℝ) :
    expInf θ V ((s + t) • Z) = expInf θ V (s • Z) * expInf θ V (t • Z) := by
  have hE := isExpFam_expInf R
  refine R.2.2.1 _ (hE ((s + t) • Z)).1 _ (mul_mem (hE (s • Z)).1 (hE (t • Z)).1) fun τ => ?_
  rw [R.2.2.2.1, (hE ((s + t) • Z)).2 τ, (hE (s • Z)).2 τ, (hE (t • Z)).2 τ]
  show NormedSpace.exp ((s + t) • (Z τ).1) = NormedSpace.exp (s • (Z τ).1) * NormedSpace.exp (t • (Z τ).1)
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Z τ).1).smul_right t).smul_left s)

theorem continuous_expInf (hθ : IsInfFam θ) (R : RealPoints θ V) : Continuous (expInf θ V) := by
  have H := isLieData R
  have h1 : Continuous fun X : LieN V => NormedSpace.exp (jInf V X) :=
    (DerLinear.contDiff_exp H).continuous
  exact (GlobalTheory.Mem.DerClosed.continuousOn_secInf hθ V).comp_continuous h1 fun X => DerLinear.exp_unitary H X


open Classical in
theorem exists_basis (V : HSp D) : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (LieN V)) (p : ι → D.what₂.Tau)
    (X : ∀ i, LieAt V (p i)), ∀ i, b i = atPlace V (p i) (X i) := by
  refine ⟨Σ τ, Fin (Module.finrank ℝ (lieU (gramAt D V τ)).toSubmodule), inferInstance,
    Pi.basis fun τ => Module.finBasis ℝ (lieU (gramAt D V τ)).toSubmodule, fun i => i.1,
    fun i => ⟨(Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).1,
      (Module.finBasis ℝ (lieU (gramAt D V i.1)).toSubmodule i.2).2⟩, fun i => ?_⟩
  exact (Pi.basis_apply _ i).trans rfl

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_lieN_le (Z : LieN V) {r : ℝ} (hr : 0 ≤ r) (h : ∀ τ i j, ‖(Z τ).1 i j‖ ≤ r) : ‖Z‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun τ => ?_
  rw [Submodule.coe_norm]
  exact (Matrix.norm_le_iff hr).2 (h τ)

end

theorem exists_log (hθ : IsInfFam θ) (R : RealPoints θ V) : ∃ δ₁ C : ℝ, 0 < δ₁ ∧ 0 ≤ C ∧
    ∀ (u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∃ Z : LieN V, expInf θ V Z = u ∧ ‖Z‖ ≤ C * δ := by
  have hG : ∀ τ, IsUnit (gramAt D V τ).det := fun τ => (R.1 τ).2
  choose δτ Cτ hδτ hτ using fun τ => GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound V.rank (gramAt D V τ) (hG τ)
  obtain ⟨δ₁, hδ₁, hle⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ τ, δ₁ ≤ δτ τ := by
    rcases isEmpty_or_nonempty D.what₂.Tau with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min δτ
      exact ⟨δτ τ₀, hδτ τ₀, hτ₀⟩
  have hC : ∀ τ, Cτ τ ≤ ∑ τ', |Cτ τ'| := fun τ =>
    (le_abs_self _).trans (Finset.single_le_sum (fun τ' _ => abs_nonneg (Cτ τ')) (Finset.mem_univ τ))
  refine ⟨δ₁, ∑ τ, |Cτ τ|, hδ₁, Finset.sum_nonneg fun τ _ => abs_nonneg _, fun u δ hδ hδle hu => ?_⟩

  have hX : ∀ τ, ∃ X : Matrix (Fin V.rank) (Fin V.rank) ℂ, Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 ∧
      NormedSpace.exp X = infMat D.sp.cm.sig V.gram (θ τ) u ∧ ∀ i j, ‖X i j‖ ≤ Cτ τ * δ := fun τ =>
    hτ τ _ δ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V u τ) (hδle.trans (hle τ)) (hu.2 τ)
  choose X hXl hXe hXn using hX
  let Z : LieN V := fun τ => ⟨X τ, (mem_lieAt_iff τ (X τ)).1 (hXl τ)⟩
  refine ⟨Z, ?_, ?_⟩
  · have hE := isExpFam_expInf R
    refine R.2.2.1 _ (hE Z).1 _ hu.1 fun τ => ?_
    rw [(hE Z).2 τ]
    exact hXe τ
  · refine norm_lieN_le Z (mul_nonneg (Finset.sum_nonneg fun τ _ => abs_nonneg _) hδ) fun τ i j => ?_
    exact (hXn τ i j).trans (mul_le_mul_of_nonneg_right (hC τ) hδ)

theorem mean_value : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  intro D θ hθ V
  classical
  have R : RealPoints θ V := (RealPts.realPoints D).2 θ hθ V
  obtain ⟨ι, hι, b, p, X, hb⟩ := exists_basis V
  obtain ⟨K, hK, hKb⟩ := exists_coord_bound b
  obtain ⟨δ₁, C₀, hδ₁, hC₀, hlog⟩ := exists_log hθ R
  have : FiniteDimensional ℝ (LieN V) := Module.Finite.of_basis b
  set B := Finset.univ.image fun i => (p i, (X i).1) with hB
  have hmemB : ∀ i, (p i, (X i).1) ∈ B := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have h0 : expInf θ V 0 ∈ expInf θ V '' Metric.closedBall 0 (C₀ * δ₁) :=
    ⟨0, Metric.mem_closedBall_self (mul_nonneg hC₀ hδ₁.le), rfl⟩
  refine ⟨B, expInf θ V '' Metric.closedBall 0 (C₀ * δ₁), K * C₀ * Fintype.card ι, δ₁, ?_, ?_, hδ₁,
    mul_nonneg (mul_nonneg hK hC₀) (Nat.cast_nonneg _), ?_⟩
  · intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    exact (mem_lieAt_iff _ _).2 (X i).2
  · exact (isCompact_closedBall 0 _).image (continuous_expInf hθ R)
  · intro ψ hψ g u δ hδ hδle hu c hc
    obtain ⟨Z, rfl, hZ⟩ := hlog u δ hδ hδle hu
    have hsm : Sm (expInf θ V) ψ := (isSmoothInf_iff ψ).1 ((smooth_iff R ψ).1 hψ)
    have hcn : ∀ q ∈ B, 0 ≤ c q := fun q hq => (norm_nonneg _).trans (hc q hq _ h0)
    have ha : ∀ i, |b.repr Z i| ≤ K * (C₀ * δ) := fun i =>
      (hKb Z i).trans (mul_le_mul_of_nonneg_left hZ hK)
    have hder : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖Der (expInf θ V) (b i) ψ (g * expInf θ V (t • Z))‖ ≤ c (p i, (X i).1) := by
      intro i t ht
      rw [hb i, ← lieDer_eq, ← Rder_eq R]
      refine hc _ (hmemB i) _ ⟨t • Z, ?_, rfl⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖Z‖ ≤ 1 * (C₀ * δ) := mul_le_mul ht.2 hZ (norm_nonneg _) zero_le_one
        _ ≤ C₀ * δ₁ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hδle hC₀
    have key := norm_sub_le (expInf θ V) (expInf_zero R) (expInf_add R) b hsm g Z (K * (C₀ * δ)) ha
      (fun i => c (p i, (X i).1)) hder
    have hsum : ∑ i, c (p i, (X i).1) ≤ Fintype.card ι * ∑ q ∈ B, c q := by
      calc ∑ i, c (p i, (X i).1) ≤ ∑ _i : ι, ∑ q ∈ B, c q :=
            Finset.sum_le_sum fun i _ => Finset.single_le_sum hcn (hmemB i)
        _ = Fintype.card ι * ∑ q ∈ B, c q := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc ‖ψ (g * expInf θ V Z) - ψ g‖ ≤ K * (C₀ * δ) * ∑ i, c (p i, (X i).1) := key
      _ ≤ K * (C₀ * δ) * (Fintype.card ι * ∑ q ∈ B, c q) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hK (mul_nonneg hC₀ hδ))
      _ = K * C₀ * Fintype.card ι * δ * ∑ q ∈ B, c q := by ring

end GlobalTheory.CuspGeo.MeanValue

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, ∃ (B : Finset (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (Ω : Set (GA D V)) (C δ₁ : ℝ), (∀ p ∈ B, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ 0 < δ₁ ∧ 0 ≤ C ∧ ∀ ψ : GA D V → ℂ, SmoothW θ V ψ → ∀ (g u : GA D V) (δ : ℝ), 0 ≤ δ → δ ≤ δ₁ → CloseR θ V u δ → ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ, (∀ p ∈ B, ∀ w ∈ Ω, ‖Rder θ V p.1 p.2 ψ (g * w)‖ ≤ c p) → ‖ψ (g * u) - ψ g‖ ≤ C * δ * ∑ p ∈ B, c p := by
  first | exact @GlobalTheory.CuspGeo.MeanValue.mean_value | exact GlobalTheory.CuspGeo.MeanValue.mean_value | (intros; apply GlobalTheory.CuspGeo.MeanValue.mean_value <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HandFam

theorem star_psi_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h2 : ψ a * star (ψ a) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', h1]; simp
  have h3 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ a ≠ 0 := by intro h; rw [h, zero_mul] at h3; exact zero_ne_one h3
  exact mul_left_cancel₀ h0 (h2.trans h3.symm)

theorem handBF_isQuasiFam : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ)
    (s : StepBF ψ B J) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ')
    (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ), IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ →
      IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) := by
  intro D ψ ρ B J s L' ζ' hz l φ Ξ hφ hΞ
  obtain ⟨hτ, -⟩ := GlobalTheory.T.besselLineLink_gram_similitude_bijective D ρ B L' ζ' hz l
  obtain ⟨hadd, hcont, hrat, heq, hsym, -⟩ :=
    GlobalTheory.T.hermitianLinkMap_additive_rational_equivariant D B.L L' J.W₀ l.τ 1 hτ (l.κ J.W₀) (fun _ => rfl)
  have hF : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (s.om₀ p Ξ) := fun p => s.weil₀.om_pres p Ξ hΞ
  have hsub := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
  refine ⟨?_, ?_, ?_⟩
  · intro h γ w
    have hr : (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) ∈ ratMx D J.W₀.rank B.V₀.rank := by
      rw [B.o.resS_symm_apply, Matrix.zero_mul, zero_add]
      exact ratMx_mul (hrat _ (rat_mem γ)) (rat_mem _)
    obtain ⟨δ, hδ⟩ := hr
    have hs : symplOH B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)))
        ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = -(symplOH J.W₀ L' (ratW L' J.W₀ γ) w) := by
      rw [B.o.symplOH_resS]
      simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]
      rw [symplOH, symplOH, hsym]
      push_cast
      ring
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ + w))) =
        ψ (symplOH J.W₀ L' (ratW L' J.W₀ γ) w) * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) := by
      intro h₀
      have e : ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ + w)) =
          ((0 : WO B.A J.W₀), l.κ J.W₀ (ratW L' J.W₀ γ)) + (0, l.κ J.W₀ w) := by
        rw [hadd, Prod.mk_add_mk, add_zero]
      have hq := (hF (B.o.emb (h₀, 1), h)).quasi δ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      have hδ' : rat δ = (B.o.resS J.W₀).symm (0, l.κ J.W₀ (ratW L' J.W₀ γ)) := hδ
      rw [ratW_eq, hδ', hs, neg_neg] at hq
      rw [e, map_add (f := _), hq]
    simp only [handBF, key]
    simp_rw [mul_left_comm (φ _) (ψ _)]
    rw [integral_const_mul, star_mul', star_psi_eq s.weil₀.std]
  · have jc := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
    have hmap : Continuous fun q : GA D B.A × (GA D J.W₀ × WO J.W₀ L') =>
        ((B.o.emb (q.1, 1), q.2.1), (B.o.resS J.W₀).symm (0, l.κ J.W₀ q.2.2)) :=
      ((B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)).prodMk
        (continuous_fst.comp continuous_snd)).prodMk
        ((B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hcont.comp (continuous_snd.comp continuous_snd))))
    have hK := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D B.A B.cpt B.vA (GA D J.W₀ × WO J.W₀ L')
      (fun h₀ p => φ h₀ * s.om₀ (B.o.emb (h₀, 1), p.1) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2)))
      ((hφ.2.comp continuous_fst).mul (jc.comp hmap)) (by
        intro γ hγ h₀ p
        have e : B.o.emb (γ * h₀, 1) = B.o.emb (γ, 1) * B.o.emb (h₀, 1) := by
          rw [← map_mul, Prod.mk_mul_mk, one_mul]
        have hq := hsub (B.o.emb (γ, 1)) (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (B.o.emb (h₀, 1)) p.1
          ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.2))
        rw [one_mul] at hq
        rw [hφ.1 γ hγ h₀, e, hq, inv_one, mt_one, Matrix.one_mul]
        simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, B.o.pB_emb, mt_one,
          Matrix.one_mul])
    exact continuous_star.comp hK.2.1
  · intro γ hγ h w
    have hκ := heq γ⁻¹ w
    rw [inv_inv] at hκ
    have key : ∀ h₀, s.om₀ (B.o.emb (h₀, 1), γ * h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) =
        s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ (w ⬝ mt J.W₀ γ))) := by
      intro h₀
      have hq := hsub 1 (one_mem _) γ hγ (B.o.emb (h₀, 1)) h ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
      rw [one_mul] at hq
      rw [hq, mt_one, Matrix.mul_one, hκ]
      simp only [B.o.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    simp only [handBF, key]

end GlobalTheory.HandFam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToFourierJacobiHandedFamilyContinuousAutomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselToFourierJacobi_handedFamily_continuous_automorphic : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E), IsLineVec L' ζ' → ∀ (l : Link B L' ζ') (φ : GA D B.A → ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ), IsContAut B.A φ → IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsQuasiFam ψ J.W₀ L' (handBF s l φ Ξ) := by
  first | exact @GlobalTheory.HandFam.handBF_isQuasiFam | exact GlobalTheory.HandFam.handBF_isQuasiFam | (intros; apply GlobalTheory.HandFam.handBF_isQuasiFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompact
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.LevelCompact

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem actO_actO' (S T : HSp D) (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_inv_actO' (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  rw [actO_actO', mul_inv_cancel, mul_inv_cancel]
  unfold actO
  rw [inv_one, mt_one', mt_one']
  simp

theorem actO_add' (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_map_infPart (S T : HSp D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx]; simp

theorem continuous_actO_inv (S T : HSp D) :
    Continuous fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2 := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [actO, inv_inv]
  exact (((hmti T).comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((hmt S).comp (continuous_fst.comp continuous_fst))

theorem exists_level_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  intro D ψ S T χS χT om hom f hf K hK
  obtain ⟨U0, hU0, hf0⟩ := hf.level
  have hz : ∀ p : GA D S × GA D T, actO S T p.1⁻¹ p.2⁻¹ 0 = 0 := fun p => by simp [actO]
  let U : AddSubgroup (WO S T) :=
    { carrier := {u | ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0}
      add_mem' := fun {a b} ha hb p hp => by
        rw [actO_add']; exact U0.add_mem (ha p hp) (hb p hp)
      zero_mem' := fun p _ => by rw [hz]; exact U0.zero_mem
      neg_mem' := fun {a} ha p hp => by
        have : actO S T p.1⁻¹ p.2⁻¹ (-a) = -actO S T p.1⁻¹ p.2⁻¹ a := by
          simp only [actO, Matrix.mul_neg, Matrix.neg_mul]
        rw [this]; exact U0.neg_mem (ha p hp) }
  have hU : ∀ u, u ∈ U ↔ ∀ p ∈ K, actO S T p.1⁻¹ p.2⁻¹ u ∈ U0 := fun _ => Iff.rfl
  refine ⟨U, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds U (g := 0) ?_
    have hn : IsOpen ((fun q : (GA D S × GA D T) × WO S T => actO S T q.1.1⁻¹ q.1.2⁻¹ q.2) ⁻¹'
        (U0 : Set (WO S T))) := hU0.preimage (continuous_actO_inv S T)
    obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hn (by
      rintro ⟨p, w⟩ ⟨_, hw⟩
      rw [Set.mem_singleton_iff] at hw
      subst hw
      show actO S T p.1⁻¹ p.2⁻¹ 0 ∈ U0
      rw [hz]; exact U0.zero_mem)
    refine Filter.mem_of_superset (hv.mem_nhds (h0v rfl)) fun w hw => (hU w).2 fun p hp => ?_
    have h2 := Set.mem_preimage.1 (huv (Set.mk_mem_prod (hKu hp) hw))
    exact SetLike.mem_coe.1 h2
  · rintro ⟨g, h⟩ hp
    change IsThetaFunO ψ S T (om (g, h) f) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (om (g, h) f) = om (g, h) f
    refine ⟨hom.om_pres (g, h) f hf, fun u hu h0 => ?_⟩
    have h1 : actO S T g⁻¹ h⁻¹ u ∈ U0 := (hU u).1 hu (g, h) hp
    have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ u) f hf
    rw [actO_inv_actO', hf0 _ h1 (actO_map_infPart S T _ _ h0)] at e
    exact e.symm

end GlobalTheory.LevelCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonHeisenbergLevelWeilTransformCompactStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_heisenbergLevel_weilTransform_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ p ∈ K, om p f ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
  first | exact @GlobalTheory.LevelCompact.exists_level_compact | exact GlobalTheory.LevelCompact.exists_level_compact | (intros; apply GlobalTheory.LevelCompact.exists_level_compact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IwaPlace

variable {D : D7}


open GlobalTheory.SelfDualAt in
theorem idAt₂ (v : Pl D) : algebraMap (AF D.host.F) (AE D) (cP (· = v)) ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show infPart D (cP (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D (algebraMap (AF D.host.F) (AE D) (cP (· = v)))) = 0
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (sndA D.host.F (cP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w.1 (indP (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      rfl
    rw [h, evalV_indP, if_neg w.2]
    exact TensorProduct.zero_tmul _ _


open GlobalTheory.SelfDualAt in
theorem eq_alg_cP {v : Pl D} {ε : AE D} (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) :
    ε = algebraMap (AF D.host.F) (AE D) (cP (· = v)) := by
  have h1 := algebraMap_placeIdempotent_mul (· = v) ε hεI.1
  have h2 := (hε _).1 (idAt₂ v)
  rw [← h2, mul_comm]
  exact h1.symm


open GlobalTheory.SelfDualAt in
theorem placeIdem_eq_cP {v : Pl D} {εF : AF D.host.F} (h : IsPlaceIdem D v εF) : εF = cP (· = v) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  unfold cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  show evalV D.host.F w α = evalV D.host.F w (indP (· = v))
  rw [evalV_indP]
  by_cases hw : w = v
  · subst hw; rw [if_pos rfl, h1]
  · rw [if_neg hw, h0 w hw]

theorem half_mem_int (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (2⁻¹) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : Valued.v (algebraMap D.host.F (Fv D.host.F v) 2⁻¹) = v.valuation D.host.F 2⁻¹ :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : v.valuation D.host.F (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) v (2 : 𝓞 D.host.F)
    simp only [map_ofNat] at this
    rw [this]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  rw [e1, map_inv₀, e2, inv_one]


open GlobalTheory.SelfDualAt in
theorem exists_trace_one_at_tame : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε)
    (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v →
    ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  intro D v ε _ _ hεI hε ht
  have hεη := eq_alg_cP hεI hε
  rcases ht.2 with h2 | ⟨e, εF, hsp, hpl, hsum⟩
  · refine ⟨algebraMap (AF D.host.F) (AE D) (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (idAt₂ v)
    · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
      refine AddSubgroup.subset_closure ⟨sndA D.host.F (cP (· = v) * algebraMap D.host.F (AF D.host.F) 2⁻¹), fun w => ?_, 1, by simp⟩
      rw [map_mul, AlgHom.commutes, map_mul]
      show evalV D.host.F w (indP (· = v)) * _ ∈ _
      rw [evalV_indP]
      by_cases hw : w = v
      · subst hw
        rw [if_pos rfl, one_mul, AlgHom.commutes]
        exact half_mem_int w h2
      · rw [if_neg hw, zero_mul]
        exact zero_mem _
    · rw [cA_alg, ← map_add (f := _), hεη]
      congr 1
      rw [← two_mul, mul_left_comm, ← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul,
        mul_inv_cancel₀ two_ne_zero, map_one, mul_one]
  · have hs : e + cA D e = ε := by rw [hsum, placeIdem_eq_cP hpl, hεη]
    refine ⟨e, ⟨?_, ?_⟩, hs⟩
    · have : e * ε = e := by rw [← hs, mul_add, hsp.1, hsp.2.1, add_zero]
      rw [← this]
      exact Ideal.mul_mem_left _ _ hεI.1
    · exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hsp.1])

end GlobalTheory.IwaPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∃ w ∈ intAt D (· = v), w + cA D w = ε := by
  first | exact @GlobalTheory.IwaPlace.exists_trace_one_at_tame | exact GlobalTheory.IwaPlace.exists_trace_one_at_tame | (intros; apply GlobalTheory.IwaPlace.exists_trace_one_at_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.VacMove

variable {D : D7}

theorem mt_mul_inv' (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mem_ideal_mul_mul {m n k l : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D))
    (u : Matrix (Fin n) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin l) (AE D)) (hu : ∀ i j, u i j ∈ I) :
    ∀ i j, (A * u * B) i j ∈ I := by
  intro i j
  simp only [Matrix.mul_apply]
  exact I.sum_mem fun x _ => I.mul_mem_right _ (I.sum_mem fun y _ => I.mul_mem_left _ (hu y x))

theorem mem_ideal_mulVec {m n : ℕ} (I : Ideal (AE D)) (A : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → AE D)
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact I.sum_mem fun j _ => I.mul_mem_left _ (hy j)

def pull {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T) : WO S T :=
  HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) u) (Formalism.L2.Theta.mt S g)

theorem smul_latV_mem (S : HSp D) (L : Lat S) (P : Pl D → Prop) (a : D.host.E) (ha : a ∈ D.host.AA) :
    ∀ y ∈ GlobalTheory.FinPl.latV S L P, ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y ∈ GlobalTheory.FinPl.latA S L P := by
  intro y hy
  have key : GlobalTheory.FinPl.latV S L P ≤ (GlobalTheory.FinPl.latA S L P).comap
      (DistribSMul.toAddMonoidHom (Fin S.rank → AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D)) := by
    unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, b, hb, x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hb
    subst hb
    show _ ∈ GlobalTheory.FinPl.latMul S {a | a ∈ D.host.AA} L P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  exact key hy

theorem mulVec_latA_mem (T : HSp D) (LT MT : Lat T) (P : Pl D → Prop) (h : GA D T) (hMT : IsSelfDualC T MT)
    (hmov : Moves T h LT MT P) : ∀ z ∈ GlobalTheory.FinPl.latA T MT P, Formalism.L2.Theta.mt T h⁻¹ *ᵥ z ∈ GlobalTheory.FinPl.latA T LT P := by
  intro z hz
  have key : GlobalTheory.FinPl.latA T MT P ≤ (GlobalTheory.FinPl.latA T LT P).comap (Matrix.mulVecLin (Formalism.L2.Theta.mt T h⁻¹)).toAddMonoidHom := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
    rw [AddSubgroup.closure_le]
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    set y' : Fin T.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] ((1 : D.host.E) * x i) with hy'def
    have hy' : y' ∈ GlobalTheory.FinPl.latV T MT P := AddSubgroup.subset_closure ⟨α, hα, hP, 1, rfl, x, hx, rfl⟩
    have hent : ∀ i, y' i ∈ idAt D P := (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 T).2.2.2 MT y' hMT.1).1 hy' |>.1
    have hy'' : Formalism.L2.Theta.mt T h⁻¹ *ᵥ y' ∈ GlobalTheory.FinPl.latV T LT P := by
      rw [hmov _ (mem_ideal_mulVec _ _ _ hent), Matrix.mulVec_mulVec, mt_mul_inv', Matrix.one_mulVec]
      exact hy'
    have hgen : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • y' := by
      funext i; simp [y', Algebra.TensorProduct.tmul_mul_tmul]
    show Formalism.L2.Theta.mt T h⁻¹ *ᵥ _ ∈ GlobalTheory.FinPl.latMul T {a | a ∈ D.host.AA} LT P
    rw [hgen, Matrix.mulVec_smul]
    exact smul_latV_mem T LT P a ha _ hy''
  exact key hz

theorem vac_of_moves : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  intro D ψ S T χS χT om hW LS LT hLS hLT P f hf g h MS MT hMS hMT hmS hmT
  unfold Vac IsLatVac at hf ⊢
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hmem : ∀ u ∈ latO S T (MS : Set _) (MT : Set _) P,
      pull g h u ∈ latO S T (LS : Set _) (LT : Set _) P := by
    intro u hu
    have hu' := (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T MS MT hMS hMT P u).1 hu
    refine (GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S T LS LT hLS hLT P _).2 ⟨?_, ?_⟩
    · exact mem_ideal_mul_mul (idAt D P) _ _ _ hu'.1
    · intro y hy
      have hent := ((((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 S).2.2.2 LS y hLS.1).1 hy).1
      have h1 : Formalism.L2.Theta.mt S g *ᵥ y ∈ GlobalTheory.FinPl.latV S MS P := (hmS y hent).1 hy
      have h2 := hu'.2 _ h1
      have h3 := mulVec_latA_mem T LT MT P h hMT hmT _ h2
      show (pull g h u) *ᵥ y ∈ _
      unfold pull
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hact : ∀ u : WO S T, actO S T g h (pull g h u) = u := by
    intro u
    unfold actO pull
    simp only [← Matrix.mul_assoc, mt_mul_inv', Matrix.one_mul]
    simp only [Matrix.mul_assoc, mt_mul_inv', Matrix.mul_one]
  have hhalf : ∀ e (u : WO S T), IsHalf e u → IsHalf e (pull g h u) := by
    intro e u hu i j
    unfold pull
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    linear_combination (Formalism.L2.Theta.mt T h⁻¹ i y * Formalism.L2.Theta.mt S g x j) * hu y x
  refine ⟨hW.om_pres (g, h) f hf1, ?_, ?_⟩
  · intro u hu
    have hw := hf2 _ (hmem u hu)
    have e1 := hW.om_heis g h (2 • (pull g h u)) f hf1
    have e2 : actO S T g h (2 • (pull g h u)) = 2 • u := by
      have := hact u
      unfold actO at this ⊢
      rw [two_nsmul, two_nsmul, Matrix.mul_add, Matrix.add_mul, this]
    rw [hw, e2] at e1
    exact e1.symm
  · intro e he u hu hhu
    have hw := hf3 e he _ (hmem u hu) (hhalf e u hhu)
    have e1 := hW.om_heis g h (pull g h u) f hf1
    have e2 : actO S T g h (pull g h u) = u := hact u
    rw [hw, e2] at e1
    exact e1.symm

end GlobalTheory.VacMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLatticeVacuum_of_carriesLatticeCompletions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (f : WO S T → ℂ), Vac ψ S T LS LT P f → ∀ (g : GA D S) (h : GA D T) (MS : Lat S) (MT : Lat T), IsSelfDualC S MS → IsSelfDualC T MT → Moves S g LS MS P → Moves T h LT MT P → Vac ψ S T MS MT P (om (g, h) f) := by
  first | exact @GlobalTheory.VacMove.vac_of_moves | exact GlobalTheory.VacMove.vac_of_moves | (intros; apply GlobalTheory.VacMove.vac_of_moves <;> assumption)
end
end
