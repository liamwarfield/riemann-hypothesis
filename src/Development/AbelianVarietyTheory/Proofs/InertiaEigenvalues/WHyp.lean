module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def cc (A : Et F E) (e : A.L) (p : A.K × A.K) : A.L :=
  algebraMap A.K A.L p.1 * e + algebraMap A.K A.L p.2 * (1 - e)

def ci (A : Et F E) (e : A.L) (y : A.L) : A.K × A.K :=
  (Algebra.trace A.K A.L (y * e), Algebra.trace A.K A.L (y * (1 - e)))

def kx (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (u b : A.K) : ℂ := A.psiK ψ (x * u * b)

def pt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  fourB ν (kx A ψ x) (fun b => Φ (p.1, b)) p.2

def rg (A : Et F E) (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  Φ (p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 0 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 0,
    p.1 * (g : Matrix (Fin 2) (Fin 2) A.K) 0 1 + p.2 * (g : Matrix (Fin 2) (Fin 2) A.K) 1 1)

def wHyp (A : Et F E) (e : A.L) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K)
    (g : SpecialLinearGroup (Fin 2) A.K) (φ : A.L → ℂ) (y : A.L) : ℂ :=
  pt A ν ψ x (pt A ν ψ x (pt A ν ψ x (rg A g (pt A ν ψ x (fun p => φ (cc A e p)))))) (ci A e y)

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapMemNonZeroDivisorsAdicCompletion
namespace GlobalTheory.BK

open PowerSeries Filter Topology

theorem algebraMap_mem_nonZeroDivisors_adicCompletion {B : Type} [CommRing B] {s : B}
    (hs : s ∈ nonZeroDivisors B) :
    algebraMap B (AdicCompletion (Ideal.span {s}) B) s ∈
      nonZeroDivisors (AdicCompletion (Ideal.span {s}) B) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1) x)
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {s}) (n + 1)) hx
  rw [map_mul, map_zero, AlgHom.commutes, ← hr, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 : (r - s ^ n * c) * s = 0 := by rw [sub_mul, hc]; ring
  have h3 := (mem_nonZeroDivisors_iff_right.1 hs) _ h2
  rw [evalₐ_of_succ _ hr.symm, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨c, sub_eq_zero.1 h3⟩

theorem Ehat_mem_nonZeroDivisors (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    [CompleteSpace K] : Ehat O K l e ∈ nonZeroDivisors (Ahat O K l e) := by
  have hE : E (K := K) l e ≠ 0 := by
    intro h
    have hcoeff := congrArg (coeff e) h
    rw [E, map_add, coeff_X_pow_self, ← map_natCast (C : K →+* K⟦X⟧),
      coeff_C_of_ne_zero (NeZero.ne e), add_zero, map_zero] at hcoeff
    exact one_ne_zero hcoeff
  let s : invL l (A O K) :=
    ⟨E (K := K) l e, by
      unfold E
      exact add_mem (pow_mem HasU.X_mem e) (natCast_mem _ l)⟩
  exact algebraMap_mem_nonZeroDivisors_adicCompletion (s := s)
    (mem_nonZeroDivisors_of_ne_zero fun h => hE (congrArg Subtype.val h))

end GlobalTheory.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TestFn

theorem unif_const (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ)
    (hf : IsTest f) : ∃ V ∈ 𝓝 (0 : X), ∀ x v, v ∈ V → f (x + v) = f x := by
  classical
  have hC : IsCompact (tsupport f) := hf.2
  have hW : ∀ x : X, ∃ W ∈ 𝓝 (0 : X), ∀ w₁ ∈ W, ∀ w₂ ∈ W, f (x + w₁ + w₂) = f x := by
    intro x
    have ho : IsOpen (f ⁻¹' {f x}) := hf.1.isOpen_fiber (f x)
    have hmem : f ⁻¹' {f x} ∈ 𝓝 (x + (0 : X) + 0) := by simpa using ho.mem_nhds (by simp)
    have hcont : Continuous (fun p : X × X => x + p.1 + p.2) := by fun_prop
    have h2 := hcont.continuousAt (x := ((0 : X), (0 : X))) hmem
    rw [nhds_prod_eq] at h2
    obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := Filter.mem_prod_iff.mp h2
    refine ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, fun w₁ h₁ w₂ h₂ => ?_⟩
    exact hsub (Set.mk_mem_prod h₁.1 h₂.2)
  choose W hW0 hWf using hW
  have hnb : ∀ x ∈ tsupport f, (fun w => x + w) '' W x ∈ 𝓝 x := by
    intro x _
    have h1 : (fun w => x + w) '' W x = (fun y => -x + y) ⁻¹' W x := by
      ext y; constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hy; exact ⟨-x + y, hy, by abel⟩
    rw [h1]
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW0 x)
  obtain ⟨t, htC, hcover⟩ := hC.elim_nhds_subcover _ hnb
  set V₀ : Set X := ⋂ x ∈ t, W x
  have hV₀ : V₀ ∈ 𝓝 (0 : X) := (Filter.biInter_finset_mem t).mpr fun x _ => hW0 x
  have hcase : ∀ y ∈ tsupport f, ∀ v ∈ V₀, f (y + v) = f y := by
    intro y hy v hv
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    obtain ⟨w, hw, rfl⟩ := hyx
    have hvx : v ∈ W x := Set.mem_iInter₂.mp hv x hxt
    have e1 := hWf x w hw v hvx
    have e2 : f (x + w) = f x := by simpa using hWf x w hw 0 (mem_of_mem_nhds (hW0 x))
    rw [e2, ← e1]
  refine ⟨V₀ ∩ (fun v => -v) ⁻¹' V₀, Filter.inter_mem hV₀ (continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV₀)),
    fun x v hv => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hcase x hx v hv.1
  by_cases hxv : x + v ∈ tsupport f
  · have := hcase (x + v) hxv (-v) hv.2
    simp only [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxv]

theorem slice_test {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (T : X × Y → ℂ) (hT : IsTest T) (y : Y) :
    IsTest (fun x => T (x, y)) := by
  refine ⟨hT.1.comp_continuous (Continuous.prodMk_left y), ?_⟩
  have hc : IsCompact (Prod.fst '' tsupport T) := hT.2.image continuous_fst
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  have h1 : IsClosed ((fun x => (x, y)) ⁻¹' tsupport T) := (isClosed_tsupport T).preimage (Continuous.prodMk_left y)
  refine (closure_minimal ?_ h1).trans ?_
  · intro x hx; exact subset_tsupport T hx
  · intro x hx; exact ⟨(x, y), hx, rfl⟩

end GlobalTheory.TestFn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def mulMat {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' ((j : A.L →ₗ[E] (Fin r → E)) ∘ₗ LinearMap.mulLeft E y ∘ₗ (j.symm : (Fin r → E) →ₗ[E] A.L))

theorem mulMat_mulVec {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) (v : Fin r → E) :
    A.mulMat j y *ᵥ v = j (y * j.symm v) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem mulMat_mulVec_apply {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y z : A.L) :
    A.mulMat j y *ᵥ j z = j (y * z) := by
  simp [mulMat_mulVec]

theorem mulMat_mul {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y y' : A.L) :
    A.mulMat j (y * y') = A.mulMat j y * A.mulMat j y' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_assoc]

theorem mulMat_one {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) : A.mulMat j 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [mulMat_mulVec]

theorem mulMat_mem_unitaryGroup {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j)
    (t : unitary A.L) : A.mulMat j t ∈ Matrix.unitaryGroup (Fin r) E := by
  rw [Matrix.mem_unitaryGroup_iff']
  set N := star (A.mulMat j t) * A.mulMat j t
  have key : ∀ v w : Fin r → E, star v ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨a, rfl⟩ := j.surjective v
    obtain ⟨b, rfl⟩ := j.surjective w
    have h1 : star (j a) ⬝ᵥ (N *ᵥ j b) = star (A.mulMat j t *ᵥ j a) ⬝ᵥ (A.mulMat j t *ᵥ j b) := by
      simp only [N, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    rw [h1, mulMat_mulVec_apply, mulMat_mulVec_apply, hx, hx]
    congr 1
    have ht : star (t : A.L) * t = 1 := Unitary.star_mul_self_of_mem t.2
    calc algebraMap A.K A.L x * star ((t : A.L) * a) * ((t : A.L) * b)
        = algebraMap A.K A.L x * star a * b * (star (t : A.L) * t) := by rw [star_mul]; ring
      _ = _ := by rw [ht, mul_one]
  have hw : ∀ w, N *ᵥ w = w := by
    intro w
    funext i
    have := key (Pi.single i 1) w
    simpa [single_dotProduct] using this
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp [hw]

def uHom {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) :
    unitary A.L →* Matrix.unitaryGroup (Fin r) E where
  toFun t := ⟨A.mulMat j t, A.mulMat_mem_unitaryGroup hx t⟩
  map_one' := by ext1; simp [mulMat_one]
  map_mul' t t' := by ext1; simp [mulMat_mul]

theorem uHom_apply {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (t : unitary A.L) :
    (A.uHom hx t : Matrix (Fin r) (Fin r) E) = A.mulMat j t := rfl

def descFn {r : ℕ} (M : GlobalTheory.JR.Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E))
    (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ) (f : Hn r F E → ℂ) (y : A.L) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g (Ax, j y, lam)) * (α g : ℂ) ∂M.μU

end GlobalTheory.JR.Et
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixedBasis
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.GaloisDescentLattice

theorem sigma_smul {K : UQ} (B : InvAlg K) {a b : K.O}
    (hab : K.c (algebraMap K.O K.E a) = algebraMap K.O K.E b) (y : B.A) :
    B.σ (a • y) = b • B.σ y := by
  rw [← algebraMap_smul K.E a y, ← algebraMap_smul K.E b (B.σ y), Algebra.smul_def, Algebra.smul_def,
    map_mul, B.σ_alg, hab]

theorem exists_fixed_basis : ∀ (K : UQ) (B : InvAlg K) (M : Submodule K.O B.A), IsLat K.O K.E M →
    (∀ y ∈ M, B.σ y ∈ M) → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A,
      Submodule.span K.O (Set.range e) = M ∧ ∀ i, B.σ (e i) = e i := by
  intro K B M hM hσ
  obtain ⟨d, d', hdd', hunit⟩ := K.c_res
  have hd'd : K.c (algebraMap K.O K.E d') = algebraMap K.O K.E d := by rw [← hdd', K.c_c]
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hunit).exists_left_inv

  let S : Type := {y : B.A // y ∈ M ∧ B.σ y = y}
  let v : S → M := fun s => ⟨s.1, s.2.1⟩
  have hspan : Submodule.span K.O (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : B.σ y ∈ M := hσ y hy
    have h1m : y + B.σ y ∈ M := M.add_mem hy hy'
    have h2m : d • y + d' • B.σ y ∈ M := M.add_mem (M.smul_mem d hy) (M.smul_mem d' hy')
    have h1f : B.σ (y + B.σ y) = y + B.σ y := by rw [map_add (f := _), B.σ_σ, add_comm]
    have h2f : B.σ (d • y + d' • B.σ y) = d • y + d' • B.σ y := by
      rw [map_add (f := _), sigma_smul B hdd', sigma_smul B hd'd, B.σ_σ, add_comm]
    have hmem1 : (⟨y + B.σ y, h1m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h1m, h1f⟩, rfl⟩
    have hmem2 : (⟨d • y + d' • B.σ y, h2m⟩ : M) ∈ Submodule.span K.O (Set.range v) :=
      Submodule.subset_span ⟨⟨_, h2m, h2f⟩, rfl⟩
    have hy_eq : (⟨y, hy⟩ : M) = u • ((⟨d • y + d' • B.σ y, h2m⟩ : M) - d' • (⟨y + B.σ y, h1m⟩ : M)) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sub, smul_add]
      have : d • y + d' • B.σ y - (d' • y + d' • B.σ y) = (d - d') • y := by rw [sub_smul]; abel
      rw [this, smul_smul, hu, one_smul]
    rw [hy_eq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem2 (Submodule.smul_mem _ _ hmem1))

  haveI : Module.Finite K.O M := Module.Finite.iff_fg.mpr hM.1
  haveI : Module.IsTorsionFree K.O M := ⟨fun r hr x y hxy => by
    have hr0 : r ≠ 0 := hr.ne_zero
    have h0 : algebraMap K.O K.E r ≠ 0 := by
      intro h; exact hr0 (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
    change r • x = r • y at hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [Submodule.coe_smul] at this
    rw [← algebraMap_smul K.E r (x : B.A), ← algebraMap_smul K.E r (y : B.A)] at this
    exact smul_right_injective B.A h0 this⟩
  haveI : Module.Free K.O M := Module.free_of_finite_type_torsion_free'
  haveI : Module.FinitePresentation K.O M := Module.finitePresentation_of_finite K.O M
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hspan
  haveI : Finite κ := Module.Finite.finite_basis b
  let w : κ → B.A := fun i => (b i : B.A)
  have hwO : LinearIndependent K.O w :=
    b.linearIndependent.map' M.subtype M.ker_subtype
  have hwE : LinearIndependent K.E w := (LinearIndependent.iff_fractionRing K.O K.E).mp hwO
  have hspanO : Submodule.span K.O (Set.range w) = M := by
    have : Set.range w = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanE : ⊤ ≤ Submodule.span K.E (Set.range w) := by
    rw [← hM.2, Submodule.span_le]
    intro x hx
    have : x ∈ Submodule.span K.O (Set.range w) := by rw [hspanO]; exact hx
    exact Submodule.span_le_restrictScalars K.O K.E _ this
  let bE : Module.Basis κ K.E B.A := Module.Basis.mk hwE hspanE
  let e := bE.reindex (bE.indexEquiv (Module.finBasis K.E B.A))
  refine ⟨e, ?_, ?_⟩
  · rw [Module.Basis.range_reindex, Module.Basis.coe_mk]; exact hspanO
  · intro i
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    show B.σ (b _ : B.A) = (b _ : B.A)
    rw [hb]
    exact (a _).2.2

end GlobalTheory.GaloisDescentLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHom
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Step.InvMap

variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}

theorem mom_glMap (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  have hp : (Y.1.map φ) ^ i = (Y.1 ^ i).map φ := by
    have := map_pow φ.mapMatrix Y.1 i
    simpa only [RingHom.mapMatrix_apply] using this.symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mom, glMap, hp, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

theorem inv_glMap (Y : Gl r k) : GlobalTheory.JR.inv (glMap φ Y) = (GlobalTheory.JR.inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, glMap, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_glMap φ Y i

theorem sec_map (a : Inv r k) : sec (a.map φ) = glMap φ (sec a) := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · ext i j
    simp only [sec, companion, glMap, Inv.map, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  · funext i
    simp only [sec, glMap]
    split_ifs <;> simp

theorem Delta_map (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  rw [Delta, Delta, RingHom.map_det]
  congr 1
  ext i j
  simp only [hankel, sec_map, mom_glMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]

private theorem mom_glMap_eq_map_mom (ψ : k →+* k') (Y : _root_.GlobalTheory.JR.Gl r k) (n : ℕ) :
    _root_.GlobalTheory.JR.mom (_root_.GlobalTheory.JR.Step.glMap ψ Y) n = ψ (_root_.GlobalTheory.JR.mom Y n) := by
  unfold _root_.GlobalTheory.JR.mom _root_.GlobalTheory.JR.Step.glMap
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_pow]
  rfl

private theorem sec_map_eq_glMap_sec (ψ : k →+* k') (a : _root_.GlobalTheory.JR.Inv r k) :
    _root_.GlobalTheory.JR.sec (a.map ψ) = _root_.GlobalTheory.JR.Step.glMap ψ (_root_.GlobalTheory.JR.sec a) := by
  unfold _root_.GlobalTheory.JR.sec _root_.GlobalTheory.JR.Inv.map _root_.GlobalTheory.JR.Step.glMap
  simp only [_root_.GlobalTheory.JR.ImgSec.companion_map, Prod.mk.injEq, true_and, and_true]
  funext i
  split_ifs <;> simp

theorem _root_.GlobalTheory.JR.Step.InvMap.inv_and_Delta_map : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ),
    (∀ Y : _root_.GlobalTheory.JR.Gl r k, _root_.GlobalTheory.JR.inv (_root_.GlobalTheory.JR.Step.glMap φ Y) = (_root_.GlobalTheory.JR.inv Y).map φ) ∧
      (∀ a : _root_.GlobalTheory.JR.Inv r k, _root_.GlobalTheory.JR.Delta (a.map φ) = φ (_root_.GlobalTheory.JR.Delta a)) := by
  intro k k' _ _ φ r
  refine ⟨fun Y => ?_, fun a => ?_⟩
  · unfold _root_.GlobalTheory.JR.inv _root_.GlobalTheory.JR.Inv.map
    simp only [mom_glMap_eq_map_mom]
    refine Prod.ext ?_ rfl
    funext i
    simp [_root_.GlobalTheory.JR.Step.glMap, Matrix.charpoly_map]
  · unfold _root_.GlobalTheory.JR.Delta
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.JR.hankel, sec_map_eq_glMap_sec, mom_glMap_eq_map_mom]

end GlobalTheory.JR.Step.InvMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedInvariantsAndHankelDetMapRingHomStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borderedInvariants_and_hankelDet_map_ringHom : ∀ (k k' : Type) [CommRing k] [CommRing k'] (φ : k →+* k') (r : ℕ), (∀ Y : Gl r k, inv (GlobalTheory.JR.Step.glMap φ Y) = (inv Y).map φ) ∧ (∀ a : Inv r k, Delta (a.map φ) = φ (Delta a)) := by
  first | exact @GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | exact GlobalTheory.JR.Step.InvMap.inv_and_Delta_map | (intros; apply GlobalTheory.JR.Step.InvMap.inv_and_Delta_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlock
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

private theorem addChar_dotProduct_eq_one_of_norm_le {F : Type} [NontriviallyNormedField F]
    [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : _root_.GlobalTheory.JR.IsStdChar ψ) {r : ℕ}
    {R : ℝ} (x δ : Fin r → F) (hx : ‖x‖ ≤ R) (hδ : ‖δ‖ * R ≤ 1) : ψ (x ⬝ᵥ δ) = 1 := by
  apply hψ.1
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  calc ‖x i‖ * ‖δ i‖ ≤ R * ‖δ‖ :=
        mul_le_mul ((norm_le_pi_norm x i).trans hx) (norm_le_pi_norm δ i) (norm_nonneg _)
          ((norm_nonneg _).trans hx)
    _ = ‖δ‖ * R := mul_comm _ _
    _ ≤ 1 := hδ

theorem _root_.GlobalTheory.JR.fourG_isLocallyConstant_of_invariant :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [_root_.GlobalTheory.JR.Unram F E] (r : ℕ) (M : _root_.GlobalTheory.JR.Meas r F E) (ψ : AddChar F ℂ),
      _root_.GlobalTheory.JR.IsStdChar ψ → ∀ f' : _root_.GlobalTheory.JR.Gl r F → ℂ, _root_.GlobalTheory.JR.IsTest f' →
      (∃ U ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F), ∀ Y : _root_.GlobalTheory.JR.Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
      IsLocallyConstant (_root_.GlobalTheory.JR.fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f hf ⟨U, hU, hUf⟩
  haveI := _root_.GlobalTheory.JR.Unram.ultraF (F := F) E
  obtain ⟨C, hC⟩ := hf.2.isCompact.exists_bound_of_continuousOn
    (f := fun x : _root_.GlobalTheory.JR.Gl r F => (x.2.1, x.2.2.1))
    (continuous_snd.fst.prodMk continuous_snd.snd.fst).continuousOn
  set R : ℝ := |C| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hCR : C ≤ R := (le_abs_self C).trans (by rw [hRdef]; linarith)
  have hbd : ∀ x ∈ tsupport f, ‖x.2.1‖ ≤ R ∧ ‖x.2.2.1‖ ≤ R := by
    intro x hx
    have h : ‖(x.2.1, x.2.2.1)‖ ≤ C := hC x hx
    exact ⟨(norm_fst_le (x.2.1, x.2.2.1)).trans (h.trans hCR),
      (norm_snd_le (x.2.1, x.2.2.1)).trans (h.trans hCR)⟩
  let P : _root_.GlobalTheory.JR.Gl r F → _root_.GlobalTheory.JR.Gl r F := fun u => (u.1, 0, 0, u.2.2.2)
  have hP : Continuous P :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hP0 : P 0 = 0 := rfl
  set W : Set (_root_.GlobalTheory.JR.Gl r F) :=
    P ⁻¹' U ∩ {u | ‖u.2.1‖ < R⁻¹} ∩ {u | ‖u.2.2.1‖ < R⁻¹} with hWdef
  have hW : W ∈ 𝓝 (0 : _root_.GlobalTheory.JR.Gl r F) := by
    refine inter_mem (inter_mem (hP.continuousAt.preimage_mem_nhds (by rwa [hP0])) ?_) ?_
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
    · exact (isOpen_lt (continuous_norm.comp continuous_snd.snd.fst) continuous_const).mem_nhds
        (by simp [hRpos])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro Y
  have hnb : {Y' | Y' - Y ∈ W} ∈ 𝓝 Y :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hW)
  filter_upwards [hnb] with Y' hY'
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hY'
  obtain ⟨u, rfl⟩ : ∃ u, Y' = Y + u := ⟨Y' - Y, by abel⟩
  simp only [add_sub_cancel_left] at hu1 hu2 hu3
  unfold _root_.GlobalTheory.JR.fourG
  congr 1; funext b'; congr 1; funext c'
  have hfeq : f ((Y + u).1, b', c', (Y + u).2.2.2) = f (Y.1, b', c', Y.2.2.2) := by
    have := hUf (Y.1, b', c', Y.2.2.2) (P u) hu1
    convert this using 2
    ext <;> simp [P]
  rw [hfeq]
  by_cases h0 : f (Y.1, b', c', Y.2.2.2) = 0
  · simp [h0]
  have hmem : (Y.1, b', c', Y.2.2.2) ∈ tsupport f := subset_tsupport f h0
  obtain ⟨hb', hc'⟩ := hbd _ hmem
  have e1 : ψ (c' ⬝ᵥ u.2.1) = 1 := addChar_dotProduct_eq_one_of_norm_le hψ c' u.2.1 hc'
    (by rw [← le_div_iff₀ hRpos, one_div]; exact hu2.le)
  have e2 : ψ (u.2.2.1 ⬝ᵥ b') = 1 := by
    rw [dotProduct_comm]
    exact addChar_dotProduct_eq_one_of_norm_le hψ b' u.2.2.1 hb'
      (by rw [← le_div_iff₀ hRpos, one_div]; exact hu3.le)
  have hsum : c' ⬝ᵥ (Y + u).2.1 + (Y + u).2.2.1 ⬝ᵥ b' =
      (c' ⬝ᵥ Y.2.1 + Y.2.2.1 ⬝ᵥ b') + c' ⬝ᵥ u.2.1 + u.2.2.1 ⬝ᵥ b' := by
    simp only [Prod.snd_add, Prod.fst_add, dotProduct_add, add_dotProduct]
    abel
  rw [hsum, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, e1, e2, mul_one, mul_one]

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlockStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → IsLocallyConstant (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | exact GlobalTheory.JR.fourG_isLocallyConstant_of_invariant | (intros; apply GlobalTheory.JR.fourG_isLocallyConstant_of_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultant
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.DetAdResultant
theorem det_aeval_eq_resultant_of_splits {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (g : K[X]) (hg : g.Monic) (hs : g.Splits) :
    (aeval A g).det = resultant A.charpoly g := by
  rw [resultant_comm, resultant_eq_prod_eval g A.charpoly _ le_rfl hs, hg.leadingCoeff, one_pow, one_mul]
  let φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toMonoidHom
  have hφ : ∀ p, φ p = (aeval A p).det := fun p => rfl
  have h1 : ∀ x : K, φ (X - C x) = (-1) ^ Fintype.card ι * eval x A.charpoly := by
    intro x
    rw [hφ]
    simp only [map_sub, aeval_X, aeval_C, Matrix.eval_charpoly]
    rw [← Matrix.det_neg, neg_sub]
    rfl
  rw [← hφ]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hg]
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    Matrix.charpoly_natDegree_eq_dim, ← hs.natDegree_eq_card_roots]

theorem det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by
  let K := AlgebraicClosure E
  apply (algebraMap E K).injective
  have h := det_aeval_eq_resultant_of_splits (A.map (algebraMap E K)) (g.map (algebraMap E K))
    (hg.map _) (IsAlgClosed.splits _)
  rw [Matrix.charpoly_map, natDegree_map, natDegree_map, resultant_map_map] at h
  rw [← h, RingHom.map_det]
  congr 1
  have e : (algebraMap E K).mapMatrix (aeval A g) = (Algebra.ofId E K).mapMatrix (aeval A g) := rfl
  rw [e, ← aeval_algHom_apply, aeval_map_algebraMap]
  rfl
theorem det_det_charmatrix {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)

theorem toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply]
  have hr : ∀ M : Matrix ι₁ ι₂ E, (Matrix.stdBasis E ι₁ ι₂).repr M (a, j) = M a j := fun M => rfl
  have hψ : LinearMap.toMatrix b₂ b₁ (b₂.linearMap b₁ (b, k)) = Matrix.single b k 1 := by
    simp [Module.Basis.linearMap, Matrix.stdBasis_eq_single]
  rw [hr, LinearMap.sub_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply', map_sub,
    LinearMap.toMatrix_comp b₂ b₁ b₁, LinearMap.toMatrix_comp b₂ b₂ b₁, hψ]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Matrix.comp_apply, Matrix.map_apply, Matrix.charmatrix_apply, Matrix.transpose_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply, hjk, Matrix.diagonal_apply_ne _ hjk]
    by_cases hab : a = b
    · subst hab; simp [Ne.symm hjk]
    · simp [hab, Ne.symm hab, Ne.symm hjk]

theorem det_ad_eq_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁]
    [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂),
    LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      resultant f₁.charpoly f₂.charpoly := by
  intro E _ V₁ V₂ _ _ _ _ _ _ f₁ f₂
  let b₁ := Module.finBasis E V₁
  let b₂ := Module.finBasis E V₂
  rw [← LinearMap.det_toMatrix (b₂.linearMap b₁), toMatrix_ad b₁ b₂, Matrix.det_reindex_self,
    det_det_charmatrix, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end GlobalTheory.DetAdResultant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultantStatement
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_commutator_map_eq_charpoly_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by
  first | exact @GlobalTheory.DetAdResultant.det_ad_eq_resultant | exact GlobalTheory.DetAdResultant.det_ad_eq_resultant | (intros; apply GlobalTheory.DetAdResultant.det_ad_eq_resultant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Et

theorem charpoly_dvd_pow_of_aeval_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem aeval_self_charpoly_lmul (A : Et F E) (z : A.K) :
    aeval z (LinearMap.charpoly (Algebra.lmul F A.K z)) = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
  have h' : Algebra.lmul F A.K (aeval z (LinearMap.charpoly (Algebra.lmul F A.K z))) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End F A.K => f 1) h'

theorem mem_OK_iff_isIntegral [IsUltrametricDist F] (A : Et F E) (z : A.K) :
    z ∈ A.OK ↔ IsIntegral (NormedField.valuation (K := F)).integer z := by
  constructor
  · intro hz
    have hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈
        Polynomial.lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      refine ⟨⟨_, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hz i
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]
    exact aeval_self_charpoly_lmul A z
  · rintro ⟨p, hpm, hp⟩ i
    have hp' : aeval z (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hp
    have h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, hp', map_zero]
    let bs := Module.finBasis F A.K
    have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z))
        (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, h1, map_zero]
    have h3 := charpoly_dvd_pow_of_aeval_zero _ _ h2
    have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly =
        LinearMap.charpoly (Algebra.lmul F A.K z) := LinearMap.charpoly_toMatrix _ bs
    rw [h4, ← Polynomial.map_pow] at h3
    have h5 := Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i
    have h6 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h6
    exact_mod_cast h6

theorem OK_isSubring : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  refine ⟨(integralClosure (NormedField.valuation (K := F)).integer A.K).toSubring, ?_⟩
  ext z
  exact (mem_OK_iff_isIntegral A z).symm

end GlobalTheory.JR.Et
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOKStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subring_eq_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  first | exact @GlobalTheory.JR.Et.OK_isSubring | exact GlobalTheory.JR.Et.OK_isSubring | (intros; apply GlobalTheory.JR.Et.OK_isSubring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open Polynomial

theorem mem_adjoin_of_pow_eq_one_of_isUnit {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hzR : IsIntegral R z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    simp [eval₂_sub, hz]
  have hzF : IsIntegral F z := hzR.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzF hadj
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzF hadj
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)
  rw [hgen] at hmem
  haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by
    rw [Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L,
      map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff] at hx
    exact hx
  have hIntAe : ∀ p : R[X], IsIntegral R (aeval z p) := fun p =>
    adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)
  set m := minpoly R z with hm
  obtain ⟨h, hmh⟩ : m ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])
  have hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h := by
    have := congrArg (fun p => aeval z (derivative p)) hmh
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add (f := _), map_mul] at this
    have h0 : aeval z m = 0 := minpoly.aeval R z
    simpa [h0] using this
  have hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)
  obtain ⟨ra, hra⟩ := hint _ (hIntAe (derivative m))
  obtain ⟨rb, hrb⟩ := hint _ (hIntAe h)
  obtain ⟨rz, hrz⟩ := hint _ hzR
  have hinj := IsFractionRing.injective R F
  have hrzN : rz ^ N = 1 := hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])
  have hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1) := by
    apply hinj
    have hNL : ((N : L)) = algebraMap F L (N : F) := (map_natCast _ _).symm
    rw [map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL,
      Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]
  have hra_unit : IsUnit ra := by
    have : IsUnit (ra * rb) := by
      rw [hprod]
      have hrzu : IsUnit rz := isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩
      exact (hN.pow _).mul (hrzu.pow _)
    exact isUnit_of_mul_isUnit_left this
  have hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]
  obtain ⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) :=
    ((isUnit_one.neg).pow _).mul hra_unit
  rw [hdisc, ← hv, algebraMap_smul] at hmem
  have : y = (↑v⁻¹ : R) • ((v : R) • y) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _

end GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  intro K K' d φ hφ hd z hz hadj y hy
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  have hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    haveI := Fintype.ofFinite (ResidueField K.O)
    have hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0 := by
      rw [← K.card_res, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hq : 1 ≤ K'.q ^ 2 := by
      rw [hφ.1, ← pow_mul, mul_comm, pow_mul]
      apply Nat.one_le_pow
      rw [← K.card_res]; exact Nat.card_pos
    rw [Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.2 one_ne_zero
  exact mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_primitiveRoot_eq_integers_unramifiedQuadratic : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  first | exact @GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | exact GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers | (intros; apply GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers <;> assumption)
end
end
