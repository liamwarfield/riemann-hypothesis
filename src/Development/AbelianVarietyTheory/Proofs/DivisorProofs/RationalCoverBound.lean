module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRational
open NumberField

namespace GlobalTheory.RationalSpan


open Classical in
theorem expand {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (v : Fin n → L) :
    v = ∑ j ∈ Finset.univ.biUnion (fun i => (b.repr (v i)).support),
      b j • (fun i => algebraMap K L (b.repr (v i) j)) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (v i)]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset _ (s := Finset.univ.biUnion (fun i => (b.repr (v i)).support))]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  · intro j hj
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩
  · intro j _
    simp

theorem repr_coord {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (a : Fin n → K) (y : Fin n → L) (j : s) :
    b.repr (∑ k, algebraMap K L (a k) * y k) j = ∑ k, a k * b.repr (y k) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [← Algebra.smul_def, map_sum, Finsupp.finsetSum_apply]

theorem map_mulVec_comp {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (M.map (algebraMap K L)).mulVec (fun i => algebraMap K L (x i)) =
      fun i => algebraMap K L (M.mulVec x i) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap K L) M x i).symm

end GlobalTheory.RationalSpan

theorem GlobalTheory.rational_eigen_image_span : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  intro K L _ _ _ n ι A lam e
  classical
  let b := Module.Basis.ofVectorSpace K L
  let f := algebraMap K L
  refine ⟨fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [GlobalTheory.RationalSpan.expand b y]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    intro p
    funext i
    have h1 := congrArg (fun z => b.repr z j) (congrFun (h p) i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [GlobalTheory.RationalSpan.repr_coord] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h1, ← Algebra.smul_def]
    simp
  · let W : Submodule L (Fin n → L) :=
      { carrier := {y | ∀ p, ((A p).map f).mulVec y = f (lam p) • y}
        add_mem' := by
          intro a c ha hc p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_add, ha p, hc p, smul_add]
        zero_mem' := by
          intro p
          simp
        smul_mem' := by
          intro c a ha p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_smul, ha p, smul_comm] }
    have hle : Submodule.span L ((fun x i => f (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x}) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ p
      rw [GlobalTheory.RationalSpan.map_mulVec_comp, hx p]
      funext i
      simp [f, Algebra.smul_def]
    exact hle h
  · obtain ⟨z, rfl⟩ := h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.RationalSpan.expand b z, map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.mulVec (fun i => b.repr (z i) j), ⟨_, rfl⟩, ?_⟩)
    rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]
  · have hle : Submodule.span L ((fun x i => f (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) ≤ LinearMap.range (e.map f).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨fun i => f (w i), by rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]; rfl⟩
    exact hle h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixEigenspaceImageSpannedRationalStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  first | exact @GlobalTheory.rational_eigen_image_span | exact GlobalTheory.rational_eigen_image_span | (intros; apply GlobalTheory.rational_eigen_image_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExt
open NumberField

namespace GlobalTheory

theorem span_inf_span_eq_span_inf_of_rational :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)),
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓
        (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) =
      Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) ''
        ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  intro K L _ _ _ _ _ n M W
  obtain ⟨m, ω, η, hη, hsum⟩ := exists_trace_dual_system K L
  let F : Fin m → (Fin n → L) → (Fin n → K) := fun i y j => Algebra.trace K L (η i * y j)
  have Fadd : ∀ i y z, F i (y + z) = F i y + F i z := by
    intro i y z; funext j; simp [F, mul_add, map_add (f := _)]
  have Fzero : ∀ i, F i 0 = 0 := by intro i; funext j; simp [F]
  have hint : ∀ i (a : 𝓞 L), ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Algebra.trace K L (η i * a) := by
    intro i a
    have h := (Submodule.mem_traceDual.mp (hη i)) (a : L) (Submodule.mem_one.mpr ⟨a, rfl⟩)
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [hc, Algebra.traceForm_apply]⟩
  have Ftr : ∀ i (c : L) (x : Fin n → K),
      F i (c • (fun j => algebraMap K L (x j))) = Algebra.trace K L (η i * c) • x := by
    intro i c x; funext j
    simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ (algebraMap K L (x j)), ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, mul_comm]
  have hsm : ∀ (a : 𝓞 L) (v : Fin n → L), a • v = (a : L) • v := by
    intro a v; funext j; rfl
  have hM : ∀ y ∈ Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))),
      ∀ i (a : 𝓞 L), F i (a • y) ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      obtain ⟨c, hc⟩ := hint i a
      rw [hsm, Ftr, ← hc, algebraMap_smul]
      exact M.smul_mem c hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact M.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact M.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  have hW : ∀ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))),
      ∀ i (a : L), F i (a • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      intro i a
      rw [Ftr]
      exact W.smul_mem _ hx
    | zero => intro i a; rw [smul_zero, Fzero]; exact W.zero_mem
    | add x y _ _ hx hy => intro i a; rw [smul_add, Fadd]; exact W.add_mem (hx i a) (hy i a)
    | smul b x _ hx => intro i a; rw [smul_smul]; exact hx i (a * b)
  apply le_antisymm
  · rintro y ⟨hy1, hy2⟩
    have hy2' : y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K))) :=
      hy2
    have hdec : y = ∑ i, ω i • (fun j => algebraMap K L (F i y j)) := by
      funext j
      rw [Finset.sum_apply, hsum (y j)]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = (ω i : L) * _
      rw [mul_comm]
    rw [hdec]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i y, ?_, rfl⟩)
    refine ⟨?_, ?_⟩
    · simpa using hM y hy1 i 1
    · simpa using hW y hy2' i 1
  · refine le_inf (Submodule.span_mono (Set.image_mono fun x hx => hx.1)) ?_
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx.2, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpanInfRationalSubspaceIntegersExtStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (n : ℕ) (M : Submodule (𝓞 K) (Fin n → K)) (W : Submodule K (Fin n → K)), Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' (M : Set (Fin n → K))) ⊓ (Submodule.span L ((fun x i => algebraMap K L (x i)) '' (W : Set (Fin n → K)))).restrictScalars (𝓞 L) = Submodule.span (𝓞 L) ((fun x i => algebraMap K L (x i)) '' ((M ⊓ W.restrictScalars (𝓞 K) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) := by
  first | exact @GlobalTheory.span_inf_span_eq_span_inf_of_rational | exact GlobalTheory.span_inf_span_eq_span_inf_of_rational | (intros; apply GlobalTheory.span_inf_span_eq_span_inf_of_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalForms
open NumberField

namespace GlobalTheory
open Formalism.IndefR.Arith

theorem mall_eq_span_rat (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (hK : A.IsKsForm) (hρ : ∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) (hc : ∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) : A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  apply le_antisymm
  swap
  · rw [Submodule.span_le]
    rintro y ⟨hy1, hy2⟩
    exact ⟨Submodule.subset_span hy1, hy2⟩
  obtain ⟨n, b, hbK, _, hspK, hliL, hspL⟩ := hK

  set ψ : (Fin n → LL) →ₗ[LL] WL := Fintype.linearCombination LL b with hψdef
  have hψ : ∀ y, ψ y = ∑ k, y k • b k := fun y => by simp [hψdef, Fintype.linearCombination_apply]
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hψ] at hy
    funext i
    exact Fintype.linearIndependent_iff.1 hliL y hy i
  set e : (Fin n → Ks) → (Fin n → LL) := fun x i => algebraMap Ks LL (x i) with he
  have hψe : ∀ x, ψ (e x) = ∑ k, x k • b k := fun x => by
    rw [hψ]; simp [he, algebraMap_smul]

  have hex : ∀ (p : J0) (k : Fin n), ∃ c : Fin n → Ks, ∑ i, c i • b i = A.ρ p (b k) := by
    intro p k
    have : A.ρ p (b k) ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact hρ p _ (hbK k)
    exact (Submodule.mem_span_range_iff_exists_fun Ks).1 this
  choose cc hcc using hex
  let Am : J0 → Matrix (Fin n) (Fin n) Ks := fun p => Matrix.of fun i k => cc p k i
  choose lamK hlamK using hc
  have hρψ : ∀ (p : J0) y, A.ρ p (ψ y) = ψ (((Am p).map (algebraMap Ks LL)).mulVec y) := by
    intro p y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hψ, hψ, map_sum]
    simp only [LinearMap.map_smul, ← hcc, Finset.smul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Am, Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    exact smul_comm _ _ _
  have hmemT : ∀ y, ψ y ∈ A.typeP J0 lam0 ↔ ∀ p : J0, ((Am p).map (algebraMap Ks LL)).mulVec y = algebraMap Ks LL (lamK p) • y := by
    intro y
    rw [FormsL.mem_typeP]
    refine forall_congr' fun p => ?_
    rw [hρψ, hlamK p, ← LinearMap.map_smul]
    exact hψinj.eq_iff
  let Wt : Submodule Ks (Fin n → Ks) :=
    { carrier := {x | ∀ p, (Am p).mulVec x = lamK p • x}
      zero_mem' := fun p => by simp
      add_mem' := fun {x y} hx hy p => by simp [Matrix.mulVec_add, hx p, hy p, smul_add]
      smul_mem' := fun a x hx p => by
        show (Am p).mulVec (a • x) = lamK p • (a • x)
        rw [Matrix.mulVec_smul, hx p, smul_smul, smul_smul, mul_comm] }
  let φ : (Fin n → Ks) →ₗ[𝓞 Ks] WL := (Fintype.linearCombination Ks b).restrictScalars (𝓞 Ks)
  let M : Submodule (𝓞 Ks) (Fin n → Ks) := A.MK.comap φ
  have hMmem : ∀ x, x ∈ M ↔ ∑ k, x k • b k ∈ A.MK := fun x => by simp [M, φ, Fintype.linearCombination_apply]
  have hI1 := (GlobalTheory.T.rational_matrix_eigenspace_image_spanned_rational Ks LL n J0 Am lamK 0).1
  have hI2 := GlobalTheory.T.lattice_span_inf_rational_subspace_integers_ext Ks LL n M Wt
  let ψO : (Fin n → LL) →ₗ[𝓞 LL] WL := ψ.restrictScalars (𝓞 LL)
  rintro y ⟨hy1, hy2⟩
  have hle : Submodule.span (𝓞 LL) (A.MK : Set WL) ≤ (Submodule.span (𝓞 LL) (e '' (M : Set _))).map ψO := by
    rw [Submodule.span_le]
    intro m hm
    have hmK : m ∈ Submodule.span Ks (Set.range b) := by rw [hspK]; exact A.MK_le_WK hm
    obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).1 hmK
    refine ⟨e x, Submodule.subset_span ⟨x, (hMmem x).2 (hx ▸ hm), rfl⟩, ?_⟩
    show ψ (e x) = m
    rw [hψe, hx]
  obtain ⟨z, hz, rfl⟩ := hle hy1
  have hzW : z ∈ Submodule.span LL (e '' (Wt : Set _)) := (hI1 z).1 ((hmemT z).1 hy2)
  have hz2 : z ∈ Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) := by
    rw [← hI2]; exact ⟨hz, hzW⟩
  have hle2 : Submodule.span (𝓞 LL) (e '' ((M ⊓ Wt.restrictScalars (𝓞 Ks) : Submodule (𝓞 Ks) _) : Set _)) ≤ (Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0}).comap ψO := by
    rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxM, hxW⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · show ψ (e x) ∈ A.MK
      rw [hψe]; exact (hMmem x).1 hxM
    · show ψ (e x) ∈ A.typeP J0 lam0
      rw [hmemT]; exact (hI1 (e x)).2 (Submodule.subset_span ⟨x, hxW, rfl⟩)
  exact hle2 hz2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalFormsStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralForms_eq_span_integralRationalForms : ∀ (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ), A.IsKsForm → (∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) → (∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) → A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  first | exact @GlobalTheory.mall_eq_span_rat | exact GlobalTheory.mall_eq_span_rat | (intros; apply GlobalTheory.mall_eq_span_rat <;> assumption)
end
end

open NumberField

namespace GlobalTheory.CovTop

open GlobalTheory.BigTop Formalism.IndefR.FWT

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rho_mem_WK (p : PtAt ex Csz) (i : Fin D.R.m) (g) (f) (hf : f ∈ (p.R.toRealDat.FW i).WK) :
    (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).WK := by
  by_cases hk : ActKeeps (κ := p.κ) p.O i
  · obtain ⟨c, hc⟩ := (p.fw.e i).surjective ⟨f, hf⟩
    obtain ⟨_, h2⟩ := (p.rhoGeo i).1 hk g c
    rw [hc] at h2
    rw [← h2]
    exact Subtype.property _
  · rw [(p.rhoGeo i).2 hk g]
    exact hf

end GlobalTheory.CovTop
