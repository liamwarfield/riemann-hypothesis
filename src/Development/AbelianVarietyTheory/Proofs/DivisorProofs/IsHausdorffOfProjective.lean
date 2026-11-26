module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.QuotientMetricDivisors.FinalW
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CEval

theorem eq_zero_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Projective O M] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] (y : M)
    (h : ∀ m : ℕ, ∃ z : M, y = ((p : O) ^ m) • z) : y = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  have h0 : s y = 0 := by
    ext i
    refine eq_of_forall_dvd p fun m => ?_
    obtain ⟨z, hz⟩ := h m
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
    exact dvd_mul_right _ _
  have := LinearMap.congr_fun hs y
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at this
  exact this.symm

theorem isHausdorff_of_projective {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  refine ⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩
  have := dvd_of_smodEq p m (hy m)
  rw [sub_zero] at this
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow, map_natCast]

theorem isEval_comp {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (p : ℕ) {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (h : IsEval p x E)
    (g : A →ₐ[R] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A]
    [Algebra R A] (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] {x : σ → A}
    {E : MvPowerSeries σ R →ₐ[R] A} (hE : IsEval p x E) (u : τ → MvPowerSeries σ R)
    (E' : MvPowerSeries τ R →ₐ[R] A) (hu : ∀ j, constantCoeff (u j) = 0)
    (hE' : IsEval p (fun j => E (u j)) E') (f : MvPowerSeries τ R) : E (subst u f) = E' f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
    (fun c => by
      show E (substAlgHom hs (C c)) = E' (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = E' (X j)
      rw [substAlgHom_X, hE'.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hE'.2 f

end GlobalTheory.CEval

namespace GlobalTheory.QLog.Chart

open GlobalTheory.CEval

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ} (c : Chart G d)

omit c in
theorem isHausdorff₂ (G : PDivGroup p O) (n : ℕ) :
    IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
  isHausdorff_of_projective (O := O) p

theorem ev₂_subst_μ (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (subst c.μ s) = Coalgebra.comul (R := O) (c.ev n s) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
  rw [eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n))
    c.isLaw.const ?_ s]
  · rfl
  convert h using 2 with j
  rw [c.comul n j]
  rfl

theorem ev₂_inL (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL s) = c.ev n s ⊗ₜ[O] (1 : G.A n) := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O)
    (A := G.A n) (B := G.A n))
  rw [inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i))
    ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  exact ⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩

theorem ev₂_inR (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR s) = (1 : G.A n) ⊗ₜ[O] c.ev n s := by
  have := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O)
    (A := G.A n) (B := G.A n))
  rw [inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i))
    ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  convert h using 2 with j
  rw [(c.isEval₂ n).1]
  rfl

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem comul_ev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), Coalgebra.comul (R := O) (c.ev n s) = c.ev n s ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] c.ev n s + c.ev₂ n (cob1 c.μ s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n s
  rw [cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]
  abel

end GlobalTheory.QLog.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerLeOfBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerEqSpanRationalKer
open Module

namespace GlobalTheory

theorem semilinear_pi_eq_sum_single {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.map_smulₛₗ]

theorem span_range_inf_ker_eq_span_rational_ker {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by
  classical
  apply le_antisymm
  · rintro w ⟨hw, hw0⟩
    have hle : Submodule.span ℂ (Set.range j)
        ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [semilinear_pi_eq_sum_single σ j x]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)
    have h0 : f (∑ k, c k • j (Pi.single k 1)) = 0 := hw0
    have h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, map_sum]
      simp only [map_smul, hf, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
      simp
    have h2 : ∀ l, ∑ k, σ (M l k) * c k = 0 := Fintype.linearIndependent_iff.1 hli _ h1
    letI : Algebra K ℂ := σ.toAlgebra
    let b := Basis.ofVectorSpace K ℂ
    let s := Finset.univ.biUnion fun k => (b.repr (c k)).support
    have hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i := by
      intro k
      have h3 := b.linearCombination_repr (c k)
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (s := s)
          (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k))
          _ (by simp)] at h3
      exact h3.symm
    have hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i) := by
      have h5 : ∀ i, b i • j (fun k => b.repr (c k) i)
          = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1) := fun i => by
        rw [semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]
      rw [Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hc k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    ext l
    have h4 : b.repr (∑ k, M l k • c k) i = 0 := by
      have : ∑ k, M l k • c k = 0 := h2 l
      rw [this]; simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply] at h4
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    exact h4
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
    have hx' : M.mulVec x = 0 := hx
    change f (j x) = 0
    rw [hf, hx', map_zero]

end GlobalTheory
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem perCol_base_smul_form (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ)
    (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

theorem perCol_eq_pairing_of_kills (D : D7) (h : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (φ : D.what₂.Mu u)
    (hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK n hnU, add_zero]

theorem span_range_inf_ker_le_of_basis {K : Type} [Field K] (σ : K →+* ℂ) {W E A I : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module K A]
    [Finite I] {n : ℕ} (b : Module.Basis I K A)
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : A →ₛₗ[σ] E) (f : W →ₗ[ℂ] E) (g : (Fin n → K) →ₗ[K] A)
    (hli : LinearIndependent ℂ (fun i => j' (b i))) (hf : ∀ x, f (j x) = j' (g x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f = Submodule.span ℂ (j '' {x | g x = 0}) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let b' := b.reindex e
  let M := LinearMap.toMatrix' (b'.equivFun.toLinearMap ∘ₗ g)
  have hM : ∀ x, M.mulVec x = b'.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have key := span_range_inf_ker_eq_span_rational_ker σ j
    (j'.comp b'.equivFun.symm.toLinearMap) f M ?_ ?_
  · rw [key]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, hM, EmbeddingLike.map_eq_zero_iff]
  · have h1 : (fun l => (j'.comp b'.equivFun.symm.toLinearMap) (Pi.single l 1))
        = (fun i => j' (b i)) ∘ e.symm := by
      funext l
      simp [b', Pi.single_apply]
    rw [h1]
    exact hli.comp _ e.symm.injective
  · intro x
    rw [hf, hM]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCover
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.LfpDescent

theorem exists_linear_retraction (B C : Type*) [CommRing B] [CommRing C] [Algebra B C]
    [Module.Finite B C] [Module.Projective B C] (hinj : Function.Injective (algebraMap B C)) :
    ∃ l : C →ₗ[B] B, l 1 = 1 := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hsum : ∀ x : C, ∑ i, s x i • π (Pi.single i 1) = x := by
    intro x
    have h1 : π (s x) = x := LinearMap.congr_fun hs x
    conv_rhs => rw [← h1]
    rw [LinearMap.pi_apply_eq_sum_univ π (s x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  let T : Ideal B := LinearMap.range (LinearMap.applyₗ (R := B) (M₂ := B) (1 : C))
  have hT : ∀ x i, s x i ∈ T := fun x i =>
    ⟨(LinearMap.proj i) ∘ₗ s ∘ₗ (LinearMap.mulRight B x), by simp⟩
  have hle : (⊤ : Submodule B C) ≤ T • (⊤ : Submodule B C) := by
    intro x _
    rw [← hsum x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hT x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hr1 : r = 0 := by
    apply hinj
    have := hr0 1 trivial
    rw [Algebra.smul_def, mul_one] at this
    simpa using this
  have h1 : (1 : B) ∈ T := by
    have := T.neg_mem hr
    simpa [hr1] using this
  obtain ⟨l, hl⟩ := h1
  exact ⟨l, hl⟩

theorem finitePresentation_of_retract (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Module.Finite A B]
    [Module.Finite A C] [Algebra.FinitePresentation A C] [Module.Finite B C]
    [Module.Projective B C] (hinj : Function.Injective (algebraMap B C)) :
    Algebra.FinitePresentation A B := by
  obtain ⟨l, hl⟩ := exists_linear_retraction B C hinj
  have : Module.FinitePresentation A C :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := A) (S := C)).2 inferInstance
  let l' : C →ₗ[A] B := l.restrictScalars A
  let i : B →ₗ[A] C := (Algebra.linearMap B C).restrictScalars A
  have hli : ∀ b, l' (i b) = b := by
    intro b
    change l (algebraMap B C b) = b
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hl, smul_eq_mul, mul_one]
  have hsurj : Function.Surjective l' := fun b => ⟨i b, hli b⟩
  have hker : LinearMap.ker l' = LinearMap.range (LinearMap.id - i ∘ₗ l') := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    constructor
    · intro hx
      exact ⟨x, by rw [hx, map_zero, sub_zero]⟩
    · rintro ⟨y, rfl⟩
      rw [map_sub, hli, sub_self]
  have hfg : (LinearMap.ker l').FG := by
    rw [hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  have : Module.FinitePresentation A B := Module.finitePresentation_of_surjective l' hsurj hfg
  exact (Module.FinitePresentation.iff_finitePresentation_of_finite (R := A) (S := B)).1 this

theorem ringHom_finitePresentation {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : f.Finite) (hgf : (g.comp f).Finite)
    (hgfp : (g.comp f).FinitePresentation) (hg : g.FaithfullyFlat) : f.FinitePresentation := by
  have hgfin : g.Finite := RingHom.Finite.of_comp_finite hgf
  have hgp : g.FinitePresentation :=
    RingHom.FinitePresentation.of_comp_finiteType f hgfp hf.finiteType
  algebraize [f, g, g.comp f]
  have : Module.FinitePresentation B C :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite (R := B) (S := C)).2 inferInstance
  have : Module.Projective B C := Module.Flat.projective_of_finitePresentation
  exact finitePresentation_of_retract A B C hg.injective

end GlobalTheory.LfpDescent

namespace GlobalTheory.LfpDescent

theorem affine_case {X Y Z : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine Z] (h : X ⟶ Y)
    (f : Y ⟶ Z) [Flat h] [Surjective h] [IsFinite f] [IsFinite (h ≫ f)]
    [LocallyOfFinitePresentation (h ≫ f)] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have hff : h.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine h).1 ⟨inferInstance, inferInstance⟩
  have hfp : (h ≫ f).appTop.hom.FinitePresentation :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ inferInstance
  have hfin1 : f.appTop.hom.Finite := f.finite_appTop
  have hfin2 : (h ≫ f).appTop.hom.Finite := (h ≫ f).finite_appTop
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfp hfin2
  exact ringHom_finitePresentation _ _ hfin1 hfin2 hfp hff

end GlobalTheory.LfpDescent

namespace GlobalTheory


open LfpDescent in
set_option backward.isDefEq.respectTransparency.types false in
theorem locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f →
      LocallyOfFinitePresentation f := by
  intro X Y Z h f _ _ _ _ _ _
  have : IsFinite f := GlobalTheory.isFinite_of_comp_surjective h f
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) (f := f) _
    (iSup_affineOpens_eq_top Z)]
  intro U
  have hU : IsAffine U := U.2
  have e := morphismRestrict_comp h f U
  have h1 : IsFinite ((h ≫ f) ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h2 : LocallyOfFinitePresentation ((h ≫ f) ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @LocallyOfFinitePresentation) inferInstance _
  have : IsAffine (f ⁻¹ᵁ (U : Z.Opens)) := isAffine_of_isAffineHom (f ∣_ U)
  have : IsAffine ((h ≫ f) ⁻¹ᵁ (U : Z.Opens)) := isAffine_of_isAffineHom ((h ≫ f) ∣_ U)
  have : IsAffine (h ⁻¹ᵁ f ⁻¹ᵁ (U : Z.Opens)) := this
  have : Surjective (h ∣_ f ⁻¹ᵁ (U : Z.Opens)) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  have : Flat (h ∣_ f ⁻¹ᵁ (U : Z.Opens)) := IsZariskiLocalAtTarget.restrict (P := @Flat) inferInstance _
  have : IsFinite (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h1' : IsFinite (h ∣_ f ⁻¹ᵁ (U : Z.Opens) ≫ f ∣_ U) := e ▸ h1
  have h2' : LocallyOfFinitePresentation (h ∣_ f ⁻¹ᵁ (U : Z.Opens) ≫ f ∣_ U) := e ▸ h2
  exact affine_case (h ∣_ f ⁻¹ᵁ U) (f ∣_ U)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFinitePresentationOfEtaleCoverStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_finite_presentation_of_etale_cover : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → LocallyOfFinitePresentation f := by
  first | (exact @GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (exact GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale) | (intros; apply GlobalTheory.locallyOfFinitePresentation_of_etale_surjective_comp_finite_etale  <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_isFinite_of_comp_etale_surjective :
    ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) →
      IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  intro X Y Z h f h1 h2 h3 h4 h5 h6
  have : LocallyOfFinitePresentation f := GlobalTheory.T.locally_finite_presentation_of_etale_cover X Y Z h f h1 h2 h3 h4 h5 h6
  exact ⟨etale_of_comp_of_etale_of_surjective h f, isFinite_of_comp_surjective h f⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensor
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KerTensor

theorem exists_factor {O σ A M : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module O M]
    (ev : MvPowerSeries σ O →ₐ[O] A) (hs : Function.Surjective ev)
    (ℓ : MvPowerSeries σ O →ₗ[O] M) (h : ∀ f, ev f = 0 → ℓ f = 0) :
    ∃ l : A →ₗ[O] M, ∀ f, l (ev f) = ℓ f := by
  have hle : LinearMap.ker ev.toLinearMap ≤ LinearMap.ker ℓ := fun f hf => h f hf
  have hs' : Function.Surjective ev.toLinearMap := hs
  refine ⟨(LinearMap.ker ev.toLinearMap).liftQ ℓ hle ∘ₗ
    (ev.toLinearMap.quotKerEquivOfSurjective hs').symm.toLinearMap, fun f => ?_⟩
  have : (ev.toLinearMap.quotKerEquivOfSurjective hs').symm (ev f) = Submodule.Quotient.mk f := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]; rfl
  simp [this]

theorem eval_coe {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (P : MvPolynomial σ O) :
    ev (P : MvPowerSeries σ O) = MvPolynomial.aeval x P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.coe_C, MvPolynomial.aeval_C, ← ev.commutes a]
    rfl
  | add p q hp hq => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p i hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, hx,
      MvPolynomial.aeval_X]

theorem eval_monomial {O σ A : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]
    (ev : MvPowerSeries σ O →ₐ[O] A) (x : σ → A)
    (hx : ∀ i, ev (X i) = x i) (γ : σ →₀ ℕ) (c : O) :
    ev ((MvPolynomial.monomial γ c : MvPolynomial σ O) : MvPowerSeries σ O) =
      c • ∏ i, x i ^ γ i := by
  rw [eval_coe ev x hx, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Algebra.smul_def]

theorem le_degree {σ : Type} [Fintype σ] (γ : σ →₀ ℕ) (k : σ) : γ k ≤ γ.degree := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (f := fun i => γ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem degree_sum {σ τ : Type} [Fintype σ] [Fintype τ] (γ : σ ⊕ τ →₀ ℕ) :
    γ.degree = (Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) : σ →₀ ℕ).degree +
      (Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) : τ →₀ ℕ).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.coe_equivFunOnFinite_symm]

end GlobalTheory.KerTensor

namespace GlobalTheory.KerTensor

theorem ker_tensor : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p O A B σ τ _ _ _ _ _ _ _ x y evA evB E m N hA hB hE sA sB kA kB f hf α hα
  classical
  set I : Ideal O := Ideal.span {(p : O) ^ m} with hI
  have fact : ∀ {ρ R : Type} [CommRing R] [Algebra O R] (ev : MvPowerSeries ρ O →ₐ[O] R),
      Function.Surjective ev → (∀ f, ev f = 0 → ∀ α : ρ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
      ∀ β : ρ →₀ ℕ, β.degree < N → ∃ l : R →ₗ[O] O ⧸ I, ∀ g, l (ev g) = Ideal.Quotient.mk I (coeff β g) := by
    intro ρ R _ _ ev hs hk β hβ
    obtain ⟨l, hl⟩ := exists_factor ev hs ((Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ coeff β) (fun g hg => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hI]
      exact Ideal.mem_span_singleton.2 (hk g hg β hβ))
    exact ⟨l, fun g => by rw [hl]; rfl⟩
  have hdeg := degree_sum α
  set α₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => α (Sum.inl i) with hα₁
  set α₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => α (Sum.inr j) with hα₂
  obtain ⟨l1, hl1⟩ := fact evA sA kA α₁ (by omega)
  obtain ⟨l2, hl2⟩ := fact evB sB kB α₂ (by omega)
  let Λ : A ⊗[O] B →ₗ[O] O ⧸ I := TensorProduct.lift ((LinearMap.mul O (O ⧸ I)).compl₁₂ l1 l2)
  have hΛ : ∀ a b, Λ (a ⊗ₜ b) = l1 a * l2 b := fun a b => by simp [Λ]

  have hmono : ∀ (γ : σ ⊕ τ →₀ ℕ) (c : O),
      Λ (E ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) =
        Ideal.Quotient.mk I (coeff α ((MvPolynomial.monomial γ c : MvPolynomial (σ ⊕ τ) O) : MvPowerSeries (σ ⊕ τ) O)) := by
    intro γ c
    set γ₁ : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => γ (Sum.inl i) with hγ₁
    set γ₂ : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => γ (Sum.inr j) with hγ₂
    have e1 := eval_monomial evA x hA.1 γ₁ 1
    have e2 := eval_monomial evB y hB.1 γ₂ 1
    have eE := eval_monomial E _ hE.1 γ c
    have split : (∏ k, (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) k ^ γ k) =
        (∏ i, x i ^ γ₁ i) ⊗ₜ[O] (∏ j, y j ^ γ₂ j) := by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, hγ₁, hγ₂, Finsupp.coe_equivFunOnFinite_symm]
      have h1 : (∏ i, (x i ⊗ₜ[O] (1 : B)) ^ γ (Sum.inl i)) = (∏ i, x i ^ γ (Sum.inl i)) ⊗ₜ[O] (1 : B) := by
        rw [← Algebra.TensorProduct.includeLeft_apply (S := O), map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeLeft_apply]
      have h2 : (∏ j, ((1 : A) ⊗ₜ[O] y j) ^ γ (Sum.inr j)) = (1 : A) ⊗ₜ[O] (∏ j, y j ^ γ (Sum.inr j)) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_prod]
        simp only [map_pow, Algebra.TensorProduct.includeRight_apply]
      rw [h1, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [eE, split, map_smul, hΛ, ← one_smul O (∏ i, x i ^ γ₁ i), ← e1, ← one_smul O (∏ j, y j ^ γ₂ j),
      ← e2, hl1, hl2]
    simp only [MvPolynomial.coe_monomial, coeff_monomial]
    have hiff : α = γ ↔ α₁ = γ₁ ∧ α₂ = γ₂ := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        ext k
        cases k with
        | inl i => simpa [hα₁, hγ₁] using congrArg (fun g => g i) h1
        | inr j => simpa [hα₂, hγ₂] using congrArg (fun g => g j) h2
    by_cases h : α = γ
    · rw [if_pos h, if_pos (hiff.1 h).1, if_pos (hiff.1 h).2]
      simp [Algebra.smul_def]
    · rw [if_neg h]
      by_cases h1 : α₁ = γ₁
      · rw [if_neg (fun h2 => h (hiff.2 ⟨h1, h2⟩))]; simp
      · rw [if_neg h1]; simp
  have hpoly : ∀ P : MvPolynomial (σ ⊕ τ) O,
      Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = Ideal.Quotient.mk I (coeff α (P : MvPowerSeries (σ ⊕ τ) O)) := by
    intro P
    induction P using MvPolynomial.induction_on' with
    | monomial γ c => exact hmono γ c
    | add P Q hP hQ => rw [MvPolynomial.coe_add, map_add (f := _), map_add (f := _), hP, hQ, map_add (f := _), map_add (f := _)]

  obtain ⟨N', hN'⟩ := hE.2 m
  set K := max N' N with hK
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => K) f with hP
  have hrest : ∀ γ : σ ⊕ τ →₀ ℕ, γ.degree < K → coeff γ (f - (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    intro γ hγ
    have hle : γ ≤ Finsupp.equivFunOnFinite.symm fun _ => K := by
      intro k
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      exact le_of_lt (lt_of_le_of_lt (le_degree γ k) hγ)
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨c, hc⟩ := hN' (f - (P : MvPowerSeries (σ ⊕ τ) O))
    (fun γ hγ => hrest γ (lt_of_lt_of_le hγ (le_max_left _ _)))
  have hzero : Λ (E (f - (P : MvPowerSeries (σ ⊕ τ) O))) = 0 := by
    rw [hc]
    have : (p : A ⊗[O] B) ^ m * c = ((p : O) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [this, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul]
  have hsplit : E f = E (P : MvPowerSeries (σ ⊕ τ) O) + E (f - (P : MvPowerSeries (σ ⊕ τ) O)) := by
    rw [← map_add (f := _), add_sub_cancel]
  have hPval : Λ (E (P : MvPowerSeries (σ ⊕ τ) O)) = 0 := by
    have := congrArg Λ hsplit
    rw [hf, map_zero, map_add (f := _), hzero, add_zero] at this
    exact this.symm
  have hcoeff : coeff α f = coeff α (P : MvPowerSeries (σ ⊕ τ) O) := by
    have := hrest α (lt_of_lt_of_le hα (le_max_right _ _))
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hmk : Ideal.Quotient.mk I (coeff α f) = 0 := by rw [hcoeff, ← hpoly, hPval]
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hmk)

end GlobalTheory.KerTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker : ∀ (p : ℕ) (O A B σ τ : Type) [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] [Fintype σ] [Fintype τ] (x : σ → A) (y : τ → B) (evA : MvPowerSeries σ O →ₐ[O] A) (evB : MvPowerSeries τ O →ₐ[O] B) (E : MvPowerSeries (σ ⊕ τ) O →ₐ[O] A ⊗[O] B) (m N : ℕ), IsEval p x evA → IsEval p y evB → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : B)) fun j => (1 : A) ⊗ₜ[O] y j) E → Function.Surjective evA → Function.Surjective evB → (∀ f, evA f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, evB f = 0 → ∀ α : τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → ∀ f, E f = 0 → ∀ α : σ ⊕ τ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  first | exact @GlobalTheory.KerTensor.ker_tensor | exact GlobalTheory.KerTensor.ker_tensor | (intros; apply GlobalTheory.KerTensor.ker_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLaw
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMulEndo

variable {R : Type} [CommRing R] {d : ℕ}

theorem hasSubst_elim {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j); exacts [hu j, hv j])

theorem constantCoeff_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim hu hv) (by rintro (j | j); exacts [hu j, hv j]) (hμ i)

theorem subst_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {σ τ : Type}
    {u v : Fin d → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {w : σ → MvPowerSeries τ R} (hw : HasSubst w) :
    (fun i => subst w (op μ u v i)) = op μ (fun i => subst w (u i)) (fun i => subst w (v i)) := by
  funext i
  simp only [op, at2]
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hw]
  congr 1
  funext j
  rcases j with j | j <;> rfl

theorem op_comm {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    op μ b a = op μ a b := by
  funext i
  have hs : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j))) :=
    hasSubst_elim (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  have hab := hasSubst_elim ha hb
  have h := congrArg (subst (Sum.elim a b)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [subst_comp_subst_apply hs hab] at h
  have e : (fun s => subst (Sum.elim a b) (Sum.elim (fun j => (X (Sum.inr j) :
      MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with s | s <;> simp [subst_X hab]
  rw [e] at h
  exact h

theorem op_assoc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) :
    op μ (op μ a b) c = op μ a (op μ b c) := by
  have hW : HasSubst (Sum.elim a (Sum.elim b c)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j | j); exacts [ha j, hb j, hc j])
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
    fun i => subst (Sum.elim a (Sum.elim b c)) (F i)) hμ.assoc
  try simp only at h
  rw [subst_op μ (constantCoeff_op μ hμ.const h1 h2) h3 hW, subst_op μ h1 h2 hW,
    subst_op μ h1 (constantCoeff_op μ hμ.const h2 h3) hW, subst_op μ h2 h3 hW] at h
  simpa [x1, x2, x3, subst_X hW] using h

theorem op_interchange {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c e : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0)
    (he : ∀ i, constantCoeff (e i) = 0) :
    op μ (op μ a b) (op μ c e) = op μ (op μ a c) (op μ b e) := by
  rw [op_assoc hμ ha hb (constantCoeff_op μ hμ.const hc he), ← op_assoc hμ hb hc he,
    op_comm hμ hc hb, op_assoc hμ hc hb he,
    ← op_assoc hμ ha hc (constantCoeff_op μ hμ.const hb he)]

theorem op_zero_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (τ : Type) :
    op μ (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = fun _ => 0 := by
  have hw : HasSubst (fun _ : Fin d => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  have hz : subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (0 : MvPowerSeries (Fin d) R) = 0 := by
    rw [← coe_substAlgHom hw, map_zero]
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d) R =>
    fun i => subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (F i)) hμ.unit
  try simp only at h
  rw [subst_op μ (fun i => constantCoeff_X i) (fun _ => map_zero _) hw] at h
  simpa [subst_X hw, hz] using h

theorem subst_nmul_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) :
    (fun j => subst a (nmul μ 0 j)) = fun _ => 0 := by
  funext j
  show subst a (0 : MvPowerSeries (Fin d) R) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

theorem subst_nmul_succ {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) :
    (fun j => subst a (nmul μ (k + 1) j)) = op μ (fun j => subst a (nmul μ k j)) a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [QLogDefect.nmul_succ, subst_op μ (QLogDefect.constantCoeff_nmul hμ k)
    (fun i => constantCoeff_X i) hs]
  congr 1
  funext i
  exact subst_X hs i

theorem constantCoeff_subst_nmul {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) (j : Fin d) :
    constantCoeff (subst a (nmul μ k j)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (QLogDefect.constantCoeff_nmul hμ k j)

theorem subst_nmul_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (k : ℕ)
    {τ : Type} {a b : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun j => subst (op μ a b) (nmul μ k j)) =
      op μ (fun j => subst a (nmul μ k j)) (fun j => subst b (nmul μ k j)) := by
  have hab := constantCoeff_op μ hμ.const ha hb
  induction k with
  | zero =>
    rw [subst_nmul_zero μ hab, subst_nmul_zero μ ha, subst_nmul_zero μ hb, op_zero_zero hμ]
  | succ k ih =>
    rw [subst_nmul_succ μ hμ.const hab, ih, subst_nmul_succ μ hμ.const ha,
      subst_nmul_succ μ hμ.const hb,
      op_interchange hμ (constantCoeff_subst_nmul μ hμ.const ha k)
        (constantCoeff_subst_nmul μ hμ.const hb k) ha hb]

theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  intro R _ d μ hμ k
  refine ⟨QLogDefect.constantCoeff_nmul hμ.const k, fun j => ?_⟩
  have hL : ∀ i, constantCoeff ((fun i => X (Sum.inl i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hR : ∀ i, constantCoeff ((fun i => X (Sum.inr i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hxy : op μ (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inr i)) = μ := by
    funext i
    have e : (Sum.elim (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inr i))) = X := by
      funext s; rcases s with s | s <;> rfl
    show subst _ (μ i) = μ i
    rw [e, subst_self]; rfl
  have h := congrFun (subst_nmul_op hμ k hL hR) j
  rw [hxy] at h
  exact h

end GlobalTheory.NMulEndo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomNmulOfIsLawStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHom_nmul_of_isLaw : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  first | exact @GlobalTheory.NMulEndo.isHom_nmul | exact GlobalTheory.NMulEndo.isHom_nmul | (intros; apply GlobalTheory.NMulEndo.isHom_nmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockP
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem isNil_V_blk_frob_xi :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hUV hnil
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  apply isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a
  refine isNil_of_theta_eq p F.θ F.σ (Fact.out) F.σ_pow _ _ ?_ hnil
  intro i j
  have hU : F.θ (U i j) = F.θ (F.a (V i j)) := by
    obtain ⟨c, hc⟩ := hUV i j
    have h := congrArg F.θ hc
    rw [map_sub, map_mul, theta_tau F hv hε, zero_mul, sub_eq_zero] at h
    exact h
  simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
  rcases j with j | j
  · simp only [Sum.elim_inl, map_mul, map_natCast, hU, F.θ_a, theta_frob_xi hv hε]
  · simp only [Sum.elim_inr, map_mul, map_one, mul_one, hU]

end GlobalTheory.WinLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockPStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_blockFrobeniusXi_ainf_of_frameBlockP : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  first | exact @GlobalTheory.WinLift.isNil_V_blk_frob_xi | exact GlobalTheory.WinLift.isNil_V_blk_frob_xi | (intros; apply GlobalTheory.WinLift.isNil_V_blk_frob_xi <;> assumption)
end
end
