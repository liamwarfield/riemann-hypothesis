module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CasFamily

theorem sum_squares_eq {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (X Y : Fin a → Fin a → A) :
    ∑ i, ∑ j, ((X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
        ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i))) =
      (8 : ℂ) • (Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
        Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j))) := by
  have h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
      ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) =
      (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) -
        ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j)) := by
    intro i j
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    match_scalars <;> ring
  have h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) +
      ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) =
      (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i) := by
    intro i j
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
    match_scalars <;> ring_nf <;> simp <;> norm_num
  have hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i := Finset.sum_comm
  have hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i := Finset.sum_comm
  have hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
      Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)) := by
    simp only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]
  rw [hc]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]
  match_scalars <;> norm_num

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def sgl (i j : Fin a) : Cinf E →ₗ[ℝ] Lie E a :=
  (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

def eW (w : InfinitePlace E) : Cinf E := atEmb w.embedding 1

def fW (w : InfinitePlace E) : Cinf E := atEmb w.embedding Complex.I

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) :
    star (atEmb w.embedding z) = atEmb w.embedding (starRingEnd ℂ z) := by
  classical
  funext v
  rw [Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_eW (w : InfinitePlace E) : star (eW w) = eW w := by
  simp [eW, star_atEmb]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem star_fW (w : InfinitePlace E) : star (fW w) = -fW w := by
  classical
  funext v
  simp only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem sum_atEmb (x : Cinf E) : x = ∑ w, ((x w).re • eW w + (x w).im • fW w) := by
  classical
  have e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w) := fun w =>
    (atEmb_eq _ _).symm
  simp only [e]
  funext v
  simp [Finset.sum_apply, atEmb_embedding_apply]

def famZ : InfinitePlace E × Fin a × Fin a × Bool × Bool → Lie E a
  | (w, i, j, false, false) => sgl i j (eW w) + sgl j i (eW w)
  | (w, i, j, false, true) => sgl i j (eW w) - sgl j i (eW w)
  | (w, i, j, true, false) => sgl i j (fW w) - sgl j i (fW w)
  | (w, i, j, true, true) => sgl i j (fW w) + sgl j i (fW w)

theorem span_famZ : Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS
  have hz : ∀ k, famZ (E := E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hE : ∀ w i j, sgl (E := E) (a := a) i j (eW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (eW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hF : ∀ w i j, sgl (E := E) (a := a) i j (fW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (fW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hx : ∀ i j (x : Cinf E), sgl (a := a) i j x ∈ S := fun i j x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_atEmb x, map_sum]
    refine S.sum_mem fun w _ => ?_
    rw [map_add (f := _), map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))
  refine eq_top_iff.2 fun L _ => ?_
  have e : L = ∑ i, ∑ j, sgl i j (L i j) := Matrix.matrix_eq_sum_single (Matrix.of L)
  rw [e]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _

theorem conjTranspose_sgl (i j : Fin a) (x : Cinf E) :
    (Matrix.of (sgl i j x))ᴴ = Matrix.of (sgl j i (star x)) :=
  Matrix.conjTranspose_single i j x

theorem skew_famZ (k : InfinitePlace E × Fin a × Fin a × Bool × Bool) (hk : k.2.2.2.2 = true) :
    (Matrix.of (famZ k))ᴴ = -(Matrix.of (famZ k)) := by
  obtain ⟨w, i, j, b, c⟩ := k
  obtain rfl : c = true := hk
  cases b
  · change (Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ =
      -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))
    rw [Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]
  · change (Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ =
      -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))
    have hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w)) := fun i j => by
      rw [map_neg]; rfl
    rw [Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]

theorem Eop_embedding (w : InfinitePlace E) (i j : Fin a) :
    Eop w.embedding i j = (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w)) := rfl

theorem Eop_conjugate (w : InfinitePlace E) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate w.embedding) i j =
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w)) := by
  have h : atEmb w.embedding (-Complex.I) = -fW w := by
    rw [atEmb_eq]; simp [fW]
  rw [Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]
  rfl

theorem sum_famZ [DecidableEq (InfinitePlace E)] :
    ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ,
        lie E a (famZ k) * lie E a (famZ k) -
      ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true,
        lie E a (famZ k) * lie E a (famZ k) =
    ∑ w : InfinitePlace E, (8 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
      Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a),
      ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k -
        ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true, f k =
      ∑ k, if k.2.2.2.2 = true then -f k else f k := fun f => by
    rw [Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.2.2.2.2 = true <;> simp [h]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))
  have c1 : Formalism.REAL.Cas (Eop (a := a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl
  have c2 : Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) :=
    congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)
  rw [c1, c2, ← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w) := map_add _ _ _
  have f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w) := map_sub _ _ _
  have f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w) := map_sub _ _ _
  have f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w) := map_add _ _ _
  simp only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]
  abel

theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  intro E _ _ _ a
  have : DecidableEq (InfinitePlace E) := Classical.decEq _
  refine ⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ,
    Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩
  rw [sum_famZ]
  exact Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _

end GlobalTheory.CompanionTheory.CasFamily
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenterStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_signature_mem_center : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.CasFamily.exists_family | exact GlobalTheory.CompanionTheory.CasFamily.exists_family | (intros; apply GlobalTheory.CompanionTheory.CasFamily.exists_family <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Lim

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
  [Algebra F R']

theorem map_eq_sum (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) x =
      ∑ k, f ((Algebra.TensorProduct.basis R b).repr x k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem repr_map (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) k =
      f ((Algebra.TensorProduct.basis R b).repr x k) := by
  have h : Algebra.TensorProduct.map f (AlgHom.id F E) x =
      ∑ j, f ((Algebra.TensorProduct.basis R b).repr x j) • (Algebra.TensorProduct.basis R' b) j := by
    rw [map_eq_sum f b x]
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  rw [h, Module.Basis.repr_sum_self]

theorem trace_map (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      ∑ k, f ((Algebra.TensorProduct.basis R b).repr x k) * algebraMap F R' (Algebra.trace F E (b k)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have h1 : ∀ e : E, Algebra.trace R' (R' ⊗[F] E) ((1 : R') ⊗ₜ[F] e) = algebraMap F R' (Algebra.trace F E e) := by
    intro e
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_eq_sum f b x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 : ∀ (a : R') (e : E), a ⊗ₜ[F] e = a • ((1 : R') ⊗ₜ[F] e) := by
    intro a e
    simp [TensorProduct.smul_tmul']
  rw [h2, map_smul, h1, smul_eq_mul]

end Tens

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def cf (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E) (x : AF F ⊗[F] E) (k : Fin d) : Fv F v :=
  ((evalV F v).comp (sndA F)) ((Algebra.TensorProduct.basis (AF F) b).repr x k)

theorem hermV_apply (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (y : HermR (AF F) σ n) (i j : Fin n) :
    ((hermV σ v (hermFin σ y) : HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j =
      Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E)
        ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) := by
  have h : Algebra.TensorProduct.map ((evalV F v).comp (sndA F)) (AlgHom.id F E) =
      (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).comp
        (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) := by
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  rw [h]
  rfl

theorem mem_latH_iff (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (y : HermR (AF F) σ n) :
    hermV σ v (hermFin σ y) ∈ latH σ b v n ↔
      (∀ i, algebraMap F (Fv F v) (1 / 2) *
          ∑ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i i) k *
            algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F) ∧
        ∀ i j, i < j → ∀ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k ∈
          v.adicCompletionIntegers F := by
  unfold latH
  simp only [Set.mem_ofPred_eq, hermV_apply, trace_map _ b, repr_map]
  rfl

theorem ev_rat (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  filter_upwards [(algebraMap F (Af F) a).2] with v hv
  have h : evalV F v (algebraMap F (Af F) a) = algebraMap F (Fv F v) a := (evalV F v).commutes a
  rw [← h]
  exact hv

theorem ev_cf {d : ℕ} (b : Module.Basis (Fin d) F E) (x : AF F ⊗[F] E) (k : Fin d) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, cf v b x k ∈ v.adicCompletionIntegers F :=
  (sndA F ((Algebra.TensorProduct.basis (AF F) b).repr x k)).2

theorem ev_latH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ} (y : HermR (AF F) σ n) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, hermV σ v (hermFin σ y) ∈ latH σ b v n := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (i j : Fin n) (k : Fin d),
      cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k => ev_cf b _ k
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k : Fin d,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_rat _
  filter_upwards [h1, h2, ev_rat (1 / 2 : F)] with v h1 h2 h3
  rw [mem_latH_iff]
  refine ⟨fun i => mul_mem h3 (sum_mem fun k _ => mul_mem (h1 i i k) (h2 k)), fun i j _ k => h1 i j k⟩

end Adelic

section Cont

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (i j : Fin n) :
    Continuous fun y : HermR (AF F) σ n => (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j :=
  continuous_subtype_val.matrix_elem i j

theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun x : AF F ⊗[F] E => cf v b x k := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous fun x : AF F ⊗[F] E => (Algebra.TensorProduct.basis (AF F) b).repr x k :=
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (AF F) b).coord k)
  have h2 : Continuous fun a : AF F => sndA F a := continuous_snd
  have h3 : Continuous fun a : Af F => a v := RestrictedProduct.continuous_eval v
  exact h3.comp (h2.comp h1)

theorem measurableSet_latH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} : MeasurableSet {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} := by
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : ∀ (i j : Fin n) (k : Fin d), Continuous fun y : HermR (AF F) σ n =>
      cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k :=
    fun i j k => (continuous_cf v b k).comp (continuous_entry σ i j)
  have hset : {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} =
      (⋂ i : Fin n, (fun y : HermR (AF F) σ n => algebraMap F (Fv F v) (1 / 2) *
          ∑ k, cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i i) k *
            algebraMap F (Fv F v) (Algebra.trace F E (b k))) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v))) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i < j, ⋂ k : Fin d,
        (fun y : HermR (AF F) σ n => cf v b ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j) k) ⁻¹'
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_ofPred_eq, mem_latH_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) (MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun k =>
      (hO.preimage (hc i j k)).measurableSet)
  refine (hO.preimage ?_).measurableSet
  exact continuous_const.mul (continuous_finsetSum _ fun k _ => (hc i i k).mul continuous_const)

theorem measurableSet_intH (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) {n : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S} := by
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S} =
      ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S,
        {y : HermR (AF F) σ n | hermV σ v (hermFin σ y) ∈ latH σ b v n} := by
    ext y
    simp [intH]
  rw [hset]
  exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => measurableSet_latH σ b v

theorem continuous_chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (T : Matrix (Fin n) (Fin n) E) : Continuous (chiT σ ψ T) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hl : ∀ t : AF F ⊗[F] E, Continuous fun x : AF F ⊗[F] E =>
      Algebra.trace (AF F) (AF F ⊗[F] E) (t * x) := fun t =>
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AF F ⊗[F] E)).comp (LinearMap.mulLeft (AF F) t))
  have hs : (fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))) =
      fun y : HermR (AF F) σ n => ∑ a, ∑ c, Algebra.trace (AF F) (AF F ⊗[F] E)
        (T.map (inclR (AF F)) a c * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) c a) := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  have ht : Continuous fun y : HermR (AF F) σ n => Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))) := by
    rw [hs]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
      (hl _).comp (continuous_entry σ c a)
  exact hψ.comp (continuous_const.mul ht).neg

end Cont

theorem coefSN_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E), Filter.Tendsto (fun S => coefSN σ b J ψ dx db Φ T S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ ψ hψ dx db Φ hI d b T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : AEStronglyMeasurable (chiT σ ψ T) db := (continuous_chiT σ ψ hψc T).aestronglyMeasurable
  have hf : AEStronglyMeasurable (fun y => starN σ J ψ dx Φ y * chiT σ ψ T y) db :=
    hI.aestronglyMeasurable.mul hchar
  have hnorm : ∀ y, ‖chiT σ ψ T y‖ = 1 := fun y => hψn _
  have hlim : coefN σ J ψ dx db Φ T = ∫ y, starN σ J ψ dx Φ y * chiT σ ψ T y ∂db := rfl
  rw [hlim]
  unfold coefSN
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖starN σ J ψ dx Φ y‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable (fun y : HermR (AF F) σ n =>
        (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)) := by
      have he : (fun y : HermR (AF F) σ n => (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)) =
          {y : HermR (AF F) σ n | hermFin σ y ∈ intH σ b n S}.indicator (fun _ => (1 : ℂ)) := by
        funext y
        by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [Set.indicator, h]
      rw [he]
      exact measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun y => ?_
    have h1 : ‖(intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y)‖ ≤ 1 := by
      by_cases h : hermFin σ y ∈ intH σ b n S <;> simp [h]
    rw [norm_mul, norm_mul, hnorm, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun y => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ hermV σ v (hermFin σ y) ∈ latH σ b v n}.Finite :=
      Filter.eventually_cofinite.1 (ev_latH σ b y)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : hermFin σ y ∈ intH σ b n S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [hmem]

end GlobalTheory.CompanionTheory.SiegelND.Coef.Lim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentityStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_unfolding_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E), Filter.Tendsto (fun S => coefSN σ b J ψ dx db Φ T S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceInnerMul
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Unip

variable {D : D7} {n : ℕ}

theorem halfTr_add' (a c : AE D) : halfTr (a + c) = halfTr a + halfTr c := by
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, map_add (f := _), mul_add]

theorem halfTr_add_cA (s : AE D) : halfTr s + halfTr (cA D s) = trA s := by
  have hinv : Function.Involutive (cA D) := by
    intro a
    have h := congrArg (fun N => N 0 0)
      (GlobalTheory.MixModel.adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a))
    simpa [GlobalTheory.MixModel.adj] using h
  have hcomm : ∀ r : AF D.host.F, cA D (algebraMap (AF D.host.F) (AE D) r) =
      algebraMap (AF D.host.F) (AE D) r := by
    intro r
    simp [Formalism.L2.Theta.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  let e : AE D ≃ₐ[AF D.host.F] AE D :=
    AlgEquiv.ofBijective { cA D with commutes' := hcomm } hinv.bijective
  have htr : trA (cA D s) = trA s := Algebra.trace_eq_of_algEquiv e s
  simp only [GlobalTheory.StdUnn.halfTr]
  rw [htr, ← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

theorem inner_add_add (V : HSp D) (z x : Mx D V.rank n) :
    GlobalTheory.StdUnn.inner V (z + x) (z + x) = GlobalTheory.StdUnn.inner V z z + GlobalTheory.StdUnn.inner V z x + GlobalTheory.StdUnn.inner V x z +
      GlobalTheory.StdUnn.inner V x x := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem adj_inner (V : HSp D) (z x : Mx D V.rank n) :
    adj (GlobalTheory.StdUnn.inner V z x) = GlobalTheory.StdUnn.inner V x z := by
  simp only [GlobalTheory.StdUnn.inner, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA,
    Matrix.mul_assoc]

theorem trace_inner_mul (V : HSp D) (b : Mx D n n) (z x : Mx D V.rank n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b)) = Matrix.trace (b * GlobalTheory.StdUnn.inner V z x) := by
  rw [Matrix.trace_mul_comm b]
  simp only [GlobalTheory.StdUnn.inner, Matrix.mul_assoc]

theorem trace_swap (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    Matrix.trace (b * GlobalTheory.StdUnn.inner V x z) = cA D (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x)) := by
  rw [← GlobalTheory.MixModel.trace_adj, GlobalTheory.MixModel.adj_mul, GlobalTheory.CompanionTheory.EisCovar.Unip.adj_inner, hb,
    Matrix.trace_mul_comm]

theorem quad_shift (V : HSp D) {b : Mx D n n} (hb : adj b = b) (z x : Mx D V.rank n) :
    halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V (z + x) (z + x))) =
      halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V z z)) + trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (x ⬝ b))) +
        halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V x (x ⬝ b))) := by
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.inner_add_add, GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul,
    GlobalTheory.CompanionTheory.EisCovar.Unip.trace_inner_mul]
  simp only [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add']
  rw [GlobalTheory.CompanionTheory.EisCovar.Unip.trace_swap V hb z x,
    ← GlobalTheory.CompanionTheory.EisCovar.Unip.halfTr_add_cA (Matrix.trace (b * GlobalTheory.StdUnn.inner V z x))]
  abel

theorem mat_inv_unip {g : G D n} {b : Mx D n n} (hg : mat g = blk4 1 b 0 1) : mat g⁻¹ = blk4 1 (-b) 0 1 := by
  have h1 : GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1 = 1 := by
    rw [hg, GlobalTheory.CompanionTheory.EisCovar.submatrix_fromBlocks_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      neg_add_cancel, GlobalTheory.CompanionTheory.EisCovar.block_matrix_one]
  calc GlobalTheory.StdUnn.mat g⁻¹ = GlobalTheory.StdUnn.mat g⁻¹ * (GlobalTheory.StdUnn.mat g * GlobalTheory.StdUnn.blk4 1 (-b) 0 1) := by
        rw [h1, Matrix.mul_one]
    _ = GlobalTheory.StdUnn.blk4 1 (-b) 0 1 := by
        rw [← Matrix.mul_assoc, GlobalTheory.CompanionTheory.EisCovar.mat_inv_mul', Matrix.one_mul]

end GlobalTheory.CompanionTheory.EisCovar.Unip

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covAt_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g b hb hg
  unfold GlobalTheory.CompanionTheory.EisCovar.CovAt
  intro v Φ Ψ hΨ
  have hinv := GlobalTheory.CompanionTheory.EisCovar.Unip.mat_inv_unip hg
  funext z
  rw [hinv, hW.unip g b hg Ψ z, hΨ]
  simp only [PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂]
  rw [GlobalTheory.CompanionTheory.EisCovar.x_part_mul_block, GlobalTheory.CompanionTheory.EisCovar.y_part_mul_block]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.mul_neg]
  rw [hW.unip g b hg Φ, GlobalTheory.CompanionTheory.EisCovar.Unip.quad_shift V hb z (xPart v)]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [GlobalTheory.StdUnn.halfTr, GlobalTheory.StdUnn.trA, GlobalTheory.StdUnn.inner, Matrix.mul_add, Matrix.mul_neg,
    Matrix.trace_add, Matrix.trace_neg, map_add, map_neg]
  ring

end GlobalTheory.CompanionTheory.EisCovar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandard
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxFN A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxFN A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxFN A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ M n d b I c minf m hE
  obtain ⟨-, -, S₀, hS₀⟩ := hE
  refine ⟨S₀, fun S hS φ hφ hφi A hA hfin hoff => ?_⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hB := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurableSet_box b n M S A hA hoff
  have hp := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurable_projInf (E := E) b n M
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) :=
    {X | ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} with hBdef
  set P : ℝ := ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal with hP
  have hP0 : 0 ≤ P := tprod_nonneg fun _ => ENNReal.toReal_nonneg
  set K : ℝ≥0∞ := (c : ℝ≥0∞) * (∏ v ∈ S, m v (A v)) * ENNReal.ofReal P with hK
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.prod_ne_top fun v _ => hfin v)) ENNReal.ofReal_ne_top
  have hmap : (I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf = K • minf := by
    ext T hT
    rw [Measure.map_apply hp hT, Measure.restrict_apply (hp hT), Measure.smul_apply, smul_eq_mul]
    have hform := hS₀ S hS (T.indicator 1) (fun v => (A v).indicator 1)
      (measurable_one.indicator hT) (fun v => measurable_one.indicator (hA v))
    simp_rw [GlobalTheory.CompanionTheory.SW.EulerBox.pureL_indicator_eq b S _ A hoff] at hform
    rw [lintegral_indicator hB, lintegral_indicator_one hT] at hform
    have hl : ∫⁻ X in B, T.indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) ∂I =
        I (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T ∩ B) := by
      have : (fun X => T.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) =
          (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T).indicator 1 := by
        funext X
        by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projInf X ∈ T
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show X ∈ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
          rfl
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show X ∉ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
      rw [this, lintegral_indicator_one (hp hT), Measure.restrict_apply (hp hT)]
    rw [hl] at hform
    change _ = _ * _ * ENNReal.ofReal P at hform
    rw [hform]
    simp_rw [lintegral_indicator_one (hA _)]
    rw [hK]; ring
  have hfun : pureN φ A = B.indicator (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) :=
    funext fun X => pureN_eq_indicator φ A X
  refine ⟨?_, ?_⟩
  · have h1 : Integrable φ ((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [hmap]; exact hφi.smul_measure hKtop
    have h2 := (integrable_map_measure hφ.aestronglyMeasurable hp.aemeasurable).1 h1
    rw [hfun]
    exact IntegrableOn.integrable_indicator h2 hB
  · have h1 : ∫ X, pureN φ A X ∂I = ∫ Y, φ Y ∂((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [integral_map hp.aemeasurable hφ.aestronglyMeasurable, hfun]
      exact integral_indicator hB
    rw [h1, hmap, integral_smul_measure]
    have hKr : K.toReal = (c : ℝ) * (∏ v ∈ S, (m v (A v)).toReal) * P := by
      rw [hK, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hP0]
      simp
    rw [hKr, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SiegelND.Coef.Euler
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandardStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_eventually_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Euler.integrable_integral_pureN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalised
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalised
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem fubini_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ ψ hψ dx hdx db hdb Φ hΦ τ hτ hinv T hT
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, hTr, -, hB, hCl, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  have := hB n M
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : LocallyCompactSpace (HermR (AF F) σ n) := (hCl n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (HermR (AF F) σ n) :=
    (hCl n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have := hdx.1
  have := hdb.1
  have : SFinite dx := inferInstance
  have : SFinite db := inferInstance
  set Th := fouH σ ψ db τ with hTh
  set S : HermR (AF F) σ n := hermOf (AF F) σ T hT with hS
  obtain ⟨hψc, hψn, -⟩ := hψ

  have hstar : ∀ (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E),
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J x)) =
      pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x) := by
    intro y x
    simp only [pairHerm, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rfl
  have hchi : ∀ y : HermR (AF F) σ n, chiT σ ψ T y = ψ (-pairHerm (AF F) σ n y S) := by
    intro y
    have e : Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) =
        ∑ a, ∑ b, (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a := by
      rw [Matrix.trace_mul_comm]
      rfl
    rw [chiT, e]
    rfl
  have hsub : ∀ y z w : HermR (AF F) σ n,
      pairHerm (AF F) σ n y z + -pairHerm (AF F) σ n y w = pairHerm (AF F) σ n y (z - w) := by
    intro y z w
    simp only [pairHerm, AddSubgroup.coe_sub, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, map_sub]
    ring
  have hpc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S) := by
    have hg : Continuous (gramR (AF F) σ J : (Fin n → Fin M → AF F ⊗[F] E) → _) := hG n M J
    show Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
      algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ a, ∑ b, (z.1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b *
          (gramR (AF F) σ J z.2 b a - (S : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) b a))
    refine continuous_const.mul (hTr.comp (continuous_finsetSum _ fun a _ =>
      continuous_finsetSum _ fun b _ => ?_))
    exact ((continuous_subtype_val.comp continuous_fst).matrix_elem a b).mul
      (((hg.comp continuous_snd).matrix_elem b a).sub continuous_const)
  have hint : Integrable (Function.uncurry fun (y : HermR (AF F) σ n) (x : Fin n → Fin M → AF F ⊗[F] E) =>
      Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S)))) (db.prod dx) := by
    have h0 : Integrable (fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) => Th z.1 * Φ z.2)
        (db.prod dx) := hτ.mul_prod hΦ
    have hc : Continuous fun z : HermR (AF F) σ n × (Fin n → Fin M → AF F ⊗[F] E) =>
        ψ (pairHerm (AF F) σ n z.1 (gramH hCM hJ (AF F) z.2 - S)) := hψc.comp hpc
    refine h0.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have := h0.aestronglyMeasurable.mul hc.aestronglyMeasurable
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry, Pi.mul_apply, mul_assoc]
    · simp only [Function.uncurry, norm_mul, hψn, mul_one, le_refl]
  have hL : ∀ y, Th y * (starN σ J ψ dx Φ y * chiT σ ψ T y) =
      ∫ x, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂dx := by
    intro y
    rw [integral_const_mul, starN, ← integral_mul_const, hchi]
    congr 2
    funext x
    rw [hstar, mul_assoc, ← AddChar.map_add_eq_mul, hsub]
  have hR : ∀ x, ∫ y, Th y * (Φ x * ψ (pairHerm (AF F) σ n y (gramH hCM hJ (AF F) x - S))) ∂db =
      Φ x * τ (S - gramH hCM hJ (AF F) x) := by
    intro x
    have := hinv (gramH hCM hJ (AF F) x - S)
    rw [neg_sub] at this
    rw [← this, ← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [hL]
  rw [integral_integral_swap hint]
  simp_rw [hR]

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilIntegralNormalisedStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_integral_normalised : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN <;> assumption)
end
end
