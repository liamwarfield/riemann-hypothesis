module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarExistence
open MeasureTheory Matrix

namespace CompanionTheory.RgExh.Dec.L

def HaarExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ),
    IsGrad ε A → ∃ ν : Measure (PSub ε A), ν.IsHaarMeasure

end CompanionTheory.RgExh.Dec.L

namespace GlobalTheory.CompanionTheory.ParabolicHaar

open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem keeps_iff_forall_mem (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) (S : Submodule ℂ (Fin n → ℂ)) :
    Keeps (g : Matrix (Fin n) (Fin n) ℂ) S ↔
      ∀ v ∈ S, (g : Matrix (Fin n) (Fin n) ℂ) *ᵥ v ∈ S := by
  unfold Keeps
  constructor
  · intro h v hv
    have hm : Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ) v ∈
        Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S := Submodule.mem_map_of_mem hv
    rw [h] at hm
    simpa [Matrix.toLin'_apply] using hm
  · intro h
    have hle : Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S ≤ S := by
      rintro _ ⟨v, hv, rfl⟩
      rw [Matrix.toLin'_apply]
      exact h v hv
    let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
      LinearEquiv.ofLinear (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ))
        (Matrix.toLin' ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
        (by rw [← Matrix.toLin'_mul, Units.mul_inv, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, Units.inv_mul, Matrix.toLin'_one])
    have hfr : Module.finrank ℂ (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) ℂ)) S) =
        Module.finrank ℂ S := LinearEquiv.finrank_map_eq e S
    exact Submodule.eq_of_le_of_finrank_eq hle hfr

theorem isClosed_keeps (ε : Fin n → Bool) (S : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {g : S7.UJ ε | Keeps (S7.toM g) S} := by
  have hset : {g : S7.UJ ε | Keeps (S7.toM g) S} =
      ⋂ v ∈ S, {g : S7.UJ ε | S7.toM g *ᵥ v ∈ S} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact keeps_iff_forall_mem (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) S
  rw [hset]
  refine isClosed_biInter fun v _ => ?_
  have hS : IsClosed (S : Set (Fin n → ℂ)) := S.closed_of_finiteDimensional
  have hc : Continuous fun g : S7.UJ ε => S7.toM g *ᵥ v :=
    (S7.continuous_toM ε).matrix_mulVec continuous_const
  exact IsClosed.preimage hc hS

theorem isClosed_pSub (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    IsClosed (PSub ε A : Set (S7.UJ ε)) := by
  exact (isClosed_keeps ε (Vm A)).inter (isClosed_keeps ε (Wm A))

instance (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) : LocallyCompactSpace (PSub ε A) :=
  (isClosed_pSub ε A).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem haar_pSub_isHaar (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Measure.haar : Measure (PSub ε A)).IsHaarMeasure := by
  infer_instance

theorem haarExists (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (_ : IsGrad ε A) : ∃ ν : Measure (PSub ε A), ν.IsHaarMeasure := by
  exact ⟨Measure.haar, haar_pSub_isHaar ε A⟩

end GlobalTheory.CompanionTheory.ParabolicHaar

theorem GlobalTheory.T.HaarExistence : CompanionTheory.RgExh.Dec.L.HaarExists :=
  GlobalTheory.CompanionTheory.ParabolicHaar.haarExists
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.FarReg.BdProd

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cre_sq (k : Pos n) : (cre k * cre k : Module.End ℂ (Cn n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply, CompanionTheory.D.LK.Car.cre_apply]
  by_cases h : k ∈ A <;> simp [h]

theorem cre_anti (i j : Pos n) : (cre i * cre j : Module.End ℂ (Cn n V)) = -(cre j * cre i) :=
  eq_neg_of_add_eq_zero_left (CompanionTheory.D.LK.Car.cre_cre i j)

theorem cre_mul_prod_of_mem {k : Pos n} {l : List (Pos n)} (h : k ∈ l) :
    (cre k * (l.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
  induction l with
  | nil => simp at h
  | cons g t ih =>
    rw [List.map_cons, List.prod_cons]
    by_cases hk : k = g
    · subst hk
      rw [← mul_assoc, cre_sq, zero_mul]
    · have h1 := ih ((List.mem_cons.1 h).resolve_left hk)
      rw [← mul_assoc, cre_anti, neg_mul, mul_assoc, h1, mul_zero, neg_zero]

theorem term_comm (k i g : Pos n) :
    (cre k * ann i * cre g - cre g * (cre k * ann i) : Module.End ℂ (Cn n V)) = if i = g then cre k else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) i g
  rw [mul_assoc, eq_sub_of_add_eq h1, mul_sub, ← mul_assoc (cre k) (cre g), cre_anti k g, neg_mul, mul_assoc (cre g),
    sub_neg_eq_add, add_sub_cancel_right]
  split_ifs <;> simp

theorem adL_cre (p q : Fin n) (g : Pos n) :
    (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) = ∑ k : Pos n, adC p q g k • cre k := by
  have h : (adL p q * cre g - cre g * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i * cre g - cre g * (cre k * ann i)) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_comm]
  rw [Finset.sum_eq_single g]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem lF_cre (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (g : Pos n) :
    (lF E p q * cre g : Module.End ℂ (Cn n V)) = cre g * lF E p q + ∑ k : Pos n, adC p q g k • cre k := by
  have h1 : (lift n (E p q) * cre g : Module.End ℂ (Cn n V)) = cre g * lift n (E p q) :=
    LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre (E p q) g x
  rw [← adL_cre, lF, add_mul, mul_add, h1]
  abel

theorem lF_prod (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (l : List (Pos n))
    (h : ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ k : Pos n,
      adC p q f k ≠ 0 → k ∈ post) :
    (lF E p q * (l.map cre).prod : Module.End ℂ (Cn n V)) = (l.map cre).prod * lF E p q := by
  induction l with
  | nil => simp
  | cons g t ih =>
    have ht := ih fun pre f post e k hk => h (g :: pre) f post (by rw [e]; rfl) k hk
    have hz : ((∑ k : Pos n, adC p q g k • cre k) * (t.map cre).prod : Module.End ℂ (Cn n V)) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : adC p q g k = 0
      · rw [hk, zero_smul, zero_mul]
      · rw [smul_mul_assoc, cre_mul_prod_of_mem (h [] g t rfl k hk), smul_zero]
    rw [List.map_cons, List.prod_cons, ← mul_assoc, lF_cre, add_mul, hz, add_zero, mul_assoc, ht, mul_assoc]

theorem bd_prod : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  intro n V _ _ E hC l x
  induction l with
  | nil => intro _ _; simp
  | cons f t ih =>
    intro hcl hx
    have ih' := ih (fun pre g post e a ha k hk =>
      hcl (f :: pre) g post (by rw [e]; rfl) a (List.mem_cons_of_mem _ ha) k hk)
      (fun e he => hx e (List.mem_cons_of_mem _ he))
    have hf : lF E f.1.1 f.1.2 (((t.map cre).prod : Module.End ℂ (Cn n V)) x) = 0 := by
      have h1 := lF_prod E f.1.1 f.1.2 t (fun pre g post e k hk =>
        hcl (f :: pre) g post (by rw [e]; rfl) f List.mem_cons_self k hk)
      have h2 := LinearMap.congr_fun h1 x
      simp only [Module.End.mul_apply] at h2
      rw [h2, hx f List.mem_cons_self, map_zero]
    have h3 := LinearMap.congr_fun (hC f) (((t.map cre).prod : Module.End ℂ (Cn n V)) x)
    simp only [LinearMap.add_apply, Module.End.mul_apply, hf, ih'] at h3
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons, pow_succ, map_smul]
    rw [eq_neg_of_add_eq_zero_left h3, mul_neg_one, neg_smul, map_smul]

end GlobalTheory.CompanionTheory.FarReg.BdProd
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLeviStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_creation_commutes_past_levi : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  first | exact @GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | exact GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | (intros; apply GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPair
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPair
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.FarReg

theorem highest_preimage_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    (T : Submodule ℂ E) (a b : ι → Module.End ℂ E) (D : Module.End ℂ E) (y : E)
    (hT : FiniteDimensional ℂ T)
    (hadj : ∀ i x z, ⟪a i x, z⟫_ℂ = ⟪x, b i z⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) :
    ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  classical
  let S : Submodule ℂ E := Submodule.span ℂ {z | ∃ i, ∃ t ∈ T, z = b i t}
  have hST : S ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, t, ht, rfl⟩
    exact hbT i t ht
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hST
  obtain ⟨u, huS, w, hw, hyuw⟩ := S.exists_add_mem_mem_orthogonal y
  have hbS : ∀ i, ∀ t ∈ T, b i t ∈ S := fun i t ht => Submodule.subset_span ⟨i, t, ht, rfl⟩
  have huT : u ∈ T := hST huS
  have hwT : w ∈ T := by
    have : w = y - u := by rw [hyuw]; abel
    rw [this]
    exact T.sub_mem hy huT
  have haw : ∀ i, a i w = 0 := by
    intro i
    have h0 : ⟪a i w, a i w⟫_ℂ = 0 := by
      rw [hadj]
      exact (Submodule.mem_orthogonal' S w).1 hw _ (hbS i _ (haT i w hwT))
    exact inner_self_eq_zero.1 h0
  have har : ∀ i, a i (D u) = 0 := by
    intro i
    have h1 : a i (D y) = a i (D u) + D (a i w) := by
      rw [← haD i w hwT, ← map_add (f := _), ← map_add (f := _), hyuw]
    rw [hDy i, haw i, map_zero, add_zero] at h1
    exact h1.symm
  have hperp : ∀ z ∈ S, ⟪D u, D z⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, t, ht, rfl⟩ := hz
      rw [← hbD i t ht, ← hadj, har i, inner_zero_left]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add (f := _), inner_add_right, hx, hz, add_zero]
    | smul c x _ hx => rw [map_smul, inner_smul_right, hx, mul_zero]
  have hDu : D u = 0 := inner_self_eq_zero.1 (hperp u huS)
  exact ⟨w, hwT, haw, by rw [hyuw, map_add (f := _), hDu, zero_add]⟩

theorem highest_preimage_of_stable : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  intro n V _ _ ι T a b D y hT hadj haT hbT haD hbD hy hDy
  let e : Cn n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Pos n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Pos n) → V)).symm
  let c : Module.End ℂ (Cn n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Pos n) => V)) := fun f =>
    (e : Cn n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cn n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

end GlobalTheory.CompanionTheory.FarReg
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPairStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_invariant_subspace_adjoint_pair : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ι : Type) (T : Submodule ℂ (Cn n V))
    (a b : ι → Module.End ℂ (Cn n V)) (D : Module.End ℂ (Cn n V)) (y : Cn n V), FiniteDimensional ℂ T →
    (∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ) →
    (∀ i, ∀ t ∈ T, a i t ∈ T) → (∀ i, ∀ t ∈ T, b i t ∈ T) →
    (∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) → (∀ i, ∀ t ∈ T, b i (D t) = D (b i t)) →
    y ∈ T → (∀ i, a i (D y) = 0) → ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  first | exact @GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable | exact GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable | (intros; apply GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationList
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationList
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgClusterOrder

def rootHt {n : ℕ} (i : Pos n) : ℕ := (i.1.2 : ℕ) - (i.1.1 : ℕ)

theorem exists_sorted_list {α : Type} (S : Finset α) (h : α → ℕ) :
    ∃ l : List α, l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ S) ∧ l.Pairwise (fun a b => h a ≤ h b) := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image S h hne
      obtain ⟨l, hnd, hmem, hs⟩ := ih (S.erase m) (Finset.erase_ssubset hm)
      refine ⟨m :: l, ?_, ?_, ?_⟩
      · refine List.nodup_cons.2 ⟨?_, hnd⟩
        intro hml
        exact (Finset.mem_erase.1 ((hmem m).1 hml)).1 rfl
      · intro i
        rw [List.mem_cons, hmem, Finset.mem_erase]
        constructor
        · rintro (rfl | hi)
          · exact hm
          · exact hi.2
        · intro hi
          by_cases him : i = m
          · exact Or.inl him
          · exact Or.inr ⟨him, hi⟩
      · refine List.pairwise_cons.2 ⟨?_, hs⟩
        intro b hb
        exact hmin b (Finset.mem_of_mem_erase ((hmem b).1 hb))

theorem adC_ne_zero_cases {n : ℕ} {p q : Fin n} {i k : Pos n} (h : adC p q i k ≠ 0) :
    (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
  by_contra hc
  rw [not_or] at hc
  exact h (by simp only [adC, if_neg hc.1, if_neg hc.2, sub_self])

theorem mem_inside_iff {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} (hlev : Monotone lev) (i : Pos n) :
    i ∈ om ε ∧ i ∉ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 = lev i.1.2 := by
  have hle : lev i.1.1 ≤ lev i.1.2 := hlev (le_of_lt i.2)
  simp only [CompanionTheory.D.LK.om, omU, Finset.mem_filter, Finset.mem_univ, true_and, cpt, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_antisymm hle (not_lt.1 (h2 h1))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => by omega⟩

theorem exists_inside_order : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  intro n ε lev hlev
  classical
  obtain ⟨l, hnd, hmem, hs⟩ := exists_sorted_list ((om ε).filter (· ∉ omU ε lev)) (rootHt (n := n))
  have hmem' : ∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev := fun i => by
    rw [hmem, Finset.mem_filter]
  refine ⟨l, hnd, hmem', ?_⟩
  intro pre f post hl e he k hk
  have hfl : f ∈ l := by simp [hl]
  obtain ⟨he1, he2⟩ := (mem_inside_iff hlev e).1 ((hmem' e).1 he)
  obtain ⟨hf1, hf2⟩ := (mem_inside_iff hlev f).1 ((hmem' f).1 hfl)
  have he0 : (e.1.1 : ℕ) < e.1.2 := e.2
  have hf0 : (f.1.1 : ℕ) < f.1.2 := f.2

  have hkey : (ε k.1.1 = ε k.1.2 ∧ lev k.1.1 = lev k.1.2) ∧ rootHt f < rootHt k := by
    rcases adC_ne_zero_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [← h1] at hf1 hf2 ⊢
        exact he1.trans hf1
      · simp only [← h1] at hf1 hf2 ⊢
        exact he2.trans hf2
      · have : (e.1.2 : ℕ) = f.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
    · rw [h2]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [h1] at hf1 hf2 ⊢
        exact hf1.trans he1
      · simp only [h1] at hf1 hf2 ⊢
        exact hf2.trans he2
      · have : (f.1.2 : ℕ) = e.1.1 := congrArg Fin.val h1
        simp only [rootHt, h2]
        omega
  have hkl : k ∈ l := (hmem' k).2 ((mem_inside_iff hlev k).2 hkey.1)
  rw [hl] at hkl hs
  rcases List.mem_append.1 hkl with hpre | hrest
  · have := (List.pairwise_append.1 hs).2.2 k hpre f (by simp)
    omega
  · rcases List.mem_cons.1 hrest with rfl | hpost
    · exact absurd hkey.2 (lt_irrefl _)
    · exact hpost

end GlobalTheory.CompanionTheory.RgClusterOrder
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationListStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ordered_creation_list : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ), Monotone lev →
    ∃ l : List (Pos n), l.Nodup ∧ (∀ i, i ∈ l ↔ i ∈ om ε ∧ i ∉ omU ε lev) ∧
      ∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post := by
  first | exact @GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | exact GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order | (intros; apply GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutator
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutator
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Cartan

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem anticommutator_triple_product {R : Type*} [Ring R] (K Aj Ai C d₁ d₂ : R) (h₁ : Ai * C + C * Ai = d₁)
    (h₂ : Aj * C + C * Aj = d₂) (h₃ : K * C + C * K = 0) :
    K * Aj * Ai * C + C * (K * Aj * Ai) = K * Aj * d₁ - K * d₂ * Ai := by
  subst h₁ h₂
  have h : C * K = -(K * C) := eq_neg_of_add_eq_zero_right h₃
  have h' : C * (K * Aj * Ai) = -(K * C * Aj * Ai) := by
    rw [← mul_assoc, ← mul_assoc, h]; noncomm_ring
  rw [h']
  noncomm_ring

theorem tri_anti (i j k e : Pos n) :
    (cre k * ann j * ann i * cre e + cre e * (cre k * ann j * ann i) : Module.End ℂ (Cn n V)) =
      (if i = e then cre k * ann j else 0) - (if j = e then cre k * ann i else 0) := by
  rw [anticommutator_triple_product _ _ _ _ _ _ (CompanionTheory.D.LK.Car.ann_cre i e) (CompanionTheory.D.LK.Car.ann_cre j e)
    (CompanionTheory.D.LK.Car.cre_cre k e)]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem cre_mul_lift (φ : Module.End ℂ V) (e : Pos n) :
    (cre e * (lift n φ : Module.End ℂ (Cn n V)) : Module.End ℂ (Cn n V)) = (lift n φ : Module.End ℂ (Cn n V)) * cre e :=
  LinearMap.ext fun x => (CompanionTheory.D.LK.lift_cre φ e x).symm

theorem part_one (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    ((∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0 :
      Module.End ℂ (Cn n V)) = lift n (E e.1.1 e.1.2) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h : ∀ i : Pos n,
      ((if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i then (lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i else 0) :
        Module.End ℂ (Cn n V)) = if i = e then (lift n (E e.1.1 e.1.2) : Module.End ℂ (Cn n V)) else 0 := by
    intro i
    rw [if_pos (rfl : cpt (allT n) i), ← mul_assoc (cre e), cre_mul_lift, mul_assoc, mul_assoc, ← mul_add,
      CompanionTheory.D.LK.Car.ann_cre]
    by_cases hi : i = e
    · subst hi; simp
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

theorem sum_anti {R : Type*} [Ring R] (T P Q : Pos n → Pos n → Pos n → R) (c : R)
    (h : ∀ i j k, T i j k * c + c * T i j k = P i j k - Q i j k) :
    (∑ i, ∑ j, ∑ k, T i j k) * c + c * ∑ i, ∑ j, ∑ k, T i j k =
      ∑ i, ∑ j, ∑ k, P i j k - ∑ i, ∑ j, ∑ k, Q i j k := by
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, h, Finset.sum_sub_distrib]

theorem part_two (e : Pos n) :
    ((∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
      cre e * ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
        if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0 : Module.End ℂ (Cn n V)) = adL e.1.1 e.1.2 := by
  have h : ∀ i j k : Pos n,
      ((if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) * cre e +
        cre e * (if cpt (allT n) i ∧ cpt (allT n) j ∧ i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2 then
          cre k * ann j * ann i else 0) : Module.End ℂ (Cn n V)) =
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0) -
        (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0) := by
    intro i j k
    by_cases ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2
    · rw [if_pos ⟨rfl, rfl, ht⟩, tri_anti]
      obtain ⟨t1, t2, t3⟩ := ht
      congr 1
      · by_cases hi : i = e
        · subst hi
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hi, if_neg fun c => hi c.1]
      · by_cases hj : j = e
        · subst hj
          rw [if_pos rfl, if_pos ⟨rfl, t1, Prod.ext t2 t3⟩]
        · rw [if_neg hj, if_neg fun c => hj c.1]
    · rw [if_neg fun c => ht c.2.2, zero_mul, mul_zero, add_zero, if_neg, if_neg, sub_zero]
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
      · rintro ⟨rfl, c1, c2⟩
        exact ht ⟨c1, by rw [c2], by rw [c2]⟩
  rw [sum_anti _ _ _ _ h]
  have s₁ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if i = e ∧ e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V))) =
      ∑ j : Pos n, ∑ k : Pos n,
        (if e.1.2 = j.1.1 ∧ k.1 = (e.1.1, j.1.2) then cre k * ann j else 0 : Module.End ℂ (Cn n V)) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have s₂ : (∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n,
      (if j = e ∧ i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V))) =
      ∑ i : Pos n, ∑ k : Pos n,
        (if i.1.2 = e.1.1 ∧ k.1 = (i.1.1, e.1.2) then cre k * ann i else 0 : Module.End ℂ (Cn n V)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [s₁, s₂]
  simp only [adL, adC, sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib]

theorem cartan (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n) :
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  have h₁ := part_one E e
  have h₂ := part_two (V := V) e
  unfold bd lF
  rw [add_mul, mul_add, add_add_add_comm, h₁, h₂]

end GlobalTheory.CompanionTheory.Cartan
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutatorStatement
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_creation_anticommutator : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (e : Pos n),
    (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2 := by
  first | exact @GlobalTheory.CompanionTheory.Cartan.cartan | exact GlobalTheory.CompanionTheory.Cartan.cartan | (intros; apply GlobalTheory.CompanionTheory.Cartan.cartan <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NumKG
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ClusterNum

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK
open GlobalTheory.CompanionTheory.DSNormLt (sig sig_anti sig_mul pair_eq abs_sig)
open PI.UpqRep

theorem numKG : NumKG := by
  intro n ε γ lev ν B C hG hB hBn hC _ hdom hn
  set X := xv ε γ with hX
  set κ := X - rhoC ε - wt B with hκ
  set μ := X - wt B - wt C with hμ
  obtain ⟨hXa, -, hgap⟩ := hG
  obtain ⟨w, hw, hs⟩ := exists_sort ε κ
  obtain ⟨m, hm, hm2⟩ := hdom w hw
  have i1 : ∑ a, κ (w a) * μ (w a) ≤ ∑ a, κ (w a) * ν a := by
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have e : ∀ a, κ (w a) * ν a - κ (w a) * μ (w a) = ∑ c, ∑ d, (m c d : ℝ) * (κ (w a) * root c d a) := fun a => by
      have := congrFun hm2 a
      simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [← mul_sub, this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun d _ => ?_
    rw [← Finset.mul_sum]
    by_cases h0 : m c d = 0
    · simp [h0]
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      simp only [root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', mem_univ, if_true, sub_nonneg]
      exact hs c d (hm c d h0).1 (hm c d h0).2
  let tC : Fin n → Fin n → ℝ := fun a b => 2 * (ind C a b - ind C b a) - sc ε a b
  have htC : ∀ a b, |tC a b| ≤ if ε a = ε b then 1 else 0 := fun a b => by
    simp only [tC, ind_eq, sc, sig]
    rcases lt_trichotomy a b with h | h | h
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h]
      by_cases h1 : (⟨(a, b), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := hC _ h1
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
    · subst h; simp
    · simp only [dif_pos h, dif_neg h.not_gt, if_pos h, if_neg h.not_gt]
      by_cases h1 : (⟨(b, a), h⟩ : Pos n) ∈ C
      · have : ε a = ε b := (hC _ h1).symm
        simp [h1, this]; norm_num
      · simp only [h1, if_false]; split_ifs <;> simp
  have i2 : ∑ a, κ a * (wt C a - rhoC ε a) ≤ ∑ a, κ (w a) * rhoC ε a := by
    have p1 := pair_eq tC (fun a b => by simp only [tC]; rw [sc_anti ε a b]; ring) κ
    have p2 := pair_eq (sc ε) (sc_anti ε) fun a => κ (w a)
    have e : ∀ a, wt C a - rhoC ε a = (∑ b, tC a b) / 2 := fun a => by
      simp only [tC]
      rw [wt_eq, rhoC_eq, Finset.sum_sub_distrib (f := fun b => 2 * (ind C a b - ind C b a)), ← Finset.mul_sum]
      ring
    simp only [e]
    simp only [rhoC_eq]
    have : ∑ a, ∑ b, tC a b * (κ a - κ b) ≤ ∑ a, ∑ b, sc ε a b * (κ (w a) - κ (w b)) := by
      calc _ ≤ ∑ a, ∑ b, (if ε a = ε b then 1 else 0) * |κ a - κ b| :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (le_abs_self _).trans (by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (htC a b) (abs_nonneg _))
        _ = ∑ a, ∑ b, (if ε (w a) = ε (w b) then 1 else 0) * |κ (w a) - κ (w b)| := by
            rw [← Equiv.sum_comp w]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Equiv.sum_comp w]
        _ = _ := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hw, hw, sc, sig]
            by_cases h : ε a = ε b
            · rcases lt_trichotomy a b with h1 | h1 | h1
              · simp [h, h1, abs_of_nonneg (sub_nonneg.2 (hs a b h1 h))]
              · simp [h1]
              · simp [h, h1, h1.not_gt, abs_of_nonpos (sub_nonpos.2 (hs b a h1 h.symm))]
            · simp [h]
    linarith
  have hκw : ∀ a, κ (w a) = ν a + rhoC ε a := by
    have e1 : ∑ a, κ a * κ a = ∑ a, κ (w a) * μ (w a) + ∑ a, κ a * (wt C a - rhoC ε a) := by
      rw [Equiv.sum_comp w fun a => κ a * μ a, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hκ, hμ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : ∑ a, κ (w a) * κ (w a) = ∑ a, κ a * κ a := Equiv.sum_comp w fun a => κ a * κ a
    have e3 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = ∑ a, κ (w a) * κ (w a) - 2 * ∑ a, κ (w a) * ν a -
        2 * ∑ a, κ (w a) * rhoC ε a + ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hn' : ∑ a, (ν a + rhoC ε a) * (ν a + rhoC ε a) = ∑ a, κ a * κ a := hn
    have h0 : ∑ a, (κ (w a) - (ν a + rhoC ε a)) ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro a
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h0 a (mem_univ _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  let t : Fin n → Fin n → ℝ := fun a b =>
    (sig a b - sc ε a b) - 2 * (ind B a b - ind B b a) + sc ε (w.symm a) (w.symm b)
  have hws : ∀ c, ε (w.symm c) = ε c := fun c => by rw [← hw, Equiv.apply_symm_apply]
  have ta : ∀ a b, t b a = -t a b := fun a b => by
    simp only [t]; rw [sig_anti a b, sc_anti ε a b, sc_anti ε (w.symm a)]; ring
  have tb : ∀ a b, a < b → |t a b| ≤ 1 := fun a b h => by
    simp only [t, ind_eq, dif_pos h, dif_neg h.not_gt, sc, hws]
    by_cases h1 : ε a = ε b
    · rw [if_neg fun h2 => (hBn _ h2).1 h1]
      simpa [h1] using abs_sig _ _
    · simp only [if_neg h1, sig, if_pos h]
      split_ifs <;> norm_num
  have tb' : ∀ a b, |t a b| ≤ 1 := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact tb a b h
    · subst h
      have := ta a a
      rw [show t a a = 0 by linarith]; simp
    · rw [ta, abs_neg]; exact tb b a h
  obtain ⟨⟨⟨c, d⟩, hcd⟩, hi⟩ := hB
  have hcd' : c < d := hcd
  have hne : t c d = -1 := by
    have h1 : ¬ε c = ε d := (hBn _ hi).1
    simp only [t, ind_eq, dif_pos hcd', dif_neg hcd'.not_gt, sc, hws, if_neg h1, if_pos hi, sig, if_pos hcd']
    norm_num
  have hgcd : Lc n ≤ X c - X d := hgap c d (hBn _ hi).2

  have p1 := pair_eq t ta X
  have p2 := pair_eq sig sig_anti X
  have hD : ∀ a b, 0 ≤ sig a b * (X a - X b) - t a b * (X a - X b) := fun a b => by
    rw [sig_mul hXa, sub_nonneg]
    exact (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (tb' a b))
  have hDcd : 2 * Lc n ≤ sig c d * (X c - X d) - t c d * (X c - X d) := by
    rw [hne, show sig c d = 1 by simp [sig, hcd']]
    linarith
  have hsum : ∑ a, ∑ b, t a b * (X a - X b) + 2 * Lc n ≤ ∑ a, ∑ b, sig a b * (X a - X b) := by
    have h1 : sig c d * (X c - X d) - t c d * (X c - X d) ≤
        ∑ a, ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)) :=
      (Finset.single_le_sum (f := fun b => sig c b * (X c - X b) - t c b * (X c - X b))
        (fun b _ => hD c b) (mem_univ d)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (sig a b * (X a - X b) - t a b * (X a - X b)))
        (fun a _ => Finset.sum_nonneg fun b _ => hD a b) (mem_univ c))
    simp only [Finset.sum_sub_distrib] at h1
    linarith
  have hy : ∀ a, (ν + (2 : ℝ) • rhoC ε) (w.symm a) = X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) := fun a => by
    have h1 := hκw (w.symm a)
    have h3 := rhoC_eq ε a
    have h4 := rhoC_eq ε (w.symm a)
    rw [← Equiv.sum_comp w.symm] at h4
    have h5 := wt_eq B a
    have ts : ∑ b, t a b = ∑ b, sig a b - ∑ b, sc ε a b - 2 * ∑ b, (ind B a b - ind B b a) +
        ∑ b, sc ε (w.symm a) (w.symm b) := by
      simp only [t]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib (f := fun b => sig a b - sc ε a b),
        Finset.sum_sub_distrib (f := fun b => sig a b), ← Finset.mul_sum]
    simp only [hκ, Equiv.apply_symm_apply, Pi.sub_apply] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ts]
    linarith
  have hY : ∀ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 2 := fun a => by
    have e : (∑ b, t a b) / 2 - (∑ b, sig a b) / 2 = (∑ b, (t a b - sig a b)) / 2 := by
      rw [Finset.sum_sub_distrib]; ring
    have h2 : |∑ b, (t a b - sig a b)| ≤ 2 * (n : ℝ) := by
      calc _ ≤ ∑ b, |t a b - sig a b| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _b : Fin n, (2 : ℝ) := Finset.sum_le_sum fun b _ => by
            have := abs_sub (t a b) (sig a b)
            linarith [tb' a b, abs_sig a b]
        _ = 2 * (n : ℝ) := by simp [mul_comm]
    rw [e, div_pow]
    have h3 : (∑ b, (t a b - sig a b)) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  have g1 : vNormSq ε ν = ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 := by
    unfold vNormSq nsq dot
    rw [← Equiv.sum_comp w.symm]
    exact Finset.sum_congr rfl fun a _ => by rw [hy, sq]
  have g2 : vNormSq ε γ = ∑ a, X a ^ 2 := by
    unfold vNormSq nsq dot
    exact Finset.sum_congr rfl fun a _ => (sq _).symm
  have g3 : ∑ a, (X a + ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2)) ^ 2 = ∑ a, X a ^ 2 +
      (2 * ∑ a, X a * ((∑ b, t a b) / 2) - 2 * ∑ a, X a * ((∑ b, sig a b) / 2)) +
      ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have g4 : ∑ a, ((∑ b, t a b) / 2 - (∑ b, sig a b) / 2) ^ 2 ≤ (n : ℝ) ^ 3 := by
    calc _ ≤ ∑ _a : Fin n, (n : ℝ) ^ 2 := Finset.sum_le_sum fun a _ => hY a
      _ = (n : ℝ) ^ 3 := by simp; ring
  have g5 : (n : ℝ) ^ 3 < Lc n := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    unfold Lc
    nlinarith [pow_le_pow_left₀ h0 (by linarith : (n : ℝ) ≤ n + 1) 3, pow_pos (by linarith : (0 : ℝ) < n + 1) 3]
  rw [g1, g2, g3]
  linarith

end GlobalTheory.CompanionTheory.ClusterNum
end
end
