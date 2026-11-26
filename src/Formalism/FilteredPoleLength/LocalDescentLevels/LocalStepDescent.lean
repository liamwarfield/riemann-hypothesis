module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.FilteredPoleLength
public import Formalism.LogFactorialIndices.LogProductFormula
public import Lemmata.MiscLemmasO.Imports
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndexSigned

@[expose] public section

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.LatticeIndexBis
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeIndexBis

theorem idx_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Formalism.LatticeIndexTer.idx O X (P.map ι) (Q.map ι) = Formalism.LatticeIndexTer.idx O Y P Q := by
  have key : ∀ P₁ Q₁ : Submodule O Y,
      Module.length O (↥(P₁.map ι) ⧸ Submodule.comap (P₁.map ι).subtype (Q₁.map ι)) =
        Module.length O (↥P₁ ⧸ Submodule.comap P₁.subtype Q₁) := by
    intro P₁ Q₁
    let e : P₁ ≃ₗ[O] P₁.map ι := Submodule.equivMapOfInjective ι hι P₁
    have hm : (Submodule.comap P₁.subtype Q₁).map (e : P₁ →ₗ[O] P₁.map ι) =
        Submodule.comap (P₁.map ι).subtype (Q₁.map ι) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : Y), hy, rfl⟩
      · intro hz
        obtain ⟨q, hq, hqz⟩ := hz
        obtain ⟨p, hp, hpz⟩ := z.2
        refine ⟨⟨p, hp⟩, ?_, Subtype.ext hpz⟩
        have hpq : q = p := hι (hqz.trans hpz.symm)
        show p ∈ Q₁
        rw [← hpq]
        exact hq
    exact (Submodule.Quotient.equiv _ _ e hm).length_eq.symm
  unfold Formalism.LatticeIndexTer.idx Formalism.LatticeIndexTer.qlen
  rw [key P Q, key Q P]

theorem span_image_span {R S M N : Type} [Ring R] [Ring S] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N] (g : M →+ N) (φ : R → S) (h : ∀ r x, g (r • x) = φ r • g x)
    (s : Set M) :
    Submodule.span S (g '' (Submodule.span R s : Set M)) = Submodule.span S (g '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [h]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

section Core

variable {O K V ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem core [Fintype ι] [DecidableEq ι] (a b : ι → V) (ha : LinearIndependent K a)
    (hb : LinearIndependent K b)
    (hab : Submodule.span K (Set.range a) = Submodule.span K (Set.range b))
    (P : Matrix ι ι K) (hP : ∀ i, a i = ∑ k, P k i • b k) :
    P.det ≠ 0 ∧ ∀ x y : O, x ≠ 0 → y ≠ 0 → algebraMap O K x = P.det * algebraMap O K y →
      Formalism.LatticeIndexTer.idx O V (Submodule.span O (Set.range b)) (Submodule.span O (Set.range a)) =
        ((IsDiscreteValuationRing.addVal O x).toNat : ℤ) -
          ((IsDiscreteValuationRing.addVal O y).toNat : ℤ) := by
  let bX := Basis.span ha
  let bY := Basis.span hb
  let f : Submodule.span K (Set.range a) ≃ₗ[K] Submodule.span K (Set.range b) :=
    LinearEquiv.ofEq _ _ hab
  have hbX : ∀ i, ((bX i : Submodule.span K (Set.range a)) : V) = a i := fun i => by
    simp [bX, Basis.span_apply]
  have hbY : ∀ i, ((bY i : Submodule.span K (Set.range b)) : V) = b i := fun i => by
    simp [bY, Basis.span_apply]
  have hM : LinearMap.toMatrix bX bY (f : _ →ₗ[K] _) = P := by
    ext k i
    rw [LinearMap.toMatrix_apply]
    have : (f : _ →ₗ[K] _) (bX i) = ∑ k, P k i • bY k := by
      apply Subtype.ext
      simp [f, hbX, hbY, hP i]
    rw [this, Basis.repr_sum_self]
  refine ⟨?_, ?_⟩
  · rw [← hM]
    exact (LinearEquiv.isUnit_det f bX bY).ne_zero
  · intro x y hx hy hxy
    have h := Formalism.LatticeIndexTer.idxDet O K _ _ ι bX bY f x y hx hy (by rw [hM]; exact hxy)
    let s : Submodule.span K (Set.range b) →ₗ[O] V :=
      (Submodule.span K (Set.range b)).subtype.restrictScalars O
    have hs : Function.Injective s := Subtype.val_injective
    rw [← idx_map_inj s hs] at h
    rw [← h]
    congr 1
    · rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      ext i
      exact (hbY i).symm
    · rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
      congr 2
      ext i
      exact (hbX i).symm

theorem exists_indep [FiniteDimensional K V] (A : Submodule O V) (hA : A.FG) (U : Submodule K V)
    (hU : Submodule.span K (A : Set V) = U) :
    ∃ a : Fin (finrank K U) → V, LinearIndependent K a ∧ A = Submodule.span O (Set.range a) ∧
      Submodule.span K (Set.range a) = U := by
  classical
  haveI : NoZeroSMulDivisors O V := ⟨fun {o v} h => by
    rw [← algebraMap_smul K o v, smul_eq_zero] at h
    rcases h with h | h
    · left
      exact (IsFractionRing.injective O K) (by rw [h, map_zero])
    · right
      exact h⟩
  haveI : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  haveI : Module.Free O A := Module.free_of_finite_type_torsion_free'
  let bA := Module.Free.chooseBasis O A
  let e : Module.Free.ChooseBasisIndex O A → V := fun i => (bA i : V)
  have hliO : LinearIndependent O e := bA.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hli : LinearIndependent K e := by
    first
    | exact (LinearIndependent.iff_fractionRing O K).1 hliO
    | exact LinearIndependent.iff_fractionRing.1 hliO
  have hAe : A = Submodule.span O (Set.range e) := by
    conv_lhs => rw [← Submodule.map_subtype_top A]
    rw [← bA.span_eq, Submodule.map_span, ← Set.range_comp] <;> rfl
  have hspan : Submodule.span K (Set.range e) = U := by
    calc Submodule.span K (Set.range e)
        = Submodule.span K (Submodule.span O (Set.range e) : Set V) :=
          (Submodule.span_span_of_tower O K _).symm
      _ = Submodule.span K (A : Set V) :=
          congrArg (fun s : Submodule O V => Submodule.span K (s : Set V)) hAe.symm
      _ = U := hU
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = Module.finrank K U := by
    rw [← hspan, finrank_span_eq_card hli]
  let σ := Fintype.equivFinOfCardEq hcard
  have hr : Set.range (e ∘ σ.symm) = Set.range e := by
    first
    | exact EquivLike.range_comp e σ.symm
    | exact Equiv.range_comp e σ.symm
    | rw [Set.range_comp, σ.symm.range_eq_univ, Set.image_univ]
  refine ⟨e ∘ σ.symm, hli.comp _ σ.symm.injective, ?_, ?_⟩
  · rw [hr]
    exact hAe
  · rw [hr]
    exact hspan

end Core

theorem addVal_map {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O)
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ)) (x : O) (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal O' (algebraMap O O' x) = IsDiscreteValuationRing.addVal O x := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def x u hϖ n hu,
    IsDiscreteValuationRing.addVal_def (algebraMap O O' x) (Units.map (algebraMap O O' : O →* O') u) hϖ' n
      (by rw [hu]; simp)]

theorem indep_baseChange {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V]
    [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁] [IsScalarTower K K' V₁]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (a : ι → V) (ha : LinearIndependent K a) :
    LinearIndependent K' (fun i => j (a i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range a) := by
    first
    | exact (linearIndepOn_id_range_iff ha.injective).2 ha
    | exact ha.to_subtype_range
    | exact (linearIndependent_subtype_range ha.injective).2 ha
  let B := Module.Basis.extend hs
  let B' := hj.basis B
  have hB' : LinearIndependent K' (fun i : hs.extend (Set.subset_univ _) => j (i : V)) := by
    have h1 := B'.linearIndependent
    convert h1 using 1
    funext i
    rw [IsBaseChange.basis_apply, Module.Basis.coe_extend]
  have hsub : ∀ i, a i ∈ hs.extend (Set.subset_univ _) :=
    fun i => hs.subset_extend _ ⟨i, rfl⟩
  exact hB'.comp (fun i => ⟨a i, hsub i⟩) (fun i i' h => ha.injective (congrArg Subtype.val h))

end LatticeIndexBis

theorem index_baseChange_lattice : RelIndexSpanImage := by
  intro O O' K K' V V₁
  intros
  rename_i j hj ϖ hϖ hϖ' A B hA hB hAB
  classical
  obtain ⟨a, ha, hAa, haU⟩ := LatticeIndexBis.exists_indep A hA (Submodule.span K (A : Set V)) rfl
  obtain ⟨b, hb, hBb, hbU⟩ := LatticeIndexBis.exists_indep B hB (Submodule.span K (A : Set V)) hAB.symm
  have hmem : ∀ i, b i ∈ Submodule.span K (Set.range a) := by
    intro i
    rw [haU, ← hbU]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hc0 : ∀ i, ∃ c : Fin (Module.finrank K (Submodule.span K (A : Set V))) → K,
      ∑ k, c k • a k = b i := by
    intro i
    first
    | exact (Submodule.mem_span_range_iff_exists_fun K).1 (hmem i)
    | exact Submodule.mem_span_range_iff_exists_fun.1 (hmem i)
  choose c hc using hc0
  let P : Matrix (Fin (Module.finrank K (Submodule.span K (A : Set V))))
      (Fin (Module.finrank K (Submodule.span K (A : Set V)))) K := fun k i => c i k
  obtain ⟨hdet, hcore⟩ := LatticeIndexBis.core (O := O) b a hb ha (hbU.trans haU.symm) P (fun i => (hc i).symm)
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) P.det
  dsimp only at hxy
  have hy0 : (y : O) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have hyK : algebraMap O K (y : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxy
    exact (mul_ne_zero hdet hyK) hxy
  have hjK : ∀ (r : K) (z : V), j (r • z) = algebraMap K K' r • j z := by
    intro r z
    rw [map_smul, algebraMap_smul]
  have hjO : ∀ (o : O) (z : V), j (o • z) = algebraMap O O' o • j z := by
    intro o z
    rw [← algebraMap_smul K o z, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j z),
      ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', algebraMap_smul]
  have hspanK : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span K (Set.range f) = Submodule.span K (A : Set V) →
      Submodule.span K' (Set.range fun i => j (f i)) =
        Submodule.span K' (j '' (Submodule.span K (A : Set V) : Set V)) := by
    intro f hf
    have h1 := LatticeIndexBis.span_image_span (R := K) (S := K') j.toAddMonoidHom (algebraMap K K')
      (fun r z => hjK r z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    calc Submodule.span K' (Set.range fun i => j (f i)) = Submodule.span K' (j '' Set.range f) := by
          rw [← Set.range_comp] <;> rfl
      _ = Submodule.span K' (j '' (Submodule.span K (Set.range f) : Set V)) := h1.symm
      _ = _ := congrArg (fun s : Submodule K V => Submodule.span K' (j '' (s : Set V))) hf
  have hspanO : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span O' (j '' (Submodule.span O (Set.range f) : Set V)) =
        Submodule.span O' (Set.range fun i => j (f i)) := by
    intro f
    have h1 := LatticeIndexBis.span_image_span (R := O) (S := O') j.toAddMonoidHom (algebraMap O O')
      (fun o z => hjO o z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1, ← Set.range_comp]
    all_goals rfl
  have hP' : ∀ i, j (b i) = ∑ k, (P.map (algebraMap K K')) k i • j (a k) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Matrix.map_apply, algebraMap_smul]
    all_goals rfl
  have hdetmap : (P.map (algebraMap K K')).det = algebraMap K K' P.det := by
    rw [RingHom.map_det]
    rfl
  have hne : ∀ z : O, z ≠ 0 → algebraMap O O' z ≠ 0 := by
    intro z hz h0
    have hzK : algebraMap O K z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hz)
    apply (map_ne_zero (algebraMap K K')).2 hzK
    rw [← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', h0, map_zero]
  have hx'y' : algebraMap O' K' (algebraMap O O' x) =
      (P.map (algebraMap K K')).det * algebraMap O' K' (algebraMap O O' (y : O)) := by
    rw [← IsScalarTower.algebraMap_apply O O' K', ← IsScalarTower.algebraMap_apply O O' K',
      IsScalarTower.algebraMap_apply O K K' x, IsScalarTower.algebraMap_apply O K K' (y : O), hdetmap,
      ← map_mul, hxy]
  have hab' : Submodule.span K' (Set.range fun i => j (b i)) =
      Submodule.span K' (Set.range fun i => j (a i)) :=
    (hspanK b hbU).trans (hspanK a haU).symm
  obtain ⟨-, hcore'⟩ := LatticeIndexBis.core (O := O') (K := K') (V := V₁) (fun i => j (b i)) (fun i => j (a i))
    (LatticeIndexBis.indep_baseChange j hj b hb) (LatticeIndexBis.indep_baseChange j hj a ha) hab'
    (P.map (algebraMap K K')) hP'
  rw [hAa, hBb, hspanO a, hspanO b,
    hcore' (algebraMap O O' x) (algebraMap O O' (y : O)) (hne x hx0) (hne _ hy0) hx'y',
    hcore x (y : O) hx0 hy0 hxy.symm, LatticeIndexBis.addVal_map ϖ hϖ hϖ' x hx0,
    LatticeIndexBis.addVal_map ϖ hϖ hϖ' (y : O) hy0]

end Formalism.LatticeBaseChangeAlt
end
end

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.LatticeDescent
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeDescentAlt

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem span_inf_eq (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro v hv
    obtain ⟨d, hd, hdv⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (K := K) M hM.2 v
    have hd' : (algebraMap O K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • v ∈ (M ⊓ V'.restrictScalars O : Submodule O V) := by
      refine ⟨hdv, ?_⟩
      show d • v ∈ V'
      rw [← algebraMap_smul K d v]
      exact V'.smul_mem _ hv
    have hsp := Submodule.subset_span (R := K) hmem
    have : v = (algebraMap O K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsp

theorem fg_inf (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM.1
  have h := IsNoetherian.noetherian (N.comap M.subtype)
  have := h.map M.subtype
  rwa [Submodule.map_comap_subtype] at this

end LatticeDescentAlt

theorem localStepDescent_of (h2 : FinrankSpanImage) (h3 : SpanImageInf) (h4 : RelIndexSpanImage) :
    LocalStepDescent := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ' M Θ V'
    hM hΘ d Y Z e h
  rw [h3 O O' K K' V V₁ j hj M V' hM, h3 O O' K K' V V₁ j hj Θ V' hΘ,
    h2 O O' K K' V V₁ j hj V',
    h4 O O' K K' V V₁ j hj ϖ hϖ hϖ' _ _ (LatticeDescentAlt.fg_inf M hM _) (LatticeDescentAlt.fg_inf Θ hΘ _)
      (by rw [LatticeDescentAlt.span_inf_eq M hM V', LatticeDescentAlt.span_inf_eq Θ hΘ V'])] at h
  exact h

end Formalism.LatticeBaseChangeAlt
end
end

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSmulMemOfMemSpan
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem exists_smul_mem_of_mem_span_alt (O K V : Type) [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : O, c ≠ 0 ∧ c • v ∈ M := by
  first | exact Bl.SecondBlockLemmaP.goal1 .. | (apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v hv | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V | exact @Bl.SecondBlockLemmaP.goal1 O K | exact @Bl.SecondBlockLemmaP.goal1 O

theorem exists_adapted_basis_alt (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.latBasis O K V M hM
  have hli0 : LinearIndependent O b0 :=
    (LinearIndependent.iff_fractionRing O K).mpr b0.linearIndependent
  let bO : Basis (Fin (finrank K V)) O M :=
    (Basis.span hli0).map (LinearEquiv.ofEq _ _ hb0.symm)
  obtain ⟨n, bM, bN, f, a, snf⟩ :=
    Submodule.smithNormalForm bO ((V'.restrictScalars O).comap M.subtype)
  have hliO : LinearIndependent O (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K (fun i => (bM i : V)) :=
    (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : M ≤ Submodule.span O (Set.range (fun i => (bM i : V))) := by
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ Submodule.span O (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hspanK : ⊤ ≤ Submodule.span K (Set.range (fun i => (bM i : V))) := by
    rw [← hM.2]
    apply Submodule.span_le.mpr
    intro m hm
    exact Submodule.span_le_restrictScalars O K _ (hspanO hm)
  let b : Basis (Fin (finrank K V)) K V := Basis.mk hliK hspanK
  have hb : ∀ i, b i = (bM i : V) := fun i => by simp [b]
  have hrange : Set.range b = Set.range (fun i => (bM i : V)) := by
    ext x; simp [hb]
  refine ⟨b, Set.range f, ?_, ?_, ?_⟩
  · rw [hrange]; exact hspanO
  · rintro _ ⟨k, rfl⟩
    rw [hb]
    refine ⟨(bM (f k)).2, ?_⟩
    have hmem : ((bN k : M) : V) ∈ V' := (bN k).2
    rw [snf k] at hmem
    have ha : a k ≠ 0 := by
      intro h0
      have : (bN k : M) = 0 := by rw [snf k, h0, zero_smul]
      exact bN.ne_zero k (Subtype.ext this)
    have haK : algebraMap O K (a k) ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne ha
    have h3 : algebraMap O K (a k) • ((bM (f k) : M) : V) ∈ V' := by
      rw [algebraMap_smul]; simpa using hmem
    exact (V'.smul_mem_iff haK).mp h3
  · intro v hv
    have hv' : v ∈ Submodule.span K (M : Set V) := by rw [hM.2]; trivial
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem_of_mem_span_alt O K V M v hv'
    have hcK : algebraMap O K c ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne hc
    have hcV : c • v ∈ V' := by
      rw [← algebraMap_smul K c]; exact V'.smul_mem _ hv
    let w : ((V'.restrictScalars O).comap M.subtype : Submodule O M) := ⟨⟨c • v, hcv⟩, hcV⟩
    have hw : w ∈ Submodule.span O (Set.range bN) := by rw [bN.span_eq]; trivial
    have key : ∀ u ∈ Submodule.span O (Set.range bN),
        ((u : M) : V) ∈ Submodule.span K (b '' Set.range f) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [snf k]
        have : ((a k • bM (f k) : M) : V) = algebraMap O K (a k) • b (f k) := by
          rw [hb, algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, ⟨k, rfl⟩, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (((r • x : _) : M) : V) = algebraMap O K r • ((x : M) : V) := by
          rw [algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    have h4 : algebraMap O K c • v ∈ Submodule.span K (b '' Set.range f) := by
      rw [algebraMap_smul]; exact key w hw
    exact (Submodule.smul_mem_iff _ hcK).mp h4

theorem inter_baseChange_lattice : SpanImageInf := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M V' hM
  obtain ⟨b, s, hMb, hs, hV'⟩ := exists_adapted_basis_alt O K V M V' hM
  let b' : Basis (Fin (finrank K V)) K' V₁ := hj.basis b
  have hb' : ∀ i, b' i = j (b i) := fun i => hj.basis_apply b i
  have hjO : ∀ (o : O) (v : V), j (o • v) = algebraMap O O' o • j v := by
    intro o v
    rw [← algebraMap_smul K o v, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j v),
      ← algebraMap_smul K' (algebraMap O O' o) (j v), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hjK : ∀ (k : K) (v : V), j (k • v) = algebraMap K K' k • j v := by
    intro k v
    rw [map_smul, algebraMap_smul]
  have hO : ∀ y ∈ Submodule.span O (Set.range b), j y ∈ Submodule.span O' (Set.range b') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjO]; exact Submodule.smul_mem _ _ hy
  have hK : ∀ y ∈ Submodule.span K (b '' s), j y ∈ Submodule.span K' (b' '' s) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hi, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjK]; exact Submodule.smul_mem _ _ hy
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ Submodule.span O' (Set.range b') := by
      refine (Submodule.span_le.mpr ?_) hx1
      rintro _ ⟨m, hm, rfl⟩
      exact hO m (hMb hm)
    have h2 : x ∈ Submodule.span K' (b' '' s) := by
      refine (Submodule.span_le.mpr ?_) hx2
      rintro _ ⟨m, hm, rfl⟩
      exact hK m (hV' hm)
    rw [b'.mem_span_iff_repr_mem O'] at h1
    rw [b'.mem_span_image] at h2
    rw [← b'.sum_repr x]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h1 i
      rw [← hc, algebraMap_smul, hb']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hs i hi, rfl⟩)
    · have : b'.repr x i = 0 := by
        by_contra h0
        exact hi (h2 (by simpa using h0))
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨m, hm1, rfl⟩, Submodule.subset_span ⟨m, hm2, rfl⟩⟩

end Formalism.LatticeBaseChangeAlt
end
end

section -- merged from Formalism.FilteredPoleLength.LocalDescentLevels.LinearIndependentOfIsBaseChange
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem linearIndependent_of_isBaseChange_alt {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (v : ι → V)
    (hv : LinearIndependent K v) : LinearIndependent K' (fun i => j (v i)) := by
  classical
  have hs : LinearIndepOn K id (Set.range v) := by
    first
    | exact hv.linearIndepOn_id_range
    | exact (linearIndepOn_id_range_iff hv.injective).mpr hv
  let B := Basis.extend hs
  have hsub : Set.range v ⊆ hs.extend (Set.subset_univ _) := hs.subset_extend (Set.subset_univ _)
  let g : ι → hs.extend (Set.subset_univ _) := fun i => ⟨v i, hsub (Set.mem_range_self i)⟩
  have hg : Function.Injective g := fun a c h => hv.injective (congrArg Subtype.val h)
  have hB' : (fun i => j (v i)) = (hj.basis B) ∘ g := by
    funext i
    first
    | simp [B, g, IsBaseChange.basis_apply, Basis.coe_extend]
    | simp [B, g, Basis.coe_extend]
  rw [hB']
  exact (hj.basis B).linearIndependent.comp g hg

theorem span_image_span_alt {K K' V V₁ : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (s : Set V) :
    Submodule.span K' (j '' (Submodule.span K s : Set V)) = Submodule.span K' (j '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : j x ∈ Submodule.span K (j '' s) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hx
    exact Submodule.span_le_restrictScalars K K' _ h1
  · first
    | exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    | exact Submodule.span_mono (Set.image_subset _ Submodule.subset_span)

theorem finrank_span_image_alt : FinrankSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj V'
  let b := Module.finBasis K V'
  let w : Fin (finrank K V') → V := V'.subtype ∘ b
  have hw : LinearIndependent K w := b.linearIndependent.map' V'.subtype V'.ker_subtype
  have hspan : Submodule.span K (Set.range w) = V' := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have h1 : Submodule.span K' (j '' (V' : Set V)) =
      Submodule.span K' (Set.range (fun i => j (w i))) := by
    have h2 := span_image_span_alt (K' := K') j (Set.range w)
    rw [hspan] at h2
    rw [h2, ← Set.range_comp]
    rfl
  rw [h1, finrank_span_eq_card (linearIndependent_of_isBaseChange_alt j hj w hw), Fintype.card_fin]

theorem isLattice_span_image_alt : IsLatticeSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M hM
  classical
  unfold Formalism.LatticeIndexTer.IsLat at hM ⊢
  have hsm : ∀ (o : O) (x : V), j (o • x) = (algebraMap O O' o) • j x := by
    intro o x
    rw [← algebraMap_smul K o x, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j x),
      ← algebraMap_smul K' (algebraMap O O' o) (j x), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨⟨S, hS⟩, hM2⟩ := hM
  let P : Submodule O' V₁ := Submodule.span O' (j '' (S : Set V))
  let Q : Submodule O V :=
    { carrier := {x | j x ∈ P}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ P
        rw [map_add (f := _)]
        exact P.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ P
        rw [map_zero]
        exact P.zero_mem
      smul_mem' := fun c x hx => by
        show j (c • x) ∈ P
        rw [hsm]
        exact P.smul_mem _ hx }
  have hQ : Submodule.span O (S : Set V) ≤ Q :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩)
  have hNP : Submodule.span O' (j '' (M : Set V)) = P := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [← hS] at hm
      exact hQ hm
    · apply Submodule.span_mono
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, by rw [← hS]; exact Submodule.subset_span hx, rfl⟩
  refine ⟨⟨S.image j, ?_⟩, ?_⟩
  · rw [Finset.coe_image, hNP]
  · rw [Submodule.span_span_of_tower, ← span_image_span_alt (K' := K') j (M : Set V), hM2]
    change Submodule.span K' (j '' Set.univ) = ⊤
    rw [Set.image_univ]
    apply top_unique
    rw [← (hj.basis (Module.finBasis K V)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (IsBaseChange.basis_apply _ _ _).symm⟩
end Formalism.LatticeBaseChangeAlt
end
end

namespace Formalism.LatticeBaseChangeAlt

theorem localStepDescent : LocalStepDescent :=
  localStepDescent_of finrank_span_image_alt inter_baseChange_lattice index_baseChange_lattice

end Formalism.LatticeBaseChangeAlt
