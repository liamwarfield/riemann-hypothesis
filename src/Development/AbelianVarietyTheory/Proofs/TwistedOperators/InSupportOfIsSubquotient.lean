module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.JacquetExact

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_finset_of_mem_twKer {τ : Representation ℂ G W} {N : Subgroup G} {w : W}
    (hw : w ∈ twKer τ N 1) :
    ∃ S : Finset G, (∀ u ∈ S, u ∈ N) ∧ ∀ H : Subgroup G, (∀ u ∈ S, u ∈ H) → w ∈ twKer τ H 1 := by
  classical
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    refine ⟨{(u : G)}, by simp, fun H hH => ?_⟩
    simpa using GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hH u (by simp)) v
  | zero => exact ⟨∅, by simp, fun _ _ => zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S, hS, hx⟩ := hx
    obtain ⟨T, hT, hy⟩ := hy
    refine ⟨S ∪ T, fun u hu => (Finset.mem_union.1 hu).elim (hS u) (hT u), fun H hH => add_mem
      (hx H fun u hu => hH u (Finset.mem_union_left _ hu))
      (hy H fun u hu => hH u (Finset.mem_union_right _ hu))⟩
  | smul c x _ hx =>
    obtain ⟨S, hS, hx⟩ := hx
    exact ⟨S, hS, fun H hH => Submodule.smul_mem _ c (hx H hH)⟩

theorem map_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    {H : Subgroup G} {v : V} (hv : v ∈ twKer σ H 1) : f v ∈ twKer τ H 1 := by
  have h : twKer σ H 1 ≤ (twKer τ H 1).comap f.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining])
  exact h hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_compact {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : IsSmooth τ)
    (f : σ.IntertwiningMap τ) (hf : Function.Injective f) {H : Subgroup G} (hH : IsCompact (H : Set G))
    {v : V} (hv : f v ∈ twKer τ H 1) : v ∈ twKer σ H 1 := by
  have hσ : IsSmooth σ := (IsSubquotient.of_injective f hf).isSmooth hτ
  obtain ⟨v', hv', he⟩ := IwahoriOnto.exists_fixed_map_eq hσ hH (twKer σ H 1).mkQ v fun h hh =>
    (Submodule.Quotient.eq _).2 (GlobalTheory.IwahoriInj.sub_mem_twKer hh v)
  have h1 : v' - v ∈ twKer σ H 1 := (Submodule.Quotient.eq _).1 he
  have h2 : f v' ∈ twKer τ H 1 := by
    have := add_mem (map_mem_twKer f h1) hv
    rwa [map_sub, sub_add_cancel] at this
  have h3 : f v' ∈ fixed τ H := GlobalTheory.IwahoriInj.mem_fixed.2 fun h hh => by
    rw [← f.isIntertwining, GlobalTheory.IwahoriInj.mem_fixed.1 hv' h hh]
  have h4 : v' = 0 := hf ((GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hH h3 h2).trans (map_zero f).symm)
  rw [h4, zero_sub] at h1
  exact neg_mem_iff.1 h1

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {s : ℕ} {d : Fin s → ℕ}

theorem jacMap_injective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (jacMap e f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  let c : n → ℤ := fun i => (blk e i).val
  have hN : unipRad k e = unipOf k c := unipRad_eq_unipOf k fun i j => by simp [c]
  obtain ⟨S, hS, h2⟩ := exists_finset_of_mem_twKer h1
  have hcompact : ∃ H : Subgroup (GL n k), H ≤ unipOf k c ∧
      IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
    let K (m : ℕ) := GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m)
    have hentries {u : GL n k} (hu : u ∈ unipOf k c) :
        ∀ᶠ m : ℕ in Filter.atTop, ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
      simp only [Filter.eventually_all]
      intro i j
      by_cases hij : c i < c j
      · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
        exact hm.mono (by nlinarith [Int.natCast_nonneg m])
      · rw [mem_unipOf.1 hu i j hij]
        refine Filter.Eventually.of_forall fun m => ?_
        by_cases heq : i = j
        · subst j
          simp [GlobalTheory.IwahoriInj.deep_zero_iff]
        · simp [one_apply_ne heq, GlobalTheory.IwahoriInj.deep_zero]
    have hmem : ∀ᶠ m in Filter.atTop, ∀ u ∈ S, u ∈ K m :=
      (Filter.eventually_all_finset S).2 fun u hu => by
        have hu' := hN ▸ hS u hu
        exact (hentries hu').and (hentries (inv_mem hu'))
    obtain ⟨m, hm⟩ := hmem.exists
    refine ⟨K m ⊓ unipOf k c, inf_le_right, ?_, fun u hu => ⟨hm u hu, hN ▸ hS u hu⟩⟩
    obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
    have hclosed : IsClosed (unipOf k c : Set (GL n k)) := by
      have heq : (unipOf k c : Set (GL n k)) =
          ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | g.val i j = (1 : Matrix n n k) i j} := by
        ext g
        simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [heq]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    rw [Subgroup.coe_inf]
    exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right hclosed
  obtain ⟨H, hle, hH, hSH⟩ := hcompact
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge) (mem_twKer_of_compact hτ f hf hH (h2 H hSH))

theorem jacMap_surjective (e : (Σ a, Fin (d a)) ≃ n) {σ : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (jacMap e f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem isSubquotient_jac (e : (Σ a, Fin (d a)) ≃ n) {π : Representation ℂ (GL n k) V}
    {τ : Representation ℂ (GL n k) W} (hτ : IsSmooth τ) (h : IsSubquotient π τ) :
    IsSubquotient (jac e π) (jac e τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (jacMap_surjective e f hf)).trans
    (.of_injective _ (jacMap_injective e hτ ι Subtype.val_injective))

end Local

theorem inSupport_of_isSubquotient (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (V : Type) [AddCommGroup V]
    [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL n k) V)
    (τ : Representation ℂ (GL n k) W) (χ : kˣ →* ℂˣ) (hτ : IsSmooth τ) (h : IsSubquotient π τ)
    (hχ : InSupport π χ) : InSupport τ χ := by
  obtain ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub, hact⟩ := hχ
  exact ⟨s, d, e, a, ha, Y, i1, i2, σ, hσ, hsub.trans (isSubquotient_jac e hτ h), hact⟩

end GlobalTheory.JacquetExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
open scoped TensorProduct

namespace GlobalTheory.PrinProd

theorem isSubquotient_prinSeries_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  let e : (Σ _ : Fin N, Fin 1) ≃ Fin N := Equiv.sigmaUnique (Fin N) fun _ => Fin 1
  let κ : ℂ ≃ₗ[ℂ] ⨂[ℂ] _ : Fin N, ℂ := (PiTensorProduct.constantBaseRingEquiv (Fin N) ℂ).toLinearEquiv.symm
  let Ψ : IndSp (points (Fin N)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin N)).symm.toMonoidHom) →ₗ[ℂ]
      IndSp e (piTensor fun i => detRep (Fin 1) (χ i)) :=
    MultiIrr.indPull (MonoidHom.id _) continuous_id κ.toLinearMap fun p =>
      ⟨⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩, rfl, fun w => by
        have hd : ∀ a, GeneralLinearGroup.det (leviProj k e p a) =
            GeneralLinearGroup.det (leviProj k (points (Fin N))
              ⟨p, mem_parab_iff.2 fun a b _ _ hab => mem_parab_iff.1 p.2 a b 0 0 hab⟩ a) := fun a => by
          ext
          simp only [GeneralLinearGroup.val_det_apply, det_unique]
          rfl
        show (deltaHalf k _ (leviProj k e p) : ℂ) • piTensor (fun i => detRep (Fin 1) (χ i)) (leviProj k e p) (κ w) =
          κ ((deltaHalf k _ (leviProj k (points (Fin N)) _) : ℂ) •
            ofChar (torusChar χ) ((leviTorus k (Fin N)).symm (leviProj k (points (Fin N)) _)) w)
        rw [map_smul, deltaHalf_apply, deltaHalf_apply]
        refine congrArg₂ (fun (c : ℂˣ) (v : ⨂[ℂ] _ : Fin N, ℂ) => (c : ℂ) • v) ?_ ?_
        · refine (Finset.prod_congr rfl fun a _ => ?_)
          rw [hd, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
        · have hκ : ∀ w, κ w = w • PiTensorProduct.tprod ℂ (fun _ : Fin N => (1 : ℂ)) := fun w => by
            apply κ.symm.injective
            simp [κ]
          rw [hκ, hκ, map_smul, piTensor_tprod, ofChar_apply, torusChar_apply]
          have : (fun i => detRep (Fin 1) (χ i) (leviProj k e p i) 1) =
              fun i => (χ i (GeneralLinearGroup.det (leviProj k e p i)) : ℂ) • (1 : ℂ) := by
            funext i
            simp [detRep]
          rw [this, MultilinearMap.map_smul_univ, smul_smul, mul_comm, Units.coe_prod]
          simp only [hd]
          rfl⟩
  refine .of_injective ⟨Ψ, fun g => rfl⟩ fun f f' h => ?_
  exact Subtype.ext (Subtype.ext (funext fun x =>
    κ.injective (congrFun (congrArg (fun φ => φ.1.1) h) x)))

end GlobalTheory.PrinProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingTopEmb
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

open Matrix Topology Module in
theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCardStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | exact GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | (intros; apply GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRank
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRank
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRankStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  first | exact @GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | exact GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank | (intros; apply GlobalTheory.exists_gl_mul_cols_eq_zero_of_rank <;> assumption)
end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct

namespace GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lower

variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]

def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
theorem _root_.GlobalTheory.RankStrataProof.isSmoothChar_omChar {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))

end Lower

section Open

variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL b k) : (_root_.GlobalTheory.RankStrataProof.lAct s x g).1 = (g⁻¹).val * x.1 := by
  unfold _root_.GlobalTheory.RankStrataProof.lAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.lAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val]
  simp

open Matrix Topology Module in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL b k) :
    _root_.GlobalTheory.RankStrataProof.lAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.lAct s (_root_.GlobalTheory.RankStrataProof.lAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
theorem _root_.GlobalTheory.RankStrataProof.continuous_lAct (s : Set ℕ) : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => _root_.GlobalTheory.RankStrataProof.lAct s p.1 p.2 := by
  have h : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => ((p.2⁻¹ : GL b k) : Matrix b b k) * p.1.1 :=
    (Units.continuous_val.comp (continuous_inv.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  refine Continuous.subtype_mk (h.congr fun p => (_root_.GlobalTheory.RankStrataProof.lAct_val s p.1 p.2).symm) _

end Open

end GlobalTheory.RankStrataProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.ParahoricConjBlocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_iff {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (z : k) :
    valuation k z < 1 ↔ valuation k z ≤ valuation k (ϖ : k) := by
  rw [hϖ, le_uniformizer_iff]

theorem scal₁ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y ≤ 1 ∧ valuation k (y * (ϖ : k) ^ n) ≤ 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ max 0 (-n)) := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, ← le_mul_inv_iff₀ (zpow_pos h0 n), one_mul, ← _root_.zpow_neg]
  rcases le_total 0 n with hn | hn
  · rw [max_eq_left (by omega), zpow_zero]
    have : (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) ^ (-n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show -n ≤ 0 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩
  · rw [max_eq_right (by omega)]
    have : valuation k (ϖ : k) ^ (-n) ≤ 1 := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 0 ≤ -n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩

theorem scal₂ {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : k) (n : ℤ) :
    (valuation k y < 1 ∧ valuation k ((ϖ : k) ^ (-n) * y) < 1) ↔
      valuation k y ≤ valuation k ((ϖ : k) ^ (1 + max 0 n)) := by
  rw [val_lt_one_iff hϖ, val_lt_one_iff hϖ]
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 ϖ.ne_zero
  have h1 : valuation k (ϖ : k) ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  rw [map_mul, map_zpow₀, map_zpow₀, mul_comm (valuation k (ϖ : k) ^ (-n)),
    ← le_mul_inv_iff₀ (zpow_pos h0 _), ← _root_.zpow_neg, neg_neg, ← zpow_one_add₀ h0.ne']
  rcases le_total 0 n with hn | hn
  · rw [max_eq_right hn]
    have : valuation k (ϖ : k) ^ (1 + n) ≤ valuation k (ϖ : k) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 ≤ 1 + n by omega)
    exact ⟨fun h => h.2, fun h => ⟨h.trans this, h⟩⟩
  · rw [max_eq_left hn, add_zero, zpow_one]
    have : valuation k (ϖ : k) ≤ valuation k (ϖ : k) ^ (1 + n) := by
      simpa using zpow_le_zpow_right_of_le_one₀ h0 h1 (show 1 + n ≤ 1 by omega)
    exact ⟨fun h => h.1, fun h => ⟨h, h.trans this⟩⟩

theorem isUnit_det_iff_of_lower {R : Type} [CommRing R] [IsLocalRing R] {A D : Type} [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (N : Matrix (A ⊕ D) (A ⊕ D) R)
    (hN : ∀ i j, N (.inr i) (.inl j) ∈ IsLocalRing.maximalIdeal R) :
    IsUnit N.det ↔ IsUnit N.toBlocks₁₁.det ∧ IsUnit N.toBlocks₂₂.det := by
  simp only [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply]
  have e : N.map (IsLocalRing.residue R) = fromBlocks (N.toBlocks₁₁.map (IsLocalRing.residue R))
      (N.toBlocks₁₂.map (IsLocalRing.residue R)) 0 (N.toBlocks₂₂.map (IsLocalRing.residue R)) := by
    ext (i | i) (j | j) <;> simp [IsLocalRing.residue_eq_zero_iff, hN, toBlocks₁₁, toBlocks₁₂, toBlocks₂₂]
  rw [e, det_fromBlocks_zero₂₁, mul_ne_zero_iff]

theorem mem_KO_val_iff {n : Type} [Fintype n] [DecidableEq n] (y : Matrix n n k) :
    y ∈ Units.val '' (KO k n : Set (GL n k)) ↔ (∀ i j, valuation k (y i j) ≤ 1) ∧ valuation k y.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  constructor
  · rintro ⟨g, ⟨u, rfl⟩, rfl⟩
    refine ⟨fun i j => (u.val i j).2, ?_⟩
    show valuation k ((algebraMap 𝒪[k] k).mapMatrix u.val).det = 1
    rw [← RingHom.map_det, ← hI.isUnit_iff_valuation_eq_one]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  · rintro ⟨h1, h2⟩
    let N : Matrix n n 𝒪[k] := fun i j => ⟨y i j, h1 i j⟩
    have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
    have hu : IsUnit N := by
      rw [Matrix.isUnit_iff_isUnit_det, hI.isUnit_iff_valuation_eq_one, RingHom.map_det, hN]
      exact h2
    exact ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hu.unit, ⟨hu.unit, rfl⟩, hN⟩

theorem val_det_iff_of_lower {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) (hi : ∀ i j, valuation k (y i j) ≤ 1)
    (hl : ∀ i j, valuation k (y (.inr i) (.inl j)) < 1) :
    valuation k y.det = 1 ↔ valuation k y.toBlocks₁₁.det = 1 ∧ valuation k y.toBlocks₂₂.det = 1 := by
  have hI := Valuation.integer.integers (valuation k)
  let N : Matrix (A ⊕ D) (A ⊕ D) 𝒪[k] := fun i j => ⟨y i j, hi i j⟩
  have hN : (algebraMap 𝒪[k] k).mapMatrix N = y := rfl
  have h11 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₁₁ = y.toBlocks₁₁ := by ext; rfl
  have h22 : (algebraMap 𝒪[k] k).mapMatrix N.toBlocks₂₂ = y.toBlocks₂₂ := by ext; rfl
  have key := isUnit_det_iff_of_lower N (fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
    exact (hl i j).ne)
  rwa [hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one, hI.isUnit_iff_valuation_eq_one,
    RingHom.map_det, RingHom.map_det, RingHom.map_det, hN, h11, h22] at key

theorem mem_parahoric_val_iff {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (y : Matrix (A ⊕ D) (A ⊕ D) k) :
    y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧ (∀ i j, valuation k (y.toBlocks₁₂ i j) ≤ 1) ∧
      (∀ i j, valuation k (y.toBlocks₂₁ i j) < 1) ∧ y.toBlocks₂₂ ∈ Units.val '' (KO k D : Set (GL D k)) := by
  have step : y ∈ Units.val '' (parahoric k A D : Set (GL (A ⊕ D) k)) ↔
      y ∈ Units.val '' (KO k (A ⊕ D) : Set (GL (A ⊕ D) k)) ∧ ∀ i j, valuation k (y (.inr i) (.inl j)) < 1 := by
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (mem_parahoric.1 hg).1, rfl⟩, (mem_parahoric.1 hg).2⟩
    · rintro ⟨⟨g, hg, rfl⟩, h⟩
      exact ⟨g, mem_parahoric.2 ⟨hg, h⟩, rfl⟩
  rw [step, mem_KO_val_iff, mem_KO_val_iff, mem_KO_val_iff]
  constructor
  · rintro ⟨⟨hi, hd⟩, hl⟩
    have hd' := (val_det_iff_of_lower y hi hl).1 hd
    exact ⟨⟨fun i j => hi _ _, hd'.1⟩, fun i j => hi _ _, hl, ⟨fun i j => hi _ _, hd'.2⟩⟩
  · rintro ⟨⟨h11, d11⟩, h12, hl, ⟨h22, d22⟩⟩
    have hi : ∀ i j, valuation k (y i j) ≤ 1 := by
      rintro (i | i) (j | j)
      · exact h11 i j
      · exact h12 i j
      · exact (hl i j).le
      · exact h22 i j
    exact ⟨⟨hi, (val_det_iff_of_lower y hi hl).2 ⟨d11, d22⟩⟩, hl⟩

theorem mem_val_map_conj_inf {n : Type} [Fintype n] [DecidableEq n] (K : Subgroup (GL n k)) (t : GL n k)
    (y : Matrix n n k) :
    y ∈ Units.val '' ((K.map (MulAut.conj t).toMonoidHom ⊓ K : Subgroup (GL n k)) : Set (GL n k)) ↔
      y ∈ Units.val '' (K : Set (GL n k)) ∧
        (t⁻¹ : GL n k).val * y * t.val ∈ Units.val '' (K : Set (GL n k)) := by
  constructor
  · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
    replace hg1 : g ∈ K.map (MulAut.conj t).toMonoidHom := hg1
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hg1
    exact ⟨⟨g, hg2, rfl⟩, ⟨_, hg1, by simp⟩⟩
  · rintro ⟨⟨g, hg, rfl⟩, ⟨h, hh, e⟩⟩
    refine ⟨g, ⟨?_, hg⟩, rfl⟩
    show g ∈ K.map (MulAut.conj t).toMonoidHom
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have : t⁻¹ * g * t = h := Units.ext (by simp [e])
    rwa [this]

theorem val_inv_torusElt {n : Type} [Fintype n] [DecidableEq n] (ϖ : kˣ) (f : n → ℤ) :
    ((torusElt k n ϖ f)⁻¹).val = diagonal fun i => (ϖ : k) ^ (-f i) := by
  have : (torusElt k n ϖ f)⁻¹ = torusElt k n ϖ (-f) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv]
    apply Units.ext
    rw [Units.val_mul, val_torusElt, val_torusElt, diagonal_mul_diagonal, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    simpa only [Pi.mul_apply, Pi.neg_apply, Pi.one_apply, _root_.zpow_neg] using
      inv_mul_cancel₀ (zpow_ne_zero (f i) ϖ.ne_zero)
  rw [this, val_torusElt]
  rfl

section conjBlocks
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ)
  (x : Matrix (A ⊕ D) (A ⊕ D) k)

theorem conj_apply (i j : A ⊕ D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)) i j =
      (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) * x i j * (ϖ : k) ^ (Sum.elim 0 e j : ℤ) := by
  have h1 : ((mtor (A := A) ϖ e)⁻¹.val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (-(Sum.elim 0 e i : ℤ)) := val_inv_torusElt _ _
  have h2 : ((mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k) =
      diagonal fun i => (ϖ : k) ^ (Sum.elim 0 e i : ℤ) := val_torusElt _ _
  rw [h1, h2, mul_diagonal, diagonal_mul]

theorem conj_toBlocks₁₁ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₁ =
      x.toBlocks₁₁ := by
  ext i j
  simp only [toBlocks₁₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₁₂ (i : A) (j : D) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₁₂ i j =
      x.toBlocks₁₂ i j * (ϖ : k) ^ e j := by
  simp only [toBlocks₁₂, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₁ (i : D) (j : A) :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₁ i j =
      (ϖ : k) ^ (-e i) * x.toBlocks₂₁ i j := by
  simp only [toBlocks₂₁, of_apply]
  rw [conj_apply]
  simp

theorem conj_toBlocks₂₂ :
    (((mtor (A := A) ϖ e)⁻¹.val * x * (mtor (A := A) ϖ e).val : Matrix (A ⊕ D) (A ⊕ D) k)).toBlocks₂₂ =
      ((torusElt k D ϖ e)⁻¹.val * x.toBlocks₂₂ * (torusElt k D ϖ e).val : Matrix D D k) := by
  have h1 : ((torusElt k D ϖ e)⁻¹.val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ (-e i) := val_inv_torusElt _ _
  have h2 : ((torusElt k D ϖ e).val : Matrix D D k) = diagonal fun i => (ϖ : k) ^ e i := val_torusElt _ _
  rw [h1, h2]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  simp only [toBlocks₂₂, of_apply]
  rw [conj_apply]
  simp

end conjBlocks

theorem blockset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  intro k _ _ _ _ ϖ hϖ A D _ _ _ _ e
  ext x
  rw [mem_val_map_conj_inf, mem_parahoric_val_iff, mem_parahoric_val_iff, conj_toBlocks₁₁, conj_toBlocks₂₂]
  simp only [conj_toBlocks₁₂, conj_toBlocks₂₁, Set.mem_setOf_eq, mem_val_map_conj_inf, ← scal₁ hϖ, ← scal₂ hϖ,
    forall_and]
  tauto

end GlobalTheory.ParahoricConjBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwiseStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  first | exact @GlobalTheory.ParahoricConjBlocks.blockset | exact GlobalTheory.ParahoricConjBlocks.blockset | (intros; apply GlobalTheory.ParahoricConjBlocks.blockset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.ZetaConvergence

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le {K : Set k} (hK : IsCompact K) : ∃ B : ℝ, ∀ x : kˣ, (x : k) ∈ K → nabs k x ≤ B := by
  obtain ⟨y, hy⟩ := hK.elim_directed_cover (fun y : kˣ => GlobalTheory.SplitWeil.cball y)
    (fun y => GlobalTheory.SplitWeil.isOpen_cball y)
    (fun x _ => by
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨1, by simp [hx, GlobalTheory.SplitWeil.cball]⟩
      · exact Set.mem_iUnion.2 ⟨Units.mk0 x hx, by simp [GlobalTheory.SplitWeil.cball]⟩)
    (fun a b => by
      rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
      · exact ⟨b, fun z hz => le_trans (show valuation k z ≤ _ from hz) h, subset_rfl⟩
      · exact ⟨a, subset_rfl, fun z hz => le_trans (show valuation k z ≤ _ from hz) h⟩)
  exact ⟨nabs k y, fun x hx => nabs_le_of_valuation_le (hy hx)⟩

theorem integrable_zetaIntegrand : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : GL n k → ℂ) (α : ℝ), Continuous c → (∀ N : ℕ, ∃ C : ℝ, ∀ g : GL n k, (∀ i j, Deep (-(N : ℤ)) (g.val i j)) → ‖c g‖ ≤ C * nabs k (GeneralLinearGroup.det g) ^ (-α)) → ∀ Φ ∈ SB (Matrix n n k), ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (zetaIntegrand Φ c s) (volGL ν n) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c α hc hb Φ hΦ
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.SBUniform.exists_bound_period k n Φ hΦ
  obtain ⟨C, hC⟩ := hb N
  obtain ⟨hl, hK⟩ : IsLocallyConstant Φ ∧ HasCompactSupport Φ := hΦ
  obtain ⟨B, hB⟩ := exists_nabs_le (IsCompact.image hK (f := fun x : Matrix n n k => x.det)
    continuous_id.matrix_det)
  have := GlobalTheory.SplitWeil.secondCountable k
  have := GlobalTheory.SplitWeil.t2Space k
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : BorelSpace (GL n k) := SplitFlip.borel_GL
  have : SecondCountableTopology (GL n k) := SplitFlip.secondCountable_GL
  have hE := GlobalTheory.SplitWeil.Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hn : IsLocallyConstant fun g : GL n k => nabs k (GeneralLinearGroup.det g) :=
    (isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det
  have hI : Integrable (fun g : GL n k => Φ g.val) ((volM ν n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable Φ (volM ν n n) := hl.continuous.integrable_of_hasCompactSupport hK
    refine hE.integrable_map_iff.1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  refine ⟨α + Fintype.card n - ((Fintype.card n : ℝ) - 1) / 2, fun s hs => ?_⟩
  set t : ℂ := s + ((Fintype.card n : ℂ) - 1) / 2 with ht
  have htr : t.re = s.re + ((Fintype.card n : ℝ) - 1) / 2 := by
    have : ((Fintype.card n : ℂ) - 1) / 2 = ((((Fintype.card n : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [ht, this, Complex.add_re, Complex.ofReal_re]
  have he : 0 ≤ -(Fintype.card n : ℝ) + -α + t.re := by linarith
  have hz : Continuous (zetaIntegrand Φ c s) :=
    ((hl.continuous.comp Units.continuous_val).mul hc).mul (hn.comp fun r : ℝ => (r : ℂ) ^ t).continuous
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (|C| * B ^ (-(Fintype.card n : ℝ) + -α + t.re))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul hz.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := nabs_pos' k (GeneralLinearGroup.det g)
  by_cases h0 : Φ g.val = 0
  · simp [zetaIntegrand, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have h2 := (hC g (hN _ h0)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hp.le _))
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), zetaIntegrand, norm_mul, norm_mul,
    val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos hp, ← ht, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  set a := nabs k (GeneralLinearGroup.det g)
  calc _ ≤ a ^ (-(Fintype.card n : ℝ)) * (‖Φ g.val‖ * (|C| * a ^ (-α)) * a ^ t.re) := by gcongr
    _ = ‖Φ g.val‖ * (|C| * a ^ (-(Fintype.card n : ℝ) + -α + t.re)) := by
      rw [Real.rpow_add hp, Real.rpow_add hp]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.ZetaConvergence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped Pointwise

namespace GlobalTheory.IndexVolume

theorem relIndex_mul_measure_subgroup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

theorem volGL_of_subset_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    (ν : Measure k) (s : Set (GL n k)) (hs : MeasurableSet s) (hK : s ⊆ KO k n) :
    volGL ν n s = volM ν n n (Units.val '' s) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  intro g hg
  obtain ⟨u, rfl⟩ := hK hg
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem relIndex_mul_volM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  intro k _ _ _ _ _ _ ν _ n _ _ H L hHL hLK hH
  obtain ⟨hB, hlc, hsc, hc, -, -, hhaar, -⟩ := volGL_haar k n ν
  have hL : IsOpen (L : Set (GL n k)) := Subgroup.isOpen_mono hHL hH
  have hLc : IsCompact (L : Set (GL n k)) := hc.of_isClosed_subset (L.isClosed_of_isOpen hL) hLK
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  haveI : Finite (L ⧸ H.subgroupOf L) :=
    Subgroup.quotient_finite_of_isOpen _ (hH.preimage continuous_subtype_val)
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := relIndex_mul_measure_subgroup H L hHL hH.measurableSet (volGL ν n)
  have h0 : volGL ν n H ≠ 0 := (hH.measure_pos _ ⟨1, one_mem _⟩).ne'
  have ht : volGL ν n H ≠ ⊤ := ((measure_mono (hHL.trans hLK)).trans_lt hc.measure_lt_top).ne
  rw [← volGL_of_subset_KO ν _ hH.measurableSet (hHL.trans hLK),
    ← volGL_of_subset_KO ν _ hL.measurableSet hLK, ← key]
  refine ⟨ENNReal.toReal_pos h0 ht, ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end GlobalTheory.IndexVolume
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGLStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  first | exact @GlobalTheory.IndexVolume.relIndex_mul_volM | exact GlobalTheory.IndexVolume.relIndex_mul_volM | (intros; apply GlobalTheory.IndexVolume.relIndex_mul_volM <;> assumption)
end
end
