module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexTwoBlockParahoricConjTorusDiagElementStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  first | exact @GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | exact GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | (intros; apply GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMul
open MeasureTheory Pointwise

namespace GlobalTheory

theorem mem_map_conj_iff_conj_mem {G : Type} [Group G] (J : Subgroup G) (g x : G) :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem measureReal_doubleCoset_eq_relIndex_mul :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  intro G _ _ _ _ _ μ _ J hJo hJc g
  set K := J.map (MulAut.conj g).toMonoidHom with hK
  set H : Subgroup J := K.subgroupOf J with hH
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJc
  have hKo : IsOpen (K : Set G) := by
    have : (K : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (J : Set G) := by
      ext x; rw [SetLike.mem_coe, hK, mem_map_conj_iff_conj_mem]; rfl
    rw [this]; exact hJo.preimage (by fun_prop)
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' (K : Set G) := by
      ext x; simp [hH, Subgroup.mem_subgroupOf]
    rw [this]; exact hKo.preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  let f : J ⧸ H → Set G := fun q => ((q.out : J) * g : G) • (J : Set G)
  have hcover : DoubleCoset.doubleCoset g (J : Set G) (J : Set G) = ⋃ q, f q := by
    ext x
    simp only [DoubleCoset.doubleCoset, Set.mem_mul, Set.mem_singleton_iff, Set.mem_iUnion, f,
      Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ⟨j, hj, b, hb, rfl⟩, k, hk, rfl⟩
      rw [hb]
      refine ⟨(QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H), ?_⟩
      set o := (Quotient.out (QuotientGroup.mk (⟨j, hj⟩ : J) : J ⧸ H) : J) with ho
      have h1 : (QuotientGroup.mk o : J ⧸ H) = QuotientGroup.mk (⟨j, hj⟩ : J) := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq] at h1
      have h2 : ((o : G))⁻¹ * j ∈ K := by
        have := Subgroup.mem_subgroupOf.1 (hH ▸ h1)
        simpa using this
      rw [hK, mem_map_conj_iff_conj_mem] at h2
      refine ⟨g⁻¹ * ((o : G)⁻¹ * j) * g * k, J.mul_mem h2 hk, ?_⟩
      group
    · rintro ⟨q, y, hy, rfl⟩
      exact ⟨(q.out : J) * g, ⟨(q.out : J), (q.out : J).2, g, rfl, rfl⟩, y, hy, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint f) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 ?_
    rintro x hx hx'
    simp only [f, Set.mem_smul_set, smul_eq_mul, SetLike.mem_coe] at hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨y', hy', hxy⟩ := hx'
    apply hqq'
    have e : ((q.out : J) : G) = (q'.out : J) * g * y' * y⁻¹ * g⁻¹ := by
      rw [hxy]; group
    have hmem : (q.out)⁻¹ * q'.out ∈ H := by
      change _ ∈ K.subgroupOf J
      rw [Subgroup.mem_subgroupOf, hK, mem_map_conj_iff_conj_mem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      have : g⁻¹ * ((((q'.out : J) : G) * g * y' * y⁻¹ * g⁻¹)⁻¹ * (q'.out : J)) * g = y * y'⁻¹ := by group
      rw [this]
      exact J.mul_mem hy (J.inv_mem hy')
    have := (QuotientGroup.eq (s := H)).2 hmem
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  have hmeas : ∀ q, MeasurableSet (f q) := fun q =>
    (hJo.smul ((q.out : J) * g : G)).measurableSet
  have hval : ∀ q, μ (f q) = μ (J : Set G) := fun q => measure_smul μ _ _
  have hfin : μ (J : Set G) ≠ ⊤ := (hJc.measure_lt_top).ne
  rw [hcover, measureReal_def, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, measureReal_def, Subgroup.relIndex,
    Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasureRealDoubleCosetEqRelIndexConjMulStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ g : G,
    μ.real (DoubleCoset.doubleCoset g (J : Set G) (J : Set G)) =
      ((J.map (MulAut.conj g).toMonoidHom).relIndex J : ℝ) * μ.real (J : Set G) := by
  first | exact @GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | exact GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul | (intros; apply GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindex
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section
namespace GlobalTheory.ReindexTorus

def reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') : GL n k ≃* GL n' k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k σ).toMulEquiv

theorem val_reindexGL (k : Type) [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (σ : n ≃ n') (g : GL n k) : (reindexGL k σ g).val = Matrix.reindex σ σ g.val := rfl

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem map_reindexGL_KO (σ : n ≃ n') : (KO k n).map (reindexGL k σ).toMonoidHom = KO k n' := by
  ext x
  rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, GlobalTheory.SplitFlip.mem_KO_iff, GlobalTheory.SplitFlip.mem_KO_iff]
  have h1 : ∀ i j, ((reindexGL k σ).symm x).val i j = x.val (σ i) (σ j) := fun i j => rfl
  have h2 : ∀ i j, (((reindexGL k σ).symm x)⁻¹).val i j = (x⁻¹).val (σ i) (σ j) := fun i j => by
    rw [← map_inv]; rfl
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, h1, h2]
  exact and_congr ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩
    ⟨fun h i j => by simpa using h (σ.symm i) (σ.symm j), fun h i j => h _ _⟩

theorem reindexGL_torusElt (σ : n ≃ n') (ϖ : kˣ) (e : n → ℤ) :
    reindexGL k σ (torusElt k n ϖ e) = torusElt k n' ϖ (e ∘ σ.symm) := by
  refine Units.ext ?_
  rw [val_reindexGL, val_torusElt, val_torusElt, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  rfl

theorem relIndex_conj_torusElt_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  intro k _ _ _ _ ϖ n n' _ _ _ _ σ e
  set φ := reindexGL k σ
  have hconj : ∀ g : GL n k, ∀ H : Subgroup (GL n k),
      (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
        (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
    intro g H
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x : 1
    simp [φ, map_mul, map_inv]
  have hK := map_reindexGL_KO k σ
  rw [← reindexGL_torusElt k σ ϖ e, ← hK, ← hconj]
  have key : ∀ A B : Subgroup (GL n k), (A.map φ.toMonoidHom).relIndex (B.map φ.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.map_equiv_eq_comap_symm' φ A, Subgroup.relIndex_comap, Subgroup.map_map]
    have : (φ.symm.toMonoidHom.comp φ.toMonoidHom) = MonoidHom.id _ := by ext x : 1; simp
    rw [this, Subgroup.map_id]
  exact key _ _

end GlobalTheory.ReindexTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntiton
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntiton
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.CellDisjoint

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def reix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m) :
    GL n k →* GL m k :=
  Units.map (Matrix.reindexAlgEquiv k k e).toAlgHom.toMonoidHom

theorem reix_val {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (g : GL n k) : (reix e g).1 = g.1.submatrix e.symm e.symm := rfl

theorem reix_mem_KO {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    {g : GL n k} (hg : g ∈ KO k n) : reix e g ∈ KO k m := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨Units.map (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] e).toAlgHom.toMonoidHom h, Units.ext ?_⟩
  ext i j
  rfl

theorem reix_torusElt {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (e : n ≃ m)
    (ϖ : kˣ) (f : n → ℤ) : reix e (torusElt k n ϖ f) = torusElt k m ϖ (f ∘ e.symm) := by
  ext1
  rw [reix_val, val_torusElt, val_torusElt, submatrix_diagonal_equiv]
  rfl

theorem perm_of_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (a b : Fin N → ℤ)
    (x y : GL (Fin N) k) (hx : x ∈ KO k (Fin N)) (hy : y ∈ KO k (Fin N))
    (h : x * torusElt k (Fin N) ϖ a * y = torusElt k (Fin N) ϖ b) :
    List.Perm (List.ofFn a) (List.ofFn b) := by
  let σ := Tuple.sort (fun i => -a i)
  let τ := Tuple.sort (fun i => -b i)
  have ha : Antitone (a ∘ σ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -a i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  have hb : Antitone (b ∘ τ) := fun i j hij => by
    have := Tuple.monotone_sort (fun i => -b i) hij
    simp only [Function.comp_apply, neg_le_neg_iff] at this
    exact this
  obtain ⟨S₁, h₁, e₁⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] σ
  obtain ⟨T₁, h₃, e₃⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ.symm
  obtain ⟨T₂, h₄, e₄⟩ := Formalism.UG.P.cartan_perm_glint (L := k) 𝒪[k] τ
  have hA : torusElt k (Fin N) ϖ a = S₁ * torusElt k (Fin N) ϖ (a ∘ σ) * S₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₁, e₂]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ a i) σ
  have hB : torusElt k (Fin N) ϖ b = T₁ * torusElt k (Fin N) ϖ (b ∘ τ) * T₂ := by
    ext1
    simp only [Units.val_mul, val_torusElt, e₃, e₄]
    exact Formalism.UG.P.cartan_diag_perm (fun i => (ϖ : k) ^ b i) τ
  have E : (T₁⁻¹ * x * S₁) * torusElt k (Fin N) ϖ (a ∘ σ) * (S₂ * y * T₂⁻¹) =
      torusElt k (Fin N) ϖ (b ∘ τ) := by
    have h' : torusElt k (Fin N) ϖ (b ∘ τ) = T₁⁻¹ * torusElt k (Fin N) ϖ b * T₂⁻¹ := by
      rw [hB]; group
    rw [h', ← h, hA]; group
  have hab : a ∘ σ = b ∘ τ := by
    refine Formalism.UG.P.cartan_unique_gen 𝒪[k] (valuation k) (fun _ => Iff.rfl) (ϖ : k) ϖ.ne_zero
      (hϖ ▸ uniformizer_lt_one) (a ∘ σ) (b ∘ τ) ha hb (T₁⁻¹ * x * S₁)
      (mul_mem (mul_mem (inv_mem h₃) hx) h₁) (S₂ * y * T₂⁻¹) (mul_mem (mul_mem h₂ hy) (inv_mem h₄)) ?_
    have := congrArg Units.val E
    simp only [Units.val_mul, val_torusElt] at this
    simpa only [Units.val_mul, Matrix.mul_assoc] using this
  exact (Equiv.Perm.ofFn_comp_perm σ a).symm.trans (hab ▸ Equiv.Perm.ofFn_comp_perm τ b)

end GlobalTheory.CellDisjoint

namespace GlobalTheory.CellDisjoint

theorem dcell_pairwise_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t a b hab
  refine Set.disjoint_left.2 fun g ha hb => hab (Subtype.ext ?_)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 ha
  obtain ⟨x', hx', y', hy', e⟩ := DoubleCoset.mem_doubleCoset.1 hb
  have hK : ∀ z : GL (Fin r ⊕ Blocks l t) k, z ∈ (parahoric k (Fin r) (Blocks l t) : Set _) →
      z ∈ KO k (Fin r ⊕ Blocks l t) := fun z hz => (mem_parahoric.1 hz).1
  have e' : (x'⁻¹ * x) * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * (y * y'⁻¹) =
      mtor ϖ (b.1 ∘ (blkEquiv l t).symm) := by
    calc _ = x'⁻¹ * (x * mtor ϖ (a.1 ∘ (blkEquiv l t).symm) * y) * y'⁻¹ := by group
      _ = _ := by rw [e]; group
  let ρ : Fin (r + l * t) ≃ Fin r ⊕ Blocks l t :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin r)) (blkEquiv l t))
  have hρ : ∀ f : Fin (l * t) → ℤ,
      (Sum.elim (0 : Fin r → ℤ) (f ∘ (blkEquiv l t).symm)) ∘ ρ.symm.symm = Fin.append (0 : Fin r → ℤ) f := by
    intro f
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp [ρ]
    · simp [ρ]
  have e'' := congrArg (reix (k := k) ρ.symm) e'
  simp only [map_mul, mtor, reix_torusElt, hρ] at e''
  have hp := perm_of_eq hϖ _ _ _ _ (mul_mem (reix_mem_KO _ (inv_mem (hK _ hx'))) (reix_mem_KO _ (hK _ hx)))
    (mul_mem (reix_mem_KO _ (hK _ hy)) (reix_mem_KO _ (inv_mem (hK _ hy')))) e''
  rw [List.ofFn_fin_append, List.ofFn_fin_append, List.perm_append_left_iff] at hp
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.2 a.2)
    (List.sortedGE_ofFn_iff.2 b.2) hp)

end GlobalTheory.CellDisjoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntitonStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | exact GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | (intros; apply GlobalTheory.CellDisjoint.dcell_pairwise_disjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjoint
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_twoBlockParahoricSubgroup k (Fin r) (Blocks l t)
  have h1 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := GlobalTheory.T.measureReal_doubleCoset_eq_relIndex_conj_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistedPlaceDoubleCosetVolumeAndDisjointStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlace_doubleCoset_volume_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.ChainCells.vol_dcell_and_disjoint | exact GlobalTheory.ChainCells.vol_dcell_and_disjoint | (intros; apply GlobalTheory.ChainCells.vol_dcell_and_disjoint <;> assumption)
end
