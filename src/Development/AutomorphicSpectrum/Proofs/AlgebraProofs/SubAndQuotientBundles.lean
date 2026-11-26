module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspace
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuot

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K)

theorem finite_not_le_one (a : K) : {i | ¬ C.v i a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    simp
  · refine (C.fin a ha).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro h
    exact hi (le_of_eq h)

theorem finite_not_mapsTo {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {n m : ℕ} (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin m) K V')
    (f : V →ₗ[K] V') :
    {i | ¬ ∀ x, (∀ q, C.v i (b.repr x q) ≤ 1) → ∀ q, C.v i (b'.repr (f x) q) ≤ 1}.Finite := by
  classical
  refine (Set.finite_iUnion fun q : Fin m => Set.finite_iUnion fun r : Fin n =>
    finite_not_le_one C (b'.repr (f (b r)) q)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  apply hi
  intro x hx q
  have hx' : f x = ∑ r, b.repr x r • f (b r) := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finsupp.finsetSum_apply]
  refine (C.v i).map_sum_le fun r _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, (C.v i).map_mul]
  exact mul_le_one' (hx r) (hcon q r)

theorem isBun_sub_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V),
    IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  unfold IsBun at hL ⊢
  obtain ⟨hloc, b0, hb0⟩ := hL
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective W.mkQ W.range_mkQ
  refine ⟨⟨fun i => ?_, Module.finBasis K W, ?_⟩, ⟨fun i => ?_, Module.finBasis K (V ⧸ W), ?_⟩⟩
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, hW, -, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bW, hW⟩
  · refine ((hb0.union (finite_not_mapsTo C (Module.finBasis K W) b0 W.subtype)).union
      (finite_not_mapsTo C b0 (Module.finBasis K W) g)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro w
    show (w : V) ∈ L i ↔ _
    rw [h1]
    have hgw : g (w : V) = w := by simpa using LinearMap.congr_fun hg w
    constructor
    · intro hw q
      have hq := h3 (w : V) hw q
      rwa [hgw] at hq
    · intro hw q
      exact h2 w hw q
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, -, hQ, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bQ, hQ⟩
  · refine ((hb0.union (finite_not_mapsTo C b0 (Module.finBasis K (V ⧸ W)) W.mkQ)).union
      (finite_not_mapsTo C (Module.finBasis K (V ⧸ W)) b0 s)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro y
    show y ∈ (L i).map W.mkQ.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ q
      exact h2 x ((h1 x).1 hx) q
    · intro hy
      have hsy : W.mkQ (s y) = y := by simpa using LinearMap.congr_fun hs y
      exact ⟨s y, (h1 (s y)).2 (h3 y hy), hsy⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_and_quotient_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegDual

open GlobalTheory.CompanionTheory.Ar.Crv Module

variable {K : Type} [Field K] (C : ACurve K)
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem isLatOf_dual (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K) (i : C.I) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (h : IsLatOf C i b (L i)) :
    IsLatOf C i b' (dualLat C L B i) := by
  intro y
  change (∀ x ∈ L i, C.v i (B x y) ≤ 1) ↔ _
  constructor
  · intro hy q
    rw [hb]
    refine hy _ ((h _).2 fun p => ?_)
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · intro hy x hx
    have hx' := (h x).1 hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
    refine (C.v i).map_sum_le fun q _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ← hb]
    exact mul_le_one' (hx' q) (hy q)

theorem dual_symm (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b : Basis (Fin n) K V) (b' : Basis (Fin n) K V')
    (hb : ∀ y q, b'.repr y q = B (b q) y) (x : V) (q : Fin n) :
    b.repr x q = B.flip (b' q) x := by
  have : b.coord q = B.flip (b' q) := by
    refine b.ext fun p => ?_
    rw [LinearMap.flip_apply, ← hb, Basis.coord_apply, Basis.repr_self, Basis.repr_self,
      Finsupp.single_apply, Finsupp.single_apply]
    simp [eq_comm]
  rw [← this, Basis.coord_apply]

theorem exists_dual [FiniteDimensional K V] [FiniteDimensional K V'] (B : V →ₗ[K] V' →ₗ[K] K)
    (hB : Function.Bijective B) {n : ℕ} (b : Basis (Fin n) K V) :
    ∃ b' : Basis (Fin n) K V', ∀ y q, b'.repr y q = B (b q) y := by
  have hf : Function.Bijective B.flip := (LinearMap.flip_bijective_iff₁).2 hB
  refine ⟨b.dualBasis.map (LinearEquiv.ofBijective B.flip hf).symm, fun y q => ?_⟩
  simp

theorem det_dual (B : V →ₗ[K] V' →ₗ[K] K) {n : ℕ}
    (b₀ b : Basis (Fin n) K V) (b₀' b' : Basis (Fin n) K V')
    (h₀ : ∀ y q, b₀'.repr y q = B (b₀ q) y) (hb : ∀ y q, b'.repr y q = B (b q) y) :
    b₀'.det b' = (b₀.det b)⁻¹ := by
  have h1 : b₀'.toMatrix b' = (b.toMatrix b₀).transpose := by
    ext p q
    rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, h₀,
      dual_symm B b b' hb, LinearMap.flip_apply]
  have h2 : (b.toMatrix b₀).det * (b₀.toMatrix b).det = 1 := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  rw [Basis.det_apply, Basis.det_apply, h1, Matrix.det_transpose]
  exact eq_inv_of_mul_eq_one_left h2

theorem isLatOf_reindex (i : C.I) {n m : ℕ} (b : Basis (Fin n) K V) (e : Fin n ≃ Fin m)
    (L : AddSubgroup V) (h : IsLatOf C i b L) : IsLatOf C i (b.reindex e) L := by
  intro x
  rw [h x]
  simp only [Basis.repr_reindex_apply]
  exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩

theorem deg_dual : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B →
    IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧
      dualLat C (dualLat C L B) B.flip = L := by
  intro K _ C V _ _ _ V' _ _ _ L B hL hB
  obtain ⟨hloc, b₀, hfin⟩ := id hL
  choose b hb using hloc
  choose d hd using fun c : Basis (Fin (finrank K V)) K V => exists_dual B hB c
  have hrk : finrank K V = finrank K V' := by
    rw [finrank_eq_card_basis (d b₀), Fintype.card_fin]
  have hd' : ∀ i, IsLatOf C i (d (b i)) (dualLat C L B i) := fun i =>
    isLatOf_dual C L B i (b i) _ (hd _) (hb i)
  have hbun : IsBun C (dualLat C L B) := by
    refine ⟨fun i => ⟨_, isLatOf_reindex C i _ (finCongr hrk) _ (hd' i)⟩,
      (d b₀).reindex (finCongr hrk), hfin.subset fun i hi h => hi ?_⟩
    exact isLatOf_reindex C i _ _ _ (isLatOf_dual C L B i b₀ _ (hd _) h)
  refine ⟨hbun, ?_, ?_⟩
  · rw [(GlobalTheory.T.bundle_degree_eq_sum_valuations K C V' _ _ (d b₀) (fun i => d (b i)) hbun hd').2,
      (GlobalTheory.T.bundle_degree_eq_sum_valuations K C V _ _ b₀ b hL hb).2, ← finsum_neg_distrib]
    refine finsum_congr fun i => ?_
    rw [det_dual B b₀ (b i) _ _ (hd _) (hd _), map_inv₀, WithZero.log_inv, mul_neg]
  · funext i
    ext x
    rw [hb i x]
    exact isLatOf_dual C _ B.flip i (d (b i)) (b i) (dual_symm B _ _ (hd _)) (hd' i) x

end GlobalTheory.CompanionTheory.Ar.Crv.DegDual
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNegStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_degree_neg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B → IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧ dualLat C (dualLat C L B) B.flip = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | exact GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem locFree_map_equiv (R : Subalgebra o Ω) {E E' : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E'] [Module Ω E'] (e : E ≃ₗ[Ω] E') {r : ℕ} {L : AddSubgroup E}
    (h : LocFree R r L) : LocFree R r (L.map e.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hst, k, f, c, hf, hc, hs, hl⟩ := h
  refine ⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩
  · rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hst a ha x hx, by simp⟩
  · obtain ⟨b, hb, hsp, hiff⟩ := hl l
    refine ⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩
    · have : Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    · have key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔
          f l ^ n • e.symm v ∈ L := by
        intro n
        constructor
        · rintro ⟨x, hx, hxe⟩
          have : x = f l ^ n • e.symm v := by
            apply e.injective
            rw [map_smul, e.apply_symm_apply]
            exact hxe
          rwa [← this]
        · intro hx
          exact ⟨_, hx, by simp⟩
      simp only [key]
      rw [hiff (e.symm v)]
      constructor
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        have := congrArg e hv
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum] using this
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        rw [hv]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} {v : ι → Ω} :
    v ∈ stdLat R ι ↔ ∀ j, v j ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem locFree_stdLat (R : Subalgebra o Ω) (m : ℕ) : LocFree R m (stdLat R (Fin m)) := by
  classical
  refine ⟨fun a ha e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem,
    by simp, fun _ => ?_⟩
  · rw [mem_stdLat] at he ⊢
    intro j
    simpa using R.mul_mem ha (he j)
  · refine ⟨fun q => (Pi.basisFun Ω (Fin m)) q, (Pi.basisFun Ω (Fin m)).linearIndependent,
      (Pi.basisFun Ω (Fin m)).span_eq, fun e => ?_⟩
    have hsum : ∀ a : Fin m → Ω, (∑ q, a q • (Pi.basisFun Ω (Fin m)) q) = a := by
      intro a
      simpa using (Pi.basisFun Ω (Fin m)).sum_repr a
    constructor
    · rintro ⟨_, hn⟩
      simp only [one_pow, one_smul] at hn
      exact ⟨e, fun q => ⟨0, by simpa using (mem_stdLat R).1 hn q⟩, (hsum e).symm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      rw [hsum, pow_zero, one_smul, mem_stdLat]
      intro q
      obtain ⟨n, hn⟩ := ha q
      simpa using hn

theorem locFree_divLat (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] {c : Ω}
    (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) : LocFree R r (divLat c L) := by
  have := locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h
  convert this using 1
  ext v
  constructor
  · intro hv
    exact ⟨c • v, hv, by simp [smul_smul, hc]⟩
  · rintro ⟨x, hx, rfl⟩
    show c • (c⁻¹ • x) ∈ L
    simpa [smul_smul, hc] using hx

theorem locFree_map_mkQ_iff (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E₂] [Module Ω E₂] (q : E →ₗ[Ω] E₂) (hq : Function.Surjective q) {r : ℕ}
    (L : AddSubgroup E) :
    LocFree R r (L.map (LinearMap.ker q).mkQ.toAddMonoidHom) ↔ LocFree R r (L.map q.toAddMonoidHom) := by
  let e := q.quotKerEquivOfSurjective hq
  have h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom =
      L.map q.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
  constructor
  · intro h
    rw [← h1]
    exact locFree_map_equiv R e h
  · intro h
    have h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom =
        L.map (LinearMap.ker q).mkQ.toAddMonoidHom := by
      rw [← h1, AddSubgroup.map_map]
      ext v
      simp
    rw [← h2]
    exact locFree_map_equiv R e.symm h

theorem isBaseChange_bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) := by
  have := Fintype.ofFinite ι
  have h := IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C)
    (fun _ => IsBaseChange.linearMap Ω C)
  exact h

theorem span_bcMap_annSub (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (n i : ℕ) :
    Submodule.span C (bcMap Ω C (Fin n) '' (annSub Ω n i : Set (Fin n → Ω))) = annSub C n i := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢
    intro j hj
    simp [bcMap, hv j hj]
  · intro v hv
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv
    have : v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · by_cases hk : (k : ℕ) < i
        · simp [hk, hv k hk, bcMap]
        · simp [hk, bcMap]
      · intro j _ hjk
        by_cases hj : (j : ℕ) < i
        · simp [hj, bcMap]
        · simp [hj, bcMap, Pi.single_apply, hjk.symm]
      · simp
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro k hk
    by_cases hj : (j : ℕ) < i
    · simp [hj]
    · have : k ≠ j := by rintro rfl; exact hj hk
      simp [hj, Pi.single_apply, this]

theorem spanOver_swap {C V Z Vc Zc : Type} [Field C] [Algebra o C] (RC : Subalgebra o C)
    [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (Γ : AddSubgroup (Z × V)) :
    spanOver RC (Prod.map b b' '' (Γ.map (AddEquiv.prodComm (M := Z) (N := V)).toAddMonoidHom : AddSubgroup (V × Z))) =
      (spanOver RC (Prod.map b' b '' Γ)).map (AddEquiv.prodComm (M := Zc) (N := Vc)).toAddMonoidHom := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExact
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExact
open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel

theorem isBaseChange_of_split {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M₁ M M₂ E₁ E E₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup E₁] [Module R E₁] [Module S E₁]
    [IsScalarTower R S E₁] [AddCommGroup E] [Module R E] [Module S E] [IsScalarTower R S E]
    [AddCommGroup E₂] [Module R E₂] [Module S E₂] [IsScalarTower R S E₂]
    (j : M₁ →ₗ[R] M) (p : M →ₗ[R] M₁) (π : M →ₗ[R] M₂) (s : M₂ →ₗ[R] M)
    (hpj : p ∘ₗ j = LinearMap.id) (hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id)
    (f₁ : M₁ →ₗ[R] E₁) (f : M →ₗ[R] E) (f₂ : M₂ →ₗ[R] E₂)
    (i : E₁ →ₗ[S] E) (q : E →ₗ[S] E₂) (hi : Function.Injective i) (hqi : ∀ x, q (i x) = 0)
    (h₁ : ∀ x, i (f₁ x) = f (j x)) (h₂ : ∀ x, q (f x) = f₂ (π x))
    (hf : IsBaseChange S f) (hf₂ : IsBaseChange S f₂) : IsBaseChange S f₁ := by
  let φ : S ⊗[R] M₁ →ₗ[S] E₁ := LinearMap.liftBaseChange S f₁
  have c₁ : ∀ t, i (φ t) = hf.equiv (j.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [φ, IsBaseChange.equiv_tmul, h₁]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₂ : ∀ t, q (hf.equiv t) = hf₂.equiv (π.baseChange S t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, h₂]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have c₃ : ∀ t, p.baseChange S (j.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hpj, LinearMap.baseChange_id]
    rfl
  have c₄ : ∀ t, j.baseChange S (p.baseChange S t) + s.baseChange S (π.baseChange S t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← LinearMap.add_apply, ← LinearMap.baseChange_add, hsum,
      LinearMap.baseChange_id]
    rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have : j.baseChange S a = j.baseChange S b := by
      apply hf.equiv.injective
      rw [← c₁, ← c₁, hab]
    rw [← c₃ a, this, c₃]
  have hsurj : Function.Surjective φ := by
    intro e
    obtain ⟨t, ht⟩ := hf.equiv.surjective (i e)
    have h0 : π.baseChange S t = 0 := by
      apply hf₂.equiv.injective
      rw [← c₂, ht, hqi, map_zero]
    refine ⟨p.baseChange S t, hi ?_⟩
    have := c₄ t
    rw [h0, map_zero, add_zero] at this
    rw [c₁, this, ht]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩) (by
    intro x
    show φ (1 ⊗ₜ[R] x) = f₁ x
    rw [LinearMap.liftBaseChange_tmul, one_smul])

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hex L r₁ r₂ hL hL₂
  let M : Submodule R E :=
    { L with smul_mem' := fun a e he => hL.1 a a.2 e he }
  let M₁ : Submodule R E₁ := M.comap (i.restrictScalars R)
  let M₂ : Submodule R E₂ := M.map (q.restrictScalars R)
  obtain ⟨hfin, hproj, hrk, hbc⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R (r₁ + r₂) M hL
  obtain ⟨hfin₂, hproj₂, hrk₂, hbc₂⟩ := GlobalTheory.T.locally_free_finite_projective_base_change R r₂ M₂ hL₂
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    rw [← LinearMap.mem_ker, ← hex]; exact LinearMap.mem_range_self i x
  let j : M₁ →ₗ[R] M := (i.restrictScalars R).restrict (fun x hx => hx)
  let π : M →ₗ[R] M₂ := (q.restrictScalars R).restrict (fun x hx => ⟨x, hx, rfl⟩)
  have hπ : Function.Surjective π := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (hi (congrArg Subtype.val hab))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hmem : ∀ x : M, (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) x ∈ LinearMap.range j := by
    intro x
    have h0 : π (x - s (π x)) = 0 := by
      have := LinearMap.congr_fun hs (π x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : ((x - s (π x) : M) : E) ∈ LinearMap.range i := by
      rw [hex]; exact congrArg Subtype.val h0
    obtain ⟨y, hy⟩ := h1
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    show i y ∈ M
    rw [hy]; exact (x - s (π x) : M).2
  let p : M →ₗ[R] M₁ := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem
  have hjp : ∀ x, j (p x) = x - s (π x) := by
    intro x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply
      (LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ π : M →ₗ[R] M) hmem x))
  have hπj : ∀ x, π (j x) = 0 := fun x => Subtype.ext (hqi x)
  have hpj : p ∘ₗ j = LinearMap.id := by
    ext1 x
    apply hj
    rw [LinearMap.comp_apply, hjp, hπj, map_zero, sub_zero, LinearMap.id_apply]
  have hsum : j ∘ₗ p + s ∘ₗ π = LinearMap.id := by
    ext1 x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hjp, LinearMap.id_apply, sub_add_cancel]
  have hbc₁ : IsBaseChange Ω M₁.subtype :=
    isBaseChange_of_split j p π s hpj hsum M₁.subtype M.subtype M₂.subtype i q hi hqi
      (fun _ => rfl) (fun _ => rfl) hbc hbc₂
  have hfin₁ : Module.Finite R M₁ :=
    Module.Finite.of_surjective p (fun x => ⟨j x, LinearMap.congr_fun hpj x⟩)
  have hproj₁ : Module.Projective R M₁ := Module.Projective.of_split j p hpj
  have : Module.Finite Ω E := Module.Finite.equiv hbc.equiv
  have hrk₁ : Module.finrank Ω E₁ = r₁ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker q
    rw [LinearMap.range_eq_top.2 hq, finrank_top, ← hex, LinearMap.finrank_range_of_inj hi,
      hrk, hrk₂] at h1
    omega
  exact GlobalTheory.T.locally_free_of_finite_projective R r₁ M₁ hfin₁ hproj₁ hrk₁ hbc₁

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExactStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_short_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main <;> assumption)
end
end

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂] (r r₂ : ℕ) (L : AddSubgroup E) (C C' : AddSubgroup E₂) (Δ : AddSubgroup (E × E₂)), LocFree R r L → LocFree R r₂ C → LocFree R r₂ C' → (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → (∀ v w, (v, w) ∈ Δ → v ∈ L ∧ w ∈ C) → (∀ v ∈ L, ∃ w, (v, w) ∈ Δ) → (∀ w, (0, w) ∈ Δ ↔ w ∈ C') → (∀ w ∈ C, ∃ v, (v, w) ∈ Δ) → LocFree R (r + r₂) Δ ∧ LocFree R r (Δ.comap (AddMonoidHom.inl E E₂)) := by
  intro o Ω _ _ _ R E E₂ _ _ _ _ r r₂ L C C' Δ hL hC hC' hsm hsub hliftL hker hliftC
  have hC'eq : AddSubgroup.comap (LinearMap.inr Ω E E₂).toAddMonoidHom Δ = C' := by
    ext w
    change (0, w) ∈ Δ ↔ w ∈ C'
    exact hker w
  have hLeq : AddSubgroup.map (LinearMap.fst Ω E E₂).toAddMonoidHom Δ = L := by
    ext v
    constructor
    · rintro ⟨⟨v', w⟩, h, rfl⟩
      exact (hsub v' w h).1
    · intro hv
      obtain ⟨w, hw⟩ := hliftL v hv
      exact ⟨(v, w), hw, rfl⟩
  have hCeq : AddSubgroup.map (LinearMap.snd Ω E E₂).toAddMonoidHom Δ = C := by
    ext w
    constructor
    · rintro ⟨⟨v, w'⟩, h, rfl⟩
      exact (hsub v w' h).2
    · intro hw
      obtain ⟨v, hv⟩ := hliftC w hw
      exact ⟨(v, w), hv, rfl⟩
  have hΔ : LocFree R (r + r₂) Δ := by
    have h := GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt.main R (LinearMap.inr Ω E E₂) (LinearMap.fst Ω E E₂)
      LinearMap.inr_injective LinearMap.fst_surjective
      (LinearMap.range_inr (R := Ω) (M := E) (M₂ := E₂)) Δ r₂ r hsm
      (by rw [hC'eq]; exact hC') (by rw [hLeq]; exact hL)
    rwa [Nat.add_comm] at h
  refine ⟨hΔ, ?_⟩
  have h := GlobalTheory.T.locally_free_of_short_exact R (LinearMap.inl Ω E E₂) (LinearMap.snd Ω E E₂)
    LinearMap.inl_injective LinearMap.snd_surjective
    (LinearMap.range_inl (R := Ω) (M := E) (M₂ := E₂)) Δ r r₂ hΔ (by rw [hCeq]; exact hC)
  have he : (LinearMap.inl Ω E E₂).toAddMonoidHom = AddMonoidHom.inl E E₂ := by
    ext x <;> simp
  rw [he] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AffineHilbertIdealSheafOfQuotientIdealTop
namespace GlobalTheory.CompanionTheory.Ar.Num.DualLattice

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.Reflexive

theorem locFree_dual : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (β : E →ₗ[Ω] E₁ →ₗ[Ω] Ω), Function.Bijective β.flip → ∀ (r : ℕ) (L : AddSubgroup E) (L₁ : AddSubgroup E₁), LocFree R r L → (∀ w, w ∈ L₁ ↔ ∀ v ∈ L, β v w ∈ R) → LocFree R r L₁ ∧ ∀ v, v ∈ L ↔ ∀ w ∈ L₁, β v w ∈ R := by
  intro o Ω _ _ _ R E E₁ _ _ _ _ β hβ r L L₁ h h₁
  classical
  refine ⟨?_, fun v => ⟨fun hv w hw => (h₁ w).1 hw v hv, fun hv => ?_⟩⟩
  swap
  · refine locFree_reflexive R r L h v fun ψ hψ => ?_
    obtain ⟨w, rfl⟩ := hβ.2 ψ
    exact hv w ((h₁ w).2 hψ)
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine ⟨fun a ha w hw => (h₁ _).2 fun v hv => ?_, k, f, c, hf, hc, h1, fun l => ?_⟩
  · rw [map_smul, smul_eq_mul]
    exact R.mul_mem ha ((h₁ w).1 hw v hv)
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  let e : E₁ ≃ₗ[Ω] Module.Dual Ω E := LinearEquiv.ofBijective β.flip hβ
  let C : Module.Basis (Fin r) Ω E₁ := B.dualBasis.map e.symm
  have hrepr : ∀ w q, C.repr w q = β (b q) w := fun w q => by
    simp [C, e, ← hB]
  have hsum : ∀ (a : Fin r → Ω) q, β (b q) (∑ q', a q' • C q') = a q := fun a q => by
    rw [← hrepr]
    exact congrFun (C.repr_sum_self a) q
  refine ⟨C, C.linearIndependent, C.span_eq, fun w => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    refine ⟨fun q => C.repr w q, fun q => ?_, (C.sum_repr w).symm⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, f l ^ m • b q ∈ L := by
      refine (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · by_cases hq : q' = q
        · subst hq; simp
        · simp [hq]
      · simp [Pi.single_apply]
    refine ⟨n + m, ?_⟩
    have h2 := (h₁ _).1 hn _ hm
    have h3 : β (f l ^ m • b q) (f l ^ n • w) = f l ^ (n + m) * C.repr w q := by
      rw [hrepr]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rwa [h3] at h2
  · rintro ⟨a, ha, rfl⟩
    let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
    have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
    obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l)
      (β.flip (∑ q, a q • C q)) fun v hv => by
        obtain ⟨a', ha', rfl⟩ := (hb v).1 ⟨0, by simpa using hv⟩
        have key : ∀ q, ∃ n : ℕ, f l ^ n • (a' q * a q) ∈ R' := fun q => by
          obtain ⟨n, hn⟩ := ha q
          obtain ⟨n', hn'⟩ := ha' q
          refine ⟨n' + n, ?_⟩
          have h4 : f l ^ (n' + n) • (a' q * a q) = f l ^ n' * a' q * (f l ^ n * a q) := by
            rw [smul_eq_mul]; ring
          rw [h4]
          exact R.mul_mem hn' hn
        obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f l) (hf l) _ key
        refine ⟨n, ?_⟩
        have h5 : β.flip (∑ q, a q • C q) (∑ q, a' q • b q) = ∑ q, a' q * a q := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum (β.flip (∑ q, a q • C q))]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [map_smul, LinearMap.flip_apply, hsum, smul_eq_mul]
        rw [h5, Finset.mul_sum]
        exact R'.sum_mem fun q _ => hn q
    refine ⟨m, (h₁ _).2 fun v hv => ?_⟩
    rw [map_smul, smul_eq_mul]
    exact hm v hv

end GlobalTheory.CompanionTheory.Ar.Num.DualLattice
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFrob

variable {K : Type} [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]

theorem det_frobVec {d : ℕ} (b : Fin d → Fin d → K) :
    (Pi.basisFun K (Fin d)).det (fun q => frobVec p (b q)) =
      ((Pi.basisFun K (Fin d)).det b) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  rw [Module.Basis.det_apply, Module.Basis.det_apply, ← frobenius_def, RingHom.map_det]
  congr 1

theorem exists_frob_basis {n d : ℕ} (b : Module.Basis (Fin n) K (Fin d → K)) :
    ∃ b' : Module.Basis (Fin n) K (Fin d → K), ∀ q, b' q = frobVec p (b q) := by
  have hnd : n = d := by
    have h := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at h
    exact h.symm
  subst hnd
  have hb : IsUnit ((Pi.basisFun K (Fin n)).det b) :=
    (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).1 ⟨b.linearIndependent, b.span_eq⟩
  have hb' : IsUnit ((Pi.basisFun K (Fin n)).det (fun q => frobVec p (b q))) := by
    rw [det_frobVec p (⇑b)]; exact hb.pow p
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det (Pi.basisFun K (Fin n))).2 hb'
  exact ⟨Module.Basis.mk hli hsp.ge, fun q => Module.Basis.mk_apply _ _ _⟩

theorem repr_frobVec {n d : ℕ} (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (y : Fin d → K) (q : Fin n) :
    b'.repr (frobVec p y) q = (b.repr y q) ^ p := by
  haveI : ExpChar K p := ExpChar.prime Fact.out
  have key : frobVec p y = ∑ i, (b.repr y i) ^ p • b' i := by
    conv_lhs => rw [← b.sum_repr y]
    funext j
    simp only [frobVec, h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_pow_char, mul_pow]
  rw [key, Module.Basis.repr_sum_self]

theorem isLatOf_frob {n d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (i : C.I)
    (b b' : Module.Basis (Fin n) K (Fin d → K))
    (h : ∀ q, b' q = frobVec p (b q)) (hb : IsLatOf C i b (L i)) :
    IsLatOf C i b' (frobLat C p L i) := by
  intro x
  change x ∈ AddSubgroup.closure _ ↔ _
  constructor
  · intro hx
    have hle : AddSubgroup.closure {y | ∃ (a : K) (z : Fin d → K), C.v i a ≤ 1 ∧ z ∈ L i ∧
        y = a • frobVec p z} ≤ GlobalTheory.CompanionTheory.Ar.Crv.Inhab.latOf C i b' := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨a, z, ha, hz, rfl⟩
      change ∀ q, C.v i (b'.repr (a • frobVec p z) q) ≤ 1
      intro q
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, repr_frobVec p b b' h z q, map_mul, map_pow]
      exact mul_le_one' ha (pow_le_one' ((hb z).1 hz q) p)
    exact hle hx
  · intro hx
    rw [← b'.sum_repr x]
    refine AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure
      ⟨b'.repr x q, b q, hx q, (hb (b q)).2 fun r => ?_, by rw [h]⟩
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem isBun_frobLat {d : ℕ} (L : C.I → AddSubgroup (Fin d → K)) (hL : IsBun C L) :
    IsBun C (frobLat C p L) := by
  obtain ⟨h1, b₀, hfin⟩ := hL
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h1 i
    obtain ⟨b', hb'⟩ := exists_frob_basis p b
    exact ⟨b', isLatOf_frob C p L i b b' hb' hb⟩
  · obtain ⟨b', hb'⟩ := exists_frob_basis p b₀
    refine ⟨b', hfin.subset fun i hi => ?_⟩
    intro h
    exact absurd (isLatOf_frob C p L i b₀ b' hb' h) hi

theorem deg_frobLat : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L →
      IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  intro K _ C p _ _ d L hL
  have hL' := isBun_frobLat C p L hL
  refine ⟨hL', ?_⟩
  choose b hb using hL.1
  choose b' hb' using fun i => exists_frob_basis p (b i)
  have e : Fin d ≃ Fin (Module.finrank K (Fin d → K)) := finCongr (Module.finrank_fin_fun K).symm
  set b₀ := (Pi.basisFun K (Fin d)).reindex e with hb₀
  have hdet : ∀ i, b₀.det (b' i) = (b₀.det (b i)) ^ p := by
    intro i
    rw [hb₀, Module.Basis.det_reindex, Module.Basis.det_reindex]
    have hc : (⇑(b' i) ∘ ⇑e) = fun q => frobVec p ((⇑(b i) ∘ ⇑e) q) := by
      funext q; exact hb' i (e q)
    rw [hc, det_frobVec]
  obtain ⟨-, h1⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) L _ b₀ b hL hb
  obtain ⟨-, h2⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C (Fin d → K) (frobLat C p L) _ b₀ b' hL'
    (fun i => isLatOf_frob C p L i (b i) (b' i) (hb' i) (hb i))
  rw [h1, h2, mul_finsum]
  refine finsum_congr fun i => ?_
  rw [hdet, map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Crv.DegFrob
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulPStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_lattice_degree_mul_p : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L → IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistApply
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

def act (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →+* Module.End K V :=
  (actMap (k := k) ρ).toRingHom

theorem act_tmul (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    [Field k] [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    act k ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a :=
  actMap_tmul ρ c a

def toEnd {K O : Type} [Field K] [CommRing O] {d : ℕ} (ρ : O →+* Matrix (Fin d) (Fin d) K) :
    O →+* Module.End K (Fin d → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin d)).toAlgHom.toRingHom.comp ρ

theorem toEnd_apply {K O : Type} [Field K] [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) (v : Fin d → K) :
    toEnd ρ a v = (ρ a).mulVec v := rfl

def twist {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K :=
  (frobenius K p).mapMatrix.comp ρ

theorem twist_apply {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : twist p ρ a = (ρ a).map (· ^ p) := rfl

def conjT {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K where
  toFun a := (ρ (star a)).transpose
  map_one' := by simp
  map_mul' a b := by
    rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp [star_add]

theorem conjT_apply {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : conjT ρ a = (ρ (star a)).transpose := rfl

def frobT (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] :
    TensorProduct ℤ k O →+* TensorProduct ℤ k O :=
  (Algebra.TensorProduct.map (frobenius k p).toIntAlgHom (AlgHom.id ℤ O)).toRingHom

theorem frobT_tmul (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k)
    (a : O) : frobT k O p (c ⊗ₜ[ℤ] a) = (c ^ p) ⊗ₜ[ℤ] a := by
  simp [frobT, frobenius_def]

def chiT {k O : Type} [Field k] [CommRing O] (χ : O →+* k) : TensorProduct ℤ k O →ₐ[k] k :=
  Algebra.TensorProduct.lift (AlgHom.id k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem chiT_tmul {k O : Type} [Field k] [CommRing O] (χ : O →+* k) (c : k) (a : O) :
    chiT χ (c ⊗ₜ[ℤ] a) = c * χ a := by
  simp [chiT]

def idealV {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]
    (τ : A →+* Module.End K V) (J : Ideal A) : Submodule K V :=
  ⨆ a : J, LinearMap.range (τ a)

def FreeAt {K : Type} [Field K] (C : ACurve K) (k : Type) {A V : Type} [Field k] [Algebra k K]
    [CommRing A] [Algebra k A] [AddCommGroup V] [Module K V] (τ : A →+* Module.End K V)
    (L : C.I → AddSubgroup V) (r : ℕ) (i : C.I) : Prop :=
  ∃ (x : Fin r → V) (Θ : (A →ₗ[k] k) → Fin r → (V →ₗ[K] K)),
    (∀ s, x s ∈ L i) ∧
    (∀ l s s' a, Θ l s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0) ∧
    (∀ l s y, y ∈ L i → C.v i (Θ l s y) ≤ 1) ∧
    ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2))

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
end
end
