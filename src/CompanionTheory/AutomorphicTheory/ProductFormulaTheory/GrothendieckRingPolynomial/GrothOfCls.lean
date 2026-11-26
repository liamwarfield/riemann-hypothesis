module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleCast

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriCoeFlattenDecW
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Δ.ms := by
  have e := GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn Δ.term
  rw [decW, ← e, Multiset.coe_reverse, Segment.ms, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL (k := k))) := by
  obtain ⟨L, rfl, hS⟩ := H
  rw [msupp, ← tri_coe_flatten_decW]
  exact (Multiset.coe_eq_coe.2 (GlobalTheory.T.perm_flatten_of_shuffle _ _ hS)).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL (k := k))) := by
  have e : wtW Γ = (((List.ofFn Γ).reverse).map decW).flatten := by
    rw [wtW, GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, List.map_ofFn]
    try rfl
  rw [e, tri_coe_flatten_decW, Multiset.coe_reverse, ← Fin.univ_val_map, H.1, msupp]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hx hy hm
  obtain ⟨Δ, hΔ, hΔL⟩ := hx
  obtain ⟨h', x', hd', ⟨Γ, hΓ, -⟩, -⟩ := id hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have w1 : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hA c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hs : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.1 hm
  have w2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hs _ w1
  have sh : InShW (Finset.univ.val.map Δ) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hA c.jac x hd Δ hΔL (wtW Γ) (GlobalTheory.T.ordered_word_letters_cuspidal Γ) w2
  rw [hΔ.1] at sh
  refine ⟨(tri_msupp_of_inShW sh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases he : 𝔪 = 𝔫
  · exact Or.inl he
  right
  have hL := GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ
  have hne : 𝔪.map toA ≠ (((List.ofFn Γ).map toA : List _) : Multiset _) := by
    rw [hL]
    intro e
    exact he (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
  have key := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
    ((List.ofFn Γ).map toA) (𝔪.map toA) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
    (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW sh) hne
  rw [hL, tri_sqLen_map_toA, tri_sqLen_map_toA] at key
  exact key

end CompanionTheory.Groth

end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JacquetFunctionalClass
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_irr {h : ℕ} (x : Fin h → IrrGL (k := k)) : (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ _ (x a).2.rep.irr
      (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem jm_ne_top {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) : jm x hd π ≠ ⊤ :=
  jhMult_ne_top (piTensor_irr x)
    (GlobalTheory.T.jacquet_module_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) V π hπ hl)

theorem jm_congr {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (hπ : IsSmooth π) (hτ : IsSmooth τ) (φ : π.Equiv τ) : jm x hd π = jm x hd τ :=
  le_antisymm (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd π τ hτ (.of_injective φ.toIntertwiningMap φ.injective))
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd τ π hπ (.of_surjective φ.toIntertwiningMap φ.surjective))

theorem jm_eq_sum {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    jm x hd π = ∑ c ∈ (finite_constituents hl).toFinset, jhMult c.rep.ρ π * jm x hd c.rep.ρ := by
  set F := (finite_constituents hl).toFinset with hF
  have hσ := piTensor_irr x
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation π,
      jm x hd S.toRepresentation = ∑ c ∈ F, jhMult c.rep.ρ S.toRepresentation * jm x hd c.rep.ρ := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation
          (unipRad k (stdBlocks (fun a => (x a).1) hd))) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      rw [jm, jhMult_of_subsingleton hσ]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [jhMult_of_subsingleton c.rep.irr, zero_mul]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hqπ : IsSubquotient (subQuot S T) π := hq.trans (.of_injective j Subtype.val_injective)
    have hsm : IsSmooth (subQuot S T) := hqπ.isSmooth hπ
    have hirr : (subQuot S T).IsIrreducible := isIrreducible_subQuot hT
    let τ : IrrRep (GL (Fin N) k) := ⟨_, subQuot S T, hsm, hirr⟩
    have hsplit : jm x hd S.toRepresentation = jm x hd T.toRepresentation + jm x hd (subQuot S T) :=
      GlobalTheory.CompanionTheory.WordIrr.jhMult_jac_of_le _ hσ hπ hT.le
    have hmult : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ T.toRepresentation + jhMult c.rep.ρ (subQuot S T) :=
      fun c => jhMult_of_le c.rep.irr hT.le
    have hzero : ∀ c : IrrCl (GL (Fin N) k), c ≠ τ.cl → jhMult c.rep.ρ (subQuot S T) = 0 := by
      intro c hc
      by_contra h0
      obtain ⟨ψ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr hirr
      exact hc (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨ψ.symm⟩))
    obtain ⟨ψ⟩ := τ.nonempty_equiv_rep
    have hone : jhMult τ.cl.rep.ρ (subQuot S T) = 1 := by
      rw [jhMult_congr_left ψ]
      exact jhMult_self hirr
    have hmem : τ.cl ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      have := GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ.cl.rep.ρ hqπ
      rw [hone, h0] at this
      exact absurd this (by simp)
    have hQ : jm x hd (subQuot S T) = ∑ c ∈ F, jhMult c.rep.ρ (subQuot S T) * jm x hd c.rep.ρ := by
      rw [Finset.sum_eq_single_of_mem τ.cl hmem (fun c _ hc => by rw [hzero c hc, zero_mul]), hone, one_mul]
      exact (jm_congr x hd τ.cl.rep.smooth hsm ψ).symm
    rw [hsplit, ih T hT.lt, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmult c, add_mul]
  have hT1 : IsSmooth (⊤ : Subrepresentation π).toRepresentation :=
    (IsSubquotient.of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective).isSmooth hπ
  rw [← jm_congr x hd hT1 hπ (topEquiv π), key ⊤]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [jhMult_congr_right _ (topEquiv π)]

end CompanionTheory.Groth.JClsPf

namespace CompanionTheory.Groth

open CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_functional_class (W : List (IrrGL (k := k))) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hl : HasFiniteLength π) :
    J W (cl0 π) = (cls π hl).sum fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k)))).toNat : ℤ) := by
  unfold J cl0
  rw [dif_pos hl, clsGL, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]


variable (k) in
theorem jCls : JCls k := by
  intro W N V _ _ π hπ hl
  by_cases hd : ∑ a, (W.get a).1 = N
  · have hjπ : jmL W π = jm W.get hd π := dif_pos hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k))) = jm W.get hd c.rep.ρ :=
      fun c => dif_pos hd
    refine ⟨by rw [hjπ]; exact jm_ne_top W.get hd π hπ hl, ?_⟩
    set F := (finite_constituents hl).toFinset with hF
    have ha : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ π ≠ ⊤ := fun c => jhMult_ne_top c.rep.irr hl
    have hb : ∀ c : IrrCl (GL (Fin N) k), jm W.get hd c.rep.ρ ≠ ⊤ :=
      fun c => jm_ne_top W.get hd c.rep.ρ c.rep.smooth c.rep.hasFiniteLength
    have hsum : jm W.get hd π =
        ((∑ c ∈ F, (jhMult c.rep.ρ π).toNat * (jm W.get hd c.rep.ρ).toNat : ℕ) : ℕ∞) := by
      rw [jm_eq_sum W.get hd π hπ hl, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, ENat.natCast_toNat (ha c), ENat.natCast_toNat (hb c)]
    have hsub : (cls π hl).support ⊆ F := by
      intro c hc
      rw [Finsupp.mem_support_iff, cls_apply] at hc
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      exact hc (by rw [h0]; rfl)
    rw [jacquet_functional_class W π hl, hjπ, hsum, ENat.toNat_natCast, Nat.cast_sum,
      Finsupp.sum_of_support_subset (cls π hl) hsub
        (fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k)))).toNat : ℤ)) (fun c _ => zero_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hjc c, cls_apply, Nat.cast_mul]
  · have hjπ : jmL W π = 0 := dif_neg hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k))) = 0 := fun c => dif_neg hd
    refine ⟨by rw [hjπ]; exact ENat.zero_ne_top, ?_⟩
    rw [jacquet_functional_class W π hl, hjπ]
    simp [hjc, Finsupp.sum]

end CompanionTheory.Groth

end
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriSupportedLe
open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  choose ε p hp hψ using h
  have hq : ∀ s, ∃ q : MvPolynomial σ ℤ, (∀ t ∈ q.vars, w t < w s) ∧ ψ q = -((ε s : ℤ) • p s) := by
    intro s
    have hmem : -((ε s : ℤ) • p s) ∈ supported ℤ {t | w t < w s} :=
      neg_mem (Subalgebra.smul_mem _ (mem_supported.2 fun t ht => hp s t ht) _)
    obtain ⟨q, hq, hq'⟩ := Subalgebra.mem_map.1
      (tri_supported_le w ψ (fun s => ⟨ε s, p s, hp s, hψ s⟩) (w s) hmem)
    exact ⟨q, fun t ht => mem_supported.1 hq ht, hq'⟩
  choose q hqv hqψ using hq
  let g : σ → MvPolynomial σ ℤ := fun s => (ε s : ℤ) • X s + q s
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ := (aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ).toRingHom
  have hφX : ∀ s, φ (X s) = (ε s : ℤ) • X s + q s := fun s => aeval_X g s
  have hcomp : ∀ x, ψ (φ x) = x := by
    have hAlg : (toZAlg ψ).comp (aeval g) = AlgHom.id ℤ (MvPolynomial σ ℤ) := by
      apply MvPolynomial.algHom_ext
      intro s
      show ψ (φ (X s)) = X s
      rw [hφX, map_add (f := _), map_zsmul, hψ, hqψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
        add_neg_cancel_right]
    intro x
    exact AlgHom.congr_fun hAlg x
  have hφs : Function.Surjective φ := tri_surj w φ fun s => ⟨ε s, q s, hqv s, hφX s⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := hφs x
  obtain ⟨b, rfl⟩ := hφs y
  have hab : a = b := (hcomp a).symm.trans (hxy.trans (hcomp b))
  rw [hab]

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  obtain ⟨m0, hm0, hmin⟩ := a.support.exists_min_image w (Finsupp.support_nonempty_iff.2 hne)
  have hval := congrArg (fun y : I →₀ ℤ => y (L m0)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hval
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m0] at hval
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hval
    exact (Finsupp.mem_support_iff.1 hm0) hval
  · intro m hm hne'
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L m0) = 0
    · simp [hf]
    · rcases hlt m m0 hf with h | h
      · exact absurd h hne'
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro h; exact absurd hm0 h

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  suffices H : ∀ d n, b (c n) - w n ≤ d → ∃ a : M →₀ ℤ, a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 by
    intro n
    obtain ⟨a, ha, ha'⟩ := H _ n le_rfl
    exact ⟨a, fun m hm => (Finsupp.mem_supported _ _).1 ha hm, ha'⟩
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hn
  have H : ∀ i ∈ (f n).support.erase (L n), ∃ a : M →₀ ℤ,
      a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.1 hi
    have hf : f n (L (L.symm i)) ≠ 0 := by
      rw [L.apply_symm_apply]; exact Finsupp.mem_support_iff.1 hi
    obtain ⟨hc, hw⟩ := hlt n (L.symm i) hf
    have hw' : w n < w (L.symm i) :=
      hw.resolve_left fun h => hne (by rw [h, L.apply_symm_apply])
    have hb' := hb (L.symm i)
    have hlt' : b (c (L.symm i)) - w (L.symm i) < d := by
      rw [hc] at hn; omega
    obtain ⟨a, ha, ha'⟩ := ih _ hlt' (L.symm i) le_rfl
    refine ⟨a, ?_, by rw [ha', L.apply_symm_apply]⟩
    rwa [hc]
  choose! g hg hg' using H
  refine ⟨Finsupp.single n 1 - ∑ i ∈ (f n).support.erase (L n), f n i • g i, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ rfl)
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hg i hi))
  · have hs : ∑ i ∈ (f n).support.erase (L n), Finsupp.linearCombination ℤ f (f n i • g i) =
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) :=
      Finset.sum_congr rfl fun i hi => by rw [map_smul, hg' i hi]
    have hsplit : f n = Finsupp.single (L n) 1 +
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) := by
      conv_lhs => rw [← Finsupp.sum_single (f n)]
      rw [Finsupp.sum, ← Finset.add_sum_erase _ _
        (Finsupp.mem_support_iff.2 (by rw [h1]; exact one_ne_zero)), h1]
      simp_rw [Finsupp.smul_single_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, Finsupp.linearCombination_single, one_smul, hs]
    exact (eq_sub_of_add_eq hsplit.symm).symm

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add (f := _), ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
end

section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
section -- merged from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltComb
noncomputable section

open Zc.Cos

namespace CompanionTheory.Groth.AltC

theorem filter_mem_eq_of_sublist {α : Type*} [DecidableEq α] {l m : List α} (hs : l.Sublist m)
    (hm : m.Nodup) : m.filter (fun x => decide (x ∈ l)) = l := by
  induction hs with
  | slnil => rfl
  | @cons l m a hs ih =>
    have ha : a ∉ l := fun h => (List.nodup_cons.1 hm).1 (hs.subset h)
    rw [List.filter_cons_of_neg (by simpa using ha)]
    exact ih (List.nodup_cons.1 hm).2
  | @cons_cons l m a hs ih =>
    rw [List.filter_cons_of_pos (by simp)]
    congr 1
    rw [← ih (List.nodup_cons.1 hm).2]
    apply List.filter_congr
    intro x hx
    have : x ≠ a := fun h => (List.nodup_cons.1 hm).1 (h ▸ hx)
    simp [this, hx]

theorem mem_sub {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) (x : α) :
    x ∈ sub W c i ↔ ∃ p, c p = i ∧ W.get p = x := by
  unfold sub
  simp [List.mem_map, List.mem_filter, List.mem_finRange]

theorem mem_sub_self {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (p : Fin W.length) :
    W.get p ∈ sub W c (c p) :=
  (mem_sub W c (c p) _).2 ⟨p, rfl, rfl⟩

theorem sub_sublist {α : Type*} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    (sub W c i).Sublist W := by
  unfold sub
  have := (List.filter_sublist (p := fun p => decide (c p = i)) (l := List.finRange W.length)).map W.get
  rwa [← List.ofFn_eq_map, List.ofFn_get] at this


open Classical in
theorem shuffleCount_eq {α : Type*} {h : ℕ} (W : List α) (D : Fin h → List α) (hW : W.Nodup) :
    shuffleCount W D = if (∀ i, (D i).Sublist W) ∧ (∀ x ∈ W, ∃! i, x ∈ D i) then 1 else 0 := by
  unfold shuffleCount
  split_ifs with hc
  · rw [Finset.card_eq_one]
    choose c0 hc0 using fun p : Fin W.length => (hc.2 (W.get p) (List.get_mem W p)).exists
    have hu : ∀ p y, W.get p ∈ D y → y = c0 p := fun p y hy =>
      (hc.2 (W.get p) (List.get_mem W p)).unique hy (hc0 p)
    refine ⟨c0, ?_⟩
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hcs
      funext p
      have := mem_sub_self W c p
      rw [hcs (c p)] at this
      exact hu p (c p) this
    · intro hcc i
      rw [hcc]
      have : sub W c0 i = W.filter (fun x => decide (x ∈ D i)) := by
        unfold sub
        conv_rhs => rw [← List.ofFn_get W, List.ofFn_eq_map, List.filter_map]
        congr 1
        apply List.filter_congr
        intro p _
        simp only [Function.comp, decide_eq_decide]
        exact ⟨fun h => h ▸ hc0 p, fun h => (hu p i h).symm⟩
      rw [this, filter_mem_eq_of_sublist (hc.1 i) hW]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c _ hcs
    apply hc
    refine ⟨fun i => hcs i ▸ sub_sublist W c i, fun x hx => ?_⟩
    obtain ⟨p, rfl⟩ := List.get_of_mem hx
    refine ⟨c p, ?_, fun j hj => ?_⟩
    · show W.get p ∈ D (c p)
      rw [← hcs (c p)]; exact mem_sub_self W c p
    simp only at hj
    rw [← hcs j] at hj
    obtain ⟨q, hq, hqp⟩ := (mem_sub W c j _).1 hj
    have := hW.get_inj_iff.1 hqp
    subst this
    exact hq.symm

theorem cond_map {β α : Type*} {h : ℕ} (f : β → α) (hf : Function.Injective f) (w : List β)
    (E : Fin h → List β) :
    ((∀ i, ((E i).map f).Sublist (w.map f)) ∧ (∀ x ∈ w.map f, ∃! i, x ∈ (E i).map f)) ↔
      ((∀ i, (E i).Sublist w) ∧ (∀ y ∈ w, ∃! i, y ∈ E i)) := by
  have hs : ∀ i, ((E i).map f).Sublist (w.map f) ↔ (E i).Sublist w := by
    intro i
    refine ⟨fun H => ?_, fun H => H.map f⟩
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.1 H
    rwa [List.map_injective_iff.2 hf he]
  simp only [hs, List.forall_mem_map, List.mem_map_of_injective hf]

def wN (L : ℕ) (T : Finset ℕ) : List ℕ :=
  ((List.range L).filter (fun x => decide (x ∈ T))).reverse ++ (List.range L).filter (fun x => decide (x ∉ T))

theorem mem_wN {L x : ℕ} {T : Finset ℕ} : x ∈ wN L T ↔ x < L := by
  unfold wN
  by_cases hx : x ∈ T <;> simp [hx]

theorem nodup_wN (L : ℕ) (T : Finset ℕ) : (wN L T).Nodup := by
  unfold wN
  rw [List.nodup_append]
  refine ⟨List.nodup_reverse.2 ((List.nodup_range).filter _), (List.nodup_range).filter _, ?_⟩
  intro a ha c hc hac
  subst hac
  simp at ha hc
  exact hc.2 ha.2

theorem sublist_of_lt {l m : List ℕ} (hl : l.Pairwise (· < ·)) (hm : m.Pairwise (· < ·))
    (hs : ∀ x ∈ l, x ∈ m) : l.Sublist m :=
  List.sublist_of_subperm_of_pairwise (List.subperm_of_subset hl.nodup hs) hl hm

theorem run_sublist {L b l : ℕ} {T : Finset ℕ} (hbl : b + l ≤ L) :
    ((List.range' b l).reverse).Sublist (wN L T) ↔ ∀ x, b < x → x < b + l → x ∈ T := by
  have hA : ((List.range L).filter (fun x => decide (x ∈ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hB : ((List.range L).filter (fun x => decide (x ∉ T))).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  constructor
  · intro hs x hbx hxl
    by_contra hxT
    obtain ⟨F1, F2, hE, h1, h2⟩ := List.sublist_append_iff.1 hs
    have hxE : x ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hbE : b ∈ (List.range' b l).reverse := by
      simp only [List.mem_reverse, List.mem_range'_1]; omega
    have hpw : (F1 ++ F2).Pairwise (fun a c => c < a) := by
      rw [← hE]; exact List.pairwise_reverse.2 List.pairwise_lt_range'
    have hx2 : x ∈ F2 := by
      rw [hE] at hxE
      rcases List.mem_append.1 hxE with h | h
      · have := h1.subset h
        simp at this
        exact absurd this.2 hxT
      · exact h
    have hb2 : b ∈ F2 := by
      rw [hE] at hbE
      rcases List.mem_append.1 hbE with h | h
      · have := (List.pairwise_append.1 hpw).2.2 b h x hx2
        omega
      · exact h
    have hinc : F2.Pairwise (· < ·) := hB.sublist h2
    have hdec := (List.pairwise_append.1 hpw).2.1
    rcases F2 with _ | ⟨y, _ | ⟨z, t⟩⟩
    · simp at hx2
    · simp at hx2 hb2
      omega
    · have a1 := (List.pairwise_cons.1 hinc).1 z (by simp)
      have a2 := (List.pairwise_cons.1 hdec).1 z (by simp)
      omega
  · intro hT
    by_cases hb : b ∈ T
    · have : (List.range' b l).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rcases Nat.eq_or_lt_of_le hx.1 with h | h
        · exact h ▸ hb
        · exact hT x h hx.2
      exact (List.reverse_sublist.2 this).trans (List.sublist_append_left _ _)
    · rcases l with _ | m
      · simp
      rw [List.range'_succ, List.reverse_cons]
      have : (List.range' (b + 1) m).Sublist ((List.range L).filter (fun x => decide (x ∈ T))) := by
        refine sublist_of_lt List.pairwise_lt_range' hA fun x hx => ?_
        rw [List.mem_range'_1] at hx
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨by omega, hT x (by omega) (by omega)⟩
      refine (List.reverse_sublist.2 this).append (List.singleton_sublist.2 ?_)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, hb⟩

def Cond (L : ℕ) (T : Finset ℕ) {h : ℕ} (b l : Fin h → ℕ) : Prop :=
  (∀ i, ((List.range' (b i) (l i)).reverse).Sublist (wN L T)) ∧
    (∀ x ∈ wN L T, ∃! i, x ∈ (List.range' (b i) (l i)).reverse)

theorem cond_iff {L : ℕ} {T : Finset ℕ} {h : ℕ} {b l : Fin h → ℕ} (hl : ∀ i, 0 < l i) :
    Cond L T b l ↔ (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → x ∈ T) := by
  have hmem : ∀ i x, x ∈ (List.range' (b i) (l i)).reverse ↔ b i ≤ x ∧ x < b i + l i := by
    intro i x; simp [List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : ∀ i, b i + l i ≤ L := fun i => by
      have hi := hl i
      have := (h1 i).subset ((hmem i (b i + l i - 1)).2 ⟨by omega, by omega⟩)
      rw [mem_wN] at this
      omega
    refine ⟨hb, fun x hx => ?_, fun i => (run_sublist (hb i)).1 (h1 i)⟩
    obtain ⟨i, hi, hu⟩ := h2 x (mem_wN.2 hx)
    exact ⟨i, (hmem i x).1 hi, fun j hj => hu j ((hmem j x).2 hj)⟩
  · rintro ⟨hb, hP, hT⟩
    refine ⟨fun i => (run_sublist (hb i)).2 (hT i), fun x hx => ?_⟩
    obtain ⟨i, hi, hu⟩ := hP x (mem_wN.1 hx)
    exact ⟨i, (hmem i x).2 hi, fun j hj => hu j ((hmem j x).1 hj)⟩

end CompanionTheory.Groth.AltC

namespace CompanionTheory.Groth.AltC


open Classical in
theorem altSumN (L : ℕ) (hL : 0 < L) (s : Finset (Finset (Fin L))) (hs : ∀ S, S ∈ s ↔ ∀ a ∈ S, (a : ℕ) ≠ 0)
    {h : ℕ} (b l : Fin h → ℕ) (hl : ∀ i, 0 < l i) (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, f S = (-1) ^ S.card * if Cond L (S.map Fin.valEmbedding) b l then 1 else 0) :
    ∑ S ∈ s, f S = if h = 1 ∧ ∀ i, b i = 0 ∧ l i = L then (-1) ^ (L - 1) else 0 := by
  have hcond : ∀ S : Finset (Fin L), Cond L (S.map Fin.valEmbedding) b l ↔ (∀ i, b i + l i ≤ L) ∧
      (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i) ∧
      (∀ i x, b i < x → x < b i + l i → ∃ a ∈ S, (a : ℕ) = x) := by
    intro S
    rw [cond_iff hl]
    simp [Finset.mem_map]
  by_cases hB : (∀ i, b i + l i ≤ L) ∧ (∀ x < L, ∃! i, b i ≤ x ∧ x < b i + l i)
  swap
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      exact fun H => hB ⟨H.1, H.2.1⟩
    · rintro ⟨rfl, hbl⟩
      apply hB
      refine ⟨fun i => by rw [(hbl i).1, (hbl i).2]; simp, fun x hx => ⟨0, ?_, fun j _ => Subsingleton.elim _ _⟩⟩
      show b 0 ≤ x ∧ x < b 0 + l 0
      rw [(hbl 0).1, (hbl 0).2]
      exact ⟨Nat.zero_le _, by omega⟩
  obtain ⟨hb, hP⟩ := hB
  by_cases hz : ∃ j, b j ≠ 0
  · obtain ⟨j, hj⟩ := hz
    rw [if_neg (by rintro ⟨_, hbl⟩; exact hj (hbl j).1)]
    have hjL : b j < L := by have := hb j; have := hl j; omega
    set a : Fin L := ⟨b j, hjL⟩ with ha_def
    have hint : ∀ i x, b i < x → x < b i + l i → x ≠ (a : ℕ) := by
      intro i x h1 h2 hx
      rw [ha_def] at hx
      simp only at hx
      subst hx
      obtain ⟨k, _, hu⟩ := hP (b j) hjL
      have e1 := hu i ⟨h1.le, h2⟩
      have e2 := hu j ⟨le_rfl, by have := hl j; omega⟩
      rw [← e2] at e1
      subst e1
      omega
    have hg : ∀ S : Finset (Fin L), (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding =
        (if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding := fun _ => rfl
    have hc : ∀ S : Finset (Fin L), Cond L ((if a ∈ S then S.erase a else insert a S).map Fin.valEmbedding) b l ↔
        Cond L (S.map Fin.valEmbedding) b l := by
      intro S
      rw [hcond, hcond]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun x =>
        imp_congr_right fun h1 => imp_congr_right fun h2 => ?_
      have hxa := hint i x h1 h2
      constructor
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        split_ifs at ha' with haS
        · exact Finset.mem_of_mem_erase ha'
        · rcases Finset.mem_insert.1 ha' with h | h
          · exact absurd (congrArg Fin.val h) hxa
          · exact h
      · rintro ⟨a', ha', rfl⟩
        refine ⟨a', ?_, rfl⟩
        have : a' ≠ a := fun h => hxa (congrArg Fin.val h)
        split_ifs
        · exact Finset.mem_erase.2 ⟨this, ha'⟩
        · exact Finset.mem_insert_of_mem ha'
    have hcard : ∀ S : Finset (Fin L), (-1 : ℤ) ^ (if a ∈ S then S.erase a else insert a S).card =
        -(-1) ^ S.card := by
      intro S
      split_ifs with haS
      · rw [Finset.card_erase_of_mem haS]
        have : 0 < S.card := Finset.card_pos.2 ⟨a, haS⟩
        obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
        rw [hn, pow_succ]
        simp
      · rw [Finset.card_insert_of_notMem haS, pow_succ]
        ring
    refine Finset.sum_involution (fun S _ => if a ∈ S then S.erase a else insert a S) ?_ ?_ ?_ ?_
    · intro S _
      rw [hf, hf, hcard, hc]
      ring
    · intro S _ _
      split_ifs with haS
      · exact fun h => Finset.notMem_erase a S (by rw [h]; exact haS)
      · exact fun h => haS (by rw [← h]; exact Finset.mem_insert_self a S)
    · intro S hS
      rw [hs] at hS ⊢
      intro x hx
      split_ifs at hx
      · exact hS x (Finset.mem_of_mem_erase hx)
      · rcases Finset.mem_insert.1 hx with rfl | h
        · exact hj
        · exact hS x h
    · intro S _
      by_cases haS : a ∈ S
      · simp [haS, Finset.insert_erase]
      · simp [haS]
  · push Not at hz
    obtain ⟨i0, _, hu⟩ := hP 0 hL
    have hall : ∀ i, i = i0 := fun i => hu i ⟨by rw [hz i], by rw [hz i]; have := hl i; omega⟩
    have hh : h = 1 := by
      have : Fintype.card (Fin h) = 1 := Fintype.card_eq_one_iff.2 ⟨i0, hall⟩
      simpa using this
    subst hh
    have hlL : ∀ i, l i = L := by
      intro i
      rw [hall i]
      have := hb i0
      rw [hz] at this
      by_contra hne
      obtain ⟨k, hk, _⟩ := hP (l i0) (by omega)
      rw [hall k, hz] at hk
      omega
    rw [if_pos ⟨rfl, fun i => ⟨hz i, hlL i⟩⟩]
    obtain ⟨S0, hS0def⟩ : ∃ S0 : Finset (Fin L), S0 = Finset.univ.filter (fun a : Fin L => (a : ℕ) ≠ 0) := ⟨_, rfl⟩
    have hS0 : S0 ∈ s := (hs S0).2 (fun a ha => by rw [hS0def] at ha; exact (Finset.mem_filter.1 ha).2)
    rw [Finset.sum_eq_single_of_mem S0 hS0]
    · rw [hf, if_pos, mul_one]
      · congr 1
        obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
        have : S0 = Finset.univ.erase 0 := by
          ext x
          rw [hS0def, Finset.mem_filter, Finset.mem_erase]
          simp only [Finset.mem_univ, true_and, and_true]
          exact ⟨fun hx h => hx (by rw [h]; rfl), fun hx h => hx (Fin.ext (by simpa using h))⟩
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · rw [hcond]
        refine ⟨hb, hP, fun i x h1 h2 => ⟨⟨x, by rw [hz, hlL] at h2; simpa using h2⟩, ?_, rfl⟩⟩
        rw [hz] at h1
        simp [hS0def]
        omega
    · intro S hS hne
      rw [hf, if_neg, mul_zero]
      rw [hcond]
      rintro ⟨_, _, hT⟩
      apply hne
      ext x
      simp only [hS0def, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        exact (hs S).1 hS x hx
      · intro hx0
        obtain ⟨a', ha', he⟩ := hT i0 x (by rw [hz]; omega) (by rw [hz, hlL]; simp)
        rwa [Fin.ext he] at ha'

end CompanionTheory.Groth.AltC

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.AltS

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tN (Δ : Segment k) (n : ℕ) : IrrGL (k := k) := Δ.first.nu (n : ℂ)

theorem tN_injective (Δ : Segment k) : Function.Injective (tN Δ) := fun a b h =>
  GlobalTheory.T.cuspidal_twist_injective CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top Δ.first Δ.isCusp_first a b h

theorem tN_zero (Δ : Segment k) : tN Δ 0 = Δ.first := by
  simp [tN]

theorem vWord_eq (Δ : Segment k) (S : Finset (Fin Δ.len)) :
    vWord Δ S = (AltC.wN Δ.len (S.map Fin.valEmbedding)).map (tN Δ) := by
  have key : ∀ (p : Fin Δ.len → Bool) (q : ℕ → Bool), (∀ a : Fin Δ.len, p a = q a) →
      ((List.finRange Δ.len).filter p).map Fin.val = (List.range Δ.len).filter q := by
    intro p q hpq
    rw [← List.map_coe_finRange_eq_range, List.filter_map]
    congr 1
    exact List.filter_congr fun a _ => hpq a
  have hmemS : ∀ a : Fin Δ.len, (a : ℕ) ∈ S.map Fin.valEmbedding ↔ a ∈ S := fun a => Finset.mem_map' Fin.valEmbedding
  unfold vWord AltC.wN
  rw [← key (fun a => decide (a ∈ S)) (fun n => decide (n ∈ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← key (fun a => decide (a ∉ S)) (fun n => decide (n ∉ S.map Fin.valEmbedding)) (by intro a; simp only [hmemS]),
    ← List.map_reverse, ← List.map_append, List.map_map]
  rfl

theorem decWord_eq (Δ Γ : Segment k) (b : ℕ) (hb : Γ.first = tN Δ b) :
    decWord Γ = ((List.range' b Γ.len).reverse).map (tN Δ) := by
  unfold decWord
  rw [List.map_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range']
  rw [Segment.term, hb, tN, tN]
  simp [Nat.cast_add]

theorem first_mem_decWord (Γ : Segment k) : Γ.first ∈ decWord Γ := by
  unfold decWord
  rw [List.mem_reverse, List.mem_ofFn]
  exact ⟨⟨0, Γ.len_pos⟩, by simp [Segment.term]⟩

end CompanionTheory.Groth.AltS

namespace CompanionTheory.Groth

open AltS

theorem altSum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    AltSum k := by
  intro Δ h Γ
  have hW : ∀ S, (vWord Δ S).Nodup := fun S => by
    rw [vWord_eq]; exact (AltC.nodup_wN _ _).map (tN_injective Δ)
  have hmapiff : (Finset.univ.val.map Γ = {Δ}) ↔ h = 1 ∧ ∀ i, Γ i = Δ := by
    rw [← Multiset.replicate_one, Multiset.eq_replicate]
    simp
  by_cases hex : ∀ i, ∃ n, (Γ i).first = tN Δ n
  · choose b hb using hex
    have hd : ∀ i, decWord (Γ i) = ((List.range' (b i) (Γ i).len).reverse).map (tN Δ) :=
      fun i => decWord_eq Δ (Γ i) (b i) (hb i)
    have H := AltC.altSumN Δ.len Δ.len_pos (vSets Δ) (by intro S; simp [vSets]) b (fun i => (Γ i).len)
      (fun i => (Γ i).len_pos)
      (fun S => (-1 : ℤ) ^ S.card * (shuffleCount (vWord Δ S) (fun i => decWord (Γ i)) : ℤ)) (by
        intro S
        congr 1
        rw [AltC.shuffleCount_eq _ _ (hW S)]
        have e : ((∀ i, (decWord (Γ i)).Sublist (vWord Δ S)) ∧ ∀ x ∈ vWord Δ S, ∃! i, x ∈ decWord (Γ i)) ↔
            AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len) := by
          simp only [hd, vWord_eq]
          rw [AltC.cond_map (tN Δ) (tN_injective Δ)]
          rfl
        by_cases hC : AltC.Cond Δ.len (S.map Fin.valEmbedding) b (fun i => (Γ i).len)
        · rw [if_pos (e.2 hC), if_pos hC]; simp
        · rw [if_neg (mt e.1 hC), if_neg hC]; simp)
    rw [H]
    have hiff : (h = 1 ∧ ∀ i, b i = 0 ∧ (Γ i).len = Δ.len) ↔ Finset.univ.val.map Γ = {Δ} := by
      rw [hmapiff]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun ⟨h0, hl⟩ => ?_, fun he => ⟨?_, by rw [he]⟩⟩
      · exact Segment.ext_first (by rw [hb i, h0, tN_zero]) hl
      · exact tN_injective Δ (by rw [← hb i, he, tN_zero])
    by_cases hc : Finset.univ.val.map Γ = {Δ}
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (mt hiff.1 hc), if_neg hc]
  · push Not at hex
    obtain ⟨i, hi⟩ := hex
    rw [if_neg]
    · apply Finset.sum_eq_zero
      intro S _
      rw [AltC.shuffleCount_eq _ _ (hW S), if_neg]
      · simp
      rintro ⟨hs, _⟩
      have := (hs i).subset (first_mem_decWord (Γ i))
      rw [vWord_eq, List.mem_map] at this
      obtain ⟨n, _, hn⟩ := this
      exact hi n hn.symm
    · rw [hmapiff]
      rintro ⟨_, hall⟩
      exact hi 0 (by rw [hall i, tN_zero])

end CompanionTheory.Groth

end
end

namespace CompanionTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hm : MulCls k := by apply mulCls
  have ha : Assoc k := by apply assoc; exact hm
  have hc : Comm k := comm k
  have h1 : One k := by apply one
  have hl : ProdList k := by apply prodList; exact hm
  refine ⟨H k, hm, ha, hc, h1, hl, tri k (H k), ?_, by apply jCls, by apply jSeg, altSum k⟩
  apply multOne <;> first | exact H k | assumption

end CompanionTheory.Groth
