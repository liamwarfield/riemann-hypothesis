module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsComplOfAdmissible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FRedUnique

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.IsZSegDetRep
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FFirstProd
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.firstProd :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL (k := k))) (h : ℕ) (y : Fin h → IrrGL (k := k)) (x : IrrGL (k := k)) (hc : ∑ i, (y i).1 = x.1), (∀ i, FirstIn (y i) P) → jhMult x.rep (prodIrr y hc) ≠ 0 → FirstIn x P := by
  intro hG hBZ k _ _ _ _ P h y x hc hy hx q hq hq0 hjm
  classical
  have h1 : jm q hq (prodIrr y hc) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hjm).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (isSmooth_parInd _ _) (jhMult_ne_zero_iff.1 hx)))
  obtain ⟨z, hr, hz, hrow, hcol⟩ := UpperTheory.Lit.Cas.cells hG hBZ k h x.1 y hc q hq h1
  have hpos : 0 < ∑ i, (z i 0).1 := (hz 0).symm ▸ hq0.1
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨A, hA, w, hwA, hwP⟩ :=
    (UpperTheory.Lit.Full.piece hG hBZ k (y i) P (z i) (hr i) (hrow i)).1 (hy i) (Nat.pos_of_ne_zero hi)
  choose t ht using fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (z j 0)
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun j => z j 0) (hd := hz 0) ht
    (q 0).2.rep.irr (jhMult_ne_zero_iff.1 (hcol 0))
  have e1 : ∑ j, t j = {q 0} := SupportUnique.eq_singleton_of_isCusp hq0 hS
  have e2 : t i = A := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (ht i) hA
  have hw : w ∈ ∑ j, t j :=
    Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => zero_le) (Finset.mem_univ i)) (e2 ▸ hwA)
  rw [e1, Multiset.mem_singleton] at hw
  exact hw ▸ hwP
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.SumOfOfFn
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FRedTimesZ
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FProdStart
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem eq_single_of_monomial {ι σ : Type*} (Ψ : (ι →₀ ℤ) ≃+ MvPolynomial σ ℤ) (C : ι →₀ ℤ) (m : σ →₀ ℕ)
    (ep : Ψ C = MvPolynomial.monomial m 1) (hnn : ∀ w, 0 ≤ C w) (hU : ∀ w x, C w ≠ 0 → C x ≠ 0 → x = w) :
    ∃ w, C = Finsupp.single w 1 := by
  classical
  have hne : C ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ep
    exact one_ne_zero ((MvPolynomial.monomial_eq_zero).1 ep.symm)
  obtain ⟨w, hw⟩ : ∃ w, w ∈ C.support := Finsupp.support_nonempty_iff.2 hne
  have hw' := Finsupp.mem_support_iff.1 hw
  have h1 : C = C w • Finsupp.single w (1 : ℤ) := by
    ext x
    rw [Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with hx
    · rw [hx, smul_eq_mul, mul_one]
    · rw [smul_zero]
      by_contra hx0
      exact hx (hU w x hw' hx0).symm
  have h2 : C w * AddMonoidAlgebra.coeff (Ψ (Finsupp.single w 1)) m = 1 := by
    have h3 := congrArg (fun p => AddMonoidAlgebra.coeff (Ψ p) m) h1
    simp only [map_zsmul, ep, MvPolynomial.coeff_monomial, if_true, MvPolynomial.coeff_smul, smul_eq_mul] at h3
    exact h3.symm
  have h4 : C w = 1 := by
    have := hnn w
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with h | h
    · exact h.1
    · omega
  rw [h4, one_smul] at h1
  exact ⟨w, h1⟩

open GlobalTheory.LocGL.SupportRing in
private theorem occ_of_cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {B : Representation ℂ (GL (Fin N) k) V}
    (hB : HasFiniteLength B) (w : IrrGL (k := k)) (hw : clsGL B hB w ≠ 0) :
    N = w.1 ∧ ∀ e : N = w.1, IsSubquotient w.rep (e ▸ B : Representation ℂ (GL (Fin w.1) k) V) := by
  obtain ⟨n, c⟩ := w
  obtain rfl : n = N := by
    by_contra hne
    refine hw ?_
    rw [clsGL, Finsupp.mapDomain_notin_range]
    rintro ⟨c', h'⟩
    exact hne (congrArg Sigma.fst h').symm
  refine ⟨rfl, fun _ => ?_⟩
  exact isSubquotient_of_clsGL_ne hB c.rep.smooth c.rep.irr (by
    have e : IrrGL.of c.rep.ρ c.rep.smooth c.rep.irr = (⟨n, c⟩ : IrrGL (k := k)) := IrrGL.of_rep ⟨n, c⟩
    rw [e]
    exact hw)

section

open GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem bas_of_isZSeg {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)}
    {Ψ : GrothGL k ≃+ MvPolynomial (Segment k) ℤ} (hS : IsSegmentClass k Z)
    (hX : ∀ Δ, Ψ (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1) = MvPolynomial.X Δ)
    (D : Segment k) (y : IrrGL (k := k)) (hy : IsZSeg D y.rep) : bas Ψ y = MvPolynomial.X D := by
  obtain ⟨n, c⟩ := y
  obtain rfl : D.len * D.d = n := hy.deg_eq
  have e : c = Z D := c.cl_rep.symm.trans (IsZSeg.cl_eq hS (π := c.rep) hy)
  rw [← hX D, e]
  rfl

private theorem prod_X_monomial {σ : Type*} {h : ℕ} (Δ : Fin h → σ) (f : Fin h → MvPolynomial σ ℤ)
    (hf : ∀ i, f i = MvPolynomial.X (Δ i)) : ∃ m, ∏ i, f i = MvPolynomial.monomial m (1 : ℤ) := by
  refine Finset.prod_induction _ (fun p => ∃ m, p = MvPolynomial.monomial m (1 : ℤ)) ?_ ⟨0, rfl⟩ fun i _ => ?_
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [MvPolynomial.monomial_mul, one_mul]⟩
  · exact ⟨_, hf i⟩

private theorem occ_prodIrr {h N : ℕ} (z : Fin h → IrrGL (k := k)) (hd : ∑ i, (z i).1 = N)
    (hp : HasFiniteLength (prodIrr z hd)) (w : IrrGL (k := k)) (hw : clsGL (prodIrr z hd) hp w ≠ 0) :
    ∃ hc : ∑ i, (z i).1 = w.1, IsSubquotient w.rep (prodIrr z hc) := by
  obtain ⟨e, h1⟩ := occ_of_cls hp w hw
  subst e
  exact ⟨hd, h1 rfl⟩

end

open GlobalTheory.LocGL.SupportRing in
theorem UpperTheory.Lit.Full.prodStart :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ : IrrGL (k := k)) (h N : ℕ) (Δ : Fin h → Segment k) (z : Fin h → IrrGL (k := k)) (hd : ∑ i, (z i).1 = N), ρ.IsCusp → (∀ i, (Δ i).first = ρ) → (∀ i, IsZSeg (Δ i) (z i).rep) → (prodIrr z hd).IsIrreducible := by
  intro hG hBZ hZ k _ _ _ _ ρ h N Δ z hd hρ hf hz
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  obtain ⟨hp, ep⟩ := prodIrr_cls hΨ z hd
  obtain ⟨m, hm⟩ := prod_X_monomial Δ _ fun i => bas_of_isZSeg hS hX _ _ (hz i)
  have hF : ∀ i, FirstIn (z i) {ρ} := fun i => by
    rw [← hf i]
    exact (UpperTheory.Lit.Full.zfirst hG hBZ hZ k (Δ i)).2 (z i) (hz i)
  have key : ∀ w : IrrGL (k := k), clsGL (prodIrr z hd) hp w ≠ 0 →
      HasSupport w.rep (∑ i, (Δ i).ms) ∧ FirstIn w {ρ} := by
    intro w hw
    obtain ⟨hc, h1⟩ := occ_prodIrr z hd hp w hw
    exact ⟨hasSupport_of_isSubquotient_prodIrr hΨ (fun i => (hz i).hasSupport) w.2.rep.irr h1,
      UpperTheory.Lit.Full.firstProd hG hBZ k {ρ} h z w hc hF (jhMult_ne_zero_iff.2 h1)⟩
  have hup : ∀ y ∈ ∑ i, (Δ i).ms, y ∈ up ρ := by
    intro y hy
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hy
    obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hi)
    exact ⟨a, by rw [← ha, hf i]⟩
  obtain ⟨w, h1⟩ := eq_single_of_monomial Ψ _ m (ep.trans hm) (clsGL_nonneg _ hp) fun w x hw hx =>
    (UpperTheory.Lit.Full.redUnique hG hBZ hZ k ρ hρ _ hup w (key w hw).1 (key w hw).2).2 x (key x hx).1 (key x hx).2
  exact GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_of_clsGL_eq_single hp (isSmooth_prodIrr z hd) h1
end

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

namespace UpperTheory.Lit.Full.RedTimesZ

open GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in
private theorem two_unit_left {r t : ℕ} (e : t + r = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL (k := k))
    (hy : ∑ i, (y i).1 = t) : Iso (two e (pr y hy) A) A := by
  with_unfolding_all
    exact GlobalTheory.ProdReorder.ind₂_unit_left k r t e A.V A.ρ hA (fun i => (y i).1) (fun i => (y i).2.rep.V)
      (fun i => (y i).rep) (stdBlocks _ hy)

unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in
private theorem iso_one_pr {h : ℕ} {x : IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : Iso (pr y hy) (one x) := ⟨φ⟩

unseal one GlobalTheory.ProdFlatten.two mp pr Iso Sm in
private theorem equiv_of_iso {h c N : ℕ} {x : Fin c → IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hx : ∑ i, (x i).1 = N}
    {hy : ∑ i, (y i).1 = N} (H : Iso (pr x hx) (pr y hy)) : Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := H

private theorem pr_single {c : ℕ} {w : Fin c → IrrGL (k := k)} {z : IrrGL (k := k)} (hl : List.ofFn w = [z])
    (hw : ∑ i, (w i).1 = z.1) : Iso (pr w hw) (one z) := by
  have h0 : ∑ i : Fin 0, ((fun i => i.elim0 : Fin 0 → IrrGL (k := k)) i).1 = 0 := by simp
  exact iso_trans (pr_cons (x := fun i : Fin 0 => i.elim0) (by simpa using hl) h0 hw rfl)
    (two_unit_pr rfl _ (sm_one z) _ h0)

private theorem pr_snoc {h c r N : ℕ} (y : Fin h → IrrGL (k := k)) (z : IrrGL (k := k)) (w : Fin c → IrrGL (k := k))
    (hl : List.ofFn w = List.ofFn y ++ [z]) (hy : ∑ i, (y i).1 = r) (hw : ∑ i, (w i).1 = N) (e : r + z.1 = N) :
    Iso (pr w hw) (two e (pr y hy) (one z)) := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have hN : N = z.1 := by
      have : r = 0 := by simpa using hy.symm
      omega
    subst hN
    exact iso_trans (pr_single (by simpa using hl) hw) (iso_symm (two_unit_left e _ (sm_one z) y hy))
  · have h1 : ∑ i, (![z] i).1 = z.1 := by simp
    exact iso_trans (pr_append y ![z] w (by simpa using hl) (Or.inl hh.ne') hy h1 hw e)
      (two_congr e (iso_refl _) (pr_single (by simp) h1))

private theorem equiv_snoc {h N : ℕ} {x : IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) (z : IrrGL (k := k)) (hd : ∑ a, (![x, z] a).1 = N)
    (hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL (k := k)) i).1 = N) :
    Nonempty ((prodIrr (Fin.snoc y z : Fin (h + 1) → IrrGL (k := k)) hw).Equiv (prodIrr ![x, z] hd)) := by
  have e : x.1 + z.1 = N := by simpa using hd
  have h1 : ∑ i, (![z] i).1 = z.1 := by simp
  refine equiv_of_iso (iso_trans (pr_snoc y z _ (by rw [List.ofFn_succ']; simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]) hy hw e) ?_)
  refine iso_trans (two_congr e (iso_one_pr φ) (iso_symm (pr_single (w := ![z]) (by simp) h1))) ?_
  exact iso_symm (pr_cons (by simp) h1 hd e)

private theorem exists_class {h : ℕ} (y : Fin h → IrrGL (k := k)) (hirr : (prodIrr y rfl).IsIrreducible) :
    ∃ (x : IrrGL (k := k)) (hy : ∑ i, (y i).1 = x.1), Nonempty ((prodIrr y hy).Equiv x.rep) :=
  ⟨IrrGL.of (prodIrr y rfl) (isSmooth_prodIrr y rfl) hirr, rfl, ⟨IrrGL.equivOf _ _ _⟩⟩

private theorem irr_snoc {h N : ℕ} {x : IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) (z : IrrGL (k := k)) (hd : ∑ a, (![x, z] a).1 = N)
    (H : ∀ hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL (k := k)) i).1 = N,
      (prodIrr (Fin.snoc y z : Fin (h + 1) → IrrGL (k := k)) hw).IsIrreducible) :
    (prodIrr ![x, z] hd).IsIrreducible := by
  have hw : ∑ i, ((Fin.snoc y z : Fin (h + 1) → IrrGL (k := k)) i).1 = N := by
    rw [Fin.sum_univ_castSucc, ← hd]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.sum_univ_two, hy]
    rfl
  obtain ⟨ψ⟩ := equiv_snoc φ z hd hw
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv ψ (H hw)

private theorem isSubquotient_of_equiv {h : ℕ} {x : IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : IsSubquotient x.rep (prodIrr y hy) :=
  .of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective

private theorem jhMult_ne_zero {h : ℕ} {x : IrrGL (k := k)} {y : Fin h → IrrGL (k := k)} {hy : ∑ i, (y i).1 = x.1}
    (φ : (prodIrr y hy).Equiv x.rep) : jhMult x.rep (prodIrr y hy) ≠ 0 :=
  jhMult_ne_zero_iff.2 (isSubquotient_of_equiv φ)

private theorem snoc_rel {α β : Type*} (R : α → β → Prop) {h : ℕ} {D : Fin h → α} {y : Fin h → β} {a : α} {b : β}
    (H : ∀ i, R (D i) (y i)) (H' : R a b) (i : Fin (h + 1)) :
    R ((Fin.snoc D a : Fin (h + 1) → α) i) ((Fin.snoc y b : Fin (h + 1) → β) i) := by
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.snoc_last]; exact H'
  | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact H i

end UpperTheory.Lit.Full.RedTimesZ

open UpperTheory.Lit.Full.RedTimesZ in
theorem UpperTheory.Lit.Full.redTimesZ :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (x z : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, z] a).1 = N), SuppIn x (up Δ.first) → FirstIn x {Δ.first} → IsZSeg Δ z.rep → (prodIrr ![x, z] hd).IsIrreducible := by
  intro hG hB hZ k _ _ _ _ Δ x z N hd hs hf hz
  obtain ⟨T, hT, hup⟩ := hs
  obtain ⟨⟨𝔪, h𝔪, hfirst⟩, huniq⟩ := UpperTheory.Lit.Full.redUnique hG hB hZ k Δ.first Δ.isCusp_first T hup x hT hf
  obtain ⟨L, rfl⟩ := Quotient.exists_rep 𝔪
  let D : Fin L.length → Segment k := L.get
  have hD : ∀ i, (D i).first = Δ.first := fun i => hfirst _ (Multiset.mem_coe.2 (List.get_mem L i))
  have hsum : ∑ i, (D i).ms = T := by
    rw [← h𝔪, ← List.sum_ofFn]
    have : List.ofFn (fun i => (D i).ms) = L.map Segment.ms := by
      conv_rhs => rw [← List.ofFn_get L, List.map_ofFn]
      rfl
    rw [this]
    simp [msupp, Multiset.bind, Multiset.join]
  choose y hy using fun i => (UpperTheory.Lit.Full.zfirst hG hB hZ k (D i)).1
  have hirr : (prodIrr y rfl).IsIrreducible :=
    UpperTheory.Lit.Full.prodStart hG hB hZ k Δ.first _ _ D y rfl Δ.isCusp_first hD hy
  obtain ⟨x', hyx, ⟨φ⟩⟩ := exists_class y hirr
  have hx' : x' = x := by
    refine huniq x' ?_ ?_
    · rw [← hsum]
      exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (hd := hyx) (fun i => (hy i).hasSupport)
        x'.2.rep.irr (isSubquotient_of_equiv φ)
    · refine UpperTheory.Lit.Full.firstProd hG hB k _ _ y x' hyx
        (fun i => hD i ▸ (UpperTheory.Lit.Full.zfirst hG hB hZ k (D i)).2 _ (hy i)) ?_
      exact jhMult_ne_zero φ
  subst hx'
  refine irr_snoc φ z hd fun hw => ?_
  refine UpperTheory.Lit.Full.prodStart hG hB hZ k Δ.first _ _ (Fin.snoc D Δ) _ hw Δ.isCusp_first ?_
    (snoc_rel (fun (Γ : Segment k) (w : IrrGL (k := k)) => IsZSeg Γ w.rep) hy hz)
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simpa using hD i
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsCovByRelJacD
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.JacStagesExact GlobalTheory.ParIndExact GlobalTheory.CompanionTheory.Hypotheses₂.TD GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_covBy_relJacD {s : ℕ} {d t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] {Θ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hΘ : Θ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    (h : IsSubquotient Θ (relJacD e' ρ)) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ IsSubquotient Θ (relJacD e' (subQuot S T)) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  refine exists_covBy_of_split (fun (S T : Subrepresentation ρ) => IsSubquotient Θ (relJacD e' (subQuot S T)))
    ?_ ?_ ⊤ ⊥ bot_le ?_
  · rintro S ⟨R, f, hf⟩
    haveI := subsingleton_subQuot_self S
    haveI := Model.nontrivial_of_isIrreducible hΘ
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨⟨v, hv⟩, rfl⟩ := hf u
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain rfl : z = 0 := Subsingleton.elim _ _
    exact hu (map_zero f)
  · intro S M T hTM hMS hQ
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := ρ) hTM hMS
    refine isSubquotient_dichotomy (relJacMap e' ι) (relJacMap e' p) hΘ (fun x hx => ?_) hQ
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer (subQuot S M) (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := hex (v - v') (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')
  · obtain ⟨ι, hι⟩ := subQuot_top_bot ρ
    exact h.trans (isSubquotient_relJacD k s d t d' e' _ _ _ _ ((isSubquotient_subQuot _ _).isSmooth hρ)
      (.of_injective ι hι))

private theorem coarse (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} (t : Fin s → ℕ) (x : ∀ a, Fin (t a) → IrrGL (k := k)) (w : IrrGL (k := k))
    (hx : ∑ c : Fin (∑ a, t a), (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1 = w.1)
    (h : jm (fun c : Fin (∑ a, t a) => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) hx w.rep ≠ 0) :
    ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, ∃ ha : ∑ b, (x a b).1 = (σ a).1, jm (x a) ha (σ a).rep ≠ 0 := by
  classical
  let d : Fin s → ℕ := fun a => ∑ b, (x a b).1
  have hd : ∑ a, d a = w.1 := by
    rw [← hx, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (t a)) => (x p.1 p.2).1), Fintype.sum_sigma]
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  obtain ⟨φR⟩ := GlobalTheory.T.piExteriorTensor_flattenedIndex_equiv_nested s t (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep
  obtain ⟨φS⟩ := GlobalTheory.T.jacquetModule_in_stages_refined_blocks k s w.1 d e t (fun a b => (x a b).1) e' _ w.rep
  obtain ⟨φP⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (stdBlocks _ hx) (refinePlace e e') _).2 w.rep
  have hirr0 : (piTensor fun c : Fin (∑ a, t a) =>
      (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun c => (x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).2.rep
  have hirr1 := GlobalTheory.FinGL.Transport.isIrreducible_comp _
    (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0
  have hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1
  have h1 := (jhMult_ne_zero_iff.1 h).trans (isSubquotient_of_equiv φP)
  have h2 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e w.rep)) :=
    (isSubquotient_of_equiv φR.symm).trans ((SupportUnique.isSubquotient_comp h1
      (flatHom fun a b => GL (Fin ((x a b).1)) k)).trans (isSubquotient_of_equiv φS))
  have hsm := isSmooth_jac e w.2.rep.smooth
  obtain ⟨S, T, hST, h3⟩ := exists_covBy_relJacD e' hirr hsm
    ((hBZ k).2.1 _ _ _ e _ w.rep w.2.rep.smooth (hasFiniteLength_of_isIrreducible w.2.rep.irr)) h2
  have hτ := isIrreducible_subQuot hST
  obtain ⟨σ, hσ⟩ := GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac hG k w.1 (Irr.ofIrrRep w.2.rep) s d e _
    (subQuot S T) hτ (isSubquotient_subQuot S T)
  let σ' : Fin s → IrrGL (k := k) := fun a => IrrGL.of (σ a).π (σ a).smooth (σ a).irr
  have hσi : (piTensor fun a => (σ' a).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (σ' a).2.rep
  have hσs : IsSmooth (piTensor fun a => (σ' a).rep) := isSmooth_piTensor fun a => (σ' a).2.rep.smooth
  have h4 : IsSubquotient (subQuot S T) (piTensor fun a => (σ' a).rep) :=
    hσ.trans (GlobalTheory.piTensor_isSubquotient_of_forall _ _ _ _ _ _ fun a =>
      isSubquotient_of_equiv (IrrGL.equivOf (σ a).π (σ a).smooth (σ a).irr))
  obtain ⟨ψ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient hτ hσi h4
  refine ⟨σ', hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv ψ).trans (isSubquotient_subQuot S T)),
    fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩
  obtain ⟨φT⟩ := GlobalTheory.T.relativeJacquet_piExteriorTensor_equiv_normalized k s d t (fun a b => (x a b).1) e' _ fun a => (σ' a).rep
  have h5 := h3.trans ((isSubquotient_relJacD k s d t _ e' _ _ _ _ hσs h4).trans (isSubquotient_of_equiv φT))
  have hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible := fun a =>
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun b => (x a b).2.rep
  exact SupportUnique.isSubquotient_factor (fun a => jac (e' a) (σ' a).rep) a (hi a)
    ((isSubquotient_comp_mulSingle (fun a => piTensor fun b => (x a b).rep) hi a).trans
      (SupportUnique.isSubquotient_comp h5 _))

private theorem supp_jm (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s : ℕ} {y : Fin s → IrrGL (k := k)} {w : IrrGL (k := k)} {hy : ∑ a, (y a).1 = w.1} (h : jm y hy w.rep ≠ 0)
    {A : Multiset (IrrGL (k := k))} (hA : HasSupport w.rep A) {T : Fin s → Multiset (IrrGL (k := k))}
    (hT : ∀ a, HasSupport (y a).rep (T a)) : A = ∑ a, T a := by
  obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hA (stdBlocks (fun a => (y a).1) hy)
    (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun a => (y a).2.rep) (jhMult_ne_zero_iff.1 h) (fun a => (y a).2.rep)
    (fun a => isSubquotient_comp_mulSingle (fun a => (y a).rep) (fun a => (y a).2.rep.irr) a)
  exact Finset.sum_congr rfl fun a _ => hasSupport_unique hG hBZ (hu a) (hT a)

private theorem jm_cast {L L' : ℕ} (hL : L = L') (y : Fin L' → IrrGL (k := k)) (z : Fin L → IrrGL (k := k))
    (hz : ∀ c, z c = y (Fin.cast hL c)) (w : IrrGL (k := k)) (hy : ∑ a, (y a).1 = w.1) (h : jm y hy w.rep ≠ 0) :
    ∃ hz : ∑ a, (z a).1 = w.1, jm z hz w.rep ≠ 0 := by
  subst hL
  obtain rfl : z = y := funext hz
  exact ⟨hy, h⟩

private theorem merge (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {s L : ℕ} (t : Fin s → ℕ) (hL : ∑ a, t a = L) {y : Fin L → IrrGL (k := k)} {w : IrrGL (k := k)} {hy : ∑ a, (y a).1 = w.1}
    (h : jm y hy w.rep ≠ 0) {T : Fin L → Multiset (IrrGL (k := k))} (hT : ∀ a, HasSupport (y a).rep (T a)) :
    ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = w.1), jm σ hσ w.rep ≠ 0 ∧
      ∀ a, HasSupport (σ a).rep (∑ b, T (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))) := by
  let x : ∀ a, Fin (t a) → IrrGL (k := k) := fun a b => y (Fin.cast hL (finSigmaFinEquiv ⟨a, b⟩))
  obtain ⟨hx, h1⟩ := jm_cast hL y (fun c => x (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)
    (fun c => by simp [x]) w hy h
  obtain ⟨σ, hσ, h2, h3⟩ := coarse hG hBZ t x w hx h1
  refine ⟨σ, hσ, h2, fun a => ?_⟩
  obtain ⟨ha, h4⟩ := h3 a
  obtain ⟨A, hA⟩ := exists_hasSupport hBZ hG (σ a)
  rw [← supp_jm hG hBZ h4 hA fun b => hT _]
  exact hA

private theorem deg_eq_zero {y : IrrGL (k := k)} {A : Multiset (IrrGL (k := k))} (hA : HasSupport y.rep A) (h0 : A = 0) :
    y.1 = 0 := by
  have h := hA.sum_fst
  rw [h0] at h
  simpa using h.symm

private theorem offdiag (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {J : Set (IrrGL (k := k))} {ρ : IrrGL (k := k)} {w : Fin 3 → IrrGL (k := k)} (h0 : LastIn (w 0) Jᶜ) (h1 : SuppIn (w 1) (J \ {ρ}))
    (h2 : SuppIn (w 2) J) (h3 : FirstIn (w 2) {ρ}) (y : Fin 3 → Fin 3 → IrrGL (k := k))
    (hr : ∀ i, ∑ j, (y i j).1 = (w i).1) (hc : ∀ j, ∑ i, (y i j).1 = (w j).1)
    (hrow : ∀ i, jm (y i) (hr i) (w i).rep ≠ 0)
    (hcol : ∀ j, jhMult (w j).rep (prodIrr (fun i => y i j) (hc j)) ≠ 0) :
    ∀ i j, j ≠ i → (y i j).1 = 0 := by
  choose T hT using fun i j => exists_hasSupport hBZ hG (y i j)
  have hC : ∀ j, HasSupport (w j).rep (∑ i, T i j) := fun j =>
    hasSupport_of_isSubquotient_prodIrr (fun i => hT i j) (w j).2.rep.irr (jhMult_ne_zero_iff.1 (hcol j))
  obtain ⟨A1, hA1, m1⟩ := h1
  obtain ⟨A2, hA2, m2⟩ := h2
  obtain rfl := hasSupport_unique hG hBZ hA1 (hC 1)
  obtain rfl := hasSupport_unique hG hBZ hA2 (hC 2)
  simp only [Fin.sum_univ_three, Multiset.mem_add] at m1 m2
  have e0 : T 0 1 + T 0 2 = 0 := by
    obtain ⟨σ, hσ, j1, j2⟩ := merge hG hBZ (![1, 2] : Fin 2 → ℕ) (by simp) (hrow 0) (hT 0)
    have j3 : HasSupport (σ 1).rep (T 0 1 + T 0 2) := by
      have := j2 1
      change HasSupport (σ 1).rep (∑ b : Fin 2, _) at this
      rw [Fin.sum_univ_two] at this
      exact this
    rcases Nat.eq_zero_or_pos (σ 1).1 with hz | hp
    · exact SupportUnique.eq_zero_of_hasSupport hz j3
    · obtain ⟨A, hA, z, hz, hzJ⟩ := (UpperTheory.Lit.Full.piece hG hBZ k (w 0) Jᶜ σ hσ j1).2 h0 hp
      obtain rfl := hasSupport_unique hG hBZ hA j3
      rcases Multiset.mem_add.1 hz with hz | hz
      · exact absurd (m1 z (Or.inl (Or.inl hz))).1 hzJ
      · exact absurd (m2 z (Or.inl (Or.inl hz))) hzJ
  have d01 := deg_eq_zero (hT 0 1) (add_eq_zero.1 e0).1
  have d02 := deg_eq_zero (hT 0 2) (add_eq_zero.1 e0).2
  have r0 := hr 0
  have r1 := hr 1
  have r2 := hr 2
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  simp only [Fin.sum_univ_three] at r0 r1 r2 c0 c1 c2
  have d10 : (y 1 0).1 = 0 := by omega
  have d20 : (y 2 0).1 = 0 := by omega
  have t20 : T 2 0 = 0 := SupportUnique.eq_zero_of_hasSupport d20 (hT 2 0)
  have e2 : T 2 1 = 0 := by
    obtain ⟨σ, hσ, j1, j2⟩ := merge hG hBZ (![2, 1] : Fin 2 → ℕ) (by simp) (hrow 2) (hT 2)
    have j3 : HasSupport (σ 0).rep (T 2 0 + T 2 1) := by
      have := j2 0
      change HasSupport (σ 0).rep (∑ b : Fin 2, _) at this
      rw [Fin.sum_univ_two] at this
      exact this
    rw [t20, zero_add] at j3
    rcases Nat.eq_zero_or_pos (σ 0).1 with hz | hp
    · exact SupportUnique.eq_zero_of_hasSupport hz j3
    · obtain ⟨A, hA, z, hz, hzJ⟩ := (UpperTheory.Lit.Full.piece hG hBZ k (w 2) {ρ} σ hσ j1).1 h3 hp
      obtain rfl := hasSupport_unique hG hBZ hA j3
      exact absurd hzJ (m1 z (Or.inr hz)).2
  have d21 := deg_eq_zero (hT 2 1) e2
  have d12 : (y 1 2).1 = 0 := by omega
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem multiProd_placing {h N : ℕ} {d : Fin h → ℕ} (e e' : (Σ i, Fin (d i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (d i)) k)) :
    IsSubquotient (multiProd e fun i => (s i).ρ) (multiProd e' fun i => (s i).ρ) := by
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e e' _).1 (piTensor fun i => (s i).ρ)
  exact isSubquotient_of_equiv φ


set_option maxHeartbeats 1000000 in
private theorem cell (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {h : ℕ} (w : Fin h → IrrGL (k := k)) {b : Fin h → Fin h → ℕ} (hr : ∀ i, ∑ j, b i j = (w i).1)
    (hc : ∀ j, ∑ i, b i j = (w j).1) (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (w i).1)
    (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (w j).1)
    (hne : jhMult (piTensor fun j => (w j).rep) (cellFunctor f g (piTensor fun i => (w i).rep)) ≠ 0) :
    ∃ s : ∀ i j, IrrCl (GL (Fin (b i j)) k),
      (∀ i, jm (fun j => (⟨b i j, s i j⟩ : IrrGL (k := k))) (hr i) (w i).rep ≠ 0) ∧
        ∀ j, jhMult (w j).rep (prodIrr (fun i => (⟨b i j, s i j⟩ : IrrGL (k := k))) (hc j)) ≠ 0 := by
  have hτ : (piTensor fun j => (w j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep
  have hρ : IsSmooth (piTensor fun i => (w i).rep) := isSmooth_piTensor fun i => (w i).2.rep.smooth
  obtain ⟨T, -, hT⟩ := (hG k).2 (Fin h) (Fin h) (fun i => Fin (w i).1) (fun i => Fin (w i).1) _ f g _
    (fun i => (w i).rep) (fun i => (w i).2.rep.smooth) (fun i => hasFiniteLength_of_isIrreducible (w i).2.rep.irr)
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (fun e => hne ((hT ⟨_, _, hρ, hτ⟩).trans e))
  refine ⟨s, fun i => ?_, fun j => ?_⟩
  · obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (f i)
      (stdBlocks (fun j => b i j) (hr i)) _).2 (w i).rep
    have k1 : IsSubquotient (piTensor fun j => (s i j).rep.ρ) (jac (f i) (w i).rep) := jhMult_ne_zero_iff.1
      (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i))
    have k2 := jhMult_ne_zero_iff.2 (k1.trans (isSubquotient_of_equiv φ))
    exact k2
  · have k2 : IsSubquotient (piTensor fun j => (w j).rep)
        (piTensor fun j => multiProd (g j) fun i => (s i j).rep.ρ) :=
      jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)
    have k3 := (isSubquotient_comp_mulSingle (fun j => (w j).rep) (fun j => (w j).2.rep.irr) j).trans
      (SupportUnique.isSubquotient_comp k2 (MonoidHom.mulSingle (fun j => GL (Fin (w j).1) k) j))
    have k4 : IsSubquotient (w j).rep (multiProd (g j) fun i => (s i j).rep.ρ) := SupportUnique.isSubquotient_factor
      (fun j => multiProd (g j) fun i => (s i j).rep.ρ) j (w j).2.rep.irr k3
    have k5 : IsSubquotient (multiProd (g j) fun i => (s i j).rep.ρ)
        (multiProd (stdBlocks (fun i => b i j) (hc j)) fun i => (s i j).rep.ρ) :=
      multiProd_placing (g j) _ fun i => (s i j).rep
    have k6 := jhMult_ne_zero_iff.2 (k4.trans k5)
    exact k6

end SlopeTestRemainingChoices

theorem UpperTheory.Lit.Full.diag3 :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (J : Set (IrrGL (k := k))) (ρ : IrrGL (k := k)) (w : Fin 3 → IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (w a).1 = N), LastIn (w 0) Jᶜ → SuppIn (w 1) (J \ {ρ}) → SuppIn (w 2) J → FirstIn (w 2) {ρ} → jm w hd (prodIrr w hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ J ρ w N hd h0 h1 h2 h3
  classical
  let M := fun i : Fin 3 => Fin (w i).1
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then (w i).1 else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hτ : (piTensor fun j => (w j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (w j).2.rep
  have hρ : IsSmooth (piTensor fun i => (w i).rep) := isSmooth_piTensor fun i => (w i).2.rep.smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have hsum := (hG k).1.jhMult_eq (m := M) (m' := M) (stdBlocks (fun a => (w a).1) hd)
    (stdBlocks (fun a => (w a).1) hd) hρ f g hτ
  refine (show jm w hd (prodIrr w hd) = _ from hsum).trans_le ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult (piTensor fun i => (w i).rep) (cellFunctor f' g' (piTensor fun i => (w i).rep)) ≤ 1 := by
      rintro _ _ rfl rfl
      exact ((jhMult_congr_right _ E₀).trans (jhMult_self hτ)).le
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    have hr : ∀ i, ∑ j, b.1 i j = (w i).1 := fun i => (b.2.1 i).trans (Fintype.card_fin _)
    have hc : ∀ j, ∑ i, b.1 i j = (w j).1 := fun j => (b.2.2 j).trans (Fintype.card_fin _)
    obtain ⟨s, hrow, hcol⟩ := cell hG hBZ w hr hc (f b) (g b) hne
    have hz : ∀ i j, j ≠ i → b.1 i j = 0 :=
      offdiag hG hBZ h0 h1 h2 h3 (fun i j => ⟨b.1 i j, s i j⟩) hr hc hrow hcol
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    by_cases hij : i = j
    · subst hij
      have r := hr i
      rw [Finset.sum_eq_single i (fun j _ hj => hz i j hj) (by simp)] at r
      exact r.trans (if_pos rfl).symm
    · exact (hz i j (Ne.symm hij)).trans (if_neg hij).symm
  · simp
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FSsEmb
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem exists_compl_of_admissible {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hbasis : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hs : IsSmooth ρ) (hun : IsUnitarisable ρ) (W : Subrepresentation ρ) (hW : IsAdmissible W.toRepresentation) :
    ∃ W' : Subrepresentation ρ, (∀ v, v ∈ W.toSubmodule → v ∈ W'.toSubmodule → v = 0) ∧
      ∀ v, ∃ w ∈ W.toSubmodule, v - w ∈ W'.toSubmodule := by
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨GlobalTheory.CompanionTheory.UnitSemisimple.orth ρ B hi W, fun v hv hv' => ?_, fun v => ?_⟩
  · by_contra hv0
    have h0 : B v v = 0 := hv' v hv
    simpa [h0] using hp v hv0
  · obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hs v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed W.toRepresentation K) := hW.2 K hKo hKc
    have hmap : (fixed W.toRepresentation K).map W.toSubmodule.subtype = W.toSubmodule ⊓ fixed ρ K := by
      ext u
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u.2, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K _).2 fun g hg => ?_⟩
        exact congrArg Subtype.val ((GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff _ K u).1 hu g hg)
      · rintro ⟨h1, h2⟩
        refine ⟨⟨u, h1⟩, (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff _ K _).2 fun g hg => ?_, rfl⟩
        exact Subtype.ext ((GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K u).1 h2 g hg)
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := by
      rw [← hmap]
      exact (Module.Finite.iff_fg.1 hfd).map _
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := GlobalTheory.CompanionTheory.UnitSemisimple.exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (GlobalTheory.CompanionTheory.UnitSemisimple.mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    exact ⟨w, hw.1, fun y hy =>
      GlobalTheory.CompanionTheory.UnitSemisimple.orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hs y)⟩

private theorem isIrreducible_of_occurs (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s N : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible)
    (π : Representation ℂ (GL (Fin N) k) V) [Nontrivial V] (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (hun : IsUnitarisable π)
    (hone : ∀ (T : Subrepresentation π) (v : V), v ∈ T.toSubmodule → v ≠ 0 →
      1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : π.IsIrreducible := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hSs : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs
  have hSa : IsAdmissible S.toRepresentation :=
    (hBZ k).1 _ _ _ hSs (GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS)
  have hS1 : 1 ≤ jhMult ρ (jac e S.toRepresentation) := by
    by_contra hc
    refine hS.1 (le_antisymm (fun v hv => ?_) bot_le)
    by_contra hv0
    exact hc (hone S v hv hv0)
  obtain ⟨T, hST, hsum⟩ := exists_compl_of_admissible π
    (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k N) hs hun S hSa
  have hT : ∀ v ∈ T.toSubmodule, v = 0 := by
    intro v hv
    by_contra hv0
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      exact Subtype.ext (hST _ ((hp0 _).1 hu) u.2)
    have h1 : 1 ≤ jhMult ρ (jac e T.toRepresentation) :=
      hone T v hv hv0
    have h2 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S)) :=
      h1.trans (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have h3 : (2 : ℕ∞) ≤ jhMult ρ (jac e π) := by
      rw [GlobalTheory.CompanionTheory.SocleJm.jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans
        (add_le_add hS1 h2)
    exact absurd (h3.trans hjm) (by norm_num)
  have htop : S = ⊤ := by
    refine le_antisymm le_top fun v _ => ?_
    obtain ⟨w, hw, h⟩ := hsum v
    rw [sub_eq_zero.1 (hT _ h)]
    exact hw
  rw [htop] at hS
  exact isSimpleOrder_iff_isAtom_top.2 hS

private theorem isIrreducible_parInd_emb (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {k : Type} [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s s' N : ℕ} {d : Fin s → ℕ}
    {d' : Fin s' → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (e' : (Σ a, Fin (d' a)) ≃ Fin N) {X X' : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup X'] [Module ℂ X']
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) X} (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ)
    {σ : Representation ℂ (Levi k fun a => Fin (d' a)) X'} (hσ : σ.IsIrreducible)
    (hun : IsUnitarisable (parInd e ρ)) (f : (parInd e ρ).IntertwiningMap (parInd e' σ))
    (hf : Function.Injective f) (hjm : jhMult σ (jac e' (parInd e' σ)) ≤ 1) :
    (parInd e ρ).IsIrreducible := by
  haveI := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp e hρ hsρ
  have hsw : IsSmooth (parInd e' σ) := isSmooth_parInd _ _
  refine isIrreducible_of_occurs hBZ e' hσ (parInd e ρ) (isSmooth_parInd _ _)
    ((hBZ k).2.2.1 _ _ _ e _ ρ hsρ (hasFiniteLength_of_isIrreducible hρ)) hun (fun T v hv hv0 => ?_) ?_
  · let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    exact GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e' hσ (f.comp ιT)
      ⟨⟨v, hv⟩, fun h0 => hv0 (hf (h0.trans (map_zero f).symm))⟩
  · exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hσ (jacMap e' f)
      (GlobalTheory.JacInj.jacMap_injective k _ _ _ e' _ _ _ _ _ hsw hf)).trans hjm

theorem UpperTheory.Lit.Full.ssEmb :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x y : IrrGL (k := k)) (N h : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (w : Fin h → IrrGL (k := k)) (hw : ∑ a, (w a).1 = N), IsUnitarisable x.rep → IsUnitarisable y.rep → (∃ f : (prodIrr ![x, y] hd).IntertwiningMap (prodIrr w hw), Function.Injective f) → jm w hw (prodIrr w hw) ≤ 1 → (prodIrr ![x, y] hd).IsIrreducible := by
  intro hBZ k _ _ _ _ x y N h hd w hw hx hy hf hjm
  obtain ⟨f, hf⟩ := hf
  have hρ : (piTensor fun a => (![x, y] a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) ![x, y]
  have hsρ : IsSmooth (piTensor fun a => (![x, y] a).rep) := isSmooth_piTensor fun a => (![x, y] a).2.rep.smooth
  have hσ : (piTensor fun a => (w a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor (fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π) w
  have hu : ∀ a, IsUnitarisable (![x, y] a).rep := fun a => by
    fin_cases a
    · exact hx
    · exact hy
  exact isIrreducible_parInd_emb hBZ _ _ hρ hsρ hσ (GlobalTheory.SmGL.UnitInd.isUnitarisable_multiProd _ hu) f hf hjm
end

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

open GlobalTheory.Parabolic (Embeds)
open GlobalTheory.ProdFlatten

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem embeds_ind₂ {r t N : ℕ} (e : r + t = N) {U U' W W' : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (h : Embeds σ σ') (h' : Embeds ρ ρ') :
    Embeds (ind₂ (stdSum e) (extTensor σ ρ)) (ind₂ (stdSum e) (extTensor σ' ρ')) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  obtain ⟨ι, hι⟩ := GlobalTheory.ParIndExact.extTensor_injective_left ρ f hf
  obtain ⟨κ, hκ⟩ := GlobalTheory.ParIndExact.extTensor_injective_right σ' g hg
  have h1 : Function.Injective (compMap (κ.comp ι) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hκ.comp hι
  exact ⟨parIndMap (GlobalTheory.SmGL.two (stdSum e)) (compMap (κ.comp ι) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ h1⟩

private def EB {n : ℕ} (A C : BR k n) : Prop := Embeds A.ρ C.ρ

private theorem EB.trans {n : ℕ} {A C D : BR k n} (h : EB A C) (h' : EB C D) : EB A D := Embeds.trans h h'

unseal GlobalTheory.ProdFlatten.Iso in
private theorem EB.of_iso {n : ℕ} {A C : BR k n} (h : Iso A C) : EB A C :=
  Nonempty.elim h fun φ => Embeds.of_equiv φ

unseal GlobalTheory.ProdFlatten.two in
private theorem EB.two {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : EB A A') (h' : EB C C') :
    EB (GlobalTheory.ProdFlatten.two e A C) (GlobalTheory.ProdFlatten.two e A' C') :=
  embeds_ind₂ e (σ := A.ρ) (σ' := A'.ρ) (ρ := C.ρ) (ρ' := C'.ρ) h h'

unseal GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.one in
private theorem EB_pr {p q N : ℕ} {x : Fin p → IrrGL (k := k)} {y : Fin q → IrrGL (k := k)} (hx : ∑ a, (x a).1 = N)
    (hy : ∑ a, (y a).1 = N) : EB (pr x hx) (pr y hy) ↔ Embeds (prodIrr x hx) (prodIrr y hy) := Iff.rfl

attribute [irreducible] EB

private def PE {p q : ℕ} (x : Fin p → IrrGL (k := k)) (y : Fin q → IrrGL (k := k)) : Prop :=
  ∑ a, (x a).1 = ∑ a, (y a).1 ∧
    ∀ (N : ℕ) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N), EB (pr x hx) (pr y hy)

private theorem PE.refl {p : ℕ} (x : Fin p → IrrGL (k := k)) : PE x x :=
  ⟨rfl, fun _ _ _ => .of_iso (iso_refl _)⟩

private theorem PE.trans {p q r : ℕ} {x : Fin p → IrrGL (k := k)} {y : Fin q → IrrGL (k := k)} {z : Fin r → IrrGL (k := k)}
    (h : PE x y) (h' : PE y z) : PE x z :=
  ⟨h.1.trans h'.1, fun N hx hz => (h.2 N hx (h.1.symm.trans hx)).trans (h'.2 N _ hz)⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
private theorem sum_of_ofFn {p q c : ℕ} {x : Fin p → IrrGL (k := k)} {y : Fin q → IrrGL (k := k)} {w : Fin c → IrrGL (k := k)}
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) : ∑ a, (w a).1 = ∑ a, (x a).1 + ∑ a, (y a).1 := by
  have := congrArg (fun l => (l.map Sigma.fst).sum) hw
  simpa [List.map_ofFn, List.sum_ofFn] using this

private theorem PE.glue {p q c p' q' c' : ℕ} {x : Fin (p + 1) → IrrGL (k := k)} {y : Fin q → IrrGL (k := k)} {w : Fin c → IrrGL (k := k)}
    {x' : Fin (p' + 1) → IrrGL (k := k)} {y' : Fin q' → IrrGL (k := k)} {w' : Fin c' → IrrGL (k := k)} (h : PE x x') (h' : PE y y')
    (hw : List.ofFn w = List.ofFn x ++ List.ofFn y) (hw' : List.ofFn w' = List.ofFn x' ++ List.ofFn y') :
    PE w w' := by
  have s := sum_of_ofFn hw
  have s' := sum_of_ofFn hw'
  refine ⟨by rw [s, s', h.1, h'.1], fun N hx hy => ?_⟩
  have e : ∑ a, (x a).1 + ∑ a, (y a).1 = N := s.symm.trans hx
  have E := pr_append x y w hw (Or.inl p.succ_ne_zero) rfl rfl hx e
  have E' := pr_append x' y' w' hw' (Or.inl p'.succ_ne_zero) h.1.symm h'.1.symm hy e
  exact ((EB.of_iso E).trans (EB.two e (h.2 _ rfl h.1.symm) (h'.2 _ rfl h'.1.symm))).trans (.of_iso (iso_symm E'))

private theorem PE.of_embeds {c : ℕ} {x : IrrGL (k := k)} {w : Fin c → IrrGL (k := k)} (hd : ∑ a, (w a).1 = x.1)
    (hf : Embeds x.rep (prodIrr w hd)) : PE (fun _ : Fin 1 => x) w := by
  have h1 : ∑ _ : Fin 1, x.1 = x.1 := by simp
  refine ⟨h1.trans hd.symm, fun N hx hy => ?_⟩
  obtain rfl : x.1 = N := h1.symm.trans hx
  have φ := (nonempty_equiv_prodIrr_one x hx).some
  exact (EB_pr _ _).2 ((Embeds.of_equiv φ.symm).trans hf)

private theorem PE.of_embeds' {c : ℕ} {x : IrrGL (k := k)} {w : Fin c → IrrGL (k := k)} (hd : ∑ a, (w a).1 = x.1)
    (hf : Embeds (prodIrr w hd) x.rep) : PE w (fun _ : Fin 1 => x) := by
  have h1 : ∑ _ : Fin 1, x.1 = x.1 := by simp
  refine ⟨hd.trans h1.symm, fun N hy hx => ?_⟩
  obtain rfl : x.1 = N := h1.symm.trans hx
  have φ := (nonempty_equiv_prodIrr_one x hx).some
  exact (EB_pr _ _).2 (hf.trans (Embeds.of_equiv φ))

private theorem PE.of_emb {x y z : IrrGL (k := k)} (h : Emb x y z) : PE (fun _ : Fin 1 => x) ![y, z] :=
  h.elim fun hd hf => PE.of_embeds hd hf

private theorem exists_cls {c : ℕ} (w : Fin c → IrrGL (k := k)) (hi : (prodIrr w rfl).IsIrreducible) :
    ∃ (x : IrrGL (k := k)) (hd : ∑ a, (w a).1 = x.1), Embeds (prodIrr w hd) x.rep ∧ IsSubquotient x.rep (prodIrr w hd) := by
  have φ := IrrGL.equivOf (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi
  exact ⟨IrrGL.of (prodIrr w rfl) (isSmooth_prodIrr w rfl) hi, rfl, .of_equiv φ,
    .of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective⟩

private theorem supp_pair {x y z : IrrGL (k := k)} {A B : Multiset (IrrGL (k := k))} (hA : HasSupport y.rep A)
    (hB : HasSupport z.rep B) (hd : ∑ a, (![y, z] a).1 = x.1) (h : IsSubquotient x.rep (prodIrr ![y, z] hd)) :
    HasSupport x.rep (A + B) := by
  have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, z]) (hd := hd) (t := ![A, B])
    (Fin.forall_fin_two.2 ⟨hA, hB⟩) x.2.rep.irr h
  rwa [Fin.sum_univ_two] at this

private theorem Emb_sub {x y z : IrrGL (k := k)} (h : Emb x y z) :
    ∃ hd : ∑ a, (![y, z] a).1 = x.1, IsSubquotient x.rep (prodIrr ![y, z] hd) :=
  h.elim fun hd hf => ⟨hd, hf.elim fun f hf => .of_injective f hf⟩

private theorem PE.chain {x z x₁ s x₂ p x₃ : IrrGL (k := k)} (e1 : Emb x x₁ s) (e2 : Emb s x₂ p)
    (e3 : PE ![p, z] (fun _ : Fin 1 => x₃)) : PE ![x, z] ![x₁, x₂, x₃] := by
  have a1 : PE ![x, z] ![x₁, s, z] := (PE.of_emb e1).glue (PE.refl ![z]) (by simp) (by simp)
  have a2 : PE ![s, z] ![x₂, p, z] := (PE.of_emb e2).glue (PE.refl ![z]) (by simp) (by simp)
  have a3 : PE ![x₁, s, z] ![x₁, x₂, p, z] := (PE.refl ![x₁]).glue a2 (by simp) (by simp)
  have a4 : PE ![x₁, x₂, p, z] ![x₁, x₂, x₃] := (PE.refl ![x₁, x₂]).glue e3 (by simp) (by simp)
  exact (a1.trans a3).trans a4

end

theorem UpperTheory.Lit.Full.topZ :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (x z : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![x, z] a).1 = N), IsUnitarisable x.rep → IsUnitarisable z.rep → IsZSeg Δ z.rep → (prodIrr ![x, z] hd).IsIrreducible := by
  intro hG hB hZ k _ _ _ _ Δ x z N hd hx hz hΔ
  have d1 := UpperTheory.Lit.Full.decompR hG hB k x (up Δ.first)
  obtain ⟨x₁, s, e1, l1, As, hAs, hAJ⟩ := d1
  have d2 := UpperTheory.Lit.Full.decompL hG hB k s {Δ.first}ᶜ
  obtain ⟨x₂, p, e2, ⟨A₂, hA₂, hA₂P⟩, fp⟩ := d2
  rw [compl_compl] at fp
  have d3 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hB hG p
  obtain ⟨Ap, hAp⟩ := d3
  have hsum : As = A₂ + Ap :=
    (Emb_sub e2).elim fun hd2 hs => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hB hAs (supp_pair hA₂ hAp hd2 hs)
  have hp : ∀ y ∈ Ap, y ∈ up Δ.first := fun y hy => hAJ y (by rw [hsum]; exact Multiset.mem_add.2 (Or.inr hy))
  have h2 : SuppIn x₂ (up Δ.first \ {Δ.first}) :=
    ⟨A₂, hA₂, fun y hy => ⟨hAJ y (by rw [hsum]; exact Multiset.mem_add.2 (Or.inl hy)), hA₂P y hy⟩⟩
  have hi := UpperTheory.Lit.Full.redTimesZ hG hB hZ k Δ p z _ rfl ⟨Ap, hAp, hp⟩ fp hΔ
  refine (exists_cls ![p, z] hi).elim fun x₃ H => H.elim fun hd3 H => ?_
  have h3 : SuppIn x₃ (up Δ.first) := by
    refine ⟨_, supp_pair hAp hΔ.hasSupport hd3 H.2, fun y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · exact hp y hy
    · obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hy)
      exact ⟨a, ha.symm⟩
  have f3 : FirstIn x₃ {Δ.first} :=
    UpperTheory.Lit.Full.firstProd hG hB k {Δ.first} 2 ![p, z] x₃ hd3
      (Fin.forall_fin_two.2 ⟨fp, (UpperTheory.Lit.Full.zfirst hG hB hZ k Δ).2 z hΔ⟩) (jhMult_ne_zero_iff.2 H.2)
  have a := PE.chain e1 e2 (PE.of_embeds' hd3 H.1)
  have hw : ∑ i, (![x₁, x₂, x₃] i).1 = N := a.1.symm.trans hd
  exact UpperTheory.Lit.Full.ssEmb hB k x z N 3 hd _ hw hx hz ((EB_pr hd hw).1 (a.2 N hd hw))
    (UpperTheory.Lit.Full.diag3 hG hB k (up Δ.first) Δ.first _ N hw l1 h2 h3 f3)
end

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem isZSeg_detRep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V] {n l : ℕ} {χ ψ : kˣ →* ℂˣ}
    {hχ : IsSmoothChar χ} {hl : 0 < l} {π : Representation ℂ (GL (Fin n) k) V}
    (h : IsZSeg (Segment.ofChar χ hχ l hl) π) (hc : χ * absPow k (((l : ℂ) - 1) / 2) = ψ) :
    IsZSeg (Segment.ofChar χ hχ l hl) (detRep (Fin l) ψ) := by
  have hn : l * 1 = n := h.deg_eq
  rw [mul_one] at hn
  subst hn hc
  obtain ⟨φ⟩ := IsZSeg.equiv_detRep h
  exact h.of_equiv φ.symm

theorem UpperTheory.Lit.Full.top :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ), IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmoothChar χ → IsUnitaryChar χ → (prod₂ σ (detRep (Fin t) χ)).IsIrreducible := by
  intro hG hBZ hZ k _ _ _ _ r t V _ _ σ χ s₁ i₁ u₁ hχ hu
  have s₂ : IsSmooth (detRep (Fin t) χ) := (isSmooth_ofChar_iff _).2 hχ.detChar
  have i₂ : (detRep (Fin t) χ).IsIrreducible := isIrreducible_ofChar _
  have u₂ : IsUnitarisable (detRep (Fin t) χ) := (isUnitarisable_ofChar_iff _).2 fun _ => hu _
  have hd : ∑ a, (![IrrGL.of σ s₁ i₁, IrrGL.of (detRep (Fin t) χ) s₂ i₂] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ s₁ i₁ (detRep (Fin t) χ) s₂ i₂ hd
  have φ₁ := IrrGL.equivOf σ s₁ i₁
  have φ₂ := IrrGL.equivOf (detRep (Fin t) χ) s₂ i₂
  have v₁ := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₁ u₁
  have v₂ := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₂ u₂
  refine GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine UpperTheory.Lit.Mix.ss hBZ k _ _ _ hd v₁ v₂
      (UpperTheory.Lit.Mix.cellone hG hBZ k _ _ _ hd fun q hq h0 _ _ _ => ?_)
    have h1 : (q 0).1 + (q 1).1 = 0 := (Fin.sum_univ_two fun a => (q a).1).symm.trans hq
    omega
  · have hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
    have hc : χ * absPow k (-((t : ℂ) - 1) / 2) * absPow k (((t : ℂ) - 1) / 2) = χ := by
      rw [mul_assoc, ← absPow_add, show -((t : ℂ) - 1) / 2 + ((t : ℂ) - 1) / 2 = 0 by ring, absPow_zero, mul_one]
    obtain ⟨z, hz⟩ := (UpperTheory.Lit.Full.zfirst hG hBZ hZ k (Segment.ofChar _ hχ' t ht)).1
    exact UpperTheory.Lit.Full.topZ hG hBZ hZ k _ _ _ _ hd v₁ v₂ ((isZSeg_detRep hz hc).of_equiv φ₂)
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace UpperTheory.Lit.Mix

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_unconditional

theorem polynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation
    (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mixed {r : ℕ} (t : ℕ) {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  UpperTheory.Lit.Full.top geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds polynomialRing k r t V π χ s i u hs hu

theorem prod₂_detRep' (_H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible := mixed t s i u hs hu

end UpperTheory.Lit.Mix

end
