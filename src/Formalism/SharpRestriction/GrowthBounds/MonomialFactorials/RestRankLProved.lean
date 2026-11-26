module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.StructureSheafH2BaseChange

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime]

theorem finrank_zp_le {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (M : Submodule ℤ_[p] V) (W : Submodule ℚ_[p] V) [FiniteDimensional ℚ_[p] W] (hMW : ∀ x ∈ M, x ∈ W) :
    Module.finrank ℤ_[p] M ≤ Module.finrank ℚ_[p] W := by
  have hr : Module.rank ℤ_[p] M ≤ (Module.finrank ℚ_[p] W : Cardinal) := by
    apply rank_le
    intro s hs
    have h1 : LinearIndependent ℤ_[p] (fun i : s => ((i : M) : V)) :=
      hs.map' M.subtype (Submodule.ker_subtype M)
    have h2 : LinearIndependent ℚ_[p] (fun i : s => ((i : M) : V)) :=
      (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]).mp h1
    have h3 : LinearIndependent ℚ_[p] (fun i : s => (⟨((i : M) : V), hMW _ (i : M).2⟩ : W)) := by
      refine LinearIndependent.of_comp W.subtype ?_
      exact h2
    have := h3.fintype_card_le_finrank
    simpa using this
  exact Module.finrank_le_of_rank_le hr

end Gen

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)


open Classical in
def xiMons (n : ℕ) : Finset (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) :=
  (CountingStatementReduction.Ev r n).image (fun e => ∑ c : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t c) (e c))

theorem card_xiMons (n : ℕ) : (xiMons (r := r) G n).card ≤ dXi r n := by
  classical
  unfold xiMons
  refine (Finset.card_image_le).trans ?_
  rw [CountingStatementReduction.card_Ev]
  unfold dXi
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e1 : r' + 1 + n - 1 = n + r' := by omega
  have e2 : n + (r' + 1) - 1 = n + r' := by omega
  rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]

theorem xiVar_inj : Function.Injective (Formalism.GM.M.xiVar N r G.T.t) := by
  intro c d h
  simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact h.2

theorem xi_mem_span (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℚ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  have hs := (Submodule.mem_inf.1 hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' := hs hm
  obtain ⟨hsupp, hsum⟩ := hm'
  have hmono : monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : ℚ_[p]) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hmono]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
  unfold xiMons
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem finrank_Ljj_le (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have h1 := finrank_zp_le (Ljj p (r := r) G j jp) W hsub
  have h2 : Module.finrank ℚ_[p] W ≤ Fintype.card (Fin (Module.finrank ℚ_[p] Yq) × Ms) := finrank_range_le_card fam
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at h2
  have h3 := card_xiMons (r := r) G (G.B - jp)
  calc Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) ≤ Module.finrank ℚ_[p] Yq * Ms.card := h1.trans h2
    _ ≤ dimY p (r := r) G j jp * dXi r (G.B - jp) := Nat.mul_le_mul le_rfl h3

end Level

theorem restRankL_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestRankL C0 CE1 CE2 X := by
  intro dl _ aTop _ x _
  exact finrank_Ljj_le X.p (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MemIntPolIff
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Gens

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : ℚ_[p] →+* KK O} {N r : ℕ} [NeZero r]

theorem map_Ehat (D : BlockData N) (i : Fin (gmB D).T.t) :
    map ι ((gmB D).Ehat p (r := r) i) = D.Ehat O (r := r) i := by
  unfold Formalism.GM.M.BlockData.Ehat Formalism.MainNotions.G.BlockData.Ehat
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_Eplus (D : BlockData N) :
    map ι ((gmB D).Eplus p (r := r)) = D.Eplus O (r := r) := by
  unfold Formalism.GM.M.BlockData.Eplus Formalism.MainNotions.G.BlockData.Eplus
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_gens (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p])
    (hx : x ∈ (gmB D).gens p (r := r) j jp) : map ι x ∈ D.gens O (r := r) j jp := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨map ι y, map_YZ hint (D.lettersAt j jp) D.T.J D.T.thr y hy, map ι g, map_XiPolZ hint g hg, ?_⟩
  simp only [map_mul, map_prod, map_pow, map_X, map_Ehat, map_Eplus, map_rename]
  rfl

theorem map_smul_Q {σ : Type} (c : ℚ_[p]) (x : MvPolynomial σ ℚ_[p]) : map ι (c • x) = ι c • map ι x := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_SSZ (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p]) (hx : x ∈ (gmB D).SSZ p (r := r)) :
    map ι x ∈ Submodule.span (KK O) (D.SSZ O (r := r) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hok, hx⟩ := hx
    have hm : MvPolynomial.map ι x ∈ D.gens O (r := r) j jp := map_gens hint D j jp x hx
    exact Submodule.subset_span (Submodule.subset_span
      (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hok, hm⟩⟩⟩))
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul ℚ_[p] a x, map_smul_Q]
    exact Submodule.smul_mem _ _ hx

abbrev intMap (σ : Type) : MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])

theorem mem_intPol_iff {σ : Type} (F : MvPolynomial σ ℚ_[p]) :
    F ∈ Formalism.GM.M.IntPol p σ ↔ F ∈ (intMap (p := p) σ).range := Iff.rfl

private theorem X_mem_intMap {σ : Type} (v : σ) :
    (X v : MvPolynomial σ ℚ_[p]) ∈ (intMap (p := p) σ).range :=
  ⟨X v, by simp⟩

theorem gens_int (D : Formalism.GM.M.BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  rw [mem_intPol_iff]
  rw [Formalism.GM.M.YZ] at hy
  rw [Formalism.GM.M.XiPolZ] at hg
  have h1 : y ∈ Formalism.GM.M.PolZ p r (D.lettersAt j jp) := (Submodule.mem_inf.1 hy).2
  rw [Formalism.GM.M.PolZ] at h1
  have h2 : y ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := (Submodule.mem_inf.1 h1).2
  have hE : ∀ i, D.Ehat p (r := r) i ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    intro i
    unfold Formalism.GM.M.BlockData.Ehat
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hP : D.Eplus p (r := r) ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    unfold Formalism.GM.M.BlockData.Eplus
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hy' : rename (Formalism.GM.M.chainEmb N r D.T.t) y ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    obtain ⟨G, rfl⟩ := (mem_intPol_iff y).1 h2
    exact ⟨rename (Formalism.GM.M.chainEmb N r D.T.t) G, by simp [map_rename]⟩
  have hg' : g ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range :=
    (mem_intPol_iff g).1 (Submodule.mem_inf.1 hg).2
  refine mul_mem (mul_mem (mul_mem ?_ (pow_mem (X_mem_intMap _) _)) hy') hg'
  exact mul_mem (mul_mem (prod_mem fun i _ => pow_mem (hE i) _) (pow_mem hP _))
    (prod_mem fun i _ => pow_mem (X_mem_intMap _) _)

theorem SSZ_int (D : Formalism.GM.M.BlockData N) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.SSZ p (r := r)) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  refine (Submodule.span_le.2 ?_) hx
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨j, jp, -, hz⟩ := hz
  exact gens_int D j jp z hz

end Gens

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
