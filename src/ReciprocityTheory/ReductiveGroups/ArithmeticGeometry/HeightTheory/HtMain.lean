module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightMinMaxFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SumLogHeightUpperBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscB

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GenericPointHeight.GenericPointStatements.GenericPointTheorem.HtGenericPt
open NumberField

theorem HtGenericPt {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by
  classical
  intro hd h
  refine ⟨?_, ⟨hd.a4.choose, hd.a4.choose_spec.1⟩⟩
  have hφ : ∀ c, ∃ φ : Module.Dual K (A c), φ (d.w (d.jc c) c) ≠ 0 := by
    intro c
    by_contra hcon
    push_neg at hcon
    exact hd.w_base c ((Module.forall_dual_apply_eq_zero_iff K _).mp hcon)
  choose φ hφ using hφ
  let P : ι → MvPolynomial (Fin (d.N + 1)) K := fun c =>
    ∑ j, MvPolynomial.C (φ c (d.w j c)) * MvPolynomial.X j
  have hev : ∀ (x : Fin (d.N + 1) → K) c, MvPolynomial.eval x (P c) = φ c (d.wx x c) := by
    intro x c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      ReciprocityTheory.ChartRestriction.G.T0.Data.wx, Finset.sum_apply, Pi.smul_apply, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hP : ∀ c, P c ≠ 0 := by
    intro c hc
    apply hφ c
    have := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single (d.jc c) 1)) hc
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      Finsupp.single_eq_single_iff] using this
  have hprod : (∏ c, P c) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hP c)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  by_contra hne
  push_neg at hne
  apply hprod
  apply MvPolynomial.funext
  intro x
  obtain ⟨c, hc⟩ := hne x
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hev, hc, map_zero])
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NlNonnegFin
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem isOver_unique {Ωc : Type*} [Field Ωc] [Algebra K Ωc] (v : AddValuation Ωc (WithTop ℤ))
    (la la' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (h1 : IsOver (K := K) v la)
    (h2 : IsOver (K := K) v la') : la = la' :=
  IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun a => (h1 a).symm.trans (h2 a))

theorem nl_nonneg_fin (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite := by
  refine ⟨fun la => ?_, ?_⟩
  · unfold Data.Nl
    refine Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw => ?_
    have h1 := hd.ord_nonneg_et c _ (d.admissible_over_prime hd h la c w hw).1
    have h2 : (0 : ℝ) ≤ (d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) : ℝ) := by exact_mod_cast h1
    exact mul_nonneg (Nat.cast_nonneg _) h2
  · have hS : ∀ c, {v | d.admitted c v ∧ d.ord c v (d.n1 • d.wde) (d.et c) ≠ 0}.Finite :=
      fun c => hd.a3' c (hd.et_mem c) (hd.et_ne c)
    refine Set.Finite.subset (Set.finite_iUnion fun c => (hS c).biUnion
      (fun v _ => (show ({la | IsOver (K := K) v la} : Set _).Subsingleton from
        fun a ha b hb => isOver_unique v a b ha hb).finite)) ?_
    intro la hla
    by_contra hno
    apply hla
    unfold Data.Nl
    refine Finset.sum_eq_zero fun c _ => finsum_eq_zero_of_forall_eq_zero fun w => ?_
    classical
    rw [finsum_eq_if]
    split_ifs with hw
    swap; · rfl
    have hs4 := d.admissible_over_prime hd h la c w hw
    by_cases h0 : d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) = 0
    · simp [h0]
    · exact absurd (Set.mem_iUnion.2 ⟨c, Set.mem_biUnion (x := d.Wres c w)
      (show d.Wres c w ∈ {v | d.admitted c v ∧ d.ord c v (d.n1 • d.wde) (d.et c) ≠ 0} from ⟨hs4.1, h0⟩)
      (show la ∈ {la | IsOver (K := K) (d.Wres c w) la} from hs4.2.1)⟩) hno

theorem disc_two (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) :
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
      d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
        (Real.log (d.N + 1 : ℕ) + 1 / 2)) + d.del * d.Pet := by
  have hta : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
  have hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) =>
      d.nrm p.1 (d.n1 • d.wde) (d.et p.1) p.2) :=
    fun sg => hd.bdd sg _ d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hint := fun c sg => (d.int_Nsg hd h hI2be c sg).1 (d.n1 • d.wde) (d.et c)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (hd.et_mem c) (hd.et_ne c)
  have h4 := (d.h_four hd h (d.n1 • d.wde) d.et hta (hd.ord_nonneg_et) hbdd hint).2
  have hNl : (fun la => d.Nl h la * logNorm la) =
      (fun la => d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := rfl
  rw [hNl]
  have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
  have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
  have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
  have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
  have hE : meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet := hI2et
  calc _ ≤ (d.Hgt h (d.n1 • d.wde) d.et + d.del * meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) +
          d.D * d.aG h (d.n1 • d.wde) d.et * (Real.log (d.N + 1 : ℕ) + 1 / 2)) / d.i :=
        div_le_div_of_nonneg_right h4 hi.le
    _ = d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
          (Real.log (d.N + 1 : ℕ) + 1 / 2)) +
          d.del * (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i) := by
        rw [hn1]; field_simp; ring
    _ ≤ _ := by gcongr

theorem disc_one (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
    (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
    2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨_hDe0, hloc⟩ := d.disc_lattice hd h
  obtain ⟨hgf, hNef, hglob⟩ := d.disc_global hd h hI2be ta' hta'
  have hl : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la := by
    intro la
    apply Real.log_nonneg
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hIL0 : ∀ la, 0 ≤ d.IL h hd.sel hd.a4.choose la := fun _ => Nat.cast_nonneg _
  have hsupp : (Function.support (d.IL h hd.sel hd.a4.choose)).Finite := by
    apply (hgf.union hNef).subset
    intro la hla
    simp only [Function.mem_support, Set.mem_union] at hla ⊢
    by_contra hc
    push_neg at hc
    have h2 := (hloc la).2
    rw [hc.1, hc.2] at h2
    push_cast at h2
    exact hla (le_antisymm (by linarith) (hIL0 la))
  refine ⟨fun la c => (d.places_over_la hd h la c).1, fun la => (hloc la).1, hsupp, ?_⟩
  have hf1 : (Function.support fun la => 2 * (d.IL h hd.sel hd.a4.choose la * logNorm la)).Finite :=
    hsupp.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0]; ring
  have hf2 : (Function.support fun la =>
      ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la).Finite :=
    (hgf.union hNef).subset fun la hla => by
      simp only [Function.mem_support, Set.mem_union] at hla ⊢
      by_contra hc; push_neg at hc; apply hla; rw [hc.1, hc.2]; simp
  have hf0 : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la).Finite :=
    hsupp.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have hle : (∑ᶠ la, 2 * (d.IL h hd.sel hd.a4.choose la * logNorm la)) ≤
      ∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la :=
    finsum_le_finsum' hf1 hf2 fun la => by
      have := (hloc la).2
      have := hl la
      nlinarith
  have hnK : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [← mul_finsum' _ _ hf0] at hle
  calc 2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ))
      = (2 * ∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ) := by ring
    _ ≤ (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
          (Module.finrank ℚ K : ℝ) := div_le_div_of_nonneg_right hle hnK.le
    _ ≤ _ := hglob

theorem disc (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
    (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
    2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * lr + 2 * d.Hgt h d.wF ta' ∧
    (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite ∧
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
      d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) * lr) +
        d.del * d.Pet := by
  intro lr
  obtain ⟨h1, h2, h3, h4⟩ := d.disc_one hd h hI2et hI2be ta' hta'
  obtain ⟨h5, h6⟩ := d.nl_nonneg_fin hd h
  exact ⟨h1, h2, h3, h4, h5, h6, d.disc_two hd h hI2et hI2be⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CardEmbPos
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem card_emb_pos : (0 : ℝ) < Fintype.card (K →+* ℂ) := by
  haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
  exact_mod_cast Fintype.card_pos

theorem meanK_le (F G H : (K →+* ℂ) → ℝ) (C r : ℝ) (hle : ∀ sg, F sg ≤ G sg + C + r * H sg) :
    meanK F ≤ meanK G + C + r * meanK H := by
  have hc : (0 : ℝ) < Fintype.card (K →+* ℂ) := card_emb_pos
  have hs : (∑ sg, F sg) ≤ (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    calc (∑ sg, F sg) ≤ ∑ sg, (G sg + C + r * H sg) := Finset.sum_le_sum (fun sg _ => hle sg)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.mul_sum]
  unfold meanK
  rw [div_le_iff₀ hc]
  have e : ((∑ sg, G sg) / (Fintype.card (K →+* ℂ) : ℝ) + C +
      r * ((∑ sg, H sg) / (Fintype.card (K →+* ℂ) : ℝ))) * (Fintype.card (K →+* ℂ) : ℝ) =
      (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    field_simp <;> ring
  linarith

theorem sg_part (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    meanK (d.Nsg d.wL f) ≤ meanK (d.NsgMM f) + d.del * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) +
      d.cc / d.i * meanK (d.Nsg (d.n1 • d.wde) d.et) := by
  apply meanK_le
  intro sg
  simp only [Nsg, NsgMM, del, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => d.sg_one hd h hI2be f hf c sg)

theorem ordMM_fin (hd : d.AxH 𝒜) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {v | d.admitted c v ∧ (d.ordMM c v f : ℝ) ≠ 0}.Finite := by
  have hA := hd.a3' c hf hf0
  have hB : ∀ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}.Finite :=
    fun j => hd.a3' c (hd.w_mem j c) j.2
  refine (hA.union (Set.finite_iUnion hB)).subset ?_
  rintro v ⟨hv, hne⟩
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and,
    not_not] at hnot
  obtain ⟨h1, h2⟩ := hnot
  apply hne
  have e1 : d.ord c v d.wL f = 0 := h1 hv
  have e2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) = 0 := fun j => h2 j hv
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = 0 := by
    have e3 : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0 := funext e2
    rw [show (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) =
      ⨅ _ : {j // d.w j c ≠ 0}, (0 : ℤ) from congrArg iInf e3]
    rcases isEmpty_or_nonempty {j // d.w j c ≠ 0} with hE | hE
    · rw [iInf, Set.range_eq_empty, Int.csInf_empty]
    · exact ciInf_const
  simp only [ordMM, e1, hinf, sub_zero, Int.cast_zero]

theorem la_part (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    (∑ᶠ la, d.NlaG h d.wL f la * logNorm la) ≤ (∑ᶠ la, d.NlaMM h f la * logNorm la) +
      d.del * (∑ᶠ la, d.nu la * logNorm la) +
      d.cc / d.i * (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := by
  have hln : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la :=
    fun la => Real.log_natCast_nonneg _

  have finG : ∀ (G : WT) (ta : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (Function.support (fun la => d.NlaG h G ta la * logNorm la)).Finite := by
    intro G ta hta
    have h1 : (Function.support (d.NlaG h G ta)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ord c v G (ta c)) (hd.a3' c (hta c).1 (hta c).2)) ?_
      exact d.aNla_supp hd h (fun c v g => d.ord c v G g) ta
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finMM : (Function.support (fun la => d.NlaMM h f la * logNorm la)).Finite := by
    have h1 : (Function.support (d.NlaMM h f)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ordMM c v (f c)) ?_) ?_
      · refine (d.ordMM_fin hd c (f c) (hf c).1 (hf c).2).subset ?_
        rintro v ⟨hv, hne⟩
        exact ⟨hv, Int.cast_ne_zero.mpr hne⟩
      · exact d.aNla_supp hd h (fun c v g => d.ordMM c v g) f
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finNu : (Function.support (fun la => d.nu la * logNorm la)).Finite :=
    hH1.2.1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finL := finG d.wL f hf
  have finE := finG (d.n1 • d.wde) d.et (fun c => ⟨hd.et_mem c, hd.et_ne c⟩)
  have finAll := finMM.union (finNu.union finE)

  have key : ∑ᶠ la, d.NlaG h d.wL f la * logNorm la ≤
      ∑ᶠ la, (d.NlaMM h f la * logNorm la + d.del * (d.nu la * logNorm la) +
        d.cc / d.i * (d.NlaG h (d.n1 • d.wde) d.et la * logNorm la)) := by
    refine finsum_le_finsum' finL (finAll.subset fun x hx => ?_) fun la => ?_
    · by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      apply hx
      simp [hn.1, hn.2.1, hn.2.2]
    · have := mul_le_mul_of_nonneg_right (d.Nla_le hd h hH1 f la) (hln la)
      exact this.trans_eq (by ring)
  refine key.trans_eq ?_
  rw [finsum_add_distrib, finsum_add_distrib, mul_finsum, mul_finsum]
  all_goals
    refine finAll.subset fun x hx => ?_
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hx
    simp [hn.1, hn.2.1, hn.2.2]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HSix
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem h_six (hd : d.AxH 𝒜) (h : d.S1) (hF1d : d.TrivialPlaceHyp) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c) (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (d.aG h d.wL (d.wx x) : ℝ) ≤ 4 / 3 * d.del ∧
    0 ≤ d.aG h (d.n1 • d.wde) d.et ∧ d.aG h (d.n1 • d.wde) d.et ≤ d.n1 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h ((2 : ℕ) • d.G1) d.ta1 ∧ d.aG h ((2 : ℕ) • d.G1) d.ta1 ≤ 2 * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.wF ta' ∧ d.aG h d.wF ta' ≤ (d.D + 4) * d.aG h d.wL (d.wx x) ∧
    0 ≤ d.aG h d.G2 d.ta2 ∧ d.aG h d.G2 d.ta2 ≤ (d.D + 4) * d.aG h d.wL (d.wx x) := by
  set sb : ∀ c, A c := fun c => d.w (d.jc c) c with hsbdef
  have hsb : ∀ c, sb c ∈ 𝒜 c d.wL ∧ sb c ≠ 0 := fun c => ⟨hd.w_mem _ c, hd.w_base c⟩
  have hwx : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
  have het : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
  have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 := fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
  have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
  rw [d.aG_wx hd h x hx]
  set aL := d.aG h d.wL sb with haL
  have hde0 : 0 ≤ d.aG h (d.n1 • d.wde) d.et := d.aG_nonneg hd h _ _ fun c v hv => hd.ord_nonneg_et c v hv
  have hG10 : 0 ≤ d.aG h ((2 : ℕ) • d.G1) d.ta1 := d.aG_nonneg hd h _ _ fun c v hv => hd.ordDoubleFirstSection_nonneg c v hv
  have hG20 : 0 ≤ d.aG h d.G2 d.ta2 := d.aG_nonneg hd h _ _ fun c v hv => hd.ordSecondSectionNonneg c v hv
  have hF0 : 0 ≤ d.aG h d.wF ta' := by
    choose k hk using d.thp_ne hd
    have hth : ∀ c, d.thp (k c) c ∈ 𝒜 c d.wF ∧ d.thp (k c) c ≠ 0 := fun c => ⟨hd.thp_mem _ c, hk c⟩
    rw [(d.norm_factorization hd h).2.1 d.wF ta' (fun c => d.thp (k c) c) hta' hth]
    refine d.aG_nonneg hd h _ _ fun c v hv => hd.ord_nonneg_Thp c v hv (d.thp (k c)) ?_ (hk c)
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨k c, rfl⟩

  obtain ⟨a, ha⟩ : ∃ a, d.n1 = a + 1 := ⟨d.n1 - 1, by
    have : 1 ≤ d.n1 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hd.i_ge; omega)
      (by have := hd.g_zero_ge_ask_sum; omega))
    omega⟩
  have hadd1 : (2 * d.n1 : ℤ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := by
    have hW : (2 * a + 1 + 1) • d.wL = (a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde) := by
      unfold G1; rw [ha]; simp only [smul_sub, ← mul_nsmul]
      rw [show (2 * a + 1 + 1) = (a + 1) * 2 by ring, show (1 + 1) * (a + 1) = (a + 1) * 2 by ring]
      abel
    have m1 := d.pow_mem_ne hd hsb (2 * a + 1)
    have m2 := d.pow_mem_ne hd hta1 a
    have m3 := d.pow_mem_ne hd het 1
    have m23 : ∀ c, (d.ta1 ^ (a + 1) * d.et ^ (1 + 1)) c ∈ 𝒜 c ((a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde)) ∧
        (d.ta1 ^ (a + 1) * d.et ^ (1 + 1)) c ≠ 0 := fun c => by
      haveI := hd.graded c
      exact ⟨SetLike.mul_mem_graded (m2 c).1 (m3 c).1, hd.mul_ne_zero c (m2 c).1 (m3 c).1 (m2 c).2 (m3 c).2⟩
    have m1' : ∀ c, (sb ^ (2 * a + 1 + 1)) c ∈ 𝒜 c ((a + 1) • ((2 : ℕ) • d.G1) + (1 + 1) • (d.n1 • d.wde)) ∧
        (sb ^ (2 * a + 1 + 1)) c ≠ 0 := fun c => by rw [← hW]; exact m1 c
    have e1 := (d.norm_factorization hd h).2.1 _ _ _ m1' m23
    rw [(d.norm_factorization hd h).2.2 _ _ _ _ m2 m3, d.aG_pow hd h hta1, d.aG_pow hd h het, ← hW,
      d.aG_pow hd h hsb] at e1
    rw [← haL] at e1
    have hn : (d.n1 : ℤ) = a + 1 := by rw [ha]; push_cast; ring
    rw [hn]; push_cast at e1 ⊢; linarith
  have hadd2 : ((d.D : ℤ) + 4) * aL = d.aG h d.wF ta' + d.aG h d.G2 d.ta2 := by
    have hW : (d.D + 3 + 1) • d.wL = d.wF + d.G2 := by
      unfold G2; rw [add_sub_cancel]
    have m1 := d.pow_mem_ne hd hsb (d.D + 3)
    have m23 : ∀ c, (ta' * d.ta2) c ∈ 𝒜 c (d.wF + d.G2) ∧ (ta' * d.ta2) c ≠ 0 := fun c => by
      haveI := hd.graded c
      exact ⟨SetLike.mul_mem_graded (hta' c).1 (hta2 c).1,
        hd.mul_ne_zero c (hta' c).1 (hta2 c).1 (hta' c).2 (hta2 c).2⟩
    have m1' : ∀ c, (sb ^ (d.D + 3 + 1)) c ∈ 𝒜 c (d.wF + d.G2) ∧ (sb ^ (d.D + 3 + 1)) c ≠ 0 :=
      fun c => by rw [← hW]; exact m1 c
    have e1 := (d.norm_factorization hd h).2.1 _ _ _ m1' m23
    rw [(d.norm_factorization hd h).2.2 _ _ _ _ hta' hta2, ← hW, d.aG_pow hd h hsb] at e1
    rw [← haL] at e1
    push_cast at e1; linarith

  have hEsum0 : 0 ≤ ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) :=
    Finset.sum_nonneg fun c _ => finsum_nonneg fun p => finsum_nonneg fun hp =>
      mul_nonneg (d.Ep_nonneg hd h c hp) (Nat.cast_nonneg _)
  have hE : ((∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) : ℤ) : ℝ) ≤
      d.cc / (2 * d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
    unfold aG
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    refine fsum_le_of _ _ _ ((d.Ep_ne hd h c _ (hsb c).1 (hsb c).2).subset fun p ⟨hp, hs⟩ =>
        ⟨hp, fun h0 => hs (by simp [h0])⟩)
      (((d.good_primes_properties hd h c).2.2.1 _ _ (het c).1 (het c).2).subset fun p ⟨hp, hs⟩ =>
        ⟨hp, fun h0 => hs (by simp [h0])⟩) _ fun p hp => ?_
    have e := d.Ep_le hd h hF1d c hp
    have hdg : (0 : ℝ) ≤ d.dg (d.gen p) := Nat.cast_nonneg _
    push_cast
    calc (d.Ep h c p : ℝ) * d.dg (d.gen p)
        ≤ (d.cc / (2 * d.i) * d.nP h c (d.n1 • d.wde) (d.et c) p) * d.dg (d.gen p) :=
          mul_le_mul_of_nonneg_right e hdg
      _ = _ := by ring
  have haLeq := d.aG_sb hd h
  rw [← haL] at haLeq
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1 : (d.n1 : ℝ) = d.i * d.g0 := by unfold n1; push_cast; ring
  have hcc := hd.cc_nonneg
  have hccg0 := hd.ccg0
  have haL0 : (0 : ℝ) ≤ aL := by rw [haLeq]; exact_mod_cast (by positivity : (0:ℤ) ≤ d.del + _ )
  have e3 : (d.aG h (d.n1 • d.wde) d.et : ℝ) ≤ d.n1 * aL := by
    have : (2 * d.n1 : ℝ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := by
      exact_mod_cast hadd1
    have h2 : (0 : ℝ) ≤ d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 :=
      mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hG10)
    linarith
  refine ⟨?_, hde0, ?_, hG10, ?_, hF0, ?_, hG20, ?_⟩
  · have k1 : d.cc / (2 * d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) ≤ d.cc / (2 * d.i) * (d.n1 * aL) :=
      mul_le_mul_of_nonneg_left e3 (by positivity)
    have k2 : d.cc / (2 * d.i) * (d.n1 * aL) = d.cc * d.g0 * aL / 2 := by
      rw [hn1]; field_simp
    have k3 : d.cc * d.g0 * (aL : ℝ) ≤ 1 / 2 * aL := mul_le_mul_of_nonneg_right hccg0 haL0
    have k4 : (aL : ℝ) = d.del + ((∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      d.Ep h c p * (d.dg (d.gen p) : ℤ) : ℤ) : ℝ) := by rw [haLeq]; push_cast; ring
    linarith
  · have : (2 * d.n1 : ℤ) * aL = d.n1 * d.aG h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.aG h (d.n1 • d.wde) d.et := hadd1
    nlinarith [Int.natCast_nonneg d.n1]
  · have h1 : (1 : ℤ) ≤ d.n1 := by rw [ha]; push_cast; omega
    nlinarith
  · linarith
  · linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Imports
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem exists_generic (hd : d.AxH 𝒜) (h : d.S1) :
    (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :=
  HtGenericPt 𝒜 d hd h

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
namespace ReciprocityTheory.ChartRestriction.G.T0


set_option maxHeartbeats 1000000 in
theorem heights_arith
    (D δ L lr lw1 hN sF laW nuS c g0 i DF PP0' PN tableLineDegreeFive tableLineDegreeTwo PI4 Prw G Pet
      aL ade aG1 aF aG2 HMM HL Hde HF SI SN Ssum δlogδ : ℝ)
    (hD : 3 ≤ D) (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcg : c * g0 ≤ 1 / 2)
    (hg0 : 0 ≤ g0) (hi : 1 ≤ i)
    (hP : 1 ≤ PP0' ∧ 1 ≤ PN ∧ 1 ≤ tableLineDegreeFive ∧ 1 ≤ tableLineDegreeTwo ∧ 1 ≤ PI4 ∧ 1 ≤ Prw ∧ 1 ≤ G ∧ 1 ≤ Pet)
    (hlr0 : 0 ≤ lr) (hlr : lr ≤ Prw * L) (hlw1 : lw1 ≤ Prw * L) (hhN : hN / 2 ≤ Prw * L)
    (hDF : DF ≤ L) (hlaW : laW ≤ G * L) (hnu : nuS ≤ PN * L)

    (hUP : sF ≤ (D + 2) * δ * (PP0' * L + max 0 laW + lw1))
    (hb1 : HMM = sF + δ * hN / 2)

    (haL : aL ≤ 4 / 3 * δ) (hade0 : 0 ≤ ade) (hade : ade ≤ aL) (haG10 : 0 ≤ aG1) (haG1 : aG1 ≤ aL)
    (haF0 : 0 ≤ aF) (haF : aF ≤ (D + 4) * aL) (haG20 : 0 ≤ aG2) (haG2 : aG2 ≤ (D + 4) * aL)

    (h7a : HL ≤ HMM + δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) + D * c * g0 * ade * lr + c * g0 * Hde)
    (h7b : Hde ≤ HL + (δ * PI4 * D * L + D * aG1 * lr))
    (h7c : HF ≤ (D + 4) * HL + δ * PI4 * D * L + D * aG2 * lr)

    (hdi : 2 * SI ≤ δlogδ + 2 * Ssum + 2 * D * aF * lr + 2 * HF)
    (hdn : SN / i ≤ g0 * (Hde + D * ade * lr) + δ * Pet) :
    2 * SI ≤ δlogδ + 2 * Ssum + 8 / 3 * D * (D + 4) * δ * Prw * L +
        2 * (D + 4) * (D + 1) * δ *
          (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L ∧
      SN / i ≤ g0 * ((D + 1) * δ *
        (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L) + δ * Pet := by
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6, hP7, hP8⟩ := hP
  have hD0 : 0 ≤ D := by linarith
  have hD4 : 0 ≤ D + 4 := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ δ * L := mul_nonneg hδ hL0
  have hcg0 : 0 ≤ c * g0 := mul_nonneg hc0 hg0
  have haL' : ade ≤ 4 / 3 * δ := hade.trans haL
  have hPL : 0 ≤ Prw * L := mul_nonneg (by linarith) hL0
  have hδPL : 0 ≤ 4 / 3 * δ * (Prw * L) := mul_nonneg (by linarith) hPL
  have hmax : max 0 laW ≤ G * L := max_le (mul_nonneg (by linarith) hL0) hlaW
  have hin : PP0' * L + max 0 laW + lw1 ≤ (PP0' + G + Prw) * L := by linarith
  have hsF : sF ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
    hUP.trans (mul_le_mul_of_nonneg_left hin (mul_nonneg (by linarith) hδ))
  have hN2 : δ * hN / 2 ≤ δ * (Prw * L) := by
    have := mul_le_mul_of_nonneg_left hhN hδ
    linarith
  have hnu2 : δ * (nuS + tableLineDegreeFive * DF + c * tableLineDegreeTwo) ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := by
    apply mul_le_mul_of_nonneg_left _ hδ
    have h1 : tableLineDegreeFive * DF ≤ tableLineDegreeFive * L := mul_le_mul_of_nonneg_left hDF (by linarith)
    have h2 : c * tableLineDegreeTwo ≤ 1 * tableLineDegreeTwo := mul_le_mul_of_nonneg_right hc1 (by linarith)
    have h3 : tableLineDegreeTwo * 1 ≤ tableLineDegreeTwo * L := mul_le_mul_of_nonneg_left hL (by linarith)
    linarith
  have hcross : D * c * g0 * ade * lr ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have h2 : c * g0 * (ade * lr) ≤ 1 / 2 * (4 / 3 * δ * (Prw * L)) :=
      mul_le_mul hcg h1 (mul_nonneg hade0 hlr0) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 hD0
    linarith
  have hadl : D * ade * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : ade * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul haL' hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hY1 : D * aG1 * lr ≤ D * (4 / 3 * δ * (Prw * L)) := by
    have h1 : aG1 * lr ≤ 4 / 3 * δ * (Prw * L) := mul_le_mul (haG1.trans haL) hlr hlr0 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hA4 : (D + 4) * aL ≤ (D + 4) * (4 / 3 * δ) := mul_le_mul_of_nonneg_left haL hD4
  have hY2 : D * aG2 * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aG2 * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haG2.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hYF : D * aF * lr ≤ D * ((D + 4) * (4 / 3 * δ) * (Prw * L)) := by
    have h1 : aF * lr ≤ (D + 4) * (4 / 3 * δ) * (Prw * L) :=
      mul_le_mul (haF.trans hA4) hlr hlr0 (mul_nonneg hD4 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hD0
    linarith
  have hPI : 0 ≤ δ * PI4 * D * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hδ (by linarith)) hD0) hL0
  have hXb0 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := by
    have e1 : 0 ≤ (D + 2) * δ * ((PP0' + G + Prw) * L) :=
      mul_nonneg (mul_nonneg (by linarith) hδ) (mul_nonneg (by linarith) hL0)
    have e2 : 0 ≤ δ * (Prw * L) := mul_nonneg hδ hPL
    have e3 : 0 ≤ δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) := mul_nonneg hδ (mul_nonneg (by linarith) hL0)
    have e4 : 0 ≤ D * (1 / 2 * (4 / 3 * δ * (Prw * L))) := mul_nonneg hD0 (by linarith)
    linarith
  have hYb0 : 0 ≤ δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)) := by
    have := mul_nonneg hD0 hδPL
    linarith
  have hHde : Hde ≤ HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by linarith
  have hHL1 : HL ≤ ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      c * g0 * (HL + (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L)))) := by
    have := mul_le_mul_of_nonneg_left hHde hcg0
    linarith
  have hHL : HL ≤ 2 * ((D + 2) * δ * ((PP0' + G + Prw) * L) + δ * (Prw * L) +
      δ * ((PN + tableLineDegreeFive + tableLineDegreeTwo) * L) + D * (1 / 2 * (4 / 3 * δ * (Prw * L)))) +
      (δ * PI4 * D * L + D * (4 / 3 * δ * (Prw * L))) := by
    by_cases hHL0 : 0 ≤ HL
    · have a1 := mul_le_mul_of_nonneg_right hcg hHL0
      have a2 := mul_le_mul_of_nonneg_right hcg hYb0
      linarith
    · push_neg at hHL0
      linarith
  have hHF := mul_le_mul_of_nonneg_left hHL hD4
  have e1 : 0 ≤ (D + 4) * (6 * D + 4) * G := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e2 : 0 ≤ (D + 4) * (10 * D + 8) * PP0' := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e3 : 0 ≤ (D + 4) * (6 * D + 6) * Prw := mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e4 : 0 ≤ (D + 4) * (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) :=
    mul_nonneg (mul_nonneg hD4 (by linarith)) (by linarith)
  have e5 : 0 ≤ (11 * D * D + 55 * D + 48) * PI4 := mul_nonneg (by nlinarith) (by linarith)
  have hE := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4) e5)
  have f1 : 0 ≤ (6 * D + 4) * G := mul_nonneg (by linarith) (by linarith)
  have f2 : 0 ≤ (10 * D + 8) * PP0' := mul_nonneg (by linarith) (by linarith)
  have f3 : 0 ≤ (12 * D + 10) * (PN + tableLineDegreeFive + tableLineDegreeTwo) := mul_nonneg (by linarith) (by linarith)
  have f4 : 0 ≤ (10 * D + 12) * PI4 := mul_nonneg (by linarith) (by linarith)
  have f5 : 0 ≤ (6 * D + 6) * Prw := mul_nonneg (by linarith) (by linarith)
  have hE2 := mul_nonneg hT (add_nonneg (add_nonneg (add_nonneg (add_nonneg f1 f2) f3) f4) f5)
  constructor
  · linarith
  · have hb : Hde + D * ade * lr ≤ (D + 1) * δ * (2 * G + 6 * (2 * (PP0' + PN + tableLineDegreeFive + tableLineDegreeTwo + PI4 + Prw) + G)) * L +
        4 / 3 * D * δ * Prw * L := by linarith
    have := mul_le_mul_of_nonneg_left hb hg0
    linarith

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)


set_option maxHeartbeats 1000000 in
theorem heights (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hLAM : d.HtLAM)
    (hSup : d.HtSup) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl (d.htOf hd h) := by
  obtain ⟨⟨x, hx⟩, ⟨ta', hta'⟩⟩ := d.exists_generic hd h
  choose F hF _hF0 using fun c => d.componentForm_poly hd h c
  have hUP := d.sum_logHeight_upper_bound hd h hLAM F hF
  have hb1 := d.HeightMinMaxFormula hd h hI2be x hx F hF
  obtain ⟨haL, hade0, hade, haG10, haG1, haF0, haF, haG20, haG2⟩ := d.h_six hd h hF1d x hx ta' hta'
  have h7 :
      let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
      let HL := d.Hgt h d.wL (d.wx x)
      let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
      let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
      let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
      let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
        (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
      let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
      HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
        d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
          d.D * d.aG h d.G2 d.ta2 * lr := by
    dsimp only
    have hf : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
    have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
    have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
    have hn1pos : (0 : ℝ) < d.n1 := by rw [hn1]; positivity
    have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
    have hla := d.la_part hd h hH1 (d.wx x) hf
    have hsg := d.sg_part hd h hI2be (d.wx x) hf
    have h0 := d.logHeight_section_bound hd h hF1d (d.wx x) hf
    obtain ⟨-, -, hind3, hind4⟩ := d.h_ind hd h hI2be
    have hta1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 :=
      fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
    have hta2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
    have hbdd1 := fun sg => hd.bdd sg _ d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
    have hbdd2 := fun sg => hd.bdd sg _ d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    have hint1 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 ((2 : ℕ) • d.G1) (d.ta1 c) (by simp)
      (hd.firstSectionMem c) (hd.firstSectionNeZero c)
    have hint2 := fun c sg => (d.int_Nsg hd h hI2be c sg).1 d.G2 (d.ta2 c) (by simp)
      (hd.secondSectionMem c) (hd.secondSectionNeZero c)
    have h41 := (d.h_four hd h _ d.ta1 hta1 hd.ordDoubleFirstSection_nonneg hbdd1 hint1).1
    have h42 := (d.h_four hd h _ d.ta2 hta2 hd.ordSecondSectionNonneg hbdd2 hint2).1
    obtain ⟨-, -, hsup1, hsup2⟩ := hSup
    have m1 := mul_le_mul_of_nonneg_left hsup1 hdel
    have m2 := mul_le_mul_of_nonneg_left hsup2 hdel
    refine ⟨?_, ?_, ?_⟩
    · have e1 : d.Hgt h d.wL (d.wx x) = (∑ᶠ la, d.NlaG h d.wL (d.wx x) la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.Nsg d.wL (d.wx x)) + d.h0f h d.wL (d.wx x) := rfl
      have e2 : d.HgtMM h (d.wx x) = (∑ᶠ la, d.NlaMM h (d.wx x) la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM (d.wx x)) + d.mahlerMeasureHeight h (d.wx x) := rfl
      have e3 : d.Hgt h (d.n1 • d.wde) d.et = (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) /
          (Module.finrank ℚ K : ℝ) + meanK (d.Nsg (d.n1 • d.wde) d.et) + d.h0f h (d.n1 • d.wde) d.et := rfl
      have hla' := div_le_div_of_nonneg_right hla hK.le
      rw [add_div, add_div, mul_div_assoc, mul_div_assoc] at hla'
      have eH : d.cc * d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1) =
          d.cc / d.i * d.Hgt h (d.n1 • d.wde) d.et := by
        rw [hn1]; field_simp
      have eA : d.D * d.cc * d.g0 * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
          (Real.log (d.N + 1 : ℕ) + 1 / 2) =
          d.D * (Real.log (d.N + 1 : ℕ) + 1 / 2) * (d.cc / d.i) * (d.aG h (d.n1 • d.wde) d.et : ℝ) := by
        rw [hn1]; field_simp
      rw [e1, e2, eH, eA, e3]
      nlinarith [hla', hsg, h0]
    · have hd3 := hind3 x hx
      have eq : d.Hgt h (d.n1 • d.wde) d.et / d.n1 =
          d.Hgt h d.wL (d.wx x) - d.Hgt h ((2 : ℕ) • d.G1) d.ta1 / 2 := by
        rw [div_eq_iff hn1pos.ne']
        linarith
      rw [eq]
      linarith [h41, m1]
    · have hd4 := hind4 x ta' hx hta'
      linarith [h42, m2]
  have hdi :
      let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
      (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
      (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
      2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
        d.del * Real.log d.del +
          2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
          2 * d.D * d.aG h d.wF ta' * lr + 2 * d.Hgt h d.wF ta' ∧
      (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite ∧
      ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
        d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) * lr) +
          d.del * d.Pet := by
    intro lr
    obtain ⟨h1, h2, h3, h4⟩ := d.disc_one hd h hI2et hI2be ta' hta'
    obtain ⟨h5, h6⟩ := d.nl_nonneg_fin hd h
    exact ⟨h1, h2, h3, h4, h5, h6, d.disc_two hd h hI2et hI2be⟩
  dsimp only at h7 hdi
  obtain ⟨h7a, h7b, h7c⟩ := h7
  obtain ⟨hplf, hIla, hIf, hdi1, hN0, hNf, hdn⟩ := hdi
  obtain ⟨hPN, hPQ, hPP0, hPP0', hPd, hGc, hPI4, hPet, hP14, hP16, hPrw, hPO⟩ := hd.P_ge
  have hn1 : (0 : ℝ) < d.n1 := by
    have h1 := hd.i_ge; have h2 := hd.g_zero_ge_ask_sum
    have : 0 < d.n1 := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hL := hd.size_L
  have hlog0 : 0 ≤ Real.log ((d.N + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos _)
  have hrw := hd.rw_le
  have hlr : Real.log ((d.N + 1 : ℕ) : ℝ) + 1 / 2 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hlw1 : Real.log ((d.N + 1 : ℕ) : ℝ) + 1 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hharm : (harmonic d.N : ℝ) ≤ Real.log ((d.N + 1 : ℕ) : ℝ) + 1 := by
    have h1 := harmonic_le_one_add_log d.N
    rcases Nat.eq_zero_or_pos d.N with h0 | hpos
    · simp [h0]
    · have : Real.log (d.N : ℝ) ≤ Real.log ((d.N + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hpos) (by push_cast; linarith)
      linarith
  have hhN : (harmonic d.N : ℝ) / 2 ≤ d.Prw * d.wsize d.wL := by nlinarith
  have hnu := hH1.2.2.1
  have hlaW := hSup.1
  have arith := heights_arith (d.D : ℝ) (d.del : ℝ) (d.wsize d.wL)
    (Real.log ((d.N + 1 : ℕ) : ℝ) + 1 / 2) (Real.log ((d.N + 1 : ℕ) : ℝ) + 1) (harmonic d.N : ℝ)
    (∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c)) (meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j)))
    ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ)) d.cc (d.g0 : ℝ) (d.i : ℝ) d.DF
    d.PP0' d.PN d.tableLineDegreeFive d.tableLineDegreeTwo d.PI4 d.Prw d.Gc d.Pet
    (d.aG h d.wL (d.wx x) : ℝ) ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1)
    ((d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2) (d.aG h d.wF ta' : ℝ) (d.aG h d.G2 d.ta2 : ℝ)
    (d.HgtMM h (d.wx x)) (d.Hgt h d.wL (d.wx x)) (d.Hgt h (d.n1 • d.wde) d.et / d.n1)
    (d.Hgt h d.wF ta')
    ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ))
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ))
    (∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))))
    (d.del * Real.log d.del)
    (by exact_mod_cast hd.D_ge) (Nat.cast_nonneg _) hL hd.cc_nonneg hd.cc_le hd.ccg0 (Nat.cast_nonneg _)
    (by exact_mod_cast hd.i_ge) ⟨hPP0', hPN, hP14, hP16, hPI4, hPrw, hGc, hPet⟩
    (by linarith) hlr hlw1 hhN hd.DF_le hlaW hnu
    (by simpa [add_assoc] using hUP) hb1
    haL (div_nonneg (by exact_mod_cast hade0) hn1.le) (by rw [div_le_iff₀ hn1]; have := (Int.cast_le (R := ℝ)).mpr hade; push_cast at this; linarith) (div_nonneg (by exact_mod_cast haG10) (by norm_num))
    (by rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; have := (Int.cast_le (R := ℝ)).mpr haG1; push_cast at this; linarith) (by exact_mod_cast haF0)
    (by exact_mod_cast haF) (by exact_mod_cast haG20) (by exact_mod_cast haG2)
    h7a h7b h7c hdi1 hdn
  obtain ⟨ar1, ar2⟩ := arith
  have hsI : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la).Finite :=
    hIf.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have hsN : (Function.support fun la => d.Nl h la * logNorm la).Finite :=
    hNf.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have eI : (fun la => (((d.htOf hd h).Ila la).toNat : ℝ) * Formalism.MainNotions.Gaps.HeightData.lN (d.htOf hd h).K la) =
      fun la => d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ := by
    funext la
    show d.IL h hd.sel hd.a4.choose la * (logNorm la / (Module.finrank ℚ K : ℝ)) = _
    rw [div_eq_mul_inv, ← mul_assoc]
    rfl
  have eN : ∀ la, (d.htOf hd h).Net la = d.Nl h la := by
    intro la
    haveI : ∀ c, Fintype {w // w ∈ d.PlOver la c} := fun c => (hplf la c).fintype
    show (∑ᶠ ζ : (Σ c, {w // w ∈ d.PlOver la c}), ((1 : ℕ) : ℝ) * (d.fze h ζ.1 ζ.2.1 : ℝ) *
      (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)) = _
    rw [finsum_eq_sum_of_fintype, Fintype.sum_sigma]
    unfold Data.Nl
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]
    simp
  have eNf : (fun la => (d.htOf hd h).Net la * Formalism.MainNotions.Gaps.HeightData.lN (d.htOf hd h).K la) =
      fun la => d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ := by
    funext la
    rw [eN la]
    show d.Nl h la * (logNorm la / (Module.finrank ℚ K : ℝ)) = _
    rw [div_eq_mul_inv, ← mul_assoc]
    rfl
  have hsI' : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la *
      (Module.finrank ℚ K : ℝ)⁻¹).Finite := hsI.subset (Function.support_mul_subset_left _ _)
  have hsN' : (Function.support fun la => d.Nl h la * logNorm la *
      (Module.finrank ℚ K : ℝ)⁻¹).Finite := hsN.subset (Function.support_mul_subset_left _ _)
  have e1 : ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ =
      (∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) * (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [tsum_eq_finsum hsI', ← finsum_mul' _ _ hsI]
  have e2 : ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ =
      (∑ᶠ la, d.Nl h la * logNorm la) * (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [tsum_eq_finsum hsN', ← finsum_mul' _ _ hsN]
  refine ⟨hIla, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩
  · rw [eI]; classical
    exact summable_of_ne_finset_zero (s := hsI'.toFinset) (by intro a ha; by_contra hn; apply ha; exact hsI'.mem_toFinset.mpr hn)
  · rw [eI]
    show 2 * ∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        d.IL h hd.sel hd.a4.choose la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹ ≤
      (d.del : ℝ) * Real.log (d.del : ℝ) +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        8 / 3 * (d.D : ℝ) * ((d.D : ℝ) + 4) * (d.del : ℝ) * d.Prw * d.wsize d.wL +
        2 * ((d.D : ℝ) + 4) * ((d.D : ℝ) + 1) * (d.del : ℝ) * (2 * d.Gc + 6 * d.PHc) * d.wsize d.wL
    rw [e1]
    have := ar1
    unfold Data.PHc Data.PH
    rw [← div_eq_mul_inv]
    linarith
  · rw [eNf]; classical
    exact summable_of_ne_finset_zero (s := hsN'.toFinset) (by intro a ha; by_contra hn; apply ha; exact hsN'.mem_toFinset.mpr hn)
  · rw [eNf]
    show (∑' la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        d.Nl h la * logNorm la * (Module.finrank ℚ K : ℝ)⁻¹) / (d.i : ℝ) ≤
      (d.g0 : ℝ) * (((d.D : ℝ) + 1) * (d.del : ℝ) * (2 * d.Gc + 6 * d.PHc) * d.wsize d.wL +
        4 / 3 * (d.D : ℝ) * (d.del : ℝ) * d.Prw * d.wsize d.wL) + (d.del : ℝ) * d.Pet
    rw [e2]
    have := ar2
    unfold Data.PHc Data.PH
    rw [← div_eq_mul_inv]
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
