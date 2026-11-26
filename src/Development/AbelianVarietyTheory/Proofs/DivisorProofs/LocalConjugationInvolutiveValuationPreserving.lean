module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Topology ValuativeRel

namespace GlobalTheory.CjInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}

theorem valuation_equiv :
    (valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact isEquiv _ _

theorem lt_one_iff (x : w.adicCompletion E) : valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  simp only [← not_le]
  exact not_congr valuation_equiv.one_le_iff_one_le

theorem tendsto_pow_zero {x : w.adicCompletion E} (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [← lt_one_iff] at h
  rw [(IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero (w.adicCompletion E)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  show valuation _ (x ^ m) < γ
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : w.adicCompletion E | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion E) := by
  have := (IsValuativeTopology.hasBasis_nhds_zero' (w.adicCompletion E)).mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩
  simpa only [lt_one_iff] using this

theorem lt_one_of_map (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) {x : w.adicCompletion E}
    (h : Valued.v x < 1) : Valued.v (s x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s x ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ Valued.v (s x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem valued_map_eq (s : w.adicCompletion E →+* w.adicCompletion E) (hs : Continuous s) (hss : ∀ x, s (s x) = x)
    (x : w.adicCompletion E) : Valued.v (s x) = Valued.v x := by

  have hle : ∀ y : w.adicCompletion E, Valued.v y ≤ 1 → Valued.v (s y) ≤ 1 := by
    intro y hy
    by_contra hc
    push_neg at hc
    have hy0 : s y ≠ 0 := by
      intro h0; rw [h0, map_zero] at hc; exact absurd hc (not_lt.2 zero_le')
    have h1 : Valued.v (s y)⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
    have h2 := lt_one_of_map s hs h1
    rw [map_inv₀, hss, map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      intro h; apply hy0; rw [h, map_zero]
    exact absurd hy (not_le.2 ((inv_lt_one₀ h0).1 h2))

  have hord : ∀ a b : w.adicCompletion E, b ≠ 0 → Valued.v a ≤ Valued.v b → Valued.v (s a) ≤ Valued.v (s b) := by
    intro a b hb hab
    have hb' : s b ≠ 0 := (map_ne_zero s).2 hb
    have h1 : Valued.v (a / b) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le'
    have h2 := hle _ h1
    rw [map_div₀, map_div₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s b) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact hb'
    exact (div_le_one₀ h0).1 h2

  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  set p : w.adicCompletion E := algebraMap E (w.adicCompletion E) π with hp
  have hvp : Valued.v p = WithZero.exp (-1) := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π
    rw [hπ] at this
    exact this
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact WithZero.exp_ne_zero hvp.symm
  have hsp0 : s p ≠ 0 := (map_ne_zero s).2 hp0
  have hvsp : Valued.v (s p) = Valued.v p := by
    apply le_antisymm
    · rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    · have := hord (s p) p hp0 (by
        rw [hvp]; apply le_exp_neg_one; apply lt_one_of_map s hs; rw [hvp]
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
      rwa [hss] at this
  by_cases hx : x = 0
  · rw [hx, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  set k := WithZero.log (Valued.v x) with hk
  set u := x * p ^ k with hu
  have hvpk : Valued.v p ^ k ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hp0)
  have hvu : Valued.v u = 1 := by
    rw [hu, map_mul, map_zpow₀, hvp, ← WithZero.exp_log hvx, ← hk, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hu0 : u ≠ 0 := by
    intro h; rw [h, map_zero] at hvu; exact zero_ne_one hvu
  have hsu1 : Valued.v (s u) ≤ 1 := hle u hvu.le
  have hsu2 : Valued.v (s u⁻¹) ≤ 1 := hle u⁻¹ (by rw [map_inv₀, hvu, inv_one])
  have hsu : Valued.v (s u) = 1 := by
    apply le_antisymm hsu1
    rw [map_inv₀, map_inv₀] at hsu2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v (s u) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero s).2 hu0
    exact (inv_le_one₀ h0).1 hsu2
  rw [hu, map_mul, map_zpow₀, map_mul, map_zpow₀, hvsp] at hsu
  rw [hu, map_mul, map_zpow₀] at hvu
  exact mul_right_cancel₀ hvpk (hsu.trans hvu.symm)

end GlobalTheory.CjInv

namespace GlobalTheory.BCT

theorem cj_involutive_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  intro E _ _ _ w
  have key : (∀ x, cj w (cj w x) = x) ∧ Continuous (cj w) := by
    unfold cj
    split_ifs with h
    · obtain ⟨hc, hE⟩ := h.choose_spec
      refine ⟨fun x => ?_, hc⟩
      have hd := HeightOneSpectrum.denseRange_algebraMap E w
      have := hd.equalizer (hc.comp hc) continuous_id (funext fun y => by
        simp only [Function.comp_apply, id_eq, hE, IsCMField.complexConj_apply_apply])
      exact congrFun this x
    · exact ⟨fun x => rfl, continuous_id⟩
  exact ⟨key.1, GlobalTheory.CjInv.valued_map_eq (cj w) key.2 key.1⟩

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConjugation_involutive_valuation_preserving : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  first | exact @GlobalTheory.BCT.cj_involutive_valuation | exact GlobalTheory.BCT.cj_involutive_valuation | (intros; apply GlobalTheory.BCT.cj_involutive_valuation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.BCT.OrbLev
open Formalism.MainNotions.Gaps.CC.Fib MulAction Function

variable {G : Type} [Group G]

theorem twCent_left (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (y : G) :
    (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * δ * θ y := by
  have h : t * δ = δ * θ t := ht
  have h2 : t⁻¹ * δ * θ t = δ := by rw [mul_assoc, ← h]; group
  calc (t * y)⁻¹ * δ * θ (t * y) = y⁻¹ * (t⁻¹ * δ * θ t) * θ y := by rw [map_mul]; group
    _ = y⁻¹ * δ * θ y := by rw [h2]

theorem Gam_mul (Γ U : Subgroup G) {γ z u : G} (hγ : γ ∈ Γ) (hu : u ∈ U) :
    Gam Γ U (γ * z * u) = (Gam Γ U z).map (MulAut.conj γ).toMonoidHom := by
  ext w
  simp only [Subgroup.mem_map, mem_Gam, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨γ⁻¹ * w * γ, ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) h1) hγ, ?_⟩, by group⟩
    have := U.mul_mem (U.mul_mem hu h2) (U.inv_mem hu)
    convert this using 1; group
  · rintro ⟨v, ⟨h1, h2⟩, rfl⟩
    refine ⟨Γ.mul_mem (Γ.mul_mem hγ h1) (Γ.inv_mem hγ), ?_⟩
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) h2) hu
    convert this using 1; group

theorem Gam_eq_stab {Γ K U : Subgroup G} (hUK : U ≤ K) (x : G) (k : K) :
    Gam Γ U (x * k) = (stabilizer (Gam Γ K x) (k : K ⧸ U.subgroupOf K)).map (Gam Γ K x).subtype := by
  ext w
  constructor
  · intro hw
    let s := (stabEquiv hUK x k).symm ⟨w, hw⟩
    exact ⟨s.1, s.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (stabEquiv hUK x k ⟨a, ha⟩).2

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem conj_mem_cpt (T : Subgroup G) {γ : G} (hγ : γ ∈ T) {t : G}
    (ht : t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}) :
    (MulAut.conj γ).toMonoidHom t ∈ {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))} := by
  obtain ⟨h1, h2⟩ := ht
  let h : G ≃ₜ G := (Homeomorph.mulRight γ⁻¹).trans (Homeomorph.mulLeft γ)
  have hf : ⇑h = ⇑(MulAut.conj γ).toMonoidHom := by
    funext z; simp [h, MulAut.conj_apply, mul_assoc]
  refine ⟨by simpa [MulAut.conj_apply] using T.mul_mem (T.mul_mem hγ h1) (T.inv_mem hγ), ?_⟩
  rw [← MonoidHom.map_zpowers, Subgroup.coe_map, ← hf, ← h.image_closure]
  exact h2.image h.continuous

theorem cptPart_map_conj (T : Subgroup G) {γ : G} (hγ : γ ∈ T) :
    (cptPart T).map (MulAut.conj γ).toMonoidHom = cptPart T := by
  apply le_antisymm
  · rw [cptPart, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_cpt T hγ ht
  · rw [cptPart, Subgroup.closure_le]
    intro t ht
    refine ⟨(MulAut.conj γ⁻¹).toMonoidHom t, Subgroup.subset_closure (conj_mem_cpt T (T.inv_mem hγ) ht), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_sigma_of_finite {ι : Type} {β : ι → Type} [∀ i, Finite (β i)] (h : (Σ i, β i) → ℂ)
    (hh : (support h).Finite) : ∑ᶠ p, h p = ∑ᶠ i, ∑ᶠ b, h ⟨i, b⟩ := by
  letI : ∀ i, Fintype (β i) := fun i => Fintype.ofFinite _
  set I := hh.toFinset.image Sigma.fst
  have h1 : support h ⊆ ((I.sigma fun _ => Finset.univ : Finset (Σ i, β i)) : Set _) := by
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, and_true, I, Finset.mem_image]
    exact ⟨p, hh.mem_toFinset.2 hp, rfl⟩
  have h2 : (support fun i => ∑ᶠ b, h ⟨i, b⟩) ⊆ (I : Set ι) := by
    intro i hi
    obtain ⟨b, hb⟩ : ∃ b, h ⟨i, b⟩ ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi (finsum_eq_zero_of_forall_eq_zero hc)
    simp only [Finset.mem_coe, I, Finset.mem_image]
    exact ⟨⟨i, b⟩, hh.mem_toFinset.2 hb, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_eq_sum_of_fintype]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem finsum_orbits {H X : Type} [Group H] [MulAction H X] [Finite X] (φ : X → ℂ)
    (hφ : ∀ (h : H) y, φ (h • y) = φ y) :
    ∑ᶠ y, φ y = ∑ᶠ ω : orbitRel.Quotient H X, ((orbit H ω.out).ncard : ℂ) * φ ω.out := by
  letI : Fintype X := Fintype.ofFinite X
  haveI : Finite (orbitRel.Quotient H X) := Quotient.finite _
  letI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ (fun y => (Quotient.mk'' y : orbitRel.Quotient H X)) φ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmem : ∀ y, (Quotient.mk'' y : orbitRel.Quotient H X) = ω ↔ y ∈ orbit H ω.out := by
    intro y
    conv_lhs => rw [← Quotient.out_eq' ω]
    rw [Quotient.eq'']
    exact orbitRel_apply
  have hc : ∀ y ∈ Finset.univ.filter (fun y => (Quotient.mk'' y : orbitRel.Quotient H X) = ω), φ y = φ ω.out := by
    intro y hy
    obtain ⟨h, rfl⟩ := (hmem y).1 (Finset.mem_filter.1 hy).2
    exact hφ h _
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Set.ncard_coe_finset]
  congr 1
  ext y
  simp [hmem]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem avg_const' {H : Type} [Group H] (u : H → ℂ) (c : ℂ) (hu : ∀ h, u h = c) : avg u = c := by
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H u ⊤ (fun k _ => show ∀ x, u (x * k) = u x from fun x => by rw [hu, hu]) (by simp)]
  simp only [hu, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  exact finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx)

theorem twOrb_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  intro G _ _ _ θ K _hKo hKc _hθK K' hL δ f hf hT hfin
  obtain ⟨hK'o, hK'K, hθK'⟩ := hL
  set T := twCent θ δ with hTdef
  set C := cptPart T with hCdef
  let F : G → ℂ := fun y => f (y⁻¹ * δ * θ y)
  have FT : ∀ t ∈ T, ∀ y, F (t * y) = F y := fun t ht y => by simp only [F, twCent_left θ δ ht y]
  have FK : ∀ y, ∀ k ∈ K', F (y * k) = F y := by
    intro y k hk
    simp only [F]
    have e : (y * k)⁻¹ * δ * θ (y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [map_mul]; group
    rw [e, (hf.2 _ (hθK' k hk) _).2, (hf.2 _ (K'.inv_mem hk) _).1]
  let g : DoubleCoset.Quotient (T : Set G) (K' : Set G) → ℂ := fun q =>
    (((T ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * F (Quotient.out q)
  have hsecond : twOrb θ K' δ f = ∑ᶠ q, g q := by
    unfold twOrb
    refine finsum_congr fun q => ?_
    congr 1
    exact avg_const' _ _ fun k => FK _ k k.2
  refine ⟨?_, hsecond⟩
  rw [hsecond]
  set S := K'.subgroupOf K with hSdef
  have hn : K'.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
    have ho : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := by
      rw [Subgroup.coe_subgroupOf]; exact hK'o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  haveI : S.FiniteIndex := ⟨hn⟩
  haveI : Finite (K ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  have avgK : ∀ x : G, avg (fun k : K => F (x * k)) = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ y : K ⧸ S, F (x * (Quotient.out y : K)) := by
    intro x
    refine GlobalTheory.T.avg_eq_of_le_rightStabiliser K _ S (fun k hk => show ∀ z : K, F (x * ((z * k : K) : G)) = F (x * z) from fun z => ?_) hn
    rw [Subgroup.coe_mul, ← mul_assoc]
    exact FK _ _ (Subgroup.mem_subgroupOf.1 hk)
  let e := fib (Γ := T) (K := K) hK'K
  haveI hfo : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G), Finite (orbitRel.Quotient (Gam T K (Quotient.out c)) (K ⧸ S)) :=
    fun c => Quotient.finite _
  have hc : ∀ c : DoubleCoset.Quotient (T : Set G) (K : Set G),
      (((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
        ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K)) = ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
    intro c
    have hwK : T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom = Gam T K (Quotient.out c) :=
      (Gam_eq_map T K _).symm
    rw [hwK]
    have hφ : ∀ (h : Gam T K (Quotient.out c)) (y : K ⧸ S),
        F (Quotient.out c * (Quotient.out (h • y) : K)) = F (Quotient.out c * (Quotient.out y : K)) := by
      intro h y
      have e1 : ((Quotient.out (h • y) : K) : K ⧸ S) =
          ((toK T K (Quotient.out c) h * Quotient.out y : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      have hu := mk_eq_iff.1 e1.symm
      have e2 : Quotient.out c * ((Quotient.out (h • y) : K) : G) = (h : G) * (Quotient.out c * (Quotient.out y : K)) *
          (((toK T K (Quotient.out c) h * Quotient.out y : K) : G)⁻¹ * (Quotient.out (h • y) : K)) := by
        rw [Subgroup.coe_mul, toK_coe]; group
      rw [e2, FK _ _ hu, FT _ (mem_Gam.1 h.2).1]
    rw [finsum_orbits (fun y : K ⧸ S => F (Quotient.out c * (Quotient.out y : K))) hφ, mul_finsum]
    refine finsum_congr fun ω => ?_
    have hq : e.symm ⟨c, ω⟩ = DoubleCoset.mk T K' (Quotient.out c * (Quotient.out ω.out : K)) := by
      have : ω = Quotient.mk'' ((Quotient.out ω.out : K) : K ⧸ S) := by
        rw [QuotientGroup.out_eq', Quotient.out_eq']
      have h := fibRep_symm_mk hK'K Quotient.out (DoubleCoset.out_eq' (H := T) (K := K)) c (Quotient.out ω.out)
      rw [← this] at h
      exact h
    obtain ⟨γ, hγ, u, hu, hout⟩ := (@DoubleCoset.eq _ _ T K' (Quotient.out c * (Quotient.out ω.out : K))
      (Quotient.out (e.symm ⟨c, ω⟩))).1 (by rw [DoubleCoset.out_eq', hq])
    have hF : F (Quotient.out (e.symm ⟨c, ω⟩)) = F (Quotient.out c * (Quotient.out ω.out : K)) := by
      rw [hout, FK _ _ hu, FT _ hγ]
    have hCc : C.map (MulAut.conj γ).toMonoidHom = C := cptPart_map_conj T hγ
    have h1 := Subgroup.relIndex_map_map_of_injective (Gam T K' (Quotient.out c * (Quotient.out ω.out : K))) C
      (f := (MulAut.conj γ).toMonoidHom) (MulAut.conj γ).injective
    rw [hCc] at h1
    have h2 : ((stabilizer (Gam T K (Quotient.out c)) ω.out).map (Gam T K (Quotient.out c)).subtype).subgroupOf
        (Gam T K (Quotient.out c)) = stabilizer (Gam T K (Quotient.out c)) ω.out :=
      Subgroup.comap_map_eq_self_of_injective (Gam T K (Quotient.out c)).subtype_injective _
    have hHC : Gam T K (Quotient.out c) ≤ C := by rw [← hwK]; exact (hT _).1
    have hw : (T ⊓ K'.map (MulAut.conj (Quotient.out (e.symm ⟨c, ω⟩))).toMonoidHom).relIndex C =
        (orbit (Gam T K (Quotient.out c)) ω.out).ncard * (Gam T K (Quotient.out c)).relIndex C := by
      rw [← Gam_eq_map, hout, Gam_mul T K' hγ hu, h1, Gam_eq_stab hK'K, QuotientGroup.out_eq',
        ← Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_subtype_le _) hHC, Subgroup.relIndex, h2,
        index_stabilizer]
    simp only [g]
    rw [hw, hF]
    push_cast
    ring
  have hsupp : (support fun p => g (e.symm p)).Finite := by
    refine (hfin.preimage e.symm.injective.injOn).subset ?_
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h0
    exact hp (by simp only [g]; rw [show F (Quotient.out (e.symm p)) = 0 from h0, mul_zero])
  calc twOrb θ K δ f
      = ∑ᶠ c : DoubleCoset.Quotient (T : Set G) (K : Set G), ((K'.relIndex K : ℕ) : ℂ)⁻¹ *
          ((((T ⊓ K.map (MulAut.conj (Quotient.out c)).toMonoidHom).relIndex C : ℕ) : ℂ) *
            ∑ᶠ y : K ⧸ S, F (Quotient.out c * (Quotient.out y : K))) := by
        unfold twOrb
        refine finsum_congr fun c => ?_
        rw [avgK]; ring
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ c, ∑ᶠ ω, g (e.symm ⟨c, ω⟩) := by
        rw [← mul_finsum]; congr 1; exact finsum_congr hc
    _ = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q, g q := by
        rw [← finsum_sigma_of_finite _ hsupp, finsum_comp_equiv e.symm]

end GlobalTheory.BCT.OrbLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  first | exact @GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | exact GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | (intros; apply GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.PhaseRational

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem eq_of_out {V : HSp D} {F F' : GA D V → ℂ} (hF : ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g)
    (hF' : ∀ γ ∈ GQ V, ∀ g, F' (γ * g) = F' g) (h : ∀ q : AutQ V, F q.out = F' q.out) (g : GA D V) : F g = F' g := by
  let q : AutQ V := Quotient.mk _ g
  have hq : (QuotientGroup.rightRel (GQ V)) g q.out := (QuotientGroup.rightRel (GQ V)).iseqv.symm (Quotient.exact (Quotient.out_eq q))
  rw [QuotientGroup.rightRel_apply] at hq
  have e : q.out = (q.out * g⁻¹) * g := by group
  have h1 := h q
  rw [e, hF _ hq, hF' _ hq] at h1
  exact h1

theorem mult_leftInv {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {T : MMap M} (hT : T ∈ Mult.Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  intro γ hγ g
  induction hT using Submodule.span_induction with
  | mem T h => exact (h.aut v).toIsAutFun.1 γ hγ g
  | zero => rfl
  | add T T' _ _ h h' => simp [h, h']
  | smul c T _ h => simp [h]

theorem adel_muPin_leftInv {C : Core D} (hL : LawsM C) {j : ℕ} (hj : InR D j) {σ : C.Q.c.F →+* ℂ} (hσ : GoodEmb C.Q.c σ)
    {W : HSp D} (hV : C.V j σ = W) (cc : (C.U j σ).Comp → ℂ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {f : C.R j} (hf : f ∈ sec (C.Q.Xo j) C.Q.c a n) : ∀ γ ∈ GQ W, ∀ g,
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) (γ * g) =
    adel W (castDict hV (C.dict j σ)) (muPin W (castDict hV (C.dict j σ)) (castDict hV (C.mu j σ)) cc) (rdU (C.U j σ) f) g := by
  subst hV
  intro γ hγ g
  obtain ⟨th, hr, -, hD⟩ := hL.dictU j hj σ hσ
  have h1 := rdU_leftInv (C.U j σ) (C.V j σ) (C.dict j σ) (C.mu j σ) (C.Kf j σ) th hr (hL.unf j hj σ hσ) hD
    (hL.muUnit j hj σ hσ) hd (hL.chiTriv j hj σ hσ a n hd) hf γ hγ g
  obtain ⟨γ', -, he⟩ := hD.1 γ hγ g
  have h2 : (C.dict j σ (γ * g)).1 = (C.dict j σ g).1 := by rw [he]
  show cc (C.dict j σ (γ * g)).1 * C.mu j σ (γ * g) * _ = cc (C.dict j σ g).1 * C.mu j σ g * _
  rw [mul_assoc, mul_assoc]
  exact congrArg₂ (· * ·) (congrArg cc h2) h1

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem finiteGroup_acts_by_lift_translation_principalType {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (g : G)
    (hg : ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) :
    ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k ∧ ∀ F h,
      Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = F (h * k) := by
  refine ⟨hg.choose, hg.choose_spec, fun F h => ?_⟩
  have h1 : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) hg.choose = 1 := by
    unfold Lev.levChi levFn
    have : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) hg.choose)) = 1 := Lev.subgroupCharExtension_one_apply _ _
    rw [this]
    simp [Lev.flagL, Lev.withP, LevCh.datWp, Lev.datY]
  show Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) F h = _
  unfold Lev.actG0
  rw [dif_pos hg]
  simp only [h1, inv_one, one_mul]

theorem rdU_of_isBC {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ i, σ' (as i) * rdU (U (σ'.comp (incF c c' hle))) (fs i) k x := by
  classical
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · let _ : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have h1 := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x =
      toC (evR Xo c (fs i) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := fun i => dif_pos hx
    simp only [e2]
    rw [e1]
    exact h1
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    have e2 : ∀ i, rdU (U (σ'.comp (incF c c' hle))) (fs i) k x = 0 := fun i => dif_neg hx
    simp only [e2, e1, mul_zero, Finset.sum_const_zero]

theorem row_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    (lev : Γ → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (hL : ActLev (Xo := Xo) c lev)
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (hrow : OneMapRow Xo c' V (unfBC hle U σ') dict mu xr a (actLev c' lev) dδ Cl' w La Nc gam vol ep io thAd Pl LL
      (cusp Xo c' (unfBC hle U) a n) cc ph) (t : Tup) (x : Cl' t → Vs) (hx : Pl t x) :
    ∃ (z : Γ) (ze : ℂ) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), ze ∈ LL ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
      ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
        adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k))) q.out) := by
  obtain ⟨-, -, z, -, hrow⟩ := hrow
  obtain ⟨ze, hze, -, hrow⟩ := hrow t
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC D.host.E H Dw l Xo c c' hle).2 r U a n f' hf'
  have hBCz := (GlobalTheory.FieldBC.actLev_and_actBC D H Dw l Xo c c' hle Γ lev hL).2 a n z m as fs f' hf's
    (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨z, ze, m, as, fs, hze, hfs, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (actLev c' lev z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (actLev c lev z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

theorem placed_of_pins {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}
    {K' : Type} [Field K'] {σ' : K' →+* ℂ} {t : T0} {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {bad : ℕ} {Mb I : Ideal (𝓞 D.host.E)} {N : Submodule (𝓞 D.host.E) La} {Cl : Type} [Fintype Cl]
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    {B : Ideal (𝓞 D.host.E) → K'} {xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}
    {φ : (Fin (Vc D i).rank → La ⧸ N) → K'} {thAd : (Cl → VsV D i K') → AutQ (Wc D i) → ℂ}
    {Plc : (Cl → VsV D i K') → Prop} (h : ThPinsT R i σ' t v₀ c0' ι bad Mb I N Lh gam vol B xi φ thAd Plc)
    (x : A.fam.amb.FL i t) : ∃ y, Plc y ∧ ∀ q, thAd y q = R.thF i t (jVx R i t x) v₀ q.out :=
  h.reps.elim fun _ h => h.elim fun _ h => (h.2.1 x).imp fun y hy =>
    ⟨(h.2.2.2 y).2 ⟨x, hy⟩, fun q => congrFun (h.2.2.1 _ y hy) q⟩

theorem comb_fin {K M X ι : Type} [Fintype ι] (e : K → ℂ) (P : M → X → ℂ) (F : X → ℂ) (a : ι → K) (f : ι → M)
    (h : ∀ x, F x = ∑ k, e (a k) * P (f k) x) :
    ∃ (n : ℕ) (a : Fin n → K) (f : Fin n → M), ∀ x, F x = ∑ k, e (a k) * P (f k) x :=
  ⟨Fintype.card ι, fun k => a ((Fintype.equivFin ι).symm k), fun k => f ((Fintype.equivFin ι).symm k), fun x =>
    (h x).trans ((Fintype.equivFin ι).symm.sum_comp fun k => e (a k) * P (f k) x).symm⟩

section Main

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev IdentityAt (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i)
    (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io
    O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

theorem lift_rational (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hmem : R.thP_thF_mem)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) (t : Tp) (t₀ : T0) (ht : tup t = t₀)
    (x : A.fam.amb.FL i t₀) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.thF i t₀ (jVx R i t₀ x) v₀ h =
        ∑ k, D.what₂.embLL (a k) * ((lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  revert x
  refine ht.rec fun x => ?_
  have hrk : (Vc D i).rank = κ.n := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).trans hn.symm
  refine (placed_of_pins (hpins.tuple t) x).elim fun y hy => ?_
  refine (row_baseChange O.hle (C.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu
    (xiR D) (wtA κ) O.lev2 hpins.act.1 hid t y hy.1).elim fun z h => h.elim fun ze h => h.elim fun m h => h.elim fun as h =>
      h.elim fun fs h => h.1.elim fun ze' hze' => (hpins.lift.lev z).elim fun kz hkz => ?_
  have hz : ∀ k, actLev C.Q.c O.lev2 z (fs k) ∈ C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n := fun k =>
    (hequiv z kz hkz.1 (fs k) (hrk ▸ h.2.1 k)).1
  have has : ∀ k, ∃ b : D.what₂.LL, D.what₂.embLL b = inC O.c' (as k) := fun k => hF.le (as k).2
  refine ⟨m, fun k => ze' * (has k).choose, fun k => ⟨_, hz k⟩, ?_⟩
  refine eq_of_out (V := Wc D i) (fun γ hγ g => ?_) (fun γ hγ g => ?_) fun q => ?_
  · exact congrArg (ph * ·) (mult_leftInv (hmem i (tup t) _) v₀ γ hγ g)
  · refine Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (congrArg (_ * ·) ?_)
    exact adel_muPin_leftInv hlaws ⟨Nat.le_add_left _ _, i.2⟩ (σ := O.s0) C.good_σ₀ O.hV cc (dom_wtA κ)
      (cusp_le_sec _ _ _ _ _ (hz k)) γ hγ g
  · refine (congrArg (ph * ·) (hy.2 q)).symm.trans ((h.2.2 q).trans ?_)
    refine Finset.sum_congr rfl fun k _ => congrArg (· * _) ?_
    exact (congrArg₂ (· * ·) hze' (has k).choose_spec).symm.trans (map_mul D.what₂.embLL _ _).symm

theorem proj_rational (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (s ph : ℂ)
    (hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) (hchi : R.grp_chiW)
    (hequiv : O.EquivAt κ cc) (F : GA D (Wc D i) → ℂ) (n : ℕ) (a : Fin n → D.what₂.LL)
    (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n)
    (hF : ∀ h, ph * F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h)) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n), ∀ h,
      ph * R.eWf i (sg0 D A) F h = ∑ k, D.what₂.embLL (a k) * (s * O.phi cc (f k : C.R ((i : ℕ) + 1)) h) := by
  have hact := fun g => finiteGroup_acts_by_lift_translation_principalType R i g (hlift g)
  have heq := fun g (k : Fin n) => hequiv g _ (hact g).choose_spec.1 _ (f k).2
  refine comb_fin D.what₂.embLL
    (fun (u : C.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) h => s * O.phi cc (u : C.R ((i : ℕ) + 1)) h)
    (fun h => ph * R.eWf i (sg0 D A) F h)
    (fun p : G × Fin n => (idemOf A.X).coeff p.1 * ((((R.FW i).chi p.1)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) * a p.2)
    (fun p => ⟨_, (heq p.1 p.2).1⟩) fun h => ?_
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have h1 : R.eWf i (sg0 D A) F h = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) * F (h * (hact g).choose) := by
    unfold RealDat.eWf gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← (hact g).choose_spec.2 F h, ← hs]
    rfl
  rw [h1, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_left_comm, hF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := ((heq g k).2 h).trans (congrArg (· * _) (hchi i g).symm)
  have h3 : D.what₂.embLL ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) *
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  dsimp only
  rw [h2, map_mul, map_mul]
  linear_combination (-(D.what₂.embLL ((idemOf A.X).coeff g) * D.what₂.embLL (a k) * s *
    O.phi cc (f k : C.R ((i : ℕ) + 1)) (h * (hact g).choose))) * h3

theorem phRat_of_identity (v₀ : (R.MW i (sg0 D A)).Vec) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ)
    {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (t : Tp) (ht : tup t = A.μ0)
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hpins : O.Pins κ v₀ ι x₀)
    (hlaws : LawsM C) (hn : κ.n = D.R.nV) (hchi : R.grp_chiW) (hmem : R.thP_thF_mem) (hG : R.thP_thG)
    (hequiv : O.EquivAt κ cc) (hid : IdentityAt O κ cc ph) : O.PhRat κ v₀ cc ph := by
  have key := lift_rational O κ v₀ cc ph hF hpins hlaws hn hmem hequiv hid t A.μ0 ht
  intro x
  refine (key x).elim fun n h => h.elim fun a h => h.elim fun f h => ?_
  have h1 := proj_rational O κ cc _ ph (fun g => (hpins.lift.lev g).imp fun _ hk => hk.1) hchi hequiv _ n a f h
  refine h1.imp fun _ h2 => h2.imp fun _ h2 => h2.imp fun _ h2 g => Eq.trans (congrArg (ph * ·) ?_) (h2 g)
  exact congrArg (fun S : MMap (R.MW i (sg0 D A)) => S v₀ g) (hG i A.μ0 (jVx R i A.μ0 x))

end Main

section Class

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m)

end Class

end GlobalTheory.PhaseRational
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocAE

theorem mem_GLint_of_entries_inv {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n),
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  intro E _ _ _ _ n x
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries_inv _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

end GlobalTheory.BCT.LocAE
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegraStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU (E := E) (n := n), ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  first | exact @GlobalTheory.BCT.LocAE.eventually_mem_KL | exact GlobalTheory.BCT.LocAE.eventually_mem_KL | (intros; apply GlobalTheory.BCT.LocAE.eventually_mem_KL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffAt_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  intro F _ σ X e he f y hy hf
  obtain ⟨W, ι, hι, g, Φ, O, hyW, hO, hgO, hΦ, hfeq⟩ := hf

  have hU : IsOpen (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W) :=
    e.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn W)
  have hyU : e y ∈ e.target ∩ e.symm ⁻¹' ptsIn X.str σ W :=
    ⟨e.map_source hy, by rw [Set.mem_preimage, e.left_inv hy]; exact hyW⟩

  have hGc : ContDiffAt ℂ ∞ (fun v a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) := by
    rw [contDiffAt_pi]
    intro a
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ hU (he W (g a))).contDiffAt
      (hU.mem_nhds hyU)

  have hΦc : ContDiffAt ℝ ∞ Φ (fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm (e y))) := by
    rw [e.left_inv hy]
    exact hΦ.contDiffAt (hO.mem_nhds hgO)
  have hcomp : ContDiffAt ℝ ∞ (fun v => Φ fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) :=
    hΦc.comp (e y) (hGc.restrict_scalars ℝ)
  refine hcomp.congr_of_eventuallyEq ?_

  have ht : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have h := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at h
    exact h
  exact ht.eventually hfeq

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAtStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  first | exact @GlobalTheory.GoodTop.contDiffAt_holoChart | exact GlobalTheory.GoodTop.contDiffAt_holoChart | (intros; apply GlobalTheory.GoodTop.contDiffAt_holoChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwTrUnit

theorem trace_eq_zero_of_finrank_eq_zero (W : Type) [AddCommGroup W] [Module ℂ W] (h : Module.finrank ℂ W = 0)
    (L : W →ₗ[ℂ] W) : LinearMap.trace ℂ W L = 0 := by
  by_cases hW : Module.Finite ℂ W
  · haveI : Subsingleton W := Module.finrank_zero_iff.1 h
    rw [show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · unfold LinearMap.trace
    rw [dite_eq_right]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem isHecke_indicator {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) :
    IsHecke K' ((K' : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K' : Set G) := K'.isClosed_of_isOpen ho
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset hcl hle
  refine ⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · have : k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_left hk
    simp only [Set.indicator_apply, this, Pi.one_apply]
  · have : x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_right hk
    simp only [Set.indicator_apply, this, Pi.one_apply]

theorem twTr_indicator {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) : twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) := by
  obtain ⟨x₀, hx₀, hL⟩ := GlobalTheory.TwTrLin.levOp_unit ρ K K'
  have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀
  have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [hL, LinearMap.smul_apply, hfx v hv]
    exact Submodule.smul_mem _ _ hv
  rw [GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]
  have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext x
    simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
  rw [hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]

theorem twTr_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  intro E _ _ _ n w K' hlev σ
  have hKc := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1,
    twTr_indicator _ _ _, fun h g => ?_⟩
  unfold twTr
  split_ifs with hm
  · exact trace_eq_zero_of_finrank_eq_zero _ h _
  · rfl

end GlobalTheory.TwTrUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTrace_indicator_level_localUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  first | exact @GlobalTheory.TwTrUnit.twTr_unit | exact GlobalTheory.TwTrUnit.twTr_unit | (intros; apply GlobalTheory.TwTrUnit.twTr_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FiberTwo

theorem eq_or_eq_of_under_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E) (hu : u ≠ w)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)))
    (h' : u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u' = w ∨ u' = u := by
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hc := IsCMField.complexConj_ne_one (K := E)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u).1 h with h1 | h1
  · exact absurd h1 hu
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u').1 h' with h2 | h2
  · exact Or.inl h2
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h2 h1)

end GlobalTheory.BCT.FiberTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u' = w ∨ u' = u := by
  first | exact @GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | (intros; apply GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq <;> assumption)
end
end
