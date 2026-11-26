module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.EmbeddingValuationsAnti
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideWithE

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NodupIntShift
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

namespace GlobalTheory.RowRegAlg

theorem nodup_int_shift (R : Ranks) (S : Multiset ℂ) (hn : S.Nodup) (hi : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    S.Nodup ∧ ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ) + ((R.r : ℂ) - 1) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, R.r = 2 * c + 1 := ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  refine ⟨hn, fun z hz => ?_⟩
  obtain ⟨n, rfl⟩ := hi z hz
  refine ⟨n - c, ?_⟩
  rw [hc]
  push_cast
  ring

theorem ralg_of_infG : ∀ (D : D7) (π : D.naut.CG D.R.r),
    (∀ τ : D.what₂.Tau, D.naut.infG π (embTau D τ) = hcSigma (D.hc τ) ∧
      D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z)) →
    D.naut.ralg π := by
  intro D π h
  rw [D.naut.ralg_def]
  intro φ
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = embTau D τ := hτ
    rw [e, (h τ).1]
    exact nodup_int_shift D.R _ (GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _) (hcSigma_int _)
  · have e : φ = embTauBar D τ := hτ
    rw [e, (h τ).2]
    refine nodup_int_shift D.R _ ((GlobalTheory.Survey.EmbeddingValuationsAnti.nodup_hcSigma _).map neg_injective) fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨n, rfl⟩ := hcSigma_int _ y hy
    exact ⟨-n, by push_cast; ring⟩

end GlobalTheory.RowRegAlg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspOfGoodRow
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings Polynomial

noncomputable section

namespace GlobalTheory.RowCuspLabels

theorem cusp_of_goodRow : ∀ (D : D7) (S : GlobalTheory.HeightCounting.RowSide D), Formalism.MainNotions.SumRepresentations.At.TieLab D.nd D.naut → ∀ (σ : D.what₂.FT),
  D.nd.goodRow σ → ∀ (Sig : List (Part D.naut.CG)), (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) →
  rankIso D.nd D.naut Sig = D.R.r →
  (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = S.locR σ w) →
  IsCuspIso D.nd D.naut Sig := by
  intro D S hT σ hg Sig hpos hrank hloc
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.ord
    have := D.R.toFrame.ord_pos
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.nd.lab k σ v = ∏ j : Fin Sig.length,
      D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [S.lab_eq k σ v, ← hloc _ (GlobalTheory.Proof.SplitPlaceGoodSignature.typePlSplit D.nd D.naut k v),
      Formalism.MainNotions.SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT,
      Formalism.MainNotions.SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, Formalism.MainNotions.SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      rw [hrk, ← (h1 v).2.1, hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r (D.nd.lab k σ)
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

end GlobalTheory.RowCuspLabels

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

end GlobalTheory.RowCuspFromLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCusp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCusp
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSStrict

theorem qpow (q : ℕ) (x : ℝ) : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
  simp

theorem pair_val (q : ℕ) (γ : ℂˣ) (x : ℝ) :
    (γ : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ) * (q : ℂ) ^ (-(x : ℂ)) =
      ((‖(γ : ℂ)‖ ^ 2 * (q : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [qpow]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_conjU (γ : ℂˣ) : ‖((Units.map (starRingEnd ℂ).toMonoidHom γ : ℂˣ) : ℂ)‖ = ‖(γ : ℂ)‖ := by
  simp

theorem hasProd_split {ι : Type*} [DecidableEq ι] (f : ι → ℂ) (T : Finset ι) (w : ι) (hw : w ∉ T) {A B : ℂ}
    (h1 : HasProd (fun v : {v : ι // v ∉ T} => f v.1) A)
    (h2 : HasProd (fun v : {v : ι // v ∉ insert w T} => f v.1) B) : A = f w * B := by
  have h1' : HasProd ({v | v ∉ T}.mulIndicator f) A :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ T})).mp h1
  have h2' : HasProd ({v | v ∉ insert w T}.mulIndicator f) B :=
    (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ insert w T})).mp h2
  have h3 : HasProd (({w} : Set ι).mulIndicator f) (f w) := by
    have := hasProd_single (f := ({w} : Set ι).mulIndicator f) w (fun b hb => by simp [Set.mulIndicator_apply, hb])
    simpa using this
  have h4 := h3.mul h2'
  have heq : (fun v => ({w} : Set ι).mulIndicator f v * {v | v ∉ insert w T}.mulIndicator f v) =
      {v | v ∉ T}.mulIndicator f := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [Set.mulIndicator_apply, hw]
    · by_cases hvT : v ∈ T <;> simp [Set.mulIndicator_apply, hv, hvT]
  rw [heq] at h4
  exact h1'.unique h4

theorem half_pow_le_norm_prod {α : Type*} (g : α → ℂ) (m : Multiset α) (h : ∀ p ∈ m, (1/2 : ℝ) ≤ ‖g p‖) :
    (1/2 : ℝ) ^ Multiset.card m ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun p hp => h p (Multiset.mem_cons_of_mem hp))
    calc (1/2 : ℝ) ^ Multiset.card s * (1/2) = (1/2) * (1/2) ^ Multiset.card s := mul_comm _ _
      _ ≤ _ := mul_le_mul ha hs (by positivity) (norm_nonneg _)

theorem half_le_norm_inv_one_sub {z : ℂ} (hz : ‖z‖ < 1) : (1/2 : ℝ) ≤ ‖(1 - z)⁻¹‖ := by
  have hpos : 0 < ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simp at this; linarith
  have hle : ‖1 - z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) z
    simp at this; linarith
  rw [norm_inv, one_div]
  exact inv_anti₀ hpos hle

def gfac (q : ℕ) (x : ℝ) (p : ℂˣ × ℂˣ) : ℂ := (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹

theorem locL_eq (q : ℕ) (B B' : Multiset ℂˣ) (x : ℝ) : locL q B B' (x : ℂ) = ((B ×ˢ B').map (gfac q x)).prod := rfl

theorem norm_sq_lt_absNorm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a →
    σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w,
      ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  intro E _ _ _ a σ ha hσ T hT w hw α hα
  classical
  obtain ⟨L1, hL1, -, c1, hc1, hlim1⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  have hT' : UnrOutside (insert w T) σ := fun v hv => hT v (fun h => hv (Finset.mem_insert_of_mem h))
  obtain ⟨L2, hL2, -, c2, hc2, hlim2⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ (insert w T) hT'
  have hsplit : ∀ x : ℝ, 1 < x → (L1 x : ℂ) = ((sat σ w ×ˢ (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom)).map
      (gfac (Ideal.absNorm w.asIdeal) x)).prod * (L2 x : ℂ) := by
    intro x hx
    rw [← locL_eq]
    have e := hasProd_split (ι := HeightOneSpectrum (𝓞 E)) (fun v : HeightOneSpectrum (𝓞 E) => locL (Ideal.absNorm v.asIdeal)
      (sat σ v) ((sat σ v).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) T w hw (hL1 x hx).1 (hL2 x hx).1
    exact e
  generalize hB' : (sat σ w).map (Units.map (starRingEnd ℂ).toMonoidHom) = B' at hsplit
  have hmem : ∀ γ ∈ sat σ w, (γ, Units.map (starRingEnd ℂ).toMonoidHom γ) ∈ (sat σ w) ×ˢ B' := fun γ hγ =>
    Multiset.mem_product.mpr ⟨hγ, hB' ▸ Multiset.mem_map_of_mem _ hγ⟩
  generalize hqd : Ideal.absNorm w.asIdeal = q at hsplit ⊢
  have hq1 : (1 : ℝ) < q := by rw [← hqd]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < q := by linarith

  have hle : ∀ γ ∈ sat σ w, ‖(γ : ℂ)‖ ^ 2 ≤ (q : ℝ) := by
    intro γ hγ
    by_contra hlt
    push_neg at hlt
    have hγ0 : (0 : ℝ) < ‖(γ : ℂ)‖ ^ 2 := by
      have : (γ : ℂ) ≠ 0 := γ.ne_zero
      positivity
    have hlogq : 0 < Real.log q := Real.log_pos hq1
    set x0 := Real.log (‖(γ : ℂ)‖ ^ 2) / Real.log q with hx0def
    have hx0 : 1 < x0 := by
      rw [hx0def, lt_div_iff₀ hlogq, one_mul]
      exact Real.log_lt_log hq0 hlt
    have hpow : (q : ℝ) ^ (-x0) = (‖(γ : ℂ)‖ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hq0.le, Real.rpow_def_of_pos hq0]
      congr 1
      have : Real.log q * x0 = Real.log (‖(γ : ℂ)‖ ^ 2) := by
        rw [hx0def]; field_simp
      rw [this, Real.exp_log hγ0]
    have hF0 : ((sat σ w ×ˢ B').map (gfac q x0)).prod = 0 := by
      apply Multiset.prod_eq_zero
      refine Multiset.mem_map.mpr ⟨(γ, Units.map (starRingEnd ℂ).toMonoidHom γ), hmem γ hγ, ?_⟩
      simp only [gfac]
      rw [pair_val, hpow, mul_inv_cancel₀ hγ0.ne']
      simp
    have h := hsplit x0 hx0
    rw [hF0, zero_mul] at h
    have h1 := (hL1 x0 hx0).2
    have : L1 x0 = 0 := by exact_mod_cast h
    linarith
  by_contra hnot
  push_neg at hnot
  have heq : ‖(α : ℂ)‖ ^ 2 = q := le_antisymm (hle α hα) hnot
  set t : ℝ → ℝ := fun x => (q : ℝ) * (q : ℝ) ^ (-x) with ht
  have ht1 : ∀ x, 1 < x → t x < 1 := by
    intro x hx
    have : (q : ℝ) ^ (1 + -x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    rwa [Real.rpow_add hq0, Real.rpow_one] at this
  obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem (hmem α hα)

  have hlow : ∀ x, 1 < x → (1/2 : ℝ) ^ Multiset.card rest ≤
      (1 - t x) * ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ := by
    intro x hx
    have hspec : gfac q x (α, Units.map (starRingEnd ℂ).toMonoidHom α) = (((1 - t x : ℝ) : ℂ))⁻¹ := by
      simp only [gfac]
      rw [pair_val, heq]
      simp only [ht]
      push_cast
      ring
    have hrestb : ∀ p ∈ rest, (1/2 : ℝ) ≤ ‖gfac q x p‖ := by
      intro p hp
      have hp' : p ∈ (sat σ w) ×ˢ B' := by
        rw [hrest]; exact Multiset.mem_cons_of_mem hp
      obtain ⟨hp1, hp2⟩ := Multiset.mem_product.mp hp'
      rw [← hB'] at hp2
      obtain ⟨β, hβ, hβe⟩ := Multiset.mem_map.mp hp2
      have hb1 := hle p.1 hp1
      have hb2 := hle β hβ
      have hn2 : ‖(p.2 : ℂ)‖ = ‖(β : ℂ)‖ := by rw [← hβe]; exact norm_conjU β
      have hprod : ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ ≤ q := by
        rw [hn2]
        nlinarith [sq_nonneg (‖(p.1 : ℂ)‖ - ‖(β : ℂ)‖), norm_nonneg (p.1 : ℂ), norm_nonneg (β : ℂ)]
      apply half_le_norm_inv_one_sub
      rw [qpow, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hq0.le _)]
      calc ‖(p.1 : ℂ)‖ * ‖(p.2 : ℂ)‖ * (q : ℝ) ^ (-x) ≤ q * (q : ℝ) ^ (-x) :=
            mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hq0.le _)
        _ < 1 := ht1 x hx
    have hpos : 0 < 1 - t x := by linarith [ht1 x hx]
    rw [hrest, Multiset.map_cons, Multiset.prod_cons, norm_mul, hspec, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    exact half_pow_le_norm_prod (gfac q x) rest hrestb

  have hnorm : ∀ x, 1 < x → ‖((sat σ w ×ˢ B').map (gfac q x)).prod‖ = ((x - 1) * L1 x) / ((x - 1) * L2 x) := by
    intro x hx
    have h := hsplit x hx
    have hL2pos : 0 < L2 x := by linarith [(hL2 x hx).2]
    have hL1pos : 0 < L1 x := by linarith [(hL1 x hx).2]
    have hFx : ((sat σ w ×ˢ B').map (gfac q x)).prod = ((L1 x / L2 x : ℝ) : ℂ) := by
      push_cast
      rw [h, mul_div_assoc, div_self (by exact_mod_cast hL2pos.ne'), mul_one]
    rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hL1pos hL2pos),
      mul_div_mul_left _ _ (by linarith : (x - 1) ≠ 0)]
  have htlim : Tendsto t (𝓝[>] 1) (𝓝 1) := by
    have hc : Continuous t := continuous_const.mul (continuous_const.rpow continuous_neg (fun _ => Or.inl hq0.ne'))
    have := hc.tendsto 1
    simp only [ht, Real.rpow_neg_one, mul_inv_cancel₀ hq0.ne'] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hlim : Tendsto (fun x => (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x))) (𝓝[>] 1) (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul (hlim1.div hlim2 hc2.ne')
    simpa using this
  have hev1 : ∀ᶠ x in 𝓝[>] (1 : ℝ), (1 - t x) * (((x - 1) * L1 x) / ((x - 1) * L2 x)) <
      (1/2 : ℝ) ^ Multiset.card rest := hlim (gt_mem_nhds (by positivity))
  have hev2 : ∀ᶠ x in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
  have := hlow x hx2
  rw [hnorm x hx2] at this
  linarith

end GlobalTheory.RSStrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNormSqLtAbsNormUnitaryCuspStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ : CG E a), 1 ≤ a → σ.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → ∀ w ∉ T, ∀ α ∈ sat σ w, ‖(α : ℂ)‖ ^ 2 < (Ideal.absNorm w.asIdeal : ℝ) := by
  first
  | exact @GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | exact GlobalTheory.RSStrict.norm_sq_lt_absNorm
  | (intros; apply GlobalTheory.RSStrict.norm_sq_lt_absNorm <;> assumption)
end
end
