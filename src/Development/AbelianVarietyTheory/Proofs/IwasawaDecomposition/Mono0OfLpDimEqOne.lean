module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}

variable (h) in
theorem lpDim_zero (h : IsPlaceOver A w) : lpDim (lpZero (h := h)) = 0 := by
  simp [lpZero]

theorem lpDim_sum (a b : WD h) : lpDim (lpSum a b) = lpDim a + lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_prod]

theorem lpDim_tw (a : WD h) (s : ℝ) : lpDim (lpTw a s) = lpDim a := by
  induction a using ind
  rw [lpTw_mk, lpDim_mk, lpDim_mk]

theorem lpDim_tensor (a b : WD h) : lpDim (lpChar a b) = lpDim a * lpDim b := by
  induction a using ind
  induction b using ind
  rw [lpChar_mk, lpDim_mk, lpDim_mk, lpDim_mk, finrank_tensorProduct]

theorem lpDim_char (a χ : WD h) (hχ : lpDim χ = 1) : lpDim (lpChar a χ) = lpDim a := by
  rw [lpDim_tensor, hχ, mul_one]

theorem lpSum_zero (a : WD h) : lpSum a (lpZero (h := h)) = a := by
  induction a using ind
  rw [lpZero, lpSum_mk]
  exact sound ⟨LinearEquiv.prodUnique, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_comm (a b : WD h) : lpSum a b = lpSum b a := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodComm _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_assoc (a b c : WD h) : lpSum (lpSum a b) c = lpSum a (lpSum b c) := by
  induction a using ind
  induction b using ind
  induction c using ind
  rw [lpSum_mk, lpSum_mk, lpSum_mk, lpSum_mk]
  exact sound ⟨LinearEquiv.prodAssoc _ _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpTw_zero (a : WD h) : lpTw a 0 = a := by
  induction a using ind
  rw [lpTw_mk]
  exact sound ⟨.refl _ _, fun σ v => by simp, fun _ => rfl⟩

theorem lpTw_add (a : WD h) (s t : ℝ) : lpTw (lpTw a s) t = lpTw a (s + t) := by
  induction a using ind
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  rw [lpTw_mk, lpTw_mk, lpTw_mk]
  refine sound ⟨.refl _ _, fun σ v => ?_, fun _ => rfl⟩
  simp only [WDRep.tw_ρ, smul_smul, LinearEquiv.refl_apply]
  rw [Complex.ofReal_add, Complex.cpow_add _ _ hq, mul_zpow, mul_comm]

theorem lpTw_sum (a b : WD h) (s : ℝ) : lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s) := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, lpTw_mk, lpTw_mk, lpTw_mk, lpSum_mk]
  exact sound ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem monomial_sum_iff (a b : WD h) : mono0 (lpSum a b) ↔ mono0 a ∧ mono0 b := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.sum_N]
  refine ⟨fun h0 => ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩, fun h0 => ?_⟩
  · exact congrArg Prod.fst (LinearMap.congr_fun h0 (v, 0))
  · exact congrArg Prod.snd (LinearMap.congr_fun h0 (0, v))
  · rw [h0.1, h0.2, LinearMap.prodMap_zero]

theorem monomial_twist_iff (a : WD h) (s : ℝ) : mono0 (lpTw a s) ↔ mono0 a := by
  induction a using ind
  rw [lpTw_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tw_N]

theorem mono0_of_lpDim_eq_one {χ : WD h} (hχ : lpDim χ = 1) : mono0 χ := by
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff]
    have h1 := b.nilpotent.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly b.N
    rwa [h1, hχ, pow_one, aeval_X] at h2

theorem monomial_char_iff (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by
  have h0 := mono0_of_lpDim_eq_one hχ
  induction a using ind with
  | hP m a =>
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]
    refine ⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩
    let e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])
    have h2 := congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x))
      (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))
    simpa using h2

theorem charPol_lpSum (a b : WD h) (σ : Weil h) :
    charPol (lpSum a b) σ = charPol a σ * charPol b σ := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]

theorem inePol_sum (a b : WD h) (σ : G E Ω) :
    inePol (lpSum a b) σ = inePol a σ * inePol b σ := by
  by_cases hσ : σ ∈ Weil h
  · rw [inePol_of_mem _ hσ, inePol_of_mem _ hσ, inePol_of_mem _ hσ, charPol_lpSum]
  · rw [inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, inePol_of_not_mem _ hσ, mul_one]

theorem inePol_tw (a : WD h) (s : ℝ) :
    ∀ σ ∈ Ine (F := E) A, inePol (lpTw a s) σ = inePol a σ := by
  intro σ hσ
  induction a using ind
  rw [inePol_of_mem_Ine _ hσ, inePol_of_mem_Ine _ hσ, lpTw_mk, charPol_mk, charPol_mk]
  congr 1
  simp

end GlobalTheory.WeilDeligne.WD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem exists_ne_zero_lt_val_subset_of_mem_nhds {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] {s : Set K} {x : K} :
    s ∈ nhds x → ∃ c : K, c ≠ 0 ∧ {y | Valued.v (y - x) < Valued.v c} ⊆ s := by
  rw [Valued.mem_nhds]
  rintro ⟨γ, hγ⟩
  obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v : Valuation K Γ)) γ.1
  have hc' : (Valued.v : Valuation K Γ).restrict c = γ.1 := hc
  refine ⟨c, ?_, fun y hy => hγ ?_⟩
  · rintro rfl
    rw [map_zero] at hc'
    exact γ.ne_zero hc'.symm
  · change (Valued.v : Valuation K Γ).restrict (y - x) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact hy

theorem exists_exp_of_nhds (v : HeightOneSpectrum (𝓞 F)) (u : Set (v.adicCompletion F)) (hu : u ∈ nhds 1) :
    ∃ M : ℕ, ∀ y : v.adicCompletion F, Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → y ∈ u := by
  obtain ⟨c, hc, hsub⟩ := exists_ne_zero_lt_val_subset_of_mem_nhds hu
  have h0 : Valued.v c ≠ 0 := by simpa using hc
  set k := WithZero.log (Valued.v c) with hkdef
  have hk : Valued.v c = WithZero.exp k := (WithZero.exp_log h0).symm
  refine ⟨(-k).toNat + 1, fun y hy => hsub ?_⟩
  show Valued.v (y - 1) < Valued.v c
  refine lt_of_le_of_lt hy ?_
  rw [hk, WithZero.exp_lt_exp]
  have := Int.self_le_toNat (-k)
  push_cast
  omega

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_adicIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  Valued.isOpen_valuationSubring _

theorem finiteSingle_mem_of_nhds (Vf : Set (FiniteAdeleRing (𝓞 F) F)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (y : v.adicCompletion F),
      y ∈ v.adicCompletionIntegers F → (v ∈ S → Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ))) →
      finiteSingle F v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) isOpen_adicIntegers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  have hM : ∀ i : HeightOneSpectrum (𝓞 F), ∃ M : ℕ, ∀ (y : i.adicCompletion F) (hy : y ∈ i.adicCompletionIntegers F),
      Valued.v (y - 1) ≤ WithZero.exp (-(M : ℤ)) → (⟨y, hy⟩ : ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ t i := by
    intro i
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht i)
    obtain ⟨M, hM⟩ := exists_exp_of_nhds i u hu
    exact ⟨M, fun y hy h => hut (hM y h)⟩
  choose M hMs using hM
  refine ⟨I, hI.toFinset.sup M, hI, fun v y hy hS => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)))) :
      (i : HeightOneSpectrum (𝓞 F)) → ((i.adicCompletionIntegers F : Set (i.adicCompletion F)))) ∈ I.pi t := by
    intro i hi
    by_cases hne : i = v
    · subst hne
      rw [Pi.mulSingle_eq_same]
      refine hMs i y hy ((hS hi).trans ?_)
      rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
      exact Finset.le_sup (hI.mem_toFinset.2 hi)
    · rw [Pi.mulSingle_eq_of_ne hne]
      exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle F v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

end GlobalTheory.OpenIdeleCongr

namespace GlobalTheory.OpenIdeleCongr

variable {F : Type} [Field F] [NumberField F]

theorem localIdele_mem_of_isOpen (V : Subgroup (Ideles F)) (hV : IsOpen (V : Set (Ideles F))) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 F))) (M : ℕ), S.Finite ∧ ∀ v (x : (v.adicCompletion F)ˣ),
      Valued.v (x : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) → localIdele F v x ∈ V := by
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have hW1 : Units.embedProduct _ (1 : Ideles F) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact V.one_mem
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 F) F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hN : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨S, M, hS, hSV⟩ := finiteSingle_mem_of_nhds Vf hVf
  refine ⟨S, M, hS, fun v x hx hxS => ?_⟩
  have hin : ∀ y : (v.adicCompletion F)ˣ, Valued.v (y : v.adicCompletion F) = 1 →
      (v ∈ S → Valued.v ((y : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M : ℤ))) →
      ((localIdele F v y : Ideles F) : AdeleRing (𝓞 F) F) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy hyS =>
    hVprod ⟨mem_of_mem_nhds hVi, hSV v _ (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hy.le) hyS⟩
  have hxi : Valued.v ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hxiS : v ∈ S → Valued.v (((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(M : ℤ)) := by
    intro hv
    have e : ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * -((x : v.adicCompletion F) - 1) := by
      rw [mul_neg, mul_sub, Units.inv_mul, mul_one]; ring
    rw [e, map_mul, Valuation.map_neg, hxi, one_mul]
    exact hxS hv
  have h1 := hin x hx hxS
  have h2 := hin x⁻¹ hxi hxiS
  rw [← SetLike.mem_coe, ← hWU, Set.mem_preimage, Units.embedProduct_apply]
  refine hprod ⟨h1.1, ?_⟩
  have h3 := h2.2
  rw [map_inv] at h3
  exact h3

theorem open_subgroup_contains_congr : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)),
    IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧
      (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧
      ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  intro F _ _ V hV S₀
  classical
  obtain ⟨S₁, M₁, hS₁, key⟩ := localIdele_mem_of_isOpen V hV
  refine ⟨S₀ ∪ hS₁.toFinset, M₁ + 1, Finset.subset_union_left, fun v hv x hx => ?_, fun v _ a ha => ?_⟩
  · refine key v x hx fun hv' => absurd (Finset.mem_union_right _ (hS₁.mem_toFinset.2 hv')) hv
  · rw [locUnit_apply]
    set x := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a with hxdef
    have hxv : (x : v.adicCompletion F) = ((a : F) : v.adicCompletion F) := rfl
    have hsub : Valued.v ((x : v.adicCompletion F) - 1) = v.valuation F ((a : F) - 1) := by
      have e : (x : v.adicCompletion F) - 1 = (((a : F) - 1 : F) : v.adicCompletion F) := by
        show algebraMap F (v.adicCompletion F) (a : F) - 1 = _
        rw [← map_one (algebraMap F (v.adicCompletion F)), ← map_sub]
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hle : Valued.v ((x : v.adicCompletion F) - 1) ≤ WithZero.exp (-(M₁ : ℤ)) := by
      rw [hsub]
      refine ha.trans ?_
      rw [WithZero.exp_le_exp]
      push_cast
      omega
    have hlt : Valued.v ((x : v.adicCompletion F) - 1) < 1 := by
      rw [hsub]
      refine lt_of_le_of_lt ha ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      push_cast
      omega
    have hunit : Valued.v (x : v.adicCompletion F) = 1 := by
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    exact key v x hunit fun _ => hle

end GlobalTheory.OpenIdeleCongr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnitsStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)), IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧ (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧ ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  first | exact @GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | exact GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | (intros; apply GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgro
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.GabSep

theorem eq_one_of_forall_isOpen_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  intro E Ω _ _ _ _ g hg
  by_contra hne
  haveI : IsClosed ((commutator (G E Ω)).topologicalClosure : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hT1 : T1Space (Gab E Ω) := inferInstance
  have hopen : IsOpen ({g}ᶜ : Set (Gab E Ω)) := isOpen_compl_singleton
  have hmem : ((QuotientGroup.mk : G E Ω → Gab E Ω) ⁻¹' {g}ᶜ) ∈ nhds (1 : G E Ω) := by
    refine (hopen.preimage QuotientGroup.continuous_mk).mem_nhds ?_
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, QuotientGroup.mk_one]
    exact fun h => hne h.symm
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hmem
  let V : Subgroup (Gab E Ω) := L.fixingSubgroup.map (QuotientGroup.mk' _)
  have hV : IsOpen (V : Set (Gab E Ω)) := by
    have : (V : Set (Gab E Ω)) = (QuotientGroup.mk : G E Ω → Gab E Ω) '' (L.fixingSubgroup : Set (G E Ω)) := by
      simp [V, Subgroup.coe_map]
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.mp (hg V hV)
  exact hsub hσ (by simpa using e)

end GlobalTheory.GabSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsoluteGaloisAbelianizationEqOneOfMemOpenSubgroStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absoluteGaloisAbelianization_eq_one_of_mem_open_subgroups : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (g : Gab E Ω), (∀ U : Subgroup (Gab E Ω), IsOpen (U : Set (Gab E Ω)) → g ∈ U) → g = 1 := by
  first | exact @GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | exact GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup | (intros; apply GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
    _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ σ τ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg σ = _root_.GlobalTheory.WeilDeligne.deg τ →
      ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ σ τ hdeg
  let x : ℕ → _root_.GlobalTheory.WeilDeligne.Weil h := fun k ↦ (τ ^ k)⁻¹ * σ ^ k
  have hmem : ∀ k, ρ (x k) ∈ Set.range fun ι ↦ ρ (_root_.GlobalTheory.WeilDeligne.ineIncl h ι) := by
    intro k
    have h0 : _root_.GlobalTheory.WeilDeligne.deg (x k) = 0 := by
      simp only [x, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv, _root_.GlobalTheory.WeilDeligne.deg_pow, hdeg]
      ring
    refine ⟨⟨_, _root_.GlobalTheory.WeilDeligne.deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only
    congr 1
  obtain ⟨k, l, hkl, hρkl⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hmem hρ.finite_range
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hx : ρ (x k) = ρ (x (k + m + 1)) := hρkl
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have key : σ ^ (m + 1) = τ ^ (k + m + 1) * x (k + m + 1) * (x k)⁻¹ * (τ ^ k)⁻¹ := by
    simp only [x]
    group
  have key' : τ ^ (m + 1) = τ ^ (k + m + 1) * (τ ^ k)⁻¹ := by
    group
  have hinv : ρ (x k) * ρ (x k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← map_pow, ← map_pow, key, key']
  simp only [map_mul]
  rw [← hx, mul_assoc (ρ _) (ρ (x k)), hinv, mul_one]

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmoothStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ σ τ : Weil h, deg σ = deg τ → ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | exact GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | (intros; apply GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaMovesRoot

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem val_eq_one_of_notMem (h : IsPlaceOver A w) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (s : E)) = 1 :=
  le_antisymm (valuation_le_one_intCl (F := E) A (algebraMap (𝓞 E) _ s))
    (not_lt.mp fun hlt => hs ((h s).mp hlt))

theorem exists_val_eq_zpow (h : IsPlaceOver A w) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {a : E} (ha : a ≠ 0) :
    ∃ m : ℤ, A.valuation (algebraMap E Ω a) = A.valuation (algebraMap E Ω (ϖ : E)) ^ m := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hϖ0' : (ϖ : E) ≠ 0 := by simpa using hϖ0
  have hv : w.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
    have a2 : ¬ _ := fun hh => h2 ((w.intValuation_le_pow_iff_mem ϖ 2).1 hh)
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0), WithZero.exp_le_exp] at a1 a2
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0)]
    congr 1
    omega
  have hv' : w.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
    rw [← hv]; exact w.valuation_of_algebraMap ϖ
  have ha' : w.valuation E a ≠ 0 := by simpa using ha
  set n := WithZero.log (w.valuation E a)
  have hu : w.valuation E (a * (ϖ : E) ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hv', ← WithZero.exp_log ha', ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp [n]
  obtain ⟨t, d, htd⟩ := w.exists_primeCompl_mul_eq_of_integer _ hu.le
  have hd : w.valuation E (algebraMap (𝓞 E) E d) = 1 := (w.valuation_eq_one_iff_notMem).2 d.2
  have ht : w.valuation E (algebraMap (𝓞 E) E t) = 1 := by rw [← htd, map_mul, hu, hd, one_mul]
  have ht' := val_eq_one_of_notMem h ((w.valuation_eq_one_iff_notMem).1 ht)
  have hd' := val_eq_one_of_notMem h d.2
  have e := congrArg (fun z => A.valuation (algebraMap E Ω z)) htd
  simp only [map_mul, map_zpow₀] at e
  change _ * A.valuation (algebraMap E Ω ((d : 𝓞 E) : E)) = A.valuation (algebraMap E Ω (t : E)) at e
  rw [ht', hd', mul_one] at e
  exact ⟨-n, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left e⟩

theorem val_term_le_one {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → A.valuation (f i) = A.valuation (f j) → i = j)
    (hs : A.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, A.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => A.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin (h : IsPlaceOver A w) {l : ℕ} (hl : 2 ≤ l) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ l = algebraMap E Ω (ϖ : E)) :
    x ∉ (⊥ : IntermediateField E Ω) ∧ ∀ (g : Ω ≃ₐ[E] Ω) (b : Ω),
      b ∈ IntermediateField.adjoin E {x} → A.valuation b ≤ 1 → A.valuation (g b - b) < 1 := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hl0 : l ≠ 0 := by omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm, map_eq_zero] at hx
    exact hϖ0 (by simpa using hx)
  set t := A.valuation x with ht
  have htl : A.valuation (algebraMap E Ω (ϖ : E)) = t ^ l := by rw [← hx, map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := (h ϖ).mpr h1
    rw [htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : E) (i : ℕ), algebraMap E Ω a * x ^ i ≠ 0 →
      ∃ m : ℤ, A.valuation (algebraMap E Ω a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := exists_val_eq_zpow h h1 h2 ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hb
    obtain ⟨m, hm⟩ := hval a 0 (by simpa [ha] using hx0)
    have := hmod 0 1 m 0 (by omega) (by omega) (by rw [← hm]; simp [ha, ht])
    omega
  intro g b hb hb1
  have halg : IsAlgebraic E x := Algebra.IsAlgebraic.isAlgebraic x
  have hb' : b ∈ Algebra.adjoin E {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  have hq : (X ^ l - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hl0
  set p := p₀ %ₘ (X ^ l - C (ϖ : E))
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C _, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C _] at this
  change A.valuation (aeval x p₀) ≤ 1 at hb1
  change A.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : A.valuation (g x) = t := by
    refine (pow_left_injective hl0 : Function.Injective (fun a : A.ValueGroup => a ^ l)) ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx, g.commutes, htl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : A.valuation (algebraMap E Ω (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

theorem mem_Ine_of_cong {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ b : IntCl E Ω, σ • b - b ∈ primeBelow (F := E) A) : σ ∈ Ine (F := E) A := by
  have hc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1 :=
    fun b hb => hσ ⟨b, hb.tower_top⟩
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    let b' : IntCl E Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := E) (σ • A) ↔ b' ∈ primeBelow (F := E) A
    rw [primeBelow_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ (σ⁻¹ • b')
    rw [smul_inv_smul] at this
    exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩
  refine ⟨hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hdec, ← A.valuation_le_one_iff]; exact hx
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← e, map_mul]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_sub_lt _ (hc t ht) ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hσx) (hc s hs)
  rwa [map_mul, hs1, one_mul] at hv

theorem exists_cong_of_cong_on_fixed {R S G : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] (Q : Ideal S) [Q.IsPrime]
    (g : G) (hg : ∀ b : S, (∀ k ∈ H, k • b = b) → g • b - b ∈ Q) :
    ∃ k ∈ H, ∃ k' ∈ H, ∀ b : S, (k' * g * k) • b - b ∈ Q := by
  let R' := FixedPoints.subalgebra R S H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : S) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' S := ⟨fun k r b => by
    change (k : G) • ((r : S) * b) = (r : S) * (k : G) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' S H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : (g⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  obtain ⟨k, hk⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R') (G := H)
    Q (g⁻¹ • Q) (by
      ext b
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      have := hg b (hR' b)
      change (b : S) ∈ Q ↔ g • (b : S) ∈ Q
      exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩)
  have hQ : (g * k) • Q = Q := by
    have hk2 : g⁻¹ • Q = (k : G) • Q := hk
    rw [mul_smul, ← hk2, smul_inv_smul]
  let φ : (S ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (S ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G S (g * k)) hQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q ((g * k) • (r : S)) = Ideal.Quotient.mk Q (r : S)
      rw [Ideal.Quotient.eq, mul_smul, hR' r k k.2]
      exact hg r (hR' r))
  obtain ⟨⟨k', hk'Q⟩, hk'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨k, k.2, k'⁻¹, inv_mem k'.2, fun b => ?_⟩
  have h1 : Ideal.Quotient.mk Q ((k' : G) • b) = Ideal.Quotient.mk Q ((g * k) • b) :=
    DFunLike.congr_fun hk' (Ideal.Quotient.mk Q b)
  rw [eq_comm, Ideal.Quotient.eq] at h1
  have h2 : (k' : G) • Q = Q := hk'Q
  rw [← h2, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, smul_smul] at h1
  rwa [mul_assoc]

theorem exists_mem_Ine_apply_ne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (l : ℕ), l.Prime → ∀ (ϖ : 𝓞 E), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 → ∀ x : Ω,
    x ^ l = algebraMap E Ω (ϖ : E) → ∃ σ ∈ Ine (F := E) A, σ x ≠ x := by
  intro E Ω _ _ _ _ _ A w h l hl ϖ h1 h2 x hx
  obtain ⟨hx1, hx2⟩ := cong_on_adjoin h hl.two_le h1 h2 hx
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g x ≠ x := by
    by_contra hc
    push Not at hc
    exact hx1 ((InfiniteGalois.mem_bot_iff_fixed x).mpr hc)
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) x
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) x)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := exists_cong_of_cong_on_fixed (R := 𝓞 E) H (primeBelow (F := E) A) g
    (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {x}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨x, IntermediateField.mem_adjoin_simple_self E x⟩)))
  refine ⟨k' * g * k, mem_Ine_of_cong hc, fun he => hg ?_⟩
  have e1 : k x = x := hk
  have e2 : k' x = x := hk'
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1] at he
  exact k'.injective (he.trans e2.symm)

end GlobalTheory.InertiaMovesRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FrobRestrict

open scoped Pointwise

theorem _root_.GlobalTheory.FrobRestrict.isFrob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by
  have hdec : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx q
    have e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1)
        = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]
      ring
    rw [e]
    refine Valuation.map_add_lt _ (ih.2 _ hxq) ?_
    rw [_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]
    exact hφ.2 x hx

private lemma restrictScalars_mem_decompositionSubgroup {E Ω : Type} [Field E] [Field Ω]
    [Algebra E Ω] {K : IntermediateField E Ω} {A : ValuationSubring Ω} {ι : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (h : ι ∈ ValuationSubring.decompositionSubgroup K A) :
    ι.restrictScalars E ∈ ValuationSubring.decompositionSubgroup E A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h ⊢
  exact h

theorem _root_.GlobalTheory.FrobRestrict.frob_restrict : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω,
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧
    (∀ ι ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A, ι.restrictScalars E ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∧
    ∀ (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (φ : _root_.Formalism.ConjugateSelfDual.G E Ω), _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV w) σ → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) φ →
    σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  intro E Ω _ _ _ _ K _ _ v w h A hw
  have hnorm : _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
    haveI := v.isMaximal
    haveI := w.isMaximal
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    unfold _root_.Formalism.ConjugateSelfDual.normV
    letI := Ideal.Quotient.field v.asIdeal
    exact Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal) (V := 𝓞 K ⧸ w.asIdeal)
  refine ⟨fun x => ?_, hnorm, fun ι hι => ?_, fun σ φ hσ hφ => ?_⟩
  · have e : (algebraMap K Ω) ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K)
        = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E K Ω]
      rfl
    rw [← e, hw, ← h, Ideal.mem_comap]
  · rw [_root_.ReciprocityTheory.Gal.mem_Ine] at hι ⊢
    exact ⟨restrictScalars_mem_decompositionSubgroup hι.1, hι.2⟩
  · have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)) (σ.restrictScalars E) := by
      rw [← hnorm]
      exact ⟨restrictScalars_mem_decompositionSubgroup hσ.1, hσ.2⟩
    have hφf := _root_.GlobalTheory.FrobRestrict.isFrob_pow hφ (w.asIdeal.inertiaDeg (𝓞 E))
    have h1 := _root_.ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hφf hσ'
    have h2 := _root_.ReciprocityTheory.Gal.conj_mem_Ine (g := φ ^ w.asIdeal.inertiaDeg (𝓞 E)) hφf.1 h1
    rwa [mul_inv_cancel_left] at h2

end GlobalTheory.FrobRestrict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertiaStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsPlaceOver A v ∧ normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧ (∀ ι ∈ Ine (F := K) A, ι.restrictScalars E ∈ Ine (F := E) A) ∧ ∀ (σ : G K Ω) (φ : G E Ω), IsFrob A (normV w) σ → IsFrob A (normV v) φ → σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.FrobRestrict.frob_restrict | exact GlobalTheory.FrobRestrict.frob_restrict | (intros; apply GlobalTheory.FrobRestrict.frob_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : ℤ → Submodule K V}
  {N : End K V}

theorem eq_zero_of_pow_eq_zero (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d : ℤ}
    (hd : d + m ≤ 0) {v : V} (hv : v ∈ U d) (h0 : (N ^ m) v = 0) : v = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = -((c + m : ℕ) : ℤ) := ⟨(-d - m).toNat, by omega⟩
  subst hc
  refine (hb (c + m)).2.1 hv (zero_mem _) ?_
  rw [pow_add, End.mul_apply, h0, map_zero, map_zero]

end Graded

end GlobalTheory.WeilDeligne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlaces
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.PlacesOver

theorem finite_fibre (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 K) | w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}.Finite := by
  have hne : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  refine (Ideal.finite_factors hne).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hw]

theorem places_over_finset (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S,
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  have hfin : (⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 K) |
      w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal}).Finite :=
    S.finite_toSet.biUnion fun v _ => finite_fibre E K v
  refine ⟨hfin.toFinset, fun w => ?_⟩
  simp

end GlobalTheory.PlacesOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetPlacesOverFinsetPlacesStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_places_over_finset_places : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ ∃ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
  first | exact @GlobalTheory.PlacesOver.places_over_finset | exact GlobalTheory.PlacesOver.places_over_finset | (intros; apply GlobalTheory.PlacesOver.places_over_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNilpotentZpowSubOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)

theorem nilpotent_part {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩

end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
end
