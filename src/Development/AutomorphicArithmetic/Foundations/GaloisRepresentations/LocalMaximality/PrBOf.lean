module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PrBOf
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.prB_of :
    GoodZ → PrB := by
  intro hG F K _ _ _ _ _ _ d x h τ hτ ρ hρ a q had hqd e he y hy
  have mono : ∀ r : ℕ, ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) r ≤ omB ℂ K (rB ℂ K (xv x) t) r :=
    fun r => (hG F K d x h r).2.2
  have hvan : ∀ i, (Finset.univ.erase i).Nonempty →
      ∀ u ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) (d - a),
      ∀ v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a,
      (LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ) u v = 0 := by
    intro i hi u hu v hv
    have hvq : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
    have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) h τ hτ (Finset.univ.erase i) hi (d - a) a
      (by omega) v hvq).2 hv u hu
    exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) h.pd ρ hρ i _ hi (Finset.notMem_erase i _) _ hmem
  obtain ⟨ε, hε⟩ := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a))
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))
    (mono _) (mono _) hvan ((d : ℤ) - (q : ℕ))
  obtain ⟨y', hy', rfl⟩ := hy
  have key := hε e he.1 y' (by
    have e1 : (d : ℤ) - ((d : ℤ) - (q : ℕ)) - 1 = (q : ℤ) - 1 := by ring
    rw [e1]
    exact hy')
  have h0 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a)).D e = 0 := he.2
  rw [h0, map_zero, LinearMap.zero_apply] at key
  exact (smul_eq_zero_iff_eq ε).1 key.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IdJCriterion
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem ext_comm_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (v : M) (q : ℕ)
    (w : ExteriorAlgebra R M) (hw : w ∈ ⋀[R]^q M) :
    ExteriorAlgebra.ι R v * w = ((-1 : ℤ) ^ q) • (w * ExteriorAlgebra.ι R v) := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [mul_add, add_mul, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    have h := ExteriorAlgebra.ι_add_mul_swap (R := R) v u
    have h' : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
      eq_neg_of_add_eq_zero_left h
    rw [← mul_assoc, h', neg_mul, mul_assoc, hx, mul_smul_comm]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, mul_assoc]

private theorem ext_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (p q : ℕ)
    (y w : ExteriorAlgebra R M) (hy : y ∈ ⋀[R]^p M) (hw : w ∈ ⋀[R]^q M) :
    y * w = ((-1 : ℤ) ^ (p * q)) • (w * y) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, ext_comm_one u q w hw, smul_mul_assoc, smul_smul,
      mul_assoc, Nat.succ_mul, pow_add]

theorem UpperTheory.Gal.productCup_of_system.idJ_of :
    LatOm → LatA → DualForm → IdJ := by
  intro hOm hA hD F K _ _ _ _ _ _ d x hc τ hτ a ha j
  obtain ⟨⟨_, n, v, φ, hv, hφ, hdec⟩, hsp⟩ := hOm F K d x hc a {j} (by simp)
  have hdec' : ∀ z ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) {j}) a : Set (DR ℂ K)), z = ∑ k, φ k z • v k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hdec z hz
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
      rw [← hp, ← hq]
    | smul c p _ hp =>
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hp]
  have hG : omG x j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x j).ne_zero
  choose w hwm hwt using fun k => (hD F K d x hc τ hτ a ha (omG x j • φ k)).2
  have hwB : ∀ k, w k ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a) := by
    intro k
    refine (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ {j} (by simp) a (d - a) (by omega) (w k) (hwm k)).1 ?_
    intro y hy
    have hy' : y ∈ ⋀[K]^a Ω[K⁄ℂ] := GlobalTheory.PD.mem_deg_of_mem_omB _ _ _ hy
    rw [ext_comm a (d - a) y (w k) hy' (hwm k), map_zsmul, map_zsmul]
    refine zsmul_mem ?_ _
    rw [← hwt k y hy']
    refine ((hA F d x hc.pd {j} j (by simp)).2.1 _).2 ?_
    simpa [hG] using hφ k y hy
  refine ⟨∑ k, w k ⊗ₜ[ℂ] v k, ?_, ?_⟩
  · show _ ∈ MZ F K (xv x) a {j} {j}
    exact Submodule.sum_mem _ fun k _ => Submodule.apply_mem_map₂ _ (hwB k) (hv k)
  · intro y hy
    conv_rhs => rw [hdec' y (hsp y hy)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : muP F K τ (w k ⊗ₜ[ℂ] v k) y = (Algebra.trace F K (τ (w k * y))) ⊗ₜ[ℂ] v k := by
      simp [muP]
    rw [this, ← hwt k y hy]
    simp [mulP]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdOneApply
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma resP_eq_zero {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V) (hA : ∀ f ∈ A, ρ f = 0)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m = 0 := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp [resP, hA a ha]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul r x _ hx => rw [map_smul, hx, smul_zero]

private lemma residueCharacteristic_mem {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V]
    (ρ : F →ₗ[ℂ] ℂ) (A : Submodule ℂ F) (B : Submodule ℂ V)
    {m : F ⊗[ℂ] V} (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ F V) A B) :
    resP V ρ m ∈ B := by
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simpa [resP] using B.smul_mem (ρ a) hb
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact B.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact B.smul_mem r hx

private lemma wd_one_apply {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (t : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • c (t.erase i) := by
  simp [wd, LinearMap.sum_apply]

theorem UpperTheory.Gal.productCup_of_system.pInt_of :
    WdUni → GoodZ → PInt := by
  intro hW _ F K _ _ _ _ _ _ d x hx τ _ ρ hρ a p t ht
  simp only [UpperTheory.Gal.productCup_of_system.Sys.mix, GlobalTheory.WH.acx, GlobalTheory.PD.Cx.B, Submodule.mem_map,
    Submodule.mem_pi] at ht
  obtain ⟨c, hc, rfl⟩ := ht
  have hU := fun I J : Finset (Fin (d + 1)) =>
    hW (Fin (d + 1)) (Fin (d + 1)) (F ⊗[ℂ] DR ℂ K) (fun _ => 1) c I J
  have hcu : ∀ I J : Finset (Fin (d + 1)), c (uni I J) ≠ 0 →
      I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + p + 1 ∧
        c (uni I J) ∈ (sysP K x a).M I J := by
    intro I J h0
    have h := hc (uni I J) (Set.mem_univ _)
    obtain ⟨_, hl, hr, hcard, _⟩ := hU I J
    split_ifs at h with h1
    · simp only [GlobalTheory.WH.mixF, hl, hr] at h
      split_ifs at h with h2
      · refine ⟨h2.1, h2.2, ?_, h⟩
        rw [hcard] at h1
        omega
      · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
    · exact absurd ((Submodule.mem_bot ℂ).mp h) h0
  have hz : ∀ (i : Fin (d + 1)) (J : Finset (Fin (d + 1))),
      resP (DR ℂ K) ρ (c (uni (Finset.univ.erase i) J)) = 0 := by
    intro i J
    by_cases h0 : c (uni (Finset.univ.erase i) J) = 0
    · rw [h0, map_zero]
    obtain ⟨hI, _, _, hm⟩ := hcu _ _ h0
    exact resP_eq_zero ρ _ _
      (fun f hf => GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hx.pd ρ hρ i _ hI (by simp) f hf) hm
  refine ⟨fun L => ((-1 : ℤ) ^ (d + 1)) • resP (DR ℂ K) ρ (c (uni Finset.univ L)), ?_, ?_⟩
  · simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.cechC, Submodule.mem_pi]
    intro L _
    by_cases h0 : c (uni Finset.univ L) = 0
    · simp [h0]
    obtain ⟨_, hL, hcard, hm⟩ := hcu _ _ h0
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    dsimp only
    rw [if_pos (show L.Nonempty ∧ (L.card : ℤ) = ↑p - 1 + 1 from ⟨hL, by omega⟩)]
    exact Submodule.smul_of_tower_mem _ _ (residueCharacteristic_mem ρ _ _ hm)
  · funext J
    simp only [Lef.omCx, GlobalTheory.PD.cech, GlobalTheory.PD.deltaL, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.DI.delta]
    rw [(hU Finset.univ J).1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [wd_one_apply, map_add (f := _), map_zsmul, map_sum, hz, smul_zero, Finset.sum_const_zero,
      zero_add, Finset.card_univ, Fintype.card_fin, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CechZero
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni]

private theorem cech_zero {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    {G : Finset ι → Submodule ℂ E} {n : ℤ} {y : Finset ι → E} (hy : y ∈ (cech G).Z n)
    (s : Finset ι) (h : (s.card : ℤ) ≠ n + 1) : y s = 0 := by
  have h1 : y s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then G s else ⊥) := hy.1 s (Set.mem_univ s)
  rw [if_neg (fun h' => h h'.2)] at h1
  simpa using h1

private theorem res_mu {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (e f w : DR ℂ K) :
    resP (DR ℂ K) ρ (muP F K τ (e ⊗ₜ f) w) = trF ℂ τ ρ (e * w) • f := by
  simp [muP, resP, trF]

end UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

open UpperTheory.Gal.productCup_of_system.PartialZeroIdentity in
theorem UpperTheory.Gal.productCup_of_system.zId_of :
    ZAct → RCupTop → KunDec → SysBasic → GoodZ → ZId := by
  intro hZA hRC hKD hSB hGZ F K _ _ _ _ _ _ d x hFC τ hT ρ hR a ha c hc hD
  have htop : top c ∈ (sysZ K x a).mix.Z (d + 2) :=
    (hSB d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).2.2.1 c hc
  obtain ⟨m, p, e, f, hk, hB⟩ := hKD (Fin (d + 1)) (DR ℂ K) (DR ℂ K)
    (fun s => omB ℂ K (rB ℂ K (xv x) s) (d - a)) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) d
    (hGZ F K d x hFC (d - a)).2.2 (hGZ F K d x hFC a).2.2 (top c) htop
  refine ⟨m, p, e, f, hk, hB, ?_⟩
  intro q α hα
  have h1 := hZA F K d x hFC τ hT ρ hR a q ha c hc hD α hα
  have h2 := hRC F K d x hFC τ hT ρ hR a q ha _ hB α hα
  have hzero : ∀ k, p k ≠ q → pr K τ ρ (e k) α = 0 := by
    intro k hkq
    simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      LinearMap.proj_apply, LinearMap.mul_apply']
    refine Finset.sum_eq_zero fun j _ => ?_
    have hc1 : ((Finset.univ.filter (· ≤ j)).card : ℤ) = (j : ℤ) + 1 := by
      rw [Finset.filter_ge_eq_Iic, Fin.card_Iic]; push_cast; ring
    have hc2 : ((Finset.univ.filter (j ≤ ·)).card : ℤ) = (d : ℤ) + 1 - j := by
      rw [Finset.filter_le_eq_Ici, Fin.card_Ici]; have := j.2; omega
    by_cases hA : ((Finset.univ.filter (· ≤ j)).card : ℤ) = ((d : ℤ) - p k) + 1
    · have : α (Finset.univ.filter (j ≤ ·)) = 0 := by
        refine cech_zero hα _ ?_
        rw [hc2]; rw [hc1] at hA
        intro h; apply hkq; omega
      simp [this]
    · have : e k (Finset.univ.filter (· ≤ j)) = 0 := cech_zero (hk k).2.1 _ hA
      simp [this]
  have key : ∀ J, resP (DR ℂ K) ρ (∑ i, muP F K τ
      ((∑ k, join (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (e k) (f k))
        (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
      ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k J := by
    intro J
    rw [Finset.sum_filter_of_ne (fun k _ hne => ?_)]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, join, lft_uni', rgt_uni', TensorProduct.mk_apply, map_sum,
        LinearMap.sum_apply, res_mu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', Finset.sum_smul]
    · by_contra hpq
      exact hne (by rw [hzero k hpq, zero_smul])
  have hfin := add_mem h1 h2
  convert hfin using 1
  ext J
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  rw [← key J]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
  abel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MemOmAIff
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → Fˣ)

private theorem ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private theorem omG_ne (i : Fin (d + 1)) : omG x i ≠ 0 := by
  unfold omG
  exact Finset.prod_ne_zero_iff.mpr (fun l _ => div_ne_zero (Units.ne_zero _) (Units.ne_zero _))

private theorem prod_eq (i i' : Fin (d + 1)) :
    (∏ j, (x i' : F) / x j) * omG x i = ((x i' : F) / x i) ^ (d + 1) := by
  unfold omG
  rw [← Finset.prod_mul_distrib]
  have h : ∀ j, (x i' : F) / x j * (x j / x i) = x i' / x i := fun j => by
    have h1 := (x j).ne_zero
    have h2 := (x i).ne_zero
    field_simp
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem mem_omA_iff' {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (y : F) :
    y ∈ omA ℂ (xv x) I ↔ y / omG x i ∈ rA ℂ (xv x) I := by
  have hG := omG_ne x i
  have key : ∀ i', (∏ j, (x i' : F) / x j) = ((x i' : F) / x i) ^ (d + 1) / omG x i := fun i' => by
    rw [eq_div_iff hG, prod_eq]
  simp only [omA, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule, xv]
  constructor
  · intro hy
    have h1 := hy i hi
    rw [key, div_self (Units.ne_zero (x i)), one_pow] at h1
    rwa [one_div, inv_mul_eq_div] at h1
  · intro hy i' hi'
    rw [key, div_mul_eq_mul_div, mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (ratio_mem x hi i') _) hy

private theorem loc_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) (y : F)
    (hy : y ∈ rA ℂ (xv x) (insert j I)) : ∃ N : ℕ, ((x j : F) / x i) ^ N * y ∈ rA ℂ (xv x) I := by
  have hs : (x j : F) / x i ∈ rA ℂ (xv x) I := ratio_mem x hi j
  unfold rA at hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, rfl⟩ := hz
    rcases Finset.mem_insert.1 ha with h | h
    · rw [h]
      refine ⟨1, ?_⟩
      have e : ((x j : F) / x i) ^ 1 * (xv x b / xv x j) = x b / x i := by
        have h1 := (x j).ne_zero
        have h2 := (x i).ne_zero
        simp only [xv, pow_one]
        field_simp
      rw [e]
      exact ratio_mem x hi b
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul]
      exact ratio_mem x h b
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y + z) = ((x j : F) / x i) ^ N2 * (((x j : F) / x i) ^ N1 * y) + ((x j : F) / x i) ^ N1 * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h1) (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hs _) h2)
  | mul y z _ _ hy hz =>
    obtain ⟨N1, h1⟩ := hy
    obtain ⟨N2, h2⟩ := hz
    refine ⟨N1 + N2, ?_⟩
    have e : ((x j : F) / x i) ^ (N1 + N2) * (y * z) = (((x j : F) / x i) ^ N1 * y) * (((x j : F) / x i) ^ N2 * z) := by ring
    rw [e]
    exact Subalgebra.mul_mem _ h1 h2

end

theorem UpperTheory.Gal.productCup_of_system.latA_of :
    LatA := by
  intro F _ _ d x _ I i hi
  refine ⟨?_, mem_omA_iff' x hi, ?_⟩
  · unfold UpperTheory.Gal.productCup_of_system.Lat
    refine ⟨?_, 1, fun _ => omG x i, fun _ => LinearMap.mulLeft F (omG x i)⁻¹, ?_, ?_, ?_⟩
    · intro a ha m hm
      rw [smul_eq_mul, mem_omA_iff' x hi, mul_div_assoc]
      exact Subalgebra.mul_mem _ ha ((mem_omA_iff' x hi m).1 hm)
    · intro _
      rw [mem_omA_iff' x hi, div_self (omG_ne x i)]
      exact Subalgebra.one_mem _
    · intro _ m hm
      rw [LinearMap.mulLeft_apply, inv_mul_eq_div]
      exact (mem_omA_iff' x hi m).1 hm
    · intro m _
      rw [Fin.sum_univ_one, LinearMap.mulLeft_apply, smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ (omG_ne x i), one_mul]
  · intro j y hy
    obtain ⟨N, hN⟩ := loc_mem x hi j _ ((mem_omA_iff' x (Finset.mem_insert_of_mem hi) y).1 hy)
    exact ⟨N, (mem_omA_iff' x hi _).2 (by rwa [mul_div_assoc])⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ZActionCriterion
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem resP_one {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V] (ρ : F →ₗ[ℂ] ℂ)
    (h : ρ 1 = 1) (w : V) : resP V ρ ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [resP, h]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni, Finset.mem_toLeft]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni, Finset.mem_toRight]

private theorem card_filter_le {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (· ≤ i)).card = (i : ℕ) + 1 := by
  have h : Finset.univ.filter (· ≤ i) = Finset.Iic i := by
    ext j
    simp
  rw [h, Fin.card_Iic]

private theorem card_filter_ge {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (i ≤ ·)).card = d + 1 - (i : ℕ) := by
  have h : Finset.univ.filter (i ≤ ·) = Finset.Ici i := by
    ext j
    simp
  rw [h, Fin.card_Ici]

theorem UpperTheory.Gal.productCup_of_system.zAct_of :
    PCup → PTheta → PCmp → PInt → EdgeRel → SysBasic → GoodZ → ZAct := by
  intro hCup hTh hCmp hInt hEdge hBas hGood F K _ _ _ _ _ _ d x hx τ hτ ρ hρ a p ha c hc hD α hα
  obtain ⟨hc1, hv1, hk1⟩ := hCup F K d x hx τ hτ a p ha c hc hD α hα
  obtain ⟨cθ, hcθ, hvθ, hkθ, htθ⟩ := hTh F K d x hx a p α hα
  have hmono := (hGood F K d x hx a).2.2
  have hE := hEdge (Fin (d + 1)) (DR ℂ K) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) p hmono α hα
  let c1 := rcup (muP F K τ) p c α - cθ
  have hZ : c1 ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) := sub_mem hc1 hcθ
  have hv : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), d < L.card → c1 (uni b L) = 0 := by
    intro b L h
    simp [c1, hv1 b L h, hvθ b L h]
  let γ : Finset (Two d) → DR ℂ K :=
    ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α - ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 α
  have hγe : γ = (-((-1 : ℤ) ^ ((p + 1) * d))) • (edge2 α - ((-1 : ℤ) ^ p) • edge1 α) := by
    have h : p * (d + 1) + d = (p + 1) * d + p := by ring
    simp only [γ, h, pow_add]
    generalize ((-1 : ℤ) ^ ((p + 1) * d)) = s
    generalize ((-1 : ℤ) ^ p) = t
    module
  have hγ : γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2) := by
    rw [hγe]
    exact zsmul_mem hE _
  have hk : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), L.card = d → mulP F K (c1 (uni b L)) = kap K x L • γ b := by
    intro b L h
    simp only [c1, γ, Pi.sub_apply, map_sub, hk1 b L h, hkθ b L h, smul_sub, Pi.smul_apply]
  have hB := hCmp F K d x hx a p c1 hZ hv γ hγ hk
  have hTop := (hBas d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu (d + p + 2)).2.2.2.1 c1 hB
  have hI := hInt F K d x hx τ hτ ρ hρ a p (top c1) hTop
  have hCc := (hBas d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).1 c hc.1
  have hαs : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hs
    have h1 : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := hα.1 s (Set.mem_univ s)
    rw [if_neg (by
      rintro ⟨-, h⟩
      exact hs (by exact_mod_cast h))] at h1
    simpa using h1
  have key : (α - fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) =
      -(fun J => resP (DR ℂ K) ρ (top c1 (uni Finset.univ J))) := by
    funext J
    have hsum : ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) := by
      by_cases hJ : J.card = p + 1
      · have : Even (p * J.card) := by
          rw [hJ]
          exact Nat.even_mul_succ_self p
        rw [this.neg_one_pow, one_smul]
      · have : ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : (Finset.univ.filter (i ≤ ·)).card = p + 1
          · have h0 : top c (uni (Finset.univ.filter (· ≤ i)) J) = 0 := by
              refine hCc _ _ ∅ (Or.inr (Or.inr ?_))
              rw [card_filter_ge] at hi
              have hid := i.is_lt
              simp only [card_filter_le, Finset.card_empty, add_zero]
              omega
            rw [h0]
            simp
          · rw [hαs _ hi]
            simp
        rw [this, smul_zero]
    have htop : top c1 (uni Finset.univ J) = ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) - (1 : F) ⊗ₜ[ℂ] α J := by
      simp only [top, c1, Pi.sub_apply, htθ, rcup, lft_uni', rgt_uni', Finset.card_empty, add_zero]
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [htop, hsum, map_sub, resP_one ρ hρ.1]
    abel
  rw [key]
  exact neg_mem hI
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKapInd
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem map_detC' {S S' κ : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [LinearOrder κ] {p : ℕ} (φ : S →ₐ[ℂ] S') (ρ : κ → Fin p → S) (s : Finset κ) :
    φ (detC ρ s) = detC (fun t b => φ (ρ t b)) s := by
  unfold detC
  split_ifs with h
  · rw [AlgHom.map_det]
    congr 1
  · simp

private def rho0 {d : ℕ} {K : Type} [Field K] (y : Fin (d + 1) → K) :
    Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → K := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then y m * y (ofLex l).2 else 0) -
    if m = (ofLex l).2 then y m * y (ofLex l).1 else 0) (ofLex t)

private theorem map_rowMu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (s : Finset (Fin (d + 1) ⊕ₗ Mi d)) :
    π (detC T.rowMu s) = detC (rho0 y) s := by
  rw [map_detC']
  congr 1
  funext t b
  rcases ht : ofLex t with i | l
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inl, Pi.single_apply]
    split_ifs <;> simp
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inr, map_sub, apply_ite π, map_mul, hX, hY, map_zero]

private theorem map_mu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (l : Mi d) : π (T.mu l) = 0 := by
  simp only [Sys.mu, map_sub, map_mul, hX, hY]
  ring

private theorem ind_of {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (hM : ThMu) (hU : WdUni) (T : Sys d S E) (π : S →ₐ[ℂ] K)
    (y : Fin (d + 1) → K) (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i)
    (i : Fin (d + 1)) (L : Finset (Mi d)) :
    π (detC T.rowMu (uni {i} L)) = π (detC T.rowMu (uni {0} L)) := by
  by_cases h : i = 0
  · rw [h]
  have h0 : (0 : Fin (d + 1)) ≠ i := fun e => h e.symm
  have h1 := congrFun (hM d S E T).1 (uni {0, i} L)
  rw [(hU _ _ _ _ _ {0, i} L).1] at h1
  have hl : wd (fun j : Fin (d + 1) => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE j : Fin (d + 1) ⊕ₗ Mi d)))
      (fun b' => detC T.rowMu (uni b' L)) {0, i} =
      detC T.rowMu (uni {i} L) - detC T.rowMu (uni {0} L) := by
    have e0 : ({0, i} : Finset (Fin (d + 1))).erase 0 = {i} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact absurd hb ha
        · exact hb
      · rintro rfl; exact ⟨h, Or.inr rfl⟩
    have ei : ({0, i} : Finset (Fin (d + 1))).erase i = {0} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact hb
        · exact absurd hb ha
      · rintro rfl; exact ⟨h0, Or.inl rfl⟩
    have s0 : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) 0 = 1 := by
      simp [GlobalTheory.cubeSign, Finset.filter_eq_empty_iff]
    have si : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) i = -1 := by
      have hp : (0 : Fin (d + 1)) < i := Fin.pos_iff_ne_zero.2 h
      have : ({0, i} : Finset (Fin (d + 1))).filter (· < i) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hb⟩
          · rfl
          · exact absurd hb (lt_irrefl _)
        · rintro rfl; exact ⟨Or.inl rfl, hp⟩
      simp [GlobalTheory.cubeSign, this]
    rw [wd_apply', Finset.sum_pair h0, e0, ei, s0, si]
    simp [app, inlE, sub_eq_add_neg, add_comm]
  have hr : π (wd (fun l : Mi d => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d)))
      (fun L' => detC T.rowMu (uni {0, i} L')) L) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [wd_apply', map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : app (fun _ : Fin (d + 1) => (1 : S)) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d) = T.mu l := by simp [app, inrE]
    rw [map_zsmul]
    simp [this, map_mu T π y hX hY l]
  rw [hl] at h1
  have h2 := congrArg π h1
  rw [map_add (f := _), map_zsmul, hr, smul_zero, add_zero, map_sub] at h2
  simpa [sub_eq_zero] using h2

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.kapInd_of :
    ThMu → WdUni → KapInd := by
  intro hM hU F K _ _ _ _ _ _ d x _ S E _ _ _ _ T π hX hY i L _
  have hZ : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).X j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  have hZ' : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).Y j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  rw [ind_of hM hU T π _ hX hY i L, kap,
    map_rowMu T π (fun j => algebraMap F K (x j)) hX hY,
    map_rowMu (sysZ K x 0) (Algebra.TensorProduct.lmul' ℂ) (fun j => algebraMap F K (x j)) hZ hZ']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RatioMemRB
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma omB_smul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hu

private lemma ratio_mem_rB {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (i j : Fin (d + 1)) :
    algebraMap F K (x j / x i) ∈ rB ℂ K x {i} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have h : x j / x i ∈ rA ℂ x {i} := Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  exact isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))

private lemma omG_ratio {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) (N : ℕ) :
    ((x j : F) / x i) ^ (N + d + 1) * ((x i : F) / x j) ^ N * omG x j = omG x i := by
  have hi : (x i : F) ≠ 0 := (x i).ne_zero
  have hj : (x j : F) ≠ 0 := (x j).ne_zero
  have h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1) := by
    simp only [omG]
    rw [show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    field_simp
  rw [h, ← inv_div (x j : F) (x i : F)]
  have ha : (x j : F) / x i ≠ 0 := div_ne_zero hj hi
  generalize (x j : F) / x i = a at ha ⊢
  rw [inv_pow, inv_pow]
  field_simp
  ring

private lemma pair_prod {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) :
    (∏ l ∈ ({i, j} : Finset (Fin (d + 1))), (x l : F) / x i) = (x j : F) / x i := by
  by_cases h : i = j
  · subst h
    simp
  · rw [Finset.prod_pair h, div_self (x i).ne_zero, one_mul]

private theorem key_lemma' {K : Type} [Field K] [Algebra ℂ K] (s t : K) (y z : DR ℂ K) :
    actZ K (s ⊗ₜ[ℂ] t) (y ⊗ₜ[ℂ] z) = (s • y) ⊗ₜ[ℂ] (t • z) := by
  simp [actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]

private lemma key {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q) (a : ℕ) (i j : Fin (d + 1))
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) (hm : m ∈ MZ F K (xv x) a {j} {j}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
      (algebraMap F K ((x i : F) / x j) ^ N)) m ∈ MZ F K (xv x) a {i} {j} := by
  have hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := ratio_mem_rB K (xv x) i j
  have hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j} := ratio_mem_rB K (xv x) j i
  have gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a,
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
        (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈
          MZ F K (xv x) a {i} {j} := by
    intro y hy z hz
    have hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a) :=
      hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j)
        (Finset.singleton_subset_iff.mpr (by simp)) hy
    obtain ⟨N1, hN1⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'
    have hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      rw [← pair_prod x i j]
      exact hN1
    refine ⟨N1, fun N hN => ?_⟩
    rw [TensorProduct.mk_apply, key_lemma']
    have h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈
        omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      have e : N + d + 1 = (N + d + 1 - N1) + N1 := by omega
      rw [e, pow_add, ← smul_smul]
      exact _root_.omB_smul_mem _ _ (pow_mem hu _) hN1'
    have h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a :=
      _root_.omB_smul_mem _ _ (pow_mem hv _) hz
    exact Submodule.apply_mem_map₂ _ h1 h2
  unfold MZ at hm
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    exact gen y hy z hz
  | zero => exact ⟨0, fun N _ => by simp⟩
  | add w w' _ _ h1 h2 =>
    obtain ⟨N1, h1⟩ := h1
    obtain ⟨N2, h2⟩ := h2
    exact ⟨max N1 N2, fun N hN => by
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩
  | smul c w _ h =>
    obtain ⟨N1, h⟩ := h
    exact ⟨N1, fun N hN => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h N hN)⟩

theorem UpperTheory.Gal.productCup_of_system.idIJ_of :
    IdJ → ActsLin → GoodZ → IdIJ := by
  intro hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j
  obtain ⟨m, hm, hact⟩ := hJ F K d x hc τ hτ a ha j
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q :=
    fun q => (hG F K d x hc q).2.2
  obtain ⟨N0, hN0⟩ := key x hc hmono a i j m hm
  refine ⟨_, hN0 N0 le_rfl, ?_⟩
  have h2 := (hL F K d x hc τ hτ a).2.1 m _
    ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact
  rw [Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    omG_ratio] at h2
  simpa only [map_pow] using h2
end
