module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StImageDimLe
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalCover

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularElement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing TensorProduct
open scoped Pointwise

section Flat

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem lid_rTensor_subtype_mem_smul_top (I : Ideal A) (t : I ⊗[A] M) :
    TensorProduct.lid A M (I.subtype.rTensor M t) ∈ I • (⊤ : Submodule A M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top
  | add s t hs ht => rw [map_add (f := _), map_add (f := _)]; exact add_mem hs ht

theorem exists_lid_rTensor_subtype_eq (I : Ideal A) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    ∃ t : I ⊗[A] M, TensorProduct.lid A M (I.subtype.rTensor M t) = x := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_
  rintro x x' ⟨s, rfl⟩ ⟨s', rfl⟩
  exact ⟨s + s', by rw [map_add (f := _), map_add (f := _)]⟩

theorem mem_colon_smul_top_of_flat [Module.Flat A M] (J : Ideal A) (a : A) {v : M}
    (hv : a • v ∈ J • (⊤ : Submodule A M)) :
    v ∈ LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) • (⊤ : Submodule A M) := by
  set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a
  have hex := Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul M J).injective
    rw [map_zero, LinearMap.rTensor_tmul]
    have : g 1 = Ideal.Quotient.mk J a := by simp [g, Ideal.Quotient.mk_eq_mk]
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨t, ht⟩ := (hex ((1 : A) ⊗ₜ v)).mp h0
  have := lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t
  rwa [ht, TensorProduct.lid_tmul, one_smul] at this

end Flat

theorem exists_not_mem_forall_mul_mem {R : Type} [CommRing R] (m J : Ideal R) (hJ : J ≠ ⊤)
    (h : ∃ n, m ^ n ≤ J) : ∃ a ∉ J, ∀ r ∈ m, r * a ∈ J := by
  classical
  have hkJ : m ^ Nat.find h ≤ J := Nat.find_spec h
  have hk0 : Nat.find h ≠ 0 := by
    intro h0
    apply hJ
    rw [h0, pow_zero, Ideal.one_eq_top] at hkJ
    exact top_le_iff.mp hkJ
  obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.mp
    (Nat.find_min h (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos))
  refine ⟨a, haJ, fun r hr => hkJ ?_⟩
  have : r * a ∈ m ^ (1 + (Nat.find h - 1)) := by
    rw [pow_add, pow_one]
    exact Ideal.mul_mem_mul hr ha
  rwa [Nat.add_sub_cancel' (Nat.pos_of_ne_zero hk0)] at this

section Local

variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

theorem mem_smul_top_iff_mem_map_smul_top (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by
  rw [← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem smul_mem_smul_top_of_mem (I : Ideal A) (y : B) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : y • x ∈ I • (⊤ : Submodule A M) := by
  rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hx ⊢
  exact Submodule.smul_mem _ y hx

variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]

theorem smul_regular_mod_of_pow_le (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hpow z hz
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  obtain ⟨a, haJ, hma⟩ := exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow
  have hlt : J < J ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hz' := ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z
    (Submodule.smul_mono_left le_sup_left hz)
  rw [Submodule.sup_smul, Submodule.mem_sup] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have hyw := smul_mem_smul_top_of_mem J y hw
  have hau : a • (y • u) ∈ J • (⊤ : Submodule A M) := by
    rw [smul_comm]
    have : y • (a • u) = y • (w + a • u) - y • w := by rw [smul_add]; abel
    rw [this]
    exact sub_mem hz hyw
  have hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A := by
    intro r hr
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
    by_contra hrm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hrm
    obtain ⟨r', rfl⟩ := hrm
    apply haJ
    have := J.mul_mem_left (↑r'⁻¹ : A) hr
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  have hu := h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))
  refine add_mem hw ?_
  refine Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_smul, mul_comm]
    exact Submodule.smul_mem_smul (hma r hr) Submodule.mem_top
  · rw [smul_add]
    exact add_mem hx hx'

variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M]

theorem smul_regular_mod_ideal (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (I : Ideal A) (z : M)
    (hz : y • z ∈ I • (⊤ : Submodule A M)) : z ∈ I • (⊤ : Submodule A M) := by
  set P : Submodule B M := I.map (algebraMap A B) • ⊤
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.map_maximalIdeal_le _).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ P) _
    (by simpa only [Ideal.jacobson_bot] using hle)
  rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero P]
  have hmem : Submodule.Quotient.mk (p := P) z ∈
      (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ i • (⊤ : Submodule B (M ⧸ P))) := by
    rw [Submodule.mem_iInf]
    intro n
    have hn := smul_regular_mod_of_pow_le y h0 (I ⊔ maximalIdeal A ^ n) ⟨n, le_sup_right⟩ z
      (Submodule.smul_mono_left le_sup_left hz)
    rw [Submodule.sup_smul, Submodule.mem_sup] at hn
    obtain ⟨w, hw, v, hv, rfl⟩ := hn
    rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hw hv
    rw [Ideal.map_pow] at hv
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero P).mpr hw, zero_add]
    have hmap : (((maximalIdeal A).map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).map P.mkQ ≤
        ((maximalIdeal A).map (algebraMap A B)) ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem hv)
  rw [hK] at hmem
  exact (Submodule.mem_bot B).mp hmem

end Local

theorem FlatLocalRegularElement.proof : FlatLocalRegularElement.Statement := by
  intro A B _ _ _ _ _ _ _ hloc M _ _ _ _ _ _ y _ hreg
  have h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    intro u hu
    rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero] at hu ⊢
    refine hreg ?_
    show y • Submodule.Quotient.mk u = y • (0 : M ⧸ _)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hu]
  have hR := smul_regular_mod_ideal (B := B) y h0
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hab' : y • a = y • b := hab
    have h := hR ⊥ (a - b) (by rw [Submodule.bot_smul, Submodule.mem_bot, smul_sub, hab', sub_self])
    rw [Submodule.bot_smul, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  · rw [Module.Flat.iff_rTensor_injective']
    intro I
    let π : M →ₗ[A] QuotSMulTop y M := (Submodule.mkQ (y • (⊤ : Submodule B M))).restrictScalars A
    let Y : M →ₗ[A] M := (LinearMap.lsmul B M y).restrictScalars A
    let μM : I ⊗[A] M →ₗ[A] M := TensorProduct.lid A M ∘ₗ I.subtype.rTensor M
    let μN : I ⊗[A] QuotSMulTop y M →ₗ[A] QuotSMulTop y M :=
      TensorProduct.lid A (QuotSMulTop y M) ∘ₗ I.subtype.rTensor (QuotSMulTop y M)
    have hμM : Function.Injective μM :=
      (TensorProduct.lid A M).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
    have natπ : μN ∘ₗ π.lTensor I = π ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μN, μM, π]
    have natY : μM ∘ₗ Y.lTensor I = Y ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μM, Y, smul_comm (i : A) y m]
    have hπY : π ∘ₗ Y = 0 := LinearMap.ext fun m =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_pointwise_smul m y ⊤ Submodule.mem_top)
    refine Function.Injective.of_comp (f := TensorProduct.lid A (QuotSMulTop y M)) ?_
    change Function.Injective μN
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    have hπs : Function.Surjective π := Submodule.mkQ_surjective (y • (⊤ : Submodule B M))
    obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective I hπs t
    have h1 : π (μM s) = 0 := by
      rw [← LinearMap.comp_apply π μM, ← natπ, LinearMap.comp_apply]
      exact ht
    have h2 : μM s ∈ y • (⊤ : Submodule B M) := (Submodule.Quotient.mk_eq_zero _).mp h1
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
    have h3 : y • z ∈ I • (⊤ : Submodule A M) := hz ▸ lid_rTensor_subtype_mem_smul_top I s
    obtain ⟨s', hs'⟩ := exists_lid_rTensor_subtype_eq I (hR I z h3)
    have h4 : s = Y.lTensor I s' := by
      apply hμM
      rw [← LinearMap.comp_apply μM (Y.lTensor I), natY, LinearMap.comp_apply]
      change μM s = y • μM s'
      rw [show μM s' = z from hs', hz]
    rw [h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπY, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermProjectionOpenNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermProjectionOpenNear.proof (hiso : IsolatedFibreNear.Statement)
    (himg : IrreducibleGermProjectionImageNear.Statement) (hopen : FiniteGermProjectionOpenAt.Statement) :
    IrreducibleGermProjectionOpenNear.Statement := by
  intro σ _ X w d A hX hirr hisow hinj
  obtain ⟨N₁, hN₁, h₁⟩ := hiso σ X w d A hX hisow
  obtain ⟨N₂, hN₂, h₂⟩ := himg σ X w d A hX hirr hisow hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩
  rintro x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV

  have hXx : IsAnalyticNear X x := ⟨N, k, f, hNo, hxN, hf, hXN⟩
  exact hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalBoundedQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem monic_eval_div_mul_pow {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hG)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := j.isLt.le
  have hGd : G ^ d = G ^ (j : ℕ) * G ^ (d - (j : ℕ)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hGd, div_pow]
  field_simp

theorem NormalBoundedQuotient.proof (hwi : WeaklyHolomorphicIntegral.Statement)
    (hic : NormalGermIntegrallyClosed.Statement) : NormalBoundedQuotient.Statement := by
  intro σ _ I w N F G hI hIc hw hN hwN hF hG hnv hb

  have hhol : HolomorphicOnSubset (fun z => F z / G z) ((zeroSetIn I ∩ N) \ {z | G z = 0}) := by
    intro z hz
    refine ⟨N ∩ G ⁻¹' {0}ᶜ, hG.continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton,
      ⟨hz.1.2, hz.2⟩, fun z => F z / G z, ?_, fun _ _ => rfl⟩
    have hsub : N ∩ G ⁻¹' {0}ᶜ ⊆ N := Set.inter_subset_left
    simp only [div_eq_mul_inv]
    exact (hF.mono hsub).mul ((hG.mono hsub).inv fun y (hy : y ∈ N ∩ G ⁻¹' {0}ᶜ) => hy.2)
  obtain ⟨V, hVo, hwV, hVN, d, a, ha, heq⟩ :=
    hwi σ I w N G (fun z => F z / G z) hI hIc hw hN hwN hG hnv hhol hb
  refine hic σ I w V F G d a hI hIc hw hVo hwV (hF.mono hVN) (hG.mono hVN) ha hnv ?_
  intro z hz
  rw [monic_eval_div_mul_pow (fun j => a j z) (show G z ≠ 0 from hz.2), heq z hz, mul_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteFibreGermIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteFibreGermIntegral.proof (hWF : WeierstrassFiniteness.Statement)
    (hR : RueckertNullstellensatz.Statement) : FiniteFibreGermIntegral.Statement := by
  intro σ _ X x d A hX hiso g hg
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hfx : ∀ i, AnalyticAt ℂ (f i) x := fun i => hf i x hxN
  have hAj : ∀ j : Fin d, AnalyticAt ℂ (fun z => A z j - A x j) x := fun j =>
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt x).sub
      analyticAt_const

  let F : Fin (k + d) → (σ → ℂ) → ℂ := Fin.append f (fun j z => A z j - A x j)
  have hFx : ∀ i, AnalyticAt ℂ (F i) x := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [F, Fin.append_left] using hfx i
    · simpa only [F, Fin.append_right] using hAj j
  have hcoord : ∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j) := by
    intro l
    have hl : AnalyticAt ℂ (fun z : σ → ℂ => z l - x l) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) l).analyticAt x).sub analyticAt_const
    have hvan : ∀ᶠ z in 𝓝 x, (∀ i, F i z = 0) → z l - x l = 0 := by
      filter_upwards [hNo.mem_nhds hxN, hW] with z hzN hzW h0
      have hf0 : ∀ i, f i z = 0 := fun i => by simpa only [F, Fin.append_left] using h0 (Fin.castAdd d i)
      have hA0 : A z = A x := funext fun j =>
        sub_eq_zero.1 (by simpa only [F, Fin.append_right] using h0 (Fin.natAdd k j))
      have hzX : z ∈ X := by
        have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hzN, hf0⟩
        exact this.1
      rw [hWiso z ⟨hzX, hzW⟩ hA0, sub_self]
    obtain ⟨m, h, -, hh, hsum⟩ := hR σ x (k + d) F (fun z => z l - x l) hFx hl hvan
    refine ⟨m, fun i => h (Fin.castAdd d i), fun j => h (Fin.natAdd k j), fun i => hh _, fun j => hh _, ?_⟩
    filter_upwards [hsum] with z hz
    rw [hz, Fin.sum_univ_add]
    simp only [F, Fin.append_left, Fin.append_right]
  obtain ⟨n, a, h, ha, -, hrel⟩ := hWF σ x k f d A hfx hcoord g hg
  refine ⟨n, a, ha, ?_⟩
  filter_upwards [hrel, hNo.mem_nhds hxN] with z hz hzN hzX
  have hz0 : z ∈ X ∩ N := ⟨hzX, hzN⟩
  rw [hXN] at hz0
  rw [hz]
  simp [hz0.2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionProperBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionProperBall.proof : FiniteProjectionProperBall.Statement := by
  intro σ _ X w d A hX hiso U hU
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hmem : N ∩ U ∩ W ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hBN : Metric.closedBall w ρ ⊆ N := fun x hx => (hball hx).1.1

  set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef
  have hCX : ∀ x ∈ C, x ∈ X := by
    intro x hx
    have hxN := hBN hx.1
    have : x ∈ X ∩ N := by
      rw [hXN]
      refine ⟨hxN, fun i => ?_⟩
      have := congrFun (show (fun i => f i x) = 0 from hx.2) i
      simpa using this
    exact this.1
  have hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C := by
    intro x hxX hxB
    have : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := hXN ▸ ⟨hxX, hBN hxB⟩
    refine ⟨hxB, ?_⟩
    show (fun i => f i x) = 0
    funext i
    simpa using this.2 i
  have hCcl : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton
    exact continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN
  have hC : IsCompact C := (isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left

  set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef
  have hS : IsCompact S := hC.inter_right Metric.isClosed_sphere
  have hT : IsCompact (A '' S) := hS.image A.continuous
  have hAw : A w ∉ A '' S := by
    rintro ⟨x, hxS, hxA⟩
    have hxw : x = w := hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA
    have hd := hxS.2
    rw [hxw, Metric.mem_sphere, dist_self] at hd
    exact hρ.ne hd
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw
  refine ⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩
  intro K hKr hK
  have heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxB⟩, hxK⟩
      exact ⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩
    · rintro ⟨hxC, hxK⟩
      refine ⟨⟨hCX x hxC, ?_⟩, hxK⟩
      have hle : dist x w ≤ ρ := hxC.1
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))
  rw [heq]
  exact hC.inter_right (hK.isClosed.preimage A.continuous)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionBranchLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionBranchLocus.proof (hL : ProperOpenProjectionLocalCover.Statement)
    (hH : FibreDiscriminantHolomorphic.Statement) (hM : MaximalCountUnbranched.Statement) :
    ProperOpenProjectionBranchLocus.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hDc hDne hmaps hprop hopen
  have loc := hL σ X B k f d A D hB hf hXB hDo hmaps hprop hopen
  choose! U g n hUo hyU hUD hg hgd hle hgen using loc

  have key : ∀ y₀ ∈ D, ∀ y ∈ U y₀, n y = n y₀ := by
    intro y₀ hy₀ y hy
    have hyD : y ∈ D := hUD y₀ hy₀ hy
    obtain ⟨t₁, ht₁, hgt₁⟩ := hgd y₀ hy₀ (U y ∩ U y₀) ((hUo y hyD).inter (hUo y₀ hy₀))
      Set.inter_subset_right ⟨y, hyU y hyD, hy⟩
    have hWo : IsOpen (U y ∩ (U y₀ ∩ g y₀ ⁻¹' {0}ᶜ)) :=
      (hUo y hyD).inter ((hg y₀ hy₀).continuousOn.isOpen_inter_preimage (hUo y₀ hy₀) isOpen_compl_singleton)
    obtain ⟨t, ht, hgt⟩ := hgd y hyD _ hWo Set.inter_subset_left
      ⟨t₁, ht₁.1, ht₁.2, by simpa using hgt₁⟩
    have e1 := (hgen y hyD t ht.1 hgt).1
    have e2 := (hgen y₀ hy₀ t ht.2.1 (by simpa using ht.2.2)).1
    exact_mod_cast e1.symm.trans e2
  obtain ⟨y₀, hy₀⟩ := hDne
  have hcont : ContinuousOn n D := by
    intro y hy
    have hc0 : ContinuousAt (fun _ : Fin d → ℂ => n y) y := continuousAt_const
    have hca : ContinuousAt n y := by
      refine hc0.congr ?_
      filter_upwards [(hUo y hy).mem_nhds (hyU y hy)] with z hz
      exact (key y hy z hz).symm
    exact hca.continuousWithinAt
  have hN : ∀ y ∈ D, n y = n y₀ := fun y hy => hDc.constant hcont hy hy₀

  have hcov : IsGenericCountCover (X ∩ B) A D (n y₀) := by
    refine ⟨fun y hy => ?_, fun y hy => ⟨U y, g y, hUo y hy, hyU y hy, hUD y hy, hg y hy, hgd y hy,
      fun z hz hgz => ?_⟩⟩
    · have := hle y hy y (hyU y hy)
      rwa [hN y hy] at this
    · obtain ⟨h1, h2⟩ := hgen y hy z hz hgz
      exact ⟨by rw [h1, hN y hy], h2⟩

  obtain ⟨ys, hysU, hgys⟩ := hgd y₀ hy₀ (U y₀) (hUo y₀ hy₀) subset_rfl ⟨y₀, hyU y₀ hy₀⟩
  have hysD : ys ∈ D := hUD y₀ hy₀ hysU
  have hcys : {x | x ∈ X ∩ B ∧ A x = ys}.encard = (n y₀ : ℕ∞) := (hgen y₀ hy₀ ys hysU hgys).1
  have hfin := Set.finite_of_encard_eq_coe hcys
  obtain ⟨l₀, hl₀⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun p : hfin.toFinset.offDiag => (p.1.1 - p.1.2 : σ → ℂ))
    (fun p => sub_ne_zero.2 (Finset.mem_offDiag.1 p.2).2.2)
  let l : (σ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  refine ⟨fibreDiscr (X ∩ B) A l (n y₀), hH σ (X ∩ B) d A D (n y₀) l hDo hmaps hprop hopen hcov,
    ⟨ys, hysD, ?_⟩, ?_⟩
  · unfold fibreDiscr
    rw [dite_eq_left hcys, Finset.prod_ne_zero_iff]
    intro p hp
    have := hl₀ ⟨p, hp⟩
    simpa [l, map_sub, sub_eq_zero] using this
  · intro x hx hδ
    have hc : {x' | x' ∈ X ∩ B ∧ A x' = A x}.encard = (n y₀ : ℕ∞) := by
      by_contra hne
      exact hδ (by unfold fibreDiscr; rw [dite_eq_right hne])
    exact hM σ (X ∩ B) d A D (n y₀) hDo hmaps hprop hopen hcov x hx hc

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassFiniteness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem WeierstrassFiniteness.proof (hE : FiniteModuloEliminate.Statement)
    (hI : FiniteModuloIntegral.Statement) : WeierstrassFiniteness.Statement := by
  intro σ _ x k f d A hf hpow g hg
  classical

  let L : Finset σ → (σ → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) := fun S =>
    ContinuousLinearMap.pi (Sum.elim (fun j => (ContinuousLinearMap.proj j).comp A)
      (fun l => if l ∈ S then ContinuousLinearMap.proj l else 0))
  have hL : ∀ S z c, L S z c = Sum.elim (fun j => A z j) (fun l => if l ∈ S then z l else 0) c := by
    intro S z c
    rcases c with j | l
    · simp [L]
    · by_cases hl : l ∈ S <;> simp [L, hl]
  have key : ∀ T : Finset σ, IsFiniteModuloOver x f (L (Finset.univ \ T)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sdiff_empty]
      let P : (Fin d ⊕ σ → ℂ) →L[ℂ] (σ → ℂ) :=
        ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
      have hPL : ∀ z, P (L Finset.univ z) = z := fun z => by
        funext l; simp [P, hL]
      refine ⟨1, fun _ _ => 1, fun _ => analyticAt_const, fun g hg => ?_⟩
      refine ⟨fun _ y => g (P y), fun _ _ => 0, fun _ => ?_, fun _ => analyticAt_const,
        Eventually.of_forall fun z => by simp only [hPL]; simp⟩
      have hg' : AnalyticAt ℂ g (P (L Finset.univ x)) := by rw [hPL]; exact hg
      exact hg'.comp (P.analyticAt _)
    | insert l T hl ih =>
      have heq : L (Finset.univ \ insert l T) = (zeroCoordinate (Sum.inr l)).comp (L (Finset.univ \ T)) := by
        ext z c
        rw [ContinuousLinearMap.comp_apply, zeroCoordinate_apply, hL, hL]
        rcases c with j | l'
        · simp
        · by_cases h1 : l' = l
          · subst h1; simp
          · by_cases h2 : l' ∈ T <;> simp [h1, h2]
      rw [heq]
      obtain ⟨r, h, h', hh, hh', hev⟩ := hpow l
      refine hE σ (Fin d ⊕ σ) x k f _ (Sum.inr l) hf ih
        ⟨r, h, Sum.elim h' (fun _ _ => 0), hh, ?_, ?_⟩
      · rintro (j | l')
        · exact hh' j
        · exact analyticAt_const
      · filter_upwards [hev] with z hz
        simp only [zeroCoordinate_apply, hL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
          Finset.mem_sdiff, Finset.mem_univ, hl, not_false_eq_true, and_self, if_true,
          reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero, add_zero]
        exact hz
  have hfin := key Finset.univ
  obtain ⟨N, a, h, ha, hh, hev⟩ := hI σ (Fin d ⊕ σ) x k f _ hf hfin g hg

  let J : (Fin d → ℂ) →L[ℂ] (Fin d ⊕ σ → ℂ) :=
    ContinuousLinearMap.pi (Sum.elim (fun j => ContinuousLinearMap.proj j) (fun _ => 0))
  have hJ : ∀ z, J (A z) = L (Finset.univ \ Finset.univ) z := fun z => by
    funext c; rcases c with j | l <;> simp [J, hL]
  refine ⟨N, fun j w => a j (J w), h, fun j => ?_, hh, ?_⟩
  · have haj : AnalyticAt ℂ (a j) (J (A x)) := by rw [hJ]; exact ha j
    exact haj.comp (J.analyticAt _)
  · filter_upwards [hev] with z hz
    simpa only [hJ] using hz

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRootSumHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Filter Topology

noncomputable section

theorem RootSumHolomorphic.proof : RootSumHolomorphic.Statement := by
  intro d m W Φ hm hW hsep hΦ y₀ hy₀
  obtain ⟨R, hR⟩ : ∃ R : Finset ℂ, R = (m.map (MvPolynomial.eval y₀)).roots.toFinset := ⟨_, rfl⟩
  have hroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).IsRoot τ := fun τ hτ => by
    rw [hR] at hτ
    exact (Polynomial.mem_roots (hm.map _).ne_zero).1 (Multiset.mem_toFinset.1 hτ)
  have hder : ∀ τ ∈ R, (m.map (MvPolynomial.eval y₀)).derivative.eval τ ≠ 0 := fun τ hτ => by
    have h := (hsep y₀ hy₀).eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ)
      (by rw [Polynomial.eval₂_id]; exact hroot τ hτ)
    rwa [Polynomial.eval₂_id] at h
  have hbr := fun τ (hτ : τ ∈ R) => SimpleRootBranch.proof d m y₀ τ (hroot τ hτ) (hder τ hτ)
  choose! U B ψ hUo hyU hBo hτB hψd hψy hψroot using hbr
  have hloc := fun τ (hτ : τ ∈ R) => hΦ y₀ hy₀ τ (hroot τ hτ)
  choose! O hOo hyO Ψ hΨd hΨeq using hloc
  obtain ⟨V, hV, hVdisj⟩ := (R.finite_toSet).t2_separation

  have hev : ∀ᶠ y in 𝓝 y₀, ∀ τ ∈ R, y ∈ U τ ∧ ψ τ y ∈ B τ ∩ V τ ∧ (y, ψ τ y) ∈ O τ := by
    refine (Filter.eventually_all_finset R).2 fun τ hτ => ?_
    have hψc : ContinuousAt (ψ τ) y₀ :=
      ((hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))).continuousAt
    have hBV : B τ ∩ V τ ∈ 𝓝 (ψ τ y₀) := by
      rw [hψy τ hτ]; exact ((hBo τ hτ).inter (hV τ).2).mem_nhds ⟨hτB τ hτ, (hV τ).1⟩
    have hO : O τ ∈ 𝓝 (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hOo τ hτ).mem_nhds (hyO τ hτ)
    have hpc : ContinuousAt (fun y => (y, ψ τ y)) y₀ := continuousAt_id.prodMk hψc
    exact Filter.Eventually.and ((hUo τ hτ).mem_nhds (hyU τ hτ))
      (Filter.Eventually.and (hψc.preimage_mem_nhds hBV) (hpc.preimage_mem_nhds hO))

  have heq : ∀ᶠ y in 𝓝 y₀, ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum =
      ∑ τ ∈ R, Ψ τ (y, ψ τ y) := by
    filter_upwards [hev] with y hy
    have hisroot : ∀ τ ∈ R, (m.map (MvPolynomial.eval y)).IsRoot (ψ τ y) := fun τ hτ =>
      ((hψroot τ hτ y (hy τ hτ).1).2 _ (hy τ hτ).2.1.1).2 rfl
    have hinj : ∀ τ ∈ R.val, ∀ τ' ∈ R.val, ψ τ y = ψ τ' y → τ = τ' := by
      intro τ hτ τ' hτ' h
      by_contra hne
      have h' : ψ τ y ∈ V τ' := by rw [h]; exact (hy τ' hτ').2.1.2
      exact Set.disjoint_left.1 (hVdisj hτ hτ' hne) (hy τ hτ).2.1.2 h'
    have hM : R.val.map (fun τ => ψ τ y) = (m.map (MvPolynomial.eval y)).roots := by
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset (Multiset.Nodup.map_on hinj R.nodup)]
        intro s hs
        obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hs
        exact (Polynomial.mem_roots (hm.map _).ne_zero).2 (hisroot τ hτ)
      · have h1 : Multiset.card (R.val.map fun τ => ψ τ y) = m.natDegree := by
          rw [Multiset.card_map, Finset.card_val, hR,
            Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (hsep y₀ hy₀)),
            IsAlgClosed.card_roots_eq_natDegree, hm.natDegree_map]
        rw [h1, ← hm.natDegree_map (MvPolynomial.eval y)]
        exact Polynomial.card_roots' _
    rw [← hM, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun τ hτ => ?_
    exact hΨeq τ hτ (y, ψ τ y) (hy τ hτ).2.2 (hisroot τ hτ)

  have hg : DifferentiableAt ℂ (fun y => ∑ τ ∈ R, Ψ τ (y, ψ τ y)) y₀ := by
    refine DifferentiableAt.fun_sum (A := fun τ y => Ψ τ (y, ψ τ y)) fun τ hτ => ?_
    have hψ : DifferentiableAt ℂ (ψ τ) y₀ :=
      (hψd τ hτ).differentiableAt ((hUo τ hτ).mem_nhds (hyU τ hτ))
    have hΨ : DifferentiableAt ℂ (Ψ τ) (y₀, ψ τ y₀) := by
      rw [hψy τ hτ]; exact (hΨd τ hτ).differentiableAt ((hOo τ hτ).mem_nhds (hyO τ hτ))
    exact hΨ.comp y₀ (differentiableAt_id.prodMk hψ)
  exact (hg.congr_of_eventuallyEq heq).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMatricesOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def sliceDeriv {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ)) :
    (Fin (k + 1) → ℂ) →L[ℂ] (Fin (k + 1) → ℂ) :=
  (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ) : _ →L[ℂ] _) ∘L
    ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L D))

theorem sliceDeriv_apply {n k : ℕ} (L : Matrix (Fin k) (Fin n) ℂ) (D : (Fin (k + 1) → ℂ) →L[ℂ] (Fin n → ℂ))
    (v : Fin (k + 1) → ℂ) : sliceDeriv L D v = vecCons (v 0) (L *ᵥ D v) := rfl

theorem hasFDerivAt_slice {n k : ℕ} {γ : (Fin (k + 1) → ℂ) → Fin n → ℂ} {s : Fin (k + 1) → ℂ}
    (hγ : DifferentiableAt ℂ γ s) (L : Matrix (Fin k) (Fin n) ℂ) :
    HasFDerivAt (fun t => vecCons (t 0) (L *ᵥ γ t)) (sliceDeriv L (fderiv ℂ γ s)) s := by
  have h1 : HasFDerivAt
      (fun t : Fin (k + 1) → ℂ => ((t 0, (Matrix.mulVecLin L).toContinuousLinearMap (γ t)) : ℂ × (Fin k → ℂ)))
      ((ContinuousLinearMap.proj 0).prod ((Matrix.mulVecLin L).toContinuousLinearMap ∘L fderiv ℂ γ s)) s :=
    (hasFDerivAt_apply 0 s).prodMk
      ((Matrix.mulVecLin L).toContinuousLinearMap.hasFDerivAt.comp s hγ.hasFDerivAt)
  exact (Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).hasFDerivAt.comp s h1

theorem bijective_iff_det_ne_zero {N : ℕ} (f : (Fin N → ℂ) →L[ℂ] (Fin N → ℂ)) :
    Function.Bijective f ↔ LinearMap.det (f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.1 h⟩⟩

theorem SliceMatricesOpen.proof : SliceMatricesOpen.Statement := by
  intro n k m γ s hd hinj
  have hfd : ∀ (L : Matrix (Fin k) (Fin n) ℂ) b,
      fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b) = sliceDeriv L (fderiv ℂ (γ b) (s b)) :=
    fun L b => (hasFDerivAt_slice (hd b) L).fderiv
  constructor
  · have hset : {L : Matrix (Fin k) (Fin n) ℂ |
        ∀ b, Function.Bijective (fderiv ℂ (fun t => vecCons (t 0) (L *ᵥ γ b t)) (s b))} =
        ⋂ b, {L | LinearMap.det
          (sliceDeriv L (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ)) ≠ 0} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hfd, bijective_iff_det_ne_zero]
    rw [hset]
    refine isOpen_iInter_of_finite fun b => isOpen_ne_fun ?_ continuous_const
    simp_rw [← LinearMap.det_toMatrix']
    refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, sliceDeriv_apply]
    refine Fin.cases ?_ (fun r => ?_) i
    · simp only [Matrix.cons_val_zero]
      exact continuous_const
    · simp only [Matrix.cons_val_succ]
      exact (continuous_apply r).comp (continuous_id.matrix_mulVec continuous_const)
  · set Lb : Fin m → (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) := fun b =>
      (fderiv ℂ (γ b) (s b) : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        ((Fin.consEquivL ℂ (fun _ : Fin (k + 1) => ℂ)).toLinearEquiv.toLinearMap ∘ₗ
          LinearMap.inr ℂ ℂ (Fin k → ℂ)) with hLbdef
    have hLapp : ∀ b w, Lb b w = fderiv ℂ (γ b) (s b) (Fin.cons 0 w) := fun b w => rfl
    have hL : ∀ b, Function.Injective (Lb b) := by
      intro b
      refine (injective_iff_map_eq_zero (Lb b)).2 fun w hw => ?_
      rw [hLapp] at hw
      have h0 := hinj b (Fin.cons 0 w) (by simp) hw
      funext i
      simpa using congrFun h0 i.succ
    obtain ⟨π, hπ⟩ := IndefiniteRowSideFullHecke.ComplexSets.GeneralProjection.proof n k m Lb hL
    refine ⟨π, fun b => ?_⟩
    rw [hfd]
    have hΦ : Function.Injective (sliceDeriv π (fderiv ℂ (γ b) (s b))) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
      rw [sliceDeriv_apply] at hv
      have hv0 : v 0 = 0 := by simpa using congrFun hv 0
      have hvc : v = Fin.cons 0 (Fin.tail v) := by rw [← hv0, Fin.cons_self_tail]
      have hw : π *ᵥ Lb b (Fin.tail v) = π *ᵥ Lb b 0 := by
        rw [map_zero, Matrix.mulVec_zero, hLapp, ← hvc]
        funext r
        simpa using congrFun hv r.succ
      rw [hvc, hπ b hw]
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    exact ⟨hΦ, (LinearMap.injective_iff_surjective
      (f := (sliceDeriv π (fderiv ℂ (γ b) (s b)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] _))).1 hΦ⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem germ_eventually_zero_of_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {y : E}
    (hf : AnalyticAt ℂ f y) (hg : AnalyticAt ℂ g y) (hfg : ∀ᶠ z in 𝓝 y, f z * g z = 0) :
    (∀ᶠ z in 𝓝 y, f z = 0) ∨ (∀ᶠ z in 𝓝 y, g z = 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hf0 : ∀ z ∈ Metric.ball y r, f z = 0
  · exact Or.inl (Filter.mem_of_superset (Metric.ball_mem_nhds y hr) hf0)
  · right
    push Not at hf0
    obtain ⟨p, hp, hfp⟩ := hf0
    have hgp : g =ᶠ[𝓝 p] 0 := by
      filter_upwards [(hball hp).1.1.continuousAt.eventually_ne hfp, Metric.isOpen_ball.mem_nhds hp]
        with z hz1 hz2
      exact (mul_eq_zero.1 (hball hz2).2).resolve_left hz1
    have hgan : AnalyticOnNhd ℂ g (Metric.ball y r) := fun z hz => (hball hz).1.2
    have hzero := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y r).isPreconnected hp hgp
    exact Filter.mem_of_superset (Metric.ball_mem_nhds y hr) fun z hz => by simpa using hzero hz

theorem germ_prod_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    (h : ι → E → ℂ) {y : E} (s : Finset ι) (han : ∀ i ∈ s, AnalyticAt ℂ (h i) y)
    (hprod : ∀ᶠ z in 𝓝 y, ∏ i ∈ s, h i z = 0) : ∃ i ∈ s, ∀ᶠ z in 𝓝 y, h i z = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨z, hz⟩ := hprod.exists
    simp at hz
  | insert a s ha ih =>
    have hg : AnalyticAt ℂ (fun z => ∏ i ∈ s, h i z) y :=
      Finset.analyticAt_fun_prod s fun i hi => han i (Finset.mem_insert_of_mem hi)
    have hprod' : ∀ᶠ z in 𝓝 y, h a z * ∏ i ∈ s, h i z = 0 := by
      filter_upwards [hprod] with z hz
      rwa [Finset.prod_insert ha] at hz
    rcases germ_eventually_zero_of_mul (han a (Finset.mem_insert_self a s)) hg hprod' with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, h2⟩ := ih (fun i hi => han i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, h2⟩

theorem mem_of_projection_germ_injective {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X x)
    (hinj : ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) → (∀ᶠ z in 𝓝 x, z ∈ X → h (A z) = 0) →
      ∀ᶠ y in 𝓝 (A x), h y = 0) : x ∈ X := by
  by_contra hx
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  have hne : ∃ i, f i x ≠ 0 := by
    by_contra hall
    push Not at hall
    have hmem : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hxN, hall⟩
    rw [← hXN] at hmem
    exact hx hmem.1
  obtain ⟨i, hi⟩ := hne
  have hev : ∀ᶠ z in 𝓝 x, z ∈ X → (fun _ : Fin d → ℂ => (1 : ℂ)) (A z) = 0 := by
    filter_upwards [(hf i x hxN).continuousAt.eventually_ne hi, hNo.mem_nhds hxN] with z hz1 hz2 hzX
    have hmem : z ∈ X ∩ N := ⟨hzX, hz2⟩
    rw [hXN] at hmem
    exact absurd (hmem.2 i) hz1
  obtain ⟨y, hy⟩ := (hinj (fun _ => 1) analyticAt_const hev).exists
  exact one_ne_zero hy

theorem FiniteGermProjectionOpenAt.proof (hcomp : AnalyticGermComponents.Statement)
    (hirr : IrreducibleFiniteGermProjectionOpenAt.Statement) : FiniteGermProjectionOpenAt.Statement := by
  classical
  intro σ _ X x d A hX hiso hinj V hV
  have hxX : x ∈ X := mem_of_projection_germ_injective A hX hinj
  obtain ⟨n, Y, hY, W, hW, hXW⟩ := hcomp σ X x hX hxX
  obtain ⟨W₀, hW₀, hisoW₀⟩ := hiso

  have hsome : ∃ i, ∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A x) →
      (∀ᶠ z in 𝓝 x, z ∈ Y i → h (A z) = 0) → ∀ᶠ y in 𝓝 (A x), h y = 0 := by
    by_contra hnone
    push Not at hnone
    choose h han hvan hne using hnone
    have hprod : ∀ᶠ y in 𝓝 (A x), ∏ i ∈ Finset.univ, h i y = 0 := by
      have hpan : AnalyticAt ℂ (fun y => ∏ i ∈ Finset.univ, h i y) (A x) :=
        Finset.analyticAt_fun_prod Finset.univ fun i _ => han i
      refine hinj (fun y => ∏ i ∈ Finset.univ, h i y) hpan ?_
      filter_upwards [Filter.eventually_all.2 hvan, hW] with z hz hzW hzX
      have hmem : z ∈ (⋃ i, Y i) ∩ W := by
        rw [← hXW]
        exact ⟨hzX, hzW⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hmem.1
      exact Finset.prod_eq_zero (Finset.mem_univ i) (hz i hi)
    obtain ⟨i, -, hi⟩ := germ_prod_eventually_zero h Finset.univ (fun i _ => han i) hprod
    exact hne i (hi.mono fun z hz => not_not.2 hz)
  obtain ⟨i, hi⟩ := hsome
  have hYX : Y i ∩ W ⊆ X := fun z hz => by
    have hmem : z ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hz.1⟩, hz.2⟩
    rw [← hXW] at hmem
    exact hmem.1
  have hisoY : ∃ W' ∈ 𝓝 x, ∀ x' ∈ Y i ∩ W', A x' = A x → x' = x :=
    ⟨W ∩ W₀, Filter.inter_mem hW hW₀, fun x' hx' hAx' => hisoW₀ x' ⟨hYX ⟨hx'.1, hx'.2.1⟩, hx'.2.2⟩ hAx'⟩
  have himg := hirr σ (Y i) x d A (hY i).1 (hY i).2 hisoY hi (V ∩ W) (Filter.inter_mem hV hW)
  refine Filter.mem_of_superset himg (Set.image_mono ?_)
  rintro z ⟨hzY, hzV, hzW⟩
  exact ⟨hYX ⟨hzY, hzW⟩, hzV⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
