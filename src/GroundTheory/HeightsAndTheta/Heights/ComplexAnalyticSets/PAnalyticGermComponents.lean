module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace AnalyticGermComponents

variable {σ : Type} [Fintype σ]

def vanishingIdeal (X : Set (σ → ℂ)) (w : σ → ℂ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0}
  add_mem' := by
    rintro a b ⟨f, hf, hf0⟩ ⟨g, hg, hg0⟩
    refine ⟨f + g, ?_, ?_⟩
    · show ((f + g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (a : Germ (𝓝 w) ℂ) + (b : Germ (𝓝 w) ℂ)
      rw [← hf, ← hg]
      rfl
    · filter_upwards [hf0, hg0] with z h1 h2 hz
      simp [h1 hz, h2 hz]
  zero_mem' := ⟨0, rfl, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hf0⟩
    obtain ⟨h, -, hh⟩ := c.2
    refine ⟨h * f, ?_, ?_⟩
    · show ((h * f : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (c : Germ (𝓝 w) ℂ) * (a : Germ (𝓝 w) ℂ)
      rw [← hh, ← hf]
      rfl
    · filter_upwards [hf0] with z h1 hz
      simp [h1 hz]

theorem mem_vanishingIdeal_iff {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by
  constructor
  · rintro ⟨g, hg, hg0⟩
    have he : g =ᶠ[𝓝 w] f := Germ.coe_eq.1 hg
    filter_upwards [hg0, he] with z h1 h2 hz
    rw [← h2]
    exact h1 hz
  · intro h
    exact ⟨f, rfl, h⟩

theorem vanishingIdeal_anti {X X' : Set (σ → ℂ)} {w : σ → ℂ} (hXX' : X' ⊆ X) :
    vanishingIdeal X w ≤ vanishingIdeal X' w := by
  rintro φ ⟨f, hf, hf0⟩
  refine ⟨f, hf, ?_⟩
  filter_upwards [hf0] with z h hz
  exact h (hXX' hz)

theorem isAnalyticNear_inter_zero {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by
  obtain ⟨N, k, F, hN, hwN, hF, hXN⟩ := hX
  refine ⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro z hz
      simpa using hz.2
    · intro z hz
      simpa using hF j z hz.1
  · ext z
    have e := Set.ext_iff.1 hXN z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨hzX, hfz⟩, hzN, hza⟩
      exact ⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩
    · rintro ⟨⟨hzN, hza⟩, hfz, hFz⟩
      exact ⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩

theorem apply_eq_zero_of_not {X : Set (σ → ℂ)} {w : σ → ℂ} {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hfg : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) (hng : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) : f w = 0 := by
  by_contra h0
  apply hng
  have hev : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuousAt.eventually_ne h0
  filter_upwards [hfg, hev] with z h1 h2 hz
  exact (mul_eq_zero.1 (h1 hz)).resolve_left h2

theorem vanishingIdeal_lt {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by
  refine lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_
  have hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w :=
    (mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)
  rw [← heq] at hm
  exact (mem_vanishingIdeal_iff hf).1 hm

theorem exists_finset {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by
  classical
  suffices H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w →
      w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
        ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro X hJ hX hw
  by_cases hirr : GermIrreducibleAt X w
  · refine ⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩
    · intro Y hY
      rw [Finset.mem_singleton] at hY
      exact hY ▸ ⟨hX, hirr⟩
    · simp
  obtain ⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧
      ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by
    by_contra hcon
    refine hirr ⟨hw, fun f g hf hg hfg => ?_⟩
    by_contra h
    rw [not_or] at h
    exact hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩
  have hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0 := by
    filter_upwards [hfg] with z h hz
    rw [mul_comm]
    exact h hz
  have hfw : f w = 0 := apply_eq_zero_of_not hf hfg hng
  have hgw : g w = 0 := apply_eq_zero_of_not hg hgf hnf
  obtain ⟨s₁, hs₁, W₁, hW₁, hX₁⟩ := ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl
    (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩
  obtain ⟨s₂, hs₂, W₂, hW₂, hX₂⟩ := ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl
    (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩
  refine ⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact hs₁ Y h
    · exact hs₂ Y h
  ext z
  have e₁ := Set.ext_iff.1 hX₁ z
  have e₂ := Set.ext_iff.1 hX₂ z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]
  constructor
  · rintro ⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases mul_eq_zero.1 (hz0 hzX) with h | h
    · obtain ⟨Y, hY, hzY⟩ := (e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1
      exact ⟨Y, Or.inl hY, hzY⟩
    · obtain ⟨Y, hY, hzY⟩ := (e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1
      exact ⟨Y, Or.inr hY, hzY⟩
  · rintro ⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases hY with hY | hY
    · exact (e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1
    · exact (e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1

theorem proof (hN : AnalyticGermsNoetherian.Statement) : AnalyticGermComponents.Statement := by
  intro σ _ X w hX hw
  obtain ⟨s, hs, W, hW, hXW⟩ := exists_finset (hN σ w) X hX hw
  refine ⟨s.card, fun i => (s.equivFin.symm i : Set (σ → ℂ)), fun i => hs _ (s.equivFin.symm i).2, W, hW, ?_⟩
  rw [hXW]
  congr 1
  ext z
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Y, hY, hz⟩
    exact ⟨s.equivFin ⟨Y, hY⟩, by simpa using hz⟩
  · rintro ⟨i, hz⟩
    exact ⟨_, (s.equivFin.symm i).2, hz⟩

end AnalyticGermComponents

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormalFibreQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem primeFibreLocalRing_nonempty_equiv_of_surjective
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by
  set q := P.comap (algebraMap S S') with hq
  have hq' : (P.comap φ).comap (algebraMap R R') = q.comap f := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]
  have hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S') := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  let ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P :=
    Localization.localRingHom (P.comap φ) P φ rfl
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨t', ht'⟩ := hφ (t : S')
    have ht'' : t' ∈ (P.comap φ).primeCompl := by
      change t' ∉ P.comap φ
      rw [Ideal.mem_comap, ht']
      exact t.2
    refine ⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'
  let χ := (Ideal.Quotient.mk ((q.map (algebraMap S S')).map
    (algebraMap S' (Localization.AtPrime P)))).comp ψ
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerχ : ((q.comap f).map (algebraMap R R')).map
      (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ := by
    ext x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap φ).primeCompl x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, htr⟩
      refine ⟨φ t, ht, ?_⟩
      rw [← map_mul, ← hmapq]
      exact Ideal.mem_map_of_mem φ htr
    · rintro ⟨t, ht, htr⟩
      obtain ⟨t', rfl⟩ := hφ t
      refine ⟨t', ht, ?_⟩
      have h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ := by
        rw [hmapq, map_mul]
        exact htr
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ] at h1
      have key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R') := by
        refine le_trans ?_ (le_trans hker (Ideal.map_mono ?_))
        · intro y hy
          simpa using hy
        · intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact q.zero_mem
      exact (sup_le le_rfl key) h1
  refine ⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩
  rw [← hkerχ, hq']

theorem exists_adicCompletion_surjection_of_surjective
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by
  have := hB
  have : IsNoetherianRing A := isNoetherianRing_of_surjective B A f hf
  set M := m.comap f with hM
  have hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n := fun n => by
    rw [Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]
  let fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n := fun n =>
    (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp
      (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)
  have hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k := by
    intro k n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h b =>
      simp only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      change Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) =
        Ideal.Quotient.mk (m ^ k) (f (b k))
      rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have hb := AdicCompletion.AdicCauchySequence.mk_eq_mk hle b
      rw [Submodule.Quotient.eq] at hb
      have hb' : b n - b k ∈ M ^ k := by simpa using hb
      rw [← map_sub]
      exact Ideal.le_comap_pow f k hb'
  let φ : AdicCompletion M B →+* AdicCompletion m A := AdicCompletion.liftRingHom m fam hfam
  have hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f := by
    refine RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom,
      RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  refine ⟨φ, ?_, hcomm, ?_⟩
  · have fgM : M.FG := IsNoetherian.noetherian M
    have fgm : m.FG := IsNoetherian.noetherian m
    have := AdicCompletion.isAdicComplete_self M fgM
    have hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ =
        m.map (algebraMap A (AdicCompletion m A)) := by
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]
    have : IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A) := by
      rw [hmap]
      exact (AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨algebraMap B _ b, ?_⟩
    rw [RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap,
      ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]
    simp [ha, AdicCompletion.algebraMap_apply]
  · intro x hx
    let _ : Algebra B A := f.toAlgebra
    let K := RingHom.ker f
    let g : B →ₗ[B] A := Algebra.linearMap B A
    have hg : Function.Surjective g := hf
    have hfg : Function.Exact K.subtype g := by
      intro y
      simp [g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    have hx' : AdicCompletion.map M g x = 0 := by
      induction x using AdicCompletion.induction_on with
      | h b => ?_
      have hb := RingHom.mem_ker.mp hx
      refine AdicCompletion.ext fun n => ?_
      have h1 : f (b n) ∈ m ^ n := by
        have := congrArg (AdicCompletion.evalₐ m n) hb
        rw [map_zero] at this
        simp only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe,
          AdicCompletion.evalₐ_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        change f (b n) ∈ (M ^ n).map f
        rw [hpow]
        exact h1
      simpa [AdicCompletion.map_mk] using h2
    obtain ⟨z, rfl⟩ := ((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite M K z
    have hnat := congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hnat
    rw [hnat]
    clear hnat hx hx'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
        Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem h₁ h₂

theorem FormalFibreQuotient.proof : FormalFibreQuotient.Statement := by
  intro B A _ _ f hf hB m P _
  obtain ⟨φ, hφ, hcomm, hker⟩ := exists_adicCompletion_surjection_of_surjective f hf hB m
  refine ⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩
  · change (P.comap φ).comap _ = _
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  · exact primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloGeneralEquation
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.DetEqZeroOfMulVecEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

noncomputable section

def analyticAtSubring {σ : Type} [Fintype σ] (p : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g p}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem mem_analyticAtSubring {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p :=
  Iff.rfl

def analyticAtComp {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    analyticAtSubring (L x) →+* analyticAtSubring x where
  toFun g := ⟨fun z => (g : (τ → ℂ) → ℂ) (L z), AnalyticAt.comp g.2 (L.analyticAt x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def analyticAtEval {σ : Type} [Fintype σ] (p y : σ → ℂ) : analyticAtSubring p →+* ℂ :=
  (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) y).comp (analyticAtSubring p).subtype

@[simp] theorem analyticAtEval_apply {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y :=
  rfl

def analyticAtGerm {σ : Type} [Fintype σ] (p : σ → ℂ) : analyticAtSubring p →+* holGerms p :=
  ((Germ.coeRingHom (𝓝 p)).comp (analyticAtSubring p).subtype).codRestrict (holGerms p)
    fun g => ⟨g, g.2, rfl⟩

theorem analyticAtGerm_eq_iff {σ : Type} [Fintype σ] {p : σ → ℂ} (a b : analyticAtSubring p) :
    analyticAtGerm p a = analyticAtGerm p b ↔ (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 p] b := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem analyticAtGerm_surjective {σ : Type} [Fintype σ] (p : σ → ℂ) :
    Function.Surjective (analyticAtGerm p) := by
  rintro ⟨φ, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem det_eq_zero_of_mulVec_eq_zero {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

theorem FiniteModuloGeneralEquation.proof : FiniteModuloGeneralEquation.Statement := by
  intro σ τ _ _ _ x k f L c hf ⟨n, e, he, hfin⟩ ⟨r, h, h', hh, hh', hpow⟩
  classical
  have hproj : ∀ c', AnalyticAt ℂ (fun y : τ → ℂ => y c') (L x) := fun c' =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c').analyticAt _

  let fs : Fin k → analyticAtSubring x := fun i => ⟨f i, hf i⟩
  let es : Fin n → analyticAtSubring x := fun m => ⟨e m, he m⟩
  let hs : Fin k → analyticAtSubring x := fun i => ⟨h i, hh i⟩
  let hs' : τ → analyticAtSubring x := fun c' => ⟨h' c', hh' c'⟩
  let T : analyticAtSubring (L x) := ⟨fun y => (y c - L x c) ^ r, mem_analyticAtSubring.2 (((hproj c).sub analyticAt_const).pow r)⟩
  let D : τ → analyticAtSubring (L x) := fun c' =>
    ⟨fun y => zeroCoordinate c y c' - zeroCoordinate c (L x) c', mem_analyticAtSubring.2 (by
      simp only [zeroCoordinate_apply]
      split_ifs
      · exact analyticAt_const
      · exact (hproj c').sub analyticAt_const)⟩

  choose b kk hb hkk hbk using fun (i : Fin n) (c' : τ) => hfin _ ((hh' c').mul (he i))
  obtain ⟨b1, k1, hb1, hk1, h1eq⟩ := hfin (fun _ => 1) analyticAt_const
  let bs : Fin n → τ → Fin n → analyticAtSubring (L x) := fun i c' j => ⟨b i c' j, hb i c' j⟩
  let b1s : Fin n → analyticAtSubring (L x) := fun m => ⟨b1 m, hb1 m⟩
  let M : Matrix (Fin n) (Fin n) (analyticAtSubring (L x)) :=
    Matrix.of fun i j => (if i = j then T else 0) - ∑ c', bs i c' j * D c'
  refine ⟨r * n, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ), ?_⟩

  let J : Ideal (holGerms x) := Ideal.span (Set.range fun i => analyticAtGerm x (fs i))
  let ψ : analyticAtSubring x →+* holGerms x ⧸ J := (Ideal.Quotient.mk J).comp (analyticAtGerm x)
  let ψ' : analyticAtSubring (L x) →+* holGerms x ⧸ J := ψ.comp (analyticAtComp x L)
  have hψf : ∀ i, ψ (fs i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  have hψeq : ∀ a b : analyticAtSubring x, (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 x] b → ψ a = ψ b := fun a b hab => by
    simp only [ψ, RingHom.comp_apply, (analyticAtGerm_eq_iff a b).2 hab]
  have R1 : ψ' T = ∑ c', ψ (hs' c') * ψ' (D c') := by
    have := hψeq (analyticAtComp x L T) (∑ i, hs i * fs i + ∑ c', hs' c' * analyticAtComp x L (D c')) (by
      filter_upwards [hpow] with z hz
      simpa [analyticAtComp, T, D, hs, hs', fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R2 : ∀ i c', ψ (hs' c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ (es j) := fun i c' => by
    have := hψeq (hs' c' * es i) (∑ j, analyticAtComp x L (bs i c' j) * es j +
      ∑ a, (⟨kk i c' a, hkk i c' a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [hbk i c'] with z hz
      simpa [analyticAtComp, bs, es, hs', fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this
  have R3 : ∑ m, ψ' (b1s m) * ψ (es m) = 1 := by
    have := hψeq 1 (∑ m, analyticAtComp x L (b1s m) * es m +
      ∑ a, (⟨k1 a, hk1 a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [h1eq] with z hz
      simpa [analyticAtComp, b1s, es, fs] using hz)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [ψ', map_add (f := _), map_sum, map_mul, hψf] using this.symm

  have hMe : (ψ'.mapMatrix M) *ᵥ (fun j => ψ (es j)) = 0 := by
    funext i
    have hdiag : ∑ j, ψ' (if i = j then T else 0) * ψ (es j) = ψ' T * ψ (es i) := by
      simp [apply_ite ψ']
    have key : ∀ c', ψ (hs' c') * ψ' (D c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ' (D c') * ψ (es j) := by
      intro c'
      rw [mul_right_comm, R2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub,
      map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply, hdiag, R1, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun c' _ => key c', Finset.sum_comm, sub_eq_zero]
  have hdet : ψ' M.det = 0 := by
    rw [RingHom.map_det]
    exact det_eq_zero_of_mulVec_eq_zero _ _ (fun m => ψ' (b1s m)) hMe R3

  have hmem : analyticAtGerm x (analyticAtComp x L M.det) ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose q hq using fun i => analyticAtGerm_surjective x (a i)
  refine ⟨fun i => q i, (M.det).2, fun i => (q i).2, ?_, ?_⟩
  · have hgerm : analyticAtGerm x (∑ i, q i * fs i) = analyticAtGerm x (analyticAtComp x L M.det) := by
      rw [← ha]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_mul, hq]
    filter_upwards [(analyticAtGerm_eq_iff _ _).1 hgerm] with z hz
    simpa [analyticAtComp, fs] using hz.symm

  · have hev : ∀ s : ℂ, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = s ^ (r * n) := by
      intro s
      rw [← analyticAtEval_apply, RingHom.map_det]
      have hdg : (analyticAtEval (L x) (L x + Pi.single c s)).mapMatrix M = Matrix.diagonal fun _ => s ^ r := by
        ext i j
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub, map_sum, map_mul,
          apply_ite (analyticAtEval (L x) (L x + Pi.single c s)), map_zero, analyticAtEval_apply, Matrix.diagonal_apply]
        have hD : ∀ c', ((D c' : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = 0 := by
          intro c'
          simp only [D, zeroCoordinate_apply]
          split_ifs with hc
          · simp
          · simp [hc]
        simp [hD, T]
      rw [hdg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [show (fun s : ℂ => ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s)) =
      fun s : ℂ => s ^ (r * n) from funext hev]
    exact ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow _).analyticOrderAt_eq_natCast.2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun s => by simp⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalZerosNowhereDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

theorem isAnalyticNear_zeroSetIn {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn_isAnalyticNear (σ := σ) I w

theorem analyticOnNhd_of_differentiableOn_scalar_fin {d : ℕ} {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : AnalyticOnNhd ℂ F U := by
  refine analyticOnNhd_of_continuousOn_of_separately hU hF.continuousOn (fun z hz i => ?_)
  have h1 : DifferentiableAt ℂ F (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hF.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem germIrreducibleAt_zeroSetIn_of_integrallyClosed (hic : NormalGermIntegrallyClosed.Statement)
    {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (hI : I.IsPrime)
    (hn : IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I)) (hw : w ∈ zeroSetIn I) :
    GermIrreducibleAt (zeroSetIn I) w := by
  refine ⟨hw, fun f g hf hg hfg => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfne, hgne⟩ := hcon
  set X := zeroSetIn I with hX
  set N : Set (σ → ℂ) :=
    ({z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}) ∩ interior {z | z ∈ X → f z * g z = 0} with hNdef
  have hNo : IsOpen N := ((isOpen_analyticAt ℂ f).inter (isOpen_analyticAt ℂ g)).inter isOpen_interior
  have hwN : w ∈ N := ⟨⟨hf, hg⟩, mem_interior_iff_mem_nhds.mpr hfg⟩
  have hfd : DifferentiableOn ℂ f N := fun z hz => hz.1.1.differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g N := fun z hz => hz.1.2.differentiableAt.differentiableWithinAt
  have hfgN : ∀ z ∈ X ∩ N, f z * g z = 0 := fun z hz => interior_subset hz.2.2 hz.1
  have hGne : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → (f + g) z = 0 := by
    intro hev
    apply hfne
    filter_upwards [hev, hfg] with z h1 h2 hz
    have hs : f z + g z = 0 := h1 hz
    have hp : f z * g z = 0 := h2 hz
    have hff : f z * f z = 0 := by linear_combination f z * hs - hp
    exact mul_self_eq_zero.mp hff
  have ha : ∀ j, DifferentiableOn ℂ ((![0, -1] : Fin 2 → (σ → ℂ) → ℂ) j) N := by
    intro j
    fin_cases j
    · exact differentiableOn_const (0 : ℂ)
    · exact differentiableOn_const (-1 : ℂ)
  obtain ⟨V, hV, hwV, H, hH, hfH⟩ := hic σ I w N f (f + g) 2 ![0, -1] hI hn hw hNo hwN hfd (hfd.add hgd)
    ha hGne (by
      intro z hz
      have hp := hfgN z hz.1
      simp [Fin.sum_univ_two]
      linear_combination -hp)
  have hHc : ContinuousAt H w := (hH.differentiableAt (hV.mem_nhds hwV)).continuousAt
  have hev : ∀ᶠ z in 𝓝 w, z ∈ V ∧ (z ∈ X → f z * g z = 0) := (show ∀ᶠ z in 𝓝 w, z ∈ V from hV.mem_nhds hwV).and hfg
  rw [Filter.not_eventually] at hfne hgne
  have h1 : H w = 1 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hfne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hg0 : g z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_left hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hg0, add_zero] at hfz
    exact hzH.2 (mul_left_cancel₀ hz.2 (hfz.symm.trans (mul_one _).symm))
  have h0 : H w = 0 := by
    by_contra hne
    obtain ⟨z, hz, hzH⟩ := (hgne.and_eventually (hev.and (hHc.eventually_ne hne))).exists
    push Not at hz
    have hf0 : f z = 0 := (mul_eq_zero.mp (hzH.1.2 hz.1)).resolve_right hz.2
    have hfz := hfH z ⟨hz.1, hzH.1.1⟩
    simp only [Pi.add_apply, hf0, zero_add] at hfz
    exact hzH.2 ((mul_eq_zero.mp hfz.symm).resolve_left hz.2)
  exact one_ne_zero (h1.symm.trans h0)

theorem NormalZerosNowhereDense.proof (hic : NormalGermIntegrallyClosed.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement) (hdense : RegularLocusDense.Statement) :
    NormalZerosNowhereDense.Statement := by
  intro σ _ I w N G hI hn hw hN hwN hG hne
  have han := isAnalyticNear_zeroSetIn I w
  have hirr := germIrreducibleAt_zeroSetIn_of_integrallyClosed hic I w hI hn hw
  set X := zeroSetIn I with hX
  obtain ⟨N₀, hN₀, hwN₀, hd⟩ := hdense σ X w han
  obtain ⟨B, hB, hwB, hBU, hpc⟩ :=
    hconn σ X w han hirr (N ∩ N₀) (Filter.inter_mem (hN.mem_nhds hwN) (hN₀.mem_nhds hwN₀))
  have hBN : B ⊆ N := hBU.trans Set.inter_subset_left
  have hdB : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hd B hB (hBU.trans Set.inter_subset_right)
  refine ⟨B, hB, hwB, hBN, ?_⟩
  intro z hz V hV
  by_contra hall
  push Not at hall
  set R := regLocus (X ∩ B) with hR
  set T : Set (σ → ℂ) := {y | y ∈ X → G y = 0} with hT

  have hloc : ∀ x ∈ R, ∃ M : Set (σ → ℂ), IsOpen M ∧ x ∈ M ∧ ((∃ p ∈ X ∩ M, T ∈ 𝓝 p) → M ⊆ T) := by
    intro x hx
    have hx' : IsRegularPointOf (X ∩ B) x := hx
    obtain ⟨hxXB, d, A, O, W, g, hO, hW, hxW, hg, hAg, hYW⟩ := hx'
    obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := by rw [← hYW]; exact ⟨hxXB, hxW⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO y₀ hy₀O
    have hgO : ∀ y ∈ O, g y ∈ X ∩ B := by
      intro y hy
      have hy' : g y ∈ (X ∩ B) ∩ W := by rw [hYW]; exact Set.mem_image_of_mem g hy
      exact hy'.1
    have hxA : A x ∈ Metric.ball y₀ r := by
      rw [← hgy₀, hAg y₀ hy₀O]
      exact Metric.mem_ball_self hr
    refine ⟨W ∩ B ∩ A ⁻¹' Metric.ball y₀ r,
      (hW.inter hB).inter (Metric.isOpen_ball.preimage A.continuous), ⟨⟨hxW, hxXB.2⟩, hxA⟩, ?_⟩
    have hcov : ∀ p ∈ X ∩ (W ∩ B ∩ A ⁻¹' Metric.ball y₀ r), ∃ y ∈ Metric.ball y₀ r, g y = p := by
      rintro p ⟨hpX, ⟨hpW, hpB⟩, hpA⟩
      obtain ⟨y, hyO, rfl⟩ : p ∈ g '' O := by rw [← hYW]; exact ⟨⟨hpX, hpB⟩, hpW⟩
      refine ⟨y, ?_, rfl⟩
      have hpA' : A (g y) ∈ Metric.ball y₀ r := hpA
      rwa [hAg y hyO] at hpA'
    have hF : AnalyticOnNhd ℂ (fun y => G (g y)) (Metric.ball y₀ r) := by
      refine analyticOnNhd_of_differentiableOn_scalar_fin Metric.isOpen_ball (fun y hy => ?_)
      have hyO := hrO hy
      exact ((hG.differentiableAt (hN.mem_nhds (hBN (hgO y hyO).2))).comp y
        (hg y hyO).differentiableAt).differentiableWithinAt
    rintro ⟨p, hpXM, hpT⟩
    obtain ⟨y₁, hy₁, rfl⟩ := hcov p hpXM
    have hev : (fun y => G (g y)) =ᶠ[𝓝 y₁] 0 := by
      filter_upwards [(hg y₁ (hrO hy₁)).continuousAt.preimage_mem_nhds hpT,
        Metric.isOpen_ball.mem_nhds hy₁] with y hyT hyb
      exact hyT (hgO y (hrO hyb)).1
    have hzero := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball y₀ r).isPreconnected hy₁ hev
    intro q hq hqX
    obtain ⟨y, hy, rfl⟩ := hcov q ⟨hqX, hq⟩
    exact hzero hy
  choose! M hMo hxM hMT using hloc

  have hallR : ∀ x ∈ R, T ∈ 𝓝 x := by
    obtain ⟨x₀, hx₀V, hx₀R⟩ := mem_closure_iff_nhds.mp (hdB hz) (interior V) (interior_mem_nhds.mpr hV)
    have hx₀T : T ∈ 𝓝 x₀ :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx₀V) (fun y hy hyX => hall y ⟨hyX, interior_subset hy⟩)
    by_contra hbad
    push Not at hbad
    obtain ⟨x₁, hx₁R, hx₁T⟩ := hbad
    have hu : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hv : IsOpen (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := isOpen_biUnion fun x hx => hMo x hx.1
    have hcover : R ⊆ (⋃ x ∈ {x | x ∈ R ∧ T ∈ 𝓝 x}, M x) ∪ (⋃ x ∈ {x | x ∈ R ∧ T ∉ 𝓝 x}, M x) := by
      intro x hx
      by_cases h : T ∈ 𝓝 x
      · exact Or.inl (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
      · exact Or.inr (Set.mem_biUnion (x := x) ⟨hx, h⟩ (hxM x hx))
    obtain ⟨q, hqR, hqu, hqv⟩ := hpc _ _ hu hv hcover
      ⟨x₀, hx₀R, Set.mem_biUnion (x := x₀) ⟨hx₀R, hx₀T⟩ (hxM x₀ hx₀R)⟩
      ⟨x₁, hx₁R, Set.mem_biUnion (x := x₁) ⟨hx₁R, hx₁T⟩ (hxM x₁ hx₁R)⟩
    obtain ⟨a, ⟨haR, haT⟩, hqa⟩ := Set.mem_iUnion₂.mp hqu
    obtain ⟨b, ⟨hbR, hbT⟩, hqb⟩ := Set.mem_iUnion₂.mp hqv
    have hqX : q ∈ X := (regLocus_subset _ hqR).1
    have hMa : M a ⊆ T := hMT a haR ⟨a, ⟨(regLocus_subset _ haR).1, hxM a haR⟩, haT⟩
    have hqT : T ∈ 𝓝 q := Filter.mem_of_superset ((hMo a haR).mem_nhds hqa) hMa
    have hMb : M b ⊆ T := hMT b hbR ⟨q, ⟨hqX, hqb⟩, hqT⟩
    exact hbT (Filter.mem_of_superset ((hMo b hbR).mem_nhds (hxM b hbR)) hMb)

  have hzeroB : ∀ y ∈ X ∩ B, G y = 0 := by
    intro y hy
    by_contra hGy
    have hc : ContinuousAt G y := (hG.differentiableAt (hN.mem_nhds (hBN hy.2))).continuousAt
    obtain ⟨x, hxG, hxR⟩ := mem_closure_iff_nhds.mp (hdB hy) _ (hc.eventually_ne hGy)
    exact hxG (mem_of_mem_nhds (hallR x hxR) (regLocus_subset _ hxR).1)
  exact hne (Filter.mem_of_superset (hB.mem_nhds hwB) fun y hyB hyX => hzeroB y ⟨hyX, hyB⟩)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
