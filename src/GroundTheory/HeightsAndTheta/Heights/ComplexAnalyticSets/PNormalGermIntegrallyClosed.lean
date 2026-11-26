module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalGermIntegrallyClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

namespace NormalGermIntegrallyClosed

theorem analyticAt_of_differentiableOn {σ : Type} [Fintype σ] {N : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ}
    (hN : IsOpen N) (hf : DifferentiableOn ℂ f N) {z : σ → ℂ} (hz : z ∈ N) : AnalyticAt ℂ f z := by
  let L : (Fin (Fintype.card σ) → ℂ) ≃L[ℂ] (σ → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
  have hO : IsOpen (L ⁻¹' N) := hN.preimage L.continuous
  have hg : DifferentiableOn ℂ (f ∘ L) (L ⁻¹' N) :=
    hf.comp L.differentiable.differentiableOn fun x hx => hx
  have hA : AnalyticOnNhd ℂ (f ∘ L) (L ⁻¹' N) := by
    refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun x hx i => ?_
    have h1 : DifferentiableAt ℂ (f ∘ L) (Function.update x i (x i)) := by
      rw [Function.update_eq_self]
      exact hg.differentiableAt (hO.mem_nhds hx)
    exact h1.comp (x i) (hasFDerivAt_update x (x i)).differentiableAt
  have hz' : L.symm z ∈ L ⁻¹' N := by simpa using hz
  have h2 := (hA _ hz').comp ((L.symm : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)).analyticAt z)
  simpa [Function.comp_def] using h2

def anFun {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := analyticAt_const
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := analyticAt_const
  neg_mem' := fun hf => hf.neg

def toGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : anFun w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (anFun w).subtype).codRestrict (holGerms w) fun u => ⟨u.1, u.2, rfl⟩

theorem toGerm_surjective {σ : Type} [Fintype σ] (w : σ → ℂ) : Function.Surjective (toGerm w) := by
  rintro ⟨φ, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

theorem toGerm_eq_iff {σ : Type} [Fintype σ] {w : σ → ℂ} {u v : anFun w} :
    toGerm w u = toGerm w v ↔ (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem vanish_of_mem_map {σ : Type} [Fintype σ] {I : Ideal (MvPolynomial σ ℂ)} {w : σ → ℂ} {u : anFun w}
    (hu : toGerm w u ∈ I.map (polyGerm w)) :
    ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 := by
  have key : ∀ x, x ∈ Submodule.span (holGerms w) (polyGerm w '' (I : Set (MvPolynomial σ ℂ))) →
      ∃ v : anFun w, toGerm w v = x ∧ ∀ᶠ z in 𝓝[zeroSetIn I] w, (v : (σ → ℂ) → ℂ) z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩, rfl,
        eventually_nhdsWithin_of_forall fun z hz => hz q hq⟩
    | zero => exact ⟨0, map_zero _, Eventually.of_forall fun z => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, rfl, hu⟩ := hx
      obtain ⟨v, rfl, hv⟩ := hy
      exact ⟨u + v, map_add _ _ _, by filter_upwards [hu, hv] with z h1 h2; simp [h1, h2]⟩
    | smul c x _ hx =>
      obtain ⟨v, rfl, hv⟩ := hx
      obtain ⟨b, rfl⟩ := toGerm_surjective w c
      exact ⟨b * v, by rw [map_mul, smul_eq_mul], by filter_upwards [hv] with z h; simp [h]⟩
  obtain ⟨v, hv, hv0⟩ := key _ hu
  have he : (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v := toGerm_eq_iff.1 hv.symm
  filter_upwards [nhdsWithin_le_nhds he, hv0] with z h1 h2
  rw [h1, h2]

theorem exists_eq_mul_of_integral_relation {S : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    {d : ℕ} (f g : S) (a : Fin d → S) (hg : g ≠ 0)
    (hrel : f ^ d + ∑ j, a j * f ^ (j : ℕ) * g ^ (d - (j : ℕ)) = 0) : ∃ y, f = g * y := by
  let K := FractionRing S
  have hinj : Function.Injective (algebraMap S K) := IsFractionRing.injective S K
  have hrelK : algebraMap S K f ^ d + ∑ j, algebraMap S K (a j) * algebraMap S K f ^ (j : ℕ) *
      algebraMap S K g ^ (d - (j : ℕ)) = 0 := by
    have h2 := congrArg (algebraMap S K) hrel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_mul, map_pow, map_zero] at h2
    exact h2
  have hg0 : algebraMap S K g ≠ 0 := fun h0 => hg (hinj (by rw [h0, map_zero]))
  generalize hfK : algebraMap S K f = fK at hrelK
  generalize hgK : algebraMap S K g = gK at hrelK hg0
  have hint : IsIntegral S (fK / gK) := by
    refine ⟨Polynomial.X ^ d + ∑ j : Fin d, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
    have hterm : ∀ j : Fin d, algebraMap S K (a j) * (fK / gK) ^ (j : ℕ) =
        algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) / gK ^ d := by
      intro j
      rw [eq_div_iff (pow_ne_zero _ hg0), div_pow,
        show gK ^ d = gK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) by rw [← pow_add, Nat.add_sub_cancel' j.2.le]]
      have hj : gK ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hg0
      rw [show algebraMap S K (a j) * (fK ^ (j : ℕ) / gK ^ (j : ℕ)) * (gK ^ (j : ℕ) * gK ^ (d - (j : ℕ))) =
          algebraMap S K (a j) * fK ^ (j : ℕ) * gK ^ (d - (j : ℕ)) * (gK ^ (j : ℕ) / gK ^ (j : ℕ)) by ring,
        div_self hj, mul_one]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [Finset.sum_congr rfl fun j _ => hterm j, div_pow, ← Finset.sum_div, ← add_div, hrelK, zero_div]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hfK, hgK, mul_div_assoc', eq_div_iff hg0, mul_comm]

theorem proof (hRueckert : RueckertNullstellensatz.Statement)
    (hZariski : ZariskiAnalyticNormality.Statement) : NormalGermIntegrallyClosed.Statement := by
  intro σ _ I w N F G d a hI hIc hw hN hwN hF hG ha hGnz hrel
  have hFa : AnalyticAt ℂ F w := analyticAt_of_differentiableOn hN hF hwN
  have hGa : AnalyticAt ℂ G w := analyticAt_of_differentiableOn hN hG hwN
  have haa : ∀ j, AnalyticAt ℂ (a j) w := fun j => analyticAt_of_differentiableOn hN (ha j) hwN

  obtain ⟨k, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hpI : ∀ i, p i ∈ I := fun i => hp ▸ Submodule.subset_span ⟨i, rfl⟩
  have hZp : ∀ z, (∀ i, eval z (p i) = 0) → z ∈ zeroSetIn I := by
    intro z hz q hq
    have hle : I ≤ RingHom.ker (eval z) := by
      rw [← hp]
      exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
    exact RingHom.mem_ker.1 (hle hq)

  obtain ⟨hJ, hJc⟩ := hZariski σ I w hI hIc hw
  let J := I.map (polyGerm w)
  have : J.IsPrime := hJ
  let S := holGerms w ⧸ J
  have : IsIntegrallyClosed S := hJc
  let π : anFun w →+* S := (Ideal.Quotient.mk J).comp (toGerm w)
  have hπ0 : ∀ u : anFun w, π u = 0 → ∀ᶠ z in 𝓝[zeroSetIn I] w, (u : (σ → ℂ) → ℂ) z = 0 :=
    fun u hu => vanish_of_mem_map (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hπpoly : ∀ q ∈ I, π ⟨fun z => eval z q, analyticAt_eval_polynomial w q⟩ = 0 := fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hq)
  have hπeq : ∀ u v : anFun w, (u : (σ → ℂ) → ℂ) =ᶠ[𝓝 w] v → π u = π v := fun u v h => by
    simp only [π, RingHom.comp_apply, toGerm_eq_iff.2 h]

  let FA : anFun w := ⟨F, hFa⟩
  let GA : anFun w := ⟨G, hGa⟩
  let aA : Fin d → anFun w := fun j => ⟨a j, haa j⟩
  let PA : anFun w := FA ^ d + ∑ j, aA j * FA ^ (j : ℕ) * GA ^ (d - (j : ℕ))
  have hPA : ∀ z, (PA : (σ → ℂ) → ℂ) z =
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) := by
    intro z
    simp [PA, FA, GA, aA, Finset.sum_apply]

  have hGS : π GA ≠ 0 := by
    intro h
    exact hGnz (eventually_nhdsWithin_iff.1 (hπ0 GA h))

  have hvan : ∀ᶠ z in 𝓝 w, (∀ i, eval z (p i) = 0) → (PA : (σ → ℂ) → ℂ) z * G z = 0 := by
    filter_upwards [hN.mem_nhds hwN] with z hzN hz
    by_cases hG0 : G z = 0
    · rw [hG0, mul_zero]
    · rw [hPA, hrel z ⟨⟨hZp z hz, hzN⟩, hG0⟩, zero_mul]
  obtain ⟨m, h, hm, hh, hgm⟩ := hRueckert σ w k (fun i z => eval z (p i))
    (fun z => (PA : (σ → ℂ) → ℂ) z * G z) (fun i => analyticAt_eval_polynomial w (p i))
    (PA.2.mul hGa) hvan
  let hA : Fin k → anFun w := fun i => ⟨h i, hh i⟩
  let pA : Fin k → anFun w := fun i => ⟨fun z => eval z (p i), analyticAt_eval_polynomial w (p i)⟩
  have hprod : π ((PA * GA) ^ m) = π (∑ i, hA i * pA i) := by
    apply hπeq
    filter_upwards [hgm] with z hz
    simpa [hA, pA, GA, Finset.sum_apply, mul_pow] using hz
  have hPS : π PA = 0 := by
    have h1 : (π PA * π GA) ^ m = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, ← map_pow, hprod, map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_mul, hπpoly _ (hpI i), mul_zero]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 hm)).1 h1)).resolve_right hGS

  have : IsDomain S := Ideal.Quotient.isDomain J
  obtain ⟨y, hy⟩ := exists_eq_mul_of_integral_relation (π FA) (π GA) (fun j => π (aA j)) hGS (by
    rw [← hPS]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PA, map_add (f := _), map_sum, map_mul, map_pow])
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨HA, rfl⟩ := toGerm_surjective w φ
  have hdiff : π (FA - GA * HA) = 0 := by
    rw [map_sub, map_mul, hy]
    exact sub_self _
  have hv := eventually_nhdsWithin_iff.1 (hπ0 _ hdiff)
  obtain ⟨V, hV, hVo, hwV⟩ := eventually_nhds_iff.1 (hv.and HA.2.eventually_analyticAt)
  refine ⟨V, hVo, hwV, HA, fun z hz => (hV z hz).2.differentiableAt.differentiableWithinAt, ?_⟩
  rintro z ⟨hzZ, hzV⟩
  have h3 := (hV z hzV).1 hzZ
  change F z - G z * (HA : (σ → ℂ) → ℂ) z = 0 at h3
  exact sub_eq_zero.1 h3

end NormalGermIntegrallyClosed

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermMinimalPolynomialDivides
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace GermMinimalPolynomialDivides

def germsAlong {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : Subring (Germ (𝓝[X] x) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f x ∧ (f : Germ (𝓝[X] x) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

def analyticAtRing {ι : Type} [Fintype ι] (w : ι → ℂ) : Subring ((ι → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f w}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (1 : ℂ)) w)
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (0 : ℂ)) w)
  neg_mem' := fun hf => hf.neg

def germOf {ι : Type} [Fintype ι] (w : ι → ℂ) : analyticAtRing w →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (analyticAtRing w).subtype).codRestrict (holGerms w)
    fun f => ⟨f.1, f.2, rfl⟩

theorem germOf_surjective {ι : Type} [Fintype ι] (w : ι → ℂ) : Function.Surjective (germOf w) := by
  intro φ
  obtain ⟨f, hf, hφ⟩ := φ.2
  exact ⟨⟨f, hf⟩, Subtype.ext hφ⟩

def germRep {ι : Type} [Fintype ι] (w : ι → ℂ) : holGerms w → analyticAtRing w :=
  Function.surjInv (germOf_surjective w)

theorem germOf_germRep {ι : Type} [Fintype ι] (w : ι → ℂ) (φ : holGerms w) : germOf w (germRep w φ) = φ :=
  Function.surjInv_eq (germOf_surjective w) φ

theorem germOf_eq_zero {ι : Type} [Fintype ι] (w : ι → ℂ) (f : analyticAtRing w) :
    germOf w f = 0 ↔ ∀ᶠ y in 𝓝 w, f.1 y = 0 := by
  rw [← Subtype.coe_inj]
  exact Germ.coe_eq

def alongOf {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) : analyticAtRing x →+* germsAlong X x :=
  ((Germ.coeRingHom (𝓝[X] x)).comp (analyticAtRing x).subtype).codRestrict (germsAlong X x)
    fun f => ⟨f.1, f.2, rfl⟩

def germCompHom {α β : Type} {l : Filter β} {l' : Filter α} (g : α → β) (hg : Tendsto g l' l) :
    Germ l ℂ →+* Germ l' ℂ where
  toFun φ := φ.compTendsto g hg
  map_one' := rfl
  map_mul' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl
  map_zero' := rfl
  map_add' φ ψ := Germ.inductionOn₂ φ ψ fun _ _ => rfl

theorem tendsto_nhdsWithin_linear {σ : Type} [Fintype σ] {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (X : Set (σ → ℂ)) (x : σ → ℂ) : Tendsto A (𝓝[X] x) (𝓝 (A x)) :=
  (A.continuous.tendsto x).mono_left nhdsWithin_le_nhds

def alongPull {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    holGerms (A x) →+* germsAlong X x :=
  ((germCompHom A (tendsto_nhdsWithin_linear A X x)).comp (holGerms (A x)).subtype).codRestrict _ fun φ => by
    obtain ⟨f, hf, hφ⟩ := φ.2
    refine ⟨f ∘ A, hf.comp (A.analyticAt x), ?_⟩
    change _ = (φ.1 : Germ (𝓝 (A x)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X x)
    rw [← hφ]
    rfl

def preLinear {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) :
    analyticAtRing (A x) →+* ((σ → ℂ) → ℂ) :=
  (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)).comp (analyticAtRing (A x)).subtype

theorem eventually_of_germ_eq {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z :=
  eventually_nhdsWithin_iff.1 (Germ.coe_eq.1 h)

theorem coe_eval₂_map {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by
  change (germsAlong X x).subtype _ = Germ.coeRingHom _ _
  rw [eval₂_map, hom_eval₂, hom_eval₂]
  rfl

theorem eval₂_monic_apply {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (Polynomial.X ^ M + ∑ j, C (b j) * Polynomial.X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by
  simp [eval₂_finsetSum, Finset.sum_apply, preLinear]

theorem proof (hF : FiniteFibreGermIntegral.Statement) (hH : HolGermsIntegrallyClosed.Statement) :
    GermMinimalPolynomialDivides.Statement := by
  intro σ _ X w d A hXan hirr hiso hinj g hg
  classical
  obtain ⟨hdom, hic⟩ := hH d (A w)

  have : (𝓝[X] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hirr.1)
  have germ_zero : ∀ f : (σ → ℂ) → ℂ, (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) →
      (f : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) :=
    fun f h => Germ.coe_eq.2 (eventually_nhdsWithin_iff.2 h)
  have : NoZeroDivisors (germsAlong X w) := by
    refine ⟨fun {a b} hab => ?_⟩
    obtain ⟨f, hf, hfa⟩ := a.2
    obtain ⟨g, hg, hgb⟩ := b.2
    have h0 : ((f * g : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      rw [Germ.coe_mul, hfa, hgb]
      exact congrArg Subtype.val hab
    rcases hirr.2 f g hf hg ((eventually_of_germ_eq h0).mono fun z hz hzX => by simpa using hz hzX) with h | h
    · exact Or.inl (Subtype.ext (hfa ▸ germ_zero f h))
    · exact Or.inr (Subtype.ext (hgb ▸ germ_zero g h))
  have : IsDomain (germsAlong X w) := NoZeroDivisors.to_isDomain _

  let _ : Algebra (holGerms (A w)) (germsAlong X w) := (alongPull X w A).toAlgebra
  have hα : Function.Injective (algebraMap (holGerms (A w)) (germsAlong X w)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ hφ
    obtain ⟨h, hh, hφh⟩ := φ.2
    have h1 : ((h ∘ A : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) := by
      have h2 := congrArg Subtype.val hφ
      change (φ.1 : Germ (𝓝 (A w)) ℂ).compTendsto A (tendsto_nhdsWithin_linear A X w) =
        (0 : Germ (𝓝[X] w) ℂ) at h2
      rw [← hφh] at h2
      exact h2
    have h3 := hinj h hh ((eventually_of_germ_eq h1).mono fun z hz hzX => hz hzX)
    apply Subtype.ext
    rw [← hφh]
    exact Germ.coe_eq.2 h3
  have : FaithfulSMul (holGerms (A w)) (germsAlong X w) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hα

  set s : germsAlong X w := alongOf X w ⟨g, hg⟩ with hs
  have aeval_zero : ∀ P : (analyticAtRing (A w))[X],
      (∀ᶠ z in 𝓝 w, z ∈ X → eval₂ (preLinear w A) g P z = 0) → aeval s (P.map (germOf (A w))) = 0 := by
    intro P hP
    rw [aeval_def]
    apply Subtype.ext
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ)
    rw [coe_eval₂_map]
    exact germ_zero _ hP

  have hint : IsIntegral (holGerms (A w)) s := by
    obtain ⟨M, b, hb, hev⟩ := hF σ X w d A hXan hiso g hg
    let bt : Fin M → analyticAtRing (A w) := fun j => ⟨b j, hb j⟩
    refine ⟨(Polynomial.X ^ M + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)).map (germOf (A w)),
      (monic_X_pow_add (degree_sum_fin_lt _)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_zero _ (hev.mono fun z hz hzX => by rw [eval₂_monic_apply]; exact hz hzX)

  set m := minpoly (holGerms (A w)) s with hm
  have hmon : m.Monic := minpoly.monic hint
  let bt : Fin m.natDegree → analyticAtRing (A w) := fun j => germRep (A w) (m.coeff j)
  let P : (analyticAtRing (A w))[X] := Polynomial.X ^ m.natDegree + ∑ j, C (bt j) * Polynomial.X ^ (j : ℕ)
  have hPm : P.map (germOf (A w)) = m := by
    have h1 := hmon.as_sum
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (m.coeff i) * Polynomial.X ^ i)] at h1
    conv_rhs => rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, bt, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C, germOf_germRep]
  have hPz : ∀ z, eval₂ (preLinear w A) g P z = g z ^ m.natDegree + ∑ j, (bt j).1 (A z) * g z ^ (j : ℕ) :=
    fun z => eval₂_monic_apply w A g bt z
  refine ⟨m.natDegree, fun j => (bt j).1, fun j => (bt j).2, ?_, ?_⟩
  ·
    have h0 : aeval s m = 0 := minpoly.aeval _ _
    rw [← hPm, aeval_def] at h0
    have h1 := congrArg Subtype.val h0
    change ((eval₂ (alongPull X w A) (alongOf X w ⟨g, hg⟩) (P.map (germOf (A w))) : germsAlong X w) :
      Germ (𝓝[X] w) ℂ) = ((0 : (σ → ℂ) → ℂ) : Germ (𝓝[X] w) ℂ) at h1
    rw [coe_eval₂_map] at h1
    exact (eventually_of_germ_eq h1).mono fun z hz hzX => (hPz z).symm.trans (hz hzX)
  ·
    intro E hE hEz
    have hcoeffs : (↑E.coeffs : Set ((Fin d → ℂ) → ℂ)) ⊆ analyticAtRing (A w) := by
      intro c hc
      obtain ⟨k, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact hE k
    let Et := E.toSubring (analyticAtRing (A w)) hcoeffs
    have hEval : ∀ z, eval₂ (preLinear w A) g Et z = E.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (g z) := by
      intro z
      have hmap : Et.map (analyticAtRing (A w)).subtype = E := map_toSubring _ _ _
      have h1 : eval₂ (preLinear w A) g Et =
          eval₂ (RingHom.pi fun z => Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) g E := by
        rw [← hmap, eval₂_map]
        rfl
      rw [h1]
      exact hom_eval₂ E _ (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) z) g
    have hEt0 : aeval s (Et.map (germOf (A w))) = 0 :=
      aeval_zero Et (hEz.mono fun z hz hzX => (hEval z).trans (hz hzX))
    obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hEt0
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective _ (germOf_surjective (A w)) q
    have hDz : (Et - P * Q).map (germOf (A w)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hPm, hq, sub_self]
    have hDev : ∀ᶠ y in 𝓝 (A w), ∀ k ∈ (Et - P * Q).support, ((Et - P * Q).coeff k).1 y = 0 := by
      rw [eventually_all_finset]
      intro k _
      have : germOf (A w) ((Et - P * Q).coeff k) = 0 := by rw [← coeff_map, hDz, coeff_zero]
      exact (germOf_eq_zero _ _).1 this
    filter_upwards [hDev] with y hy
    let ev : analyticAtRing (A w) →+* ℂ :=
      (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticAtRing (A w)).subtype
    have hD0 : (Et - P * Q).map ev = 0 := by
      ext k
      rw [coeff_map, coeff_zero]
      by_cases hk : k ∈ (Et - P * Q).support
      · exact hy k hk
      · rw [notMem_support_iff.1 hk, map_zero]
    have hE' : Et.map ev = E.map (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y) := by
      rw [← map_toSubring E (analyticAtRing (A w)) hcoeffs, Polynomial.map_map]
    have hP' : P.map ev =
        Polynomial.X ^ m.natDegree + ∑ j, C ((bt j).1 y) * Polynomial.X ^ (j : ℕ) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [P, ev, Polynomial.map_sum]
    refine ⟨Q.map ev, ?_⟩
    rw [← hE', ← hP', ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    exact hD0

end GermMinimalPolynomialDivides

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAuslanderBuchsbaumProjDimUpper
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AuslanderBuchsbaumDepthBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

theorem exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) :
    ∃ s : R, s ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a * s = 0 := by
  have hmk : ∀ y : R, y • (1 : R ⧸ maximalIdeal R) = Ideal.Quotient.mk (maximalIdeal R) y := fun y ↦ by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have hns : ¬ Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    rw [IsSMulRegular.subsingleton_linearMap_iff]
    rintro ⟨r, hr, hreg⟩
    refine h r ?_ hreg
    have h1 := Module.mem_annihilator.mp hr (1 : R ⧸ maximalIdeal R)
    rwa [hmk, Ideal.Quotient.eq_zero_iff_mem] at h1
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨f, hf⟩ := exists_ne (0 : (R ⧸ maximalIdeal R) →ₗ[R] R)
  refine ⟨f 1, fun h0 ↦ hf (LinearMap.ext fun y ↦ ?_), fun a ha ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← hmk, map_smul, h0, smul_zero, LinearMap.zero_apply]
  · rw [← smul_eq_mul, ← map_smul, hmk, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

theorem hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular [IsLocalRing R] [IsNoetherianRing R]
    (h : ∀ y ∈ maximalIdeal R, ¬ IsSMulRegular R y) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (k : ℕ) (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) 0 := by
  obtain ⟨s, hs, hms⟩ := exists_ne_zero_mul_eq_zero_of_forall_not_isSMulRegular h
  have : Module.Free R M := GroundTheory.Arith.SchemeCoh.free_of_hasProjectiveDimensionLT_of_mul_eq_zero hs hms k M hM
  exact (projective_iff_hasProjectiveDimensionLE_zero _).mp (by
    rw [← IsProjective.iff_projective]; infer_instance)

theorem hasProjectiveDimensionLT_of_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) (k : ℕ) (M : Type u) [AddCommGroup M]
    [Module R M] [Module.Finite R M] (hxM : IsSMulRegular M x)
    (hM : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (k + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) := by
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM ⊢
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hfree : Module.Free (R ⧸ span {x}) (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
    have := Module.finitePresentation_of_finite R M
    have : Module.Free R M :=
      (Module.free_quotSMulTop_iff_free R M (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ hx) hxM).mp hfree
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    let f₁ : QuotSMulTop x K →ₗ[R] QuotSMulTop x (Fin n → R) := QuotSMulTop.map x K.subtype
    let f₂ : QuotSMulTop x (Fin n → R) →ₗ[R] QuotSMulTop x M := QuotSMulTop.map x π
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact f₁ f₂ := QuotSMulTop.map_exact x hex0 hπ
    have surj : Function.Surjective f₂ := QuotSMulTop.map_surjective x hπ
    have inj : Function.Injective f₁ := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearMap.mem_ker] at hy
      simp only [f₁, Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨b, -, hb⟩ := hy
      have hπb : π b = 0 := by
        apply hxM
        show x • π b = x • 0
        rw [← map_smul, hb, smul_zero]
        exact y.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨b, hπb⟩, Submodule.mem_top, Subtype.ext hb⟩
    let g₁ := f₁.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let g₂ := f₂.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := span {x}))
    let T := ModuleCat.shortComplexOfCompEqZero g₁ g₂
      (LinearMap.ext fun y ↦ ex.apply_apply_eq_zero y)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T ex inj surj
    have hproj2 : Projective T.X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK' : HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x K)) (k + 1) :=
      (hT.hasProjectiveDimensionLT_X₃_iff k hproj2).mp hM
    exact (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mpr (ih K hxK hK')

theorem length_le_of_isWeaklyRegular_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hxR : IsSMulRegular R x) [IsLocalRing (R ⧸ span {x})] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d + 1)
    (rs : List (R ⧸ span {x})) (hrs : ∀ r ∈ rs, r ∈ maximalIdeal (R ⧸ span {x}))
    (hreg : IsWeaklyRegular (R ⧸ span {x}) rs) : rs.length ≤ d := by
  let lift : R ⧸ span {x} → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ b, Ideal.Quotient.mk (span {x}) (lift b) = b :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  have hrs' : (rs.map lift).map (algebraMap R (R ⧸ span {x})) = rs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id rs]
    exact List.map_congr_left fun b _ ↦ by simp [Ideal.Quotient.algebraMap_eq, hlift]
  have hloc : IsLocalHom (Ideal.Quotient.mk (span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (R ⧸ span {x})).comap (Ideal.Quotient.mk (span {x})) =
      maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  have hmem : ∀ r ∈ x :: rs.map lift, r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
      rw [← hcomap, Ideal.mem_comap, hlift]
      exact hrs b hb
  have e : (R ⧸ span {x}) ≃ₗ[R] QuotSMulTop x R :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have hreg' : IsWeaklyRegular R (x :: rs.map lift) := by
    rw [isWeaklyRegular_cons_iff]
    refine ⟨hxR, (e.isWeaklyRegular_congr _).mp ?_⟩
    rw [← isWeaklyRegular_map_algebraMap_iff (R ⧸ span {x}), hrs']
    exact hreg
  have := hd _ hmem hreg'
  simp only [List.length_cons, List.length_map] at this
  omega

theorem hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _ _ _ k hM
    refine hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM
    have := hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')
    simp at this
  | succ d ih =>
    intro R _ _ _ hd M _ _ _ k hM
    by_cases hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y
    swap
    · push Not at hex
      have := hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM
      exact hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)
    obtain ⟨x, hx, hxR⟩ := hex
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hd' := length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp
        (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hKx := GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hKx' := ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx
    have hK2 := hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'
    exact (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

theorem hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d)
    (ms : List R) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R M) n → (∀ r ∈ ms, r ∈ maximalIdeal R) →
        IsWeaklyRegular M ms → HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length) := by
  induction ms with
  | nil =>
    intro M _ _ _ _ n hM _ _
    simpa using hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le d R hd M n hM
  | cons x ms ih =>
    intro M _ _ _ _ n hM hms hreg
    simp only [List.mem_cons, forall_eq_or_imp] at hms
    rw [isWeaklyRegular_cons_iff] at hreg
    have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hms.1
    have heq : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) =
        projectiveDimension (ModuleCat.of R M) + 1 :=
      ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R M) x hreg.1 hms.1
    have hQ : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x M)) (n + 1) := by
      rw [← projectiveDimension_le_iff, heq, Nat.cast_add, Nat.cast_one]
      gcongr
      exact (projectiveDimension_le_iff _ _).mpr hM
    have hih := ih (QuotSMulTop x M) (n + 1) hQ hms.2 hreg.2
    rw [← projectiveDimension_le_iff, heq] at hih
    rw [← projectiveDimension_le_iff, List.length_cons]
    rcases Nat.eq_zero_or_pos (d - ms.length) with h0 | hpos
    · rw [h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton] at hih
      exact absurd hih (not_subsingleton M)
    · have hsplit : d - ms.length = (d - (ms.length + 1)) + 1 := by omega
      rw [hsplit, Nat.cast_add, ← Nat.cast_one (R := WithBot ℕ∞)] at hih
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp hih

theorem AuslanderBuchsbaumProjDimUpper.proof : AuslanderBuchsbaumProjDimUpper.Statement := by
  intro R _ _ _ M _ _ _ _ n d ms hM hd hms hreg
  exact hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg

end GroundTheory.Heights₂.Heights
end
