module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBScale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyScaleLift

theorem exists_keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (x : KeyIn R') (a : Rˣ) (M : Matrix (Fin x.P.g) (Fin x.P.g) R), KeyPB x y f → IsUnit M.det → ∃ y₁ : KeyIn R, ∀ (t : x.P.L.Sec) (ht : _) (v : Fin x.P.g → (epsR R' ⟶ x.P.A)) (hv : _), (∀ i, t.f i = constFn x.P.A.hom _ (f a) * x.th.f i) → (∀ i, IsLieComb (fun k => f (M i k)) x.v (v i)) → KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, t, ht, v, hv⟩ y₁ f := by
  intro R R' _ _ f y x a M h hM
  obtain ⟨e⟩ : Nonempty (x.P.g = y.P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := h
    exact ⟨hg⟩
  haveI := y.P.isAb.comm
  let N : Matrix (Fin y.P.g) (Fin y.P.g) R := Matrix.reindex (finCongr e) (finCongr e) M
  have hN : IsUnit N.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra R y.P.A y.P.g y.v y.basis.1
  choose v₁ hv₁ using fun i => (ex (N i)).exists
  obtain ⟨s, hs, -, hle⟩ := exists_sec_div y.P.A.hom a.inv_mul y.th
  refine ⟨⟨y.P, y.g_pos, y.rig, y.rig_gen, s, fun p => (y.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁,
    (bas N v₁ y.basis hv₁).2 hN⟩, fun t ht v hv h₁ h₂ => ?_⟩
  exact KeyPBScale.keyPB_scale R R' f y.P y.g_pos y.rig y.rig_gen y.th y.th_ne y.v y.basis s _ v₁ _ a N x.P e
    x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis t ht v hv hs hv₁ h₁ h₂ h

end GlobalTheory.KeyScaleLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDominantComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyCx


open TensorProduct in
theorem exists_dominant_component :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (g : R →+* ℂ), ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ), Algebra.FiniteType ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  intro R _ _ _ g
  letI : Algebra R (ℂ ⊗[ℤ] R) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Flat R (ℂ ⊗[ℤ] R) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight ℤ R ℂ).symm.toLinearEquiv
  let e₀ : (ℂ ⊗[ℤ] R) →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g.toIntAlgHom (fun _ _ => Commute.all _ _)
  have he : ∀ r : R, e₀ (algebraMap R (ℂ ⊗[ℤ] R) r) = g r := by
    intro r
    change e₀ (1 ⊗ₜ r) = g r
    simp [e₀]
  let Q : Ideal (ℂ ⊗[ℤ] R) := RingHom.ker e₀.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqQ, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal R)) (q := Q.under R) Q bot_le
  refine ⟨(ℂ ⊗[ℤ] R) ⧸ q, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk q).comp (algebraMap R _),
    Ideal.Quotient.liftₐ q e₀ (fun a ha => hqQ ha), inferInstance, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : r ∈ q.under R :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [← hlo.over] at h1
    exact h1
  · ext r
    exact he r

end GlobalTheory.KeyCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSmoothNormalisation
namespace GlobalTheory.CurveNorm

theorem exists_lift_of_isIntegral {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by
  have hsurj : Function.Surjective e := fun c => ⟨algebraMap k E c, by simp⟩
  haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E')
    (RingHom.ker e) ⊥ (by
      intro x hx
      have : x = 0 := hinj (by simpa using hx)
      simp [this])
  have key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x) := by
    intro x
    have h1 : algebraMap k E (e x) - x ∈ RingHom.ker e := by simp [RingHom.mem_ker]
    rw [← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  haveI : Algebra.IsIntegral k (E' ⧸ Q) := by
    constructor
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp0⟩ := Algebra.IsIntegral.isIntegral (R := E) y
    refine ⟨p.map (e : E →+* k), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap k (E' ⧸ Q)).comp (e : E →+* k)
        = (Ideal.Quotient.mk Q).comp (algebraMap E E') := RingHom.ext key
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hbij : Function.Bijective (algebraMap k (E' ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : k ≃ₐ[k] (E' ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  refine ⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩
  ext x
  apply φ.injective
  exact (φ.apply_symm_apply _).trans (key x).symm

theorem exists_smooth_normalisation (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] [Ring.DimensionLEOne E] (e : E →ₐ[ℂ] ℂ) :
    ∃ (E' : Type) (_ : CommRing E') (_ : IsDomain E') (_ : Algebra ℂ E') (ρ : E →ₐ[ℂ] E')
      (e' : E' →ₐ[ℂ] ℂ), Algebra.Smooth ℂ E' ∧ Function.Injective ρ ∧ e'.comp ρ = e := by
  let F := FractionRing E
  let E' : Type := integralClosure E F
  haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F
  letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra
  haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'
  haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F
  haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsDedekindRing E' := ⟨⟩
  haveI : IsDedekindDomain E' := inferInstance
  have hinj : Function.Injective (algebraMap E E') := by
    intro x y h
    apply IsFractionRing.injective E F
    exact congrArg Subtype.val h
  obtain ⟨e', he'⟩ := exists_lift_of_isIntegral hinj e
  exact ⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e',
    GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩

end GlobalTheory.CurveNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomNeZeroOfCountable
namespace GlobalTheory

theorem exists_eval_ne_zero_of_countable {σ : Type} [Finite σ] (T : Set (MvPolynomial σ ℂ))
    (hT : T.Countable) (h0 : (0 : MvPolynomial σ ℂ) ∉ T) :
    ∃ c : σ → ℂ, ∀ p ∈ T, MvPolynomial.eval c p ≠ 0 := by
  classical
  have := Fintype.ofFinite σ
  have hd : Dense (⋂ p ∈ T, {c : σ → ℂ | MvPolynomial.eval c p ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun p _ => ?_) hT (fun p hp => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const
    · intro c
      by_contra hc
      have hev : (fun c : σ → ℂ => MvPolynomial.eval c p) =ᶠ[nhds c] 0 := by
        have h1 : (closure {c : σ → ℂ | MvPolynomial.eval c p ≠ 0})ᶜ ∈ nhds c :=
          isClosed_closure.isOpen_compl.mem_nhds hc
        filter_upwards [h1] with x hx
        by_contra hx'
        exact hx (subset_closure hx')
      have hz := (AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ c) hev
      have : p = 0 := MvPolynomial.funext fun x => by
        simpa using hz (Set.mem_univ x)
      exact h0 (this ▸ hp)
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun p hp => Set.mem_iInter₂.1 hc p hp⟩

theorem exists_algHom_ne_zero_of_countable (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by
  classical
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin d) ℂ) E := hfin
  have hn : ∀ r : E, r ≠ 0 → ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap (MvPolynomial (Fin d) ℂ) E n ∈ Ideal.span {r} := by
    intro r hr
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ)
      (I := Ideal.span {r}) hr (Ideal.mem_span_singleton_self r)
      (Algebra.IsIntegral.isIntegral r)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose! n hn0 hnr using hn
  have hne : ∀ r ∈ T, r ≠ 0 := fun r hr h => h0 (h ▸ hr)
  obtain ⟨c, hc⟩ := exists_eval_ne_zero_of_countable (n '' T) (hT.image n) (by
    rintro ⟨r, hr, h⟩
    exact hn0 r (hne r hr) h)
  have hsurj : Function.Surjective (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ) :=
    fun z => ⟨MvPolynomial.C z, by simp⟩
  haveI hmax : (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := E)
    (RingHom.ker (MvPolynomial.eval c : MvPolynomial (Fin d) ℂ →+* ℂ)) (by
      have : RingHom.ker (algebraMap (MvPolynomial (Fin d) ℂ) E) = ⊥ :=
        (RingHom.injective_iff_ker_eq_bot _).1 hinj
      rw [this]
      exact bot_le)
  letI : Field (E ⧸ Q) := Ideal.Quotient.field Q
  haveI : Module.Finite ℂ (E ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (E ⧸ Q)
  have hbij : Function.Bijective (Algebra.ofId ℂ (E ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] (E ⧸ Q) := AlgEquiv.ofBijective _ hbij
  refine ⟨(e.symm : (E ⧸ Q) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ Q), fun r hr h => ?_⟩
  have h1 : Ideal.Quotient.mk Q r = 0 := by
    apply e.symm.injective
    rw [map_zero]
    exact h
  have h2 : r ∈ Q := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : n r ∈ Q.under (MvPolynomial (Fin d) ℂ) :=
    (Ideal.mem_under (MvPolynomial (Fin d) ℂ) Q).2
      ((Ideal.span_singleton_le_iff_mem Q).2 h2 (hnr r (hne r hr)))
  rw [hQp] at h3
  exact hc (n r) ⟨r, hr, rfl⟩ h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MkTensorLe
namespace GlobalTheory.EmbC

open Cardinal TensorProduct

theorem mk_tensor_le (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by
  have h1 : Function.Surjective (fun l : List (A × B) => (l.map (fun p => p.1 ⊗ₜ[R] p.2)).sum) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨[], by simp⟩
    | tmul a b => exact ⟨[(a, b)], by simp⟩
    | add x y hx hy =>
      obtain ⟨l, rfl⟩ := hx
      obtain ⟨m, rfl⟩ := hy
      exact ⟨l ++ m, by simp⟩
  refine (Cardinal.mk_le_of_surjective h1).trans ((Cardinal.mk_list_le_max _).trans ?_)
  refine max_le Cardinal.aleph0_le_continuum ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
  calc #A * #B ≤ 𝔠 * 𝔠 := mul_le_mul' hA hB
    _ = 𝔠 := Cardinal.continuum_mul_self

theorem exists_emb (R A B : Type) [CommRing R] [IsDomain R] [Field A] [Field B] [CharZero A]
    [Algebra R A] [Algebra R B] (hA : #A = 𝔠) (hB : #B = 𝔠)
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B)) :
    ∃ (σ : A →+* ℂ) (σ' : B →+* ℂ), σ.comp (algebraMap R A) = σ'.comp (algebraMap R B) := by
  haveI : Nontrivial (A ⊗[R] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain R A B ha hb
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (A ⊗[R] B)
  letI : Field ((A ⊗[R] B) ⧸ m) := Ideal.Quotient.field m
  let L := (A ⊗[R] B) ⧸ m
  let Ω := AlgebraicClosure L
  let p : (A ⊗[R] B) →+* Ω := (algebraMap L Ω).comp (Ideal.Quotient.mk m)
  let i : A →+* Ω := p.comp (Algebra.TensorProduct.includeLeftRingHom)
  let j : B →+* Ω := p.comp (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  haveI : CharZero Ω := charZero_of_injective_ringHom i.injective
  have hL : #L ≤ 𝔠 :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans (mk_tensor_le R A B hA.le hB.le)
  have hΩ : #Ω = 𝔠 := by
    apply le_antisymm
    · exact (Algebra.IsAlgebraic.cardinalMk_le_max L Ω).trans (max_le hL Cardinal.aleph0_le_continuum)
    · rw [← hA]; exact Cardinal.mk_le_of_injective i.injective
  obtain ⟨e⟩ : Nonempty (Ω ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [hΩ]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by rw [hΩ, Cardinal.mk_complex]))
  refine ⟨e.toRingHom.comp i, e.toRingHom.comp j, ?_⟩
  ext r
  have : (algebraMap R A r) ⊗ₜ[R] (1 : B) = (1 : A) ⊗ₜ[R] (algebraMap R B r) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show e (p ((algebraMap R A r) ⊗ₜ[R] (1 : B))) = e (p ((1 : A) ⊗ₜ[R] (algebraMap R B r)))
  rw [this]

theorem exists_comp_eq (R : Type) [CommRing R] [IsDomain R] (f f' : R →+* ℂ)
    (hf : Function.Injective f) (hf' : Function.Injective f') :
    ∃ σ σ' : ℂ →+* ℂ, σ.comp f = σ'.comp f' :=
  @exists_emb R ℂ ℂ _ _ _ _ _ f.toAlgebra f'.toAlgebra Cardinal.mk_complex Cardinal.mk_complex hf hf'

end GlobalTheory.EmbC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrimeDimensionLEOneAvoiding
open Polynomial
namespace GlobalTheory.LineThrough

theorem exists_common_nonroot (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Countable)
    (h0 : (0 : MvPolynomial (Fin d) ℂ) ∉ S) :
    ∃ c : Fin d → ℂ, ∀ f ∈ S, MvPolynomial.eval c f ≠ 0 := by
  have hd : Dense (⋂ f ∈ S, {c : Fin d → ℂ | MvPolynomial.eval c f ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun f _ => ?_) hS (fun f hf => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval f) continuous_const
    · rw [Metric.dense_iff]
      intro x r hr
      by_contra hne
      apply h0
      have : f = 0 := by
        refine MvPolynomial.funext_set (fun i => Metric.ball (x i) r)
          (fun i => (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) |> infinite_of_mem_nhds (x i)) ?_
        intro y hy
        by_contra hy0
        apply hne
        refine ⟨y, ?_, by simpa using hy0⟩
        rw [ball_pi _ hr]
        exact hy
      exact this ▸ hf
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun f hf => by simpa using Set.mem_iInter₂.1 hc f hf⟩

noncomputable def lineMap {d : ℕ} (a c : Fin d → ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => C (a i) + C (c i - a i) * X

theorem eval_zero_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem eval_one_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 1 = MvPolynomial.eval c f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem lineMap_self {d : ℕ} (a : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    lineMap a a f = C (MvPolynomial.eval a f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, hp]; simp [lineMap]

theorem lineMap_surjective {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : c i - a i ≠ 0 := sub_ne_zero.2 hi
  have hX : (X : ℂ[X]) ∈ (lineMap a c).range := by
    refine ⟨MvPolynomial.C (c i - a i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)), ?_⟩
    simp only [lineMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [add_sub_cancel_left, ← mul_assoc, ← C_sub, ← C_mul, inv_mul_cancel₀ hi', C_1, one_mul]
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X]
  exact Algebra.adjoin_le (by simpa using hX)

theorem isMaximal_of_ker_lineMap_lt {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by
  by_cases hc : c = a
  · subst hc
    have hk : RingHom.ker (lineMap c c) = RingHom.ker (MvPolynomial.eval c) := by
      ext f
      simp [RingHom.mem_ker, lineMap_self]
    have hm : (RingHom.ker (MvPolynomial.eval c)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)
    rw [hk] at h
    exact absurd (hm.1.2 P h) hP.ne_top
  · have hs := lineMap_surjective hc
    have hp : (P.map (lineMap a c)).IsPrime := Ideal.map_isPrime_of_surjective hs h.le
    have hcm : (P.map (lineMap a c)).comap (lineMap a c) = P := by
      rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left]
      exact h.le
    have hne : P.map (lineMap a c) ≠ ⊥ := by
      intro hb
      rw [hb] at hcm
      exact h.ne hcm
    have hm : (P.map (lineMap a c)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hp
    rw [← hcm]
    exact Ideal.comap_isMaximal_of_surjective _ hs

theorem exists_prime_dimensionLEOne_avoiding
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) E := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hn : ∀ r : T, ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap _ E n ∈ Ideal.span {(r : E)} := by
    intro r
    have hr : (r : E) ≠ 0 := fun h => h0 (h ▸ r.2)
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) hr
      (Ideal.mem_span_singleton_self (r : E)) (Algebra.IsIntegral.isIntegral _)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose n hn0 hn using hn
  haveI : Countable T := hT.to_subtype
  obtain ⟨c, hc⟩ := exists_common_nonroot d (Set.range n) (Set.countable_range n)
    (by rintro ⟨r, hr⟩; exact hn0 r hr)
  let a : Fin d → ℂ := fun i => e (g (MvPolynomial.X i))
  have hea : ∀ f, e (g f) = MvPolynomial.eval a f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      have : g (MvPolynomial.C r) = algebraMap ℂ E r := g.commutes r
      simp [this]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, a]
  haveI hpp : (RingHom.ker (lineMap a c)).IsPrime := RingHom.ker_isPrime _
  haveI hM : (RingHom.ker e).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (lineMap a c) ≤ (RingHom.ker e).under (MvPolynomial (Fin d) ℂ) := by
    intro f hf
    change e (g f) = 0
    rw [hea, ← eval_zero_lineMap a c, RingHom.mem_ker.1 hf, eval_zero]
  obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := RingHom.ker (lineMap a c)) (RingHom.ker e) hle
  have hQc : Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) = RingHom.ker (lineMap a c) :=
    hQo.over.symm
  refine ⟨Q, hQp, hQ, fun r hr hrQ => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · have h1 : n ⟨r, hr⟩ ∈ RingHom.ker (lineMap a c) := by
      rw [← hQc]
      exact (Ideal.span_singleton_le_iff_mem _).2 hrQ (hn ⟨r, hr⟩)
    apply hc _ ⟨⟨r, hr⟩, rfl⟩
    rw [← eval_one_lineMap a c, RingHom.mem_ker.1 h1, eval_zero]
  · have hs : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
    have hlt : Q < P.comap (Ideal.Quotient.mk Q) := by
      refine lt_of_le_of_ne (fun x hx => ?_) (fun h => hP0 ?_)
      · simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
      · rw [← Ideal.map_comap_of_surjective _ hs P, ← h, Ideal.map_quotient_self]
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ) hlt
    change Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) < _ at hlt'
    rw [hQc] at hlt'
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := MvPolynomial (Fin d) ℂ) _
      (isMaximal_of_ker_lineMap_lt a c _ hlt')
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hs hm with h | h
    · rw [Ideal.map_comap_of_surjective _ hs] at h
      exact absurd h hP.ne_top
    · rwa [Ideal.map_comap_of_surjective _ hs] at h

end GlobalTheory.LineThrough
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.ThetaFrameSpec

theorem key_descends (hL : Out.Laws) (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
    (x : KeyIn S) (u : S) :
    ∃ (R : Subring S) (y : KeyIn R), u ∈ R ∧ Algebra.FiniteType ℤ R ∧ KeyPB x y R.subtype := by
  classical
  obtain ⟨R₀, P₀, φ, hfg, hg, hφ, hiso⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring S x.P
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨r, hr, hnear⟩ := GlobalTheory.KeyNear.main hL R₀ P₀ (hg ▸ x.g_pos)
    (PrimeSpectrum.comap R₀.subtype (IsLocalRing.closedPoint S))
  have hru : IsUnit (r : S) := by
    by_contra h
    exact hr ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨R₁, h₁, hF₁, hfg₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin S R₀ {((hru.unit⁻¹ : Sˣ) : S)} hfg
  have hm : ((hru.unit⁻¹ : Sˣ) : S) ∈ R₁ := hF₁ (by simp)
  obtain ⟨y, π, hyg, hπ, hπiso⟩ := hnear R₁ (Subring.inclusion h₁)
    (IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext hru.mul_val_inv))
  have hcomp : spMap R₁.subtype ≫ spMap (Subring.inclusion h₁) = spMap R₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  let ψ : x.P.A.left ⟶ y.P.A.left := hπ.1.lift φ (x.P.A.hom ≫ spMap R₁.subtype)
    (by rw [Category.assoc, hcomp]; exact hφ.1.w)
  have hψ₁ : ψ ≫ π = φ := hπ.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ y.P.A.hom = x.P.A.hom ≫ spMap R₁.subtype := hπ.1.lift_snd _ _ _
  have hψ : IsGrpPullback x.P.A y.P.A (spMap R₁.subtype) ψ :=
    hπ.cancel (by rw [hcomp, hψ₁]; exact hφ) hψ₂
  have hψiso : LBIso x.P.L (y.P.L.pull ψ) :=
    LBIso.trans x.P.isLB (pull_isLB P₀.isLB φ) (pull_isLB y.P.isLB ψ) hiso
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hπiso ψ hψ₁.symm).symm
  obtain ⟨rig, hrig, th, hth, v, hv, hpb⟩ := GlobalTheory.KeyTf.exists_keyPB_on R₁ S R₁.subtype y x.P ψ x.g_pos (hg.symm.trans hyg.symm) hψ hψiso
  obtain ⟨a, t, ht, hta, hid⟩ := (GlobalTheory.KeyOnPol.main hL S).2 ⟨x.P, x.g_pos, rig, hrig, th, hth, v, hv⟩
    x.rig x.rig_gen x.th x.th_ne x.v x.basis
  haveI := x.P.isAb.comm
  choose M hM using fun i => (hv.2 (x.v i) (x.basis.1 i)).exists
  have hdet : IsUnit (Matrix.det (Matrix.of M)) :=
    ((GlobalTheory.LieComb.lieComb_algebra S x.P.A x.P.g v hv.1).2.2.2.2 (Matrix.of M) x.v hv hM).1 x.basis
  obtain ⟨R₂, h₂, hF₂, hfg₂⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin S R₁
    ({u, (a : S), ((a⁻¹ : Sˣ) : S), ((hdet.unit⁻¹ : Sˣ) : S)} ∪ Finset.univ.image fun p : Fin x.P.g × Fin x.P.g => M p.1 p.2) hfg₁
  have m₁ : u ∈ R₂ := hF₂ (by simp)
  have m₂ : (a : S) ∈ R₂ := hF₂ (by simp)
  have m₃ : ((a⁻¹ : Sˣ) : S) ∈ R₂ := hF₂ (by simp)
  have m₄ : ((hdet.unit⁻¹ : Sˣ) : S) ∈ R₂ := hF₂ (by simp)
  have m₅ : ∀ i k, M i k ∈ R₂ := fun i k => hF₂ (by
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union]
    exact Or.inr ⟨(i, k), by simp, rfl⟩)
  obtain ⟨y₂, hy₂⟩ := exists_keyPB_ring y (Subring.inclusion h₂)
  have hpb₂ := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ (Subring.inclusion h₂) R₂.subtype hy₂ hpb
  let a₂ : R₂ˣ := ⟨⟨a, m₂⟩, ⟨_, m₃⟩, Subtype.ext a.mul_inv, Subtype.ext a.inv_mul⟩
  let M₂ : Matrix (Fin x.P.g) (Fin x.P.g) R₂ := Matrix.of fun i k => ⟨M i k, m₅ i k⟩
  have hdet₂ : IsUnit M₂.det := by
    refine IsUnit.of_mul_eq_one ⟨_, m₄⟩ (Subtype.ext ?_)
    have e : (M₂.det : S) = (Matrix.of M).det := R₂.subtype.map_det M₂
    show (M₂.det : S) * _ = 1
    rw [e]
    exact hdet.mul_val_inv
  obtain ⟨y₃, hy₃⟩ := GlobalTheory.KeyScaleLift.exists_keyPB_scale R₂ S R₂.subtype y₂ ⟨x.P, x.g_pos, rig, hrig, th, hth, v, hv⟩ a₂ M₂ hpb₂ hdet₂
  exact ⟨R₂, y₃, m₁, hfg₂, GlobalTheory.keyPB_trans _ _ _ _ _ _ R₂.subtype (RingHom.id S) (hy₃ t ht x.v x.basis hta hM) hid⟩

theorem exists_smooth_through (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [Countable R]
    (g : R →+* ℂ) :
    ∃ (E : Type) (_ : CommRing E) (_ : IsDomain E) (_ : Algebra ℂ E) (ρ : R →+* E) (e : E →ₐ[ℂ] ℂ),
      Algebra.Smooth ℂ E ∧ Function.Injective ρ ∧ e.toRingHom.comp ρ = g := by
  obtain ⟨E, _, _, _, ρ, e, hft, hρ, he⟩ := GlobalTheory.KeyCx.exists_dominant_component R g
  obtain ⟨Q, hQ, hle, hT, hdim⟩ := GlobalTheory.LineThrough.exists_prime_dimensionLEOne_avoiding E e (ρ '' {0}ᶜ) ((Set.to_countable _).image _) (by
    rintro ⟨r, hr, h⟩
    exact hr (hρ (h.trans (map_zero ρ).symm)))
  obtain ⟨E', _, _, _, ρ', e', hs, hρ', he'⟩ := GlobalTheory.CurveNorm.exists_smooth_normalisation (E ⧸ Q) (Ideal.Quotient.liftₐ Q e fun a ha => hle ha)
  refine ⟨E', inferInstance, inferInstance, inferInstance, (ρ'.toRingHom.comp (Ideal.Quotient.mk Q)).comp ρ, e', hs,
    ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h
    refine hT _ ⟨r, h, rfl⟩ (Ideal.Quotient.eq_zero_iff_mem.1 (hρ' ?_))
    rw [map_zero]; exact hr
  · rw [← he]
    ext r
    exact AlgHom.congr_fun he' (Ideal.Quotient.mk Q (ρ r))

def IsVal (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8

theorem exists_isVal (hT : ThetaUnifAV) (x : KeyIn ℂ) : ∃ t, IsVal x t := by
  obtain ⟨τ, M, a, b, c, h₁, h₂, -, h₃⟩ := (GlobalTheory.KeyNormalExists.exists_normalAt hT x).1
  exact ⟨_, τ, M, a, b, c, h₁, h₂, h₃, rfl⟩

theorem isVal_injective (hT : ThetaUnifAV)
    (hE : ∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → IsVal x t → IsVal x' t' → t' = f t)
    {R : Type} [CommRing R] [IsDomain R] (y : KeyIn R) (g g' : R →+* ℂ) (hg : Function.Injective g)
    (hg' : Function.Injective g') (u : R) {x x' : KeyIn ℂ} (hx : KeyPB x y g) (hx' : KeyPB x' y g')
    (ht : IsVal x (g u)) {t' : ℂ} (ht' : IsVal x' t') : t' = g' u := by
  obtain ⟨σ, σ', h⟩ := GlobalTheory.EmbC.exists_comp_eq R g g' hg hg'
  obtain ⟨z, hz⟩ := exists_keyPB_ring x σ
  obtain ⟨s, hs⟩ := exists_isVal hT z
  have hz' : KeyPB z x' σ' := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ g' σ' hx'
    (h ▸ GlobalTheory.keyPB_trans _ _ _ _ _ _ g σ hx hz)
  refine σ'.injective ((hE σ' x' z t' s hz' ht' hs).symm.trans ((hE σ x z _ s hz ht hs).trans ?_))
  exact RingHom.congr_fun h u

theorem value_specialises : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → (∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf) → (∀ (f : ℂ →+* ℂ) (x x' : KeyIn ℂ) (t t' : ℂ), KeyPB x' x f → (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8) → (∃ (τ M : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a b : Fin x'.P.g → ℂ) (c : ℂ), charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x' τ M a b c ∧ t' = M.det ^ 4 / c ^ 8) → t' = f t) → (∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsPrincipalIdealRing S] (x₀ : KeyIn S) (f f' : S →+* ℂ) (u : S) (x x' : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ) (τ' M' : Matrix (Fin x'.P.g) (Fin x'.P.g) ℂ) (a' b' : Fin x'.P.g → ℂ) (c' : ℂ), Function.Injective f → KeyPB x x₀ f → KeyPB x' x₀ f' → charHalf _ a b → charHalf _ a' b' → c ≠ 0 → c' ≠ 0 → NormalAt x τ M a b c → NormalAt x' τ' M' a' b' c' → M.det ^ 4 / c ^ 8 = f u → M'.det ^ 4 / c' ^ 8 = f' u) := by
  intro hL hT hI hN hE S _ _ _ _ x₀ f f' u x x' τ M a b c τ' M' a' b' c' hf hx hx' hab hab' hc hc' hn hn' hu
  obtain ⟨N, hN, hK⟩ := hN
  obtain ⟨R, y, huR, hfg, hy⟩ := key_descends hL S x₀ u
  haveI : Countable R := by
    obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hfg
    haveI : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max_lift.trans (by simp)
    exact hp.countable
  obtain ⟨E, _, _, _, ρ, e, hs, hρ, he⟩ := exists_smooth_through R (f'.comp R.subtype)
  obtain ⟨z, hz⟩ := exists_keyPB_ring y ρ
  obtain ⟨κ, hκ⟩ := GlobalTheory.KeySmoothBase.exists_unit_of_smooth hT hL.polBaseChange N hK ℂ E z
  choose w hw using fun s : E →ₐ[ℂ] ℂ => exists_keyPB_ring z s.toRingHom
  choose t ht using fun s : E →ₐ[ℂ] ℂ => exists_isVal hT (w s)
  have hxy : KeyPB x y (f.comp R.subtype) := GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hy hx
  have gen : ∀ s : E →ₐ[ℂ] ℂ, (∀ r ∈ ρ '' {0}ᶜ, s r ≠ 0) → t s = s (ρ ⟨u, huR⟩) := fun s h =>
    isVal_injective hT hE y (f.comp R.subtype) (s.toRingHom.comp ρ) (hf.comp Subtype.val_injective)
      ((injective_iff_map_eq_zero _).2 fun r hr => by_contra fun h' => h _ ⟨r, h', rfl⟩ hr) ⟨u, huR⟩ hxy
      (GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hz (hw s)) ⟨τ, M, a, b, c, hab, hc, hn, hu.symm⟩ (ht s)
  have hc₀ : (ρ '' {0}ᶜ).Countable := (Set.to_countable _).image _
  have h₀ : (0 : E) ∉ ρ '' {0}ᶜ := by
    rintro ⟨r, hr, h⟩
    exact hr (hρ (h.trans (map_zero ρ).symm))
  have hpow : ρ ⟨u, huR⟩ ^ N z.P.g = κ := by
    by_contra h
    obtain ⟨s, hs⟩ := GlobalTheory.exists_algHom_ne_zero_of_countable E (insert (ρ ⟨u, huR⟩ ^ N z.P.g - κ) (ρ '' {0}ᶜ)) (hc₀.insert _) (by
      rintro (h' | h')
      exacts [h (sub_eq_zero.1 h'.symm), h₀ h'])
    refine hs _ (Set.mem_insert _ _) ?_
    rw [map_sub, map_pow, ← gen s fun r hr => hs r (Set.mem_insert_of_mem _ hr),
      hκ s.toRingHom (w s) (t s) (hw s) (ht s)]
    exact sub_self _
  have hunit : IsUnit (ρ ⟨u, huR⟩) :=
    (isUnit_pow_iff (Nat.one_le_iff_ne_zero.1 (hN z.P.g))).1 (hpow ▸ κ.isUnit)
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.exists_algHom_ne_zero_of_countable E _ hc₀ h₀
  have key := GlobalTheory.RootConst.value_eq_unit_of_pow_eq hL hT hI E z (N z.P.g) hunit.unit t s₀ (hN _) (fun s => ⟨w s, hw s, ht s⟩)
    (fun s => by
      rw [hκ s.toRingHom (w s) (t s) (hw s) (ht s), ← map_pow, IsUnit.unit_spec, hpow]; rfl)
    (gen s₀ hs₀) e
  have hwe : KeyPB (w e) y (f'.comp R.subtype) := he ▸ GlobalTheory.keyPB_trans _ _ _ _ _ _ _ _ hz (hw e)
  have hid : KeyPB x' (w e) (RingHom.id ℂ) := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ _ _ _ _ (RingHom.id ℂ) hwe
    (GlobalTheory.keyPB_trans _ _ _ _ _ _ R.subtype f' hy hx')
  refine (hE _ _ _ (t e) _ hid (ht e) ⟨τ', M', a', b', c', hab', hc', hn', rfl⟩).trans (key.trans ?_)
  exact RingHom.congr_fun he ⟨u, huR⟩

end GlobalTheory.ThetaFrameSpec
end
