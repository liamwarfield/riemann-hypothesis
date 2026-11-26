module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OpenNear

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearUp
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NearCore
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer

open UpperTheory.ConvolutionTheory.Loc.BallG

private theorem quot_zero {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H) {F : G → ℂ}
    (h : ∀ g, F g = 0) : quotIntegral μ H ν F = 0 := by
  simp [quotIntegral, h]

section Alg

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

private theorem incl_inj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun x y h => by
  ext i j
  exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)

private theorem sigma_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) : sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  ext i j
  exact σ.commutes _

private theorem norm_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) :
    normGL σ (incl y : GL (Fin n) E) = incl (y ^ Module.finrank k E) := by
  unfold normGL
  induction Module.finrank k E with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, ih, pow_succ y, map_mul]
    congr 1
    clear ih
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ_apply, sigma_incl, ih]

private theorem sep_incl (γ : GL (Fin n) k) :
    ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable ↔ IsRegSemisimple γ := by
  have e : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) k).map (algebraMap k E) := rfl
  rw [e, Matrix.charpoly_map, Polynomial.separable_map]
  rfl

private theorem sep_conj (x h : GL (Fin n) E) : ((h * x * h⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly =
    (x : Matrix (Fin n) (Fin n) E).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private theorem comm_of_sep {a x y : GL (Fin n) E} (ha : (a : Matrix (Fin n) (Fin n) E).charpoly.Separable)
    (hx : x * a = a * x) (hy : y * a = a * y) : x * y = y * x :=
  Units.ext (UpperTheory.V.Z.Tf.Orb.centComm E n a x y ha (congrArg Units.val hx) (congrArg Units.val hy))

private theorem theta_pow [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) :
    (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
  rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]

private theorem mem_twCent_conj {G : Type} [Group G] (θ : Monoid.End G) (δ g x : G) :
    x ∈ twCent θ δ ↔ g⁻¹ * x * g ∈ twCent θ (twConj θ g δ) := by
  rw [mem_twCent, mem_twCent, twConj, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc _ = g⁻¹ * (x⁻¹ * δ * θ x) * θ g := by group
      _ = _ := by rw [h]
  · intro h
    calc _ = g * ((g⁻¹ * x * g)⁻¹ * (g⁻¹ * δ * θ g) * ((θ g)⁻¹ * θ x * θ g)) * (θ g)⁻¹ := by group
      _ = _ := by rw [h]; group

end Alg

section Loc

variable {k E : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] {σ : E ≃ₐ[k] E}
  (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} {r : ValueGroupWithZero E}
  (hr : r < valuation E (Module.finrank k E : E))

include hr in
private theorem root_conj {u u' y : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    (h : y⁻¹ * u ^ Module.finrank k E * y = u' ^ Module.finrank k E) : y⁻¹ * u * y = u' := by
  apply incl_inj (E := E)
  rw [map_mul, map_mul, map_inv]
  refine rootConj E n _ r hr _ hu _ hu' _ ?_
  rw [← map_pow, ← map_pow, ← h, map_mul, map_mul, map_inv]

include hgen hr in
private theorem rigid {u u' y y' : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (hu' : (incl u' : GL (Fin n) E) ∈ ball n r)
    {g : GL (Fin n) E} (h : g⁻¹ * incl (y * u * y⁻¹) * sigmaGL σ g = incl (y' * u' * y'⁻¹)) : ∃ x : GL (Fin n) k, incl x = g := by
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  obtain ⟨x, hx⟩ := ((hb n).2.2.1 hgen ((incl y)⁻¹ * g * incl y')).mp
    (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ (by
      show _ * _ * sigmaGL σ _ = _
      simp only [map_mul, map_inv, sigma_incl] at h ⊢
      calc _ = (incl y')⁻¹ * (g⁻¹ * (incl y * incl u * (incl y)⁻¹) * sigmaGL σ g) * incl y' := by group
        _ = _ := by rw [h]; group))
  exact ⟨y * x * y'⁻¹, by rw [map_mul, map_mul, map_inv, hx]; group⟩

include hgen hr in
private theorem cent_eq {u : GL (Fin n) k} (hu : (incl u : GL (Fin n) E) ∈ ball n r) (y : GL (Fin n) k) :
    twCent (sigmaGL σ) (incl (y * u * y⁻¹) : GL (Fin n) E) =
      (Subgroup.centralizer {y * u ^ Module.finrank k E * y⁻¹}).map incl := by
  ext x
  rw [mem_twCent, Subgroup.mem_map]
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := rigid hgen hr hu hu h
    refine ⟨x, ?_, rfl⟩
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul] at h
    have h1 := incl_inj h
    rw [Subgroup.mem_centralizer_singleton_iff, ← conj_pow]
    refine (Commute.pow_right ?_ _).eq
    calc x * (y * u * y⁻¹) = x * (x⁻¹ * (y * u * y⁻¹) * x) := by rw [h1]
      _ = _ := by group
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    have h1 := root_conj hr hu hu (y := y⁻¹ * x * y) (by
      calc _ = y⁻¹ * x⁻¹ * (y * u ^ Module.finrank k E * y⁻¹ * x) * y := by group
        _ = _ := by rw [← hx]; group)
    rw [sigma_incl, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc _ = y * ((y⁻¹ * x * y)⁻¹ * u * (y⁻¹ * x * y)) * y⁻¹ := by group
      _ = _ := by rw [h1]

end Loc

end UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer


open UpperTheory.ConvolutionTheory.Loc.NearIdentityCentralizer UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in
theorem UpperTheory.ConvolutionTheory.Loc.nearCore :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
      ∀ r : ValueGroupWithZero E, r < valuation E (Module.finrank k E : E) →
      ∀ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r → IsOpen (K : Set (GL (Fin n) E)) → IsCompact (K : Set (GL (Fin n) E)) →
      ∀ φ ∈ SB (GL (Fin n) E), ∀ f ∈ SB (GL (Fin n) k),
        (∀ g, φ g ≠ 0 → ∃ κ ∈ K, ∃ u : GL (Fin n) k, incl u ∈ K ∧ g = κ⁻¹ * incl u * sigmaGL σ κ) →
        (∀ g, f g ≠ 0 → ∃ u : GL (Fin n) k, incl u ∈ K ∧ g = u ^ Module.finrank k E) →
        (∀ u : GL (Fin n) k, incl u ∈ K →
          ∫ κ in (K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Set (GL (Fin n) k)), f (κ⁻¹ * u ^ Module.finrank k E * κ) ∂μk =
            ∫ κ in (K : Set (GL (Fin n) E)), φ (κ⁻¹ * incl u * sigmaGL σ κ) ∂μE) →
        Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk r hr K hK hKo hKc φ hφ f hf hs h2 h1
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  have mem : ∀ {g : GL (Fin n) E}, g ∈ K ↔ g ∈ ball n r := fun {g} => by rw [← hK]; rfl
  refine ⟨fun δ γ h μδ μγ hδ hN hμδ hμγ hmap => ?_, fun γ μγ _ hno _ => ?_⟩
  swap
  · refine quot_zero _ _ _ fun y => ?_
    by_contra h0
    obtain ⟨u, -, hu⟩ := h2 _ h0
    exact hno ⟨incl u, (incl y)⁻¹, by rw [norm_incl, ← hu, map_mul, map_mul, map_inv, inv_inv]⟩
  have hγE : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    rw [← sep_conj _ h, ← hN]
    exact hδ
  have hγ : IsRegSemisimple γ := (sep_incl γ).mp hγE
  by_cases hex : ∃ u y : GL (Fin n) k, (incl u : GL (Fin n) E) ∈ ball n r ∧ γ = y * u ^ Module.finrank k E * y⁻¹
  swap
  · rw [twOrbIntegralC, orbIntegralC, quot_zero, quot_zero]
    · intro y
      by_contra h0
      obtain ⟨u, hu, e⟩ := h2 _ h0
      exact hex ⟨u, y, mem.1 hu, by rw [← e]; group⟩
    · intro g
      by_contra h0
      obtain ⟨κ, -, u, hu, e⟩ := hs _ h0
      replace hu := mem.1 hu
      have e1 := congrArg (twNorm (sigmaGL σ) (Module.finrank k E)) e
      rw [← twConj, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), twNorm_twConj_of_pow_eq_one _ (theta_pow σ),
        ← normGL, ← normGL, hN, norm_incl] at e1
      obtain ⟨y, hy⟩ := conjDesc k E n γ (u ^ Module.finrank k E) hγ ⟨κ * g⁻¹ * h, by
        calc _ = κ * (κ⁻¹ * incl (u ^ Module.finrank k E) * κ) * κ⁻¹ := by group
          _ = _ := by rw [← e1]; group⟩
      exact hex ⟨u, y⁻¹, hu, by rw [hy]; group⟩
  obtain ⟨u, y, hu, hγu⟩ := hex
  have hN1 : normGL σ (incl (y * u * y⁻¹) : GL (Fin n) E) = incl γ := by rw [norm_incl, conj_pow, hγu]
  obtain ⟨g, hg⟩ := normInj k E σ hgen n γ hγ δ (incl (y * u * y⁻¹)) ⟨h, hN⟩ ⟨1, by simpa using hN1⟩
  obtain ⟨μ', hμ', hmap'⟩ := haarConj (GL (Fin n) E) _ _ g (mem_twCent_conj (sigmaGL σ) δ g) μδ hμδ
  rw [← twOrbConj k E σ n μE hμE δ g μδ μ' hδ hμδ hμ' hmap' φ hφ]
  have hz : h⁻¹ * g * incl γ = incl γ * (h⁻¹ * g) := by
    have e := hN1
    rw [hg, normGL, twNorm_twConj_of_pow_eq_one _ (theta_pow σ), ← normGL, hN] at e
    calc _ = h⁻¹ * g * (g⁻¹ * (h * incl γ * h⁻¹) * g) := by rw [e]
      _ = _ := by group
  have hpt : (fun x : twCent (sigmaGL σ) δ => g⁻¹ * (x : GL (Fin n) E) * g) =
      fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h := by
    funext x
    have e := comm_of_sep hγE (Subgroup.mem_centralizer_singleton_iff.mp
      (conj_twCent_mem_centralizer _ (theta_pow σ) hN x.2)) hz
    calc _ = (h⁻¹ * g)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h * (h⁻¹ * g)) := by group
      _ = _ := by rw [e]; group
  rw [hpt, hmap] at hmap'
  clear hμ' hpt
  revert μ'
  rw [← hg]
  intro μ' hmap'
  have hT : IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) := by
    have e : (Subgroup.centralizer ({γ} : Set (GL (Fin n) k)) : Set (GL (Fin n) k)) = {x | x * γ = γ * x} :=
      Set.ext fun x => Subgroup.mem_centralizer_singleton_iff
    rw [e]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hinv := (haarComm (GL (Fin n) k) _ hT (fun a ha b hb => comm_of_sep hγ
    (Subgroup.mem_centralizer_singleton_iff.mp ha) (Subgroup.mem_centralizer_singleton_iff.mp hb)) μγ hμγ).2.1
  have hreg : IsTwRegSemisimple σ (incl (y * u * y⁻¹) : GL (Fin n) E) := by
    rw [IsTwRegSemisimple, hN1]
    exact hγE
  obtain ⟨D, hD, hDs⟩ := orbProper k E σ hgen n _ hreg _ hφ.2
  haveI : ValuativeExtension k k := ⟨fun {_ _} => Iff.rfl⟩
  obtain ⟨a1, a2, a3, -⟩ := untwist k n μk γ
  obtain ⟨D', hD', hDs'⟩ := orbProper k k 1 a1 n γ (a3 hγ) _ hf.2
  have hKo' : IsOpen ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hKo.preimage hj.continuous
  have hKc' : IsCompact ((K.comap (incl : GL (Fin n) k →* GL (Fin n) E) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    hj.isCompact_preimage hKc
  rw [twOrbIntegralC, quotDesc _ _ incl hj μE μk hμE (unimod gLTop E n μE hμE).1 hμk (unimod gLTop k n μk hμk).1 K hKo hKc
    _ _ μ' μγ hT (by rw [cent_eq hgen hr hu y, ← hγu]) hμγ hinv hmap'.symm (fun g => φ (twConj (sigmaGL σ) g (incl (y * u * y⁻¹))))
    (hφ.1.continuous.comp (by unfold twConj; fun_prop))
    (fun s hs g => by rw [twConj_mul_left _ _ hs]) ?_ ⟨D, hD, fun x hx => hDs x (subset_tsupport _ hx)⟩, orbIntegralC,
    quotDesc _ _ (MonoidHom.id _) Topology.IsClosedEmbedding.id μk μk hμk (unimod gLTop k n μk hμk).1 hμk (unimod gLTop k n μk hμk).1
      _ hKo' hKc' _ _ μγ μγ hT (Subgroup.map_id _).symm hμγ hinv rfl (fun g => f (g⁻¹ * γ * g))
      (hf.1.continuous.comp (by fun_prop))
      (fun s hs g => by
        rw [Subgroup.mem_centralizer_singleton_iff] at hs
        congr 1
        calc _ = g⁻¹ * (s⁻¹ * (γ * s)) * g := by group
          _ = _ := by rw [← hs]; group)
      (fun g _ => ⟨g, 1, one_mem _, by simp⟩)
      ⟨D', hD', fun x hx => by
        obtain ⟨t, ht, d, hd, e⟩ := hDs' x (by rw [twConj, a2]; exact subset_tsupport _ hx)
        refine ⟨t, ?_, d, hd, e⟩
        rw [mem_twCent, a2] at ht
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc t * γ = t * (t⁻¹ * γ * t) := by rw [ht]
          _ = _ := by group⟩, Subgroup.comap_id]
  · congr 2
    funext x
    set w := (y⁻¹ * x)⁻¹ * u * (y⁻¹ * x) with hwdef
    have e : ∀ κ, twConj (sigmaGL σ) (incl x * κ) (incl (y * u * y⁻¹)) = κ⁻¹ * incl w * sigmaGL σ κ := fun κ => by
      simp only [hwdef, twConj, map_mul, map_inv, sigma_incl, mul_inv_rev, inv_inv, mul_assoc]
    have e' : x⁻¹ * γ * x = w ^ Module.finrank k E := by
      have := conj_pow (a := (y⁻¹ * x)⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      rw [hwdef, this, hγu]
      group
    have e'' : ∀ κ, ((MonoidHom.id _) x * κ)⁻¹ * γ * ((MonoidHom.id _) x * κ) = κ⁻¹ * w ^ Module.finrank k E * κ := fun κ => by
      rw [← e', MonoidHom.id_apply]; group
    simp only [e, e'']
    by_cases hw : (incl w : GL (Fin n) E) ∈ K
    · exact (h1 w hw).symm
    · rw [setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero]
      · intro κ hκ
        by_contra h0
        obtain ⟨u', hu', e2⟩ := h2 _ h0
        have e3 := root_conj hr hu (mem.1 hu') (y := y⁻¹ * x * κ) (by rw [← e2, ← e', hγu]; group)
        have e4 : w = κ * u' * κ⁻¹ := by rw [← e3, hwdef]; group
        rw [e4, map_mul, map_mul, map_inv] at hw
        exact hw (K.mul_mem (K.mul_mem hκ hu') (K.inv_mem hκ))
      · intro κ hκ
        by_contra h0
        obtain ⟨κ', hκ', u', hu', e2⟩ := hs _ h0
        have s1 : sigmaGL σ κ ∈ K := mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ))
        have s2 : sigmaGL σ κ' ∈ K := mem.2 ((sg_mem_ball_iff hc.isom).mpr (mem.1 hκ'))
        have h5 := K.mul_mem (K.mul_mem hκ (K.mul_mem (K.mul_mem (K.inv_mem hκ') hu') s2)) (K.inv_mem s1)
        rw [← e2, show κ * (κ⁻¹ * incl w * sigmaGL σ κ) * (sigmaGL σ κ)⁻¹ = incl w by group] at h5
        exact hw h5
  · intro x hx
    obtain ⟨κ, hκ, u', hu', e⟩ := hs _ hx
    obtain ⟨z, hz⟩ := rigid hgen hr hu (mem.1 hu') (y := y) (y' := 1) (g := x * κ⁻¹) (by
      rw [one_mul, inv_one, mul_one, map_mul (sigmaGL σ), map_inv]
      calc _ = κ * twConj (sigmaGL σ) x (incl (y * u * y⁻¹)) * (sigmaGL σ κ)⁻¹ := by unfold twConj; group
        _ = _ := by rw [e]; group)
    exact ⟨z, κ, hκ, by rw [hz]; group⟩
end

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent

private theorem sb_of_push {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {U : Set X} (hU : IsCompact U)
    {p : X → Y} (hp : Continuous p) (ho : IsOpen (p '' U)) {a : X → ℂ} (ha : IsLocallyConstant a) {f : Y → ℂ}
    (h1 : ∀ u ∈ U, f (p u) = a u) (h2 : ∀ y, y ∉ p '' U → f y = 0) : f ∈ SB Y := by
  refine ⟨fun s => ?_, HasCompactSupport.intro (hU.image hp) h2⟩
  rw [← isClosed_compl_iff, ← Set.preimage_compl]
  generalize sᶜ = t
  have hc : IsClosed (a ⁻¹' t) := by
    rw [← isOpen_compl_iff, ← Set.preimage_compl]
    exact ha _
  have e : f ⁻¹' t = p '' (U ∩ a ⁻¹' t) ∪ ((p '' U)ᶜ ∩ {_y | (0 : ℂ) ∈ t}) := by
    ext y
    by_cases hy : y ∈ p '' U
    · obtain ⟨u, hu, rfl⟩ := hy
      constructor
      · intro h
        exact Or.inl ⟨u, ⟨hu, by rwa [Set.mem_preimage, h1 u hu] at h⟩, rfl⟩
      · rintro (⟨u', ⟨hu', h⟩, e⟩ | ⟨h, -⟩)
        · rw [Set.mem_preimage, ← e, h1 u' hu']
          exact h
        · exact absurd ⟨u, hu, rfl⟩ h
    · rw [Set.mem_preimage, h2 y hy]
      constructor
      · exact fun h => Or.inr ⟨hy, h⟩
      · rintro (⟨u', ⟨hu', -⟩, e⟩ | ⟨-, h⟩)
        · exact absurd ⟨u', hu', e⟩ hy
        · exact h
  rw [e]
  exact ((hU.inter_right hc).image hp).isClosed.union (ho.isClosed_compl.inter isClosed_const)

private theorem avg_locConst {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    (μ : Measure G) {θ : G → G} (hθ : Continuous θ) {K : Set G} (hK : IsCompact K) (hm : MeasurableSet K) {φ : G → ℂ}
    (hφ : IsLocallyConstant φ) : IsLocallyConstant fun u => ∫ κ in K, φ (κ⁻¹ * u * θ κ) ∂μ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro u₀
  have h : ∀ᶠ u in nhds u₀, ∀ κ ∈ K, φ (κ⁻¹ * u * θ κ) = φ (κ⁻¹ * u₀ * θ κ) := by
    refine hK.eventually_forall_of_forall_eventually fun κ _ => ?_
    have h1 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * z.1 * θ z.2) (by fun_prop)).eventually_eq (u₀, κ)
    have h2 := (hφ.comp_continuous (f := fun z : G × G => z.2⁻¹ * u₀ * θ z.2) (by fun_prop)).eventually_eq (u₀, κ)
    filter_upwards [h1, h2] with z hz1 hz2
    exact hz1.trans hz2.symm
  filter_upwards [h] with u hu
  exact setIntegral_congr_fun hm hu

private theorem set_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (hm : MeasurableSet (K : Set G)) (F : G → ℂ) {z : G} (hz : z ∈ K) :
    ∫ κ in (K : Set G), F (z * κ) ∂μ = ∫ κ in (K : Set G), F κ ∂μ := by
  rw [← integral_indicator hm, ← integral_indicator hm, ← integral_mul_left_eq_self ((K : Set G).indicator F) z]
  congr 1
  funext κ
  by_cases h : κ ∈ K
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (K.mul_mem hz h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h ((K.mul_mem_cancel_left hz).1 h')]

variable {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ}

private theorem incl_inj : Function.Injective (incl : GL (Fin n) k → GL (Fin n) E) := fun x y h => by
  ext i j
  exact (algebraMap k E).injective (congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) h)

private theorem sigma_incl (σ : E ≃ₐ[k] E) (y : GL (Fin n) k) : sigmaGL σ (incl y : GL (Fin n) E) = incl y := by
  ext i j
  exact σ.commutes _

private theorem small [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension k E] {s : ValueGroupWithZero E} (hs : s ≠ 0) :
    ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ∀ g ∈ ball n ρ, (incl g : GL (Fin n) E) ∈ ball n s := by
  have key : ∀ a b : k, valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔ valuation k a ≤ valuation k b := fun a b => by
    rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]
  obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
  have h1 : valuation k x < 1 := hx ▸ uniformizer_lt_one
  have h0 : x ≠ 0 := fun h => by
    rw [h, map_zero] at hx
    exact uniformizer_ne_zero hx.symm
  have h2 : valuation E (algebraMap k E x) < 1 := by
    have := key 1 x
    rw [map_one, map_one, map_one] at this
    exact lt_of_not_ge fun h => (not_le.2 h1) (this.1 h)
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h2 (Units.mk0 s hs)
  refine ⟨valuation k (x ^ m), zero_lt_iff.2 (by simpa using fun h => absurd h h0), fun g hg i j => ?_⟩
  have e : ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j =
      algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) := by
    rw [map_sub]
    congr 1
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [e]
  refine ((key _ _).2 (hg i j)).trans ?_
  rw [map_pow, map_pow]
  exact hm.le

end UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent

open UpperTheory.ConvolutionTheory.Loc.NearIdentityAscent UpperTheory.ConvolutionTheory.Loc.BallG UpperTheory.V.Z.Tf.Orb in
theorem UpperTheory.ConvolutionTheory.Loc.nearUp :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure → ∃ ρ : ValueGroupWithZero k, 0 < ρ ∧ ∀ f ∈ SB (GL (Fin n) k), Function.support f ⊆ ball n ρ →
        ∃ φ ∈ SB (GL (Fin n) E), Match σ μE μk φ f := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk
  classical
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨hc, -, hb⟩ := bridge k E σ
  have hj := (hb n).2.2.2.1
  obtain ⟨_, _, _, -⟩ := gLTop E n
  obtain ⟨_, _, _, -⟩ := gLTop k n
  have hθ : Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E) := ((extCont k E).2.2 n).2 σ
  obtain ⟨r, hr0, hr⟩ := exists_radius (w := valuation E (Module.finrank k E : E))
    ((Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hc.pos.ne'))
  have hr1 : r < 1 := hr.trans_le (valuation_natCast_le_one (E := E) (Module.finrank k E))
  have hs0 : r * valuation E (Module.finrank k E : E) ≠ 0 := (mul_pos hr0 (hr0.trans hr)).ne'
  obtain ⟨ρ, hρ, hρb⟩ := small (k := k) (n := n) hs0
  refine ⟨ρ, hρ, fun f hf hs => ?_⟩
  set K := BallG.ballSub n r hr1 with hK
  have hKo : IsOpen (K : Set (GL (Fin n) E)) := isOpen_ball hr0.ne'
  have hKc : IsCompact (K : Set (GL (Fin n) E)) := isCompact_ball hr1
  set K' : Subgroup (GL (Fin n) k) := K.comap (incl : GL (Fin n) k →* GL (Fin n) E) with hK'
  have hKo' : IsOpen (K' : Set (GL (Fin n) k)) := hKo.preimage hj.continuous
  have hKc' : IsCompact (K' : Set (GL (Fin n) k)) := hj.isCompact_preimage hKc
  set A : GL (Fin n) k → ℂ := fun u => ∫ κ in (K' : Set (GL (Fin n) k)), f (κ⁻¹ * u * id κ) ∂μk with hA
  have hAl : IsLocallyConstant A := avg_locConst μk continuous_id hKc' hKo'.measurableSet hf.1
  set c : ℂ := ((μE.real (K : Set (GL (Fin n) E)) : ℝ) : ℂ) with hcd
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hKo.measure_ne_zero μE ⟨1, one_mem _⟩, hKc.measure_ne_top⟩)
  let p : GL (Fin n) E × GL (Fin n) k → GL (Fin n) E := fun z => z.1⁻¹ * incl z.2 * sigmaGL σ z.1
  let U : Set (GL (Fin n) E × GL (Fin n) k) := (K : Set _) ×ˢ (K' : Set _)
  let a : GL (Fin n) E × GL (Fin n) k → ℂ := fun z => c⁻¹ * A (z.2 ^ Module.finrank k E)
  let φ : GL (Fin n) E → ℂ := fun g => if h : ∃ z ∈ U, p z = g then a h.choose else 0
  have wd : ∀ z ∈ U, ∀ z' ∈ U, p z = p z' → a z = a z' := by
    rintro ⟨κ, u⟩ ⟨hκ, hu⟩ ⟨κ', u'⟩ ⟨hκ', hu'⟩ e
    have e1 : (κ * κ'⁻¹)⁻¹ * incl u * sigmaGL σ (κ * κ'⁻¹) = incl u' := by
      rw [map_mul, map_inv]
      calc _ = κ' * (κ⁻¹ * incl u * sigmaGL σ κ) * (sigmaGL σ κ')⁻¹ := by group
        _ = κ' * (κ'⁻¹ * incl u' * sigmaGL σ κ') * (sigmaGL σ κ')⁻¹ := congrArg (fun t => κ' * t * (sigmaGL σ κ')⁻¹) e
        _ = _ := by group
    obtain ⟨x, hx⟩ := ((hb n).2.2.1 hgen (κ * κ'⁻¹)).mp
      (rigidNear E n σ _ hc r hr _ hu _ hu' (sigma_incl σ u) (sigma_incl σ u') _ e1)
    have hxK : x ∈ K' := by
      show incl x ∈ K
      rw [hx]
      exact K.mul_mem hκ (K.inv_mem hκ')
    rw [← hx, sigma_incl, ← map_inv, ← map_mul, ← map_mul] at e1
    have e2 := incl_inj e1
    show c⁻¹ * A (u ^ _) = c⁻¹ * A (u' ^ _)
    congr 1
    have e3 : u' ^ Module.finrank k E = x⁻¹ * u ^ Module.finrank k E * x := by
      have := conj_pow (a := x⁻¹) (b := u) (i := Module.finrank k E)
      rw [inv_inv] at this
      rw [← e2, this]
    rw [hA, e3]
    refine (set_left μk K' hKo'.measurableSet (fun κ => f (κ⁻¹ * u ^ Module.finrank k E * id κ)) hxK).symm.trans ?_
    simp only [id, mul_inv_rev, mul_assoc]
  have h1 : ∀ z ∈ U, φ (p z) = a z := fun z hz => by
    have h : ∃ z' ∈ U, p z' = p z := ⟨z, hz, rfl⟩
    simp only [φ, dif_pos h]
    exact wd _ h.choose_spec.1 _ hz h.choose_spec.2
  have h2 : ∀ g, g ∉ p '' U → φ g = 0 := fun g h => dif_neg h
  have ho : IsOpen (p '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨⟨κ, u⟩, ⟨hκ, hu⟩, rfl⟩
    have hO : IsOpen ((fun g => (incl u)⁻¹ * κ * g * (sigmaGL σ κ)⁻¹) ⁻¹' ball n (r * valuation E (Module.finrank k E : E))) :=
      (isOpen_ball hs0).preimage (by fun_prop)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) fun g hg => ?_
    · have : (incl u)⁻¹ * κ * p (κ, u) * (sigmaGL σ κ)⁻¹ = 1 := by simp only [p]; group
      rw [Set.mem_preimage, this]
      exact fun i j => by simp
    · obtain ⟨κ', hκ', u', hu', hf', e⟩ := openNear E n σ _ hc r r hr le_rfl (incl u) hu (sigma_incl σ u) _ hg
      obtain ⟨u', rfl⟩ := ((hb n).2.2.1 hgen u').mp hf'
      refine ⟨(κ' * κ, u * u'), ⟨K.mul_mem hκ' hκ, K'.mul_mem hu hu'⟩, ?_⟩
      change _ = κ'⁻¹ * _ * sigmaGL σ κ' at e
      simp only [p, map_mul]
      calc _ = κ⁻¹ * (κ'⁻¹ * (incl u * incl u') * sigmaGL σ κ') * sigmaGL σ κ := by group
        _ = _ := by rw [← e]; group
  have hφ : φ ∈ SB (GL (Fin n) E) := sb_of_push (hKc.prod hKc') (p := p) (by have := hj.continuous; fun_prop) ho (a := a)
    ((hAl.comp_continuous (f := fun z : GL (Fin n) E × GL (Fin n) k => z.2 ^ Module.finrank k E) (by fun_prop)).comp fun z => c⁻¹ * z) h1 h2
  refine ⟨φ, hφ, nearCore k E σ hgen n μE μk hμE hμk r hr K rfl hKo hKc φ hφ f hf (fun g hg => ?_) (fun g hg => ?_) fun u hu => ?_⟩
  · by_contra h
    refine hg (h2 g ?_)
    rintro ⟨⟨κ, u⟩, ⟨hκ, hu⟩, rfl⟩
    exact h ⟨κ, hκ, u, hu, rfl⟩
  · obtain ⟨u, hu, hf', huq⟩ := exists_fixed_root hc.isom hr (hρb g (hs hg)) (sigma_incl σ g)
    obtain ⟨u, rfl⟩ := ((hb n).2.2.1 hgen u).mp hf'
    exact ⟨u, hu, incl_inj (by rw [map_pow, huq])⟩
  · rw [setIntegral_congr_fun (μ := μE) hKo.measurableSet (g := fun _ => c⁻¹ * A (u ^ Module.finrank k E))
      (fun κ hκ => h1 (κ, u) ⟨hκ, hu⟩), setIntegral_const, Complex.real_smul, ← hcd, mul_inv_cancel_left₀ hc0]
    rfl
end

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)

theorem UpperTheory.ConvolutionTheory.Loc.placeUp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) (CompletionsOver E v))] [BorelSpace (GL (Fin n) (CompletionsOver E v))]
        [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
        (mE : Measure (GL (Fin n) (CompletionsOver E v))) (mF : Measure (GL (Fin n) (v.adicCompletion F))), mE.IsHaarMeasure → mF.IsHaarMeasure →
      ∃ ρ : ValueGroupWithZero (v.adicCompletion F), 0 < ρ ∧ ∀ f ∈ SB (GL (Fin n) (v.adicCompletion F)), Function.support f ⊆ ball n ρ →
        ∃ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), PositivityTheory.Rg.Tf.Geo.Match (incFin E v) (galFin σ v) (Module.finrank F E) mE mF 1 (fun g => φ (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g)) f := by
  intro F E _ _ _ _ _ _ σ hσ v w hw n _ _ _ _ mE mF hE hF
  obtain ⟨iA, iV, iF, iG, s, hs, hrk, hinc, hgal, -⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hM⟩ := UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E σ hσ v w hw s hs hrk hinc hgal n mE mF hE hF
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨ρ, hρ, h⟩ := UpperTheory.ConvolutionTheory.Loc.nearUp (v.adicCompletion F) (w.1.adicCompletion E) s hs n _ mF hH hF
  refine ⟨ρ, hρ, fun f hf hsup => ?_⟩
  obtain ⟨φ, hφ, hm⟩ := h f hf hsup
  exact ⟨φ, hφ, hM φ hφ f hf hm⟩
