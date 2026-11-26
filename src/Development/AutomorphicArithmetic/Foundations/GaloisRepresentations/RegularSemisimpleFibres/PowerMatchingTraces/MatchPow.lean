module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.SelmerRankBoundLaurent
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem norm_incl {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (x : (v.adicCompletion F)ˣ) :
    ‖completionMap v w.1 (x : v.adicCompletion F)‖ = ‖(x : v.adicCompletion F)‖ ^ Module.finrank F E := by
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  clear hw
  obtain ⟨w, hwv⟩ := w
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hwv
  haveI := hwv
  let y : (w.adicCompletion E)ˣ := Units.map (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).toMonoidHom x
  have hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x ^ Module.finrank F E := by
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    change Algebra.norm _ (algebraMap _ (w.adicCompletion E) (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F)) = _
    rw [Algebra.norm_algebraMap, hrk, Units.val_pow_eq_pow_val]
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h2] at h3
  have h4 := congrArg Subtype.val h3
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding,
    Units.val_pow_eq_pow_val, norm_pow] at h4
  exact h4.symm

private theorem norm_gal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (y : CompletionsOver E v) : ‖galFin σ v y w‖ = ‖y w‖ := by
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have h0 : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 hfix x).symm
      · exact ((galEquiv v σ w.1 w.1 hfix).commutes a).symm
  rw [h0]
  have hk : ∀ x : E, ‖algebraMap E (w.1.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
    intro x
    have key : ∀ u : HeightOneSpectrum (𝓞 E), u = σ • w.1 →
        ‖algebraMap E (u.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
      rintro _ rfl
      exact norm_algebraMap_smul σ w.1 x
    exact key _ hfix
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
    (continuous_norm.comp (continuous_galEquiv v σ w.1 w.1 hfix)) continuous_norm ?_) (y w)
  funext x
  simp only [Function.comp_apply, galEquiv_algebraMap, hk]

private theorem quotInt_mul_const {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (Φ : X → ℂ) (c : ℂ) :
    quotInt μ u j ν (fun x => Φ x * c) = quotInt μ u j ν Φ * c := by
  unfold quotInt
  split_ifs with h
  · rw [← integral_mul_const]
    congr 1
    funext x
    ring
  · simp

private theorem det_mapGL {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (f : R →+* S) (g : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (mapGL n f g) : Sˣ) : S) = f ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) :=
  (RingHom.map_det f g.val).symm

private theorem chiAt_conj {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) (x γ : Gw n v) :
    chiAt n χ v (x⁻¹ * γ * x) = chiAt n χ v γ := by
  unfold chiAt
  simp only [map_mul, map_inv]
  rw [mul_comm _ (χ.loc v (Matrix.GeneralLinearGroup.det x)), mul_inv_cancel_left]

private theorem hom_twNorm {G : Type*} [Group G] (N : G → ℝ) (h0 : N 1 = 1) (h1 : ∀ a b, N (a * b) = N a * N b)
    (θ : Monoid.End G) (hθ : ∀ y, N (θ y) = N y) (m : ℕ) (δ : G) :
    N (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = N δ ^ m := by
  have hp : ∀ (k : ℕ) (y : G), N ((θ ^ k) y) = N y := by
    intro k y
    induction k with
    | zero => rfl
    | succ k ih => rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', hθ, ih]
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, h1, ih, hp, pow_succ]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.G.matchPow :
    UpperTheory.Gal.InertialTypesAlt.G.MatchPow := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn z χ χ' h h' v w hw

  let N : GL (Fin n) (CompletionsOver E v) → ℝ := fun g =>
    ‖((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w‖
  have hN0 : N 1 = 1 := by simp [N]
  have hN1 : ∀ a b, N (a * b) = N a * N b := fun a b => by simp [N]
  have hNθ : ∀ y, N (mapGL n (galFin σ v) y) = N y := fun y => by
    simp only [N]
    rw [det_mapGL, norm_gal σ w hw]
  have hχ' : ∀ g, chiAt n χ' w.1 (GM.cmp w g) = ((N g : ℝ) : ℂ) ^ z := fun g => by
    unfold chiAt
    rw [pow_loc h']
    have e : ((Matrix.GeneralLinearGroup.det (GM.cmp w g) : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
        ((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w :=
      det_mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g
    rw [e]
  have hθ : ∀ x, chiAt n χ' w.1 (GM.cmp w (mapGL n (galFin σ v) x)) = chiAt n χ' w.1 (GM.cmp w x) := fun x => by
    rw [hχ', hχ', hNθ]
  have hsurj : ∀ g : Gw n w.1, ∃ g₀, GM.cmp w g₀ = g := fun g => by
    obtain ⟨⟨e, he⟩, -, -⟩ := cmpIso F E n v w hw
    exact ⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩
  have hl : Module.finrank F E ≠ 0 := hp.ne_zero

  have hnorm : ∀ (γ : Gw n v) (δ : GL (Fin n) (CompletionsOver E v)),
      PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ →
      chiAt n χ' w.1 (GM.cmp w δ) = chiAt n χ v γ := fun γ δ hδ => by
    have h1 := hom_twNorm N hN0 hN1 (mapGL n (galFin σ v)) hNθ (Module.finrank F E) δ
    rw [hδ] at h1
    have h2 : N (mapGL n (incFin E v) γ) =
        ‖((Matrix.GeneralLinearGroup.det γ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ Module.finrank F E := by
      simp only [N]
      rw [det_mapGL]
      exact norm_incl w hw _
    rw [h2] at h1
    have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hl).1 h1
    rw [hχ']
    unfold chiAt
    rw [pow_loc h, h3]
  refine ⟨fun s hs g => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hsurj g
    rw [← hs g₀, hθ]
  intro c φ f hm _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
  obtain ⟨ha, hb⟩ := hm mE mF hE hF h1 h2 γ hγ ν hν
  have horb : orb mF γ ν (fun g => f g * chiAt n χ v g) = orb mF γ ν f * chiAt n χ v γ := by
    unfold orb
    rw [← quotInt_mul_const]
    congr 1
    funext x
    beta_reduce
    rw [chiAt_conj]
  refine ⟨fun δ hδ => ?_, fun hne => ?_⟩
  · have htw : twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g) * chiAt n χ' w.1 (GM.cmp w g)) =
        twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g)) * chiAt n χ' w.1 (GM.cmp w δ) := by
      unfold twOrb
      rw [← quotInt_mul_const]
      congr 1
      funext x
      beta_reduce
      have e : N x⁻¹ * N x = 1 := by rw [← hN1, inv_mul_cancel, hN0]
      have hc : N (x⁻¹ * δ * mapGL n (galFin σ v) x) = N δ := by
        rw [hN1, hN1, hNθ]
        linear_combination (N δ) * e
      rw [hχ' (x⁻¹ * δ * mapGL n (galFin σ v) x), hc, ← hχ' δ]
    rw [htw, horb, ha δ hδ, hnorm γ δ hδ]
    ring
  · rw [horb, hb hne, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCutAlt
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormOpen
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.normOpen :
    UpperTheory.Gal.InertialTypesAlt.G.NormOpen := by
  intro F E _ _ _ _ _ _ _ _ σ _ hp n _ v
  obtain ⟨η, hη⟩ := UpperTheory.ConvolutionTheory.R.classChar2 F E hp
  have hpow := (UpperTheory.ConvolutionTheory.R.normCharPow_holds F E hp η hη).1
  have key : ∀ g : Gw n v, g ∈ normSet E n v ↔ chiAt n η v g = 1 := by
    intro g
    constructor
    · intro h
      have h1 := h η hη.1
      simp only [chiAt, h1, Units.val_one]
    · intro h χ hχ
      obtain ⟨j, -, -, rfl⟩ := hpow χ hχ
      have h1 : η.loc v (Matrix.GeneralLinearGroup.det g) = 1 := Units.ext h
      show (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = 1
      have h2 : (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = (η.loc v (Matrix.GeneralLinearGroup.det g)) ^ j := rfl
      rw [h2, h1, one_pow]
  refine ⟨?_, fun γ x => ?_⟩
  · have hs : normSet E n v = chiAt n η v ⁻¹' {1} := Set.ext fun g => key g
    rw [hs]
    exact ((UpperTheory.Gal.InertialTypesAlt.G.chiBasic F n η v).1).isClopen_fiber 1
  · have hd : Matrix.GeneralLinearGroup.det (x⁻¹ * γ * x) = Matrix.GeneralLinearGroup.det γ := by
      rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det γ), mul_assoc, inv_mul_cancel, mul_one]
    rw [key, key]
    simp only [chiAt, hd]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormLoc
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.NL

open GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem atFin_galAd (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x => rw [galAd, galOf_tmul, tensor_atFin, tensor_atFin, galFin, galOf_tmul]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

private theorem atFin_adeleMap (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem galAd_eq_smul (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : galAd σ a = σ • a := by
  have h1 : (MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ) = Formalism.L2.Host.CT.adMap σ.toRingEquiv :=
    UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv _ (continuous_const_smul σ) fun x => smul_algebraMap σ x
  rw [UpperTheory.ConvolutionTheory.K.galAdEq, ← h1]
  rfl

private theorem atFin_pow_smul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (a : 𝔸[E]) :
    atFin v ((σ ^ i) • a) = (galFin σ v)^[i] (atFin v a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_smul, ← galAd_eq_smul, atFin_galAd, ih, Function.iterate_succ_apply']

private theorem prod_gal [IsGalois F E] {M : Type*} [CommMonoid M] (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (f : (E ≃ₐ[F] E) → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank F E), f (σ ^ i) := by
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf (by simpa [ho] using i.2) (by simpa [ho] using j.2) h)
  have hbij : Function.Bijective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [← Fin.prod_univ_eq_prod_range (fun i => f (σ ^ i))]
  exact (Fintype.prod_bijective _ hbij _ _ fun _ => rfl).symm

private theorem det_iter {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (i : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (θ^[i] δ) : Rˣ) : R) = s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hθ]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]

private theorem det_twNorm {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (l : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (twNorm θ l δ) : Rˣ) : R) =
      ∏ i ∈ Finset.range l, s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [twNorm_succ, map_mul, Units.val_mul, ih, Finset.prod_range_succ, Monoid.End.coe_pow, det_iter s n θ hθ]

end

end UpperTheory.Gal.InertialTypesAlt.G.NL

open UpperTheory.Gal.InertialTypesAlt.G.NL GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc in
open scoped NumberField.AdeleRing in
theorem UpperTheory.Gal.InertialTypesAlt.G.normLoc :
    UpperTheory.Gal.InertialTypesAlt.G.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v γ δ h η hη
  set d : (CompletionsOver E v)ˣ := Matrix.GeneralLinearGroup.det δ with hd
  let du : ∀ u : PlacesOver E v, (u.1.adicCompletion E)ˣ := fun u =>
    Units.map (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) u).toMonoidHom d
  let x : IdeleGroup E := ∏ u : PlacesOver E v, IdeleGroup.finiteEmbedding u.1 (du u)
  have hc : ∀ u : PlacesOver E v, ∃ c : (v.adicCompletion F)ˣ,
      ideleNorm F E (IdeleGroup.finiteEmbedding u.1 (du u)) = IdeleGroup.finiteEmbedding v c := by
    rintro ⟨w, hw⟩
    obtain rfl : below F w = v := (below_eq_iff w v).2 hw
    exact ⟨_, ideleNorm_finiteEmbedding w _⟩
  choose c hc using hc
  have hx : ideleNorm F E x = IdeleGroup.finiteEmbedding v (∏ u, c u) := by
    simp only [x, map_prod, hc]
  have hat : atFin v (x : 𝔸[E]) = (d : CompletionsOver E v) := by
    funext w
    change (((IdeleGroup.finiteProj w.1 x : (w.1.adicCompletion E)ˣ)) : w.1.adicCompletion E) = _
    have : IdeleGroup.finiteProj w.1 x = du w := by
      simp only [x, map_prod]
      rw [Finset.prod_eq_single w (fun b _ hb => IdeleGroup.finiteProj_finiteEmbedding_of_ne
        (fun e => hb (Subtype.ext e.symm)) _) (by simp), IdeleGroup.finiteProj_finiteEmbedding]
    rw [this]
    rfl
  have hy : ∏ u, c u = Matrix.GeneralLinearGroup.det γ := by
    haveI := (GroundTheory.Global.nonempty_placesOver E v)
    apply Units.ext
    apply (incFin E v).injective
    have h1 : incFin E v ((∏ u, c u : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        atFin v (adeleMap F E ((ideleNorm F E x : IdeleGroup F) : 𝔸[F])) := by
      rw [hx, atFin_adeleMap]
      congr 1
      exact (congrArg Units.val (IdeleGroup.finiteProj_finiteEmbedding v _)).symm
    rw [h1, coe_ideleNorm, adeleMap_norm, map_prod, prod_gal σ hσ]
    simp only [atFin_pow_smul, hat]
    rw [hd, ← det_twNorm (galFin σ v) n _ (fun _ => rfl), h]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη x
  rw [hx, hy] at h3
  exact h3
end

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.matchCut :
    UpperTheory.Gal.InertialTypesAlt.G.MatchCut := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn v c φ f
  have hO := normOpen F E σ hσ hp n hn v
  refine ⟨?_, ?_⟩
  · intro hM _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
    obtain ⟨ha, hb⟩ := hM mE mF hE hF h1 h2 γ hγ ν hν
    by_cases hg : γ ∈ normSet E n v
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = orb mF γ ν f := by
        unfold orb
        congr 1
        funext x
        exact Set.indicator_of_mem ((hO.2 γ x).2 hg) f
      rw [horb]
      exact ⟨ha, hb⟩
    · have horb : orb mF γ ν ((normSet E n v).indicator f) = 0 := by
        have hz : (fun x => (normSet E n v).indicator f (x⁻¹ * γ * x)) = fun _ => (0 : ℂ) := by
          funext x
          exact Set.indicator_of_notMem (fun h => hg ((hO.2 γ x).1 h)) f
        unfold orb quotInt
        rw [hz]
        simp
      exact ⟨fun δ hδ => absurd (normLoc F E σ hσ hp n hn v γ δ hδ) hg, fun _ => horb⟩
  · intro hT
    obtain ⟨h1, h2⟩ : IsLocallyConstant f ∧ HasCompactSupport f := hT
    exact ⟨(LocallyConstant.indicator (⟨f, h1⟩ : LocallyConstant _ ℂ) hO.1).isLocallyConstant,
      h2.mono fun x hx hx0 => hx (Set.indicator_apply_eq_zero.2 fun _ => hx0)⟩
end
