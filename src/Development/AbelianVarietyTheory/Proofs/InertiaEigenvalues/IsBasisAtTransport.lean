module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatIso

open MvPolynomial

theorem mem_localization_comap_iff {R R' W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R' W'] (φ : R ≃+* R') (f : W → W') (hf : ∀ (r : R) x, f (r • x) = φ r • f x)
    (p : Ideal R') [p.IsPrime] (L : Submodule R W) (L' : Submodule R' W') (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ (p.comap (φ : R →+* R')) L ↔ f x ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  show (∃ s ∈ (p.comap (φ : R →+* R')).primeCompl, s • x ∈ L) ↔ ∃ s ∈ p.primeCompl, s • f x ∈ L'
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨φ s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      exact hs
    · rw [← hf]; exact (hL _).2 h
  · rintro ⟨s, hs, h⟩
    refine ⟨φ.symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff] at hs ⊢
      rw [Ideal.mem_comap]
      simpa using hs
    · rw [← hL, hf, RingEquiv.apply_symm_apply]; exact h

section Fields

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K' ≃+* K)

abbrev vmE (n : ℕ) : (Fin n → K') ≃+ (Fin n → K) := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vmE_apply (n : ℕ) (x : Fin n → K') (a : Fin n) : vmE e n x a = e (x a) := rfl

theorem vmE_smul (n : ℕ) (r : 𝓞 K') (x : Fin n → K') :
    vmE e n (r • x) = RingOfIntegers.mapRingEquiv e r • vmE e n x :=
  funext fun i => GlobalTheory.IdealTransport.map_smul_int e r (x i)

theorem mem_span_vmE_iff {n : ℕ} (S : Set (Fin n → K')) (x : Fin n → K') :
    vmE e n x ∈ Submodule.span (𝓞 K) (vmE e n '' S) ↔ x ∈ Submodule.span (𝓞 K') S := by
  rw [← GlobalTheory.IdealTransport.span_image_span (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    GlobalTheory.IdealTransport.mem_span_image (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n),
    AddEquiv.symm_apply_apply]

theorem mem_tauLat_iff {E : Type} [Field E] [NumberField E] {ι : Type} {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (τ : ι)
    (M : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → K') :
    vmE e n x ∈ tauLat emb2 τ M ↔ x ∈ tauLat emb τ M := by
  have h2 : tauLat emb2 τ M =
      Submodule.span (𝓞 K) (vmE e n '' ((fun (y : Fin n → E) (a : Fin n) => emb τ (y a)) '' (M : Set (Fin n → E)))) := by
    rw [Set.image_image]
    unfold tauLat
    congr 1
    refine Set.image_congr fun y _ => funext fun a => ?_
    rw [h]; rfl
  rw [h2, mem_span_vmE_iff]
  rfl

theorem mem_dualFr' {F : Type} [Field F] [NumberField F] {n : ℕ} (L : Submodule (𝓞 F) (Fin n → F)) (y : Fin n → F) :
    y ∈ dualFr L ↔ ∀ x ∈ L, y ⬝ᵥ x ∈ (1 : Submodule (𝓞 F) F) := Iff.rfl

theorem map_mem_one_iff (a : K') : e a ∈ (1 : Submodule (𝓞 K) K) ↔ a ∈ (1 : Submodule (𝓞 K') K') := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(RingOfIntegers.mapRingEquiv e).symm r, e.injective ?_⟩
    rw [← hr]
    change e (e.symm (r : K)) = (r : K)
    exact e.apply_symm_apply _
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem mem_dualFr_iff {n : ℕ} (L : Submodule (𝓞 K') (Fin n → K')) (L2 : Submodule (𝓞 K) (Fin n → K))
    (hL : ∀ x, vmE e n x ∈ L2 ↔ x ∈ L) (y : Fin n → K') : vmE e n y ∈ dualFr L2 ↔ y ∈ dualFr L := by
  have hd : ∀ x : Fin n → K', vmE e n y ⬝ᵥ vmE e n x = e (y ⬝ᵥ x) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul, vmE_apply]
  rw [mem_dualFr', mem_dualFr']
  constructor
  · intro hy x hx
    rw [← map_mem_one_iff e, ← hd]
    exact hy _ ((hL x).2 hx)
  · intro hy x2 hx2
    obtain ⟨x, rfl⟩ := (vmE e n).surjective x2
    rw [hd, map_mem_one_iff]
    exact hy x ((hL x).1 hx2)

theorem mem_colLat_iff {n : ℕ} (B : GL (Fin n) K) (x : Fin n → K') :
    vmE e n x ∈ colLat B ↔ x ∈ colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  have h : colLat B = Submodule.span (𝓞 K) (vmE e n '' Set.range fun j : Fin n => fun a : Fin n =>
      ((Matrix.GeneralLinearGroup.map e.symm.toRingHom B : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') a j) := by
    unfold colLat
    rw [← Set.range_comp]
    congr 1
    congr 1
    funext j a
    simp only [Function.comp_apply, vmE_apply]
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact (e.apply_symm_apply _).symm
  rw [h, mem_span_vmE_iff]
  unfold colLat
  rfl

theorem isBasisAt_transport {n : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K') (Fin n → K'))
    (M2 : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x, vmE e n x ∈ M2 ↔ x ∈ M) (B : GL (Fin n) K) (hB : IsBasisAt w M2 B) :
    IsBasisAt (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) M
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom B) := by
  unfold IsBasisAt at hB ⊢
  ext x
  have h1 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal M M2 hM x
  have h2 := mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (vmE e n) (vmE_smul e n) w.asIdeal
    (colLat (Matrix.GeneralLinearGroup.map e.symm.toRingHom B)) (colLat B) (mem_colLat_iff e B) x
  refine h1.trans (Iff.trans ?_ h2.symm)
  rw [hB]

theorem map_smul_int' {σ : Type} (r : 𝓞 K') (P : MvPolynomial σ K') :
    map e.toRingHom (r • P) = RingOfIntegers.mapRingEquiv e r • map e.toRingHom P :=
  GlobalTheory.IoExtend.map_smul_alg e.toRingHom (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (fun _ => rfl) r P

theorem map_symm_map {σ : Type} (P : MvPolynomial σ K') : map e.symm.toRingHom (map e.toRingHom P) = P := by
  rw [map_map]
  convert map_id P
  ext a
  simp

theorem mem_nabStd_iff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K' ι n) :
    map e.toRingHom F ∈ nabStd K lam ↔ F ∈ nabStd K' lam := by
  constructor
  · intro h
    have := GlobalTheory.IoExtend.map_mem_nabStd e.symm.toRingHom lam h
    rwa [map_symm_map] at this
  · intro h
    exact GlobalTheory.IoExtend.map_mem_nabStd e.toRingHom lam h

theorem map_mem_nabP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K') (Fin n → K')) (M2 : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ x, vmE e n x ∈ M2 τ ↔ x ∈ M τ) {F : Pol K' ι n} (hF : F ∈ nabP lam M) :
    map e.toRingHom F ∈ nabP lam M2 := by
  unfold nabP transLat at hF ⊢
  simp only [Submodule.mem_iInf] at hF ⊢
  intro w B hB
  let B' : ι → GL (Fin n) K' := fun τ => Matrix.GeneralLinearGroup.map e.symm.toRingHom (B τ)
  have h1 := hF (w.comap (RingOfIntegers.mapRingEquiv e : 𝓞 K' →+* 𝓞 K) (RingOfIntegers.mapRingEquiv e).surjective) B'
    (fun τ => isBasisAt_transport e w (M τ) (M2 τ) (hM τ) (B τ) (hB τ))
  rw [Submodule.mem_comap] at h1 ⊢
  have hinv : ∀ t, ((B⁻¹ t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((B'⁻¹ t : GL (Fin n) K') : Matrix (Fin n) (Fin n) K').map e.toRingHom := by
    intro t
    have : B'⁻¹ t = Matrix.GeneralLinearGroup.map e.symm.toRingHom ((B t)⁻¹) := by
      simp only [Pi.inv_apply, B', map_inv]
    rw [this]
    ext a b
    change _ = e (e.symm _)
    rw [e.apply_symm_apply]
    rfl
  have hact := GlobalTheory.IoExtend.polyAction_map e.toRingHom lam B'⁻¹ B⁻¹ hinv F
  have h2 := (mem_localization_comap_iff (RingOfIntegers.mapRingEquiv e) (map e.toRingHom) (map_smul_int' e) w.asIdeal
    (nabStd K' lam) (nabStd K lam) (mem_nabStd_iff e lam) _).1 h1
  change actP lam B⁻¹ (map e.toRingHom F) ∈ _
  rw [hact]
  exact h2

theorem map_mem_nabAtr {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K')
    (emb2 : ι → E →+* K) (h : ∀ τ, emb2 τ = e.toRingHom.comp (emb τ)) (lam : ι → DomWeight n)
    (M : Submodule (𝓞 E) (Fin n → E)) {F : VV K' lam} (hF : F ∈ nabAtr emb lam M) :
    (⟨map e.toRingHom F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ lam _ F.2⟩ : VV K lam) ∈ nabAtr emb2 lam M := by
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  exact map_mem_nabP e lam _ _ (fun τ x => mem_dualFr_iff e _ _ (fun y => mem_tauLat_iff e emb emb2 h τ M y) x) hF

end Fields

theorem coefLatFn_ringEquiv (D : D7) (n : ℕ) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K' ≃+* K) (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K')) (O : Subring ℂ) (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    coefLatFn (σ.comp e.toRingHom) emb O lam M = coefLatFn σ (fun τ => e.toRingHom.comp (emb τ)) O lam M := by
  have hc : ∀ (P : Pol K' D.what₂.Tau n) (x : GLR D n),
      coefFn σ lam (map e.toRingHom P) x = coefFn (σ.comp e.toRingHom) lam P x := by
    intro P x
    unfold coefFn
    rw [MvPolynomial.eval₂Hom_map_hom]
  apply le_antisymm
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨_, map_mem_nabAtr e emb _ (fun _ => rfl) lam M hF, funext fun x => (hc F.1 x).symm⟩
  · rw [coefLatFn, Submodule.span_le]
    rintro _ ⟨G, hG, rfl⟩
    have hG' := map_mem_nabAtr e.symm (fun τ => e.toRingHom.comp (emb τ)) emb
      (fun τ => by ext a; simp) lam M hG
    refine Submodule.subset_span ⟨_, hG', funext fun x => ?_⟩
    refine Eq.trans ?_ (hc _ x)
    change coefFn σ lam G.1 x = coefFn σ lam (map e.toRingHom (map e.symm.toRingHom G.1)) x
    rw [map_map]
    congr 2
    convert (map_id G.1).symm
    ext a
    simp

end GlobalTheory.CoefLatIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.IdemSumForm

open GlobalTheory.SplitScalar
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisL_commute_of {a : AE D} (ha : cA D a * a = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf a y) :
    Commute (heisL ψ S T x) (heisL ψ S T y) := by
  have add : ∀ {x y : WO S T}, IsHalf a x → IsHalf a y → heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y :=
    fun hx hy => LinearMap.ext fun f => heisO_add_of_orth ψ S T (symplO_eq_zero S T ha hx hy) f
  rw [Commute, SemiconjBy, ← add hx hy, ← add hy hx, add_comm]

theorem dual_half {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : IsHalf e y) (hyΛ : y ∉ Λ) :
    ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 := by
  rw [hd y (hfin y hy)] at hyΛ
  push Not at hyΛ
  obtain ⟨u, hu, h⟩ := hyΛ
  refine ⟨cA D e • u, hst u hu, isHalf_smul (by rw [← RingHom.map_mul, he1]) u, psi_skew_ne ?_⟩
  rwa [← symplO_smul, (isHalf_iff _ _).1 hy]

theorem count_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he2' : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he2]
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_of he2' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
        ((Commute.one_left _).smul_left _)
    · rintro _ ⟨y, hy, hyΛ, rfl⟩
      obtain ⟨l, hl, hl', hne⟩ := dual_half he1 hfin hd hst hy hyΛ
      refine ⟨_, ⟨l, hl, _, hl', hne, rfl⟩, ?_⟩
      rw [LinearMap.sub_apply, heisL_apply, heisO_comm, hfc l hl hl']
      exact sub_self _
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1},
          ∃ c : ℂ, c ≠ 0 ∧ B f = c • f := by
        intro B hB
        induction hB using Submonoid.closure_induction with
        | mem b hb =>
          obtain ⟨l, hl, z, hl', hz, rfl⟩ := hb
          refine ⟨1 - z, sub_ne_zero.2 hz.symm, ?_⟩
          rw [LinearMap.sub_apply, heisL_apply, hfc l hl hl', sub_smul, one_smul]
          rfl
        | one => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
        | mul x y _ _ hx hy =>
          obtain ⟨c, hc, hx⟩ := hx
          obtain ⟨d, hd, hy⟩ := hy
          exact ⟨d * c, mul_ne_zero hd hc, by rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul]⟩
      intro B hB
      obtain ⟨c, hc, h⟩ := this B hB
      rw [h]
      exact smul_ne_zero hc hf0
  obtain ⟨κ, hκ, hκ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(κ f)⁻¹ • κ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ], fun y hy => ?_⟩
  by_cases hyΛ : y ∈ Λ
  · rw [hfe y hyΛ hy, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ]
    exact zero_le_one
  · have : κ (heisO ψ S T y f) = 0 := by
      rw [← Submodule.mem_bot ℂ, ← hκ']
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hy, hyΛ, rfl⟩)
    rw [LinearMap.smul_apply, this, smul_zero]

theorem invariant_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := count_form he1 he2 hfin hd hst hf0 hfe hfc
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_of he2 (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (hfin y hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (hfin _ (isHalf_nsmul hy _)), sub_self]
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)},
          (∀ y, IsHalf e y → 0 ≤ κ (B (heisO ψ S T y f))) ∧ 0 < κ (B f) := by
        intro B hB
        induction hB using Submonoid.closure_induction_right with
        | one => exact ⟨hκ, by rw [Module.End.one_apply, hκ1]; exact zero_lt_one⟩
        | mul_right B _ g hg ih =>
          obtain ⟨y', N, hy', rfl⟩ := hg
          refine ⟨fun y hy => ?_, ?_⟩
          set_option synthInstance.maxHeartbeats 100000 in
            · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
              refine Finset.sum_nonneg fun k _ => ?_
              rw [heisL_apply, ← heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy' k) hy)]
              exact ih.1 _ (isHalf_add (isHalf_nsmul hy' k) hy)
          set_option synthInstance.maxHeartbeats 100000 in
            · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
              refine Finset.sum_pos' (fun k _ => ih.1 _ (isHalf_nsmul hy' k)) ⟨0, Finset.mem_range.2 N.succ_pos, ?_⟩
              rw [heisL_apply, zero_smul, heisO_zero]
              exact ih.2
      intro B hB h0
      have := (this B hB).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  obtain ⟨ℓ, hℓ, hℓ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨ℓ, hℓ, fun y hy φ hφ => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← Submodule.mem_bot ℂ, ← hℓ']
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, φ, hy, hφ, rfl⟩)

theorem fix_sum_smul {Λ : AddSubgroup (WO S T)} (hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) {ι : Type} [DecidableEq ι] (es : ι → AE D)
    {l : WO S T} (hl : l ∈ Λ) : ∀ s : Finset ι, (∀ P ∈ s, IsSplitIdem D (es P)) →
      (∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0) → heisO ψ S T ((∑ P ∈ s, es P) • l) f = f := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _; rw [Finset.sum_empty, zero_smul, heisO_zero]
  | insert a s ha ih =>
    intro hs ho
    have hs' : ∀ P ∈ s, IsSplitIdem D (es P) := fun P hP => hs P (Finset.mem_insert_of_mem hP)
    have ho' : ∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0 := fun P hP Q hQ =>
      ho P (Finset.mem_insert_of_mem hP) Q (Finset.mem_insert_of_mem hQ)
    have hsa := hs a (Finset.mem_insert_self a s)
    have horth : symplO S T (es a • l) ((∑ P ∈ s, es P) • l) = 0 := by
      rw [symplO_smul, smul_smul, Finset.mul_sum,
        Finset.sum_eq_zero fun Q hQ => ho a (Finset.mem_insert_self a s) Q (Finset.mem_insert_of_mem hQ),
        zero_smul, symplO_zero_right]
    rw [Finset.sum_insert ha, add_smul, heisO_add_of_orth ψ S T horth, ih hs' ho',
      hf.2 (es a) hsa _ (hΛ _ hsa.1 l hl) (isHalf_smul hsa.1 l)]

end GlobalTheory.LevelSeries.IdemSumForm

namespace GlobalTheory.LevelSeries

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm

theorem exists_invariant_form_idemSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨-, -, -, -, hΛV, hΛW, -, -, hψ, hvac⟩ := hP
  obtain ⟨⟨es, hes, rfl⟩, hTo⟩ := hT
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hΛV hΛW
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), a • u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hmul : ∀ P ∈ T, (∑ Q ∈ T, es Q) * es P = es P := by
    intro P hP
    rw [Finset.sum_mul, Finset.sum_eq_single_of_mem P hP]
    · exact (hes P hP).1.1
    · intro Q hQ hne
      exact GlobalTheory.Tow.idemAt_orth (hes Q hQ) (hes P hP) hne
  have hcross : ∀ P ∈ T, ∀ Q ∈ T, cA D (es P) * es Q = 0 := by
    intro P hP Q hQ
    rw [← hmul P hP, ← hmul Q hQ, RingHom.map_mul]
    calc cA D (∑ R ∈ T, es R) * cA D (es P) * ((∑ R ∈ T, es R) * es Q)
        = ((∑ R ∈ T, es R) * cA D (∑ R ∈ T, es R)) * (cA D (es P) * es Q) := by ring
      _ = 0 := by rw [hTo, zero_mul]
  have hsum1 : (∑ Q ∈ T, es Q) * (∑ Q ∈ T, es Q) = ∑ Q ∈ T, es Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hmul
  set eT := ∑ Q ∈ T, es Q with heT
  have hcsum : cA D eT = ∑ Q ∈ T, cA D (es Q) := map_sum _ _ _
  have hf0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hvac.norm.1
    have := hvac.norm.2 p hp
    simp [nrm2] at this
  have hfe : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf eT l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh]
    exact fix_sum_smul hΛ hvac.lat es hl T (fun P hP => (hes P hP).1) hcross
  have hfc : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf (cA D eT) l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh, hcsum]
    refine fix_sum_smul hΛ hvac.lat (fun Q => cA D (es Q)) hl T (fun P hP => isSplitIdem_conj (hes P hP).1) ?_
    intro P hP Q hQ
    rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hcross Q hQ P hP
  have hfin : ∀ u : WO V W, IsHalf (cA D eT) u → u.map (infPart D) = 0 := by
    intro u hu
    ext i j
    show infPart D (u i j) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu i j, RingHom.map_mul, hcsum, map_sum,
      Finset.sum_eq_zero fun Q hQ => infPart_splitIdem (isSplitIdem_conj (hes Q hQ).1), zero_mul]
  have he1 : cA D eT * cA D eT = cA D eT := by rw [← RingHom.map_mul, hsum1]
  have he2 : cA D (cA D eT) * cA D eT = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hTo]
  exact invariant_form he1 he2 hfin hd (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hΛ _ hsum1 u hu) hf0
    (fun l hl hlh => hfc l hl hlh) (fun l hl hlh => hfe l hl (by rwa [GlobalTheory.DualPairCheck.cA_cA] at hlh))

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZeroStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjHalfInvariant_form_idemSum_vacuum_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  first | exact @GlobalTheory.LevelSeries.exists_invariant_form_idemSum | exact GlobalTheory.LevelSeries.exists_invariant_form_idemSum | (intros; apply GlobalTheory.LevelSeries.exists_invariant_form_idemSum <;> assumption)
end
end
