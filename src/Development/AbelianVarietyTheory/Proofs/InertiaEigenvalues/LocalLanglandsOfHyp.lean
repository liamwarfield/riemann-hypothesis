module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglandsBridge

theorem localLanglandsGL_of_depthZero_zelevinsky_bernstein : LocalLanglandsExists → LocalConverseGL → DepthZeroCuspidalLL → DepthZeroInduction →
    BrauerDegreeZero → ChevalleyUnits → GlobalArtinReciprocity → LanglandsExhaustionGL → LanglandsMultisegments →
    StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → LocalLanglandsGL := by
  intro hEx hConv hDep hInd hBr hChev hArt hExh hMult hCos hZel hGeo hBZ
  have hRec := GlobalTheory.T.rec_of_rec_literal hDep hInd hExh hMult hCos hZel hGeo hBZ
  have hComp := GlobalTheory.T.local_langlands_transport hArt hChev hBr hEx hConv hExh hBZ
  refine ⟨?_, ?_⟩
  · intro E Ω _ _ _ _ _ A w h
    obtain ⟨rc, hrc⟩ := hEx E Ω A w h
    refine ⟨rc, hRec E Ω A w h rc hrc, ?_⟩
    intro rc' hrc'
    funext x
    obtain ⟨n, c⟩ := x
    have hC := hComp E Ω A w h E Ω A w h rc' rc hrc'.toLit hrc
      (RingEquiv.refl Ω) (RingHom.id E) (RingEquiv.refl _) (fun _ => Iff.rfl) (fun _ => rfl) continuous_id
      (fun _ => rfl) n c.rep c.rep (LinearEquiv.refl ℂ _) (fun g v => by
        have hg : GeneralLinearGroup.map (RingEquiv.refl (w.adicCompletion E)).toRingHom g = g :=
          Units.ext (Matrix.ext fun _ _ => rfl)
        rw [hg]; rfl)
    obtain ⟨b, b', hb, hb', hN, hρ⟩ := hC
    have hbb : WD.mk b = WD.mk b' := WD.sound ⟨LinearEquiv.refl ℂ _, fun σ v => by
      simp only [LinearEquiv.refl_apply]; rw [hρ σ σ (fun _ => rfl)], fun v => by
      simp only [LinearEquiv.refl_apply]; rw [hN]⟩
    have hx : (⟨n, c⟩ : IrrGL (k := w.adicCompletion E)) = cls c.rep := congrArg (Sigma.mk _) c.cl_rep.symm
    rw [hx, ← hb, ← hb', hbb]
  · intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc' hrc hrc'
    exact hComp E Ω A w h E' Ω' A' w' h' rc rc' hrc.toLit hrc'.toLit

end GlobalTheory.LocLanglandsBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped TensorProduct

namespace GlobalTheory.RedHalfDrop

variable {D : D7}

theorem toEAf_cA_sig (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul y e => rfl

theorem int_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (idemAt PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hu, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (h.isIdemAt hPP)
  exact hu

theorem int_cA_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (cA D (idemAt PP)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [toEAf_cA_sig]
  exact GlobalTheory.ResConjPlace.conj_mem_int _ (int_idemAt h hPP)

theorem resS_eq_zero_of_mul {e a : AE D} {PP : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : e * a = 0) :
    resS D.host.F PP ⟨toEAf D a, ha⟩ = 0 := by
  obtain ⟨hu, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hm : (⟨toEAf D e, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
      ⟨toEAf D a, ha⟩ = 0 :=
    Subtype.ext (by show toEAf D e * toEAf D a = 0; rw [← map_mul, h0, map_zero])
  have h2 := congrArg (resS D.host.F PP) hm
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem subring_hom_dite_sub_mul_eq_of_kernel {R k : Type} [CommRing R] [CommRing k] (O : Subring R) (f : O →+* k) (x c : R) (hx : x ∈ O)
    (hc : c ∈ O) (h0 : f ⟨c, hc⟩ = 0) [Decidable (x - c * x ∈ O)] [Decidable (x ∈ O)] :
    (if h : x - c * x ∈ O then f ⟨x - c * x, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hm : x - c * x ∈ O := sub_mem hx (mul_mem hc hx)
  rw [dite_eq_left hm, dite_eq_left hx]
  have e : (⟨x - c * x, hm⟩ : O) = ⟨x, hx⟩ - ⟨c, hc⟩ * ⟨x, hx⟩ := rfl
  rw [e, map_sub, map_mul, h0, zero_mul, sub_zero]

theorem redM_sub_smul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) {c : EAf D}
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    redM PP (N - c • N) = redM PP N := by
  ext i j
  unfold redM
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact subring_hom_dite_sub_mul_eq_of_kernel _ (resS D.host.F PP) _ _ (hN i j) hc h0

theorem frMapO_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  unfold frMapAdj
  have h1 : ((e • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      cA D e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  have h2 : ∀ M : Matrix (Fin S.rank) (Fin T.rank) (AE D),
      (cA D e • M).map (toEAf D) = toEAf D (cA D e) • M.map (toEAf D) :=
    fun M => Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem redM_drop : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  intro D S T βS βT Pg Qa Qb hP hQ x hx h1 h2
  obtain ⟨P, hPg, hQa, hS⟩ := hP.split
  have hab : halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
    unfold halfIdem idem
    rw [← Finset.sum_sdiff hQ]
    ring
  have hxx : (halfIdem Pg Qb + idem (Qa \ Qb)) • x = x := by
    rw [← hab]
    ext i j
    exact hx i j
  have hsub : ∀ P' ∈ Qa \ Qb, P' ∈ P := fun P' hP' => hQa (Finset.sdiff_subset hP')
  constructor
  · intro PP hPP
    have e1 := frMapAdj_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), map_add (f := _), add_smul] at e1
    have e2 : frMapAdj S T βS βT (halfIdem Pg Qb • x) =
        frMapAdj S T βS βT x - toEAf D (cA D (idem (Qa \ Qb))) • frMapAdj S T βS βT x := by
      rw [frMapAdj_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (cA D (idem (Qa \ Qb))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      exact sum_mem fun P' hP' => int_cA_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hPg hPP)) hint (by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_conj (hPg hPP) (hsub P' hP'))
    rw [e2, redM_sub_smul PP h1 hint hz]
  · intro PP hPP
    have e1 := frMapO_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add (f := _), add_smul] at e1
    have e2 : frMapO S T βS βT (halfIdem Pg Qb • x) =
        frMapO S T βS βT x - toEAf D (idem (Qa \ Qb)) • frMapO S T βS βT x := by
      rw [frMapO_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (idem (Qa \ Qb)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact sum_mem fun P' hP' => int_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hQa (hQ hPP))) hint (by
      unfold idem
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_eq_zero (hQa (hQ hPP)) (hsub P' hP')
        fun e => (Finset.mem_sdiff.1 hP').2 (e ▸ hPP))
    rw [e2, redM_sub_smul PP h2 hint hz]

end GlobalTheory.RedHalfDrop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixReduction_eq_of_halfIdempotent_subset : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  first | exact @GlobalTheory.RedHalfDrop.redM_drop | exact GlobalTheory.RedHalfDrop.redM_drop | (intros; apply GlobalTheory.RedHalfDrop.redM_drop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.ExportSeries

namespace RestrictHalfModel

variable {D : D7} {m n : ℕ}

theorem isHalf_iff' (e : AE D) (u : Mx D m n) : IsHalf e u ↔ e • u = u := GlobalTheory.SplitScalar.isHalf_iff e u

theorem isHalf_smul {e : AE D} (he : e * e = e) (u : Mx D m n) : IsHalf e (e • u) := by
  rw [isHalf_iff', smul_smul, he]

theorem halfInd_smul_congr {e : AE D} (he : e * e = e) (Λ : AddSubgroup (Mx D m n)) {z t : Mx D m n}
    (h : e • z - e • t ∈ Λ) : halfInd e Λ (e • z) = halfInd e Λ (e • t) := by
  unfold halfInd
  have hz := isHalf_smul he z
  have ht := isHalf_smul he t
  by_cases h1 : e • t ∈ Λ
  · rw [if_pos ⟨by simpa using Λ.add_mem h h1, hz⟩, if_pos ⟨h1, ht⟩]
  · rw [if_neg fun h2 => h1 (by simpa using Λ.sub_mem h2.1 h), if_neg fun h2 => h1 h2.1]

theorem smul_of_half {a' b : AE D} (hab : a' * b = 0) {x : Mx D m n} (hx : IsHalf a' x) :
    b • x = 0 ∧ (a' + b) • x = x := by
  rw [isHalf_iff'] at hx
  have h0 : b • x = 0 := by
    rw [← hx, smul_smul, mul_comm, hab, zero_smul]
  exact ⟨h0, by rw [add_smul, hx, h0, add_zero]⟩

theorem isHalf_add_iff {e : AE D} {t u : Mx D m n} (hu : e • u = u) : IsHalf e (t + u) ↔ IsHalf e t := by
  rw [isHalf_iff', isHalf_iff', smul_add, hu, add_left_inj]

theorem isSBHalf_restrictHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ) :
    IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [restrictHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [restrictHalf_apply]
    have e1 : a' • (t + k • u) = a' • t + k • (a' • u) := by rw [smul_add, smul_comm]
    have e2 : (a' + b) • (k • u) = k • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' u hu) (isHalf_smul ha' u), halfInd_smul_congr hb Λ (z := t + k • u) (t := t) (by
      rw [smul_add, add_sub_cancel_left, smul_comm]
      exact Λ.nsmul_mem (hΛ b hb u hu) k)]
    simp only [isHalf_add_iff e2]
  · rw [restrictHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : halfInd b Λ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    have h2' : b • t ∈ Λ := by
      unfold halfInd at h2
      by_contra h
      exact h2 (if_neg fun h' => h h'.1)
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add]
    exact Λ.add_mem (hlat _ h1) (Λ.nsmul_mem h2' k)

end RestrictHalfModel


open RestrictHalfModel in
theorem isPlaceModel_comp_restrictHalf : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  intro D S T ψ Λ f₀ a' b T₀ ha' hb hab hΛ hT
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (restrictHalf a' b Λ Φ) :=
    fun Φ hΦ => isSBHalf_restrictHalf ha' hb hΛ hΦ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : restrictHalf a' b Λ (fun t => Φ (t + x)) = fun t => restrictHalf a' b Λ Φ (t + x) := by
      funext z
      simp only [restrictHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : restrictHalf a' b Λ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * restrictHalf a' b Λ Φ t := by
      funext z
      simp only [restrictHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · have e : restrictHalf a' b Λ ((1 : ℂ) • halfInd a' Λ) = (1 : ℂ) • halfInd (a' + b) Λ := by
      funext t
      simp only [one_smul, restrictHalf_apply]
      unfold halfInd
      have i1 := isHalf_smul ha' t
      have i2 := isHalf_smul hb t
      by_cases hat : IsHalf (a' + b) t
      · have ht' : t = a' • t + b • t := by rw [← add_smul]; exact ((isHalf_iff' _ _).1 hat).symm
        by_cases ht : t ∈ Λ
        · rw [if_pos ⟨hΛ a' ha' t ht, i1⟩, if_pos ⟨hΛ b hb t ht, i2⟩, if_pos hat, if_pos ⟨ht, hat⟩]
          ring
        · rw [if_neg (show ¬ (t ∈ Λ ∧ IsHalf (a' + b) t) from fun h => ht h.1), if_pos hat, mul_one]
          by_cases h1 : a' • t ∈ Λ
          · rw [if_neg (show ¬ (b • t ∈ Λ ∧ IsHalf b (b • t)) from fun h => ht (by rw [ht']; exact Λ.add_mem h1 h.1)),
              mul_zero]
          · rw [if_neg (show ¬ (a' • t ∈ Λ ∧ IsHalf a' (a' • t)) from fun h => h1 h.1), zero_mul]
      · rw [if_neg hat, mul_zero, if_neg fun h => hat h.2]
    rw [LinearMap.comp_apply, e]
    exact hT.vac

end GlobalTheory.ExportSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompRestrictToHalfLatticeIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPlaceModel_comp_restrictToHalfLatticeIndicator : ∀ {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}, a' * a' = a' → b * b = b → a' * b = 0 → (∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 f₀ (T₀ ∘ₗ restrictHalf a' b Λ) := by
  first | exact @GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf | exact GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf | (intros; apply GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadings
noncomputable section

namespace GlobalTheory.CoverIndep

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Matrix
open GlobalTheory.ShortMove GlobalTheory.ShortMoveIso GlobalTheory.TwistTie

theorem rmul_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b b' : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (hb' : b' ∈ Bor Ψ r) : rmul b b' ∈ Bor Ψ r := by
  intro τ
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have ht' : (mat b' τ).BlockTriangular id := fun a c h => (hb' τ).2 a c h
  refine ⟨?_, fun a c h => (ht.mul ht') h⟩
  show (mat b τ * mat b' τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero (hb τ).1 (hb' τ).1

theorem rmul_lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b b' : Frame Ψ r) :
    rmul (lact γ (rmul x b)) b' = rmul (lact γ x) (rmul b b') := by
  funext τ
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)) * mat b' τ =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * (mat b τ * mat b' τ)
  simp only [Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem dict_onto {D : D7} (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r)
    (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)
    (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hσ : GoodEmb c σ) (hA : l.A = 1) (hpq : 1 ≤ Dw.p + Dw.q)
    (hU : IsUnf U) (hW : ∀ k, ModelW V hr (U.X k)) (hD : DictLat U V hr dict io e F ik φ th x₀)
    (hι : GlobalTheory.Member.IotaOK Dw V io) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hx : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) (k : U.Comp) (x : Frame (U.X k).Ψ r) (hxd : x ∈ (U.X k).dom) :
    ∃ h, ∃ γ ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, dict h = ⟨k, rmul (lact γ x) b⟩ := by
  subst hr
  have hx₀ : ∀ k, IsOrthogonalFrame (U.X k) x₀ := fun k τ hτ => by
    rw [(hW k).1, (hU.2.1 k).1]
    exact hx τ (((hU.2.1 k).2 τ).1 hτ)
  obtain ⟨h1, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm
  obtain ⟨x₁, b, hb, ho, hx₁⟩ := h1 x hxd
  have hx₁d : x₁ ∈ (U.X k).dom := ((GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (U.X k).p0
    (U.X k).Ψ (U.X k).Gm (U.X k).Gm_herm).2.1 x₁ ho).1
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θ hθ
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hmem : ∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
    intro k τ
    rw [(hU.2.1 k).2 τ, hι.rt, hι.rt0]
  have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (U.X k).Ψ,
      uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x₁ ⟨τ, hτ⟩ = u * x₀ τ := by
    intro τ
    by_cases hτ : τ ∈ (U.X k).Ψ
    · obtain ⟨u, hu⟩ := h4 τ (x₀ τ) (mat x₁ ⟨τ, hτ⟩) (hx₀ k τ hτ) ((ho ⟨τ, hτ⟩).trans (hx₀ k τ hτ).symm)
      rw [hG] at hu
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hτ⟩
  choose u hu using hex
  obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem k τ).2 hτ)).1
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨h₀, hh₀⟩ := GlobalTheory.ShortMove.exists_marked_of_component D V H Dw l Xo _ g _ F hty _ rfl (U.X k) (ik k) (φ k) io
    (hW k) (hD.1.1 k) hι.emb hι.isom
  obtain ⟨a₀, ha₀, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h₀
  have hfin : finHom V (a₀ * f) = finHom V (a * f) := by
    rw [map_mul, map_mul, show finHom V a₀ = 1 from ha₀, show finHom V a = 1 from ha]
  have hh : Marked V rfl io l (U.X k).Λ (fun a => (φ k (F.t (ik k) a) : Fin V.rank → D.host.E)) (a * f) := by
    obtain ⟨e₁, e₂⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).2.1 _ _ hfin
    unfold Marked at hh₀ ⊢
    rwa [e₁, e₂, hfin] at hh₀
  refine ⟨a * f, ?_⟩
  obtain ⟨γ, hγ, hΛ, hm, hfr⟩ := hD.2 (a * f)
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V γ hγ
  obtain ⟨gam, e₁, t₁, hgam⟩ := marked_isometry_half V l io (U.X k) (U.X (dict (a * f)).1) _ _ (φ k) (φ _) (F.t _) (F.t _)
    LinearMap.id (a * f) γ 1 (hW k) (hW _) (hD.1.1 k) (hD.1.1 _) δ hδu hδf rfl (fun a _ => ⟨0, zero_mem _, by
      rw [map_one, Units.val_one, Matrix.one_mulVec, smul_zero, add_zero]; rfl⟩) hh
    (by rw [mul_one]; exact ⟨hΛ, hm⟩)
  obtain ⟨P, hPe, hP, hy, hd⟩ := hD.1.2 k ⟨x₁, hx₁d⟩
  obtain ⟨P', hPe', hP', hy', hd'⟩ := hD.1.2 (dict (a * f)).1 ⟨_, hdom _⟩
  obtain ⟨γ', hγ', b', hb', hk⟩ := (hU.2.2.2.1 k (dict (a * f)).1 ⟨x₁, hx₁d⟩ ⟨_, hdom _⟩).1
    (GlobalTheory.CoverOnto.frBor_of_isometry e F hpq hσ hA gam e₁ t₁ hP hP' (fun v => funext fun j => by
      rw [hPe, hPe', hgam]
      refine perFr_of_unitary _ _ (fun τ => by rw [hmem, hmem]) (by rw [hG, hG])
        (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h h' => ?_) _ _ _
      rw [hfr ⟨τ, h'⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h'⟩) (hθ τ), (hAr τ).2.1, (hAr τ).2.1,
        (hAr τ).2.2.1 f hf, hδa τ _ (hθ τ), hau τ ((hmem k τ).1 h), (hu τ h).2, Matrix.mul_one, ← Matrix.mul_assoc]
      rfl) _ _ hy hy' hd hd')
  refine ⟨γ', hγ', rmul b b', rmul_mem_bor hb hb', ?_⟩
  rw [← rmul_lact_rmul, ← hx₁]
  exact hk

theorem bchar_ne_zero' {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  have ht : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular ht] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

theorem indep_along {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp G : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (dict : G → Σ k, Frame (X k).Ψ r)
    (honto : ∀ k, ∀ x ∈ (X k).dom, ∃ g, ∃ γ ∈ (X k).Γ, ∃ b ∈ Bor (X k).Ψ r, dict g = ⟨k, rmul (lact γ x) b⟩)
    (ν : G → ℂ) (hν : ∀ g, ν g ≠ 0)
    {m : ℕ} (P : Fin m → FDSec X) (hS : ∀ i k, (X k).IsSec (la k) (P i k)) (h0 : ∀ i, P i ∈ offZero X)
    (hP : LinearIndependent ℂ P) (φ : Fin m → G → ℂ) (hφ : ∀ i g, φ i g = ν g * P i (dict g).1 (dict g).2) :
    LinearIndependent ℂ φ := by
  rw [Fintype.linearIndependent_iff] at hP ⊢
  intro c hc
  refine hP c ?_
  funext k x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases hx : x ∈ (X k).dom
  · obtain ⟨g, γ, hγ, b, hb, hg⟩ := honto k x hx
    have h := congrFun hc g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hφ] at h
    have hγx : lact γ x ∈ (X k).dom := dom_lact (X k) hx ((X k).Γ_stab γ hγ)
    have hχ : (X k).χ (la k) γ ≠ 0 := by
      obtain ⟨N, hN, hN1⟩ := (X k).χ_fin (la k)
      intro h0'
      have := hN1 γ hγ
      rw [h0', zero_pow hN.ne'] at this
      exact zero_ne_one this
    have e : ∀ i, P i (dict g).1 (dict g).2 = bchar (la k) b * (X k).χ (la k) γ * P i k x := by
      intro i
      rw [hg]
      show P i k (rmul (lact γ x) b) = _
      rw [(hS i k).2.1 _ hγx b hb, (hS i k).2.2 γ hγ x hx, mul_assoc]
    have hne := mul_ne_zero (hν g) (mul_ne_zero (bchar_ne_zero' (la k) hb) hχ)
    have key : ν g * (bchar (la k) b * (X k).χ (la k) γ) * ∑ i, c i * P i k x =
        ∑ i, c i * (ν g * P i (dict g).1 (dict g).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [e i]; ring
    rw [h] at key
    exact (mul_eq_zero.1 key).resolve_left hne
  · exact Finset.sum_eq_zero fun i _ => by rw [h0 i k x hx, mul_zero]


open GlobalTheory.CoverRead GlobalTheory.Member in
set_option maxHeartbeats 1000000 in
theorem cover_rd_linearIndependent : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) → LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => C.rd a (f i)) := by
  intro D T hT j hj σ hσ C hC hcc a n hdn m f hf hind
  obtain ⟨-, hA, hinc, hU, hdom, hr, g, e, F, ik, φ, th, hW, hth, hD⟩ := hC
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hσ₂ : GoodEmb C.d.c₂ C.σ₂ := by
    rw [← hinc] at hσ
    exact hσ
  have hI : LinearIndependent ℂ (fun i => rdU C.U₂ (f i)) :=
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ _ _ _ _
      (Formalism.L2.PjFree.Unf.ofPj C.U₂) hU a n).1 m f hf hind
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  refine indep_along C.U₂.X (laU C.U₂ a n) C.dict₂
    (fun k x hx => dict_onto (T.V j σ) hr C.U₂ C.dict₂ _ e F ik φ th _ hσ₂ hA (by omega) hU hW hD hio hth hx₀ hdom
      k x hx)
    (fun g => ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) * (C.cc₂ (C.dict₂ g).1 * T.mu j σ g)) ?_
    (fun i => rdU C.U₂ (f i)) (fun i k => hU.2.2.2.2.1 a n hdn _ (hf i) k)
    (fun i => rdU_mem_offZero _ _) hI _ ?_
  · intro g
    refine mul_ne_zero hl (mul_ne_zero ?_ ?_)
    · exact norm_ne_zero_iff.1 (by rw [hcc]; exact one_ne_zero)
    · exact norm_ne_zero_iff.1 (by rw [(hT.muVal j hj σ hσ).norm g]; exact one_ne_zero)
  · intro i g
    simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
    ring

end GlobalTheory.CoverIndep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverSectionsLinearIndependentAdelicReadingsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coverSections_linearIndependent_adelicReadings : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → CUnit C.cc₂ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (m : ℕ) (f : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ i, f i ∈ sec C.d.Xo₂ C.d.c₂ a n) → LinearIndependent C.d.c₂.F f → LinearIndependent ℂ (fun i => C.rd a (f i)) := by
  first | exact @GlobalTheory.CoverIndep.cover_rd_linearIndependent | exact GlobalTheory.CoverIndep.cover_rd_linearIndependent | (intros; apply GlobalTheory.CoverIndep.cover_rd_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CellDec

open Filter

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_finGL (v : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (Af E)) :
    compV E n v (finGL E n h) = GeneralLinearGroup.map (pLoc E v) h :=
  map_cornerGL_of_hom _ _ _ (fun _ => rfl) h

theorem compV_finGL_locGL_same (v : HeightOneSpectrum (𝓞 E)) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n v (finGL E n (locGL E n v y)) = y := by
  rw [compV_finGL, pLoc_locGL]

theorem compV_finGL_locGL_ne {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v) (y : GL (Fin n) (v.adicCompletion E)) :
    compV E n w (finGL E n (locGL E n v y)) = 1 := by
  rw [compV_finGL, pLoc_locGL_of_ne h]

theorem cornerGL_mem_unipB {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {g : GL (Fin a) R}
    (hg : g ∈ GlobalTheory.SmGL.unipB R (Fin a)) : cornerGL a s g ∈ GlobalTheory.SmGL.unipB S (Fin a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hg
  refine (GlobalTheory.SmGL.mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s ((g : Matrix _ _ R) i j) = 0
    rw [h1 i j hij, Matrix.one_apply_ne hij.ne', Matrix.one_apply_ne hij.ne', map_zero]
    simp
  · change (1 : Matrix (Fin a) (Fin a) S) i i - s ((1 : Matrix (Fin a) (Fin a) R) i i) + s ((g : Matrix _ _ R) i i) = 1
    rw [h2 i, Matrix.one_apply_eq, Matrix.one_apply_eq]
    simp

theorem finGL_locGL_mem_NA (v : HeightOneSpectrum (𝓞 E)) {y : GL (Fin n) (v.adicCompletion E)}
    (hy : y ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n)) : finGL E n (locGL E n v y) ∈ NA E n :=
  cornerGL_mem_unipB _ (cornerGL_mem_unipB _ hy)

theorem mem_US {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E n} :
    g ∈ US E n S ↔ ∀ v, v ∉ S → compV E n v g ∈ GlobalTheory.LFun.KGL v (n := n) := by
  simp [US, Subgroup.mem_iInf]

theorem eventually_compV_mem (g : GA E n) : ∀ᶠ w in cofinite, compV E n w g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h : ∀ x : GA E n, ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ i j,
      (compV E n w x).val i j ∈ w.adicCompletionIntegers E := fun x => by
    simp only [Filter.eventually_all]
    intro i j
    exact (pFin E ((x : Matrix (Fin n) (Fin n) (Ad E)) i j)).2
  filter_upwards [h g, h g⁻¹] with w a b
  exact GlobalTheory.BCT.GoodInt.mem_GLint _ _ a (by rw [← map_inv]; exact b)

end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m₁ m₂ : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    adl ϖ (m₁ + m₂) = adl ϖ m₁ * adl ϖ m₂ := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m₁ + m₂) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m₁ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m₂ v : (v.adicCompletion E)ˣ) : _)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

theorem adl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : adl ϖ 0 = 1 := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (0 : HeightOneSpectrum (𝓞 E) →₀ ℤ) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
  simp

theorem tl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l₁ l₂ : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ (l₁ + l₂) = tl n ϖ l₁ * tl n ϖ l₂ := by
  unfold tl
  rw [← map_mul, ← map_mul]
  congr 2
  funext i
  rw [Pi.mul_apply, ← adl_add]
  congr 1
  ext v
  simp

theorem tl_zero (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) : tl n ϖ 0 = 1 := by
  unfold tl
  have : (fun i : Fin n => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)))) = 1 := by
    funext i
    rw [Finsupp.mapRange_zero, adl_zero]
    rfl
  rw [this, map_one, map_one]

theorem GL_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem tl_single (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (v : HeightOneSpectrum (𝓞 E)) (a : Fin n → ℤ) :
    tl n ϖ (Finsupp.single v a) = finGL E n (locGL E n v (GlobalTheory.IwaCell.tD (ϖ v) a)) := by
  unfold tl
  congr 1
  apply GL_ext_pLoc
  intro w
  by_cases hw : w = v
  · subst hw
    rw [pLoc_locGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [GlobalTheory.IwaCell.val_tD]
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single w a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  · rw [pLoc_locGL_of_ne hw]
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl (Finsupp.single v a)) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp [Finsupp.single_apply, Ne.symm hw]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem ord_eq_one_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {π : (v.adicCompletion E)ˣ} (h : IsUnifV E v (π : v.adicCompletion E)) :
    GlobalTheory.SmGL.ord (v.adicCompletion E) π = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, h]
  change -WithZero.log (WithZero.exp (-1 : ℤ)) = 1
  simp

end
end GlobalTheory.CellDec

noncomputable section
namespace GlobalTheory.CellDec
open Filter
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem tl_inv_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : (tl n ϖ l)⁻¹ * u * tl n ϖ l ∈ NA E n := by
  have h : tl n ϖ (-l) = (tl n ϖ l)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← tl_add, neg_add_cancel, tl_zero])
  have := tl_conj_mem ϖ (-l) hu
  rwa [h, inv_inv] at this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem exists_of_finset (S : Finset (HeightOneSpectrum (𝓞 E))) (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ g : GA E n, (∀ w, w ∉ S → w ∉ T → compV E n w g ∈ GlobalTheory.LFun.KGL w (n := n)) →
      ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧ (tl n ϖ l)⁻¹ * g ∈ C0 E n S := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    refine ⟨0, fun _ _ => rfl, 1, one_mem _, g, mem_US.2 fun w hw => hg w hw (Finset.notMem_empty w), ?_⟩
    rw [tl_zero, inv_one, one_mul]
  | insert v T hvT ih =>
    intro g hg
    by_cases hvS : v ∈ S
    · refine ih g fun w hwS hwT => hg w hwS ?_
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hwS (h ▸ hvS), hwT⟩
    · obtain ⟨a, u, hu, κ, hκ, e⟩ := GlobalTheory.IwaCell.exists_mem_cell (v.adicCompletion E) n (ϖ v) (ord_eq_one_of_isUnifV (hϖ v))
        (compV E n v g)
      rw [GlobalTheory.HeckeEigConj.KO_eq_KGL] at hκ
      set x := finGL E n (locGL E n v u) with hx
      set t := tl n ϖ (Finsupp.single v a) with ht
      have hg' : ∀ w, w ∉ S → w ∉ T → compV E n w ((x * t)⁻¹ * g) ∈ GlobalTheory.LFun.KGL w (n := n) := by
        intro w hwS hwT
        rw [map_mul, map_inv, map_mul, hx, ht, tl_single]
        by_cases hw : w = v
        · subst hw
          rw [compV_finGL_locGL_same, compV_finGL_locGL_same, e]
          convert hκ using 1
          group
        · rw [compV_finGL_locGL_ne hw, compV_finGL_locGL_ne hw, one_mul, inv_one, one_mul]
          refine hg w hwS ?_
          rw [Finset.mem_insert, not_or]
          exact ⟨hw, hwT⟩
      obtain ⟨l', hl'S, u', hu', k, hk, e'⟩ := ih _ hg'
      refine ⟨Finsupp.single v a + l', fun w hw => ?_, (tl n ϖ (Finsupp.single v a + l'))⁻¹ * x *
        tl n ϖ (Finsupp.single v a + l') * u', mul_mem (tl_inv_conj_mem ϖ _ (finGL_locGL_mem_NA v hu)) hu', k, hk, ?_⟩
      · rw [Finsupp.add_apply, hl'S w hw, Finsupp.single_apply, if_neg (fun (h : v = w) => hvS (h ▸ hw)), add_zero]
      · have hg2 : g = x * t * (tl n ϖ l' * (u' * k)) := by
          rw [← e', mul_inv_cancel_left, mul_inv_cancel_left]
        rw [hg2, tl_add, ← ht]
        group

theorem adelic_iwasawa_decomposition_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  intro E _ _ n S ϖ hϖ g
  have hfin : {w | compV E n w g ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite :=
    Filter.eventually_cofinite.1 (eventually_compV_mem g)
  refine exists_of_finset S ϖ hϖ hfin.toFinset g fun w _ hw => ?_
  by_contra h
  exact hw (hfin.mem_toFinset.2 h)

end GlobalTheory.CellDec
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinsetStatement
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tl_inv_mul_mem_C0_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ g : GA E n, ∃ l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ), (∀ v ∈ S, l v = 0) ∧
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S := by
  first | exact @GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | exact GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset | (intros; apply GlobalTheory.CellDec.adelic_iwasawa_decomposition_off_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem compV_mem_unipB (v : HeightOneSpectrum (𝓞 E)) {u : GA E n} (hu : u ∈ NA E n) :
    compV E n v u ∈ GlobalTheory.SmGL.unipB (v.adicCompletion E) (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [compV, h1 i j hij]
  · simp [compV, h2 i]

theorem compV_tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (v : HeightOneSpectrum (𝓞 E)) :
    compV E n v (tl n ϖ l) = GlobalTheory.IwaCell.tD (ϖ v) (l v) := by
  rw [tl_eq_diagT]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [compV, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have hc : ∀ x : Af E, pFin E (GlobalTheory.CuspRep.corner (sFin E) x) = x := fun x => by
      show ((1 : InfiniteAdeleRing E × Af E) - ((0 : InfiniteAdeleRing E), (1 : Af E)) + ((0 : InfiniteAdeleRing E), x)).2 = x
      simp
    have hf : ∀ y : (Af E)ˣ, ((finId E y : Ad E)) = GlobalTheory.CuspRep.corner (sFin E) (y : Af E) := fun y => rfl
    rw [hf, hc]
    congr 1
    show ((ϖ v ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = _
    rw [Finsupp.mapRange_apply, Units.val_zpow_eq_zpow_val]
  · simp

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem ord_of_isUnifV {v : HeightOneSpectrum (𝓞 E)} {x : (v.adicCompletion E)ˣ}
    (hx : IsUnifV E v (x : v.adicCompletion E)) : GlobalTheory.SmGL.ord (v.adicCompletion E) x = 1 := by
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
  rfl

theorem compV_mem_cell (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {g : GA E n} (h : (tl n ϖ l)⁻¹ * g ∈ C0 E n S)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) : compV E n v g ∈ GlobalTheory.IwaCell.cell (ϖ v) (l v) := by
  obtain ⟨u, hu, k, hk, e⟩ := h
  have hg : g = tl n ϖ l * u * (tl n ϖ l)⁻¹ * tl n ϖ l * k := by
    rw [inv_mul_eq_iff_eq_mul] at e
    rw [e]; group
  have hkv : compV E n v k ∈ GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.HeckeEigConj.KO_eq_KGL]
    have := (Subgroup.mem_iInf.1 hk) v
    exact Subgroup.mem_comap.1 ((Subgroup.mem_iInf.1 this) hv)
  refine ⟨compV E n v (tl n ϖ l * u * (tl n ϖ l)⁻¹), compV_mem_unipB v (tl_conj_mem ϖ l hu), compV E n v k, hkv, ?_⟩
  rw [hg, map_mul, map_mul, compV_tl]

end GlobalTheory.CellDec

theorem GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  intro E _ _ n S ϖ hϖ l l' g hl hl' h h'
  ext v : 1
  by_cases hv : v ∈ S
  · rw [hl v hv, hl' v hv]
  · exact GlobalTheory.IwaCell.eq_of_mem_cell (GlobalTheory.CellDec.ord_of_isUnifV (hϖ v))
      (GlobalTheory.CellDec.compV_mem_cell ϖ l h hv) (GlobalTheory.CellDec.compV_mem_cell ϖ l' h' hv)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinsetStatement
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_iwasawa_cells_disjoint_off_finset : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) →
    ∀ (l l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n), (∀ v ∈ S, l v = 0) → (∀ v ∈ S, l' v = 0) →
      (GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → (GlobalTheory.CellDec.tl n ϖ l')⁻¹ * g ∈ GlobalTheory.CellDec.C0 E n S → l = l' := by
  first | exact @GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | exact GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 | (intros; apply GlobalTheory.CellDec.eq_of_tl_inv_mul_mem_C0_of_tl_inv_mul_mem_C0 <;> assumption)
end
end
