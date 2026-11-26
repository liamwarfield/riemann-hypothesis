module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfFin
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FderivApplyConst
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.EpowCongr
noncomputable section

open MeasureTheory Matrix Finset Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (X : Mat n) : EqOn (Rd X f) (Rd X f') (GLs n) := by
  intro g hg
  have he : f =ᶠ[nhds g] f' := Filter.eventually_of_mem ((isOpen_GLs n).mem_nhds hg) h
  simp only [Rd, he.fderiv_eq]

theorem eu_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (a b : Fin n) :
    EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply, rd_congr h _ hg]

theorem epow_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b, EqOn (Epow s m a b f) (Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b g hg
    simp only [Epow]
    split_ifs
    · exact h hg
    · rfl
  | succ m ih =>
    intro a b g hg
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_congr rfl fun c _ => eu_congr (ih c b) s a c hg

theorem gel_congr {f f' : Mat n → V} (h : EqOn f f' (GLs n)) (s : Bool) (m : ℕ) :
    EqOn (gel s m f) (gel s m f') (GLs n) := by
  intro g hg
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun a _ => epow_congr h s m a a hg

theorem rd_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf

end Ops

theorem gel_sum (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type} [Fintype ι]
    (F : ι → Mat n → V) (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (GLs n)) (s : Bool) (m : ℕ) :
    ∀ g ∈ GLs n, gel s m (fun y => ∑ i, F i y) g = ∑ i, gel s m (F i) g := by
  classical
  intro g hg
  let Φ : Mat n → (ι → V) := fun y i => F i y
  have hΦ : ContDiffOn ℝ ∞ Φ (GLs n) := contDiffOn_pi.2 hF
  have hsum := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (∑ i, ContinuousLinearMap.proj (R := ℂ) i)
  have hproj : ∀ i, gel s m (F i) g = gel s m Φ g i := by
    intro i
    have := ((hG n (ι → V) V s m Φ hΦ).2 g hg).2.2 (ContinuousLinearMap.proj (R := ℂ) i)
    simpa [Φ] using this
  have e : (fun y => ∑ i, F i y) = fun y => (∑ i, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => V) i) (Φ y) := by
    funext y; simp [Φ]
  rw [e, hsum]
  simp [hproj]

theorem gel_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (_h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ x ∈ GLs n, gel s m (DC ε Fr f) x = DC ε Fr (gel s m f) x := by
  intro x hx
  have hR : ∀ p, ContDiffOn ℝ ∞ (Rd (hb p) f) (GLs n) := fun p => rd_smooth hf _
  have hD : ∀ p, ContDiffOn ℝ ∞ (fun y => fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hGp : ∀ p, ContDiffOn ℝ ∞ (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) (GLs n) :=
    fun p => (hR p).add (hD p)
  have hFp : ∀ p, ContDiffOn ℝ ∞ (fun y => ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y))) (GLs n) :=
    fun p => ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (hGp p)
  have e1 : DC ε Fr f = fun y => ∑ p, ε (hb p) (Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) := rfl
  rw [e1, gel_sum hG _ hFp s m x hx]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [((hG n E.V E.V s m _ (hGp p)).2 x hx).2.2 (ε (hb p))]
  congr 1
  have h2 := gel_sum hG (fun (i : Fin 2) y => if i = 0 then Rd (hb p) f y else fderiv ℝ Fr 1 (hb p) (f y))
    (fun i => by fin_cases i <;> simp [hR p, hD p]) s m x hx
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false] at h2
  have h2' : gel s m (fun y => Rd (hb p) f y + fderiv ℝ Fr 1 (hb p) (f y)) x =
      gel s m (Rd (hb p) f) x + gel s m (fun y => fderiv ℝ Fr 1 (hb p) (f y)) x := by
    simpa using h2
  rw [h2', ((hG n E.V E.V s m f hf).2 x hx).2.2 (fderiv ℝ Fr 1 (hb p)), ((hG n E.V E.V s m f hf).2 x hx).1 (hb p)]

theorem zopDC : ZopDC := by
  intro hG n lam E Fr ε ι S Γ T hCx h hh w
  induction w with
  | nil => exact ⟨hh, fun x _ => rfl⟩
  | cons p w ih =>
    obtain ⟨ihs, ihc⟩ := ih
    refine ⟨(hG n E.V E.V p.1 p.2 _ ihs).1, fun x hx => ?_⟩
    show gel p.1 p.2 (zOp w (DC ε Fr h)) x = DC ε Fr (gel p.1 p.2 (zOp w h)) x
    rw [gel_congr (fun y hy => ihc y hy) p.1 p.2 hx]
    exact gel_DC hG hCx (zOp w h) ihs p.1 p.2 x hx

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

noncomputable section

open MeasureTheory Matrix Finset Set Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainOf2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt.ChainPf
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Partial

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_snd' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) (v : Mat n) :
    fderiv ℝ (fun y => U (s, y)) x v = fderiv ℝ U (s, x) (0, v) := by
  have h : HasFDerivAt (fun y : Mat n => U (s, y)) ((fderiv ℝ U (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Mat n))) x :=
    hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  rw [h.fderiv]
  rfl

theorem hasDerivAt_fst' {U : ℝ × Mat n → W} {s : ℝ} {x : Mat n} (hU : DifferentiableAt ℝ U (s, x)) :
    HasDerivAt (fun t => U (t, x)) (fderiv ℝ U (s, x) (1, 0)) s := by
  have hp : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × Mat n)) ((1 : ℝ), (0 : Mat n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hU.hasFDerivAt.comp_hasDerivAt s hp

theorem fderiv_apply_const' {F : ℝ × Mat n → (ℝ × Mat n →L[ℝ] W)} {q : ℝ × Mat n} (hF : DifferentiableAt ℝ F q)
    (w d : ℝ × Mat n) : fderiv ℝ (fun q' => F q' w) q d = fderiv ℝ F q d w := by
  set_option backward.isDefEq.respectTransparency false in
   have h := fderiv_clm_apply hF (show DifferentiableAt ℝ (fun _ : ℝ × Mat n => w) q from differentiableAt_const w)
   rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add] at h
   exact congrArg (fun L : ℝ × Mat n →L[ℝ] W => L d) h

theorem mixed' {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) (a b : ℝ × Mat n) :
    fderiv ℝ (fun q' => fderiv ℝ U q' a) q b = fderiv ℝ (fun q' => fderiv ℝ U q' b) q a := by
  have hd := hU.fderiv_of_isOpen hO (m := ∞) (by simp)
  have hdq : DifferentiableAt ℝ (fderiv ℝ U) q :=
    (hd.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)
  have hs := (hU.contDiffAt (hO.mem_nhds hq)).isSymmSndFDerivAt (by simp)
  rw [fderiv_apply_const' hdq, fderiv_apply_const' hdq]
  exact hs b a

theorem pd_smooth {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) (a : ℝ × Mat n) :
    ContDiffOn ℝ ∞ (fun q => fderiv ℝ U q a) O :=
  (hU.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem diffAt_of {U : ℝ × Mat n → W} {O : Set (ℝ × Mat n)} (hO : IsOpen O) (hU : ContDiffOn ℝ ∞ U O) {q : ℝ × Mat n}
    (hq : q ∈ O) : DifferentiableAt ℝ U q :=
  (hU.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp)

end Partial

theorem dc_add_smul (hG : GelComm) {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
    (F₁ F₂ : Mat n → E.V) (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) (c : ℂ) :
    ∀ x ∈ GLs n, DC ε Fr (c • (F₁ + F₂)) x = c • (DC ε Fr F₁ x + DC ε Fr F₂ x) := by
  intro x hx
  have hs : ContDiffOn ℝ ∞ (F₁ + F₂) (GLs n) := h₁.add h₂
  simp only [DC]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GlobalTheory.CompanionTheory.RCalc.Rd_smul c (hb p) hs hx, Pi.smul_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add (hb p) h₁ h₂ hx, Pi.add_apply]
  simp only [Pi.smul_apply, Pi.add_apply, map_add (f := _), map_smul, smul_add]
  abel

theorem om_DC (hG : GelComm) {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)}
    {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)} {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}
    (h : CxData lam E Fr ε ι S Γ T) (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ∀ x ∈ GLs n, Om (DC ε Fr f) x = DC ε Fr (Om f) x := by
  intro x hx
  have ht := (hG n E.V E.V true 2 f hf).1
  have hfa := (hG n E.V E.V false 2 f hf).1
  have e : Om f = (2 : ℂ) • (gel true 2 f + gel false 2 f) := rfl
  rw [e, dc_add_smul hG _ _ ht hfa 2 x hx]
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [gel_DC hG h f hf true 2 x hx, gel_DC hG h f hf false 2 x hx]

theorem dCwave_of (hin : DCinCE) : DCwave := by
  intro hG n lam E Fr ε ι S Γ T hCx u hu
  obtain ⟨hsm, hCE, heq, h0⟩ := hu
  set O : Set (ℝ × Mat n) := Set.univ ×ˢ GLs n with hOdef
  have hO : IsOpen O := isOpen_univ.prod GlobalTheory.CompanionTheory.RCalc.isOpen_GLs
  set Ψ : ℝ × Mat n → E.V := Function.uncurry u with hΨ
  have hmem : ∀ s, ∀ x ∈ GLs n, ((s, x) : ℝ × Mat n) ∈ O := fun s x hx => ⟨Set.mem_univ _, hx⟩
  set A : ℝ × Mat n → E.V := fun q => fderiv ℝ Ψ q (1, 0) with hA
  have hAs : ContDiffOn ℝ ∞ A O := pd_smooth hO hsm (1, 0)
  set B : ℝ × Mat n → E.V := fun q => fderiv ℝ A q (1, 0) with hB
  have hBs : ContDiffOn ℝ ∞ B O := pd_smooth hO hAs (1, 0)
  set D : Fin n × Fin n → (E.V →L[ℂ] E.V) := fun p => fderiv ℝ Fr 1 (hb p) with hD

  have hslice : ∀ s, ∀ x ∈ GLs n, DC ε Fr (u s) x =
      ∑ p, ε (hb p) (fderiv ℝ Ψ (s, x) (0, x * hb p) + D p (Ψ (s, x))) := by
    intro s x hx
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show u s = fun y => Ψ (s, y) from rfl, fderiv_snd' (diffAt_of hO hsm (hmem s x hx))]

  have hΨA : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => u t x) (A (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := Ψ) (diffAt_of hO hsm (hmem s x hx))
  have hAB : ∀ s, ∀ x ∈ GLs n, HasDerivAt (fun t => A (t, x)) (B (s, x)) s := fun s x hx =>
    hasDerivAt_fst' (U := A) (diffAt_of hO hAs (hmem s x hx))
  have hBom : ∀ s, ∀ x ∈ GLs n, B (s, x) = Om (u s) x := by
    intro s x hx
    rw [← heq s x hx, iteratedDeriv_succ, iteratedDeriv_one]
    have h1 : deriv (fun t => u t x) = fun t => A (t, x) := funext fun t => (hΨA t x hx).deriv
    rw [h1, (hAB s x hx).deriv]
  have hdpsi : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ Ψ (t, x) w) (fderiv ℝ A (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ Ψ q w) (s, x) := diffAt_of hO (pd_smooth hO hsm w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hsm (hmem s x hx) w (1, 0)] at this
  have hdA : ∀ (w : ℝ × Mat n), ∀ s, ∀ x ∈ GLs n,
      HasDerivAt (fun t => fderiv ℝ A (t, x) w) (fderiv ℝ B (s, x) w) s := by
    intro w s x hx
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ A q w) (s, x) := diffAt_of hO (pd_smooth hO hAs w) (hmem s x hx)
    have := hasDerivAt_fst' hd
    rwa [mixed' hO hAs (hmem s x hx) w (1, 0)] at this
  refine ⟨?_, fun t => hin n lam E Fr ε ι S Γ T hCx (u t) (hCE t), ?_, ?_⟩
  ·
    have hsm' : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n =>
        ∑ p, ε (hb p) (fderiv ℝ Ψ q (0, q.2 * hb p) + D p (Ψ q))) O := by
      refine ContDiffOn.sum fun p _ => ?_
      refine ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn ?_
      refine ContDiffOn.add ?_ (((D p).restrictScalars ℝ).contDiff.comp_contDiffOn hsm)
      have hv : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((0 : ℝ), q.2 * hb p)) :=
        contDiff_const.prodMk ((GlobalTheory.CompanionTheory.RCalc.mulR (hb p)).contDiff.comp contDiff_snd)
      exact (hsm.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply hv.contDiffOn
    refine hsm'.congr fun q hq => ?_
    obtain ⟨s, x⟩ := q
    exact hslice s x hq.2
  · intro t g hg
    have hf : ∀ s, (fun s => DC ε Fr (u s) g) s = ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
      fun s => hslice s g hg
    have hf1 : ∀ s, HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g)))) s := by
      intro s
      have : (fun s => DC ε Fr (u s) g) = fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) :=
        funext hf
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdpsi _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hΨA s g hg)))
    have hf2 : ∀ s, HasDerivAt (fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))))
        (∑ p, ε (hb p) (fderiv ℝ B (s, g) (0, g * hb p) + D p (B (s, g)))) s := by
      intro s
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
        ((hdA _ s g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hAB s g hg)))
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have e1 : deriv (fun s => DC ε Fr (u s) g) =
        fun s => ∑ p, ε (hb p) (fderiv ℝ A (s, g) (0, g * hb p) + D p (A (s, g))) := funext fun s => (hf1 s).deriv
    rw [e1, (hf2 t).deriv]
    have hu2 : ContDiffOn ℝ ∞ (u t) (GLs n) := (hCE t).1
    have hom : ContDiffOn ℝ ∞ (Om (u t)) (GLs n) := by
      have ht := (hG n E.V E.V true 2 (u t) hu2).1
      have hfa := (hG n E.V E.V false 2 (u t) hu2).1
      exact (ht.add hfa).const_smul (2 : ℂ)
    rw [om_DC hG hCx (u t) hu2 g hg]
    simp only [DC, Rd]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hBe : EqOn (fun y => B (t, y)) (Om (u t)) (GLs n) := fun y hy => hBom t y hy
    have hev : (fun y => B (t, y)) =ᶠ[𝓝 g] Om (u t) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) hBe
    rw [← fderiv_snd' (diffAt_of hO hBs (hmem t g hg)), hev.fderiv_eq, hBom t g hg]
  · intro g hg
    have hf1 : HasDerivAt (fun s => DC ε Fr (u s) g)
        (∑ p, ε (hb p) (fderiv ℝ A (0, g) (0, g * hb p) + D p (A (0, g)))) 0 := by
      have : (fun s => DC ε Fr (u s) g) =
          fun s => ∑ p, ε (hb p) (fderiv ℝ Ψ (s, g) (0, g * hb p) + D p (Ψ (s, g))) := funext fun s => hslice s g hg
      rw [this]
      refine HasDerivAt.fun_sum fun p _ => ?_
      exact ((ε (hb p)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
        ((hdpsi _ 0 g hg).add (((D p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hΨA 0 g hg)))
    rw [hf1.deriv]
    have hA0 : ∀ x ∈ GLs n, A (0, x) = 0 := fun x hx => by rw [← (hΨA 0 x hx).deriv]; exact h0 x hx
    have hev : (fun y => A (0, y)) =ᶠ[𝓝 g] fun _ => (0 : E.V) :=
      Filter.eventuallyEq_of_mem (GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg) fun y hy => hA0 y hy
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← fderiv_snd' (diffAt_of hO hAs (hmem 0 g hg)), hev.fderiv_eq, hA0 g hg]
    simp

end PositivityTheory.RgBcC.LfSt.ChainOf2
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Fin

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  show det k.1 ≠ 0
  intro h0
  have hd := Matrix.det_of_mem_unitary k.2
  rw [h0] at hd
  have h1 : star (0 : ℂ) * 0 = 1 := hd.1
  simp at h1

theorem act_sum (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) {m : ℕ} (c : Fin m → ℂ) (ks : Fin m → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V))
    (hsum : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) (hcont : ∀ i, ContinuousOn (ks i) (GLs n)) (hcpt : ∀ i, Cpt (ks i))
    (F : Mat n → E.V) (hF : ContinuousOn F (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    act μ E k F x = ∑ i, c i • act μ E (ks i) F x := by
  unfold act
  have hFx : ContinuousOn (fun z => F (x * z)) (GLs n) :=
    hF.comp (continuous_const.mul continuous_id).continuousOn (fun z hz => mul_mem_GLs hx hz)
  have hint : ∀ i, Integrable (fun y : G n => (ks i ↑y) (F (x * ↑y))) μ :=
    fun i => int_of_cptK hL μ (ks i) (fun z => F (x * z)) (hcont i) hFx (hcpt i)
  have hint' : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      Integrable (fun y : G n => c i • (ks i ↑y) (F (x * ↑y))) μ :=
    fun i _ => (hint i).smul (c i)
  have hfun : (fun y : G n => (k ↑y) (F (x * ↑y))) = fun (y : G n) => ∑ i, c i • (ks i ↑y) (F (x * ↑y)) := by
    funext y
    rw [hsum _ (mem_GLs_of y)]
    simp [ContinuousLinearMap.sum_apply]
  rw [hfun, integral_finsetSum _ hint']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_smul]

theorem dc_sum {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (ε : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (Fr : Mat n → (V →L[ℂ] V)) {m : ℕ} (c : Fin m → ℂ) (h : Fin m → Mat n → V)
    (hd : ∀ i, DifferentiableAt ℝ (h i) 1) :
    DC ε Fr (fun x => ∑ i, c i • h i x) 1 = ∑ i, c i • DC ε Fr (h i) 1 := by
  have hsd : HasFDerivAt (fun x => ∑ i, c i • h i x) (∑ i, c i • fderiv ℝ (h i) 1) 1 :=
    HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt.const_smul (c i)
  simp only [DC, Rd, hsd.fderiv]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sum,
    map_smul, Finset.smul_sum, smul_add]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_add, map_smul]

end PositivityTheory.RgBcC.LfSt.ChainPf.Fin
end
end

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Done

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top
  PositivityTheory.RgBcC.LfSt.ChainPf.Fin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem chainOf'_of (hDC : DCinCE) (hP : ParamInt) (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hU : Unimod)
    (hR : RCalc) (hL : LgFacts) : ChainOf' := by
  intro hWE _hWS hG hKZ n lam E Fr ε ι S Γ T hC _ _ μ _ k val τ hk
  haveI := FiniteDimensional.complete ℂ E.V
  have hDW : DCwave := PositivityTheory.RgBcC.LfSt.ChainOf2.dCwave_of hDC
  have hZ : ZopDC := PositivityTheory.RgBcC.LfSt.ChainOf2.zopDC
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hk
  have hks1 : ∀ i, ContDiffOn ℝ ∞ (ks i) (GLs n) := fun i => (hks i).2.1
  have hkc1 : ∀ i, Cpt (ks i) := fun i => (hks i).2.2.1
  have hke1 : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ks i (y * k₂.1) = ks i y * E.ρ k₂ := by
    intro i y hy k₂
    have := (hks i).2.2.2.1 y hy 1 k₂
    simpa using this

  have hsm : ContDiffOn ℝ ∞ k (GLs n) :=
    (ContDiffOn.sum fun i _ => (hks1 i).const_smul (c i)).congr fun y hy => hsum y hy
  have hcp : Cpt k := by
    choose R hR using hkc1
    refine ⟨∑ i, max (R i) 0, fun y hy hlt => ?_⟩
    rw [hsum y hy]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ j, max (R j) 0 :=
      (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (R j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i))
    rw [hR i y hy (lt_of_le_of_lt hle hlt), smul_zero]
  have hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂ := by
    intro y hy k₂
    rw [hsum _ (mul_mem_GLs hy (unitary_mem_GLs k₂)), hsum y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hke1 i y hy k₂, smul_mul_assoc]
  have hcont : ∀ i, ContinuousOn (ks i) (GLs n) := fun i => (hks1 i).continuousOn
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]

  let ΓE : E.V ≃L[ℂ] E.V := ContinuousLinearEquiv.equivOfInverse Γ Γ
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
  have hΓρ : ∀ k₀ : Matrix.unitaryGroup (Fin n) ℂ, Γ * E.ρ k₀ = E.ρ k₀ * Γ := by
    intro k₀
    have := hC.ΓFr k₀.1 (unitary_mem_GLs k₀)
    rwa [hC.onK] at this
  have hA' : ∀ (k₀ : Matrix.unitaryGroup (Fin n) ℂ) v, ΓE (E.ρ k₀ v) = E.ρ k₀ (ΓE v) := by
    intro k₀ v
    show Γ (E.ρ k₀ v) = E.ρ k₀ (Γ v)
    rw [← ContinuousLinearMap.mul_apply, hΓρ]
    rfl
  have hΓc : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1) := by
    intro f hf
    have hfΓ : ContinuousOn (fun x => Γ (f x)) (GLs n) := continuousOn_const.clm_apply hf.1.continuousOn
    set_option synthInstance.maxHeartbeats 100000 in
      rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hfΓ 1 h1, act_sum hL μ E c ks k hsum hcont hkc1 _ hf.1.continuousOn 1 h1,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    exact act_equiv hWE μ E ΓE hA' (w i) (g i) (ks i) (hks i).2 f hf

  have hDc : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1 := by
    intro f hf
    have hDf := hDC n lam E Fr ε ι S Γ T hC f hf
    have hsmooth : ∀ i, ContDiffOn ℝ ∞ (act μ E (ks i) f) (GLs n) := fun i =>
      (hA hU n μ E (ks i) f (hks1 i) (hkc1 i) hf.1).1
    have eqk : Set.EqOn (act μ E k f) (fun x => ∑ i, c i • act μ E (ks i) f x) (GLs n) := fun x hx =>
      act_sum hL μ E c ks k hsum hcont hkc1 f hf.1.continuousOn x hx
    rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hDf.1.continuousOn 1 h1, dc_congr ε Fr (isOpen_GLs n) eqk h1,
      dc_sum ε Fr c _ fun i => ((hsmooth i).differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds h1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_dc hDW hP hZ hG hWE hC μ (w i) (g i) τ (hks i).1 (ks i) (hks i).2 f hf]
  intro y hy
  refine ⟨gamma_of_comm hKZ hL Γ hΓρ μ k hsm.continuousOn hke hΓc y hy, ?_⟩
  exact dc_of_comm hA hI hK hKZ hU hR hL hC μ k hsm hcp hke hDc y hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Done
