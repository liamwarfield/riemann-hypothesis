module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfDD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem gg_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul ha hb

theorem gg_one : (1 : Mat k r) ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r

theorem hasDeriv_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) (dsig σ Y v) 0 :=
  Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv [] (by simp) hY

theorem smooth_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) : IsSmoothVec (k := k) (r := r) σ (dsig σ Y v) := by
  have h2 := Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv [Y] (by simpa using hY)
  intro g₀ hg₀
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h2 ((1 : Mat k r), g₀) (gg_one) hg₀
  have hc : ContDiff ℝ ∞ (fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) ⁻¹' U, fun g => F ((1 : Mat k r), g),
    hU.preimage hc.continuous, hp, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE ((1 : Mat k r), g) hgU gg_one hgH
  simp only [hσ.1.1, ContinuousLinearMap.one_apply] at this
  exact this

theorem lie_conj {g Y : Mat k r} (hg : g ∈ GG k r) (hY : InLieHpk k r Y) :
    InLieHpk k r (g * Y * g⁻¹) := by
  have hd : IsUnit g.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hgM : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hd
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM' : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hM
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgM, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg']
  have e2 : Hpk k r * g = (g⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * g = ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hM']
      _ = (g⁻¹)ᴴ * Hpk k r * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hMg, Matrix.mul_one]
  have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (g * Y * g⁻¹)ᴴ * Hpk k r + Hpk k r * (g * Y * g⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (g⁻¹)ᴴ * (Yᴴ * gᴴ) * Hpk k r + Hpk k r * (g * Y * g⁻¹)
      = (g⁻¹)ᴴ * Yᴴ * (gᴴ * Hpk k r) + (Hpk k r * g) * Y * g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (g⁻¹)ᴴ * Yᴴ * (Hpk k r * g⁻¹) + ((g⁻¹)ᴴ * Hpk k r) * Y * g⁻¹ := by rw [e1, e2]
    _ = (g⁻¹)ᴴ * (Yᴴ * Hpk k r + Hpk k r * Y) * g⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) {g : Mat k r} (hg : g ∈ GG k r) :
    σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v) := by
  have hd : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg)
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hd)
  have h1 := hasDeriv_dsig hσ hv hY
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * Y * g⁻¹))) (σ g v)) =
      (⇑((σ g).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
    funext t
    have hx := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t
    have hs : (t : ℂ) • (g * Y * g⁻¹) = g * ((t : ℂ) • Y) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hs, Matrix.exp_conj _ _ hd]
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    have hc : g * NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := gg_mul hg hx
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (gg_mul hc hM) g hg,
      ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ hx]
    congr 2
    rw [Matrix.mul_assoc, hMg, Matrix.mul_one]
  show _ = deriv _ 0
  rw [e, h2.deriv]
  rfl

theorem smooth_dsigW (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) → IsSmoothVec (k := k) (r := r) σ (dsigW σ Ys v) := by
  intro Ys
  induction Ys with
  | nil => intro _; exact hv
  | cons Y Ys ih =>
    intro h
    exact smooth_dsig hσ (ih fun X hX => h X (List.mem_cons_of_mem _ hX)) (h Y List.mem_cons_self)

theorem dsigW_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {g : Mat k r} (hg : g ∈ GG k r) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) →
      σ g (dsigW σ Ys v) = dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v) := by
  intro Ys
  induction Ys with
  | nil => intro _; rfl
  | cons Y Ys ih =>
    intro h
    have h' : ∀ X ∈ Ys, InLieHpk k r X := fun X hX => h X (List.mem_cons_of_mem _ hX)
    show σ g (dsig σ Y (dsigW σ Ys v)) = dsig σ (g * Y * g⁻¹) (dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v))
    rw [dsig_conj hσ (smooth_dsigW hσ hv Ys h') (h Y List.mem_cons_self) hg, ih h']

theorem dsig_zero (Y : Mat k r) : dsig σ Y (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add (hσ : IsURepOn (GG k r) σ) {a b : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (hb : IsSmoothVec (k := k) (r := r) σ b) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (a + b) = dsig σ Y a + dsig σ Y b := by
  have h := (hasDeriv_dsig hσ ha hY).add (hasDeriv_dsig hσ hb hY)
  show deriv _ 0 = _
  simp only [map_add (f := _)]
  exact h.deriv

theorem dsig_smul (hσ : IsURepOn (GG k r) σ) {a : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (c : ℂ) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (c • a) = c • dsig σ Y a := by
  have h := (hasDeriv_dsig hσ ha hY).const_smul c
  show deriv _ 0 = _
  simp only [map_smul]
  exact h.deriv

theorem DD_stable (hσ : IsURepOn (GG k r) σ) (w : H) {g : Mat k r} (hg : g ∈ GG k r) :
    DD σ w ≤ (DD σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, rfl⟩
  show σ g (σ h w) ∈ DD σ w
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  exact mem_DD σ w (gg_mul hg hh)

theorem mem_DD_self (hσ : IsURepOn (GG k r) σ) (w : H) : w ∈ DD σ w := by
  have := mem_DD σ w (gg_one (k := k) (r := r))
  rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this

theorem DD_dense (hσ : IsURepOn (GG k r) σ) (hirr : IsIrredOn (GG k r) σ) {w : H} (hw : w ≠ 0) :
    Dense (DD σ w : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hst : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w).topologicalClosure, σ g v ∈ (DD σ w).topologicalClosure := by
    intro g hg v hv
    have hle : (DD σ w).topologicalClosure ≤ ((DD σ w).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · exact (DD_stable hσ w hg).trans (Submodule.comap_mono (DD σ w).le_topologicalClosure)
      · exact (DD σ w).isClosed_topologicalClosure.preimage (σ g).continuous
    exact hle hv
  rcases hirr (DD σ w).topologicalClosure (DD σ w).isClosed_topologicalClosure hst with h | h
  · exfalso
    have h1 : w ∈ (DD σ w).topologicalClosure := (DD σ w).le_topologicalClosure (mem_DD_self hσ w)
    rw [h, Submodule.mem_bot] at h1
    exact hw h1
  · exact h

theorem DD_le_Vinf (w : H) : DD σ w ≤ Vinf σ w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨[], g, by simp, hg, rfl⟩

theorem Vinf_smooth (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w) :
    ∀ v ∈ Vinf σ w, IsSmoothVec (k := k) (r := r) σ v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    exact smooth_dsigW hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hg) Ys hYs
  | zero => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero
  | add x y _ _ hx hy => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_add hx hy
  | smul a x _ hx => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_smul a hx

theorem Vinf_stable (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {g : Mat k r} (hg : g ∈ GG k r) : Vinf σ w ≤ (Vinf σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨Ys, h, hYs, hh, rfl⟩
  show σ g (dsigW σ Ys (σ h w)) ∈ Vinf σ w
  rw [dsigW_conj hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hh) hg Ys hYs,
    ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  refine Submodule.subset_span ⟨Ys.map fun Y => g * Y * g⁻¹, g * h, ?_, gg_mul hg hh, rfl⟩
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  exact lie_conj hg (hYs X hX)

theorem Vinf_dsig (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {Y : Mat k r} (hY : InLieHpk k r Y) : ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨Y :: Ys, g, ?_, hg, rfl⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hY
    · exact hYs X hX
  | zero => rw [dsig_zero]; exact (Vinf σ w).zero_mem
  | add x y hx hy ihx ihy =>
    rw [dsig_add hσ (Vinf_smooth hσ hw x hx) (Vinf_smooth hσ hw y hy) hY]
    exact (Vinf σ w).add_mem ihx ihy
  | smul a x hx ihx =>
    rw [dsig_smul hσ (Vinf_smooth hσ hw x hx) a hY]
    exact (Vinf σ w).smul_mem a ihx

theorem DD_stable_dense : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ →
    (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧
    (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧
    (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧
      ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧
        ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧
    (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧
      ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  intro k r H _ _ _ σ w hσ
  refine ⟨fun g hg v hv => DD_stable hσ w hg hv, fun hirr hw => DD_dense hσ hirr hw, DD_le_Vinf w,
    fun v hv => ⟨fun g hg => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg, fun Y hY =>
      ⟨smooth_dsig hσ hv hY, fun g hg => ⟨lie_conj hg hY, dsig_conj hσ hv hY hg⟩⟩⟩,
    fun hw => ⟨Vinf_smooth hσ hw, fun g hg v hv => Vinf_stable hσ hw hg hv, fun Y hY => Vinf_dsig hσ hw hY⟩⟩

end GlobalTheory.SgInfDD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_dense_invariant : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ → (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧ (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧ (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧ ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧ ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧ (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧ ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  first | exact @GlobalTheory.SgInfDD.DD_stable_dense | exact GlobalTheory.SgInfDD.DD_stable_dense | (intros; apply GlobalTheory.SgInfDD.DD_stable_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFrames
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  refine ⟨h1.map _, ?_, ?_⟩
  · have himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_img, Set.mem_image]
      rfl
    rw [himg, ← Submodule.map_span, h2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  · intro x
    constructor
    · intro hx y hy
      obtain ⟨a, ha, rfl⟩ := (mem_img g Λ x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_img g Λ y).1 hy
      rw [hg]
      exact (h3 a).1 ha b hb
    · intro hx
      obtain ⟨a, rfl⟩ := g.surjective x
      refine (mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩
      have := hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [hg] at this

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩
  · exact p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · intro x hx hs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hs
    obtain ⟨y', hy', hyy⟩ := hs
    have hyy' : y' = y := g.injective hyy
    subst hyy'
    have hO := p3 y' hy hy'
    have hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f),
        g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b)) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        exact Submodule.subset_span ⟨b, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : g (c • a) = c • g a := by
          change g ((c : E) • a) = (c : E) • g a
          exact map_smul g (c : E) a
        rw [this]
        exact Submodule.smul_mem _ c ha
    exact hmap y' hO
  · intro a b hab
    rw [hg]
    exact h2 a b hab
  · rw [hg]
    exact h3

lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_datum_of_two_congruent_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  first | exact @GlobalTheory.LocOver.TermOver.exists_datum | exact GlobalTheory.LocOver.TermOver.exists_datum | (intros; apply GlobalTheory.LocOver.TermOver.exists_datum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinates
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

end GlobalTheory.SnMass.VolN

private lemma mul_vecMulVec_mul_flag_measures {n : Type} [Fintype n] (M N : Matrix n n ℂ) (u v : n → ℂ) :
    M * vecMulVec u v * N = vecMulVec (M *ᵥ u) (v ᵥ* N) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

private lemma single_vecMul_Hpk_eI (k r : ℕ) (a : Fin r) :
    Pi.single (_root_.Formalism.QuantumDeterminants.eI k r a) 1 ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r = Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) := by
  funext j
  rw [single_one_vecMul]
  change _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.eI k r a) j = (Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) : _ → ℂ) j
  unfold _root_.Formalism.QuantumDeterminants.Hpk _root_.Formalism.QuantumDeterminants.eI _root_.Formalism.QuantumDeterminants.esI
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  have ha := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)

theorem _root_.GlobalTheory.SnMass.VolN.rowE_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), _root_.GlobalTheory.SnMass.VolN.gM A (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = _root_.Formalism.QuantumDeterminants.esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD a y t w i j
  obtain ⟨hσ, -, hJ, -, -, -, -, hA, -, hAd⟩ := hD
  set x : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (P l a.castSucc) with hx_def
  set v : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (y l) with hv_def
  have hconj : ∀ z : E, w.embedding (σ z) = star (w.embedding z) := fun z => hσ.2.2.2 w.embedding z
  have hiso : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map w.embedding := hA w
  have hAx : A w *ᵥ x = (s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a) := (hAd w a).1
  have hdet : IsUnit (A w).det := by
    have h1 : (J.map w.embedding).det ≠ 0 := by
      rw [show (J.map w.embedding).det = w.embedding J.det from (RingHom.map_det _ _).symm]
      exact (map_ne_zero _).2 hJ.2
    rw [← hiso, det_mul, det_mul] at h1
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h1)
  have hinv : A w * (A w)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hrow : ∀ u : Fin (2 * r + k + 1) → ℂ,
      star u ᵥ* J.map w.embedding ᵥ* (A w)⁻¹ = star (A w *ᵥ u) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r := by
    intro u
    rw [← hiso, vecMul_vecMul, Matrix.mul_assoc, hinv, Matrix.mul_one, ← vecMul_vecMul,
      ← star_mulVec]
  have hmap : (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun l => P l a.castSucc) y t).map
      w.embedding = 1 + vecMulVec (v + w.embedding t • x) (star x ᵥ* J.map w.embedding) -
        vecMulVec x (star v ᵥ* J.map w.embedding) := by
    ext p q
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.SnMass.VolN.rowE, vecMulVec_apply, vecMul, dotProduct, map_sum, hconj,
      one_apply, x, v]
      exact Matrix.one_apply.symm
  unfold _root_.GlobalTheory.SnMass.VolN.gM
  rw [hmap, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one, hinv,
    mul_vecMulVec_mul_flag_measures, mul_vecMulVec_mul_flag_measures, hrow, hrow, mulVec_add, mulVec_smul, hAx]
  have hstar : star ((s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r =
      (s a : ℂ) • Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 := by
    unfold _root_.Formalism.QuantumDeterminants.bvec
    rw [star_smul, ← Pi.single_star, star_one, smul_vecMul, single_vecMul_Hpk_eI, Complex.star_def,
      Complex.conj_ofReal]
  rw [hstar]
  unfold _root_.Formalism.QuantumDeterminants.herm _root_.Formalism.QuantumDeterminants.bvec
  rw [dotProduct_mulVec, dotProduct_single_one]
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Matrix.one_apply]
  split_ifs <;> ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIsometry_entries_in_modelCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = eI k r a then (s a : ℂ) * herm (Hpk k r) (bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  first | exact @GlobalTheory.SnMass.VolN.rowE_entries | exact GlobalTheory.SnMass.VolN.rowE_entries | (intros; apply GlobalTheory.SnMass.VolN.rowE_entries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.RowIso

section Alg
variable {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_sub_left (x x' y : Fin n → E) : form σ J (x - x') y = form σ J x y - form σ J x' y := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_sub_right (x y y' : Fin n → E) : form σ J x (y - y') = form σ J x y - form σ J x y' := by
  simp [form, dotProduct, sub_mul, Finset.sum_sub_distrib]

theorem form_neg_right (x y : Fin n → E) : form σ J x (-y) = -form σ J x y := by
  simp [form, dotProduct]

theorem form_neg_left (x y : Fin n → E) : form σ J (-x) y = -form σ J x y := by
  simp [form, Matrix.mulVec_neg]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J x y = σ (form σ J y x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowE_mulVec (e y : Fin n → E) (t : E) (x : Fin n → E) :
    rowE σ J e y t *ᵥ x = x + form σ J x e • (y + t • e) - form σ J x y • e := by
  ext i
  simp only [rowE, mulVec, dotProduct, form, vecMul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun (a b : Fin n) => y i * (σ (e b) * (J b a * x a))),
    Finset.sum_comm (f := fun (a b : Fin n) => t * (e i * (σ (e b) * (J b a * x a)))),
    Finset.sum_comm (f := fun (a b : Fin n) => e i * (σ (y b) * (J b a * x a))), ← Finset.sum_add_distrib]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · funext a
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem isUn_of_form (g : Matrix (Fin n) (Fin n) E)
    (h : ∀ x x', form σ J (g *ᵥ x) (g *ᵥ x') = form σ J x x') : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite σ, map_one, map_zero, ite_mul, one_mul, zero_mul] at this
  rw [← this]
  simp only [IsUn, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg
end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

section Iso
variable {E : Type} [Field E] {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  (hJ : ∀ i j, σ (J j i) = J i j) {e y : Fin n → E} {t : E} (he : form σ J e e = 0)
  (hye : form σ J y e = 0) (ht : form σ J y y + t + σ t = 0)
include hσ hJ he hye ht

theorem form_rowE (x x' : Fin n → E) :
    form σ J (rowE σ J e y t *ᵥ x) (rowE σ J e y t *ᵥ x') = form σ J x x' := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have h1 : form σ J y x' = σ (form σ J x' y) := form_herm σ J hσ hJ _ _
  have h2 : form σ J e x' = σ (form σ J x' e) := form_herm σ J hσ hJ _ _
  simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_add_right, form_sub_right,
    form_smul_right, map_add, map_sub, map_mul, hσ, he, hye, hey, h1, h2]
  linear_combination (form σ J x e * σ (form σ J x' e)) * ht

theorem rowE_inv (x : Fin n → E) :
    rowE σ J e y t *ᵥ (rowE σ J e (-y) (σ t) *ᵥ x) = x := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have hα : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) e = form σ J x e := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, he, hye]
    ring
  have hβ : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) y = form σ J x y - form σ J x e * form σ J y y := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, form_neg_right, hey]
    ring
  rw [rowE_mulVec σ J e y t, hα, hβ, rowE_mulVec σ J e (-y) (σ t) x]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, form_neg_right]
  linear_combination (form σ J x e * e i) * ht

end Iso

section Lat
variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.SnMass.FrameDual in
theorem rowE_mem {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E}
    (h0 : 𝔞 ≠ 0) (hs : Stab σ 𝔞) {e y : Fin n → E} {t : E} (he : ∀ c ∈ 𝔞, c • e ∈ Λ)
    (hy : ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ) (ht : t ∈ 𝔞 * 𝔞) {v : Fin n → E} (hv : v ∈ Λ) :
    rowE σ J e y t *ᵥ v ∈ Λ := by
  have hO : ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range := (hΛ.2 v).1 hv
  have hα : form σ J v e ∈ 𝔞⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff h0]
    intro z hz
    have := hO _ (he _ (hs z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hβ : form σ J v y ∈ 𝔞 := by
    have h0' : 𝔞⁻¹ ≠ 0 := inv_ne_zero h0
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff h0']
    intro z hz
    have := hO _ (hy _ (Stab.inv hσ hs h0 z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hγ : t * form σ J v e ∈ 𝔞 := by
    have := FractionalIdeal.mul_mem_mul ht hα
    rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this
  have hvec : rowE σ J e y t *ᵥ v =
      v + form σ J v e • y + (t * form σ J v e) • e - form σ J v y • e := by
    rw [rowE_mulVec, smul_add, smul_smul, mul_comm (form σ J v e) t, add_assoc]
  rw [hvec]
  exact Λ.sub_mem (Λ.add_mem (Λ.add_mem hv (hy _ hα)) (he _ hγ)) (he _ hβ)

end Lat

end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

theorem form_col_col {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (b c : Fin m) :
    form σ J (fun i => P i b) (fun i => P i c) = pairM σ J P P c b := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

open GlobalTheory.SnMass.FrameDual in
theorem rowE_mem_GN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a y t hyc hyt hyΛ htI
  obtain ⟨hcm, -, hJ, hΛ, hP, -, htup, -⟩ := hV
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσ : ∀ x, σ' (σ' x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h := hcm.2.2.2 τ
    simp only [hσ', AlgHom.coe_toRingHom, h, star_star]
  have hJ' : ∀ i j, σ' (J j i) = J i j := hJ.1
  have hyt' : form σ' J y y + t + σ' t = 0 := hyt
  set e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc with he_def
  set 𝔞 : FractionalIdeal (𝓞 E)⁰ E := dInv E (r - a.val) with h𝔞
  have heb : ∀ b c : Fin r, form σ' J (fun i => P i b.castSucc) (fun i => P i c.castSucc) = 0 := by
    intro b c
    rw [form_col_col, hP.2, TF, Matrix.diagonal_apply]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 (Fin.castSucc_ne_last c)
  have hee : form σ' J e e = 0 := heb a a
  have hye : form σ' J y e = 0 := hyc a le_rfl
  have hyb : ∀ b : Fin r, b ≤ a → form σ' J (fun i => P i b.castSucc) y = 0 := by
    intro b hb
    rw [form_herm σ' J hσ hJ', hyc b hb, map_zero]
  have h0 : 𝔞 ≠ 0 := dInv_ne_zero _
  have hs : Stab σ' 𝔞 := stab_dInv hσ _
  have he𝔞 : ∀ c ∈ 𝔞, c • e ∈ Λ := by
    intro c hc
    refine htup (Submodule.subset_span ⟨Fin.castAdd r a.castSucc, c, ?_, ?_⟩)
    · rw [frameDualTupleIdeals_castAdd]; exact hc
    · funext i
      simp [sideM, he_def]
  have ht2 : t ∈ 𝔞 * 𝔞 := by
    rw [h𝔞, SgGlob.dInv, ← pow_add, ← two_mul]
    exact htI
  refine ⟨⟨isUn_of_form σ' J _ (form_rowE hσ hJ' hee hye hyt'), ?_, ?_⟩, ?_⟩
  · refine ⟨Matrix.of fun i j => (if i = j then 1 else 0) -
        (if i = a then form σ' J (fun l => P l j.castSucc) y else 0), ?_, ?_⟩
    · intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have hne : i ≠ j := (ne_of_lt hji).symm
        by_cases hia : i = a
        · subst hia
          simp [hne, hyb j (le_of_lt hji)]
        · simp [hne, hia]
      · subst hij
        by_cases hia : i = a
        · subst hia
          simp [hyb i le_rfl]
        · simp [hia]
    · ext l j
      change (rowE σ' J e y t *ᵥ fun m => P m j.castSucc) l = ∑ i : Fin r, P l i.castSucc *
        ((if i = j then 1 else 0) - (if i = a then form σ' J (fun l => P l j.castSucc) y else 0))
      rw [rowE_mulVec, heb j a]
      simp only [Matrix.of_apply, eOf, Matrix.submatrix_apply, id, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, he_def]
      ring
  · intro v hv
    have hve : form σ' J v e = 0 := by
      have := congrFun hv a
      rw [← Matrix.mulVec_mulVec] at this
      simpa [form, cT, mulVec, dotProduct, eOf, he_def] using this
    refine ⟨Pi.single a (-form σ' J v y), ?_⟩
    rw [rowE_mulVec, hve, Matrix.mulVec_single]
    ext l
    simp [eOf, he_def] <;> ring
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact rowE_mem hσ hΛ h0 hs he𝔞 hyΛ ht2 hv
    · intro v hv
      have hy' : ∀ c ∈ 𝔞⁻¹, c • (-y) ∈ Λ := fun c hc => by
        rw [smul_neg]; exact Λ.neg_mem (hyΛ c hc)
      refine ⟨rowE σ' J e (-y) (σ' t) *ᵥ v, rowE_mem hσ hΛ h0 hs he𝔞 hy' (hs.mul hs t ht2) hv, ?_⟩
      exact rowE_inv hσ hJ' hee hye hyt' v

end GlobalTheory.SnMass.VolN.RowIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  first | exact @GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN | exact GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN | (intros; apply GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

variable {E : Type} [Field E] [NumberField E]

def reV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).re

def imV (x : E) : InfinitePlace E → ℝ := fun w => (w.embedding x).im

end GlobalTheory.SnMass.SkewVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.St

theorem siegelWeil_volumes : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J ∧ Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J := by
  intro hSW F E _ _ _ _ _ σ hσ n J hJ

  exact hSW F E σ hσ n J hJ

end GlobalTheory.St
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitary
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.WeylUnitary

theorem delSq_irreducible_unitary :
    ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  intro n lam
  rw [← Formalism.L2.Col.nablaSq_eq_delSq ℂ lam]
  have ha : Antitone lam.natW := fun i j hij => by
    have := lam.anti hij
    simp only [DomWeight.natW]
    omega
  refine ⟨GlobalTheory.Branching.finite_nablaSq ℂ n lam, rfl,
    fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ g p hp, fun U hle hU => ?_⟩
  rw [or_iff_not_imp_left]
  intro hne
  exact le_antisymm hle (GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl _ ha U hle
    (GlobalTheory.Branching.rowDivClosed_of_rowAct_stable U (GlobalTheory.Branching.rowAct_mem_of_unitary_stable U hU)) hne)

end GlobalTheory.WeylUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DelSqIrreducibleUnitaryStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delSq_unitary_stable_and_irreducible : ∀ (n : ℕ) (lam : DomWeight n), FiniteDimensional ℂ (delSq ℂ n lam) ∧ delSq ℂ n lam = nablaSq ℂ n lam ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ delSq ℂ n lam, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam) ∧ ∀ U : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ), U ≤ delSq ℂ n lam → (∀ g ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ p ∈ U, Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ U) → U = ⊥ ∨ U = delSq ℂ n lam := by
  first | exact @GlobalTheory.WeylUnitary.delSq_irreducible_unitary | exact GlobalTheory.WeylUnitary.delSq_irreducible_unitary | (intros; apply GlobalTheory.WeylUnitary.delSq_irreducible_unitary <;> assumption)
end
end
