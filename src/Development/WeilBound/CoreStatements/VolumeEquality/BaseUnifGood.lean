module

public import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitary
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelNormalFormOfHermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainIffPosDef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicPeriodFamily
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CongruenceSubgroupOfFormAutomorphisms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbCompInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem labelEmb_comp_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H)
    (c : Coeff l) (κ : c.F →+* ℂ), Function.Injective fun lab : CMType H ⊕ CMType H => κ.comp (labelEmb c lab) := by
  intro E _ _ _ H l c κ a b h
  exact LabelCount.labelEmb_injective c (RingHom.ext fun x => κ.injective (RingHom.congr_fun h x))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifSig
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def HasRk (H : Host E) (p q : ℕ) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : Prop :=
  ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then p else q

theorem label_conj (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inr τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inl τ))) := by
  refine RingHom.ext fun a => ?_
  let ψ : E →+* ℂ := κ.comp (τ.1.codRestrict c.F (c.conj τ.1))
  show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem label_conj' (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inl τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inr τ))) := by
  rw [label_conj]
  exact RingHom.ext fun a => by simp

theorem label_bij (κ : c.F →+* ℂ) : Function.Bijective fun lab : CMType H ⊕ CMType H => κ.comp (labelEmb c lab) :=
  LabPt.bijective_of_injective H _ (FamEx.labelEmb_comp_injective E H l c κ)

theorem label_cm (κ : c.F →+* ℂ) :
    IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inl τ))) ∧ IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inr τ))) := by
  refine LabPt.isCMFam_of_bijective _ _ ?_ (label_conj κ)
  convert label_bij (c := c) κ using 1
  funext s
  rcases s with τ | τ <;> rfl

theorem hasRk_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    HasRk H p q R ↔ ∀ τ : CMType H, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inl τ)))) = p ∧
      Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inr τ)))) = q := by
  have hne : -H.rt0 ≠ H.rt0 := fun e => FamEx.rt0_ne_zero H (by linear_combination (-1/2 : ℂ) * e)
  constructor
  · intro h τ
    obtain ⟨s, hs, hv⟩ := FamEx.exists_emb_label E H l c κ (.inl τ)
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ (.inr τ)
    have e := hv ρ hρ
    have e' := hv' ρ hρ
    simp only [Sum.elim_inl, Sum.elim_inr, hκ] at e e'
    rw [hs, hs', h s, h s', if_pos e, if_neg (by rw [e']; exact hne)]
    exact ⟨rfl, rfl⟩
  · intro h s
    obtain ⟨lab, hl⟩ := (label_bij (c := c) κ).2 (s.comp (algebraMap (𝓞 E) E))
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ lab
    have e := hv' ρ hρ
    have hl' : κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) := hl
    have e2 : s (H.rt : E) = s' (H.rt : E) := RingHom.congr_fun (hl'.symm.trans hs') H.rt
    rw [← hl', e2, e]
    rcases lab with τ | τ
    · simp only [Sum.elim_inl, hκ, if_true]
      exact (h τ).1
    · simp only [Sum.elim_inr, hκ, if_neg hne]
      exact (h τ).2

theorem hasSig_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ)
    (sm : CMType H → CMType H ⊕ CMType H) (j j' : ℕ)
    (hs : sm = Sum.inr ∧ j = p ∧ j' = q ∨ sm = Sum.inl ∧ j = q ∧ j' = p) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H p q R := by
  rw [hasRk_iff κ ρ hρ hκ]
  refine forall_congr' fun τ => ?_
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [label_conj' κ τ]
    exact and_comm
  · rw [label_conj κ τ]

theorem side_cm (κ : c.F →+* ℂ) (sm : CMType H → CMType H ⊕ CMType H) (hs : sm = Sum.inr ∨ sm = Sum.inl) :
    IsCMFam fun τ => κ.comp (labelEmb c (sm τ)) := by
  rcases hs with rfl | rfl
  · exact (label_cm κ).2
  · exact (label_cm κ).1

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivC
section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivB
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ.Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def Tan (_ : RiemLat E g Λ) : Type := Fin g → ℂ

instance (R : RiemLat E g Λ) : AddCommGroup (Tan R) := inferInstanceAs (AddCommGroup (Fin g → ℂ))

instance (R : RiemLat E g Λ) : Module ℂ (Tan R) := inferInstanceAs (Module ℂ (Fin g → ℂ))

instance (R : RiemLat E g Λ) : FiniteDimensional ℂ (Tan R) := inferInstanceAs (FiniteDimensional ℂ (Fin g → ℂ))

theorem ip_conj' (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  rw [← ip_conj' R y, ip_add_right', map_add (f := _), ip_conj', ip_conj']

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = starRingEnd ℂ c * R.ip x y := by
  rw [← ip_conj' R y, ip_smul_right', map_mul, ip_conj']

theorem ip_self_nonneg' (R : RiemLat E g Λ) (x : Fin g → ℂ) : 0 ≤ (R.ip x x).re := by
  by_cases hx : x = 0
  · subst hx
    simp [RiemLat.ip]
  · exact (R.pos x hx).le

theorem ip_self_zero' (R : RiemLat E g Λ) {x : Fin g → ℂ} (h : R.ip x x = 0) : x = 0 := by
  by_contra hx
  have := R.pos x hx
  change 0 < (R.ip x x).re at this
  rw [h] at this
  simp at this

def core (R : RiemLat E g Λ) : InnerProductSpace.Core ℂ (Tan R) where
  inner x y := R.ip x y
  conj_inner_symm x y := ip_conj' R y x
  re_inner_nonneg x := ip_self_nonneg' R x
  add_left x y z := ip_add_left' R x y z
  smul_left x y r := ip_smul_left' R r x y
  definite x h := ip_self_zero' R h

theorem exists_orthoBasis (R : RiemLat E g Λ) (S : Submodule ℂ (Fin g → ℂ)) (m : ℕ)
    (h : Module.finrank ℂ S = m) :
    ∃ e : Fin m → Fin g → ℂ, (∀ c, e c ∈ S) ∧ (∀ a b, R.ip (e a) (e b) = if a = b then 1 else 0) ∧
      S ≤ Submodule.span ℂ (Set.range e) := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let S' : Submodule ℂ (Tan R) := S
  have h' : Module.finrank ℂ S' = m := h
  let b := (stdOrthonormalBasis ℂ S').reindex (finCongr h')
  refine ⟨fun c => ((b c : S') : Tan R), fun c => (b c).2, fun x y => ?_, fun x hx => ?_⟩
  · exact orthonormal_iff_ite.1 b.orthonormal x y
  · have hb : Submodule.span ℂ (Set.range b) = ⊤ := by simpa using b.toBasis.span_eq
    have hm := congrArg (Submodule.map S'.subtype) hb
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hm
    have hx' : x ∈ S' := hx
    rw [← hm] at hx'
    exact hx'

theorem linearIndependent_of_ortho (R : RiemLat E g Λ) {I : Type} [DecidableEq I] (c : I → Fin g → ℂ)
    (h : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) : LinearIndependent ℂ c := by
  letI : NormedAddCommGroup (Tan R) := (core R).toNormedAddCommGroup
  letI : InnerProductSpace ℂ (Tan R) := InnerProductSpace.ofCore (core R).toCore
  let c' : I → Tan R := c
  have ho : Orthonormal ℂ c' := orthonormal_iff_ite.2 h
  exact ho.linearIndependent

variable {Ψ : Type} [Fintype Ψ]

theorem cm_ne {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (τ τ' : Ψ) :
    σ τ ≠ (starRingEnd ℂ).comp (σ τ') := fun h =>
  ((hσ.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, h⟩

theorem conj_comp_conj (s : 𝓞 E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem cm_cover {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) (s : 𝓞 E →+* ℂ) :
    (∃ τ, σ τ = s) ∨ ∃ τ, (starRingEnd ℂ).comp (σ τ) = s := by
  by_cases h : ∃ τ, σ τ = s
  · exact Or.inl h
  · right
    have h2 : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
      by_contra h3
      exact h ((hσ.2 s).2 h3)
    obtain ⟨τ, hτ⟩ := h2
    exact ⟨τ, by rw [hτ, conj_comp_conj]⟩

theorem exists_ortho_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (hσ : IsCMFam σ) (hs : R₀.HasSig σ j j') :
    ∃ (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) ∧
      ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
  obtain ⟨-, -, h3, h4, h5⟩ := SheetDecomposition.riemBasic E g Λ Ψ R₀
  choose f hf1 hf2 hf3 using fun τ => exists_orthoBasis R₀ _ j' (hs τ).1
  choose f' hf1' hf2' hf3' using fun τ => exists_orthoBasis R₀ _ j (hs τ).2
  let c : Ix Ψ j j' → Fin g → ℂ := fun i => Sum.elim (f i.2) (f' i.2) i.1
  have hmem : ∀ i, c i ∈ eigSp R₀.B (emb σ i) := by
    rintro ⟨a | a, τ⟩
    · exact hf1 τ a
    · exact hf1' τ a
  have hinj' : ∀ {τ τ' : Ψ}, τ ≠ τ' → (starRingEnd ℂ).comp (σ τ) ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' hne h
    apply hne
    apply hσ.1
    rw [← conj_comp_conj (σ τ), h, conj_comp_conj]
  have hort : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0 := by
    rintro ⟨a | a, τ⟩ ⟨b | b, τ'⟩
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2 τ a b
        simpa [c] using this
      · have := h5 _ _ (fun h => ht (hσ.1 h)) _ (hf1 τ a) _ (hf1 τ' b)
        simpa [c, ht] using this
    · have := h5 _ _ (cm_ne hσ τ τ') _ (hf1 τ a) _ (hf1' τ' b)
      simpa [c] using this
    · have := h5 _ _ (cm_ne hσ τ' τ).symm _ (hf1' τ a) _ (hf1 τ' b)
      simpa [c] using this
    · by_cases ht : τ = τ'
      · subst ht
        have := hf2' τ a b
        simpa [c] using this
      · have := h5 _ _ (hinj' ht) _ (hf1' τ a) _ (hf1' τ' b)
        simpa [c, ht] using this
  have hli : LinearIndependent ℂ c := linearIndependent_of_ortho R₀ c hort
  have hsp1 : ∀ τ, eigSp R₀.B (σ τ) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3 τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inl a, τ), rfl⟩))
  have hsp2 : ∀ τ, eigSp R₀.B ((starRingEnd ℂ).comp (σ τ)) ≤ Submodule.span ℂ (Set.range c) := fun τ =>
    (hf3' τ).trans (Submodule.span_mono (by
      rintro _ ⟨a, rfl⟩
      exact ⟨(Sum.inr a, τ), rfl⟩))
  have hsp : ∀ s : 𝓞 E →+* ℂ, eigSp R₀.B s ≤ Submodule.span ℂ (Set.range c) := by
    intro s
    rcases cm_cover hσ s with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · exact hsp1 τ
    · exact hsp2 τ
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range c) := by
    intro x _
    rw [← h4 x]
    exact Submodule.sum_mem _ fun s _ => hsp _ ((h3 _).1 x)
  have hcard : Fintype.card (Ix Ψ j j') = g := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    simpa using this.symm
  exact ⟨Fintype.equivFinOfCardEq hcard, c, hmem, hort⟩

end SheetDecomposition.Univ.Frame
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifUnivA
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

theorem imH_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    ((z + z') ⬝ᵥ M *ᵥ star w).im = (z ⬝ᵥ M *ᵥ star w).im + (z' ⬝ᵥ M *ᵥ star w).im := by
  rw [add_dotProduct, Complex.add_im]

theorem imH_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    ((r • z) ⬝ᵥ M *ᵥ star w).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  rw [smul_dotProduct, Complex.smul_im, smul_eq_mul]

theorem imH_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (w + w')).im = (z ⬝ᵥ M *ᵥ star w).im + (z ⬝ᵥ M *ᵥ star w').im := by
  rw [star_add, mulVec_add, dotProduct_add, Complex.add_im]

theorem imH_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (r • w)).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  have h : star (r • w) = (r : ℂ) • star w := by
    ext i
    simp
  rw [h, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]

theorem exists_realExt {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (hf : R'.form = R.form) :
    ∃ L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ x, L (R.P x) = R'.P x) ∧
      (∀ z w, (L z ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (z ⬝ᵥ R.Hm *ᵥ star w).im) ∧
      ∀ a z, L (R.B a z) = R'.B a (L z) := by
  classical
  haveI := R.free
  haveI := R.fin
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (SheetDecomposition.riemBasic E g Λ Unit R).2.1
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ R.rank
  let v : Fin (2 * g) → Fin g → ℂ := fun k => R.P (b k)
  have hsum : ∀ (Q : Λ →+ (Fin g → ℂ)) (x : Λ), Q x = ∑ k, (b.repr x k : ℝ) • Q (b k) := by
    intro Q x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hv : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hsum R.P x]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  let c : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ) := basisOfTopLeSpanOfCardEqFinrank v hv hcard
  have hc : ∀ k, c k = R.P (b k) := fun k => by
    simp [c, v, coe_basisOfTopLeSpanOfCardEqFinrank]
  let L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := c.constr ℝ fun k => R'.P (b k)
  have hLb : ∀ k, L (R.P (b k)) = R'.P (b k) := fun k => by
    rw [← hc k]
    exact c.constr_basis ℝ _ k
  have hL : ∀ x, L (R.P x) = R'.P x := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum R.P x, hsum R'.P x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hLb]
  have hall : ∀ z : Fin g → ℂ, z ∈ Submodule.span ℝ (Set.range R.P) := fun z => hspan ▸ Submodule.mem_top
  refine ⟨L, hL, ?_, ?_⟩
  · have h1 : ∀ (x : Λ) (w : Fin g → ℂ),
        (L (R.P x) ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (R.P x ⬝ᵥ R.Hm *ᵥ star w).im := by
      intro x w
      induction hall w using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨y, rfl⟩ := hw
        rw [hL, hL, R'.im, R.im, hf]
      | zero => simp
      | add w w' _ _ h h' => rw [map_add (f := _), imH_add_right, imH_add_right, h, h']
      | smul r w _ h => rw [map_smul, imH_smul_right, imH_smul_right, h]
    intro z w
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact h1 x w
    | zero => simp
    | add z z' _ _ h h' => rw [map_add (f := _), imH_add_left, imH_add_left, h, h']
    | smul r z _ h => rw [map_smul, imH_smul_left, imH_smul_left, h]
  · intro a z
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← R.act, hL, hL, R'.act]
    | zero => simp
    | add z z' _ _ h h' => simp only [map_add (f := _), h, h']
    | smul r z _ h =>
      rw [LinearMap.map_smul_of_tower, map_smul, h, map_smul, LinearMap.map_smul_of_tower]

end SheetDecomposition.Univ
end
end

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

section Tz

variable {I : Type} [Fintype I]

theorem tz_add (Z : Matrix I I ℂ) (z w : I → ℂ) : tz Z (z + w) = tz Z z + tz Z w := by
  simp only [tz, star_add, mulVec_add]
  abel

theorem tz_I (Z : Matrix I I ℂ) (z : I → ℂ) :
    tz Z (Complex.I • z) = Complex.I • (z + Z *ᵥ star z) := by
  have h : star (Complex.I • z) = (-Complex.I) • star z := by
    funext i
    simp
  rw [tz, h, mulVec_smul, smul_add]
  funext i
  simp

def tzR (Z : Matrix I I ℂ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) where
  toFun := tz Z
  map_add' := tz_add Z
  map_smul' r z := by
    have h : star (r • z) = r • star z := by
      funext i
      simp
    simp only [tz, h, RingHom.id_apply, smul_sub]
    rw [mulVec_smul]

theorem tz_support [DecidableEq I] (Z : Matrix I I ℂ) (d : I → ℂ) (M : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (h : ∀ z, tz Z (d * z) = M (tz Z z)) (i k : I) : d i * Z i k = Z i k * star (d k) := by
  have h2 : ∀ z : I → ℂ, d * z + Z *ᵥ star (d * z) = M z + M (Z *ᵥ star z) := by
    intro z
    have e : d * (Complex.I • z) = Complex.I • (d * z) := by
      funext i
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := h (Complex.I • z)
    rw [e, tz_I, tz_I, map_smul, map_add (f := _)] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h1 : ∀ z : I → ℂ, d * z - Z *ᵥ star (d * z) = M z - M (Z *ᵥ star z) := by
    intro z
    have := h z
    rwa [tz, tz, map_sub] at this
  have h3 : ∀ z : I → ℂ, d * z = M z := by
    intro z
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star (d * z) = d * (Z *ᵥ star z) := by
    intro z
    rw [h3 (Z *ᵥ star z)]
    funext a
    have a1 := congrFun (h1 z) a
    have a2 := congrFun (h2 z) a
    simp only [Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a2 - a1) / 2
  have := congrFun (h4 (Pi.single k 1)) i
  have s1 : star (d * (Pi.single k 1 : I → ℂ)) = Pi.single k (star (d k)) := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s1, s2] at this
  simp only [Pi.mul_apply, mulVec_single, MulOpposite.op_mul] at this
  simpa [mul_comm] using this.symm

theorem tz_unique [DecidableEq I] (S : Set (I → ℂ)) (hS : Submodule.span ℝ S = ⊤) (A A' : (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (Z Z' : Matrix I I ℂ) (h : ∀ z ∈ S, A (tz Z z) = A' (tz Z' z)) : Z = Z' := by
  have hall : ∀ z, A (tz Z z) = A' (tz Z' z) := by
    have hf : (A.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z = (A'.toLinearMap.restrictScalars ℝ) ∘ₗ tzR Z' :=
      LinearMap.ext_on hS fun z hz => h z hz
    exact fun z => LinearMap.congr_fun hf z
  have h2 : ∀ z : I → ℂ, A (z + Z *ᵥ star z) = A' (z + Z' *ᵥ star z) := by
    intro z
    have := hall (Complex.I • z)
    rw [tz_I, tz_I, map_smul, map_smul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : ∀ z : I → ℂ, A z = A' z := by
    intro z
    funext a
    have a1 := congrFun (hall z) a
    have a2 := congrFun (h2 z) a
    simp only [tz, map_sub, map_add (f := _), Pi.sub_apply, Pi.add_apply] at a1 a2
    linear_combination (a1 + a2) / 2
  have h4 : ∀ z : I → ℂ, Z *ᵥ star z = Z' *ᵥ star z := by
    intro z
    apply A.injective
    have := h2 z
    rw [map_add (f := _), map_add (f := _), h3 z] at this
    rw [h3 (Z' *ᵥ star z)]
    exact add_left_cancel this
  ext i k
  have := congrFun (h4 (Pi.single k 1)) i
  have s2 : star (Pi.single k 1 : I → ℂ) = Pi.single k 1 := by
    funext a
    by_cases hak : a = k
    · subst hak
      simp
    · simp [Pi.single_eq_of_ne hak]
  rw [s2] at this
  simpa using this

end Tz

section Big

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ}

theorem bigZe_symm (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (bigZe e q t)ᵀ = bigZe e q t := by
  unfold bigZe bigZ
  rw [transpose_submatrix, blockDiagonal_transpose]
  congr 2
  funext τ
  rw [fromBlocks_transpose]
  simp

theorem bigZ_entry (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) (a : Fin j) (b : Fin j') :
    bigZ q t (Sum.inr a, τ) (Sum.inl b, τ) = t (q (τ, a, b)) := by
  simp [bigZ, blockDiagonal_apply_eq, ballMat]

theorem bigZe_injective (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    Function.Injective (bigZe e q) := by
  intro t t' h
  funext k
  obtain ⟨⟨τ, a, b⟩, rfl⟩ := q.surjective k
  have := congrFun (congrFun h (e (Sum.inr a, τ))) (e (Sum.inl b, τ))
  simpa [bigZe, bigZ_entry] using this

theorem bigZ_hol (q : Ψ × Fin j × Fin j' ≃ Fin n) (i k : Ix Ψ j j') :
    Differentiable ℂ (fun t => bigZ q t i k) := by
  obtain ⟨a, τ⟩ := i
  obtain ⟨b, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases a with a | a <;> rcases b with b | b <;>
      simp [bigZ, blockDiagonal_apply_eq, ballMat, differentiable_apply]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem bigZe_hol (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (z : Fin g → ℂ) :
    Differentiable ℂ (fun t => tz (bigZe e q t) z) := by
  refine differentiable_pi.2 fun i => ?_
  simp only [tz, Pi.sub_apply, mulVec, dotProduct, bigZe, submatrix_apply]
  refine (differentiable_const _).sub (Differentiable.fun_sum fun k _ => ?_)
  exact (bigZ_hol q _ _).mul_const _

end Big

theorem member {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R₁ : RiemLat E g Λ) (Z : Matrix (Fin g) (Fin g) ℂ) (hH : R₁.Hm = 1) (hs : Zᵀ = Z) (hp : (1 - Zᴴ * Z).PosDef)
    (hc : ∀ a x, tz Z (R₁.B a x) = R₁.B a (tz Z x)) :
    ∃ R : RiemLat E g Λ, R.form = R₁.form ∧ R.B = R₁.B ∧ R.Hm = (1 - Zᴴ * Z)⁻¹ ∧ ∀ x, R.P x = tz Z (R₁.P x) := by
  have hinv : ((1 - Zᴴ * Z)⁻¹).PosDef := hp.inv
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x => tz Z (R₁.P x)
      map_zero' := by simp [tz]
      map_add' := fun x y => by rw [map_add (f := _), tz_add] }
  refine ⟨{ free := R₁.free, fin := R₁.fin, rank := R₁.rank, form := R₁.form, alt := R₁.alt, unimod := R₁.unimod,
            adj := R₁.adj, P := P, Hm := (1 - Zᴴ * Z)⁻¹, herm := hinv.isHermitian, pos := ?_, im := ?_, B := R₁.B,
            act := ?_ }, rfl, rfl, rfl, fun _ => rfl⟩
  · intro z hz
    have h := (Matrix.posDef_iff_dotProduct_mulVec.1 hinv).2 (x := star z) (by simpa using hz)
    rw [star_star, Complex.lt_def] at h
    exact h.1
  · intro x y
    show (tz Z (R₁.P x) ⬝ᵥ (1 - Zᴴ * Z)⁻¹ *ᵥ star (tz Z (R₁.P y))).im = _
    rw [GlobalTheory.T.siegel_transform_symplectic_imaginary Z hs hp, ← R₁.im, hH, one_mulVec]
  · intro a x
    show tz Z (R₁.P (a • x)) = R₁.B a (tz Z (R₁.P x))
    rw [R₁.act, hc]

theorem exists_univFam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ R₀ σ q hσ hsig
  classical
  obtain ⟨e, c, hc, hco⟩ := Frame.exists_ortho_frame R₀ σ hσ hsig
  obtain ⟨R₁, hform, hHm, hB⟩ := GlobalTheory.T.exists_normalized_riemann_lattice R₀ σ e c hc hco
  have hmem : ∀ t, ∃ R : RiemLat E g Λ, R.form = R₀.form ∧ (t ∈ ballDom q → R.B = R₁.B ∧
      R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ ∧ ∀ x, R.P x = tz (bigZe e q t) (R₁.P x)) := by
    intro t
    by_cases ht : t ∈ ballDom q
    · obtain ⟨R, h1, h2, h3, h4⟩ := member R₁ (bigZe e q t) hHm (bigZe_symm e q t)
        ((GlobalTheory.T.ball_domain_iff_pos_def e q t).1 ht) (GlobalTheory.T.siegel_transform_commutes_action σ e q t R₁.B hσ hB)
      exact ⟨R, h1.trans hform, fun _ => ⟨h2, h3, h4⟩⟩
    · exact ⟨R₁, hform, fun h => absurd h ht⟩
  choose R hRf hR using hmem
  have hfr := GlobalTheory.T.span_standard_basis_eigenspace σ e R₁.B hσ hB
  have hli : ∀ {m : ℕ} (f : Fin m → Ix Ψ j j'), Function.Injective f →
      LinearIndependent ℂ (fun i : Fin m => (Pi.single (e (f i)) 1 : Fin g → ℂ)) := by
    intro m f hf
    have := (Pi.basisFun ℂ (Fin g)).linearIndependent.comp (fun i => e (f i))
      (e.injective.comp hf)
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  have hl : ∀ τ, LinearIndependent ℂ (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inl i, τ)) (fun a b h => by simpa using h)
  have hr : ∀ τ, LinearIndependent ℂ (fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) := fun τ =>
    hli (fun i => (Sum.inr i, τ)) (fun a b h => by simpa using h)
  refine ⟨{ q := q, σ := σ, cm := hσ, form := R₀.form, R := R, form_eq := hRf,
            hol := ?_, sig := ?_, b := fun τ i _ => Pi.single (e (Sum.inl i, τ)) 1,
            frames := ?_, logDet_eq := ?_, univ := ?_ }, rfl, rfl, rfl⟩
  · refine ⟨fun t _ t' _ => (hRf t).trans (hRf t').symm, fun x => ?_⟩
    exact ((bigZe_hol e q (R₁.P x)).differentiableOn).congr fun t ht => (hR t ht).2.2 x
  · intro t ht τ
    rw [(hR t ht).1, ← (hfr τ).1, ← (hfr τ).2]
    exact ⟨by rw [finrank_span_eq_card (hl τ)]; simp, by rw [finrank_span_eq_card (hr τ)]; simp⟩
  · refine ⟨fun τ i => differentiableOn_const _, fun t ht τ => ⟨hl τ, ?_⟩⟩
    show _ = eigSp (R t).B (σ τ)
    rw [(hR t ht).1]
    exact (hfr τ).1
  · intro t ht
    exact GlobalTheory.T.log_det_eq_ball_potential e q t (R t) ht (hR t ht).2.1
  · intro R' hR' _
    obtain ⟨L, hL1, hL2, hL3⟩ := exists_realExt R₁ R' (hR'.trans hform.symm)
    obtain ⟨A, Z, hZs, hZp, hLZ⟩ := GlobalTheory.T.siegel_normal_form_of_hermitian L R'.Hm R'.herm R'.pos (by
      intro z w
      rw [hL2, hHm, one_mulVec])
    have hsupp : ∀ (a : 𝓞 E) i k, emb σ (e.symm i) a * Z i k = Z i k * star (emb σ (e.symm k) a) := by
      intro a
      refine tz_support Z (fun k => emb σ (e.symm k) a)
        (A.symm.toLinearMap ∘ₗ (R'.B a) ∘ₗ A.toLinearMap) fun z => ?_
      have hz : (fun k => emb σ (e.symm k) a) * z = R₁.B a z := by
        funext k
        simp [hB]
      apply A.injective
      rw [hz]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← hLZ, ← hLZ, hL3]
    have hZ0 : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft := by
      intro i k hik
      refine (GlobalTheory.T.conjugate_embeddings_criterion σ hσ (e.symm i) (e.symm k)).1 fun a => ?_
      have := hsupp a i k
      rw [mul_comm] at this
      exact mul_left_cancel₀ hik this
    obtain ⟨t, rfl⟩ := GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe e q Z hZs hZ0
    have ht : t ∈ ballDom q := (GlobalTheory.T.ball_domain_iff_pos_def e q t).2 hZp
    refine ⟨t, ⟨ht, A, fun x => ?_⟩, ?_⟩
    · rw [(hR t ht).2.2 x, ← hLZ, hL1]
      rfl
    · rintro t' ⟨ht', h', hh⟩
      have hspan := (SheetDecomposition.riemBasic E g Λ Ψ R₁).2.1
      refine bigZe_injective e q (tz_unique _ hspan h' A _ _ ?_)
      rintro _ ⟨x, rfl⟩
      rw [← (hR t' ht').2.2 x, ← hh x, ← hLZ, hL1]
      rfl

end SheetDecomposition.Univ

theorem SheetDecomposition.univExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsCMFam σ → R₀.HasSig σ j j' → ∃ F : UnivFam E Ψ j j' n g Λ, F.q = q ∧ F.σ = σ ∧ F.form = R₀.form :=
  SheetDecomposition.Univ.exists_univFam
end
end

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem exists_equiv_of_det {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (hd : IsUnit h.det) :
    ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e z = h *ᵥ z :=
  ⟨h.toLinearEquiv' (h.invertibleOfIsUnitDet hd), fun z => Matrix.toLin'_apply h z⟩

theorem u_eq_of_equiv {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σ ty) (i : Fin FU.n)
    {P P' Q : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P) (hP' : IsPeriod (FU.Di i) ty P')
    (e e' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ x, P x = e (Q x)) (he' : ∀ x, P' x = e' (Q x)) :
    FU.u i P = FU.u i P' :=
  (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, e.symm.trans e', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
    fun a => ⟨0, by simp⟩, fun a => by simp [he, he']⟩

theorem j_over (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (x : Sp ℂ ⟶ Xo.XF c)
    (hx : x ≫ pullback.snd _ _ = spMap κ) : (x ≫ Y.j) ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) := by
  rw [Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hx,
    spMap_comp]

theorem j_inj (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {x x' : Sp ℂ ⟶ Xo.XF c}
    (hx : x ≫ pullback.snd _ _ = x' ≫ pullback.snd _ _) (h : x ≫ Y.j = x' ≫ Y.j) : x = x' := by
  have := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · simpa [Model.j] using h
  · rw [Category.assoc, Category.assoc, Y.jQ_over, hx]

theorem j_interior (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (x : Sp ℂ ⟶ Xo.XF c) :
    centre (x ≫ Y.j) ∈ abLocus Y.t.G := by
  have h : Y.jQ (centre x) ∈ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  exact h

theorem exists_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Y.X)
    (hp : centre p ∈ abLocus Y.t.G) (hs : p ≫ Y.s = spMap (κ.comp (algebraMap (𝓞 c.F) c.F))) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ Y.j = p ∧ x ≫ pullback.snd _ _ = spMap κ := by
  have hc : p ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp]
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift p (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = p := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact hp
  have hx : IsOpenImmersion.lift Y.jQ w hr ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

theorem isHolTo_of_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (κ : c.F →+* ℂ) {m : ℕ} {T : Set (Fin m → ℂ)}
    {x : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.XF c)} (hT : IsOpen T) (hs : ∀ b, x b ≫ pullback.snd _ _ = spMap κ)
    (h : IsHolTo T fun b => x b ≫ Y.j) : IsHolTo T x := by
  have := Y.jQ_open
  have he : ∀ b, (x b ≫ Y.j) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun b => by
    rw [j_over Y κ _ (hs b), spMap_comp]
  have hq : ∀ b, x b ≫ Y.jQ = pullback.lift (x b ≫ Y.j) (spMap κ) (he b) := fun b => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
      rfl
    · rw [pullback.lift_snd, Category.assoc, Y.jQ_over, hs]
  have h₃ : IsHolTo T fun b => x b ≫ Y.jQ := by
    have := PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) m T (fun b => x b ≫ Y.j) (fun _ => spMap κ) he hT h
      (PullbackSections.isHolTo_spMap hT (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    simpa only [hq] using this
  exact Flat.isHolTo_of_comp_openImmersion Y.jQ h₃

set_option maxHeartbeats 1600000 in
theorem kUnif_good (hV : VecOfPeriods) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H)
    (j j' n g : ℕ) (q : CMType H × Fin j × Fin j' ≃ Fin n) (κ : c.F →+* ℂ) (ty : Fin g → (E →+* ℂ))
    (hty : IsTypeFn H D.p D.q ty) (hs : sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p)
    (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0)
    (FU : FamilyUnif Xo (κ.comp (IntermediateField.inclusion c.le).toRingHom) ty) :
    Nonempty (KUnif Y sm j j' n g q κ) := by
  classical
  let ι : Type := {i : Fin FU.n // ∃ P, IsPeriod (FU.Di i) ty P}
  have htyi : ∀ i, IsTypeFn H (FU.Di i).p (FU.Di i).q ty := fun i => by
    rw [(FU.sig i).1, (FU.sig i).2]
    exact hty
  have hsig : ∀ {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ),
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H D.p D.q R :=
    fun R => hasSig_iff κ ρ hρ hκ D.p D.q sm j j' hs R
  have hriem : ∀ i P, IsPeriod (FU.Di i) ty P → ∃ R : RiemLat E g (FU.Di i).La, R.P = P ∧ R.form = (FU.Di i).EF ∧
      R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' := fun i P hP => by
    obtain ⟨R, h₁, h₂, -, h₄⟩ := GlobalTheory.T.exists_riemann_lattice_of_period E H (FU.Di i) g ty P (htyi i) hP
    rw [(FU.sig i).1, (FU.sig i).2] at h₄
    exact ⟨R, h₁, h₂, (hsig R).2 h₄⟩
  have hF : ∀ k : ι, ∃ F : UnivFam E (CMType H) j j' n g (FU.Di k.1).La, F.q = q ∧
      F.σ = (fun τ => κ.comp (labelEmb c (sm τ))) ∧ F.form = (FU.Di k.1).EF := fun k => by
    obtain ⟨P, hP⟩ := k.2
    obtain ⟨R, -, h₂, h₃⟩ := hriem _ P hP
    obtain ⟨F, a₁, a₂, a₃⟩ := univExists E (CMType H) j j' n g _ R _ q
      (side_cm κ sm (hs.imp (·.1) (·.1))) h₃
    exact ⟨F, a₁, a₂, a₃.trans h₂⟩
  choose F hq hσ hform using hF
  have hΓ : ∀ k : ι, ∃ Γ : Subgroup ((FU.Di k.1).La ≃ₗ[𝓞 E] (FU.Di k.1).La), (F k).IsArith Γ ∧
      ∀ γ, γ ∈ Γ ↔ InLevel l (FU.Di k.1) γ := fun k => by
    haveI := ((F k).R 0).fin
    obtain ⟨Γ, a₁, a₂, a₃⟩ := GlobalTheory.T.congruence_subgroup_of_form_automorphisms E (FU.Di k.1).La (FU.Di k.1).EF (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) l.M l.A
      (by have := l.three_le; omega) l.A_pos
    refine ⟨Γ, ?_, a₃⟩
    unfold UnivFam.IsArith
    rw [hform]
    exact ⟨a₁, a₂⟩
  choose Γ hΓa hΓm using hΓ
  have hO : IsOpen (ballDom q) := (GlobalTheory.T.ball_domain_open_convex_zero _ j j' n q).1
  have hRf : ∀ k t, ((F k).R t).form = (FU.Di k.1).EF := fun k t => ((F k).form_eq t).trans (hform k)
  have hloc : ∀ k : ι, ∀ t₀ ∈ ballDom q, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → ((FU.Di k.1).La →+ (Fin g → ℂ)))
      (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ ballDom q ∧
      IsHolPeriods (FU.Di k.1) ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧
      ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ ((F k).R t).P x := fun k =>
    GlobalTheory.T.local_holomorphic_period_family E H (FU.Di k.1) g n ty (ballDom q) (F k).R (htyi _) hO (hq k ▸ (F k).hol) fun t ht => ⟨hRf k t, by
      rw [(FU.sig _).1, (FU.sig _).2]
      refine (hsig _).1 ?_
      rw [← hσ k]
      exact (F k).sig t (by rw [hq]; exact ht)⟩
  have hPt : ∀ (k : ι) (t : Fin n → ℂ), ∃ P, IsPeriod (FU.Di k.1) ty P ∧ (t ∈ ballDom q →
      ∃ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, P x = e (((F k).R t).P x)) := fun k t => by
    by_cases ht : t ∈ ballDom q
    · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
      obtain ⟨e, he⟩ := exists_equiv_of_det (h t) (hh t hm).1
      exact ⟨P t, hP.1 t hm, fun _ => ⟨e, fun x => by rw [he, (hh t hm).2]⟩⟩
    · obtain ⟨P, hP⟩ := k.2
      exact ⟨P, hP, fun h => absurd h ht⟩
  choose Pt hPt hPe using hPt
  have hu : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ e : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ x, P x = e (((F k).R t).P x)) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP e he => by
    obtain ⟨e₀, he₀⟩ := hPe k t ht
    exact u_eq_of_equiv FU k.1 (hPt k t) hP e₀ e he₀ he
  have hum : ∀ (k : ι), ∀ t ∈ ballDom q, ∀ P, IsPeriod (FU.Di k.1) ty P → ∀ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h.det →
      (∀ x, P x = h *ᵥ ((F k).R t).P x) → FU.u k.1 (Pt k t) = FU.u k.1 P := fun k t ht P hP h hd hh => by
    obtain ⟨e, he⟩ := exists_equiv_of_det h hd
    exact hu k t ht P hP e fun x => by rw [he, hh]
  have hc : ∀ (k : ι) t, FU.u k.1 (Pt k t) ≫ Xo.s = spMap κ ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    fun k t => by rw [FU.over_σ _ _ (hPt k t), spMap_comp]
  let xF : ι → (Fin n → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun k t => pullback.lift _ _ (hc k t)
  have hx₁ : ∀ k t, xF k t ≫ pullback.fst _ _ = FU.u k.1 (Pt k t) := fun k t => pullback.lift_fst _ _ _
  have hx₂ : ∀ k t, xF k t ≫ pullback.snd _ _ = spMap κ := fun k t => pullback.lift_snd _ _ _
  have hxhol : ∀ k, IsHolTo (ballDom q) (xF k) := fun k => by
    refine PullbackSections.holPair _ _ _ _ _ n _ _ _ (hc k) hO ?_
      (PullbackSections.isHolTo_spMap hO (Ψ := fun _ => κ) fun a => differentiableOn_const _)
    refine GlobalTheory.HolPeriods.isHolTo_of_local fun t₀ ht₀ => ?_
    obtain ⟨V', P, h, hVo, hm, hsub, hP, -, hh⟩ := hloc k t₀ ht₀
    exact ⟨V', hm, hsub, GlobalTheory.HolPeriods.isHolTo_congr (FU.hol _ n V' P hVo hP).1 fun t ht =>
      hum k t (hsub ht) _ (hP.1 t ht) _ (hh t ht).1 (hh t ht).2⟩
  have hpt : ∀ k k' t t', xF k t ≫ Y.j = xF k' t' ≫ Y.j ↔ FU.u k.1 (Pt k t) = FU.u k'.1 (Pt k' t') := fun k k' t t' => by
    constructor
    · intro h
      rw [← hx₁, ← hx₁, j_inj Y ((hx₂ k t).trans (hx₂ k' t').symm) h]
    · intro h
      congr 1
      apply pullback.hom_ext
      · rw [hx₁, hx₁, h]
      · rw [hx₂, hx₂]
  have hmono : ∀ {X : Scheme.{0}} {B B' : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)}, IsHolTo B y → IsOpen B' →
      B' ⊆ B → IsHolTo B' y := fun h hB hsub => GlobalTheory.HolPeriods.isHolTo_comp (φ := id) h hB differentiableOn_id hsub
  refine ⟨{
    ι := ι
    fin := inferInstance
    Di := fun k => FU.Di k.1
    sig := fun k => FU.sig k.1
    F := F
    q_eq := hq
    form_eq := fun k => Or.inl (hform k)
    σ_eq := fun k τ => by rw [hσ]
    Γ := Γ
    mem_Γ := hΓm
    arith := hΓa
    pt := fun k t => xF k t ≫ Y.j
    hol := fun k => PullbackSections.isHolTo_comp (hxhol k) Y.j
    comp_s_eq_spMap_of_isOver := fun k t _ => j_over Y κ _ (hx₂ k t)
    interior := fun k t _ => j_interior Y _
    disj := fun k k' t _ t' _ h => Subtype.ext (FU.disj _ _ _ _ (hPt k t) (hPt k' t') ((hpt k k' t t').1 h))
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hVo hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hpt, FU.fibre _ _ _ (hPt k t) (hPt k t')]
    obtain ⟨e, he⟩ := hPe k t ht
    obtain ⟨e', he'⟩ := hPe k t' ht'
    constructor
    · rintro ⟨γ, h, a₁, a₂, a₃, a₄⟩
      refine ⟨γ, (hΓm k γ).2 ⟨a₁, a₂, a₃⟩, (e.trans h).trans e'.symm, fun x => ?_⟩
      have := a₄ x
      rw [he', he] at this
      simp [← this]
    · rintro ⟨γ, hγ, h, hh⟩
      obtain ⟨a₁, a₂, a₃⟩ := (hΓm k γ).1 hγ
      refine ⟨γ, (e.symm.trans h).trans e', a₁, a₂, a₃, fun x => ?_⟩
      rw [he', he, hh]
      simp
  · obtain ⟨x, hx, hxs⟩ := exists_j Y κ p hp hps
    obtain ⟨i, P, hP, hui⟩ := FU.onto (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
    obtain ⟨R, h₁, h₂, h₃⟩ := hriem i P hP
    let k : ι := ⟨i, P, hP⟩
    obtain ⟨t, ⟨ht, e, he⟩, -⟩ := (F k).univ R (h₂.trans (hform k).symm) (by rw [hσ]; exact h₃)
    rw [hq] at ht
    refine ⟨k, t, ht, ?_⟩
    rw [← hx]
    congr 1
    apply pullback.hom_ext
    · rw [hx₁, ← hui]
      exact hu k t ht P hP e fun a => by rw [← h₁]; exact he a
    · rw [hx₂, hxs]
  · obtain ⟨V', P, h, -, hm, -, hP, -, hh⟩ := hloc k t ht
    have h₁ : FibreLat Xo.univ.t (FU.u k.1 (P t)) ((F k).R t) :=
      GlobalTheory.T.family_period_riemann_lattice E H D l Xo _ g ty FU k.1 ((F k).R t) (P t) (h t) (hP.1 t hm) (hRf k t) (hh t hm).1 (hh t hm).2 Empty _ _
        fun a => a.elim
    rw [← hum k t ht _ (hP.1 t hm) _ (hh t hm).1 (hh t hm).2, ← hx₁] at h₁
    have h₂ := ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Xo.univ.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m0.toSABMap⟩).2 h₁
    exact ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Y.oF.t _ g _ ((F k).R t) ((F k).R t) (xF k t)).1 ⟨Y.m⟩).1 h₂
  · obtain ⟨V', P, h, hVo', hm, hsub, hP, hd, hh⟩ := hloc k t₀ (hVs ht₀)
    have hW : IsOpen (V ∩ V') := hVo.inter hVo'
    refine hV E H D l Xo c Y S Ω K J y 𝔐 κ _ g ty FU k.1 n (V ∩ V') z (xF k) (F k).R P h hW
      (hmono hz hW Set.inter_subset_left) (hmono (hxhol k) hW fun t ht => hsub ht.2)
      ⟨fun t ht => hP.1 t ht.2, fun x => (hP.2 x).mono Set.inter_subset_right⟩
      (fun a b => (hd a b).mono Set.inter_subset_right) (fun t ht => ?_) t₀ ⟨ht₀, hm⟩
    exact ⟨hRf k t, (hh t ht.2).1, (hh t ht.2).2, (hzf t ht.1).symm,
      (hx₁ k t).trans (hum k t (hsub ht.2) _ (hP.1 t ht.2) _ (hh t ht.2).1 (hh t ht.2).2), hx₂ k t⟩
  · have hx : ∀ a, ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap κ ∧ (a ∈ T → x ≫ Y.j = y a) := fun a => by
      by_cases ha : a ∈ T
      · obtain ⟨x, h₁, h₂⟩ := exists_j Y κ _ (hyi a ha) (hys a ha)
        exact ⟨x, h₂, fun _ => h₁⟩
      · exact ⟨xF k t, hx₂ k t, fun h => absurd h ha⟩
    choose x hxs hxj using hx
    have hol := isHolTo_of_j Y κ hT hxs (GlobalTheory.HolPeriods.isHolTo_congr hy hxj)
    obtain ⟨i, hi⟩ := Flat.exists_index_of_isPreconnected E H D l Xo _ g ty FU m T (fun a => x a ≫ pullback.fst _ _) hT hTc
      ⟨b, hb⟩ (fun a _ => by rw [Category.assoc, pullback.condition, ← Category.assoc, hxs, spMap_comp])
      (PullbackSections.isHolTo_comp hol _)
    have key : ∀ a ∈ T, ∀ (k : ι) (t : Fin n → ℂ), y a = xF k t ≫ Y.j → k.1 = i := fun a ha k t e => by
      obtain ⟨B', P, -, haB, -, hP, hu'⟩ := hi a ha
      refine FU.disj _ _ _ _ (hPt k t) (hP.1 a haB) ?_
      rw [hu' a haB, ← hx₁, j_inj Y ((hxs a).trans (hx₂ k t).symm) ((hxj a ha).trans e)]
    exact Subtype.ext ((key b hb k t e).trans (key b' hb' k' t' e').symm)

end SheetDecomposition
