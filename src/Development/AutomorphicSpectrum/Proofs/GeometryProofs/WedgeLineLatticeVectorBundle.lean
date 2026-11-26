module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundle
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeVectorBundle

theorem alt_det {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v : Fin p → E) (c : Matrix (Fin p) (Fin p) Ω) :
    f (fun i => ∑ j, c i j • v j) = c.det • f v := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Ω]
  intro φ
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin p))
    (φ.compAlternatingMap (f.compLinearMap (Fintype.linearCombination Ω v)))
  have h2 := congrArg (fun g => g (fun i => c i)) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    AlternatingMap.smul_apply, Pi.basisFun_det_apply, Pi.basisFun_apply,
    Fintype.linearCombination_apply_single, one_smul, smul_eq_mul] at h2
  simp only [Fintype.linearCombination_apply] at h2
  rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_eq_zero]
  rfl

theorem line_of_span {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v v' : Fin p → E)
    (h : Submodule.span Ω (Set.range v') = Submodule.span Ω (Set.range v)) : ∃ c : Ω, f v' = c • f v := by
  have : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = v' i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using this
  refine ⟨(Matrix.of c).det, ?_⟩
  rw [← alt_det]
  congr 1
  funext i
  exact (hc i).symm

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem wedge_frame {A : Lat ξ E} {p : ℕ} {v : Fin p → E} {x : Cpt ξ} (h : A.IsFrameAt v x) :
    A.wedge p x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p v} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have : ∀ i, ∃ c : Fin p → regAt ξ x, ∑ j, c j • v j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (h.2 ▸ hb i)
    choose c hc using this
    refine Submodule.mem_span_singleton.2 ⟨(Matrix.of c).det, ?_⟩
    have e := alt_det (exteriorPower.ιMulti Ω p) v ((regAt ξ x).subtype.mapMatrix (Matrix.of c))
    rw [← RingHom.map_det] at e
    refine e.symm.trans ?_
    congr 1
    funext i
    exact hc i
  · refine Submodule.span_mono ?_
    rintro w rfl
    exact ⟨v, fun i => h.2 ▸ Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem span_unit {x : Cpt ξ} {u : Ω} (hu : unitAt ξ x u) (e : E) :
    Submodule.span (regAt ξ x) {u • e} = Submodule.span (regAt ξ x) {e} := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨u, hu.2.1⟩, rfl⟩
  · exact ⟨⟨u⁻¹, hu.2.2⟩, by
      change u⁻¹ • u • e = e
      rw [inv_smul_smul₀ hu.1]⟩

theorem coeff_unit {x : Cpt ξ} {a : E} (ha : a ≠ 0) {α α' : Ω} (h0 : α ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a}) :
    ∃ u, unitAt ξ x u ∧ α = u * α' := by
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) h
  exact ⟨u, hu, smul_left_injective Ω ha (by simpa [mul_smul] using e)⟩

theorem on_line {A : Lat ξ E} {T : Set (Cpt ξ)} {p : ℕ} {V : Submodule Ω E} (hA : A.IsVBOn T p V)
    {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} (hx : x ∈ T) {α : Ω} (h0 : α ≠ 0)
    (h : A.wedge p x = Submodule.span (regAt ξ x) {α • a}) (v : Fin p → E)
    (hv : Submodule.span Ω (Set.range v) = V) : ∃ γ : Ω, γ ≠ 0 ∧ exteriorPower.ιMulti Ω p v = γ • a := by
  obtain ⟨U, hU, b, hb, hf⟩ := hA x hx
  have h1 := wedge_frame (hf x hx hU)
  obtain ⟨u, -, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) (h.symm.trans h1)
  obtain ⟨c, hc⟩ := line_of_span (exteriorPower.ιMulti Ω p) v b (hb.trans hv.symm)
  rw [hc, smul_smul] at e
  have huc : u * c ≠ 0 := by
    intro h'
    rw [h', zero_smul] at e
    exact smul_ne_zero h0 ha e
  refine ⟨(u * c)⁻¹ * α, mul_ne_zero (inv_ne_zero huc) h0, ?_⟩
  rw [mul_smul, e, inv_smul_smul₀ huc]

section
variable {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ}

theorem gen_of_coeff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) :
    (lineLat A B p q a b).IsGenAt x f⁻¹ := by
  have h' := h
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← e, zero_mul])
  refine ⟨inv_ne_zero hf, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨g, ⟨α', β', hα', hβ', hA', hB', e'⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := coeff_unit ha hα' (hA'.symm.trans hA)
    obtain ⟨w, hw, ew⟩ := coeff_unit hb hβ (hB.symm.trans hB')
    refine Submodule.mem_span_singleton.2 ⟨⟨u * w, mul_mem hu.2.1 hw.2.1⟩, ?_⟩
    change u * w * f⁻¹ = g⁻¹
    have hg : g ≠ 0 := by
      rintro rfl
      exact hβ' (by rw [← e', zero_mul])
    have key : f * α = (w * g * u) * α := by rw [e, ew, ← e', eu]; ring
    have key2 : f = w * g * u := mul_right_cancel₀ hα key
    have := hu.1
    have := hw.1
    rw [key2]
    field_simp
  · rintro t rfl
    exact ⟨f, h', rfl⟩

theorem gen_iff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) (t : Ω) :
    (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹ := by
  constructor
  · rintro ⟨ht, hL⟩
    refine ⟨ht, ?_⟩
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht (hL.symm.trans (gen_of_coeff ha hb h).2)
    obtain ⟨α, β, hα, hβ, hA, hB, e'⟩ := h
    refine ⟨u * α, β, mul_ne_zero hu.1 hα, hβ, ?_, hB, ?_⟩
    · rw [mul_smul, span_unit hu, hA]
    · have := hu.1
      rw [e, ← e', smul_eq_mul, mul_inv, inv_inv]
      field_simp
  · rintro ⟨-, h⟩
    simpa using gen_of_coeff ha hb h

theorem coeff_of_frames {v : Fin p → E} {w : Fin q → E} {α β : Ω} (hv : A.IsFrameAt v x) (hw : B.IsFrameAt w x)
    (hα : α ≠ 0) (hβ : β ≠ 0) (ev : exteriorPower.ιMulti Ω p v = α • a)
    (ew : exteriorPower.ιMulti Ω q w = β • b) : IsCoeffAt A B p q a b x (α / β)⁻¹ :=
  ⟨α, β, hα, hβ, ev ▸ wedge_frame hv, ew ▸ wedge_frame hw, by field_simp⟩

end

theorem ne_zero_of_frames {A : Lat ξ E} {p : ℕ} {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} {v v' : Fin p → E}
    {α α' : Ω} (hv : A.IsFrameAt v x) (hv' : A.IsFrameAt v' x) (e : exteriorPower.ιMulti Ω p v = α • a)
    (e' : exteriorPower.ιMulti Ω p v' = α' • a) (h : α' ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h1 := (wedge_frame hv').symm.trans (wedge_frame hv)
  rw [e, e', zero_smul, Submodule.span_zero_singleton, Submodule.span_singleton_eq_bot] at h1
  exact smul_ne_zero h ha h1

end PositivityTheory.Xgn.LineLatticeVectorBundle

theorem PositivityTheory.Xgn.line_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) := by
  intro X Ω _ ξ E _ _ A B p q V V' T a b hA hB ha hb hex
  obtain ⟨x₀, hx₀, f₀, α₀, β₀, hα₀, hβ₀, hA₀, hB₀, -⟩ := hex
  have loc : ∀ x ∈ T, ∃ U : X.Opens, x.1 ∈ U ∧ ∃ (v : Fin p → E) (w : Fin q → E) (α β : Ω), α ≠ 0 ∧ β ≠ 0 ∧
      exteriorPower.ιMulti Ω p v = α • a ∧ exteriorPower.ιMulti Ω q w = β • b ∧
      ∀ y ∈ T, y.1 ∈ U → A.IsFrameAt v y ∧ B.IsFrameAt w y := by
    intro x hx
    obtain ⟨U, hU, v, hv, hfv⟩ := hA x hx
    obtain ⟨U', hU', w, hw, hfw⟩ := hB x hx
    obtain ⟨α, hα, ev⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hA ha hx₀ hα₀ hA₀ v hv
    obtain ⟨β, hβ, ew⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hB hb hx₀ hβ₀ hB₀ w hw
    exact ⟨U ⊓ U', ⟨hU, hU'⟩, v, w, α, β, hα, hβ, ev, ew, fun y hy hyU => ⟨hfv y hy hyU.1, hfw y hy hyU.2⟩⟩
  refine ⟨fun x hx => ?_, fun x hx t => ?_, fun x hx v w α β hv hw ev ew => ?_⟩
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    have h0 : α / β ≠ 0 := div_ne_zero hα hβ
    have hr : Set.range (fun _ : Fin 1 => α / β) = {α / β} := Set.range_const
    refine ⟨U, hU, fun _ => α / β, ?_, fun y hy hyU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro s _
      exact Submodule.mem_span_singleton.2 ⟨s / (α / β), div_mul_cancel₀ s h0⟩
    · exact linearIndependent_unique_iff.2 h0
    · have := (PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
        (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h y hy hyU).1 (h y hy hyU).2 hα hβ ev ew)).2
      rw [inv_inv] at this
      rw [hr, this]
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    exact PositivityTheory.Xgn.LineLatticeVectorBundle.gen_iff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h x hx hU).1 (h x hx hU).2 hα hβ ev ew) t
  · obtain ⟨U, hU, v', w', α', β', hα, hβ, ev', ew', h⟩ := loc x hx
    have := PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames hv hw
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames ha hv (h x hx hU).1 ev ev' hα)
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames hb hw (h x hx hU).2 ew ew' hβ) ev ew)
    rwa [inv_inv] at this
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lineLat_isVBOn_gen_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) :=
  @PositivityTheory.Xgn.line_lattice_vector_bundle

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeVectorBundleStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
alias GlobalTheory.T.wedge_line_lattice_vector_bundle := GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

namespace OverUnique

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

theorem evC_eq_aeval (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  have h : algebraMap ℤ ℂ = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [evC, eval_map, aeval_def, h]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩) := fun i e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, h', h]

theorem homog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) :
    IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

theorem exists_form (c : ∀ k, ι k) (G : MRing ι) :
    ∃ (D : K → ℕ) (H M : MRing ι), IsMultiHomog H D ∧ IsMultiHomog M D ∧
      ∀ (L : Type) [Field L] (w : (Σ k, ι k) → L), (∀ k, w ⟨k, c k⟩ ≠ 0) →
        aeval w M ≠ 0 ∧ aeval w H = aeval w M * aeval (fun p => w p / w ⟨p.1, c p.1⟩) G := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩
    · intro m hm k
      have := support_monomial_subset hm
      simp at this
      simp [this]
    · simp
  | add p q hp hq =>
    obtain ⟨D₁, H₁, M₁, h₁, m₁, e₁⟩ := hp
    obtain ⟨D₂, H₂, M₂, h₂, m₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂,
      isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁),
      isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩
    obtain ⟨n₁, f₁⟩ := e₁ L w hw
    obtain ⟨n₂, f₂⟩ := e₂ L w hw
    refine ⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩
    simp only [map_add (f := _), map_mul, f₁, f₂]
    ring
  | mul_X p i hp =>
    obtain ⟨D, H, M, h, m, e⟩ := hp
    have hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ) := homog_X i
    have hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ) :=
      homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)
    have hH := isMultiHomog_mul h hX₁
    have hM := isMultiHomog_mul m hX₂
    refine ⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩
    obtain ⟨n, f⟩ := e L w hw
    have hc := hw i.1
    refine ⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩
    simp only [map_mul, aeval_X, f]
    field_simp

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem aeval_eq_zero {P : MRing ι} {d : K → ℕ} (hz : z ∈ mcPts (mCoordIdeal y)) (hP : IsMultiHomog P d)
    (h0 : aeval y P = 0) : aeval z P = 0 := by
  rw [← evC_eq_aeval]
  exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)

theorem chart_ne {k : K} {i : ι k} (hz : z ∈ mcPts (mCoordIdeal y)) (h : z ⟨k, i⟩ ≠ 0) : y ⟨k, i⟩ ≠ 0 := by
  classical
  intro h0
  apply h
  have := aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)
  simpa using this

theorem chart_ker (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : MRing ι} (h0 : aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = 0) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩) G = 0 := by
  obtain ⟨D, H, M, h, m, e⟩ := exists_form c G
  obtain ⟨-, fy⟩ := e Ω y hy
  obtain ⟨nz, fz⟩ := e ℂ z hc
  rw [h0, mul_zero] at fy
  have := aeval_eq_zero hz h fy
  rw [fz] at this
  exact (mul_eq_zero.mp this).resolve_left nz

theorem exists_intHom (φ : F →+* Ω) (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)) :
    ∃ τ : 𝓞 F →+* ℂ, ∀ (a : 𝓞 F) (G : MRing ι), aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) →
      τ a = aeval (fun p => z p / z ⟨p.1, c p.1⟩) G := by
  set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv
  set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu
  let A : MRing ι →ₐ[ℤ] Ω := aeval v
  let ψ : MRing ι →+* A.range := (A.rangeRestrict : MRing ι →+* A.range)
  let ψ' : MRing ι →+* ℂ := ((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)
  have hs : Function.Surjective ψ := A.rangeRestrict_surjective
  have hker : RingHom.ker ψ ≤ RingHom.ker ψ' := by
    intro G hGk
    rw [RingHom.mem_ker] at hGk ⊢
    have h1 : aeval v G = 0 := congrArg Subtype.val hGk
    exact chart_ker hz hc hy h1
  let l : A.range →+* ℂ := RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩
  have hl : ∀ G, l (ψ G) = ψ' G := fun G =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G
  let ρ : 𝓞 F →+* A.range := (φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by
    obtain ⟨G, hG'⟩ := hG a
    exact ⟨G, hG'⟩)
  refine ⟨l.comp ρ, fun a G h => ?_⟩
  have : ρ a = ψ G := Subtype.ext h.symm
  rw [RingHom.comp_apply, this, hl]
  rfl

theorem intHom_injective (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

end OverUnique


open OverUnique GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem existsUnique_ptOver (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (hO : OverInt y φ) :
    ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  classical
  intro z hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => chart_ne hz (hc k)
  have hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) := by
    intro a
    have h := hO.2 c hy a
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  obtain ⟨τ, hτ⟩ := exists_intHom φ hz hc hy hG
  have hinj := intHom_injective τ
  let σ : F →+* ℂ := IsFractionRing.lift hinj
  have hσ : ∀ a : 𝓞 F, σ (a : F) = τ a := fun a => IsFractionRing.lift_algebraMap hinj a
  refine ⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩
  · obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha₂
    obtain ⟨G₁, e₁⟩ := hG a₁
    obtain ⟨G₂, e₂⟩ := hG a₂
    obtain ⟨D₁, H₁, M₁, h₁, m₁, f₁⟩ := exists_form c G₁
    obtain ⟨D₂, H₂, M₂, h₂, m₂, f₂⟩ := exists_form c G₂
    obtain ⟨ny₁, y₁⟩ := f₁ Ω y hy
    obtain ⟨ny₂, y₂⟩ := f₂ Ω y hy
    obtain ⟨nz₁, z₁⟩ := f₁ ℂ z hc
    obtain ⟨nz₂, z₂⟩ := f₂ ℂ z hc
    have hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d) := by
      refine homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)
      rw [add_comm D₁]
      exact isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg
    have h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0 := by
      have hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
      simp only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]
      rw [map_div₀]
      field_simp
      ring
    have h1 := aeval_eq_zero hz hP h0
    simp only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g,
      ← evC_eq_aeval z h, ← hσ] at h1
    have hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
    rw [map_div₀]
    have hM : aeval z M₁ * aeval z M₂ ≠ 0 := mul_ne_zero nz₁ nz₂
    have h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h := by
      apply mul_left_cancel₀ hM
      linear_combination h1
    field_simp
    linear_combination h2
  · refine RingHom.ext fun a => ?_
    have key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F) := by
      intro a
      obtain ⟨G, e⟩ := hG a
      obtain ⟨D, H, M, h, m, f⟩ := exists_form c G
      obtain ⟨-, fy⟩ := f Ω y hy
      obtain ⟨nz, fz⟩ := f ℂ z hc
      have hy' : aeval y H = φ (a : F) * aeval y M := by rw [fy, e, mul_comm]
      have h1 := hσ'.2 (a : F) D H M h m hy'
      rw [evC_eq_aeval, evC_eq_aeval, fz] at h1
      rw [hσ, hτ a G e]
      have := mul_left_cancel₀ nz (h1.trans (mul_comm _ _))
      exact this.symm
    obtain ⟨a₁, a₂, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    rw [map_div₀, map_div₀]
    exact congrArg₂ _ (key a₁) (key a₂)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
alias GlobalTheory.T.complex_point_existsUnique_embedding := GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersion
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersion
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_comp_surjective_of_open_part :
    ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens)
      (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW →
      jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  intro S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx
  have := he
  have hO : IsOpenImmersion (W'.ι ≫ f) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y) :=
    Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y
  have := (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y
  have hι : Function.Bijective (W'.ι.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have key : Function.Surjective (f.stalkMap (W'.ι y)) := by
    intro t
    obtain ⟨s, hs⟩ := h1 (W'.ι.stalkMap y t)
    refine ⟨s, hι.1 ?_⟩
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  rw [Scheme.Hom.stalkMap_comp]
  exact key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
alias GlobalTheory.T.stalk_surjective_open_immersion := GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem evC_conj {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    evC (fun p => (starRingEnd ℂ) (z p)) g = (starRingEnd ℂ) (evC z g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, Polynomial.map_add (f := _), map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]

theorem ptOver_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ),
    PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  intro K _ ι _ Ω _ F _ _ y φ σ z h
  obtain ⟨⟨hne, hvan⟩, hrel⟩ := h
  refine ⟨⟨fun k => ?_, fun f hf => ?_⟩, fun a d g h' hg hh e => ?_⟩
  · obtain ⟨i, hi⟩ := hne k
    exact ⟨i, by simpa using hi⟩
  · have := evC_conj z f
    have h0 : evC z f = 0 := hvan f hf
    rw [h0, map_zero] at this
    exact this
  · rw [evC_conj, evC_conj, hrel a d g h' hg hh e, map_mul, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugateStatement
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
alias GlobalTheory.T.complex_point_conjugate := GlobalTheory.CompanionTheory.Ar.Flat.ptOver_conj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem regAt_generic_eq_top {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine (RingHom.mem_range).2 ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hs

theorem exists_leftInverse_flagForms (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ)
    (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E)
    (hT : CoordTie ℤ ξ x) (hV : L.IsVB r V) (hG : IsTwistGen ξ x L m φ)
    (hc : LinearIndependent Ω c) (hs : Submodule.span Ω (Set.range c) = V) :
    ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := fun a => regAt_generic_eq_top hT.gen a
  obtain ⟨k, hk⟩ := hT.cover p₀
  unfold Lat.IsVB Lat.IsVBOn at hV
  obtain ⟨U, hU, b, hbV, hbF⟩ := hV p₀ (Set.mem_univ _)
  obtain ⟨-, hLp⟩ := hbF p₀ (Set.mem_univ _) hU
  obtain ⟨-, hG2⟩ := hG
  have hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0 := by
    intro i
    obtain ⟨w, hwf⟩ := LinearMap.exists_extend ((Module.Basis.span hc).coord i)
    refine ⟨w, fun l => ?_⟩
    have h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l) := by
      rw [← hwf]
      simp [Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  choose w hw using hw0
  have hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧
      ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m) :=
    fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)
  choose g hgr hg using hg0
  have key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e := by
    intro i
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j := ⟨_, rfl⟩
    have hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e := by
      intro e
      rw [hψdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have heq : Set.EqOn (w i) ψ (Set.range b) := by
      rintro _ ⟨t, rfl⟩
      have hbt : b t ∈ L p₀ := by
        rw [hLp]
        exact Submodule.subset_span ⟨t, rfl⟩
      rw [hg i (b t) hbt, hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    intro e he
    rw [← hbV] at he
    rw [LinearMap.eqOn_span' heq he, hψ]
  refine ⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩
  ext i l
  have hcl : c l ∈ V := by
    rw [← hs]
    exact Submodule.subset_span ⟨l, rfl⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← key i (c l) hcl, hw i l]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGeneratorsStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
alias GlobalTheory.T.frame_via_twisted_generators := GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem adjugate_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ}
    (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (i j : Fin r) :
    P.adjugate i j ∈ R := by
  let P' : Matrix (Fin r) (Fin r) R := fun a b => ⟨P a b, hP a b⟩
  have hPP : P = (R.subtype).mapMatrix P' := by
    ext a b
    rfl
  rw [hPP, ← RingHom.map_adjugate]
  exact (P'.adjugate i j).2

theorem linearIndependent_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {β : Fin r → E} (hβ : LinearIndependent Ω β) (P : Matrix (Fin r) (Fin r) Ω) (hd : P.det ≠ 0) :
    LinearIndependent Ω (fun k => ∑ a, P a k • β a) := by
  rw [Fintype.linearIndependent_iff] at hβ ⊢
  intro g hg
  have h1 : ∀ a, ∑ k, P a k * g k = 0 := by
    apply hβ
    refine Eq.trans ?_ hg
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have h2 : Matrix.mulVec P g = 0 := by
    funext a
    exact h1 a
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hd h2
  intro i
  rw [h3]
  rfl

theorem span_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ}
    (β : Fin r → E) (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (hd : P.det ≠ 0)
    (hdi : P.det⁻¹ ∈ R) :
    Submodule.span R (Set.range fun k => ∑ a, P a k • β a) = Submodule.span R (Set.range β) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)
    refine sum_mem fun a _ => ?_
    exact Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro b
    show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)
    have hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b := fun a =>
      (Matrix.mul_apply).symm
    have hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b := by
      calc ∑ k, P.adjugate k b • ∑ a, P a k • β a
          = ∑ a, (∑ k, P a k * P.adjugate k b) • β a := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = ∑ a, (P * P.adjugate) a b • β a := by
            simp only [hm]
        _ = P.det • β b := by
            rw [Matrix.mul_adjugate]
            simp [Matrix.one_apply]
    have key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a := by
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [key]
    refine sum_mem fun k _ => ?_
    exact Submodule.smul_mem _
      (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R)
      (Submodule.subset_span ⟨k, rfl⟩)

theorem isFrameAt_matrix_comb : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ)
    (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det →
    L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  intro X Ω _ ξ E _ _ L r β q P h1 h2 h3
  obtain ⟨hli, hspan⟩ := h1
  obtain ⟨hne, -, hinv⟩ := h3
  show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧
    L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)
  refine ⟨linearIndependent_matrix_comb hli P hne, ?_⟩
  rw [hspan]
  exact (span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrixStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
alias GlobalTheory.T.frame_change_by_unit_matrix := GlobalTheory.CompanionTheory.Ar.FlagBun.isFrameAt_matrix_comb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionId
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionId
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionIdStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
alias GlobalTheory.T.hopf_order_induction_id := GlobalTheory.CompanionTheory.Ar.BT.indOrder_id_eq_of_isHopfOrder
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem isFinOpenSub_top (Γ : QFGroup R T) (hfin : IsFinite Γ.G.hom) : Γ.IsFinOpenSub ⊤ := by
  constructor
  · have := hfin
    have hi : IsIso (⊤ : Γ.G.left.Opens).ι := (Scheme.topIso Γ.G.left).isIso_hom
    infer_instance
  all_goals simp

noncomputable def secMap {X : Scheme.{0}} {A : Type} [CommRing A] (j : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop).hom

theorem val_secMap (Γ : QFGroup R T) {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens)) (a : A) :
    valAt (Γ.pt t).left ⊤ h (secMap j a) = algebraMap R (FractionRing R) ((a : T → R) t) := by
  have e0 : j.appLE ⊤ ⊤ (by simp) = j.appTop := Scheme.Hom.appLE_eq_app _
  have h2 : ⊤ ≤ ((Γ.pt t).left ≫ j) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have h3 : ⊤ ≤ (Spec.map (CommRingCat.ofHom
    ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have e1 := valHom_appLE (Γ.pt t).left j (V := ⊤) (W := ⊤) (by simp) h h2
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)
  rw [e0, valHom_congr (hj.pt t) _ h2 h3, valHom_spec_top] at e1
  exact e1

theorem isIso_of_secMap_bijective {X : Scheme.{0}} [IsAffine X] {A : Type} [CommRing A]
    (j : X ⟶ Spec (CommRingCat.of A)) (hb : Function.Bijective (secMap j)) : IsIso j := by
  have h1 : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h2 : IsIso j.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of A)).inv j.appTop
  have e := Scheme.isoSpec_hom_naturality j
  have h3 : IsIso (j ≫ (Spec (CommRingCat.of A)).isoSpec.hom) := by
    rw [← e]; infer_instance
  exact IsIso.of_isIso_comp_right j (Spec (CommRingCat.of A)).isoSpec.hom

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

namespace GlobalTheory.CompanionTheory.Ar.BT.FiniteIso

open GlobalTheory.CompanionTheory.Ar.BT.SubOrder

theorem isIso_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  intro R _ _ _ T _ _ Γ j hj hfin
  have hF := isFinOpenSub_top Γ hfin
  have hU := isAffineOpen_of_fin Γ hF
  have : IsAffine Γ.G.left := by
    have := hfin
    exact isAffine_of_isAffineHom Γ.G.hom
  obtain ⟨H, A', hH, hopf, hA'⟩ := GlobalTheory.T.finite_open_hopf_order R T Γ ⊤ hF
  have htop : ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ (⊤ : Γ.G.left.Opens) := fun t => by simp
  have hHt : ∀ t, t ∈ H := fun t => (hH t).2 (htop t)
  have inj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra R Γ(Γ.G.left, ⊤) := (secRho Γ hU).toAlgebra
  have hρ : hU.fromSpec ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R Γ(Γ.G.left, ⊤))) :=
    fromSpec_hom Γ hU
  have hfinite := sec_finite hρ hF
  have hval : ∀ (s : Γ(Γ.G.left, ⊤)) (t : T),
      ∃ r : R, algebraMap R (FractionRing R) r = valAt (Γ.pt t).left ⊤ (htop t) s := by
    intro s t
    have h1 : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    exact IsIntegrallyClosed.isIntegral_iff.1 (h1.map (valAlg hρ t (htop t)))
  apply isIso_of_secMap_bijective
  constructor
  · intro a b hab
    apply Subtype.ext
    funext t
    apply inj
    rw [← val_secMap Γ hj t (htop t) a, ← val_secMap Γ hj t (htop t) b, hab]
  · intro s
    choose f hf using hval s
    let f' : H → R := fun h => f h
    have hf' : f' ∈ A' := (hA' f').2 ⟨s, fun t h => (hf t).symm⟩
    have hind : f' ∈ indOrder (MonoidHom.id H) A' := by
      rw [GlobalTheory.T.hopf_order_induction_id R H A' hopf]
      exact hf'
    have hmem : f ∈ Γ.btOrder ⊤ := by
      apply Algebra.subset_adjoin
      intro t g _
      obtain ⟨s', hs'⟩ := (hA' _).1 (hind ⟨t, hHt t⟩)
      exact ⟨⊤, trivial, s', fun u h => hs' ⟨u, hHt u⟩ h⟩
    refine ⟨⟨f, hmem⟩, ?_⟩
    rw [← sub_eq_zero]
    apply GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤
    intro t h
    rw [← valHom_apply, map_sub, valHom_apply, valHom_apply, val_secMap Γ hj, hf, sub_self]

end GlobalTheory.CompanionTheory.Ar.BT.FiniteIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFiniteStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.btOrder_embedding_iso_finite := GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite
end
end
