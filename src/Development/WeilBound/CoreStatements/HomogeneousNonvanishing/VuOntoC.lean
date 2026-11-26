module

public import Development.WeilBound.CoreStatements.ProjectiveValuations.FrequentlyNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReading
section -- merged from Development.WeilBound.CoreStatements.ProjectiveValuations.HolomorphicExtensionSections
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS

theorem DifferentiableLines.holomorphic_extension_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x := by
  intro E _ _ _ H D l Xo c r σ V T e k P h hR m as ss he x hx
  classical
  haveI : IsLocalRing (CAt σ) := (inferInstance : IsLocalRing ℂ)
  obtain ⟨i, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing T.X.F.cover (T.X.ptY (V.un k ⟨x, hx⟩))
  have hl := T.X.lies_ptY (V.un k ⟨x, hx⟩)
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd (V.un k ⟨x, hx⟩)) hl.1 i hz
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  have hO : ⊤ ≤ T.X.ptY (V.un k ⟨x, hx⟩) ⁻¹ᵁ flagOpen T.X := by
    rw [← T.X.pt_inc]
    exact GlobalTheory.FlagMod.le_preimage_map T.X.inc (top_le_inc T.X) le_top
  let y : GlobalTheory.CxPts (flagStr T.X) σ := ⟨(T.X.ptY (S := CAt σ) (V.un k ⟨x, hx⟩) :), ptY_str (S := CAt σ) T.X (V.un k ⟨x, hx⟩)⟩
  have hy : y ∈ GlobalTheory.CxPts.ptsIn (flagStr T.X) σ ((T.X.LL e).U i) := hz
  haveI : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have hs : h i y = ∑ j, as j * GlobalTheory.CxPts.secVal (flagStr T.X) σ (ss j) i y := by
    rw [he]
    exact (congrFun (Finset.sum_apply (show (T.X.LL e).ι from i) _ _) y).trans (Finset.sum_apply y _ _)
  rw [hR x hx i y hz Q t rfl hQ ht, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have a : rdU V (ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j))) k x =
      toC (evR Xo c (ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j))) (V.un k ⟨x, hx⟩)) := dif_pos hx
  have b : GlobalTheory.CxPts.secVal (flagStr T.X) σ (ss j) i y = _ := GlobalTheory.CxPts.ev_eq hy _
  have d := evR_ruleTop (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)) hO hQ ht
  have f := GlobalTheory.Vanishing.H0.val_ofSec (p := flagStr T.X) (O := ⊤) (B := T.X.LL e) (T.X.ptY (V.un k ⟨x, hx⟩)) i le_top hz (ss j)
  rw [a, d, f, b, mul_left_comm]
  rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReading
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS

theorem GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x :=
  @DifferentiableLines.holomorphic_extension_sections
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReadingStatement
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extension_section_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | exact GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombination
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsResidueEval
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClosedPt

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts TopologicalSpace

theorem exists_residue_eval : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ),
    LocallyOfFiniteType p → ∀ (B : LB Y), B.IsLB → ∀ z : Y, IsClosed ({z} : Set Y) →
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (e : B.Sec →+ K),
      (∀ (a : F) (s : B.Sec), e (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a • s) = algebraMap F K a * e s) ∧
      (∀ s : B.Sec, z ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s → e s ≠ 0) ∧
      ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∃ (y : GlobalTheory.CxPts p σ) (i : B.ι),
        y.1 (IsLocalRing.closedPoint ℂ) = z ∧ ∀ s : B.Sec, GlobalTheory.CxPts.secVal p σ s i y = τ (e s) := by
  intro F _ Y p σ hp B hB z hz
  obtain ⟨i, hzi⟩ : ∃ i, z ∈ B.U i := Opens.mem_iSup.1 (by rw [hB.cover]; trivial)
  obtain ⟨U, hU, hzU, hUi⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hzi
  replace hU : IsAffineOpen U := hU
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have hftA : Algebra.FiniteType F Γ(Y, U) := hft
  set x0 := hU.primeIdealOf ⟨z, hzU⟩ with hx0
  have hfx : hU.fromSpec x0 = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hcl : IsClosed ({x0} : Set (PrimeSpectrum Γ(Y, U))) := by
    have h1 : IsClosed (hU.fromSpec.base ⁻¹' {z}) := hz.preimage hU.fromSpec.base.hom.continuous
    have h2 : hU.fromSpec.base ⁻¹' {z} = {x0} := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hq
        exact hU.fromSpec.isOpenEmbedding.injective (hq.trans hfx.symm)
      · rintro rfl; exact hfx
    rw [h2] at h1
    exact h1
  have hmax : x0.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hcl
  let P := x0.asIdeal
  letI : Field (Γ(Y, U) ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType F (Γ(Y, U) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P) Ideal.Quotient.mk_surjective
  have hfin : Module.Finite F (Γ(Y, U) ⧸ P) := finite_of_finite_type_of_isJacobsonRing F _
  have hmem : ∀ f : Γ(Y, U), z ∈ Y.basicOpen f ↔ f ∉ P := by
    intro f
    have h1 : x0 ∈ hU.fromSpec ⁻¹ᵁ Y.basicOpen f ↔ hU.fromSpec x0 ∈ Y.basicOpen f := Iff.rfl
    rw [hfx, hU.fromSpec_preimage_basicOpen] at h1
    exact h1.symm.trans (PrimeSpectrum.mem_basicOpen _ _)
  let e : B.Sec →+ Γ(Y, U) ⧸ P :=
    { toFun := fun s => Ideal.Quotient.mk P (resG Y hUi (s.f i))
      map_zero' := by simp
      map_add' := fun s t => by simp only [GlobalTheory.LB.add_f, map_add (f := _)] }
  refine ⟨Γ(Y, U) ⧸ P, inferInstance, inferInstance, hfin, e, ?_, ?_, ?_⟩
  · intro a s
    change Ideal.Quotient.mk P (resG Y hUi ((algX p ⊤ a • s).f i)) = _ * Ideal.Quotient.mk P _
    have hres : resG Y (hUi.trans le_top) (algX p ⊤ a) = algX p U a :=
      RingHom.congr_fun (GlobalTheory.TopForm.resG_comp_algX p (hUi.trans le_top)) a
    rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LB.resG_resG, hres]
    rfl
  · intro s hs
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hs
    have hki : z ∈ B.U i ⊓ B.U k := ⟨hzi, Y.basicOpen_le _ hk⟩
    have hrel := GlobalTheory.LB.sec_rel s i k (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) inf_le_right le_rfl
    have h1 : z ∈ Y.basicOpen (resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i)) := by
      rw [hrel, Scheme.basicOpen_mul, Y.basicOpen_of_isUnit
        ((B.g i k).isUnit.map (resG Y le_rfl))]
      refine ⟨hki, ?_⟩
      have : resG Y (inf_le_right : B.U i ⊓ B.U k ≤ B.U k) (s.f k) =
          Y.presheaf.map (homOfLE (inf_le_right : B.U i ⊓ B.U k ≤ B.U k)).op (s.f k) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hki, hk⟩
    have h2 : z ∈ Y.basicOpen (s.f i) := by
      have : resG Y (inf_le_left : B.U i ⊓ B.U k ≤ B.U i) (s.f i) =
          Y.presheaf.map (homOfLE (inf_le_left : B.U i ⊓ B.U k ≤ B.U i)).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res] at h1
      exact h1.2
    have h3 : z ∈ Y.basicOpen (resG Y hUi (s.f i)) := by
      have : resG Y hUi (s.f i) = Y.presheaf.map (homOfLE hUi).op (s.f i) := rfl
      rw [this, Scheme.basicOpen_res]
      exact ⟨hzU, h2⟩
    change Ideal.Quotient.mk P _ ≠ 0
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact (hmem _).1 h3
  · intro τ hτ
    let φ : Γ(Y, U) →+* ℂ := τ.comp (Ideal.Quotient.mk P)
    have hφ : ∀ a, φ (algX p U a) = σ a := fun a => by
      rw [← hτ]; rfl
    refine ⟨ofHom hU φ hφ, i, ?_, fun s => ?_⟩
    · have hker : RingHom.ker φ = P := by
        rw [RingHom.ker_comp_of_injective _ τ.injective]
        exact Ideal.mk_ker
      have hpt : (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) = x0 := by
        apply PrimeSpectrum.ext
        change Ideal.comap φ (IsLocalRing.maximalIdeal ℂ) = P
        rw [IsLocalRing.maximalIdeal_eq_bot]
        exact hker
      change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ)) = z
      rw [hpt, hfx]
    · rw [secVal_apply, ← ev_res hUi (ofHom_mem hU φ hφ), ev_ofHom]
      rfl

end GlobalTheory.CompanionTheory.Ar.ClosedPt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LinIndepDescent
open Matrix

namespace GlobalTheory.CompanionTheory.Arith.DedekindDescent

theorem single_ext (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : F →+* ℂ) {κ : Type} [Fintype κ] (b : κ → ℂ)
    (hb : ∀ c : κ → F, ∑ k, σ (c k) * b k = 0 → c = 0) (x : κ → K)
    (h : ∀ τ : K →+* ℂ, τ.comp (algebraMap F K) = σ → ∑ k, b k * τ (x k) = 0) : x = 0 := by
  let _ : Algebra F ℂ := σ.toAlgebra
  have : CharZero F := ⟨fun a b hab => Nat.cast_injective (R := ℂ) (by
    have := congrArg σ hab
    simpa only [map_natCast] using this)⟩
  have key : ∀ y : K, ∑ k, σ (Algebra.trace F K (x k * y)) * b k = 0 := by
    intro y
    have htr : ∀ k, σ (Algebra.trace F K (x k * y)) = ∑ φ : K →ₐ[F] ℂ, φ (x k * y) :=
      fun k => trace_eq_sum_embeddings ℂ (x := x k * y)
    simp only [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun φ _ => ?_
    have hφ := h (φ : K →+* ℂ) φ.comp_algebraMap
    have hsplit : ∑ k, φ (x k * y) * b k = φ y * ∑ k, b k * (φ : K →+* ℂ) (x k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, AlgHom.coe_toRingHom]
      ring
    rw [hsplit, hφ, mul_zero]
  funext k0
  by_contra hne
  have h0 := congrFun (hb _ (key (x k0)⁻¹)) k0
  simp only [Pi.zero_apply] at h0 hne
  rw [mul_inv_cancel₀ hne, ← map_one (algebraMap F K), Algebra.trace_algebraMap, nsmul_eq_mul,
    mul_one, Nat.cast_eq_zero] at h0
  exact (Module.finrank_pos (R := F) (M := K)).ne' h0

theorem linIndep_descent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (J : Type) (K : J → Type) [∀ j, Field (K j)] [∀ j, Algebra F (K j)] [∀ j, FiniteDimensional F (K j)] (ι : Type) [Fintype ι] (v : ι → ∀ j, K j), (∀ a : ι → F, (∀ j, ∑ l, algebraMap F (K j) (a l) * v l j = 0) → a = 0) → ∀ d : ι → ℂ, (∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ → ∑ l, d l * τ (v l j) = 0) → d = 0 := by
  intro F _ σ J K _ _ _ ι _ v hv d hd
  let _ : Algebra F ℂ := σ.toAlgebra
  let S := Submodule.span F (Set.range d)
  have : FiniteDimensional F S := FiniteDimensional.span_of_finite F (Set.finite_range d)
  let B := Module.finBasis F S
  have hmem : ∀ l, d l ∈ S := fun l => Submodule.subset_span ⟨l, rfl⟩
  have hval : ∀ e : Fin (Module.finrank F S) → F,
      ((∑ k, e k • B k : S) : ℂ) = ∑ k, σ (e k) * (B k : ℂ) := by
    intro e
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  have hdc : ∀ l, d l = ∑ k, σ (B.repr ⟨d l, hmem l⟩ k) * (B k : ℂ) := by
    intro l
    rw [← hval]
    exact (congrArg Subtype.val (B.sum_repr ⟨d l, hmem l⟩)).symm
  have hbind : ∀ e : Fin (Module.finrank F S) → F, ∑ k, σ (e k) * (B k : ℂ) = 0 → e = 0 := by
    intro e he
    have h1 : ∑ k, e k • B k = 0 := by
      apply Subtype.ext
      rw [hval, he]
      rfl
    funext k
    exact Fintype.linearIndependent_iff.1 B.linearIndependent e h1 k
  have hx : ∀ j k, ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j = 0 := by
    intro j
    have hτ' : ∀ τ : K j →+* ℂ, τ.comp (algebraMap F (K j)) = σ →
        ∀ a, τ (algebraMap F (K j) a) = σ a := fun τ hτ a => by rw [← hτ]; rfl
    have := single_ext F (K j) σ (fun k => (B k : ℂ)) hbind
      (fun k => ∑ l, algebraMap F (K j) (B.repr ⟨d l, hmem l⟩ k) * v l j) (fun τ hτ => by
        refine Eq.trans ?_ (hd j τ hτ)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, hτ' τ hτ]
        rw [Finset.sum_congr rfl fun l _ => congrArg (· * τ (v l j)) (hdc l)]
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring)
    intro k
    exact congrFun this k
  have hc0 : ∀ k, (fun l => B.repr ⟨d l, hmem l⟩ k) = 0 := fun k => hv _ fun j => hx j k
  funext l
  rw [hdc l, Pi.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrFun (hc0 k) l
  simp only [Pi.zero_apply] at this
  rw [this, map_zero, zero_mul]

end GlobalTheory.CompanionTheory.Arith.DedekindDescent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombination
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.VanDescent

theorem exists_closed_mem_notMem : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), LocallyOfFiniteType p → ∀ (U O : Y.Opens), ¬ U ≤ O → ∃ z : Y, IsClosed ({z} : Set Y) ∧ z ∈ U ∧ z ∉ O := by
  intro F _ Y p hp U O hUO
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hzU, hzO⟩ := Set.not_subset.1 hUO
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set Y) ∩ (O : Set Y)ᶜ)
    ⟨z, hzU, hzO⟩ (U.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
  exact ⟨y, hc, hy, hy'⟩

theorem secVal_eq_zero_of_le {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ}
    {B : LB Y} {O : Y.Opens} (s : B.Sec) (hs : nonzeroLocus s ≤ O) (i : B.ι) (y : CxPts p σ)
    (hy : y ∉ ptsIn p σ O) : secVal p σ s i y = 0 := by
  by_contra h
  by_cases hi : y ∈ ptsIn p σ (B.U i)
  · exact hy (ptsIn_mono hs ((secVal_ne_zero_iff s hi).1 h))
  · exact h (by rw [secVal_apply]; exact ev_of_notMem hi _)

theorem vanish_descent : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  intro F _ Y p σ hp B hB O x hx
  let J := {z : Y // IsClosed ({z} : Set Y) ∧ z ∉ O}
  have hpt := fun j : J => GlobalTheory.CompanionTheory.Ar.ClosedPt.exists_residue_eval F Y p σ hp B hB j.1 j.2.1
  choose K instF instA instFD e he_smul he_ne he_pt using hpt
  let G : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    Submodule.span ℂ {f | ∃ s : B.Sec, nonzeroLocus s ≤ O ∧ secVal p σ s = f}
  let Z : Submodule ℂ (B.ι → CxPts p σ → ℂ) :=
    { carrier := {v | ∀ i y, y ∉ ptsIn p σ O → v i y = 0}
      add_mem' := fun {u v} hu hv i y hy => by simp [hu i y hy, hv i y hy]
      zero_mem' := fun i y _ => rfl
      smul_mem' := fun c v hv i y hy => by simp [hv i y hy] }
  have hGZ : G ≤ Z := Submodule.span_le.2 (by
    rintro _ ⟨s, hs, rfl⟩ i y hy
    exact secVal_eq_zero_of_le s hs i y hy)
  have key : ∀ (n : ℕ) (b : Fin n → B.Sec) (d : Fin n → ℂ) (g : B.ι → CxPts p σ → ℂ), g ∈ G →
      (∑ l, d l • secVal p σ (b l) + g) ∈ Z → (∑ l, d l • secVal p σ (b l) + g) ∈ G := by
    intro n
    induction n with
    | zero => intro b d g hg _; simpa using hg
    | succ m ih =>
      intro b d g hg hv
      by_cases H : ∀ a : Fin (m + 1) → F,
          (∀ j, ∑ l, algebraMap F (K j) (a l) * e j (b l) = 0) → a = 0
      · have hz : ∀ j (τ : K j →+* ℂ), τ.comp (algebraMap F (K j)) = σ →
            ∑ l, d l * τ (e j (b l)) = 0 := by
          intro j τ hτ
          obtain ⟨y, i, hyz, hy⟩ := he_pt j τ hτ
          have hyO : y ∉ ptsIn p σ O := fun h => j.2.2 (hyz ▸ mem_ptsIn.1 h)
          have h1 := hv i y hyO
          have h2 := hGZ hg i y hyO
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h2, add_zero,
            hy] at h1
          exact h1
        have hd : d = 0 := GlobalTheory.CompanionTheory.Arith.DedekindDescent.linIndep_descent F σ J K (Fin (m + 1)) (fun l j => e j (b l)) H d hz
        subst hd
        simpa using hg
      · push Not at H
        obtain ⟨a, ha0, ha⟩ := H
        have hes : ∀ j, e j (∑ l, algX p ⊤ (a l) • b l) = 0 := fun j => by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, he_smul]
          exact ha0 j
        have hsO : nonzeroLocus (∑ l, algX p ⊤ (a l) • b l) ≤ O := by
          by_contra h
          obtain ⟨z, hzc, hzs, hzO⟩ := exists_closed_mem_notMem F Y p hp _ O h
          exact he_ne ⟨z, hzc, hzO⟩ _ hzs (hes _)
        have hsG : secVal p σ (∑ l, algX p ⊤ (a l) • b l) ∈ G :=
          Submodule.subset_span ⟨_, hsO, rfl⟩
        have hsv : secVal p σ (∑ l, algX p ⊤ (a l) • b l) = ∑ l, σ (a l) • secVal p σ (b l) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, secVal_smul]
        rw [hsv] at hsG
        obtain ⟨l₀, hl₀⟩ := Function.ne_iff.1 ha
        have hσ : σ (a l₀) ≠ 0 := (map_ne_zero σ).2 hl₀
        obtain ⟨c, hc⟩ : ∃ c, c = d l₀ * (σ (a l₀))⁻¹ := ⟨_, rfl⟩
        have hdc : d l₀ = c * σ (a l₀) := by rw [hc, inv_mul_cancel_right₀ hσ]
        have heq : ∑ l, d l • secVal p σ (b l) + g =
            ∑ i, (d (l₀.succAbove i) - c * σ (a (l₀.succAbove i))) •
              secVal p σ (b (l₀.succAbove i)) + (g + c • ∑ l, σ (a l) • secVal p σ (b l)) := by
          rw [Fin.sum_univ_succAbove _ l₀, Fin.sum_univ_succAbove (fun l => σ (a l) • _) l₀]
          simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdc]
          module
        rw [heq] at hv ⊢
        exact ih _ _ _ (G.add_mem hg (G.smul_mem c hsG)) hv
  have hxspan : x ∈ Submodule.span ℂ (Set.range (SecC.of p σ : B.Sec → SecC p σ B)) :=
    by rw [SecC.span_range_of (p := p) (σ := σ) (B := B)]; exact Submodule.mem_top
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hxspan
  choose b hb using fun i => (g i).2
  have hval : SecC.val x = ∑ l, f l • secVal p σ (b l) + 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hfg, add_zero, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← hb l, SecC.val_of]
  have hxZ : SecC.val x ∈ Z := hx
  rw [hval] at hxZ
  have hmem := key n b f 0 G.zero_mem hxZ
  rw [← hval] at hmem
  obtain ⟨m, as, ss, hss⟩ := Submodule.mem_span_set'.1 hmem
  choose t ht1 ht2 using fun j => (ss j).2
  exact ⟨m, as, t, ht1, by rw [← hss]; exact Finset.sum_congr rfl fun j _ => by rw [ht2]⟩

end GlobalTheory.CompanionTheory.VanDescent
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexSectionFiniteCombinationStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_section_finite_combination : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (σ : F →+* ℂ), LocallyOfFiniteType p → ∀ (B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y), B.IsLB → ∀ (O : Y.Opens) (x : GlobalTheory.SecC p σ B), (∀ i y, y ∉ GlobalTheory.CxPts.ptsIn p σ O → GlobalTheory.SecC.val x i y = 0) → ∃ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → B.Sec), (∀ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (ss j) ≤ O) ∧ GlobalTheory.SecC.val x = ∑ j, as j • GlobalTheory.CxPts.secVal p σ (ss j) := by
  first | exact @GlobalTheory.CompanionTheory.VanDescent.vanish_descent | exact GlobalTheory.CompanionTheory.VanDescent.vanish_descent | (intros; apply GlobalTheory.CompanionTheory.VanDescent.vanish_descent <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoB
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

section ThetaShiftProofs

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 800000 in
theorem tendsto_arc_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h) (i : T.X.F.J)
    {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)] (hWi : W ≤ T.X.F.U i)
    (s : ℂ → GlobalTheory.CxPts (flagStr T.X) σ) {ρ : ℝ} (hρ : 0 < ρ) (hsW : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s u ∈ ptsIn _ σ W)
    (hsd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u => ev _ σ W f (s u)) (Metric.ball 0 ρ))
    (h0 : s 0 ∉ ptsIn _ σ (flagOpen T.X)) (h1 : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s u ∈ ptsIn _ σ (flagOpen T.X)) :
    Tendsto (fun u => h i (s u)) (𝓝[≠] 0) (𝓝 0) := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  let A : Type := Γ(T.X.YY, W)
  let q : Sp A ⟶ T.X.YY := GlobalTheory.FlagMod.tau hW
  let φ : c.F →+* A := (GlobalTheory.FlagMod.ev (q ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  have hφ : q ≫ flagStr T.X = spMap φ := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW hWi
  have hxc : (q ≫ T.X.π) ≫ T.Y.s = spMap φ ≫ spMap (RingHom.id c.F) :=
    ((Category.assoc _ _ _).trans hφ).trans ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Spec.map_id _).symm))
  let x : Sp A ⟶ gen T.Y := pullback.lift _ _ hxc
  have hx : q ≫ T.X.π = x ≫ genι T.Y := (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr T.Y = spMap φ := pullback.lift_snd _ _ _
  obtain ⟨fr, hfr⟩ := exists_eigFrame_tau T hW hφ i hz hx
  have hb0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  let ψ : ℂ → (A →+* ℂ) := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then
    GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) else GlobalTheory.FlagMod.ev (s 0).1 W (hsW 0 hb0)
  have hψ : ∀ u (hu : u ∈ Metric.ball (0 : ℂ) ρ), ψ u = GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) := fun u hu => dif_pos hu
  have hψq : ∀ u ∈ Metric.ball (0 : ℂ) ρ, spMap (ψ u) ≫ q = (s u).1 := fun u hu => by
    rw [hψ u hu]
    exact GlobalTheory.FlagMod.spMap_ev (s u).1 hW _
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) ρ, (ψ u).comp φ = σ := fun u hu => by
    have e₁ : spMap ((ψ u).comp φ) = spMap (ψ u) ≫ spMap φ := Spec.map_comp _ _
    rw [← hφ, ← Category.assoc, hψq u hu, (s u).2] at e₁
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have key : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ p : Sp ℂ,
      (s u).1 p ∈ flagOpen T.X ↔ (spMap (ψ u) ≫ x) p ∉ genBd T.Y := by
    intro u hu p
    have := GlobalTheory.LogKS.isIso_fst T.Y
    have e : (s u).1 p ∈ flagOpen T.X ↔ genι T.Y ((spMap (ψ u) ≫ x) p) ∈ Set.range T.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx, ← Category.assoc, hψq u hu]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι T.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc T.Y σ φ x ψ ρ := by
    refine ⟨⟨⟨hρ, fun f => (hsd f).congr fun u hu => ?_⟩, hxs, hφu⟩, fun p => ?_,
      fun u hu hne p => (key u hu p).1 (h1 u hu hne (Set.mem_univ p))⟩
    · rw [hψ u hu]
      exact (ev_eq (hsW u hu) f).symm
    · by_contra hp
      refine h0 (mem_ptsIn.2 ?_)
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) p]
      exact (key 0 hb0 p).2 hp
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H D l Xo c c.F (RingHom.id c.F) T.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ ∧ ((ρ / 2 : ℝ) : ℂ) ≠ 0 := by
    refine ⟨?_, by exact_mod_cast (half_pos hρ).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hρ).le]
    exact half_lt_self hρ
  have : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! y hy using hy'
  have hm : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → Matches fr (ψ u) (y u) := fun u hu hne => hy u ⟨hu, hne⟩
  obtain ⟨k', T₀, M₀, γ₀, xx, hT, hO₀, hL⟩ :=
    GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y hσ hU hb.1 hm
  have hne0 : ∀ w, eTwoPi w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hi : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ⊤ ≤ zOf (s u) ⁻¹ᵁ T.X.F.U i := fun u hu => ptsIn_mono hWi (hsW u hu)
  have hfb : ∀ w (hw : T₀ < w.im), ∃ (hd : xx w ∈ (V.X k').dom) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
      T.X.F.ChartFr i (zOf (s (eTwoPi w))) (hi _ (hT w hw)) Q ∧ FrBor t Q (V.un k' ⟨_, hd⟩) ∧ ∀ s, t (some s) = 1 := by
    intro w hw
    obtain ⟨hd, hl⟩ := hL w hw
    exact ⟨hd, exists_frBor_of_matches T q i hz hx fr hfr (ψ _)
      (matches_of_sameLie (hm _ (hT w hw) (hne0 w)) hl) (hψq _ (hT w hw)) _⟩
  have hev : ∀ᶠ w in imTop, T₀ < w.im := (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  refine tendsto_punctured ?_
  by_cases hk : k' = k
  swap
  · refine tendsto_const_nhds.congr' (hev.mono fun w hw => (hZ i _ fun x' hx' e => hk ?_).symm)
    obtain ⟨hd, Q, t, hQ, ht, -⟩ := hfb w hw
    have e' : T.X.ptY (V.un k ⟨x', hx'⟩) = zOf (s (eTwoPi w)) := e
    have hlx : T.X.F.Lies (zOf (s (eTwoPi w))) (V.un k ⟨x', hx'⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := hQ.exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k' k _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E r _ T₀ M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', a1, a2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E r _ T₀ M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ xx hσ hU hb hm hL x₀ hx₀ x' a1 a2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E r _ T₀ M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ := GlobalTheory.T.exists_arcLift_periods_tendsto_span E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E r _ T₀ M γ xx la m v Lp Lm hO hlim hper
  have hp := tendsto_cusp hP hO.2.2.2.1 hξ hc' ht hn
  refine hp.congr' ?_
  filter_upwards [hev] with w hw
  obtain ⟨hd, Q, t, hQ, ht, ht1⟩ := hfb w hw
  have hu := hT w hw
  have e₁ : P (xx w) = chr ee t * h i (s (eTwoPi w)) :=
    hR (xx w) hd i _ (hi _ hu) Q t (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ.lies.frBor ht)).symm hQ ht
  rw [chr_of_some ht1, hee, zpow_zero, one_mul] at e₁
  exact e₁

end ThetaShiftProofs

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC


set_option maxHeartbeats 800000 in
theorem holoOn_bdZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la) {d : ℕ} [SmoothOfRelativeDimension d (flagStr T.X)]
    (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h)
    (hh : ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL ee).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i))
    (i : T.X.F.J) :
    R.HoloOn (ptsIn _ σ (T.X.F.U i)) (h i) := by
  intro j v hv
  have hs : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have : GlobalTheory.IsNormalScheme T.X.YY := hn
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let y₀ := C.e.symm v
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain T.X.YY (y₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨W, hW, hyW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le y₀.1
    (mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hyW₁, hv.2⟩ : y₀ ∈ ptsIn _ σ (W₁ ⊓ T.X.F.U i))
  have hyW' : y₀ ∈ ptsIn _ σ W := hyW
  have := hW₁ W (mem_ptsIn.1 hyW') (hWle.trans inf_le_left)
  have hWi := hWle.trans inf_le_right
  obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen ⟨_, mem_ptsIn.1 hyW'⟩
  obtain ⟨g, hgO, hpg⟩ := hW.exists_basicOpen_le (V := flagOpen T.X) ⟨p, hpO⟩ hpW
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hpg
    exact hpg
  let s : (Fin d → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ := fun b => C.e.symm (L.symm b)
  have ho : ∀ {S}, IsOpen S → IsOpen (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' S)) := fun hS =>
    (GlobalTheory.ChartGlue.isOpen_over C.e hS).preimage L.symm.continuous
  have hU' := ho (isOpen_ptsIn W)
  have hd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun b => ev _ σ W f (s b))
      (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W)) := fun f =>
    (C.holo W f).comp L.symm.differentiableOn fun _ hb => hb
  have key : DifferentiableAt ℂ (fun b => h i (s b)) (L v) := by
    refine differentiableAt_of_lines hU' (ho ((isOpen_ptsIn (T.X.F.U i)).inter (isOpen_ptsIn (flagOpen T.X)))) (hd g)
      (fun t ht h0 => ⟨ht.1, ptsIn_mono hWi ht.2, ptsIn_mono hgO ((mem_ptsIn_basicOpen ht.2 g).2 h0)⟩)
      ((hh i j).comp L.symm.differentiableOn fun _ hb => hb) (fun τ hτ hτO w hw => ?_)
      (by simpa using ⟨hv.1, hyW'⟩) fun ρ hρ => ?_
    · have hout : s τ ∉ ptsIn _ σ (flagOpen T.X) := fun h' => hτO ⟨hτ.1, ptsIn_mono hWi hτ.2, h'⟩
      have h0 : h i (s τ) = 0 := hZ i _ fun x hx e => hout (mem_open_of_ptY T _ _ e)
      have hline : Differentiable ℂ fun z : ℂ => τ + z • w := by fun_prop
      have hnb : ∀ᶠ z : ℂ in 𝓝 0, τ + z • w ∈ L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W) :=
        hline.continuous.continuousAt.preimage_mem_nhds (hU'.mem_nhds (by simpa using hτ))
      obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hnb.and (eventually_nhdsWithin_iff.1 hw))
      show Tendsto (fun z : ℂ => h i (s (τ + z • w))) _ (𝓝 (h i (s τ)))
      rw [h0]
      have b₁ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s (τ + u • w) ∈ ptsIn _ σ W := fun u hu => (hb u hu).1.2
      have b₂ : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u : ℂ => ev _ σ W f (s (τ + u • w))) (Metric.ball 0 ρ) :=
        fun f => DifferentiableOn.comp (g := fun b => ev _ σ W f (s b)) (f := fun u : ℂ => τ + u • w) (hd f)
          hline.differentiableOn fun u hu => (hb u hu).1
      have b₃ : s (τ + (0 : ℂ) • w) ∉ ptsIn _ σ (flagOpen T.X) := by
        rw [zero_smul, add_zero]
        exact hout
      have b₄ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s (τ + u • w) ∈ ptsIn _ σ (flagOpen T.X) :=
        fun u hu hu0 => ((hb u hu).2 hu0).2.2
      exact tendsto_arc_readsZ hσ hU T hee hP hR hZ i hW hWi (fun z => s (τ + z • w)) hρ b₁ b₂ b₃ b₄
    · have hsrc : y₀ ∈ C.e.source := C.e.map_target hv.1
      have hc : ContinuousAt (fun y => L (C.e y)) y₀ := L.continuous.continuousAt.comp (C.e.continuousAt hsrc)
      have hN : {y | L (C.e y) ∈ Metric.ball (L v) ρ} ∈ 𝓝 y₀ :=
        hc.preimage_mem_nhds (by rw [C.e.right_inv hv.1]; exact Metric.ball_mem_nhds _ hρ)
      obtain ⟨y', hy', hne⟩ := frequently_ne_zero (flagStr T.X) hW hg hyW'
        (inter_mem hN (C.e.open_source.mem_nhds hsrc))
      refine ⟨_, hy'.1, ?_⟩
      simp only [s, ContinuousLinearEquiv.symm_apply_apply]
      rwa [C.e.left_inv hy'.2]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (key.comp v L.differentiableAt).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [s, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuOntoA
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology

def Tw (V : Unf Xo c σ r) (e : Ix D → ℤ) (k : V.Comp) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ (a a₀ : (E →+* ℂ) × ℕ → ℕ) (n n₀ : ℕ) (g : Rul Xo c), Dom a n ∧ NV Xo c σ a n ∧ Dom a₀ n₀ ∧
    g ∈ sec Xo c a₀ n₀ ∧ (fun i => (ex D a n i : ℤ)) = e + (fun i => (ex D a₀ n₀ i : ℤ)) ∧
    laU V a n k = la + laU V a₀ n₀ k ∧ evR Xo c g y ≠ 0

theorem isSec_mul {X : Data E r} {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hdiag : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
      have hdet := (hb τ).1
      rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    have hadd : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
    show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, hadd]
    ring
  · show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem sec_frBorZ {V : Unf Xo c σ r} (hU : IsUnf V) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {x x' : (V.X k).dom} {t : Ix D → (CAt σ)ˣ} (ht : FrBor t (V.un k x) (V.un k x')) :
    P x'.1 = chr e t * P x.1 := by
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT (V.un k x)
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  have h1 : P x'.1 * rdU V g k x'.1 = chr (fun i => (ex D a n i : ℤ)) t * (P x.1 * rdU V g k x.1) :=
    sec_frBor hU hD hN hPg ht
  rw [rdU_eq, rdU_eq, DifferentiableLines.evR_frBor hg ht, he, chr_add] at h1
  refine mul_right_cancel₀ (mul_ne_zero (chr_ne_zero (fun i => (ex D a₀ n₀ i : ℤ)) t)
    (show toC (evR Xo c g (V.un k x)) ≠ 0 from hg0)) ?_
  rw [h1]
  ring

theorem open_secZ {V : Unf Xo c σ r} (hU : IsUnf V) (T : TorFlag Xo c) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) :
    ∃ h ∈ GlobalTheory.CxPts.fibSec (flagStr T.X) σ (T.X.LL e), Reads V T e k P h ∧ OffZero V T k h := by
  classical
  obtain ⟨-, g1, g2, g3⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  have hex : ∀ (i : T.X.F.J) (z : Sp (CAt σ) ⟶ T.X.YY), ∃ v : ℂ,
      (∀ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q → FrBor t Q (V.un k x) → P x.1 = chr e t * v) ∧
      ((¬ ⊤ ≤ z ⁻¹ᵁ T.X.F.U i ∨ ∀ x : (V.X k).dom, T.X.ptY (V.un k x) ≠ z) → v = 0) := by
    intro i z
    by_cases h : ∃ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q ∧ FrBor t Q (V.un k x)
    · obtain ⟨x₀, hz₀, Q₀, t₀, hQ₀, ht₀⟩ := h
      refine ⟨(chr e t₀)⁻¹ * P x₀.1, fun x hz Q t hQ ht => ?_, fun h => ?_⟩
      · obtain rfl : Q₀ = Q := hQ₀.unique hQ
        have h1 := sec_frBorZ hU hT hP (g1 _ _ _ _ _ (g2 _ _ _ ht₀) ht)
        have h2 : chr e t = chr e t₀ * chr e (t₀⁻¹ * t) := by rw [← chr_mul, mul_inv_cancel_left]
        rw [h1, h2]
        have := chr_ne_zero e t₀
        field_simp
        try exact mul_comm _ _
      · exact (h.elim (fun h => h hz₀) fun h =>
          h x₀ (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ₀.lies.frBor ht₀)).symm).elim
    · exact ⟨0, fun x hz Q t hQ ht => (h ⟨x, hz, Q, t, hQ, ht⟩).elim, fun _ => rfl⟩
  choose v hv hv0 using hex
  refine ⟨fun i y => v i y.1, ⟨fun i j y hi hj => ?_, fun i y hi => hv0 i y.1 (Or.inl hi)⟩,
    fun x hx i y hz Q t _ hQ ht => hv i y.1 ⟨x, hx⟩ hz Q t hQ ht,
    fun i y h => hv0 i y.1 (Or.inr fun x => h x.1 x.2)⟩
  by_cases h : ∃ x : (V.X k).dom, T.X.ptY (V.un k x) = y.1
  · obtain ⟨x, hx⟩ := h
    obtain ⟨Q, t, hQ, ht⟩ := exists_chart_frBor T (V.un k x) i hx hi
    obtain ⟨Q', t', hQ', ht'⟩ := exists_chart_frBor T (V.un k x) j hx hj
    have hh : ⊤ ≤ (y.1 : Sp (CAt σ) ⟶ T.X.YY) ⁻¹ᵁ (T.X.F.U i ⊓ T.X.F.U j) := GlobalTheory.FlagMod.le_preimage_inf hi hj
    have h1 := g3 _ _ _ _ ht (g1 _ _ _ _ _ (hQ.frBor hQ' hh) ht')
    have h2 := (hv i y.1 x hi Q t hQ ht).symm.trans (hv j y.1 x hj Q' t' hQ' ht')
    have h3 : GlobalTheory.CxPts.gv (flagStr T.X) σ (T.X.LL e) i j y = chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) :=
      (GlobalTheory.CxPts.ev_eq (p := flagStr T.X) (σ := σ) (y := y) (U := T.X.F.U i ⊓ T.X.F.U j) hh _).trans
        (T.X.F.ev_LL_g (S := CAt σ) e i j y.1 hh)
    have h4 : chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) * chr e (T.X.F.TAt (S := CAt σ) i j y.1 hh) = 1 := by
      rw [← chr_add, neg_add_cancel, chr_zero]
    rw [h1, chr_mul] at h2
    show v i y.1 = _ * v j y.1
    rw [h3]
    refine mul_left_cancel₀ (chr_ne_zero e t') ?_
    linear_combination (chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh)) * h2 - chr e t' * v i y.1 * h4
  · push Not at h
    show v i y.1 = _ * v j y.1
    rw [hv0 i y.1 (Or.inr h), hv0 j y.1 (Or.inr h), mul_zero]

theorem differentiableAt_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) (i : T.X.F.J) {m : ℕ}
    {B : Set (Fin m → ℂ)} (s : (Fin m → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ)
    (ho : ∀ W, IsOpen (B ∩ s ⁻¹' ptsIn _ σ W))
    (hd : ∀ W (u : Γ(T.X.YY, W)), DifferentiableOn ℂ (fun b => ev _ σ W u (s b)) (B ∩ s ⁻¹' ptsIn _ σ W))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hi : s b₀ ∈ ptsIn _ σ (flagOpen T.X ⊓ T.X.F.U i)) :
    DifferentiableAt ℂ (fun b => h i (s b)) b₀ := by
  obtain ⟨hO, hz⟩ := mem_ptsIn_inf.1 hi
  obtain ⟨Q₀, hQ₀⟩ := exists_chartFr_alg T (S := CAt σ) (zOf (s b₀)) hO (s b₀).2 i hz
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT Q₀
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  choose u hu using fun j => exists_fun_chart (σ := σ) T hg j
  let h' : T.X.F.J → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := fun j y => h j y * ev _ σ _ (u j) y
  have hR' : Reads V T (fun i => (ex D a n i : ℤ)) k (fun x => P x * rdU V g k x) h' := by
    intro x hx j y hy Q t hxy hQ ht
    have e₁ : P x = chr e t * h j y := hR x hx j y hy Q t hxy hQ ht
    have e₂ : rdU V g k x = _ := (rdU_eq V g k ⟨x, hx⟩).trans (DifferentiableLines.evR_frBor hg ht)
    rw [hu j y hy Q (mem_open_of_ptY T _ _ hxy) hQ] at e₂
    show P x * rdU V g k x = chr (fun i => (ex D a n i : ℤ)) t * (h j y * ev _ σ _ (u j) y)
    rw [e₁, e₂, he, chr_add]
    ring
  have hZ' : OffZero (e := fun i => (ex D a n i : ℤ)) V T k h' := fun j y hy => by
    show h j y * _ = 0
    rw [hZ j y hy, zero_mul]
  have d₁ : DifferentiableAt ℂ (fun b => h' i (s b)) b₀ :=
    differentiableAt_reads hσ hU T hD hN hPg hR' hZ' i s ho hd hb₀ hi
  have d₂ : DifferentiableAt ℂ (fun b => ev _ σ _ (u i) (s b)) b₀ :=
    (hd _ (u i)).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)
  have n₂ : ev _ σ _ (u i) (s b₀) ≠ 0 := by
    rw [← hu i _ hz Q₀ hO hQ₀]
    exact hg0
  refine (d₁.mul (d₂.inv n₂)).congr_of_eventuallyEq ?_
  filter_upwards [d₂.continuousAt.eventually_ne n₂] with b hb
  exact (mul_inv_cancel_right₀ hb _).symm

theorem open_holoZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) {d : ℕ} (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) :
    ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL e).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i) := by
  intro i j v hv
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have key := differentiableAt_readsZ hσ hU T hT hP hR hZ i (B := L.symm ⁻¹' C.e.target)
    (fun b => C.e.symm (L.symm b))
    (fun W => (GlobalTheory.ChartGlue.isOpen_over C.e (isOpen_ptsIn W)).preimage L.symm.continuous)
    (fun W u => (C.holo W u).comp L.symm.differentiableOn fun b hb => hb) (b₀ := L v)
    (by simpa using hv.1) (by
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩)
  refine DifferentiableAt.differentiableWithinAt ?_
  have := key.comp v L.differentiableAt
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem evR_mul' (f g : Rul Xo c) (y : FrPt Xo c (CAt σ)) : evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y :=
  evalAt_mul _ _ _ _ _

theorem evR_pow_ne {f : Rul Xo c} {y : FrPt Xo c (CAt σ)} (h : toC (evR Xo c f y) ≠ 0) (N : ℕ) :
    toC (evR Xo c (f ^ (N + 1)) y) ≠ 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [pow_succ, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) ih h


open GlobalTheory.AllWt GlobalTheory.ShFam in
theorem tw_of_dec {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (κ : KeySec Xo c)
    (hNV : ∀ a n, Dom a n → NV Xo c σ a n) (G : WTZ E) (hG : G.2 = 0)
    (hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < D.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) (k : V.Comp) :
    Tw V (exZ D G) k (modelWt V G k) := by
  intro y
  set M : ℕ := ∑ τ : E →+* ℂ, ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs with hM
  have hMb : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → -G.1 (τ, i) ≤ M := fun τ i hi => by
    have h1 : (G.1 (τ, i)).natAbs ≤ ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs :=
      Finset.single_le_sum (f := fun i => (G.1 (τ, i)).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hi)
    have h2 : ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs ≤ M :=
      Finset.single_le_sum (f := fun τ => ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    have h3 : -G.1 (τ, i) ≤ ((G.1 (τ, i)).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    omega
  obtain ⟨n₁, hn0, ⟨m', hm'⟩, h, hh, h0⟩ := GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H D l Xo c σ y
  obtain ⟨m, rfl⟩ : ∃ m, n₁ = 2 * (m + 1) := ⟨m' - 1, by omega⟩
  set g : Rul Xo c := h ^ (M + 1) * (κ.ρ : Rul Xo c) ^ (M + 1) with hgdef
  have hh' : h ∈ secZ Xo c (fun i => (ex D 0 (2 * (m + 1)) i : ℤ)) := by
    rw [secZ_nat]; exact hh
  have hg0 := mul_mem_secZ (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ hh' M) (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ κ.mem M)
  have hg : g ∈ sec Xo c (fun _ => M + 1) (2 * ((M + 1) * m)) := by
    rw [← secZ_nat]
    convert hg0 using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, keyEx]
      ring
    · simp [ex, keyEx]
  set a : (E →+* ℂ) × ℕ → ℕ := fun x => if x.2 < D.mult x.1 then (G.1 x + (M + 1)).toNat else 0 with ha
  have haZ : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → (a (τ, i) : ℤ) = G.1 (τ, i) + (M + 1) := fun τ i hi => by
    show ((if i < D.mult τ then (G.1 (τ, i) + (M + 1)).toNat else 0 : ℕ) : ℤ) = _
    rw [if_pos hi, Int.toNat_of_nonneg (by linarith [hMb τ i hi])]
  have hDa : Dom a (2 * ((M + 1) * m)) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul _⟩
    simp only [ha]
    split_ifs with h1 h2 h2
    · exact Int.toNat_le_toNat (by linarith [hdec τ i j hij h1])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hEx : exZ D (wtZ a (2 * ((M + 1) * m))) = exZ D (G + wtZ (fun _ => M + 1) (2 * ((M + 1) * m))) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp only [exZ, wtZ, Prod.snd_add, hG, zero_add]
    · simp [exZ, wtZ]
      exact haZ τ i i.2
  have hκ : toC (evR Xo c (κ.ρ : Rul Xo c) y) ≠ 0 := fun hz => by
    have e₁ : evR Xo c (κ.ρ : Rul Xo c) y * evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y = 1 := by
      rw [← evR_mul', Units.mul_inv]
      exact evalAt_one _ _ _ ((GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c).1.test _ _)
    have e₂ : toC (evR Xo c (κ.ρ : Rul Xo c) y) * toC (evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y) = 1 := e₁
    rw [hz, zero_mul] at e₂
    exact zero_ne_one e₂
  refine ⟨a, fun _ => M + 1, _, _, g, hDa, hNV _ _ hDa, ⟨fun _ => antitone_const, even_two_mul _⟩, hg, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AllWt.exZ_wtZ, ← GlobalTheory.AllWt.exZ_wtZ, hEx]
    exact funext fun i => by first | exact Formalism.L2.Pj.exZ_add _ _ i | exact GlobalTheory.AllWt.exZ_add _ _ i | (cases i <;> rfl)
  · rw [← modelWt_wtZ, modelWt_congr V hσ hU hEx, modelWt_add V (hG ▸ Even.zero)
      ⟨(((M + 1) * m : ℕ) : ℤ), by simp [wtZ]; ring⟩, modelWt_wtZ]
  · rw [hgdef, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) (evR_pow_ne h0 M) (evR_pow_ne hκ M)

end PositivityTheory.UnitarySelfGeneration.VuOnto
end
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open GlobalTheory.CxPts

theorem exists_comb {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} (he : e none = 0) {la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : ∀ k, Tw V e k (la k))
    {P : ∀ k, Frame (V.X k).Ψ r → ℂ} (hP : ∀ k, P k ∈ (V.X k).SS (la k)) :
    ∃ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ extVanZ T.X e) ∧
      ∀ k, ∀ x ∈ (V.X k).dom, P k x = ∑ i, as i * rdU V (fs i) k x := by
  classical
  letI := V.fin
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  obtain ⟨d, hsm, hpr⟩ := GlobalTheory.T.toroidal_flag_smooth_projective E H D l Xo c T
  let R : GlobalTheory.AnRead (flagStr T.X) σ d := GlobalTheory.AnRead.all _ _ _
  choose hk hf hR hZ using fun k => open_secZ hU T (hT k) (hP k).1.1
  have hh : ∀ k, hk k ∈ R.holSec (T.X.LL e) := fun k =>
    ⟨hf k, holoOn_bdZ hσ hU T he (hP k) R (hR k) (hZ k) (open_holoZ hσ hU T (hT k) (hP k).1.1 R (hR k) (hZ k))⟩
  let h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := ∑ k, hk k
  have hh' : h ∈ R.holSec (T.X.LL e) := Submodule.sum_mem _ fun k _ => hh k
  have hap : ∀ (i : (T.X.LL e).ι) y, h i y = ∑ k, hk k i y := fun i y => by simp only [h, Finset.sum_apply]
  have hv : ∀ i y, y ∉ ptsIn (flagStr T.X) σ (flagOpen T.X) → h i y = 0 := fun i y hy => by
    simp only [h, Finset.sum_apply]
    exact Finset.sum_eq_zero fun k _ => hZ k i y fun x hx e' => hy (mem_open_of_ptY T _ _ e')
  have hRh : ∀ k, Reads V T e k (P k) h := fun k x hx i y hz Q t hxy hQ ht => by
    have e₁ : h i y = hk k i y := by
      refine (hap i y).trans (Finset.sum_eq_single k (fun k' _ hne => hZ k' i y fun x' hx' e' => hne ?_)
        fun h' => (h' (Finset.mem_univ _)).elim)
      have e'' : T.X.ptY (V.un k' ⟨x', hx'⟩) = zOf y := e'
      have hlx : T.X.F.Lies (zOf y) (V.un k' ⟨x', hx'⟩) := e'' ▸ T.X.lies_ptY _
      obtain ⟨t', ht'⟩ := GlobalTheory.FlagMod.Frames.ChartFr.exists_frBor (z := zOf y) hQ hlx
      obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k k' _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
      exact (Sigma.mk.inj h').1
    rw [e₁]
    exact hR k x hx i y hz Q t hxy hQ ht
  have hB := T.X.F.isLB_LL e
  obtain ⟨xC, hx⟩ := (GlobalTheory.AnRead.bijective_valC hpr R hB).2 ⟨h, hh'⟩
  have hxv : GlobalTheory.SecC.val xC = h := congrArg Subtype.val hx
  have hlft : LocallyOfFiniteType (flagStr T.X) := by
    haveI := hsm
    haveI : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
    infer_instance
  obtain ⟨m, as, ss, hss, hsum⟩ := GlobalTheory.T.complex_section_finite_combination c.F T.X.YY (flagStr T.X) σ hlft _ hB (flagOpen T.X) xC
    (fun i y hy => by rw [hxv]; exact hv i y hy)
  refine ⟨m, as, fun j => ruleTop T.X _ (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)), fun j => ?_,
    fun k => GlobalTheory.T.holomorphic_extension_section_reading E H D l Xo c r σ V T e k (P k) h (hRh k) m as ss (hxv.symm.trans hsum)⟩
  refine ruleTop_mem_extVanZ.2 (mem_vanOut_iff_le.2 ?_)
  have e' : toSec (GlobalTheory.Vanishing.H0.ofSec (flagStr T.X) ⊤ (ss j)) = ss j :=
    (Equiv.ofBijective _ GlobalTheory.Vanishing.H0.bijective_ofSec_top).symm_apply_apply (ss j)
  rw [e']
  exact hss j

end PositivityTheory.UnitarySelfGeneration.VuOnto
