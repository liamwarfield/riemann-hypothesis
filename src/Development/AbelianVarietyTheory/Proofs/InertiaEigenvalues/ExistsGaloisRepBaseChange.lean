module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraic
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem weight_localisation_regular_algebraic : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ),
    (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  intro D i P τ
  rw [D.nbc.embAV_inf i P]
  exact D.nbc.infW_alg _ _ τ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightLocalisationRegularAlgebraicStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infWt_nodup_and_half_integral : ∀ (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (τ : D.host.E →+* ℂ), (D.naut.infWt i τ).Nodup ∧ ∀ z ∈ D.naut.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
  first | exact @GlobalTheory.weight_localisation_regular_algebraic | exact GlobalTheory.weight_localisation_regular_algebraic | (intros; apply GlobalTheory.weight_localisation_regular_algebraic <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.GalIsoBC

theorem lpTw_lpZero (D : D7) (w : PlE D.host) (s : ℝ) : D.naut.lpTw (D.naut.lpZero w) s = D.naut.lpZero w := by
  have hu : D.naut.unr (D.naut.lpTw (D.naut.lpZero w) s) := (D.naut.unr_tw _ s).2 (D.naut.lpZero_unr w)
  have e3 : D.naut.frobEig (D.naut.lpTw (D.naut.lpZero w) s) = D.naut.frobEig (D.naut.lpZero w) := by
    rw [D.naut.frobEig_tw _ s (D.naut.lpZero_unr w), D.naut.frobEig_zero]; simp
  rw [D.naut.unr_eq_lpUnr _ hu, e3, ← D.naut.unr_eq_lpUnr _ (D.naut.lpZero_unr w)]

theorem lpTw_foldr (D : D7) (w : PlE D.host) {β : Type*} (f : β → D.naut.LP w) (s : ℝ) :
    ∀ L : List β, D.naut.lpTw (L.foldr (fun x acc => D.naut.lpSum (f x) acc) (D.naut.lpZero w)) s =
      L.foldr (fun x acc => D.naut.lpSum (D.naut.lpTw (f x) s) acc) (D.naut.lpZero w)
  | [] => lpTw_lpZero D w s
  | x :: L => by
      simp only [List.foldr_cons]
      rw [D.naut.lpTw_sum, lpTw_foldr D w f s L]

theorem map_list_sum {α γ : Type*} (h : α → γ) :
    ∀ L : List (Multiset α), L.sum.map h = (L.map fun x => x.map h).sum
  | [] => by simp
  | x :: L => by simp [Multiset.map_add (f := _), map_list_sum h L]

theorem le_list_sum {α : Type*} {x : Multiset α} : ∀ {L : List (Multiset α)}, x ∈ L → x ≤ L.sum
  | [], hx => by simp at hx
  | y :: L, hx => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Multiset.le_add_right _ _
      · exact le_trans (le_list_sum hx) (Multiset.le_add_left _ _)

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

theorem flatMap_single {γ : Type*} (f : ℕ → γ) : ∀ l : List ℕ, List.flatMap (fun a => [f a]) l = l.map f
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_single f l]

theorem spehLoc_eq (D : D7) (p : Formalism.BasicNotions.Part D.naut.CG) (w : PlE D.host) :
    spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (k : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - (k : ℝ))) acc) (D.naut.lpZero w) := by
  unfold spehLoc
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℝ)), List.foldr_map]

theorem isoInf_eq (D : D7) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut Pa τ = (Pa.map fun p => ((List.range p.d).map fun k : ℕ =>
        (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (k : ℂ)))).sum).sum := by
  unfold isoInf
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [bind, pure]
  rw [flatMap_single (fun a : ℕ => (a : ℂ)), List.map_map]
  rfl

end GlobalTheory.GalIsoBC

namespace GlobalTheory.GalIsoBC

end GlobalTheory.GalIsoBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeRec

theorem pull_iso_of_cls_eq {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (σ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (h : GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls τ) : Nonempty (pull I k v σ ≅ pull I k v τ) := by
  have h1 : σ.cl = τ.cl := by
    have := (Sigma.mk.inj_iff.1 h).2
    exact eq_of_heq this
  obtain ⟨φ⟩ := GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h1
  exact ⟨Rep.mkIso (Representation.Equiv.mk φ.toLinearEquiv fun g =>
    φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g))⟩

end GlobalTheory.TypeRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec

theorem exists_isComp_of_rowDepth {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h : GlobalTheory.HeightCounting.RowDepth D rep) : ∃ cp, IsComp I rep cp := by
  have : ∀ σ k v, ∃ c : GlobalTheory.GoodTypes.LocRep D k, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ c = pull I k v τ := by
    intro σ k v
    obtain ⟨s, τ, hs, h1, -⟩ := h σ k v
    have gen : ∀ (w) (e : s.w = w), ∃ τ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)),
        GlobalTheory.HeightCounting.IsLocS (rep σ).S s (e ▸ τ') := by
      rintro _ rfl
      exact ⟨τ, h1⟩
    obtain ⟨τ', a⟩ := gen _ hs
    exact ⟨_, s, hs, τ', a, rfl⟩
  choose c hc using this
  exact ⟨c, hc⟩

end GlobalTheory.TypeRec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramified
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SphSeg

theorem isSubquotient_prodIrr_prinSeries {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = h)
    (μ : Fin h → kˣ →* ℂˣ) (hμ : ∀ a, IsSmoothChar (μ a)) (hx : ∀ a, x a = IrrGL.ofChar (μ a) (hμ a)) :
    IsSubquotient (prodIrr x hd) (prinSeries μ) := by
  obtain rfl : x = fun a => IrrGL.ofChar (μ a) (hμ a) := funext hx
  let φ := multiProdEquiv (stdBlocks (fun a => (IrrGL.ofChar (μ a) (hμ a)).1) hd) fun a =>
    (LocGL.equivRep (IrrRep.det (Fin 1) (μ a) (hμ a))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (PermPrin.isSubquotient_multiProd_prinSeries _ μ)

end GlobalTheory.SphSeg

namespace GlobalTheory.SphSeg

theorem len_eq_one_and_isUnramChar : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing →
    GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsSpherical y.rep →
    Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  intro hLM hSC hZP hGL hBZ k _ _ _ _ _ Δ y hL hS
  obtain ⟨N, c⟩ := y
  obtain ⟨hd, hc⟩ := id hL
  have hsub : IsSubquotient c.rep.ρ (prodIrr Δ.term hd) := hc.isSubquotient
  have hsph := GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k Δ.len N Δ.term hd _ c.rep.ρ hsub hS
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have key : ∀ x z : IrrGL (k := k), x = z → IsSpherical x.rep → IsSpherical z.rep := by
    rintro _ _ rfl h; exact h
  have hU : Δ.first.IsUnramChar :=
    GlobalTheory.T.isUnramifiedChar_of_cuspidal_spherical hGL hBZ hZP k Δ.first Δ.isCusp_first (key _ _ h0 (hsph _))
  refine ⟨?_, hU⟩
  obtain ⟨μ, hμ, hfirst⟩ := hU
  have hμs := isSmoothChar_of_isUnram hμ
  have hterm : ∀ a, Δ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by simp only [Segment.term, IrrGL.nu, hfirst, IrrGL.tw_ofChar]
  have hd1 : Δ.d = 1 := congrArg Sigma.fst hfirst
  have hN : N = Δ.len := by
    have h2 : ∑ a, (Δ.term a).1 = N := hd
    rw [Segment.sum_term_fst, Segment.deg, hd1, mul_one] at h2
    exact h2.symm
  subst hN

  let Γ := Segment.ofChar μ hμs Δ.len Δ.len_pos
  have hterm' : ∀ a, Γ.term a = IrrGL.ofChar (μ * absPow k ((a : ℕ) : ℂ)) (hμs.mul (isSmoothChar_absPow _)) :=
    fun a => by
      show (IrrGL.ofChar μ hμs).nu _ = _
      simp only [IrrGL.nu, IrrGL.tw_ofChar]
  have hd' : ∑ a, (Γ.term a).1 = Δ.len := (Segment.sum_term_fst _).trans (mul_one _)
  have hP := isSubquotient_prodIrr_prinSeries Δ.term hd _ _ hterm
  have hP' := isSubquotient_prodIrr_prinSeries Γ.term hd' _ _ hterm'
  let χ' := μ * absPow k (((Δ.len : ℂ) - 1) / 2)
  have hu' : IsUnram χ' := fun x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  have hχs : IsSmoothChar χ' := isSmoothChar_of_isUnram hu'
  obtain ⟨f, hf⟩ := embeds_detRep_segment hμs Δ.len_pos hd'

  obtain ⟨ϖ, hϖ⟩ := LocGL.exists_uniformizer k
  have hu : ∀ i : Fin Δ.len, IsUnram (μ * absPow k ((i : ℕ) : ℂ)) := fun i x hx => by
    rw [MonoidHom.mul_apply, hμ x hx, isUnram_absPow k _ x hx, one_mul]
  let α : Fin Δ.len → ℂˣ := fun i => (μ * absPow k ((i : ℕ) : ℂ)) ϖ
  have heq : (fun i => unrChar k (α i)) = fun i : Fin Δ.len => μ * absPow k ((i : ℕ) : ℂ) :=
    funext fun i => (eq_unrChar (hu i) hϖ).symm
  have hA : HasSatake c.rep.ρ α := ⟨c.rep.irr, hS, by rw [heq]; exact hsub.trans hP⟩
  have hB : HasSatake (IrrRep.det (Fin Δ.len) χ' hχs).ρ α :=
    ⟨(IrrRep.det (Fin Δ.len) χ' hχs).irr, isSpherical_detRep hu',
      by rw [heq]; exact (IsSubquotient.of_injective f hf).trans hP'⟩
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_equiv_of_same_satakeParameters hBZ k Δ.len α c.rep (IrrRep.det (Fin Δ.len) χ' hχs) hA hB
  have hL2 := (GlobalTheory.T.isLanglandsClassification_detCharacter hSC k Δ.len χ' hχs).of_equiv E.symm
  have hL1 := hL.isL
  have hm := (hLM k).1 _ _ ⟨Δ.len, c⟩ hL1 hL2
  have := congrArg Multiset.card hm
  simpa using this.symm

end GlobalTheory.SphSeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramifiedStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSegmentRep_length_one_unramified : LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsSpherical y.rep → Δ.len = 1 ∧ Δ.first.IsUnramChar := by
  first | exact @GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | exact GlobalTheory.SphSeg.len_eq_one_and_isUnramChar | (intros; apply GlobalTheory.SphSeg.len_eq_one_and_isUnramChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceInjectivity

theorem eq_or_conj_of_comap_eq {L : Type} [Field L] [NumberField L] [IsCMField L]
    (P P' : HeightOneSpectrum (𝓞 L))
    (h : P.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) =
      P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L))) :
    P' = P ∨ ∀ x : 𝓞 L, x ∈ P'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ P.asIdeal := by
  set σ : 𝓞 L →+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L : 𝓞 L →+* 𝓞 L) with hσ
  have key : ∀ x ∈ P'.asIdeal, x ∈ P.asIdeal ∨ x ∈ P.asIdeal.comap σ := by
    intro x hx
    have hfix : IsCMField.complexConj L ((x * σ x : 𝓞 L) : L) = ((x * σ x : 𝓞 L) : L) := by
      simp [hσ, IsCMField.coe_ringOfIntegersComplexConj, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff (K := L) (x * σ x)).1 hfix
    have hy' : algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) y = x * σ x := RingOfIntegers.ext hy
    have h1 : y ∈ P'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := by
      rw [Ideal.mem_comap, hy']; exact P'.asIdeal.mul_mem_right _ hx
    rw [← h, Ideal.mem_comap, hy'] at h1
    rcases P.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [Ideal.mem_comap]; exact h2)
  have hsub : (P'.asIdeal : Set (𝓞 L)) ⊆ (P.asIdeal : Set (𝓞 L)) ∪ (P.asIdeal.comap σ : Set (𝓞 L)) :=
    fun x hx => key x hx
  have hmax : P'.asIdeal.IsMaximal := P'.isMaximal
  rcases Ideal.subset_union.1 hsub with h3 | h3
  · left
    exact HeightOneSpectrum.ext (hmax.eq_of_le P.isPrime.ne_top h3)
  · right
    have hpr : (P.asIdeal.comap σ).IsPrime := Ideal.comap_isPrime σ P.asIdeal
    have he := hmax.eq_of_le hpr.ne_top h3
    intro x
    rw [he, Ideal.mem_comap]
    rfl

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInjectivity

theorem not_mem_of_coprime {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (w : HeightOneSpectrum (𝓞 E)) (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) :
    ((q : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have hco : IsCoprime ((p : ℤ)) ((q : ℤ)) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using (Nat.coprime_primes hp hq).mpr hpq)
  have hco' : IsCoprime ((p : ℕ) : 𝓞 E) ((q : ℕ) : 𝓞 E) := by
    simpa using hco.map (Int.castRingHom (𝓞 E))
  exact Ideal.IsPrime.notMem_of_isCoprime_of_mem hco' h1

end GlobalTheory.PlaceInjectivity

namespace GlobalTheory.PlaceInj

theorem splitPlace_v_injective : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E), (∀ k v, (s k v).w = D.naut.plGw k v) → Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) := by
  intro D s hs ⟨k, v⟩ ⟨k', v'⟩ heq
  simp only at heq
  have hc : (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      (D.naut.plGw k' v').asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [← hs, ← hs, (s k v).w_under, (s k' v').w_under, heq]
  by_cases hk : k = k'
  · subst hk
    rcases GlobalTheory.PlaceInjectivity.eq_or_conj_of_comap_eq _ _ hc with h | h
    · have := D.naut.plGw_inj k h.symm
      subst this
      rfl
    · exfalso
      apply D.naut.plGw_nconj k v v'
      intro x y hxy
      have hconj : (IsCMField.ringOfIntegersComplexConj D.host.E y : D.host.E) = (x : D.host.E) := by
        rw [IsCMField.coe_ringOfIntegersComplexConj, hxy]
        apply D.host.φ₀.injective
        rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
        simp
      rw [h y, RingOfIntegers.ext hconj]
  · exfalso
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k' <;> simp_all [D.host.g_ne, D.host.g_ne.symm]
    have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈
        (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, map_natCast]; exact D.naut.plGw_over k v
    rw [hc, Ideal.mem_comap, map_natCast] at h1
    exact GlobalTheory.PlaceInjectivity.not_mem_of_coprime (D.host.g_prime k') (D.host.g_prime k) hg.symm _
      (D.naut.plGw_over k' v') h1

end GlobalTheory.PlaceInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.JacFactor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_comp_surj {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact e.isSimpleOrder

def piTensorBoolEquiv {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {X : Bool → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]
    (F : ∀ j, Representation ℂ (GL (Two a b j) R) (X j)) :
    Representation.Equiv ((piTensor F).comp (leviTwo R a b).toMonoidHom :
      Representation ℂ (GL a R × GL b R) (⨂[ℂ] j, X j)) (extTensor (F false) (F true)) :=
  .mk (Exponents.boolTensorEquiv (X := X)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show Exponents.boolTensorEquiv (X := X) (piTensor F (leviTwo R a b g) (PiTensorProduct.tprod ℂ x)) =
      extTensor (F false) (F true) g (Exponents.boolTensorEquiv (X := X) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, Exponents.boolTensorEquiv_tprod, Exponents.boolTensorEquiv_tprod, extTensor_tmul]
    rfl

theorem isIrreducible_extTensor {R a b W W' : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL a R) W) (ρ : Representation ℂ (GL b R) W')
    (hσ : σ.IsIrreducible) (hρ : ρ.IsIrreducible)
    (hSσ : ∀ φ : W →ₗ[ℂ] W, (∀ g x, φ (σ g x) = σ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id)
    (hSρ : ∀ φ : W' →ₗ[ℂ] W', (∀ g x, φ (ρ g x) = ρ g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id) :
    (extTensor σ ρ).IsIrreducible := by
  have h1 : (piTensor (Exponents.twoRep σ ρ)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => by cases j <;> assumption)
      (fun j => by cases j <;> assumption)
  have h2 := isIrreducible_comp_surj _ (leviTwo R a b).toMonoidHom (leviTwo R a b).surjective h1
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (piTensorBoolEquiv (Exponents.twoRep σ ρ)) h2

theorem nontrivial_of_isIrreducible {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ G Y} (hτ : τ.IsIrreducible) : Nontrivial Y := by
  haveI : IsSimpleOrder (Subrepresentation τ) := hτ
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤)
  ext v
  exact ⟨fun _ => trivial, fun _ => Subsingleton.elim v 0⟩

end GlobalTheory.JacFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure BR (k : Type) [Field k] (n : ℕ) : Type 1 where

  V : Type
  [ac : AddCommGroup V]
  [smul : Module ℂ V]

  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] BR.ac BR.smul

def one (w : IrrGL (k := k)) : BR k w.1 := ⟨_, w.rep⟩

def two {r t N : ℕ} (e : r + t = N) (A : BR k r) (C : BR k t) : BR k N :=
  ⟨_, ind₂ (stdSum e) (extTensor A.ρ C.ρ)⟩

def mp {d M : ℕ} (N : Fin d → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i)) : BR k M :=
  ⟨_, multiProd (stdBlocks N hM) fun i => (A i).ρ⟩

def pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : BR k N :=
  mp (fun i => (x i).1) hx fun i => one (x i)

def Iso {n : ℕ} (A C : BR k n) : Prop := Nonempty (A.ρ.Equiv C.ρ)

def Sm {n : ℕ} (A : BR k n) : Prop := IsSmooth A.ρ

theorem iso_refl {n : ℕ} (A : BR k n) : Iso A A := eqv_refl A.ρ

theorem iso_symm {n : ℕ} {A C : BR k n} (h : Iso A C) : Iso C A := eqv_symm (ρ := A.ρ) (σ := C.ρ) h

theorem iso_trans {n : ℕ} {A C D : BR k n} (h : Iso A C) (h' : Iso C D) : Iso A D :=
  eqv_trans (ρ := A.ρ) (σ := C.ρ) (τ := D.ρ) h h'

theorem sm_one (w : IrrGL (k := k)) : Sm (one w) := w.2.rep.smooth

theorem sm_pr {a N : ℕ} (x : Fin a → IrrGL (k := k)) (hx : ∑ i, (x i).1 = N) : Sm (pr x hx) := isSmooth_prodIrr x hx

theorem two_congr {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : Iso A A') (h' : Iso C C') :
    Iso (two e A C) (two e A' C') :=
  ind₂_congr e (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := C.ρ) (σ₂ := C'.ρ) h h'

theorem two_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : BR k r) (C : BR k s) (D : BR k t) (s₁ : Sm A) (s₂ : Sm C) (s₃ : Sm D) :
    Iso (two h₂ (two h₁ A C) D) (two h₄ A (two h₃ C D)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ C.ρ D.ρ s₁ s₂ s₃

theorem mp_head {d T M : ℕ} (N : Fin (d + 1) → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i))
    (hT : ∑ i : Fin d, N i.succ = T) (e : N 0 + T = M) :
    Iso (mp N hM A) (two e (A 0) (mp (fun i : Fin d => N i.succ) hT fun i => A i.succ)) :=
  multiProd_head (d := N) (X := fun i => (A i).V) (fun i => (A i).ρ) (stdBlocks N hM) e
    (stdBlocks (fun i : Fin d => N i.succ) hT)

theorem two_unit {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (N : Fin 0 → ℕ) (hN : ∑ i, N i = t)
    (C : ∀ i, BR k (N i)) : Iso (two e A (mp N hN C)) A :=
  ind₂_unit_right e A.ρ hA (d := N) (X := fun i => (C i).V) (fun i => (C i).ρ) (stdBlocks N hN)

theorem two_unit_pr {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL (k := k))
    (hy : ∑ i, (y i).1 = t) : Iso (two e A (pr y hy)) A :=
  two_unit e A hA _ hy _

theorem pr_succ {a t N : ℕ} (z : Fin (a + 1) → IrrGL (k := k))
    (hx : ∑ i : Fin a, (z i.succ).1 = t) (hz : ∑ i, (z i).1 = N) (e : (z 0).1 + t = N) :
    Iso (pr z hz) (two e (one (z 0)) (pr (fun i : Fin a => z i.succ) hx)) :=
  mp_head (fun i => (z i).1) hz (fun i => one (z i)) hx e

theorem of_iso {d h : ℕ} (y : Fin d → Fin h → IrrGL (k := k)) (N : Fin d → ℕ) {M c : ℕ} (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M) (z : Fin c → IrrGL (k := k)) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

attribute [irreducible] one two mp pr Iso Sm

theorem pr_congr {a b N : ℕ} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)} (h : List.ofFn x = List.ofFn z)
    (hx : ∑ i, (x i).1 = N) (hz : ∑ i, (z i).1 = N) : Iso (pr x hx) (pr z hz) := by
  obtain rfl : a = b := by simpa using congrArg List.length h
  obtain rfl := List.ofFn_injective h
  exact iso_refl _

theorem pr_cons {a b t N : ℕ} {w : IrrGL (k := k)} {x : Fin a → IrrGL (k := k)} {z : Fin b → IrrGL (k := k)}
    (h : List.ofFn z = w :: List.ofFn x) (hx : ∑ i, (x i).1 = t) (hz : ∑ i, (z i).1 = N) (e : w.1 + t = N) :
    Iso (pr z hz) (two e (one w) (pr x hx)) := by
  have hb : b = a + 1 := by simpa using congrArg List.length h
  subst hb
  have h' : z 0 :: List.ofFn (fun i : Fin a => z i.succ) = w :: List.ofFn x := List.ofFn_succ.symm.trans h
  have h₁ : z 0 = w := (List.cons.inj h').1
  have h₂ : (fun i : Fin a => z i.succ) = x := List.ofFn_injective (List.cons.inj h').2
  subst h₁ h₂
  exact pr_succ z hx hz e

theorem pr_append {a : ℕ} : ∀ {b c r t N : ℕ} (x : Fin a → IrrGL (k := k)) (y : Fin b → IrrGL (k := k)) (z : Fin c → IrrGL (k := k))
    (_ : List.ofFn z = List.ofFn x ++ List.ofFn y) (_ : a ≠ 0 ∨ b = 0) (hx : ∑ i, (x i).1 = r)
    (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (e : r + t = N),
    Iso (pr z hz) (two e (pr x hx) (pr y hy)) := by
  induction a with
  | zero =>
    intro b c r t N x y z h hab hx hy hz e
    obtain rfl : b = 0 := by simpa using hab
    obtain rfl : t = 0 := by simpa using hy.symm
    have e0 : N = r := e.symm
    subst e0
    exact iso_trans (pr_congr (by simpa using h) hz hx) (iso_symm (two_unit_pr e _ (sm_pr x hx) y hy))
  | succ a ih =>
    intro b c r t N x y z h _ hx hy hz e
    have hx' : List.ofFn x = x 0 :: List.ofFn fun i : Fin a => x i.succ := List.ofFn_succ
    have hs : (x 0).1 + ∑ i : Fin a, (x i.succ).1 = r := (Fin.sum_univ_succ fun i => (x i).1).symm.trans hx
    have A := pr_cons hx' rfl hx hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain rfl : (x 0).1 = r := by simpa using hs
      have B := iso_trans A (two_unit_pr hs _ (sm_one (x 0)) (fun i : Fin 0 => x i.succ) rfl)
      refine iso_trans (pr_cons (w := x 0) (by simpa using h) hy hz e) ?_
      exact two_congr e (iso_symm B) (iso_refl _)
    · let L := (List.ofFn fun i : Fin a => x i.succ) ++ List.ofFn y
      have hL : List.ofFn L.get = L := List.ofFn_get L
      have hT : ∑ i, (L.get i).1 = ∑ i : Fin a, (x i.succ).1 + t := by
        have := congrArg (fun l : List (IrrGL (k := k)) => (l.map Sigma.fst).sum) hL
        simp only [L, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
        rw [← hy]
        exact this
      have e' : (x 0).1 + (∑ i : Fin a, (x i.succ).1 + t) = N := by omega
      have B := pr_cons (w := x 0) (z := z) (x := L.get) (by rw [h, hx', hL]; rfl) hT hz e'
      have C := ih (fun i => x i.succ) y L.get hL (Or.inl ha.ne') rfl hy hT rfl
      have D := two_assoc hs e rfl e' (one (x 0)) (pr (fun i : Fin a => x i.succ) rfl) (pr y hy)
        (sm_one _) (sm_pr _ _) (sm_pr _ _)
      exact iso_trans B (iso_trans (two_congr e' (iso_refl _) C) (iso_trans (iso_symm D)
        (two_congr e (iso_symm A) (iso_refl _))))

end GlobalTheory.ProdFlatten
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockType

theorem blockChar_eventually_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  intro k _ _ _ _ r t χ hχ
  have hval : Topology.IsOpenEmbedding (Units.val : kˣ → k) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hV : IsOpen ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)) := hval.isOpenMap _ hχ
  have hd : Continuous fun g : GL (Fin (r + t)) k =>
      (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det :=
    (Units.continuous_val.matrix_submatrix _ _).matrix_det
  refine ⟨(fun g : GL (Fin (r + t)) k => (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ⁻¹'
      ((Units.val : kˣ → k) '' (χ.ker : Set kˣ)), hV.preimage hd, ?_, ?_⟩
  · refine ⟨1, χ.ker.one_mem, ?_⟩
    simp only [Units.val_one]
    rw [Matrix.submatrix_one _ (Fin.natAdd_injective t r), Matrix.det_one]
  · rintro g ⟨u, hu, he⟩
    rw [blockChar_eq χ g u he, MonoidHom.mem_ker.1 hu, Units.val_one]

end GlobalTheory.BlockType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  first | exact @GlobalTheory.BlockType.blockChar_eventually_one | exact GlobalTheory.BlockType.blockChar_eventually_one | (intros; apply GlobalTheory.BlockType.blockChar_eventually_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffTendsto
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec.TwistInert

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem valuation_lt_one_iff_tendsto (x : K) :
    valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h1 : 1 ≤ valuation K x := not_lt.1 hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ h1
  exact absurd hn (not_lt.2 h2)

theorem valuation_lt_one_map (f : K →+* L) (hf : Continuous f) {x : K} (hx : valuation K x < 1) :
    valuation L (f x) < 1 := by
  rw [valuation_lt_one_iff_tendsto] at hx ⊢
  simpa [Function.comp_def, map_pow] using (hf.tendsto 0).comp hx

end Val

def twistEquiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) (χ : G →* ℂˣ) :
    (GlobalTheory.SmGL.twist π χ).Equiv (GlobalTheory.SmGL.twist σ χ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => LinearMap.ext fun x => by
    have e := LinearMap.congr_fun (φ.isIntertwining' g) x
    simp only [LinearMap.comp_apply] at e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, GlobalTheory.SmGL.twist_apply, map_smul]
    congr 1

end GlobalTheory.TypeRec.TwistInert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodProper

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

theorem polAt_of_fibre {S Z : Scheme.{0}} {K : Type} [Field K] {t : SAB H S} {u : SAB H Z} {t' : SAB H (Sp K)}
    {x : Sp K ⟶ S} {y : Sp K ⟶ Z} (m : SABMap t' t x) (n : SABMap t' u y) (hp : IsProper u.G.hom)
    (hA : RelAmple u.G u.PP.L) (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) t.G x (pullback.fst t.G.hom x) := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m.φ = pullback.fst t.G.hom x ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G (𝟙 _) ψ :=
    m.cart.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have g₃ : IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _ ≫ y) (ψ ≫ n.φ) := g₂.comp n.cart
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull (ψ ≫ n.φ)) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) (pull_isLB u.PP.isLB _)
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ h₁.symm).symm
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap n) _ rfl)
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₃.1 hp
  have hq := amplePt Z K (𝟙 _ ≫ y) u.G ((Over.pullback x).obj t.G) _ g₃ u.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    u.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

theorem isProper_of_abLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  intro E _ _ _ H Dw l Xo T x t t' m₁ m₂ hab
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  have hW : GlobalTheory.LN.CDvr T.V := ⟨T.dvr, T.cpl, T.ch0⟩
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H T.V hW t
    (polAt_of_fibre m₂ m₁ Xo.univ.proper Xo.univ.ample Xo.univ.ktriv)
    (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (T.V ⧸ maximalIdeal T.V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (T.V ⧸ maximalIdeal T.V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick T.V (maximalIdeal T.V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (isAbelianScheme_of_unif_of_subsingleton l₁ l₂ T.V T.cpl P.D P.A t.G t.semi P.U hs).proper

end GlobalTheory.GoodProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUnivStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_semiAbelian_triple_of_abelianLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  first | exact @GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | exact GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | (intros; apply GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUTestNontrivial
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {L : LB G.left} {L' : LB G'.left} {L'' : LB G''.left}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}


open IsLocalRing in
theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExist

theorem exists_algCl {p : ℕ} [Fact p.Prime] {z : ℂ_[p]} (hz : IsAlgebraic ℚ_[p] z) :
    ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = z := by
  have h1 : IsIntegral (PadicAlgCl p) z := (hz.tower_top (PadicAlgCl p)).isIntegral
  have h2 : (minpoly (PadicAlgCl p) z).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1)
  exact minpoly.mem_range_of_degree_eq_one _ _ h2

theorem exists_factor_algCl {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ b : F →+* PadicAlgCl p, ∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (b x) = φ x := by
  have hex : ∀ x : F, ∃ y : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] y = φ x := fun x => by
    apply exists_algCl
    have h1 : IsAlgebraic ℚ (φ x) := by
      have := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom
      simpa using this
    exact h1.tower_top ℚ_[p]
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; exact map_mul φ x y
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add (f := _), hf, hf, hf]; exact map_add φ x y

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_inv {x : K} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have h := vV_mul (V := V) hx (inv_ne_zero hx)
  have h1 : vV V (1 : K) = 0 := by simp [vV]
  rw [mul_inv_cancel₀ hx, h1] at h
  omega

theorem norm_lt_one_iff_vV_pos {C : Type} [NormedField C] (c : K →+* C)
    (hn : ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V K)) {y : K} (hy : y ≠ 0) :
    ‖c y‖ < 1 ↔ 0 < vV V y := by
  have key : ∀ x, ‖c x‖ ≤ 1 ↔ 0 ≤ vV V x := fun x =>
    (hn x).trans (Set.mem_range.trans (GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff (V := V) x))
  have h0 : 0 < ‖c y‖ := norm_pos_iff.2 ((map_ne_zero c).2 hy)
  have hi := key y⁻¹
  rw [map_inv₀, norm_inv, vV_inv hy, inv_le_one₀ h0] at hi
  constructor
  · intro h
    by_contra h'
    have := hi.2 (by omega)
    linarith
  · intro h
    by_contra h'
    have := hi.1 (not_lt.1 h')
    omega

end Val

theorem mem_iff_vLa_pos {F : Type} [Field F] [NumberField F] (la : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F)
    (hx : (x : F) ≠ 0) : x ∈ la.asIdeal ↔ 0 < vLa la (x : F) := by
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  have h0 : la.valuation F (x : F) ≠ 0 := (la.valuation F).ne_zero_iff.2 hx
  have e := WithZero.log_lt_log h0 one_ne_zero
  rw [WithZero.log_one] at e
  change _ ↔ 0 < -WithZero.log (la.valuation F (x : F))
  rw [← e]
  omega

theorem exists_isReading : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p])
    (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes →
    ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  intro p _ F _ _ φ T io e ho hT
  obtain ⟨q, hq, c, hn⟩ := GlobalTheory.DegenerateTest.exists_padic_embedding T.V hT

  have ha : ∀ x : 𝓞 F, ‖c (io (x : F))‖ < 1 ↔ x ∈ (placeAt φ).asIdeal := by
    intro x
    by_cases hx : (x : F) = 0
    · have hx' : x = 0 := by exact_mod_cast hx
      subst hx'
      simp
    rw [norm_lt_one_iff_vV_pos c hn ((map_ne_zero io).2 hx), ho.2, mem_iff_vLa_pos _ x hx]
    constructor
    · intro h
      exact pos_of_mul_pos_right h (by positivity)
    · intro h
      exact mul_pos (by exact_mod_cast ho.1) h

  have hqp : q = p := by
    have h1 := (ha (p : 𝓞 F)).2 (natCast_mem_placeAt φ)
    have e1 : c (io (((p : ℕ) : 𝓞 F) : F)) = algebraMap ℚ_[q] (PadicAlgCl q) (p : ℚ_[q]) := by simp
    rw [e1, PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff] at h1
    exact (Nat.prime_dvd_prime_iff_eq hq.out (Fact.out : p.Prime)).1 h1
  subst hqp
  obtain ⟨b, hb⟩ := exists_factor_algCl φ
  have hbn : ∀ x, ‖b x‖ = ‖φ x‖ := fun x => by
    rw [← hb, ← PadicComplex.coe_eq, PadicComplex.norm_extends]
  obtain ⟨g, hg⟩ := GlobalTheory.EmbThroughCompletion.exists_conj (c.comp io) b
    (GlobalTheory.EmbThroughCompletion.norm_lt_one_iff (placeAt φ) _ _ ha
      (fun x => by rw [hbn]; exact (mem_placeAt φ x).symm))
  refine ⟨(algebraMap (PadicAlgCl q) ℂ_[q]).comp ((g : PadicAlgCl q →+* PadicAlgCl q).comp c), ?_, ?_⟩
  · intro a
    simp only [RingHom.comp_apply]
    have := hg a
    simp only [RingHom.comp_apply] at this
    rw [RingHom.coe_coe, this, hb]
  · intro x
    simp only [RingHom.comp_apply]
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, RingHom.coe_coe, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv g, PadicAlgCl.spectralNorm_eq, hn]
    rfl

end GlobalTheory.GeoTie.ReadExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidueStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes → ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  first | exact @GlobalTheory.GeoTie.ReadExist.exists_isReading | exact GlobalTheory.GeoTie.ReadExist.exists_isReading | (intros; apply GlobalTheory.GeoTie.ReadExist.exists_isReading <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.GLp.reduction_GL_surjective : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), Function.Surjective (GlobalTheory.GLp.red g n) :=
  fun g _ n => GlobalTheory.GLp.red_surjective g n
end
