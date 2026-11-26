module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpanFrame

open GlobalTheory.AmpleSpan

theorem secScal_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (a : ℤ)
    {T T' : Over S} (k : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (k ▷ A) (whiskerRight_snd k A) s s') :
    GeneratorPullback.SecScal L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) s' (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s
      (k ▷ A).left 1 := by
  have e : (k ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  apply (secScal_const_iff hL e).2
  intro i Z r z hz
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
  have le := chart_le_res A L (k ▷ A) (whiskerRight_snd k A) a (fun _ => i)
  refine Eq.symm ((congrArg (gs r z _) (H fun _ => i)).trans ?_)
  exact (gs_res r z le hm _).trans (gs_pull r (k ▷ A).left z _ (le (x := r z) hm) _)

theorem valR_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}
    {ε' : K' → ℤ} {χ : Y ⟶ X} {χ' : Y' ⟶ X} {h : Y' ⟶ Y} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)}
    (H : GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1) {R : Type} [CommRing R] (x : Sp R ⟶ Y') (j : L.ι)
    (hx : ⊤ ≤ (x ≫ χ') ⁻¹ᵁ L.U j) :
    valR (x ≫ h) (LB.wchart L (fun _ : K => χ) (fun _ => j)) (s.f fun _ => j) =
      valR x (LB.wchart L (fun _ : K' => χ') (fun _ => j)) (s'.f fun _ => j) := by
  subst e
  have E := H (fun _ => j) (fun _ => j) (by rintro (a | a) (b | b) _ <;> rfl)
  have hm : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K' => h ≫ χ) (fun _ => j) ⊓ LB.wchart L (fun _ : K => h ≫ χ) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hx hz, Set.mem_iInter.2 fun _ => hx hz⟩
  have E' := congrArg (valR x _) E
  rw [HolHom.valR_res _ _ _ hm, resTop, map_one, one_mul] at E'
  exact (HolHom.valR_comp _ _ _ _).trans (E'.trans (HolHom.valR_res _ _ _ hm))

theorem exists_span_powOver (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ}
    (hN : 1 ≤ N) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ (m : ℕ) (b : Fin m → LB.Sec (powOver P.A P.L U N)), ∀ (X' Y' : Scheme.{0}) [IsAffine Y']
      (h : X' ⟶ (P.A.hom ⁻¹ᵁ U).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ U.toScheme), IsPullback h f' (P.A.hom ∣_ U) g →
      ∀ (K : Type) [Fintype K] (ε : K → ℤ) (φ : X' ⟶ P.A.left), h ≫ (P.A.hom ⁻¹ᵁ U).ι = φ → ∑ k, ε k = N →
      ∀ b' : Fin m → LB.Sec (LB.LinComb P.L (fun _ : K => φ) ε),
        (∀ i, GeneratorPullback.SecScal P.L _ _ (b' i) (fun _ : Fin N => (P.A.hom ⁻¹ᵁ U).ι) (fun _ => 1) (b i) h 1) →
        ∀ s, InSpan f' b' s := by
  obtain ⟨m, b₀, hb₀⟩ := exists_sections_span_affine hS S P N hN U hU
  obtain ⟨h₀, e₀, -, -, hE⟩ := translate_powOver_LPow P.A P.isLB N (U := U) (overRes (T := baseOver S) U)
    (𝟙 U.toScheme) (by simp)
  obtain ⟨E, hE⟩ := hE (IsIso.id _)
  refine ⟨m + 1, fun i => E.symm (b₀ i), fun X' Y' _ h f' g sq K _ ε φ e hε b' hb' s => ?_⟩
  let T' : Over S := Over.mk (g ≫ U.ι)
  have : IsAffine T'.left := ‹IsAffine Y'›
  let k : T' ⟶ overRes (T := baseOver S) U := Over.homMk g (by simp [T'])
  obtain ⟨h', e', sq', -, -⟩ := translate_powOver_LPow P.A P.isLB N (U := U) T' g rfl
  let b'' : Fin (m + 1) → LB.Sec (LPow P.A P.L N T') := fun i =>
    SecM.toSec P.A (SecAff.pull P.A P.L N k (SecM.ofSec P.A (b₀ i)))
  have hb'' : ∀ i, IsPullSec P.A P.L N (k ▷ P.A) (whiskerRight_snd k P.A) (b₀ i) (b'' i) := fun i =>
    (SecAff.isPullSec_iff P.A P.L N _ _ _).2 rfl
  have hsp := hb₀ T' k b'' hb''
  let θ := sq.isoIsPullback _ _ sq'
  have θ₁ : θ.hom ≫ h' = h := sq.isoIsPullback_hom_fst _ _ sq'
  have θ₂ : θ.hom ≫ (fst T' P.A).left = f' := sq.isoIsPullback_hom_snd _ _ sq'
  have θ₃ : θ.hom ≫ (snd T' P.A).left = φ := by rw [← e', ← Category.assoc, θ₁, e]
  obtain ⟨F, hF⟩ := exists_equiv_secScal P.isLB (h := θ.hom) (formEq_const (K := Fin 1) (K' := K)
    (ε := fun _ => (N : ℤ)) (ε' := ε) θ₃ (by simp [hε]))
  have θ₄ : θ.hom ≫ (k ▷ P.A).left ≫ h₀ = h := by
    rw [← cancel_mono (P.A.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, e₀, ← Over.comp_left, whiskerRight_snd, θ₃, e]
  refine InSpan.secScal P.isLB (h := θ.hom) (f := (fst T' P.A).left) (g := 𝟙 Y') (θ₂.trans (Category.comp_id _).symm)
    (t := b'') (s := F.symm s) ((inSpan_iff_mem_span P.A b'' _).2 (by rw [hsp]; trivial)) (fun i => ?_)
    ((hF _ _).2 (F.apply_symm_apply s))
  apply (secScal_iff_sval P.isLB).2
  intro Z r z J hJ
  rw [← SectionScalarValuation.secScal_sval (hb' i) r z hJ, ← SectionScalarValuation.secScal_sval (secScal_of_isPullSec P.A P.isLB N k (hb'' i)) _ z hJ,
    ← SectionScalarValuation.secScal_sval ((hE _ _).2 (E.apply_symm_apply (b₀ i))) _ z hJ, Category.assoc, Category.assoc, θ₄]

end GlobalTheory.SpanFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteSiteAlg
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FreeQuotientRank Formalism.L2.Pj Formalism.L2.Pj.QAt

section Norm

variable {V F C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F] [NormedField C] (f : F →+* C)
  (hf : ∀ v : V, ‖f (algebraMap V F v)‖ ≤ 1)

include hf

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V F] in
theorem norm_map_unit_eq_one (u : Vˣ) : ‖f (algebraMap V F u)‖ = 1 := by
  have h : ‖f (algebraMap V F u)‖ * ‖f (algebraMap V F (u⁻¹ : Vˣ))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  exact le_antisymm (hf _) (h.ge.trans (mul_le_of_le_one_right (norm_nonneg _) (hf _)))

theorem norm_map_eq_zpow_vV {π : V} (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ‖f x‖ = ‖f (algebraMap V F π)‖ ^ vV V x := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  have hv : vV V (u • algebraMap V F π ^ n) = n := by
    rw [vV, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
      PlaceCompletion.valV_algebraMap_of_isUnit u.isUnit,
      PlaceCompletion.valV_algebraMap_of_irreducible hπ, one_mul, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp
  rw [hv, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, norm_mul, norm_zpow,
    norm_map_unit_eq_one f hf, one_mul]

theorem norm_map_le_one_iff {π : V} (hπ : Irreducible π) (h1 : ‖f (algebraMap V F π)‖ < 1) (x : F) :
    ‖f x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V F) := by
  refine ⟨fun h => ?_, by rintro ⟨v, rfl⟩; exact hf v⟩
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have h0 : 0 < ‖f (algebraMap V F π)‖ := norm_pos_iff.2 ((map_ne_zero f).2
    ((map_ne_zero_iff _ (IsFractionRing.injective V F)).2 hπ.ne_zero))
  rw [norm_map_eq_zpow_vV f hf hπ hx, zpow_le_one_iff_right_of_lt_one₀ h0 h1] at h
  refine PlaceCompletion.exists_algebraMap_eq_of_valV_le_one ?_
  rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), ← WithZero.exp_zero, WithZero.exp_le_exp]
  rw [vV] at h
  omega

end Norm


open DiscEval in
theorem exists_finSite_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr) (e : ℕ), Tv.FinRes → OverLa w Tv.V io e →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, ‖ιT x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap Tv.V Tv.Fr)) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  refine ⟨?_, fun Tv io e hfin ho => ?_⟩
  · obtain ⟨T, io, h1, h2, -⟩ := PlaceCompletion.exists_initial_completion K₁ w
    exact ⟨T, io, h2, h1⟩
  haveI : Finite (IsLocalRing.ResidueField Tv.V) := hfin
  obtain ⟨p, _, _, _⟩ := exists_padicInt_algebra_finite Tv.V
  obtain ⟨i, hinj, hi⟩ := exists_injective_norm_le_one (p := p) Tv.V
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let ιT : Tv.Fr →+* ℂ_[p] := IsFractionRing.lift hinj
  have hι : ∀ v, ιT (algebraMap Tv.V Tv.Fr v) = i v := fun v => IsFractionRing.lift_algebraMap hinj v
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => by rw [hι]; exact hi v
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  have h0 : 0 < ‖i π‖ := norm_pos_iff.2 ((map_ne_zero_iff i hinj).2 hπ.ne_zero)
  have h1 : ‖i π‖ < 1 :=
    (hi π).lt_of_ne fun h => hπ.not_isUnit ((norm_map_eq_one_iff i hi hinj π).1 h)
  let Z : FinSite K₁ w :=
    { K := ℂ_[p]
      ι := ιT.comp io
      r := ‖i π‖ ^ e
      r_pos := pow_pos h0 e
      r_lt := pow_lt_one₀ h0.le h1 ho.1.ne'
      norm_ι := fun x hx => by
        rw [RingHom.comp_apply, norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hx), hι, ho.2 x,
          zpow_mul, zpow_natCast]
        rfl
      K₀ := algField p
      res := residueFieldInfiniteOn_algField p
      S := algDisc p
      S_disc := fun _ ht => ht.2
      S_dense := algDisc_dense p
      S_units := mul_mem_algDisc p }
  refine ⟨Z, ιT, rfl, norm_map_le_one_iff ιT hf hπ (by rw [hι]; exact h1), ?_⟩
  intro (s : Finset ℂ_[p]) hs
  have hsK : (s : Set ℂ_[p]) ⊆ algField p := fun x hx => (hs x hx).1.elim id fun h => h.1
  haveI := finiteDimensional_genField i hi s.finite_toSet
  set L := genField i (s : Set ℂ_[p])
  haveI : CharZero (integralClosure ℤ_[p] L) := RingHom.charZero (intEmb L)
  let T' : CDVR := { V := integralClosure ℤ_[p] L, cpl := isAdicComplete_integralClosure L }
  obtain ⟨j, hj⟩ := exists_comp_eq_of_mem_range _ (intEmb_injective L) i fun a =>
    (mem_range_intEmb_iff _ _).2 ⟨map_mem_genField i hi hsK a, hi a⟩
  let i' : FractionRing (integralClosure ℤ_[p] L) →+* ℂ_[p] := IsFractionRing.lift (intEmb_injective L)
  have hi' : ∀ v, i' (algebraMap _ _ v) = intEmb L v := fun v =>
    IsFractionRing.lift_algebraMap (intEmb_injective L) v
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[p] L)
  refine ⟨T', j, i', finite_residueField_integralClosure L, isLocalHom_of_intEmb_eq i hi L hinj hj,
    fun v => (hi' _).trans ((hj v).trans (hι v).symm),
    norm_map_le_one_iff i' (fun v => by rw [hi']; exact norm_intEmb_le_one L v) hπ' (by
      rw [hi', ← mem_maximalIdeal_iff_norm]
      exact hπ'.not_isUnit), fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := (mem_range_intEmb_iff L x).2 ⟨mem_genField_of_mem i hi hsK hx, (hs x hx).2⟩
  exact ⟨v, (hi' v).trans hv⟩

end GlobalTheory.ArcQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.PerFlow

open Matrix
open scoped ComplexConjugate ComplexOrder

section aux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma perFr_mem (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dif_pos τ.2]

lemma perFr_conj (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dite_eq_right h1, dif_pos h2, dif_pos h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (u : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ u =
      u + (s * τ.1 X.κ0 * hermC τ.1 X.Gm u (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  rw [EmbeddingHermitianPairs.flowMat_eq, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    EmbeddingHermitianPairs.wv_dot, X.tau_kappa0]
  funext a
  simp
  ring

lemma flow_mem {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ.1 i =
      perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i := by
  simp only [perFr_mem]
  split_ifs with hi
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    have hinv : (X.flowMat ξ τ (s τ))⁻¹ = X.flowMat ξ τ (-s τ) := by
      apply inv_eq_right_inv
      rw [EmbeddingHermitianPairs.flowMat_mul X hξ, add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero]
    have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
      EmbeddingHermitianPairs.hermC_emb _ _ _ _
    rw [hm, Matrix.mul_inv_rev, hinv, ← mulVec_mulVec, flowMat_mulVec, mulVec_add, mulVec_smul, he,
      map_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

lemma flow_conj (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (hi : i < X.p0) :
    perFr X (X.flow ξ s x) v (conjEmb τ.1) i =
      perFr X x v (conjEmb τ.1) i -
        s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i := by
  have hlt : X.p0 - 1 - i < r := by have := X.p0_le; omega
  simp only [perFr_conj X _ _ τ i ⟨_, hlt⟩ rfl]
  have hc : FD.col (mat (X.flow ξ s x) τ) ⟨_, hlt⟩ =
      X.flowMat ξ τ (s τ) *ᵥ FD.col (mat x τ) ⟨_, hlt⟩ := rfl
  have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
    EmbeddingHermitianPairs.hermC_emb _ _ _ _
  have he' : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 v) = conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← he, hermC_conj τ.1 X.Gm_herm]
  have hk : conj (τ.1 X.κ0) = -τ.1 X.κ0 := by
    rw [← EmbeddingHermitianPairs.emb_cc', X.cc_kappa0, map_neg]
  have h2 : conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) = -τ.1 X.κ0 * conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← hk, ← map_mul, ← map_mul]; rfl
  rw [hc, flowMat_mulVec, hermC_add_left, hermC_smul_left, he', h2]
  ring

def blockEquiv : Fin X.p0 ⊕ Fin (r - X.p0) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega))

lemma blockEquiv_inl (a : Fin X.p0) : blockEquiv X (.inl a) = Fin.castLE X.p0_le a := by
  apply Fin.ext; simp [blockEquiv]

lemma blockEquiv_inr (a : Fin (r - X.p0)) : ((blockEquiv X (.inr a) : Fin r) : ℕ) = X.p0 + a := by
  simp [blockEquiv]

def blk (P : Matrix (Fin X.p0) (Fin X.p0) ℂ) (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.reindex (blockEquiv X) (blockEquiv X) (fromBlocks P 0 0 Q)

lemma blk_mul (P P' : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q Q' : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    blk X P Q * blk X P' Q' = blk X (P * P') (Q * Q') := by
  simp [blk, fromBlocks_multiply]

lemma blk_one : blk X 1 1 = 1 := by
  simp [blk]

lemma blk_mulVec_inr (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (w : Fin r → ℂ) (i : Fin (r - X.p0)) :
    (blk X P Q *ᵥ w) (blockEquiv X (.inr i)) = ∑ k, Q i k * w (blockEquiv X (.inr k)) := by
  simp only [mulVec, dotProduct]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type]

lemma col_mul_blk (M : Matrix (Fin r) (Fin r) ℂ) (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (j : Fin X.p0) :
    FD.col (M * blk X P Q) (Fin.castLE X.p0_le j) =
      ∑ k, P k j • FD.col M (Fin.castLE X.p0_le k) := by
  funext a
  simp only [FD.col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ← blockEquiv_inl]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type, mul_comm]

lemma block_change (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ)
    (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ) (hA : ∀ τ, (A τ).det ≠ 0) (hB : ∀ τ, (B τ).det ≠ 0) :
    ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ),
      (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧
      ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  let P : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ :=
    fun τ => ((B τ).submatrix Fin.revPerm Fin.revPerm)ᵀ
  have hP : ∀ τ, (P τ).det ≠ 0 := fun τ => by
    simp only [P, det_transpose, det_submatrix_equiv_self]; exact hB τ
  let x' : Frame X.Ψ r := fun τ => (mat x τ * blk X (P τ) (A τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, mat x' τ = mat x τ * blk X (P τ) (A τ)⁻¹ := fun τ => rfl
  have hone : ∀ τ, blk X (P τ) (A τ)⁻¹ * blk X (P τ)⁻¹ (A τ) = 1 := fun τ => by
    rw [blk_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hP τ)),
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA τ)), blk_one]
  have hcol : ∀ τ j, X.colP x' τ j = ∑ k, P τ k j • X.colP x τ k := fun τ j => by
    unfold Data.colP
    rw [hm, col_mul_blk]
  refine ⟨x', AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩, fun v τ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rw [hm, det_mul]
    refine mul_ne_zero (hx τ).1 fun h0 => ?_
    have := congrArg det (hone τ)
    rw [det_mul, h0] at this
    simp at this
  · have hg : X.gramPos x' τ = (P τ)ᵀ * X.gramPos x τ * ((P τ)ᵀ)ᴴ := by
      ext a b
      rw [Data.gramPos_apply, hcol, hcol, hermC_sum_right]
      simp only [Matrix.mul_apply, hermC_smul_right, hermC_sum_left, hermC_smul_left,
        conjTranspose_apply, transpose_apply, Data.gramPos_apply, Complex.star_def]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hg]
    refine (X.gramPos_posDef hx τ).mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (by rw [det_transpose]; exact hP τ)))
  · have hlt : ∀ k : Fin (r - X.p0), X.p0 + k < r := fun k => by have := k.2; omega
    have hidx : ∀ k : Fin (r - X.p0), (⟨X.p0 + k, hlt k⟩ : Fin r) = blockEquiv X (.inr k) :=
      fun k => Fin.ext (blockEquiv_inr X k).symm
    simp only [perFr_mem, dif_pos (hlt _), hidx]
    rw [hm, Matrix.mul_inv_rev, inv_eq_right_inv (hone τ), ← mulVec_mulVec, blk_mulVec_inr]
  · have hr : ∀ (y : Frame X.Ψ r) (k : Fin X.p0), perFr X y v (conjEmb τ.1) k =
        hermC τ.1 X.Gm (X.colP y τ k.rev) (Data.emb τ.1 v) := fun y k =>
      perFr_conj X y v τ k (Fin.castLE X.p0_le k.rev) (by simp [Fin.val_rev]; omega)
    simp only [hr]
    rw [hcol, hermC_sum_left, ← Equiv.sum_comp Fin.revPerm]
    simp [P, hermC_smul_left]

end aux

theorem perFr_flow_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  intro E _ _ _ r X
  exact ⟨fun ξ hξ s x _ v τ i => ⟨flow_mem X hξ s x v τ i, flow_conj X ξ s x v τ i⟩,
    fun x hx A B hA hB => block_change X x hx A B hA hB⟩

end GlobalTheory.PerFlow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChangeStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  first | exact @GlobalTheory.PerFlow.perFr_flow_block | exact GlobalTheory.PerFlow.perFr_flow_block | (intros; apply GlobalTheory.PerFlow.perFr_flow_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
noncomputable section

namespace GlobalTheory.LetterDenom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section General

variable {σ R L : Type*} [CommRing R] [CommRing L]

theorem exists_map_eq_of_constantCoeff (φ : R →+* L) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.constantCoeff A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  classical
  have hcoe : ∀ B : MvPolynomial σ R, ((MvPolynomial.map φ B : MvPolynomial σ L) : MvPowerSeries σ L) =
      MvPowerSeries.map φ (B : MvPowerSeries σ R) := by
    intro B
    ext m
    simp [MvPolynomial.coeff_map]
  have hu : (A : MvPowerSeries σ R) * MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 = 1 := by
    apply MvPowerSeries.mul_invOfUnit
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    simpa [MvPolynomial.constantCoeff_eq] using hA
  have hP : (P : MvPowerSeries σ L) =
      MvPowerSeries.map φ (MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 * (G : MvPowerSeries σ R)) := by
    rw [map_mul, ← hcoe G, ← h, MvPolynomial.coe_mul, hcoe A, ← mul_assoc, ← map_mul, mul_comm _ (A : MvPowerSeries σ R), hu,
      map_one, one_mul]
  have hc : ∀ m, ∃ r, φ r = P.coeff m := by
    intro m
    rw [← MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  choose r hr using hc
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (r m), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  conv_rhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, hr]

theorem exists_map_eq_of_eval (φ : R →+* L) (a : σ → R) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.eval a A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  let s : σ → MvPolynomial σ R := fun x => MvPolynomial.X x + MvPolynomial.C (a x)
  let t : σ → MvPolynomial σ R := fun x => MvPolynomial.X x - MvPolynomial.C (a x)
  have h1 : MvPolynomial.constantCoeff (MvPolynomial.bind₁ s A) = 1 := by
    rw [← hA]
    have : (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R).comp (MvPolynomial.bind₁ s).toRingHom =
        MvPolynomial.eval a := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro x; simp [s]
    exact RingHom.congr_fun this A
  have h2 := congrArg (MvPolynomial.bind₁ fun x => MvPolynomial.map φ (s x)) h
  rw [map_mul, ← MvPolynomial.map_bind₁, ← MvPolynomial.map_bind₁] at h2
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_constantCoeff φ _ _ _ h1 h2
  refine ⟨MvPolynomial.bind₁ t Q, ?_⟩
  rw [MvPolynomial.map_bind₁, hQ, MvPolynomial.bind₁_bind₁]
  have : (fun x => MvPolynomial.bind₁ (fun i => MvPolynomial.map φ (t i)) (MvPolynomial.map φ (s x))) =
      MvPolynomial.X := by
    funext x
    simp [s, t]
  rw [this, MvPolynomial.bind₁_X_left]
  rfl

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eval_arcDetR (Dw : Datum H) (V : Type) [CommRing V] :
    MvPolynomial.eval (fun x : ArcLt Dw => if x.2.1 = x.2.2 then (1 : PowerSeries V) else 0)
      (arcDetR Dw V) = 1 := by
  classical
  unfold arcDetR
  rw [map_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [RingHom.map_det]
  convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := PowerSeries V)
  ext i k : 2
  simp [Matrix.one_apply]

theorem map_arcDetR (Dw : Datum H) (V K : Type) [CommRing V] [Field K] (φ : PowerSeries V →+* LaurentSeries K) :
    MvPolynomial.map φ (arcDetR Dw V) = arcDet Dw K := by
  unfold arcDetR arcDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i k : 2
  simp

theorem arcDetR_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [Nontrivial V] : arcDetR Dw V ≠ 0 := by
  intro h0
  have h1 := eval_arcDetR Dw V
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem den_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] {ϖ : V} (hϖ : ϖ ≠ 0) :
    MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V ≠ 0 := by
  refine mul_ne_zero ?_ (arcDetR_ne_zero Dw V)
  rw [Ne, MvPolynomial.C_eq_zero]
  refine mul_ne_zero ?_ PowerSeries.X_ne_zero
  intro h
  exact hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))

section Parts

variable (Dw : Datum H) (V K : Type) [CommRing V] [IsDomain V] [Field K] {ϖ : V}

theorem isDomain_letter (hϖ : ϖ ≠ 0) : IsDomain (ArcSR Dw V ϖ) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem algebraMap_letter_injective (hϖ : ϖ ≠ 0) :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B]
    (j : A →+* B) (hi : Function.Injective j) : j.Flat := by
  letI : Algebra A B := j.toAlgebra
  change Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : j a * x = 0 := hx
  have ha' : j a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem exists_lift (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ) :
    ∃ ψ : ArcSR Dw V ϖ →+* ArcS Dw K,
      ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ) := by
  have hu : IsUnit (((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
      (MvPolynomial.map φ)) (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · have hne : φ (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
        intro h
        apply den_ne_zero Dw V hϖ
        rw [hφ (h.trans (map_zero _).symm), map_zero, zero_mul]
      rw [RingHom.comp_apply, MvPolynomial.map_C]
      exact (hne.isUnit.map MvPolynomial.C).map _
    · rw [RingHom.comp_apply, map_arcDetR]
      exact IsLocalization.Away.algebraMap_isUnit _
  exact ⟨IsLocalization.Away.lift _ hu, IsLocalization.Away.lift_comp _ hu⟩

theorem denominators_gen {σ R L S S' : Type} [CommRing R] [CommRing L] [CommRing S] [CommRing S'] [IsDomain S]
    [Algebra (MvPolynomial σ R) S] (c Δ : MvPolynomial σ R) [IsLocalization.Away (c * Δ) S]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ R) S))
    (j : MvPolynomial σ L →+* S') (hj : Function.Injective j) (a : σ → R) (ha : MvPolynomial.eval a Δ = 1)
    (φ : R →+* L) (hφ : Function.Injective φ) (ψ : S →+* S')
    (hψ : ∀ B, ψ (algebraMap (MvPolynomial σ R) S B) = j (MvPolynomial.map φ B))
    (f : S) (P : MvPolynomial σ L) (hP : j P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial σ R), f * algebraMap (MvPolynomial σ R) S c ^ N = algebraMap _ S G := by
  obtain ⟨N, G₀, hf⟩ := IsLocalization.Away.surj (c * Δ) f
  have h3 := congrArg ψ hf
  rw [map_mul ψ, ← map_pow, ← hP, hψ, hψ, ← map_mul] at h3
  have h4 := hj h3
  have h5 : MvPolynomial.map φ (Δ ^ N) * (P * MvPolynomial.map φ (c ^ N)) = MvPolynomial.map φ G₀ := by
    rw [← h4, mul_pow, map_mul]; ring
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_eval φ a _ _ _ (by rw [map_pow, ha, one_pow]) h5
  rw [← hQ, ← map_mul] at h5
  have h6 := MvPolynomial.map_injective φ hφ h5
  refine ⟨N, Q, ?_⟩
  have hu : IsUnit (algebraMap _ S (c * Δ)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hu
  have hu' : IsUnit (algebraMap _ S (Δ ^ N)) := by
    rw [map_pow]
    exact (isUnit_of_mul_isUnit_right hu).pow N
  apply hu'.mul_left_cancel
  rw [← map_mul, h6, ← hf, map_mul, map_pow, mul_pow]
  ring

theorem denominators (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ)
    (ψ : ArcSR Dw V ϖ →+* ArcS Dw K)
    (hψ : ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ))
    (f : ArcSR Dw V ϖ) (P : MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (hP : algebraMap _ (ArcS Dw K) P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries V)),
      f * arcιR Dw V ϖ (PowerSeries.C (R := V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw V ϖ) G := by
  haveI := isDomain_letter Dw V hϖ
  have hinj := algebraMap_letter_injective Dw V hϖ
  have hD : arcDet Dw K ≠ 0 := by
    rw [← map_arcDetR Dw V K φ]
    exact fun h => arcDetR_ne_zero Dw V (MvPolynomial.map_injective φ hφ (h.trans (map_zero _).symm))
  have hinjL : Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
    IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hD)
  exact denominators_gen (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X)) (arcDetR Dw V) hinj _ hinjL _
    (eval_arcDetR Dw V) φ hφ ψ (fun B => RingHom.congr_fun hψ B) f P hP

theorem comp_eq_of_letters (φ : PowerSeries V →+* PowerSeries K) (ψ : ArcSR Dw V ϖ →+* ArcS Dw K) :
    ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
          (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ K).comp φ)) ↔
      ψ.comp (arcιR Dw V ϖ) = (arcι Dw K).comp φ ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw V ϖ x) = arcX Dw K x.1 x.2.1 x.2.2 := by
  constructor
  · intro hψ
    refine ⟨RingHom.ext fun p => ?_, fun x => ?_⟩
    · have := RingHom.congr_fun hψ (MvPolynomial.C p)
      simp only [RingHom.comp_apply, MvPolynomial.map_C] at this
      simp only [RingHom.comp_apply, arcιR, arcι, this]
    · have := RingHom.congr_fun hψ (MvPolynomial.X x)
      simp only [RingHom.comp_apply, MvPolynomial.map_X] at this
      simp only [arcXR, arcX, this]
  · rintro ⟨h1, h2⟩
    apply MvPolynomial.ringHom_ext
    · intro p
      have := RingHom.congr_fun h1 p
      simp only [RingHom.comp_apply, arcιR, arcι] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_C, this]
    · intro x
      have := h2 x
      simp only [arcXR, arcX] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_X, this]

theorem flat_letter [IsBezout V] (hϖ : ϖ ≠ 0) : ((arcιR Dw V ϖ).comp (PowerSeries.C (R := V))).Flat := by
  haveI := isDomain_letter Dw V hϖ
  refine flat_of_injective _ ?_
  rw [arcιR, RingHom.coe_comp, RingHom.coe_comp]
  exact ((algebraMap_letter_injective Dw V hϖ).comp (MvPolynomial.C_injective _ _)).comp PowerSeries.C_injective

omit [IsDomain V] in
theorem toLaurent_injective (i : V →+* K) (hi : Function.Injective i) :
    Function.Injective ((HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)) := by
  rw [RingHom.coe_comp]
  exact HahnSeries.ofPowerSeries_injective.comp (PowerSeries.map_injective _ hi)

end Parts

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  intro E _ _ _ H Dw Tv ϖ hϖ
  have hφ := toLaurent_injective Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) (IsFractionRing.injective Tv.V Tv.Fr)
  refine ⟨isDomain_letter Dw Tv.V hϖ, algebraMap_letter_injective Dw Tv.V hϖ, flat_letter Dw Tv.V hϖ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_lift Dw Tv.V Tv.Fr hϖ _ hφ
    exact ⟨ψ, (comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).1 hψ⟩
  · rintro ψ h1 h2 f ⟨P, hP⟩
    exact denominators Dw Tv.V Tv.Fr hϖ _ hφ ψ ((comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).2 ⟨h1, h2⟩) f P hP

end GlobalTheory.LetterDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominatorsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcLetterRingOverDVR_polynomial_denominators : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  first | exact @GlobalTheory.LetterDenom.main | exact GlobalTheory.LetterDenom.main | (intros; apply GlobalTheory.LetterDenom.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NfacParallelFlowV
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

section FlowNorm

open ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

theorem sum_step_telescope (L : ℕ → ℝ) (m : ℝ) {p r : ℕ} (hp : p ≤ r) :
    ∑ k ∈ Finset.range r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r + L 0 - 2 * L p) := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, (if p ≤ k then m else -m) * (L (k + 1) - L k) = -m * (L p - L 0) := by
    rw [← Finset.sum_range_sub L p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
  have h2 : ∑ k ∈ Finset.Ico p r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r - L p) := by
    rw [← Finset.sum_Ico_sub L hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).1]
  rw [h1, h2]; ring

theorem nfac_parallel_flowV {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) (la : Wt X.Ψ r) (m : ℝ)
    (hla : ∀ τ (j : Fin r), (la τ j : ℝ) = if X.p0 ≤ (j : ℕ) then m else -m)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) :
    X.nfac la (X.flowV e s x) * (∏ τ, (X.ttV e (X.flowV e s x) τ)⁻¹) ^ m =
      X.nfac la x * (∏ τ, (X.ttV e x τ)⁻¹) ^ m := by
  have hρ : ∀ τ, 0 < rho X e s x τ X.p0 := fun τ => rho_pos X e he hx s hT τ _ X.p0_le
  have hr : ∀ τ, rfac X la x (X.flowV e s x) τ = (rho X e s x τ X.p0)⁻¹ ^ m := by
    intro τ
    have hsg := hsg_of X hx τ
    rw [rfac_eq X e he hx s hT τ la]
    set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
    have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
    have hLr : L r = 0 := by
      simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
    have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
        ∑ k ∈ Finset.range r, (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k)) r]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hla]
      split_ifs <;> simp only [L] <;> ring
    rw [hsum, sum_step_telescope L (m / 2) X.p0_le, hL0, hLr,
      Real.rpow_def_of_pos (inv_pos.mpr (hρ τ)), Real.log_inv]
    congr 1
    simp only [L]; ring
  have hm : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (hsg_of X hx τ) (e τ) (he τ).1 (he τ).2
  have htpos : ∀ τ, 0 ≤ (X.ttV e x τ)⁻¹ := fun τ => by
    have := hm τ
    have := c_pos X τ
    rw [Data.ttV, maj_eq X hx e τ (he τ).1]
    positivity
  have ht : ∀ τ, (X.ttV e (X.flowV e s x) τ)⁻¹ = (rho X e s x τ X.p0)⁻¹ * (X.ttV e x τ)⁻¹ := by
    intro τ
    have h1 := hρ τ
    have h2 := hm τ
    have h3 := c_pos X τ
    rw [Data.ttV, Data.ttV, maj_flow X hx e τ (he τ).1 s h1.ne', maj_eq X hx e τ (he τ).1]
    simp only [rho] at h1 ⊢
    field_simp
  have hN := FlowCoefficientBounds.nfac_pos X hT la
  have hdiv := nfac_div X la x (X.flowV e s x)
  rw [div_eq_iff hN.ne', Finset.prod_congr rfl fun τ _ => hr τ,
    Real.finsetProd_rpow _ _ (fun τ _ => (inv_pos.mpr (hρ τ)).le)] at hdiv
  rw [hdiv, Finset.prod_congr rfl fun τ _ => ht τ, Finset.prod_mul_distrib,
    Real.mul_rpow (Finset.prod_nonneg fun τ _ => (inv_pos.mpr (hρ τ)).le)
      (Finset.prod_nonneg fun τ _ => htpos τ)]
  ring

end FlowNorm

theorem nfac_parallel_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (n : ℕ) (ξ' : Fin r → E), Even n → (U.X k).IsIso ξ' → ∀ x ∈ (U.X k).dom, ∀ s : (U.X k).Ψ → ℂ, (U.X k).flow ξ' s x ∈ (U.X k).dom → (U.X k).nfac (laU U 0 n k) ((U.X k).flow ξ' s x) * (∏ τ, ((U.X k).tt ξ' ((U.X k).flow ξ' s x) τ)⁻¹) ^ ((n : ℝ) / 2) = (U.X k).nfac (laU U 0 n k) x * (∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U k n ξ' hn hξ x hx s hT
  have hiso : (U.X k).IsIsoV ((U.X k).embV ξ') := fun τ =>
    ⟨by rw [show (U.X k).embV ξ' τ = Data.emb τ.1 ξ' from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  refine nfac_parallel_flowV (U.X k) ((U.X k).embV ξ') hiso (laU U 0 n k) ((n : ℝ) / 2) ?_ hx s hT
  intro τ j
  obtain ⟨m, rfl⟩ := hn
  have h2 : (m + m) / 2 = m := by omega
  simp only [laU, h2]
  split_ifs <;> simp

end GlobalTheory.ArcQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibre
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.GenDvr

open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1

theorem generates_of_generic_line {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X X' : Scheme.{0}}
    (p : X ⟶ Sp V) [Flat p] {p' : X' ⟶ Sp (FractionRing V)} {φ : X' ⟶ X}
    (hφ : IsPullback φ p' p (spMap (algebraMap V (FractionRing V)))) {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (b : L'.Sec)
    (hb : ∀ s : L'.Sec, ∃ a : FractionRing V, ∀ i, s.f i = constFn p' _ a * b.f i)
    (θ : L.Sec) {g : X} (hg : p g = closedPoint V) (hθ : g ∈ Out.nonzeroLocus θ) (σ : L.Sec) :
    ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i := by
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  have hk₀ : g ∈ L.U k₀ := X.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w, gw'⟩ := hw
  have down := sec_pull_down ((isGen_iff w).1 gw') hL hL'
  obtain ⟨θ', hθ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hφ.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hφ.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f σ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f τ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn p' _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn p _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_pull (𝟙 _) φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk,
      (sec_eq_iff _ _ _ _).1 h₃ k y hk, Category.id_comp, hφ.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : L'.Sec} {a a' : FractionRing V}, (∀ k, s.f k = constFn p' _ a * t.f k) →
      (∀ k, t.f k = constFn p' _ a' * u.f k) → ∀ k, s.f k = constFn p' _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : L'.Sec} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn p' _ a * t.f k) →
      ∀ k, t.f k = constFn p' _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : L.Sec) (r : V), (∀ j, θ.f j = constFn p _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit p g hg hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀⟩ := hb θ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ θ' θ' 0 hθ' hθ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  obtain ⟨σK, hσK⟩ := down σ
  obtain ⟨a, ha⟩ : ∃ a : FractionRing V, ∀ i, σK.f i = constFn p' _ a * θ'.f i := by
    obtain ⟨a, ha⟩ := hb σK
    exact ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀)⟩
  obtain ⟨r, hr⟩ : ∃ r : V, ∀ i, σ.f i = constFn p _ r * θ.f i := by
    by_cases h : IsLocalization.IsInteger V a
    · obtain ⟨r, rfl⟩ := h
      exact ⟨r, inj σ θ σK θ' r hσK hθ' ha⟩
    · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
      obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
      obtain ⟨u, rfl⟩ := unit σ r (inj θ σ θ' σK r hθ' hσK (hr ▸ invc hne ha))
      exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
  refine ⟨r, hr, fun r' hr' => ?_⟩
  by_contra hne
  have e : cst p g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst p g (r' - r) * 0 := by
    rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
  exact un.ne_zero (cst_regular p g (sub_ne_zero.2 hne) e)

theorem generates_of_nonzero_on_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  intro _ h₂ E _ _ _ H Dw l Xo _ T G t' x m₁ m₂ θ ⟨g, hg, hθ⟩ σ
  have := G.semi.smooth
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre h₂.secTwist amplePt Xo.univ m₁
  obtain ⟨w, hw, -⟩ := m₂.lin
  exact generates_of_generic_line G.G.hom m₂.cart.1 G.PP.isLB t'.PP.isLB ⟨w, hw⟩ b (fun s => (hb s).exists) θ hg hθ σ

end GlobalTheory.GenDvr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibreStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_section_generates_of_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  first | exact @GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | exact GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre | (intros; apply GlobalTheory.GenDvr.generates_of_nonzero_on_special_fibre <;> assumption)
end
end
