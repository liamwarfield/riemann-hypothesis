module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreadsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquiv
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem adjKlt_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  intro k K K' _ _ _ _ c c' e hce n x T φ S S' hx hS h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FieldPair.placeEquiv_ringEquiv c c' e hce
  have hmem : ∀ (P : Place c) (b : K'), b ∈ (Φ P).ring ↔ e.symm b ∈ P.ring := fun P b => by
    simpa using (hΦ P).1 (e.symm b)
  have hord : ∀ (P : Place c) (b : K'), (Φ P).ord b = P.ord (e.symm b) := fun P b => by
    simpa using (hΦ P).2.1 (e.symm b)
  have hdisc : ∀ P : Place c, (Φ P).disc (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) =
      P.disc (dForm c x) φ := fun P => by
    simp only [Place.disc]
    rw [(hΦ P).2.2.1 φ, (hΦ P).2.2.2 n x hx]
    rfl
  have hΦS : Φ S = S' := Place.ext (ValuationSubring.ext _ _ fun b => by
    rw [hmem, ← hS (e.symm b), e.apply_symm_apply])
  have hk : Klt c n ⊤ (dForm c x) φ := ⟨h.1, h.2.1, fun P hP =>
    (P.ring_ne_top (eq_top_iff.2 fun f _ => hP f trivial)).elim⟩
  have hk' := ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x ⊤ φ hx).2.2.1).1 hk
  refine ⟨hk'.1, hk'.2.1, ?_⟩
  intro Q' hQ' t' u' E' hTQ hmax hdim hSQ hEQ ht hu hoth
  set Q : Subring K := Q'.map e.symm.toRingHom with hQdef
  have hQmem : ∀ a : K, a ∈ Q ↔ e a ∈ Q' := fun a => by
    exact Subring.mem_map_equiv (f := e.symm) (K := Q')
  have hQQ : Q.map e.toRingHom = Q' := by
    ext b
    exact (Subring.mem_map_equiv (f := e) (K := Q)).trans ((hQmem _).trans (by rw [e.apply_symm_apply]))
  have hQ : IsLocModel c Q :=
    ((GlobalTheory.FieldPair.transport_ringEquiv c c' e hce n x Q φ hx).2.1).2 (hQQ ▸ hQ')
  let ψ : Q' ≃+* Q := e.symm.subringMap
  have hψ : ∀ y, ((ψ y : Q) : K) = e.symm y := fun y => rfl
  have hprime : ∀ P : Place c, (Φ P).IsPrimeOf Q' ↔ P.IsPrimeOf Q := by
    intro P
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · have := h1 (e f) ((hQmem f).1 hf)
        rwa [hmem, e.symm_apply_apply] at this
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ :=
          h2 (e f) (by rw [hmem, e.symm_apply_apply]; exact hf)
        refine ⟨e.symm a, by rw [hQmem, e.apply_symm_apply]; exact ha,
          e.symm b, by rw [hQmem, e.apply_symm_apply]; exact hb,
          by simpa using hb0, by rw [← hord]; exact hbo, ?_⟩
        apply e.injective
        rw [map_mul, e.apply_symm_apply, e.apply_symm_apply, hfab]
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · rw [hmem]
        exact h1 _ (by rw [hQmem, e.apply_symm_apply]; exact hf)
      · obtain ⟨a, ha, b, hb, hb0, hbo, hfab⟩ := h2 (e.symm f) ((hmem P f).1 hf)
        refine ⟨e a, (hQmem a).1 ha, e b, (hQmem b).1 hb, by simpa using hb0,
          by rw [hord, e.symm_apply_apply]; exact hbo, ?_⟩
        rw [← hfab, map_mul, e.apply_symm_apply]
  set E := Φ.symm E' with hEdef
  have hE : Φ E = E' := Φ.apply_symm_apply E'
  haveI := hQ'.isLocalRing
  haveI := hQ.isLocalRing
  have hTQ' : T ≤ Q := fun f hf => (hQmem f).2 (hTQ (Subring.mem_map.2 ⟨f, hf, rfl⟩))
  have hmax' : Ideal.span {ψ t', ψ u'} = IsLocalRing.maximalIdeal Q := by
    have h1 := congrArg (Ideal.map ψ) hmax
    rw [Ideal.map_span, Set.image_pair] at h1
    rw [h1]
    ext z
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      rwa [isUnit_map_iff]
    · intro hz
      refine ⟨ψ.symm z, ?_, ψ.apply_symm_apply z⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
      rwa [isUnit_map_iff ψ.symm]
  have hdim' : ringKrullDim Q = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ψ]
    exact hdim
  have hSQ' : S.IsPrimeOf Q := (hprime S).1 (hΦS ▸ hSQ)
  have hEQ' : E.IsPrimeOf Q := (hprime E).1 (hE ▸ hEQ)
  have ht' : S.ord ((ψ t' : Q) : K) = 1 := by
    rw [hψ, ← hord, hΦS]
    exact ht
  have hu' : E.ord ((ψ u' : Q) : K) = 1 := by
    rw [hψ, ← hord, hE]
    exact hu
  have hoth' : ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.disc (dForm c x) φ = 0 := by
    intro P hP hPS hPE
    rw [← hdisc]
    refine hoth (Φ P) ((hprime P).2 hP) (fun hr => hPS ?_) (fun hr => hPE ?_)
    · have h3 : Φ P = Φ S := Place.ext (hr.trans (congrArg Place.ring hΦS).symm)
      rw [Φ.injective h3]
    · have h3 : Φ P = Φ E := Place.ext (hr.trans (congrArg Place.ring hE).symm)
      rw [Φ.injective h3]
  have key := h.2.2 Q hQ (ψ t') (ψ u') E hTQ' hmax' hdim' hSQ' hEQ' ht' hu' hoth'
  rw [← hE, hdisc]
  exact key

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAlongPlaceNeighboursRingEquivStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kltAlongPlaceNeighbours_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (T : Subring K) (φ : K →₀ ℚ) (S : Place c) (S' : Place c'), TrBasis c x → (∀ a, e a ∈ S'.ring ↔ a ∈ S.ring) → AdjKlt c n T S (dForm c x) φ → AdjKlt c' n (T.map e.toRingHom) S' (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ) := by
  first | exact @GlobalTheory.FieldPair.adjKlt_ringEquiv | exact GlobalTheory.FieldPair.adjKlt_ringEquiv | (intros; apply GlobalTheory.FieldPair.adjKlt_ringEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGenerated
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

theorem formallyEtale_eval₂Hom_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {r : ℕ}
    {τ : Fin r → F} (hτ : TrBasis c τ) : (MvPolynomial.eval₂Hom c τ).FormallyEtale := by
  letI := c.toAlgebra
  have hτ' : IsTranscendenceBasis ℂ τ := hτ
  have hv := hτ'.1
  let P := MvPolynomial (Fin r) ℂ
  let A := Algebra.adjoin ℂ (Set.range τ)
  let Lf := IntermediateField.adjoin ℂ (Set.range τ)
  haveI := hτ'.isAlgebraic_field
  haveI : Algebra.IsSeparable Lf F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let f1 : P →+* A := hv.aevalEquiv.toAlgHom.toRingHom
  have h1 : f1.FormallyEtale := by
    letI : Algebra P A := f1.toAlgebra
    show Algebra.FormallyEtale P A
    exact .of_equiv (AlgEquiv.ofBijective (Algebra.ofId P A) hv.aevalEquiv.bijective)
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have h2 : (algebraMap A Lf).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (.of_isLocalization (nonZeroDivisors A))
  have h3 : (algebraMap Lf F).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isSeparable Lf F)
  have hc := RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp h1 h2) h3
  convert hc using 1
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change c a = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.C a)))
    have hAF : ∀ y : A, algebraMap Lf F (algebraMap A Lf y) = algebraMap A F y := fun y => rfl
    rw [hAF, hv.algebraMap_aevalEquiv, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply]
    change τ i = algebraMap Lf F (algebraMap A Lf (hv.aevalEquiv (MvPolynomial.X i)))
    have := hv.algebraMap_aevalEquiv (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X] at this
    rw [← this]
    rfl

theorem exists_basis_omega_of_trBasis {F : Type} [Field F] (c : ℂ →+* F) {n : ℕ}
    {x : Fin n → F} (hx : TrBasis c x) :
    ∃ b : Module.Basis (Fin n) F (Omega c), ∀ i, b i = dFun c (x i) := by
  letI := c.toAlgebra
  have hx' : IsTranscendenceBasis ℂ x := hx
  haveI := hx'.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℂ (Set.range x)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact exists_basis_kaehler_of_algebraicIndependent hx'.1

end GlobalTheory.DiagLoc

namespace GlobalTheory.DiagLoc

theorem isFreeGen_dForm_graph : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n k' x τ' hc _ _ hx hτ
  let β := (algebraMap ℂ L).codRestrict (loc L σ) hc
  let ρ : K →+* loc L σ := (toLoc L σ).comp Algebra.TensorProduct.includeLeftRingHom
  have hρ : ρ.comp (algebraMap ℂ K) = β := by
    ext a
    change algebraMap (K ⊗[ℂ] κ') L (algebraMap ℂ K a ⊗ₜ[ℂ] (1 : κ')) = algebraMap ℂ L a
    rw [← Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  obtain ⟨b, hb⟩ := exists_basis_omega_of_trBasis (algebraMap ℂ K) hx
  have hg := formallyEtale_mvPolynomial_eval₂_tensor (R := K) τ'
    (formallyEtale_eval₂Hom_of_trBasis (algebraMap ℂ κ') hτ)
  have hl : (toLoc L σ).FormallyEtale :=
    RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization (ker σ).primeCompl)
  have hφ : (MvPolynomial.eval₂Hom ρ (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i))).FormallyEtale := by
    convert RingHom.FormallyEtale.comp hg hl using 1
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ]
    · intro i
      simp
  exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial (algebraMap ℂ K) β ρ hρ x b hb
    (fun i => toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) hφ

end GlobalTheory.DiagLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormsGraphLocalRingFreelyGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topForms_graphLocalRing_freelyGenerated : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ')
  (hc : ∀ a, algebraMap ℂ L a ∈ GlobalTheory.DiagLoc.loc L σ),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' →
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' →
  IsFreeGen (GlobalTheory.DiagLoc.loc L σ) (dForm ((algebraMap ℂ L).codRestrict (GlobalTheory.DiagLoc.loc L σ) hc)
    (Fin.append (fun i => GlobalTheory.DiagLoc.toLoc L σ (1 ⊗ₜ[ℂ] τ' i)) (fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1)))) := by
  first | exact @GlobalTheory.DiagLoc.isFreeGen_dForm_graph | exact GlobalTheory.DiagLoc.isFreeGen_dForm_graph | (intros; apply GlobalTheory.DiagLoc.isFreeGen_dForm_graph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotient
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRigid

open GlobalTheory.CechPic

theorem cls_lam_pull {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : LB B.left} (hL : L.IsLB)
    (x y : B ⟶ B) (h : ((abelian₂ B L).pull (lift x y).left).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have h₁ : cls _ hlam = lam (cls L hL) (fst B B) (snd B B) := cls_cube_two hL _ _ hlam
  rw [cls_pull hlam, h₁, pull_lam, lift_fst, lift_snd]

theorem lbIso_lam_of_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  intro R R₀ _ _ _ _ π hπ B _ _ B₀ _ _ i i₂ hA hpb hsq P hP hP₁ hP₂ L L₀ hL hL₀ e₀ e
  haveI : IsLocalRing R₀ := IsLocalRing.of_surjective' π hπ
  have hlam : (abelian₂ B L).IsLB := LB.isLB_linComb hL _ _
  have hlam₀ : (abelian₂ B₀ L₀).IsLB := LB.isLB_linComb hL₀ _ _
  have hD : (LB.div (abelian₂ B L) P).IsLB := LB.isLB_div hlam hP
  have hcD : cls _ hD = cls _ hlam - cls P hP := cls_div hlam hP hD

  have triv_of : ∀ {Y : Scheme.{0}} (f : Y ⟶ (G2 B).left), pull f (cls _ hlam) = pull f (cls P hP) →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull f) := fun f hf =>
    (cls_eq_zero_iff (pull_isLB hD f)).1 (by rw [cls_pull hD, hcD, map_sub, hf, sub_self])

  have ax : ∀ (x y : B ⟶ B), (∃ t : (P.pull (lift x y).left).Gen, t.IsGen) → lam (cls L hL) x y = 0 →
      GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift x y).left) := fun x y hPxy hl => by
    refine triv_of _ ?_
    rw [← cls_pull hlam _ (pull_isLB hlam _), cls_lam_pull hL x y, hl, ← cls_pull hP _ (pull_isLB hP _)]
    exact ((cls_eq_zero_iff (pull_isLB hP _)).2 hPxy).symm
  have h₁ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift (𝟙 B) 1).left) := ax _ _ hP₂ (lam_one_right _ _)
  have h₂ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (lift 1 (𝟙 B)).left) := ax _ _ hP₁ (lam_one_left _ _)

  have hsq₀ : pull i₂ (cls _ hlam) = pull i₂ (cls P hP) := by
    have a : LBIso (abelian₂ B₀ L₀) ((abelian₂ B L).pull i₂) := GlobalTheory.ZM.SiegPull.lbIso_lam_pull hpb e₀.symm hsq
    rw [← cls_pull hlam _ (pull_isLB hlam _), ← cls_pull hP _ (pull_isLB hP _),
      ← (cls_eq_iff hlam₀ (pull_isLB hlam _)).2 a, (cls_eq_iff hlam₀ (pull_isLB hP _)).2 e]

  let k := ResidueField R₀
  let g₀ : R →+* k := (residue R₀).comp π
  have hpb₂ : IsPullback i₂ (G2 B₀).hom (G2 B).hom (spMap π) :=
    GlobalTheory.SiegelDescent.isPullback_square hpb.1 i₂ hsq
  have h₀ := (IsPullback.of_hasPullback (G2 B₀).hom (spMap (residue R₀))).paste_horiz hpb₂
  have e₁ : spMap (residue R₀) ≫ spMap π = Spec.map (CommRingCat.ofHom g₀) := by
    simp only [spMap, g₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [e₁] at h₀
  have ht₀ : GlobalTheory.AbLaw.Triv ((LB.div (abelian₂ B L) P).pull (pullback.fst (G2 B₀).hom (spMap (residue R₀)) ≫ i₂)) :=
    triv_of _ (by rw [pull_comp, pull_comp, hsq₀])
  have hPf : GlobalTheory.SpreadingModels.PerfAll :=
    GlobalTheory.T.perfect_of_models (GlobalTheory.T.has_model_of_spreading GlobalTheory.T.scheme_models_spread GlobalTheory.T.smooth_spreads_out GlobalTheory.T.isProper_spreads_out GlobalTheory.T.line_bundle_spreads_out')
  haveI := hA.smooth
  haveI := hA.proper
  have sm : Smooth (B ⊗ B).hom := by
    change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have pr : IsProper (B ⊗ B).hom := by
    change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  obtain ⟨r, hr, hU⟩ := GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.globalFns_holds GlobalTheory.AbLaw.Seesaw.seesaw
    (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.globalFns_holds GlobalTheory.KuennethOne.kuenneth_injective)
    R B hA _ hD (hPf R _ (B ⊗ B).hom sm pr _ hD) h₁ h₂ k g₀ _ _ _ h₀ ht₀

  have hru : IsUnit r := by
    by_contra hnu
    refine hr ?_
    show residue R₀ (π r) = 0
    rw [residue_eq_zero_iff]
    intro hu
    obtain ⟨s, hs⟩ := hu.exists_right_inv
    obtain ⟨t, rfl⟩ := hπ s
    have hk : r * t - 1 ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hs, map_one, sub_self]
    have hm : RingHom.ker π ≤ maximalIdeal R := le_maximalIdeal (RingHom.ker_ne_top π)
    have hunit : IsUnit (r * t) := by
      by_contra h'
      have h1 : r * t ∈ maximalIdeal R := (mem_maximalIdeal _).2 h'
      have h2 : (1 : R) ∈ maximalIdeal R := by
        have := (maximalIdeal R).sub_mem h1 (hm hk)
        simpa using this
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
    exact hnu (isUnit_of_mul_isUnit_left hunit)
  let U := (B ⊗ B).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)
  have hsub : Set.range (𝟙 (B ⊗ B).left) ⊆ Set.range U.ι := by
    rintro x -
    rw [Scheme.Opens.range_ι]
    change r ∉ ((B ⊗ B).hom x).asIdeal
    exact fun hx => ((B ⊗ B).hom x).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hru)
  have hT := GlobalTheory.AbLaw.CubeOpen.triv_comp (IsOpenImmersion.lift U.ι (𝟙 _) hsub) (IsOpenImmersion.lift_fac _ _ _) hU
  have hz : cls _ hD = 0 := by
    rw [← pull_id (cls _ hD), ← cls_pull hD _ (pull_isLB hD _)]
    exact (cls_eq_zero_iff _).2 hT
  exact (cls_eq_iff hlam hP).1 (sub_eq_zero.1 (hcD ▸ hz))

end GlobalTheory.PolRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [CommRing R₀] [Nontrivial R₀] (π : R →+* R₀), Function.Surjective π → ∀ (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (B₀ : Over (Sp R₀)) [GrpObj B₀] [IsCommMonObj B₀] (i : B₀.left ⟶ B.left) (i₂ : (G2 B₀).left ⟶ (G2 B).left), IsAbelianScheme B → IsGrpPullback B₀ B (spMap π) i → IsSquare i i₂ → ∀ (P : LB (G2 B).left), P.IsLB → (∃ t : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, t.IsGen) → ∀ (L : LB B.left) (L₀ : LB B₀.left), L.IsLB → L₀.IsLB → LBIso (L.pull i) L₀ → LBIso (abelian₂ B₀ L₀) (P.pull i₂) → LBIso (abelian₂ B L) P := by
  first | exact @GlobalTheory.PolRigid.lbIso_lam_of_quotient | exact GlobalTheory.PolRigid.lbIso_lam_of_quotient | (intros; apply GlobalTheory.PolRigid.lbIso_lam_of_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisRestrictFinerOpens
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisRestrictFinerOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem res_res_frameRestrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(X, U)ˣ) :
    res h' (res h x) = res (h'.trans h) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isFrame_restrict : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  intro X C _ V hV L u C' _ V' hV' H hH ⟨τ, hgen, hcomp⟩
  refine ⟨fun T m ↦ res (inf_le_inf_right (L.U m) (hH T)) (τ (H.obj T) m), fun T m m' ↦ ?_, fun T T' a m ↦ ?_⟩
  · have key := congrArg (res (inf_le_inf_right (L.U m') (inf_le_inf_right (L.U m) (hH T)))) (hgen (H.obj T) m m')
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key
  · have key := congrArg (res (inf_le_inf_right (L.U m) (hH T'))) (hcomp (H.obj T) (H.obj T') (H.map a) m)
    simp only [map_mul, res_res_frameRestrict] at key
    simpa only [map_mul, res_res_frameRestrict] using key

end GlobalTheory.LBObs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundleFrameOnBasisRestrictFinerOpensStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLineBundleFrameOnBasis_restrict_finer_opens : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens) (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L : LB X) (u : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ) (C' : Type) [Category.{0} C'] (V' : C' → X.Opens) (hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T) (H : C' ⥤ C) (hH : ∀ T, V' T ≤ V (H.obj T)), IsFrame L V hV u → IsFrame L V' hV' fun T T' a ↦ res (hH T') (u _ _ (H.map a)) := by
  first | exact @GlobalTheory.LBObs.isFrame_restrict | exact GlobalTheory.LBObs.isFrame_restrict | (intros; apply GlobalTheory.LBObs.isFrame_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasis
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

variable {R₀ : Type} [CommRing R₀] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀}
  {C D : Type} [Category.{0} C] [Category.{0} D]

theorem opOf_le_of_natTrans (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) (T : D) :
    opOf K T ≤ opOf G (H.obj T) := leOfHom (θ.app T).unop

def natCoef (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (θ : H ⋙ G ⟶ K) :
    CoefMap (RingHom.id R₀) (G ⋙ OAff s₀) (K ⋙ OAff s₀) where
  G := H
  α T := (mp (OAff s₀) (θ.app T)).toRingHom
  naturality {T T'} φ b := by
    change mp (OAff s₀) (θ.app T') (mp (OAff s₀) ((H ⋙ G).map φ) b) = mp (OAff s₀) (K.map φ) (mp (OAff s₀) (θ.app T) b)
    rw [← mp_comp, ← mp_comp, θ.naturality φ]
  smul T r b := by
    change mp (OAff s₀) (θ.app T) (r • b) = r • mp (OAff s₀) (θ.app T) b
    exact map_smul _ r b

theorem obAt_refine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)
    (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀)))
    (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C)
    (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) →
      ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L c C D _ _ G K H θ h
  obtain ⟨u, hf, ho⟩ := h
  refine ⟨fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)), ?_, ?_⟩
  · exact GlobalTheory.T.isLineBundleFrameOnBasis_restrict_finer_opens X₀ C (opOf G) (opOf_le G) L u D (opOf K) (opOf_le K) H (opOf_le_of_natTrans G K H θ) hf
  · have key := GlobalTheory.T.unitCocycleLiftObstruction_pullback_naturality R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) D (K ⋙ OAff s₀)
      ((ofSys S).restrict K) (natCoef (s₀ := s₀) G K H θ) (fun T ↦ mp S.F (θ.app T)) u
      (fun T T' a ↦ res (opOf_le_of_natTrans G K H θ T') (u _ _ (H.map a)))
      ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c)
      (fun T b ↦ S.nat (θ.app T) b)
      (fun T T' a b ↦ by
        change mp S.F (K.map a) (mp S.F (θ.app T) b) = mp S.F (θ.app T') (mp S.F ((H ⋙ G).map a) b)
        exact (mp_comp S.F _ _ b).symm.trans
          ((congrArg (fun f ↦ mp S.F f b) (θ.naturality a).symm).trans (mp_comp S.F _ _ b)))
      (fun T T' a ↦ rfl) ho
    have hc : (extMap R₁ (natCoef (s₀ := s₀) G K H θ)).pull2 ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) =
        (extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c := by
      rw [← CoefMap.pullCohomologyTwo_comp]
      refine CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ θ (fun T b ↦ ?_) c
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [← hc]
    exact key

end GlobalTheory.LBObs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) → ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  first | exact @GlobalTheory.LBObs.obAt_refine | exact GlobalTheory.LBObs.obAt_refine | (intros; apply GlobalTheory.LBObs.obAt_refine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.VExist

theorem cube_corr {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) (a a' b b' p q : G) :
    θ b q a * θ b q p * θ a p (b * q) * (θ b' q a' * θ b' q p * θ a' p (b' * q)) * θ (a * b) (a' * b') (p * q) =
      θ a a' p * θ b b' q * θ a a' q * θ b b' p *
        (θ (b * b') q (a * a') * θ (b * b') q p * θ (a * a') p (b * b' * q)) := by
  have E := fun {x y : U} (e : x = y) => congrArg Additive.ofMul e
  have k0 := E (h.compat a b (a' * b') (p * q))
  have k1 := E (h.compat b b' q (a * a'))
  have k2 := E (h.compat a a' p (b * b' * q))
  have k3 := E (h.compat a' b' a (p * q))
  have k4 := E (h.compat a' b' b (p * q))
  have k5 := E (h.coc b b' q p)
  have k6 := E (h.coc b' q p b)
  have k7 := E (h.coc a' (b' * p * q) b a)
  have k8 := E (h.coc a a' q b)
  have k9 := E (h.coc a a' q b')
  have k10 := E (h.coc a' q b' a)
  have k11 := E (h.coc a (a' * q) b' b)
  have k12 := E (h.coc a a' b' b)
  have k13 := E (h.coc a' (b' * q) b a)
  have k14 := E (h.coc a' q b' b)
  have k15 := E (h.coc b (b' * q) p a)
  have k16 := E (h.coc b q p a)
  have k17 := E (h.coc b' q p a)
  have k18 := E (h.coc b (b' * q) p a')
  have k19 := E (h.coc a (p * q) b' a')
  have k20 := E (h.coc b (p * q) b' a')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  simp only [mul_comm, mul_assoc, mul_left_comm, h.s01, h.s12] at *
  linear_combination (norm := abel) k0 - k1 - k2 + k3 + k4 - k5 - k6 + k7 - k8 - k9 - k10 - k11 + k12 - k13 - k14 - k15 + k16 - k17 - k18 + k19 + k20

end GlobalTheory.Mum.TensTor.VExist

namespace GlobalTheory.Mum.TensTor.VExist

theorem pair_mult {F : Type} [Field F] (N : NumD F) (gi gj : N.Gt) (ai aj ai' aj' : N.X) :
    gj.s (ai + ai') * gi.s (aj + aj') /
        (N.θ (N.c (aj + aj')) gj.b (N.c (ai + ai')) * N.θ (N.c (aj + aj')) gj.b gi.b *
          N.θ (N.c (ai + ai')) gi.b (N.c (aj + aj') * gj.b)) *
      (N.θ (N.c ai * N.c aj) (N.c ai' * N.c aj') (gi.b * gj.b) /
        (N.θ (N.c ai) (N.c ai') gi.b * N.θ (N.c aj) (N.c aj') gj.b)) =
    gj.s ai * gi.s aj / (N.θ (N.c aj) gj.b (N.c ai) * N.θ (N.c aj) gj.b gi.b * N.θ (N.c ai) gi.b (N.c aj * gj.b)) *
      (gj.s ai' * gi.s aj' /
        (N.θ (N.c aj') gj.b (N.c ai') * N.θ (N.c aj') gj.b gi.b * N.θ (N.c ai') gi.b (N.c aj' * gj.b))) := by
  have m₁ := congrArg Additive.ofMul (gj.mult ai ai')
  have m₂ := congrArg Additive.ofMul (gi.mult aj aj')
  have k := congrArg Additive.ofMul (cube_corr N.cub (N.c ai) (N.c ai') (N.c aj) (N.c aj') gi.b gj.b)
  rw [N.c_add, N.c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m₁ m₂ k ⊢
  linear_combination (norm := abel) m₁ + m₂ + k

theorem gtRelV_exists : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  intro F _ N N' r W φ e wv hT vs
  obtain ⟨-, hφb, he_add, -, hc, hw0, hθ, -⟩ := hT
  set b' := Function.surjInv hφb.2 (fun j => (vs j).b) with hb'def
  have hb' : ∀ j, φ b' j = (vs j).b := fun j => congrFun (Function.surjInv_eq hφb.2 _) j
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  let R : N'.X → Fˣ := fun χ' => ∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j
  let s' : N'.X → Fˣ := fun χ' => R χ' * U (N'.c χ' * b') * U 1 / (U (N'.c χ') * U b')
  have hmult : ∀ χ χ' : N'.X, s' (χ + χ') * N'.θ (N'.c χ) (N'.c χ') b' = s' χ * s' χ' := by
    intro χ χ'
    let P : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ i) * N.c (e χ j)) (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) /
        (N.θ (N.c (e χ i)) (N.c (e χ' i)) (vs i).b * N.θ (N.c (e χ j)) (N.c (e χ' j)) (vs j).b)) ^ W i j
    have hθu : N'.θ (N'.c χ) (N'.c χ') b' * U (N'.c χ * N'.c χ' * b') * U (N'.c χ) * U (N'.c χ') * U b' =
        P * U (N'.c χ * N'.c χ') * U (N'.c χ * b') * U (N'.c χ' * b') * U 1 := by
      have h := hθ (N'.c χ) (N'.c χ') b'
      simp only [hc, hb'] at h
      exact Units.ext (by simpa [U, P] using h)
    have hR : R (χ + χ') * P = R χ * R χ' := by
      simp only [R, P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow, he_add, he_add, pair_mult]
    have a := congrArg Additive.ofMul hθu
    have b := congrArg Additive.ofMul hR
    simp only [s', N'.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a + b
  refine ⟨⟨b', s', hmult⟩, hb', fun χ' => ?_⟩
  have h1 := hw0 (N'.c χ')
  have h2 := hw0 b'
  simp only [s', U, Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
  field_simp
  simp only [R]
  ring

end GlobalTheory.Mum.TensTor.VExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTupleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  first | exact @GlobalTheory.Mum.TensTor.VExist.gtRelV_exists | exact GlobalTheory.Mum.TensTor.VExist.gtRelV_exists | (intros; apply GlobalTheory.Mum.TensTor.VExist.gtRelV_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibreVal

variable {X Y Z : Scheme.{0}}

theorem gs_pow (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by simp only [gs_eq f y U h, map_pow]

theorem gs_sum (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ) (a : κ → Γ(X, U)) :
    gs f y U (S.sum a) = S.sum (fun i => gs f y U (a i)) := by simp only [gs_eq f y U h, map_sum]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem mem_finset_inf {κ : Type} (S : Finset κ) (V : κ → X.Opens) (x : X) (h : ∀ i ∈ S, x ∈ V i) : x ∈ S.inf V :=
  Finset.inf_induction (p := fun W : X.Opens => x ∈ W) trivial (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) h

end GlobalTheory.Mum.FibreVal

theorem GlobalTheory.Mum.FibreVal.pG_app_eq_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {V : D.P.A.left.Opens} (x : Γ(D.P.A.left, V))
    (h : ((pullback.fst D.P.A.hom (thick R I e)).app V).hom x = 0) : (g.pG.left.app V).hom x = 0 := by
  have h' := congrArg (g.q.left.app (pullback.fst D.P.A.hom (thick R I e) ⁻¹ᵁ V)).hom h
  rw [map_zero] at h'
  exact h'

theorem GlobalTheory.Mum.FibreVal.sval_comp_eq_zero {X W Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (g : Z ⟶ W) (p : W ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J)
    (h : (p.app (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k)))).hom (s.f (fun k => J ((g ≫ p) ≫ φ k))) = 0) :
    sval s (g ≫ p) z J = 0 := by
  have e1 := gs_pull g p z (LB.wchart L φ (fun k => J ((g ≫ p) ≫ φ k))) (hJ.mem φ (g ≫ p)) (s.f (fun k => J ((g ≫ p) ≫ φ k)))
  rw [h, gs_zero] at e1
  exact e1.symm


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.FibreVal in
theorem GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  intro R _ _ _ D A G _ _ U Y T g y hP k z J J' hJ hJ'
  let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) := (fun _ => J' (g ≫ (U.gt 0).pG.left), fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left))
  have hpp : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG (maximalIdeal R) 0 G).left)).U pp :=
    ⟨Set.mem_iInter.2 fun _ => hJ' (g ≫ (U.gt 0).pG.left), Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩
  refine ⟨(gm g z _ ((U.w 0).s pp) ^ k)⁻¹, ?_⟩
  intro α b τ F s hT hL hE
  obtain ⟨S, h0, hS⟩ := hE
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J (g ≫ (fstG (maximalIdeal R) 0 G).left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB β i)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β i => J' (g ≫ D.toPre.Oφ (U.gt 0).pG β i)
  have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ c, (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) c =
        J' (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) c) := by
      rintro (a | a | a) <;> simp [jf, jt, pp]
    intro a c e
    rw [key, key, e]
  have e := hS pp j₁ jf jt rfl hcoh
  have hz : g z ∈ U.expW 0 pp j₁ S jf jt :=
    ⟨⟨hpp, hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG (maximalIdeal R) 0 G).left)⟩, mem_finset_inf _ _ _ fun β _ =>
      ⟨hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left), hJ'.mem (D.toPre.Oφ (U.gt 0).pG β) g⟩⟩
  have e' := congrArg (gs g z (U.expW 0 pp j₁ S jf jt)) e
  rw [gs_mul g z _ hz, gs_pow g z _ hz, gs_unit g z _ hz, gm_res g z _ hz, gs_res g z _ hz] at e'
  erw [gs_pull g (fstG (maximalIdeal R) 0 G).left z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁) (Set.mem_iInter.2 fun _ => hJ (g ≫ (fstG (maximalIdeal R) 0 G).left))] at e'
  rw [gs_sum g z _ hz] at e'
  have hterm : ∀ (β : D.toPre.X) (hβ : β ∈ S),
      gs g z (U.expW 0 pp j₁ S jf jt)
        (((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 pp j₁ jf jt hβ)).op).hom
            (((U.gt 0).pG.left.app _).hom ((F.f β).f (jf β))) *
          (Semi.res (U.expWeight_le_chart_weight 0 pp j₁ jf jt hβ) (((U.gt 0).t β).s (jt β))).val) =
      sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val := by
    intro β hβ
    rw [gs_mul g z _ hz, gs_res g z _ hz, gs_unit g z _ hz]
    erw [gm_res g z _ hz]
    erw [gs_pull g (U.gt 0).pG.left z _ (hJ'.mem (D.toPre.famφB β) (g ≫ (U.gt 0).pG.left))]
    rfl
  replace e' := (e'.trans (Finset.sum_congr rfl fun (β : S) _ => hterm β.1 β.2)).trans
    (Finset.sum_attach S (fun β => sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val))
  have hsum : ∑ β ∈ S, sval (F.f β) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t β) g z J').val =
      sval (F.f α) (g ≫ (U.gt 0).pG.left) z J' * (val ((U.gt 0).t α) g z J').val := by
    apply Finset.sum_eq_single α
    · intro β _ hne
      rw [sval_comp_eq_zero (F.f β) g (U.gt 0).pG.left z hJ' (pG_app_eq_zero (U.gt 0) _ (hL.2 β hne _)), zero_mul]
    · intro hα
      rw [sval_comp_eq_zero (F.f α) g (U.gt 0).pG.left z hJ' (h0 α hα _), zero_mul]
  rw [hsum] at e'
  have hq : (y ≫ Y.q).left = g ≫ (U.gt 0).pG.left := by
    have h1 := (Y.rep.1 T Y.H y (𝟙 Y.H)).1
    rw [Category.comp_id] at h1
    rw [Over.comp_left]
    exact h1.symm.trans hP.1
  have ht : val ((Y.Φ T y).s α) (𝟙 _) z J' = val ((U.gt 0).t α) g z J' :=
    (val_corr hJ' (hP.2 α) (𝟙 _)).trans ((val_pull hJ' _ g (𝟙 _)).trans (by rw [Category.id_comp]))
  rw [hT T y z J' hJ', hq, ht, ← hL.1, ← e',
    sval_of s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J j₁ (fun _ => by rw [Category.comp_id]),
    ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (Y : Ext D.toPre) (T : Over (Sp R)) (g : T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) (y : T ⟶ Y.H), GlobalTheory.TorusCoord.IsPointOf (U.gt 0) g (Y.Φ T y) → ∀ (k : ℕ) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι) (J' : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z J → Good D.toPre.P.L z J' → ∃ c : (T.left.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), IsTermOf Y b τ → F.Lead α b → U.ExpandsAt 0 k s F.f → sval s (g ≫ (fstG (maximalIdeal R) 0 G).left) z J = c.val * sval τ y.left z J' := by
  first | exact @GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | exact GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term | (intros; apply GlobalTheory.Mum.FibreVal.sval_eq_unit_mul_term <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValue
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section Val

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem sec_sub_id_eq_val (E : SqExt R) {x : Sp E.B ⟶ X} (hx : x ≫ s = spMap (algebraMap R E.B))
    (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (h : spMap ((E.π : E.C →+* E.B).comp (AlgHom.id R E.C : E.C →+* E.C)) ≫ y = x) (f : Z1 (O (dp0 R) s)) :
    ev f (E.secHom hx E.i E.π_i) - ev f (Thick.trivHom (hx := hy) (T := E.thick x hx) (AlgHom.id R E.C) h) =
      E.val y hy f := by
  subst h
  rfl

theorem val_congr (E : SqExt R) {y y' : Sp E.C ⟶ X} (e : y = y') (hy : y ≫ s = spMap (algebraMap R E.C))
    (hy' : y' ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) : E.val y hy f = E.val y' hy' f := by
  subst e
  rfl

end Val

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

theorem ev_sec_sub_ev_tan_eq_val (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v)
    (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) :
    ev f P.sec - ev f (P.tan hv) = (SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f :=
  sec_sub_id_eq_val (SqExt.ofModule K P.B P.B) P.w (P.trx v) (P.tr v).w ((P.isTransl_trx v).red hv) f

theorem dualMap_id (B : Type) [CommRing B] : dualMap (RingHom.id B) = RingHom.id (DualNumber B) :=
  RingHom.ext fun c ↦ by ext <;> simp [dualMap]

@[reducible] def Pt.origin (A : Over (Sp K)) [GrpObj A] : GPt A where
  B := K
  x := η[A].left
  w := by
    rw [Category.comp_id, Over.w η[A]]
    exact (Cris.spMap_id K).symm

theorem isTransl_origin (v : epsR K ⟶ A) : IsTransl (algebraMap K K) η[A].left v v.left := by
  refine ⟨1, Over.homMk (spMap (dualMap (algebraMap K K)) ≫ v.left) (by
      rw [Category.assoc, Over.w v]
      change spMap _ ≫ spMap _ = spMap _
      rw [← Cris.spMap_comp, dualMap_comp_algebraMap]), rfl, rfl, ?_⟩
  rw [_root_.one_mul]
  change spMap (dualMap (RingHom.id K)) ≫ v.left = v.left
  rw [dualMap_id, Cris.spMap_id, Category.id_comp]

theorem origin_trx (v : epsR K ⟶ A) : (Pt.origin A).trx v = v.left :=
  ((Pt.origin A).isTransl_trx v).unique (isTransl_origin v)

end GlobalTheory.CechKS

namespace GlobalTheory.CechKS

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def tanFn (v : epsR K ⟶ A) (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ ((SqExt.ofModule K P.B P.B).val (P.trx v) (P.tr v).w f).snd

theorem isNat_tanFn (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) : IsNat ⊤ (tanFn v ω.1) := by
  intro P Q φ _
  have := (SqExt.ofModule K P.B P.B).val_map (SqExt.ofModule K Q.B Q.B) (dualAlg φ.ρ) φ.ρ
    (fun c ↦ (fst_dualAlg φ.ρ c).symm) (fun b ↦ by ext <;> simp) (P.trx v) (P.tr v).w (Q.trx v) (Q.tr v).w
    (φ.tr v).pt ω
  simp only [tanFn]
  rw [this, snd_dualAlg]

theorem tanFn_eq (hA : IsAbelianScheme A) (v : epsR K ⟶ A) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A) :
    tanFn v ω.1 P = algebraMap K P.B (tanVal v ω) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ ⊤) ⊤ (fun _ ↦ le_rfl)
    (le_iSup_of_le () le_rfl) (tanFn v ω.1) (fun _ ↦ isNat_tanFn v ω)
  obtain ⟨g₀, rfl⟩ := (GlobalTheory.globalFns_holds (Sp K) A hA).2 g
  have key : ∀ Q : GPt A, tanFn v ω.1 Q = algebraMap K Q.B (valR (𝟙 (Sp K)) ⊤ g₀) := by
    intro Q
    rw [hg () Q (fun _ _ ↦ trivial)]
    have e1 : valR Q.x ⊤ (A.hom.appTop.hom g₀) = valR (Q.x ≫ A.hom) ⊤ g₀ := by
      rw [GlobalTheory.Points.valR_comp Q.x A.hom ⊤ g₀]; rfl
    have e2 : Q.x ≫ A.hom = spMap (algebraMap K Q.B) ≫ 𝟙 (Sp K) :=
      (Category.comp_id (Q.x ≫ A.hom)).symm.trans ((Category.assoc _ _ _).trans (Q.w.trans (Category.comp_id _).symm))
    rw [e1, e2, GlobalTheory.Points.valR_spMap_comp _ _ _ (GlobalTheory.Points.le_preimage_top _)]
  have h0 : tanFn v ω.1 (Pt.origin A) = tanVal v ω := by
    simp only [tanFn]
    rw [tanVal_apply]
    exact congrArg TrivSqZeroExt.snd (val_congr (SqExt.dual K) (origin_trx v) _ _ ω.1)
  rw [key, ← h0, key]
  rfl

theorem ev_sec_sub_ev_tan : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A),
    ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  intro K _ A _ hA v hv ω P
  rw [ev_sec_sub_ev_tan_eq_val P hv ω.1]
  ext
  · rw [TrivSqZeroExt.fst_inr]; exact SqExt.π_val (SqExt.ofModule K P.B P.B) _ _ ω
  · exact tanFn_eq hA v ω P

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValueStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_abelianVariety_translate_value : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (v : epsR K ⟶ A) (hv : IsTangent v) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (P : GPt A), ev ω.1 P.sec - ev ω.1 (P.tan hv) = (TrivSqZeroExt.inr (algebraMap K P.B (tanVal v ω)) : DualNumber P.B) := by
  first | exact @GlobalTheory.CechKS.ev_sec_sub_ev_tan | exact GlobalTheory.CechKS.ev_sec_sub_ev_tan | (intros; apply GlobalTheory.CechKS.ev_sec_sub_ev_tan <;> assumption)
end
end
