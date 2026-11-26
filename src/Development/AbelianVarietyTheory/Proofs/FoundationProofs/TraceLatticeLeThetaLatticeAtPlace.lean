module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Trace

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
  (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ)

def traceLat : Submodule (𝓞 D.what₂.LL) (Fin (R.nW ι) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL)
    ((fun f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) =>
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u)) ''
      {f | IsOrbitFamily (T.Q.Xo ((ι : ℕ) + 1)) T.Q.c (badN D) (wtA (κ ι)) (T.dδ ((ι : ℕ) + 1) (κ ι).n) (fun u : U => ℓ u)
        fun u => ((f u).1 : T.R ((ι : ℕ) + 1))})

def CompareAt (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  localization₂ lam.asIdeal (traceLat h fw ι ℓ U ψ) ≤ localization₂ lam.asIdeal (thetaBase R ι U ψ ph v p)

def CompareOffOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam ≠ p → CompareAt h fw ι ℓ U ψ ph v p lam

variable {h fw ι ℓ U ψ ph v p} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
    {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

def comapEquiv {P G : Type} [Group P] [Group G] {inc : P →* G} (hi : Function.Injective inc) {U : Subgroup G}
    (hU : U ≤ inc.range) : U.comap inc ≃ U :=
  Equiv.ofBijective (fun u => ⟨inc u, u.2⟩) ⟨fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e)), fun u => by
    obtain ⟨g, hg⟩ := hU u.2
    exact ⟨⟨g, show inc g ∈ U from hg ▸ u.2⟩, Subtype.ext hg⟩⟩

theorem isOrbitFamily_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {d : DeltaDat Xo c n} {I I' : Type}
    {m : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {m' : I' → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)}
    {f : I → Rul Xo c} (hf : IsOrbitFamily Xo c bad a d m f) (e : I' → I) (he : ∀ u, m' u = m (e u)) :
    IsOrbitFamily Xo c bad a d m' fun u => f (e u) := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨Λ, N, x₀, P, fun u => x (e u), h1, h2, h3, h4, h5, h6, fun u => he u ▸ h7 (e u)⟩

theorem Th0_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) :
    O.Th0 v i = (traceLat h fw ι ℓ U ψ).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) := by
  have hm : (O.Th0 v i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = traceLat h fw ι ℓ U ψ := by
    rw [t.Th0_eq, t.U_eq]
    unfold thetaEig traceSpan traceLat
    rw [Submodule.map_span, Set.image_image]
    have key : ∀ f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
        (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)
          (∑ᶠ u : U.comap inc, O.ψ (u : P) • z.symm (1 ⊗ₜ[(recB h.toLawsCore).KO] f (comapEquiv hi hU u))) =
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u) := fun f => by
      rw [map_finsum _ (Set.toFinite _), ← finsum_comp_equiv (comapEquiv hi hU)]
      refine finsum_congr fun u => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, toForms_tmul, one_smul, ← algebraMap_smul D.what₂.LL]
      exact congrArg (· • _) (t.ψ_eq u u.2)
    congr 1
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨fun u => f ((comapEquiv hi hU).symm u), isOrbitFamily_comp hf _ (fun u => ?_), ?_⟩
      · exact congrArg (fun a : U => ℓ a) ((comapEquiv hi hU).apply_symm_apply u).symm
      · refine (key _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun u => f (comapEquiv hi hU u), isOrbitFamily_comp hf _ fun u => rfl, key f⟩
  rw [← hm]
  exact (Submodule.comap_map_eq_of_injective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    (toForms_bijective h fw ι z).1 _).symm

theorem trace_lattice_le_theta_lattice_at_place (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    localization₂ v.asIdeal (O.Th0 v i) ≤ localization₂ v.asIdeal (O.ThJ v i) := by
  rw [Th0_eq_comap t hi hU, t.ThJ_eq]
  refine localization_comap_le v _ (hA v fun e => ?_)
  have h1 := hp.1
  split_ifs at h1 with h2
  · exact D.host.pde_ne (h2.symm.trans (e.trans h1))
  · exact h2 (e.trans h1)

end Trace

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def RankAtPlaces (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)

def fillJ (O : OnObj S P c) : OnObj S P c := { O with ThJ := fun v j => O.ThJ v j ⊔ O.Th0 v j }

theorem leafRankJ_fillJ {O : OnObj S P c} (h : RankAtPlaces O) : LeafRankJ (fillJ O) := by
  have key : ∀ v j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) →
      Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) → Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((fillJ O).eJ v j) := fun v j a b => by
    change Formalism.EigenvalueLevelCeiling.IsLatIn _ ((O.ThJ v j ⊔ O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K)))
    rw [Submodule.map_sup]
    refine ⟨b.1.sup a.1, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · change _ ≤ (O.Zg j).restrictScalars (𝓞 K)
      exact sup_le (fun x hx => b.2.le (Submodule.subset_span hx)) fun x hx => a.2.le (Submodule.subset_span hx)
    · exact b.2.ge.trans (Submodule.span_mono (show O.eJ v j ≤ _ from le_sup_left))
  exact fun w hw =>
    ⟨fun j => ⟨((h w hw).1 j).1, key _ j ((h w hw).1 j).1 ((h w hw).1 j).2.1, le_sup_right⟩,
      fun j => ⟨((h w hw).2 j).1, key _ j ((h w hw).2 j).1 ((h w hw).2 j).2.1, le_sup_right⟩⟩

theorem lix_fillJ {O : OnObj S P c} {v : HeightOneSpectrum (𝓞 K)} {j : Bs.J}
    (h : localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)) (M : Submodule (𝓞 K) (Fin (O.nZ j) → K)) :
    Formalism.EigenvalueLevelCeiling.lix v M ((fillJ O).eJ v j) = Formalism.EigenvalueLevelCeiling.lix v M (O.eJ v j) := by
  have h1 : O.ThJ v j ⊔ O.Th0 v j ≤ localization₂ v.asIdeal (O.ThJ v j) :=
    sup_le (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _) ((Formalism.HermitianLatticesTheory.locBasic_le_locS _ _).trans h)
  have h2 : (fillJ O).eJ v j ≤ localization₂ v.asIdeal (O.eJ v j) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := h1 hx
    exact ⟨s, hs, _, hsx, map_smul ((O.e j).restrictScalars (𝓞 K)) s x⟩
  have h3 : localization₂ v.asIdeal ((fillJ O).eJ v j) = localization₂ v.asIdeal (O.eJ v j) :=
    le_antisymm ((Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h2).trans (Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _).le)
      (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (Submodule.map_mono le_sup_left))
  exact (Formalism.EigenvalueLevelCeiling.lix_locP v M _).trans ((congrArg _ h3).trans (Formalism.EigenvalueLevelCeiling.lix_locP v M _).symm)

theorem leafTW1_fillJ {O : OnObj S P c} (h : RankAtPlaces O) (h1 : LeafTW1 O) : LeafTW1 (fillJ O) :=
  ⟨fun w hw =>
    ⟨fun j => ⟨((h1.1 w hw).1 j).1, ((h1.1 w hw).1 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).1 j).2.2 _).symm)⟩,
      fun j => ⟨((h1.1 w hw).2 j).1, ((h1.1 w hw).2 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).2 j).2.2 _).symm)⟩⟩, h1.2⟩

theorem on_core_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn :=
  on_core N (fillJ O) CE hRk hMk hSup hProj hC hSp hS hT0 hD (leafRankJ_fillJ hJ) hI h2 (leafTW1_fillJ hJ h1) hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1

end Place

section Row

variable {T : HeightOneSpectrum (𝓞 D.what₂.LL) → Full D} [inst : ∀ v, Algebra (T v).J.Q.c.F D.what₂.LL]
  {R : ∀ v, RealDat D A (T v).J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ v (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ((R v).MW i σ).Vec}
  {h : ∀ v, LawsP (T v).toTop} {fw : ∀ v, FWTie (T v).J (R v) κ (v₀ v)} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {ι : Bs.J → Fin D.R.m} {wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)} {nT : ℕ}
  {z : ∀ v i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB (h v).toLawsCore).KO] (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {act : ∀ v i, P → (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) →
    (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {inc : P →* G}
  {ℓ : ∀ v i, G → (LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l ≃ₗ[𝓞 D.host.E] LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) ((R v).mu v) U ψ) → D.what₂.LL)}

end Row

end GlobalTheory.TraceClassRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
open MeasureTheory Set GlobalTheory.AdelicU GlobalTheory.OpTrace NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff InnerProductSpace Matrix

noncomputable section

namespace GlobalTheory.Orb

section Operators

variable {H H' V W : Type} [Group H] [Group H'] [MeasurableSpace H] [MeasurableSpace H']
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem repOp_congr {π : H →* (V →L[ℂ] V)} {π' : H' →* (V →L[ℂ] V)} {μ : Measure H} {μ' : Measure H'} {f : H → ℂ}
    {f' : H' → ℂ} (h : ∀ T, IsRepOp π μ f T ↔ IsRepOp π' μ' f' T) : repOp π μ f = repOp π' μ' f' := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    rw [hT.repOp_eq, ((h T).1 hT).repOp_eq]
  · rw [repOp, repOp, dite_eq_right hT, dite_eq_right fun ⟨T, h'⟩ => hT ⟨T, (h T).2 h'⟩]

theorem IsUnitEquiv.symm {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') :
    IsUnitEquiv π' π := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.symm, fun g v => A.injective (by simp [hA])⟩

theorem IsUnitEquiv.trans {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : H →* (V →L[ℂ] V)}
    {π' : H →* (W →L[ℂ] W)} {π'' : H →* (U →L[ℂ] U)} (h : IsUnitEquiv π π') (h' : IsUnitEquiv π' π'') :
    IsUnitEquiv π π'' := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨B, hB⟩ := h'
  exact ⟨A.trans B, fun g v => by simp [hA, hB]⟩

variable [CompleteSpace V] [CompleteSpace W]

theorem isRepOp_conj {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (A : V ≃ₗᵢ[ℂ] W)
    (hA : ∀ g v, A (π g v) = π' g (A v)) {μ : Measure H} {f : H → ℂ} {T : V →L[ℂ] V} (h : IsRepOp π μ f T) :
    IsRepOp π' μ f ((A.toContinuousLinearEquiv : V →L[ℂ] W) ∘L T ∘L
      (A.toContinuousLinearEquiv.symm : W →L[ℂ] V)) := fun w => by
  obtain ⟨h1, h2⟩ := h (A.symm w)
  have e : ∀ g, f g • π' g w = (A.toContinuousLinearEquiv : V →L[ℂ] W) (f g • π g (A.symm w)) := fun g => by
    simp [hA]
  simp only [e]
  refine ⟨ContinuousLinearMap.integrable_comp _ h1, ?_⟩
  rw [ContinuousLinearMap.integral_comp_comm _ h1, ← h2]
  rfl

theorem IsUnitEquiv.hasTrace {π : H →* (V →L[ℂ] V)} {π' : H →* (W →L[ℂ] W)} (h : IsUnitEquiv π π') {μ : Measure H}
    {f : H → ℂ} {c : ℂ} (ht : HasTrace (repOp π μ f) c) : HasTrace (repOp π' μ f) c := by
  by_cases hT : ∃ T, IsRepOp π μ f T
  · obtain ⟨T, hT⟩ := hT
    obtain ⟨A, hA⟩ := h
    rw [hT.repOp_eq] at ht
    rw [(isRepOp_conj A hA hT).repOp_eq]
    exact ⟨ht.1.comp_comp _ _, (ht.1.trace_conj _).trans ht.2⟩
  · obtain ⟨A, hA⟩ := h.symm
    rw [repOp, dite_eq_right hT] at ht
    rw [repOp, dite_eq_right fun ⟨T, h'⟩ => hT ⟨_, isRepOp_conj A hA h'⟩]
    exact ⟨isTraceClass_zero, trace_zero.trans (trace_zero.symm.trans ht.2)⟩

end Operators

section Transport

variable {H H' n V W : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H'] [Fintype n]
  [DecidableEq n] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (e : H ≃ₜ* H') {ι : H →* Matrix n n ℂ} {ι' : H' →* Matrix n n ℂ} {a : Matrix n n ℂ}

variable {e}

theorem conj_symm (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (g : H') :
    ι (e.symm g) = a⁻¹ * ι' g * a⁻¹⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 ha
  obtain ⟨g, rfl⟩ := e.surjective g
  rw [hι, e.symm_apply_apply, Matrix.nonsing_inv_nonsing_inv _ hd]
  simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one]

theorem comp_mem_ccMat (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {f' : H' → ℂ} (h : f' ∈ CcMat ι') :
    f' ∘ e ∈ CcMat ι := by
  obtain ⟨hc, Φ, hΦ, hf⟩ := h
  refine ⟨hc.comp_homeomorph e.toHomeomorph, Φ ∘ fun y i j => ∑ l, (∑ k, a i k * y k l) * a⁻¹ l j,
    hΦ.comp (by fun_prop), fun g => (hf _).trans (congrArg Φ ?_)⟩
  funext i j
  simp only [matCoord, hι, Matrix.mul_apply]

theorem isRegSS_conj_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) (s : H) :
    IsRegSS (ι' (e s)) ↔ IsRegSS (ι s) := by
  rw [IsRegSS, IsRegSS, hι, Matrix.charpoly_mul_comm,
    Matrix.nonsing_inv_mul_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 ha)]


variable (e) in
theorem isCompact_cent_iff (s : H) : IsCompact (cent (e s) : Set H') ↔ IsCompact (cent s : Set H) := by
  rw [isCompact_iff_compactSpace, isCompact_iff_compactSpace]
  exact ⟨fun _ => (centEquiv e s rfl).toHomeomorph.symm.compactSpace,
    fun _ => (centEquiv e s rfl).toHomeomorph.compactSpace⟩

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H'] (e)

theorem measurableEmbedding_equiv : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding

theorem map_symm_map (μ' : Measure H') : (μ'.map e.symm).map e = μ' := by
  rw [Measure.map_map (map_continuous e).measurable (map_continuous e.symm).measurable]
  convert Measure.map_id using 2
  ext x; simp

theorem repOp_map (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) (f' : H' → ℂ) :
    repOp π' (μ.map e) f' = repOp (π'.comp (e : H →* H')) μ (f' ∘ e) :=
  repOp_congr fun T => forall_congr' fun v => and_congr (measurableEmbedding_equiv e).integrable_map_iff
    (by rw [(measurableEmbedding_equiv e).integral_map]; rfl)

theorem isTempered_map_iff (π' : H' →* (V →L[ℂ] V)) (μ : Measure H) :
    IsTempered (μ.map e) π' ↔ IsTempered μ (π'.comp (e : H →* H')) :=
  exists_congr fun _ => and_congr_right fun _ => forall₂_congr fun _ _ =>
    (measurableEmbedding_equiv e).integrable_map_iff

variable {e} [CompleteSpace V]

theorem IsCharFn.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H}
    {π' : H' →* (V →L[ℂ] V)} {Θ : H' → ℂ} (h : IsCharFn ι' (μ.map e) π' Θ) :
    IsCharFn ι μ (π'.comp (e : H →* H')) (Θ ∘ e) := by
  refine ⟨(locallyIntegrable_map_homeomorph e.toHomeomorph).1 h.1, fun s hs =>
    ContinuousAt.comp (h.2.1 _ ((isRegSS_conj_iff ha hι s).2 hs)) (map_continuous e).continuousAt, fun f hf => ?_⟩
  have := h.2.2 _ (comp_mem_ccMat (conj_symm ha hι) hf)
  rw [repOp_map, (measurableEmbedding_equiv e).integral_map] at this
  convert this using 2 <;> ext x <;> simp

variable [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']

theorem IsPseudoCoeff.of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' (μ.map e) D' f') :
    IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  obtain ⟨Θ, hΘ, hO⟩ := h.orb_compact
  refine ⟨comp_mem_ccMat hι h.mem, repOp_map e D' μ f' ▸ h.trace_self, fun U _ _ _ π h1 h2 h3 h4 => ?_,
    fun s hs hT dt _ _ => ?_, Θ ∘ e, hΘ.of_map ha hι, fun s hs hT dt _ _ => ?_⟩
  · obtain ⟨π', rfl⟩ : ∃ π' : H' →* (U →L[ℂ] U), π = π'.comp (e : H →* H') :=
      ⟨π.comp (e.symm : H' →* H), MonoidHom.ext fun x => by simp⟩
    rw [← repOp_map]
    refine h.trace_other U π' ⟨fun g v => ?_, fun v => ?_⟩ ⟨h2.1, fun S hS => h2.2 S ⟨hS.1, fun g => hS.2 _⟩⟩
      ((isTempered_map_iff e π' μ).2 h3) fun ⟨A, hA⟩ => h4 ⟨A, fun g => hA _⟩
    · simpa using h1.1 (e.symm g) v
    · simpa [Function.comp_def] using (h1.2 v).comp (map_continuous e.symm)
  · exact (hasOrbInt_map e rfl f' _).1.1 (h.orb_noncompact _ ((isRegSS_conj_iff ha hι s).2 hs)
      (mt (isCompact_cent_iff e s).1 hT) _)
  · have := hO _ ((isRegSS_conj_iff ha hι s).2 hs) ((isCompact_cent_iff e s).2 hT) (dt.map (centEquiv e s rfl))
    rw [map_measureReal_apply (map_continuous _).measurable MeasurableSet.univ, preimage_univ] at this
    exact (hasOrbInt_map e rfl f' _).1.1 this

theorem IsPseudoCoeff.comp (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ' : Measure H'} [μ'.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPseudoCoeff ι' μ' D' f') :
    IsPseudoCoeff ι (μ'.map e.symm) (D'.comp (e : H →* H')) (f' ∘ e) :=
  IsPseudoCoeff.of_map ha hι (by rwa [map_symm_map])

theorem isPseudoCoeff_map_iff (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} :
    IsPseudoCoeff ι' (μ.map e) D' f' ↔ IsPseudoCoeff ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  refine ⟨IsPseudoCoeff.of_map ha hι, fun h => ?_⟩
  convert h.comp (e := e.symm) (Matrix.isUnit_nonsing_inv_iff.2 ha) (conj_symm ha hι) using 1
  · rfl
  · exact MonoidHom.ext fun x => by simp
  · ext x; simp

end Transport

section Scaling

variable {H n V W : Type} [Group H] [TopologicalSpace H] [Fintype n] [DecidableEq n] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [MeasurableSpace H]
  {ι : H →* Matrix n n ℂ} {μ : Measure H} {c : ℝ≥0}


variable [CompleteSpace V] [CompleteSpace W]

variable [BorelSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [μ.IsHaarMeasure]

end Scaling

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

theorem exists_frameMat_eq (ρ : D.what₂.Tau) {x : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hx : x ∈ UJset (M.ε ρ)) :
    ∃ g, frameMat M ρ g = x := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have e : M.fr ρ * ((M.fr ρ)⁻¹ * x * M.fr ρ) * (M.fr ρ)⁻¹ = x := by
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hd, mul_one]
  obtain ⟨g, hg⟩ := exists_archEquiv_eq V (embOverOf D ρ) rfl ((conj_mem_UJset_iff M ρ _).1 (e.symm ▸ hx))
  exact ⟨g, (congrArg (M.fr ρ * · * (M.fr ρ)⁻¹) hg).trans e⟩

theorem isEmbedding_frameMat (ρ : D.what₂.Tau) : Topology.IsEmbedding (frameMat M ρ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h : Topology.IsEmbedding fun x : Matrix (Fin V.rank) (Fin V.rank) ℂ => M.fr ρ * x * (M.fr ρ)⁻¹ :=
    Function.LeftInverse.isEmbedding (f := fun x => (M.fr ρ)⁻¹ * x * M.fr ρ) (fun x => by
      simp only [mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.nonsing_inv_mul_cancel_left _ _ hd, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  exact h.comp (isEmbedding_archMat V.gram (isCMExt_host D) (embOverOf D ρ))

def frameHom (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) →* Formalism.REAL.UJ (M.ε ρ) :=
  (frameMat M ρ).toHomUnits.codRestrict _ (frameMat_mem M ρ)

theorem frameHom_bijective (ρ : D.what₂.Tau) : Function.Bijective (frameHom M ρ) :=
  ⟨fun _ _ h => (isEmbedding_frameMat M ρ).injective (congrArg (ujMat (M.ε ρ)) h), fun x => by
    obtain ⟨g, hg⟩ := exists_frameMat_eq M ρ (x := ujMat (M.ε ρ) x) x.2
    exact ⟨g, Subtype.ext (Units.ext hg)⟩⟩

theorem isEmbedding_ujMat {m : ℕ} (ε : Fin m → Bool) : Topology.IsEmbedding (ujMat ε) :=
  (Formalism.REAL.isClosedEmbeddingMatrix m ε).1.isEmbedding

def frameEquiv (ρ : D.what₂.Tau) : GArch D.sp.cm.sig V.gram (placeOf D ρ) ≃ₜ* Formalism.REAL.UJ (M.ε ρ) :=
  { MulEquiv.ofBijective _ (frameHom_bijective M ρ) with
    continuous_toFun := (isEmbedding_ujMat _).continuous_iff.2 (isEmbedding_frameMat M ρ).continuous
    continuous_invFun := (isEmbedding_frameMat M ρ).continuous_iff.2 ((isEmbedding_ujMat _).continuous.congr
      fun x => congrArg (ujMat (M.ε ρ))
        ((MulEquiv.ofBijective _ (frameHom_bijective M ρ)).apply_symm_apply x).symm) }

theorem ujMat_frameEquiv_eq_conj (ρ : D.what₂.Tau) (g : GArch D.sp.cm.sig V.gram (placeOf D ρ)) :
    ujMat (M.ε ρ) (frameEquiv M ρ g) = M.fr ρ * matAt V ρ g * (M.fr ρ)⁻¹ := rfl

theorem isPseudoCoeff_dsRep_iff (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ) : haveI := (M.ds ρ).1
    IsPseudoCoeff (ujMat (M.ε ρ)) (μ.map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1) f ↔
      IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) (f ∘ frameEquiv M ρ) :=
  haveI := (M.ds ρ).1
  isPseudoCoeff_map_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ)

end Record

end GlobalTheory.Orb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemHatSwap
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HLatMove

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_hatL {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) (hx : x ∈ St β) {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) Λ) : x.1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨y, rfl⟩ := hx
  rw [hβ] at hz ⊢
  intro i
  have e : (β⁻¹).1 *ᵥ ((frGL β y).1 *ᵥ z) = (intGL F E n y).1 *ᵥ ((β⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    change β⁻¹ * (β * intGL F E n y * β⁻¹) = _
    group
  rw [e]
  exact Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (y.1 i j).2 (hz j)

theorem mulVec_mem_hat {β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hq : Formalism.UG.bc (Algebra.TensorProduct.comm F _ E).toAlgHom.toRingHom q ∈ St β)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) :
    q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) := by
  have h := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _
    (mulVec_mem_hatL hβ hq (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
  convert h using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl


omit [NumberField F] [NumberField E] in
theorem bc_map_bc_inclR {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (g : GL (Fin n) E) :
    Formalism.UG.bc (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (Formalism.UG.bc (inclR (F := F) R) g) =
      Formalism.UG.bc (inclR (F := F) S) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change Algebra.TensorProduct.map f (AlgHom.id F E) (1 ⊗ₜ g.1 i j) = 1 ⊗ₜ g.1 i j
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl


omit [NumberField F] [NumberField E] in
theorem span_move {R O : Type} [CommRing R] [Algebra F R] [CommRing O] [Algebra O E] (H : AddSubgroup (Fin n → R ⊗[F] E))
    (g : GL (Fin n) E) (h q : GL (Fin n) (R ⊗[F] E)) (h1 : ∀ z ∈ H, q.1 *ᵥ z ∈ H) (h2 : ∀ z ∈ H, (q⁻¹).1 *ᵥ z ∈ H) :
    Submodule.span O {x : Fin n → E |
        ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H} =
      (Submodule.span O {x : Fin n → E | (h⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) ∈ H}).map
        ((Matrix.mulVecLin g.1).restrictScalars O) := by
  have hv : ∀ (g : GL (Fin n) E) (x : Fin n → E),
      (Formalism.UG.bc (inclR (F := F) R) g).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) = fun i => (1 : R) ⊗ₜ[F] (g.1 *ᵥ x) i := by
    intro g x
    funext i
    exact (RingHom.map_mulVec (inclR (F := F) R) g.1 x i).symm
  have key : ∀ z, (q⁻¹).1 *ᵥ z ∈ H ↔ z ∈ H := by
    refine fun z => ⟨fun hz => ?_, h2 z⟩
    have := h1 _ hz
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
  have hs : ∀ x : Fin n → E,
      ((Formalism.UG.bc (inclR (F := F) R) g * h * q)⁻¹).1 *ᵥ (fun i => (1 : R) ⊗ₜ[F] x i) =
        (q⁻¹).1 *ᵥ ((h⁻¹).1 *ᵥ fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ x) i) := by
    intro x
    rw [← hv, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      mul_inv_rev, mul_inv_rev, mul_assoc]
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(g⁻¹).1 *ᵥ x, (key _).1 (hs x ▸ hx), ?_⟩
    change g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    change _ *ᵥ _ ∈ H
    rw [hs, key]
    change _ *ᵥ (fun i => (1 : R) ⊗ₜ[F] ((g⁻¹).1 *ᵥ (g.1 *ᵥ y)) i) ∈ H
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy

end General

variable {D : D7}

theorem exists_ratMat (V : HSp D) (γ : GQ V) : ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧
    (Bridge.ratF V γ).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
  obtain ⟨γE, -, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  refine ⟨γE, hm, ?_⟩
  change finHom V γ.1 = _
  rw [finHom, MonoidHom.comp_apply, hm]
  exact bc_map_bc_inclR _ _

theorem hLat_eq_span {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (h : Bridge.Gf V) :
    Bridge.hLat V h = Submodule.span (𝓞 D.host.E) {x : Fin V.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))} := by
  rw [GlobalTheory.PrincInLevel.eq_latC hΛ, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
  rfl

theorem mulVec_mem_hat_swap {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : IsFrame β Λ) {q : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)} (hq : Formalism.UG.bc (swapAE D) q ∈ St β) :
    ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)),
      q.1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) :=
  fun _ hz => mulVec_mem_hat hβ hq hz

theorem hLat_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSDFrame V β Λ 1) (g h q : Bridge.Gf V) (γE : GL (Fin V.rank) D.host.E)
    (hf : g.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE) (hq : Formalism.UG.bc (swapAE D) q.1 ∈ St β) :
    Bridge.hLat V (g * h * q) = (Bridge.hLat V h).map ((Matrix.mulVecLin γE.1).restrictScalars (𝓞 D.host.E)) := by
  have hfr : IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hq' : Formalism.UG.bc (swapAE D) (q.1⁻¹) ∈ St β := by
    rw [MonoidHom.map_inv]; exact (St β).inv_mem hq
  have e : (g * h * q).1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE * h.1 * q.1 := hf ▸ rfl
  rw [hLat_eq_span hΛ, hLat_eq_span hΛ, e]
  exact span_move _ γE h.1 q.1 (mulVec_mem_hat_swap hfr hq) (mulVec_mem_hat_swap hfr hq')

theorem hLat_rat_mul_stab : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ γ : GQ V, ∃ γE : GL (Fin V.rank) D.host.E, Bridge.IsRatMat V γ γE ∧ ∀ h q : Bridge.Gf V, Formalism.UG.bc (swapAE D) (q : GL (Fin V.rank) _) ∈ St β → Bridge.hLat V (Bridge.ratF V γ * h * q) = Formalism.HermitianLatticesTheory.gmap ((Formalism.L2.Col.toGLm D.host.E V.rank).symm γE) (Bridge.hLat V h) := by
  intro D V β Λ hΛ γ
  obtain ⟨γE, hγ, hf⟩ := exists_ratMat V γ
  refine ⟨γE, hγ, fun h q hq => ?_⟩
  rw [Formalism.L2.Col.gmap_eq_map, MulEquiv.apply_symm_apply]
  exact hLat_mul hΛ _ h q γE hf hq

end GlobalTheory.HLatMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
open Set Filter GlobalTheory.AdelicU NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology ComplexConjugate ContDiff Matrix

noncomputable section

namespace GlobalTheory.Orb

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IsSmoothRealFam (u : P → GAd σ J) : Prop :=
  (∀ t, projFin σ J (u t) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j, ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (u t)) i j


omit [NumberField E] in
theorem isSmoothRealFam_one : IsSmoothRealFam fun _ : P => (1 : GAd σ J) :=
  ⟨fun _ => map_one _, fun _ _ _ _ => contDiff_const⟩


omit [NumberField E] in
theorem IsSmoothRealFam.mul {u v : P → GAd σ J} (hu : IsSmoothRealFam u) (hv : IsSmoothRealFam v) :
    IsSmoothRealFam fun t => u t * v t := by
  refine ⟨fun t => by rw [map_mul, hu.1, hv.1, one_mul], fun w τ i j => ?_⟩
  simp only [map_mul, Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hu.2 w τ i k).mul (hv.2 w τ k j)


omit [NumberField E] in
theorem IsSmoothRealFam.comp {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {u : P → GAd σ J}
    (hu : IsSmoothRealFam u) {p : Q → P} (hp : ContDiff ℝ ∞ p) : IsSmoothRealFam fun t => u (p t) :=
  ⟨fun _ => hu.1 _, fun w τ i j => (hu.2 w τ i j).comp hp⟩


omit [NumberField E] in
theorem isSmoothRealFam_prod {k : ℕ} {u : Fin k → P → GAd σ J} (hu : ∀ i, IsSmoothRealFam (u i)) :
    IsSmoothRealFam fun t => (List.ofFn fun i => u i t).prod := by
  induction k with
  | zero => simpa using isSmoothRealFam_one
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hu 0).mul (ih fun i => hu i.succ)


omit [NumberField E] in
theorem infCoord_mul (x : GInf σ J) (y : GAd σ J) : infCoord σ J (x * projInf σ J y) =
    fun w τ i j => ∑ k, infCoord σ J x w τ i k * archMat σ J τ (projArch σ J w y) k j := by
  funext w τ i j
  simp only [infCoord, archCoord, matCoord, map_mul, Matrix.mul_apply, projInfArch_projInf]

theorem IsSmoothRealFam.contDiff {u : P → GAd σ J} (hu : IsSmoothRealFam u) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J)
    (g : GAd σ J) : ContDiff ℝ ∞ fun t => f (g * u t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, -, rfl⟩ := hf
    simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]
    refine (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (hu.2 w τ k j))).mul contDiff_const
  | zero => exact contDiff_const
  | add f f' _ _ h h' => exact h.add h'
  | smul a f _ h => exact h.const_smul a

theorem IsSmoothRealFam.deriv_mem_ccInf {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {a : GInf σ J → ℂ} (ha : a ∈ CcInf σ J) :
    (fun x => deriv (fun t => a (x * projInf σ J (u t))) 0) ∈ CcInf σ J := by
  obtain ⟨hs, Φ, hΦ, e⟩ := ha
  refine ⟨.intro hs fun x hx => ?_, fun y => fderiv ℝ Φ y fun w τ i j =>
    ∑ k, y w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0, ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun t => x * projInf σ J (u t)) (𝓝 0) (𝓝 x) := by
      simpa [h0] using (continuous_const.mul ((continuous_projInf σ J).comp hc)).tendsto (f := fun t => x * projInf σ J (u t)) 0
    rw [EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) (h1.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)),
      deriv_const]
  · refine (hΦ.fderiv_right (m := ∞) le_rfl).clm_apply ?_
    exact contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) τ) i) k).mul
        contDiff_const
  · have h1 : HasDerivAt (fun t => infCoord σ J (x * projInf σ J (u t))) (fun w τ i j =>
        ∑ k, infCoord σ J x w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0) 0 := by
      simp only [infCoord_mul]
      exact hasDerivAt_pi.2 fun w => hasDerivAt_pi.2 fun τ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j =>
        HasDerivAt.fun_sum fun k _ => ((hu.2 w τ k j).differentiable (by simp) 0).hasDerivAt.const_mul _
    have h2 := (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 h1
    simp only [h0, map_one, mul_one] at h2
    simp only [e]
    exact h2.deriv

theorem IsSmoothRealFam.deriv_mem_ccAd {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (fun g => deriv (fun t => f (g * u t)) 0) ∈ CcAd σ J := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    convert infFin_mem_ccAd (hu.deriv_mem_ccInf hc h0 ha) hb using 1
    funext g
    simp only [infFin, map_mul, hu.1, mul_one, deriv_mul_const_field]
  | zero =>
    simp only [Pi.zero_apply, deriv_const]
    exact (CcAd σ J).zero_mem
  | add f f' hf hf' h h' =>
    convert (CcAd σ J).add_mem h h' using 1
    funext g
    exact deriv_fun_add ((hu.contDiff hf g).differentiable (by simp) 0) ((hu.contDiff hf' g).differentiable (by simp) 0)
  | smul c f _ h =>
    convert (CcAd σ J).smul_mem c h using 1
    funext g
    exact deriv_fun_const_smul_field c _

theorem isSmoothRealFam_embArch (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {x : P → GArch σ J w}
    (hx : ∀ i j, ContDiff ℝ ∞ fun t => archMat σ J τ (x t) i j) :
    IsSmoothRealFam (fun t => embArch σ J w (x t)) ∧ Continuous fun t => embArch σ J w (x t) := by
  refine ⟨⟨fun t => projFin_embArch σ J w _, fun w' τ' i j => ?_⟩, (continuous_embArch σ J w).comp
    ((isEmbedding_archMat J h τ).continuous_iff.2 (continuous_pi fun i => continuous_pi fun j => (hx i j).continuous))⟩
  by_cases e : w' = w
  · subst e
    simp only [projArch_embArch_self]
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · simpa only [archMat_apply, e] using hx i j
    · simp only [archMat_apply, e]
      exact Complex.conjCLE.contDiff.comp (hx i j)
  · simp only [projArch_embArch_ne σ J e]
    exact contDiff_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_exp_smul_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X) : Matrix (Fin n) (Fin n) ℂ) i j := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp
    (h.comp (contDiff_id.smul contDiff_const))

end

end General

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSmoothRealFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) :
    IsSmoothRealFam (oneP θ V τ X) ∧ Continuous (oneP θ V τ X) ∧ oneP θ V τ X 0 = 1 := by
  choose x hx using fun t : ℝ => exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  have e : oneP θ V τ X = fun t => embArch _ _ _ (x t) := funext fun t => by
    rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl]
  have h := isSmoothRealFam_embArch (isCMExt_host D) (embOverOf D τ) (x := x) fun i j => by
    simp only [archMat_eq_archEquiv _ (isCMExt_host D), hx]
    exact contDiff_exp_smul_entry X i j
  refine ⟨e ▸ h.1, e ▸ h.2, ?_⟩
  have h1 := atTau_archEquiv hθ V (embOverOf D τ) rfl 1
  rw [map_one, map_one] at h1
  rw [oneP, zero_smul, NormedSpace.exp_zero]
  exact h1

theorem ccGA_smooth_and_Rder_mem (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (f : GA D V → ℂ)
    (hf : f ∈ CcGA V) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧
    ∀ τ, ∀ X ∈ lieAt V τ, Rder θ V τ X f ∈ CcGA V :=
  ⟨fun _ _ _ hX g => (isSmoothRealFam_prod fun i => (isSmoothRealFam_oneP hθ (hX i)).1.comp
      (contDiff_apply ℝ (fun _ => ℝ) i)).contDiff hf g,
    fun _ _ hX => have h := isSmoothRealFam_oneP hθ hX; h.1.deriv_mem_ccAd h.2.1 h.2.2 hf⟩

end Record

end GlobalTheory.Orb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
noncomputable section

namespace GlobalTheory.Eis.Conv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.AdelicU

theorem norm_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h : Module.finrank F E = 2) :
    Algebra.norm (AF F) (halfE F E).1 = (halfInf F).1 ^ 2 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
  change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1) = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h]

theorem evFin_halfInf (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (halfInf F).1 = 1 :=
  map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (halfInf F).1 = algebraMap F _ 2⁻¹ :=
  (GlobalTheory.AutFunCompare.evW w).commutes _

theorem nnnorm_evInf_halfInf (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    ‖evInf F w (halfInf F).1‖₊ = 2⁻¹ := by
  rw [evInf_halfInf]
  have h2 : w (2⁻¹ : F) = 2⁻¹ := by
    rw [← InfinitePlace.norm_embedding_eq w, map_inv₀, norm_inv, map_ofNat]
    simp
  have e : ‖((2⁻¹ : F) : w.Completion)‖ = 2⁻¹ := (InfinitePlace.Completion.norm_coe w _).trans h2
  apply NNReal.eq
  rw [NNReal.coe_inv, NNReal.coe_ofNat]
  rw [InfinitePlace.Completion.algebraMap_apply]
  exact e

theorem absE_halfE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) : absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  haveI := h.1
  have hn := norm_halfE F E h.2.2.1
  have hfin : ∀ v, absEv F E v (unitFin F E v (halfE F E)) = 1 := fun v => by
    rw [absEv_unitFin, hn, map_pow, evFin_halfInf]
    simp
  have hinf : ∀ w, absEw F E w (unitInf F E w (halfE F E)) = 4⁻¹ := fun w => by
    rw [absEw_unitInf, hn, map_pow, nnnorm_pow, nnnorm_evInf_halfInf, InfinitePlace.mult,
      if_pos (IsTotallyReal.isReal w), pow_one, inv_pow]
    norm_num
  rw [absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, Finset.prod_congr rfl fun w _ => hinf w,
    Finset.prod_const, Finset.card_univ, inv_pow]

end GlobalTheory.Eis.Conv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinityStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → absE F E (halfE F E) = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := by
  first | exact @GlobalTheory.Eis.Conv.absE_halfE | exact GlobalTheory.Eis.Conv.absE_halfE | (intros; apply GlobalTheory.Eis.Conv.absE_halfE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlDetEqOneOfMemUnip
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem gl_det_eq_one_of_mem_unip {κ : Type} [CommRing κ] {r : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unip κ r) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular (M := (g : Matrix (Fin r) (Fin r) κ))
    (fun i j h => unip_lower hg h)]
  simp [unip_diag hg]

theorem chi_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.IsGrp F) :
    ∀ i, ∀ u ∈ F.P0, (R.FW i).chi u = 1 := by
  intro i u hu
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simpa using hu
  rw [h1] at h2
  apply Units.ext
  apply D.what₂.embLL.injective
  rw [h.chiW i u, Units.val_one, map_one]
  refine Finset.prod_eq_one fun PP _ => ?_
  rw [gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)), map_one, Units.val_one]

end GlobalTheory.TraceIncl
end
