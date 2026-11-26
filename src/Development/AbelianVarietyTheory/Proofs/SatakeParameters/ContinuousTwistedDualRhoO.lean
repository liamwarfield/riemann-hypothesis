module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoinStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
noncomputable section

namespace GlobalTheory.HTW.RecS.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec GlobalTheory.HTW.RecS

theorem coefExt_dvr {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    ∃ _ : IsDomain ↥(OL Cx.LL), IsDiscreteValuationRing ↥(OL Cx.LL) ∧ IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1 :=
  (goodO_finExt_integers _ Cx.LL).1

section Std

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}

theorem mem_stdG_OL (x : Fin k → ↥LL.1) : x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Lat K LL where
  V := Fin k → ↥LL.1
  ρ := matRep M
  cont := hc
  L :=
    { T := stdG ↥(OL LL) ↥LL.1 k
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        change ∑ b, M g j b * x b ∈ OL LL
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hO g j b) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective k))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL.1 (Fin k)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem stdLat_isMatRep (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : IsMatRep (stdLat M hO hc) M :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem finrank_stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Module.finrank ↥LL.1 (stdLat M hO hc).V = k :=
  Module.finrank_fin_fun _

def latId (T : Lat K LL) : LatHom T.L T.L where
  f := LinearMap.id
  equiv _ _ := rfl
  cont := continuous_id
  T_le _ h := h

theorem latId_onto (T : Lat K LL) : (latId T).Onto := fun y hy => ⟨y, hy, rfl⟩

end Std

section LocRep

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem locC_mem_OL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : TruncatedSeriesCountingIdentities.locC Cx M g a b ∈ OL Cx.LL := by
  have h1 : Br.loc D.nbr i w hw M g a b ∈ OL (D.nbr i w hw).LL :=
    ((D.nbr i w hw).eO (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)).2
  change Cx.inc (Br.loc D.nbr i w hw M g a b) ∈ OL Cx.LL
  exact IsIntegral.map ((IntermediateField.inclusion Cx.le).restrictScalars ℤ_[D.nd.l i]) h1

end LocRep

section Glob

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem continuous_twistedDual_rhoO (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous fun g => T2O D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have hW : Continuous fun g => WpO D.nd i ρ π g := h1.smul hρ
  have hε : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  exact hε.smul (hW.comp continuous_inv).matrix_transpose

end Glob

section Sub

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

def phiK : KK D.nd i →+* ↥Cx.LL.1 := Cx.inc.comp (Br.toLLK (D.nbr i w hw))

theorem locC_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC Cx M g = (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiK i w hw Cx) := by
  refine Matrix.ext fun a b => ?_
  change Cx.inc ((D.nbr i w hw).toLL (M _ a b)) = Cx.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M _ a b)))
  rw [Br.toLLK_alg]
  rfl

theorem mapM_rDuO (h : GE D.nd) :
    mapM (toK D.nd i) (rDuO D.nd i r π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rO D.nd i r π) h⁻¹).transpose := by
  ext a b
  simp [mapM, rDuO, twistM, dualM]

theorem mapM_T2O (h : GE D.nd) :
    mapM (toK D.nd i) (T2O D.nd i ρ π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rhoO D.nd i ρ π) h⁻¹).transpose := by
  ext a b
  simp [mapM, T2O, WpO, twistM, dualM]
  ring

end Sub

section Sub2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem isSubOfSums_T2O (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsSubOfSums (matRep (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))) fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) := by
  obtain ⟨e, he⟩ := hd
  let A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' ((LinearMap.fst (KK D.nd i) _ _).comp e.toLinearMap)
  let B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap.comp (LinearMap.inl (KK D.nd i) _ _))
  have hA : ∀ u, A.mulVec u = (e u).1 := fun u => by simp [A, LinearMap.toMatrix'_mulVec]
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hint : ∀ h : GE D.nd, A * mapM (toK D.nd i) (rO D.nd i r π) h = mapM (toK D.nd i) (rhoO D.nd i ρ π) h * A := by
    intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he]
  let φ := phiK i w hw Cx
  let At : Matrix (Fin D.R.nV) (Fin D.R.r) ↥Cx.LL.1 := A.transpose.map φ
  have hinj : Function.Injective At.mulVec := by
    have h1 : B.transpose.map φ * At = 1 := by
      rw [← Matrix.map_mul, ← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (B.transpose.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  refine ⟨1, fun _ => π, LinearMap.pi fun _ => Matrix.mulVecLin At, ?_, fun g v => ?_⟩
  · intro u v huv
    exact hinj (congrFun huv 0)
  · funext a
    change At.mulVec ((TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π) g).mulVec v) =
      (TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r π) g).mulVec (At.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [locC_eq_map, locC_eq_map, mapM_rDuO, mapM_T2O]
    have hK : ∀ (s : KK D.nd i) (h : GE D.nd),
        A.transpose * (s • (mapM (toK D.nd i) (rhoO D.nd i ρ π) h).transpose) =
          (s • (mapM (toK D.nd i) (rO D.nd i r π) h).transpose) * A.transpose := by
      intro s h
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hint]
    simp only [At]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hK]

end Sub2

theorem exists_lattices {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (h : PtIn i r ρ π) :
    ∃ (T₁ T₂ : Lat (D.nbr i w hw).Kw Cx.LL) (F : LatHom T₁.L T₂.L),
      IsSubOfTwistedDualSums i r w hw Cx T₁ ∧ IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ ∧ F.Onto ∧ Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
  let T := stdLat (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) (locC_mem_OL i w hw Cx _)
    (fun v => locC_cont D i _ (continuous_twistedDual_rhoO i ρ π h.contρ) w hw Cx v)
  exact ⟨T, T, latId T, isSubOfSums_T2O i r ρ π w hw Cx h.dec, stdLat_isMatRep _ _ _, latId_onto T,
    finrank_stdLat _ _ _⟩

end GlobalTheory.HTW.RecS.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_field_le_unramified : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : w ∈ placesOver H.E (N.l i)),
    N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  intro R H what₂ N nbr i w hw h2 hq hd
  have hK := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E ((nbr i w hw).j.comp (algebraMap H.E N.Om)) (nbr i w hw).Kw.1
    (nbr i w hw).j_E (nbr i w hw).Kw.2 (nbr i w hw).j_dense
  rw [hK, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified H (N.l i) h2 hq hd _ x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i)), N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  first | exact @GlobalTheory.bridge_field_le_unramified | exact GlobalTheory.bridge_field_le_unramified | (intros; apply GlobalTheory.bridge_field_le_unramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasCohomologyTransport
noncomputable section

namespace GlobalTheory.ConjCoh

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.ContraPair Topology
open scoped TensorProduct

variable {E : Type} [Field E] {a : ℕ}

section Transport

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  {κ : Kinf E a → Module.End ℂ M} {L : Lie E a →ₗ[ℝ] Module.End ℂ M}
  {κ' : Kinf E a → Module.End ℂ M'} {L' : Lie E a →ₗ[ℝ] Module.End ℂ M'}

def tr (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) :
    Herm E a [⋀^Fin q]→ₗ[ℝ] M' :=
  (T.restrictScalars ℝ).compAlternatingMap (ω.compLinearMap σ)

theorem tr_apply (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (X : Fin q → Herm E a) : tr σ T ω X = T (ω fun i => σ (X i)) := rfl

theorem isCochain_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} {T : M →ₗ[ℂ] M'}
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ' (tr σ T ω) := fun k X => by
  rw [tr_apply, tr_apply, ← hκ, ← hω]
  simp only [had]

theorem dCo_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {T : M →ₗ[ℂ] M'}
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m))
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : dCo L' (tr σ T ω) = tr σ T (dCo L ω) := by
  refine AlternatingMap.ext fun X => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tr_apply, dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hL, tr_apply]
  rfl

theorem tr_tr {σ : Herm E a →ₗ[ℝ] Herm E a} (hσ : ∀ X, σ (σ X) = X) (T : M ≃ₗ[ℂ] M')
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : tr σ T.symm.toLinearMap (tr σ T.toLinearMap ω) = ω := by
  refine AlternatingMap.ext fun X => ?_
  simp [tr_apply, hσ]

theorem tr_zero (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} :
    tr σ T (0 : Herm E a [⋀^Fin q]→ₗ[ℝ] M) = 0 :=
  AlternatingMap.ext fun X => by simp [tr_apply]

theorem hasCohomology_transport {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} (T : M ≃ₗ[ℂ] M')
    (hσ : ∀ X, σ (σ X) = X) (hs : ∀ k, s (s k) = k)
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m)) (H : HasCohomology κ L) : HasCohomology κ' L' := by
  have hκ' : ∀ k m, T.symm (κ' (s k) m) = κ k (T.symm m) := fun k m => by
    rw [T.symm_apply_eq]
    have := hκ (s k) (T.symm m)
    rw [hs, T.apply_symm_apply] at this
    exact this.symm
  have hL' : ∀ X m, T.symm (L' (toL (σ X).1) m) = L (toL X.1) (T.symm m) := fun X m => by
    rw [T.symm_apply_eq]
    have := hL (σ X) (T.symm m)
    rw [hσ, T.apply_symm_apply] at this
    exact this.symm
  rcases H with ⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩
  · refine Or.inl ⟨tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun h => h2 ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · rw [← tr_tr hσ T ω, h, tr_zero]
  · refine Or.inr ⟨q, tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun η hη h => ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · refine h2 (tr σ T.symm.toLinearMap η) (isCochain_tr (T := T.symm.toLinearMap) had hκ' hη) ?_
      rw [dCo_tr (L := L') (T := T.symm.toLinearMap) hL', h, tr_tr hσ]

end Transport

variable [NumberField E] [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.ConjCoh

end

namespace GlobalTheory.ConjCoh

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

end GlobalTheory.ConjCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKurFrobTauEmbPosPl
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem exists_aut_of_algHoms {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →ₐ[ℚ] K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) := by
  have hmem : ∀ x, ∃ y, f y = g x := fun x => by
    have hs := Normal.splits (inferInstance : Normal ℚ E) x
    have hi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hr : (((minpoly ℚ x).map (algebraMap ℚ E)).map (f : E →+* K)).IsRoot (g x) := by
      rw [Polynomial.map_map, AlgHom.comp_algebraMap_of_tower, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    exact hs.mem_range_of_isRoot (Polynomial.map_ne_zero (minpoly.ne_zero hi)) hr
  choose v hv using hmem
  have hf : Function.Injective f := f.toRingHom.injective
  let w : E →ₐ[ℚ] E :=
    { toFun := v
      map_one' := hf (by rw [hv, map_one, map_one])
      map_mul' := fun a b => hf (by rw [hv, map_mul, map_mul, hv, hv])
      map_zero' := hf (by rw [hv, map_zero, map_zero])
      map_add' := fun a b => hf (by rw [hv, map_add (f := _), map_add (f := _), hv, hv])
      commutes' := fun r => hf (by
        rw [hv, AlgHom.commutes, AlgHom.commutes]) }
  exact ⟨AlgEquiv.ofBijective w (AlgHom.normal_bijective ℚ E E w), fun x => (hv x).symm⟩

theorem exists_aut_of_embeddings {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K]
    (f g : E →+* K) : ∃ u : E ≃ₐ[ℚ] E, ∀ x, g x = f (u x) :=
  exists_aut_of_algHoms f.toRatAlgHom g.toRatAlgHom

theorem padic_mem_Kur (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  have hc : Continuous (algebraMap ℚ_[p] ℂ_[p]) := (algebraMap_isometry ℚ_[p] ℂ_[p]).continuous
  refine (Padic.denseRange_ratCast p).induction_on (p := fun x => algebraMap ℚ_[p] ℂ_[p] x ∈ MaximalUnramifiedExtension p) x ?_ ?_
  · exact Formalism.L2.Th1.D.GaussNormEstimates.isClosed_Kur.preimage hc
  · intro q
    simp

theorem coe_mem_Kur (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension p) :
    algebraMap (PadicAlgCl p) ℂ_[p] x ∈ MaximalUnramifiedExtension p := by
  unfold Formalism.BasicNotions.Loc.MaximalUnramifiedExtension at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, hm, hpm, h1⟩ := hx
    exact Formalism.L2.Th1.D.GaussNormEstimates.mu_mem_Kur hm hpm (by rw [← map_pow, h1, map_one])
  | algebraMap x =>
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur p x
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem host_image_mem_Kur_complex {R : Ranks} (H : Host R) (p : ℕ) [Fact p.Prime] (h2 : p ∉ H.small) (hq : p ≠ H.q)
    (hd : p ≠ H.d) (ρ : H.E →+* ℂ_[p]) (x : H.E) : ρ x ∈ MaximalUnramifiedExtension p := by
  have : IsGalois ℚ H.E := H.hostE_isGalois
  let c : H.E →+* PadicAlgCl p := (IsAlgClosed.lift : H.E →ₐ[ℚ] PadicAlgCl p)
  obtain ⟨u, hu⟩ := exists_aut_of_embeddings ((algebraMap (PadicAlgCl p) ℂ_[p]).comp c) ρ
  rw [hu, RingHom.comp_apply]
  exact coe_mem_Kur p (GlobalTheory.HostKur.host_image_mem_Kur H p h2 hq hd c _)

theorem exists_kur_frob_tauEmb_posPl : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ∃ a : MaximalUnramifiedExtension p, (a : ℂ_[p]) = tauEmb D lam (tauPl D z) y ∧ ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y) := by
  intro D p _ lam σ hσ h z y
  have ⟨h2, hq, hd⟩ : p ∉ D.host.small ∧ p ≠ D.host.q ∧ p ≠ D.host.d := by
    rcases h with h | h
    · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
    · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
      exact ⟨k.1, k.2.1, k.2.2.1⟩
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = rhoH D lam (tauPl D z) := ⟨_, rfl⟩
  have hK : ∀ x, ρ x ∈ MaximalUnramifiedExtension p := host_image_mem_Kur_complex D.host p h2 hq hd ρ
  let ρ' : D.host.E →+* MaximalUnramifiedExtension p := ρ.codRestrict (MaximalUnramifiedExtension p) hK
  have hρ' : ∀ x, ((ρ' x : MaximalUnramifiedExtension p) : ℂ_[p]) = ρ x := fun _ => rfl
  let ρ2 : D.host.E →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (σ.comp ρ')
  obtain ⟨g, hg⟩ := exists_aut_of_embeddings ρ ρ2
  have := primeOf_isPrime ρ
  have hL := primeOf_liesOver ρ
  have hc : Nat.card (ℤ ⧸ Ideal.under ℤ (primeOf ρ)) = p := by
    rw [← hL.over, Int.card_ideal_quot]
  have hgF : IsArithFrobAt ℤ g (primeOf ρ) := by
    intro x
    rw [hc, mem_primeOf]
    have hx : ‖ρ' (x : D.host.E)‖ ≤ 1 := norm_int_le ρ x
    have h3 := hσ.2.2.2.2 _ hx
    have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    refine lt_of_le_of_lt ?_ hp1
    refine le_of_eq_of_le ?_ h3
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x - x ^ p)) =
        ((σ (ρ' (x : D.host.E)) - ρ' (x : D.host.E) ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
      have e0 : algebraMap (𝓞 D.host.E) D.host.E ((MulSemiringAction.toAlgHom ℤ (𝓞 D.host.E) g) x) = g (x : D.host.E) := rfl
      rw [map_sub, map_sub, e0, ← hg, map_pow, map_pow]
      rfl
    rw [e1]
    rfl
  obtain ⟨φ, hφ⟩ := (D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).1
  have hgφ : g = φ := by
    have hI := hgF.mul_inv_mem_inertia hφ
    have h1 := ((D.host.der.frob p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ)).2.2.2 (g * φ⁻¹)).1 (fun x => hI x)
    exact mul_inv_eq_one.1 h1
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj])
  refine ⟨ρ' y, ?_, ?_⟩
  · rw [hρ', hρ, ← coe_rhoH]
  · have hplGG : ∀ z : Bool × HH D, plGG D (posPl D p z 1) = plGG D z * D.host.galE φ * D.R.cc := by
      have hC := factClassFrob D.R D.host p (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) (primeOf ρ) φ hφ
      have hc := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
      have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D p := ⟨_, primeOf ρ, inferInstance, inferInstance, φ, hφ, rfl⟩
      obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
      have e1 := (D.host.toHostAx.frob_iff p hc (primeOf ρ) φ).1 hφ
      have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx p _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
      have hH : (D.host.galE φ).2 = D.R.iota (G.hP D p) := by
        unfold Formalism.MainNotions.G.hP
        rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
        exact congrArg Prod.snd (e1.trans e2.symm)
      have hp : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
        rintro ⟨b, t⟩
        cases b <;> rfl
      intro z
      rw [hp, hp]
      refine Prod.ext ?_ ?_
      · rcases h with h | h
        · have h1 := hC.2.2.1 h
          have hs : ¬ IsSg D p := fun hs => by have := h.symm.trans hs; cases this
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, partner, hs]
          cases z.1 <;> simp
        · have h1 := hC.2.1.1 h
          have hp : (partner D p z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
          simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, posPl, hp]
          cases z.1 <;> simp
      · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
        rw [Formalism.HC.Frame.iota_add]
    have hemb : ∀ (g : _ ) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (x : D.host.E), D.host.emb (g * D.host.galE σ) x = D.host.emb g (σ x) := by
      intro g σ x
      have he : D.host.sigmaOf (g * D.host.galE σ) = D.host.sigmaOf g * σ := by
        unfold Host.sigmaOf
        rw [map_mul, MulEquiv.symm_apply_apply]
      change D.host.φ₀ (D.host.sigmaOf (g * D.host.galE σ) x) = D.host.φ₀ ((D.host.sigmaOf g * σ) x)
      rw [he]
    have het : ∀ z : Bool × HH D, embT D (tauPl D z) = D.host.emb (plGG D z) := by
      intro z
      unfold embT tauPl
      rw [Equiv.apply_symm_apply]
    have h4 : rhoH D lam (tauPl D (posPl D p z 1)) (D.host.conj y) = rhoH D lam (tauPl D z) (φ (D.host.conj (D.host.conj y))) := by
      rw [rhoH_apply, rhoH_apply, het, het, hplGG, ← D.host.galE_conjE, hemb, hemb]
    rw [hcc] at h4
    rw [← coe_rhoH, h4, ← hρ, ← hgφ, ← hg]
    rfl

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit

theorem dvd_absNorm_of_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) : p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime ((p : ℤ)) ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← hab]
    refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
    · simpa using h
    · simpa using Ideal.absNorm_mem P.asIdeal
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem intOff_of_val {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (S : Finset ℕ) (x : K)
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    IntOff S (σ x) := by
  have hQ : σ x ∈ TaylorLogMetric.Qbar := by
    rw [TaylorLogMetric.Qbar, mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom
  refine ⟨hQ, fun p hp lam hpS => ?_⟩
  rw [lamC_of_mem lam hQ]
  obtain ⟨M, hM, hint⟩ := exists_coprime_mul_isIntegral hp.out x (h p hp.out hpS)
  have h1 : IsIntegral ℤ ((M : ℂ) * σ x) := by
    have := map_isIntegral_int σ hint
    simpa using this
  have h2 : IsIntegral ℤ ((M : TaylorLogMetric.Qbar) * (⟨σ x, hQ⟩ : TaylorLogMetric.Qbar)) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 (by simpa using h1)
  exact GlobalTheory.HeckeVal.norm_le_one_of_denom lam hM h2

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (z : X.E) (n : X.Tau → ℤ), 0 < M ∧ (∀ τ, (n τ : ℚ) = 2 * e τ) ∧ P.valuation X.E z = P.valuation X.E (k : X.E) ^ M ∧
      (∀ Q : HeightOneSpectrum (𝓞 X.E), Q ≠ P → Q.valuation X.E z = 1) ∧ c ^ (2 * M) = ∏ τ, X.emb τ (z / star z) ^ n τ := by
  classical
  have hg : ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := fun i => by exact_mod_cast (hPr.g_prime i).ne_zero
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E μ (divs ((Pr.g 0 : ℕ) : 𝓞 X.E) ∪ divs ((Pr.g 1 : ℕ) : 𝓞 X.E))
    (productRule μ) (fun v hv => hμ.unr v fun i hi => hv (by
      rw [Finset.mem_union, mem_divs (hg 0), mem_divs (hg 1)]
      fin_cases i
      exacts [Or.inl hi, Or.inr hi])) hμ.tame P k
  obtain ⟨n, hn, hinf⟩ := hμ.inf
  refine ⟨M, z, fun τ => -n τ, hM, fun τ => by push_cast; rw [hn]; ring, h1, h2, σ₀.injective ?_⟩
  have h4 : ((μ.locK P k : ℂˣ) : ℂ) ^ M = (((μ.inf z : ℂˣ) : ℂ))⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val]
  rw [map_pow, hc, mul_comm 2 M, pow_mul, h4, hinf z, ← Finset.prod_inv_distrib, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, ← zpow_neg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  congr 1
  change _ = X.embC σ₀ τ (z / star (z : X.E))
  have h0 : X.embC σ₀ τ (z : X.E) ≠ 0 := by simp
  rw [map_div₀, hconj, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core_of_conj hconj hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem embC_star (t : KerEntTied ex) (τ : t.X.Tau) (x : t.X.E) :
    t.X.embC t.seam.σ₀ τ (star x) = starRingEnd ℂ (t.X.embC t.seam.σ₀ τ x) := by
  change t.seam.σ₀ (t.X.emb τ (star x)) = starRingEnd ℂ (t.seam.σ₀ (t.X.emb τ x))
  rw [t.seam_ok.1, t.seam_ok.1, t.seam_ok.2]
  exact D.host.conjE_apply (TaylorLogMetric.embT D (t.seam.iT τ)) (t.seam.iE x)

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit

theorem muq_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∉ t.Pr.vGs → IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)) ∧ IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hQg i hi P hP
  have hPQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.1 P.2).resolve_left hP
  have hg : ∀ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun k hk =>
    hQg k (t.g_rec k ▸ (t.Q_rec μ (t.Pr.g k)).2 ⟨t.pr_ok.g_prime k, P.1, hPQ, hk⟩)
  have hq := (t.idx_ok μ).muqQ i hi P hP
  have key : ∀ p : ℕ, p.Prime → p ∉ (t.O u μ).S → ∀ w : HeightOneSpectrum (𝓞 t.X.K), ((p : ℕ) : 𝓞 t.X.K) ∈ w.asIdeal →
      w.valuation t.X.K ((t.cst μ).muq (i + 1) P) = 1 := by
    intro p hp hpS w hw
    have hpP : ((p : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun h =>
      hpS ((sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P).2 p hp (dvd_absNorm_of_mem P.1 hp h))
    obtain ⟨e, he⟩ := hmu ⟨i, hi⟩
    have hm := mu_unit_of_conj (embC_star t) t.pr_ok he (Formalism.L2.Host.unif P.1) (hval ⟨i, hi⟩ P.1 hg) hpP hw
    have htw := (GlobalTheory.ColPeriod.twistUnit t.X.F t.X.E t.X.K t.S (t.tup μ) P.1 w).2
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hm, htw]
    simp
  refine ⟨intOff_of_val _ _ _ fun p hp hpS w hw => (key p hp hpS w hw).le, ?_⟩
  have h2 := intOff_of_val t.seam.σ₀ (t.O u μ).S ((t.cst μ).muq (i + 1) P)⁻¹ fun p hp hpS w hw => by
    rw [map_inv₀, key p hp hpS w hw, inv_one]
  exact h2

end GlobalTheory.KerTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertLoc

open GlobalTheory.SplitScalar GlobalTheory.FinWeilO


set_option maxHeartbeats 800000 in
theorem exists_locPair : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → ∀ e, IsPrimeIdem P e e → ∃ (ϖ : P.adicCompletion D.host.E) (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (q : ℕ) (δ : P.adicCompletion D.host.E) (JS : GL (Fin S.rank) (P.adicCompletion D.host.E)) (JT : GL (Fin T.rank) (P.adicCompletion D.host.E)) (ψ' : AddChar (P.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) × Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* Module.End ℂ M) (ιS : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) →* GA D S) (ιT : Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* GA D T), LocPair ϖ σ q δ JS JT ψ' ρ ω ∧ (∀ g, g ∈ ιS.range ↔ SuppF S e g) ∧ (∀ g, g ∈ ιT.range ↔ SuppF T e g) ∧ (∀ g, ιS g ∈ hyp S P ↔ (g : GL (Fin S.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin S.rank) (Formalism.UG.intL _)) ∧ (∀ g, ιT g ∈ hyp T P ↔ (g : GL (Fin T.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin T.rank) (Formalism.UG.intL _)) ∧ (∀ g h (m : M), ((ω (g, h) m : M) : WO S T → ℂ) = om (ιS g, ιT h) m) ∧ (∀ f, IsVacAt ψ S T P f → f ∈ M) ∧ ∀ m : M, LocVac ρ m ↔ IsVacAt ψ S T P m := by
  intro D ψ S T χS χT om P hW hP hfix e he
  obtain ⟨ϖ, σ, q, π, hU, h2, h, hV⟩ := exists_chart hP he
  obtain ⟨βS, ιS, hS, gS⟩ := hV S
  obtain ⟨βT, ιT, hT, gT⟩ := hV T
  obtain ⟨c, hc⟩ := exists_isGen D P
  have hψ := hW.std
  obtain ⟨δ, ψ', hδ, p1, p2, p3⟩ := exists_delta_psi hU h2 (th ψ h c) (th_conj h hU.1) (by
    obtain ⟨β, -, hβ, -⟩ := hV D.sp.X'
    refine th_cond hψ h hU.2.1 hβ ⟨0, ?_⟩ hc
    have h1 := D.R.m_add_three_le_k
    rw [D.sp.X'_rank, Ranks.rankX', Ranks.r]
    omega)
  let ρ : Matrix (Fin T.rank) (Fin S.rank) (LP D P) → Module.End ℂ (thetaSub ψ S T) := fun x =>
    (heisL ψ S T (kap h βS βT c x)).restrict fun _ hf =>
      GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (h.half_fin (kap_half h x)) hf
  have hρ : ∀ x (m : thetaSub ψ S T), (ρ x m : WO S T → ℂ) = heisO ψ S T (kap h βS βT c x) m := fun _ _ => rfl
  let ω : Formalism.UG.UJ σ (1 : Matrix (Fin S.rank) (Fin S.rank) (LP D P)) ×
      Formalism.UG.UJ σ (1 : Matrix (Fin T.rank) (Fin T.rank) (LP D P)) →* Module.End ℂ (thetaSub ψ S T) :=
    { toFun := fun p => (om (ιS p.1, ιT p.2)).restrict fun _ hf => hW.om_pres _ _ hf
      map_one' := LinearMap.ext fun m => Subtype.ext (by
        show om (ιS 1, ιT 1) m = m
        rw [map_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply])
      map_mul' := fun p p' => LinearMap.ext fun m => Subtype.ext (by
        show om (ιS (p.1 * p'.1), ιT (p.2 * p'.2)) m = om (ιS p.1, ιT p.2) (om (ιS p'.1, ιT p'.2) m)
        rw [map_mul, map_mul, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]) }
  have hω : ∀ g k (m : thetaSub ψ S T), (ω (g, k) m : WO S T → ℂ) = om (ιS g, ιT k) m := fun _ _ _ => rfl
  have hlat := kap_mem_iff h hU.2.1 hS hT hc
  have hvac0 : ∀ m : thetaSub ψ S T, LocVac ρ m ↔
      ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u → heisO ψ S T u m = m := fun m => by
    refine ⟨fun hm u hu hh => ?_, fun hm x hx => Subtype.ext (hm _ ((hlat x).2 hx) (kap_half h x))⟩
    obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
    exact congrArg Subtype.val (hm x ((hlat x).1 hu))
  have hvac : ∀ m : thetaSub ψ S T, LocVac ρ m ↔ IsVacAt ψ S T P m := fun m => by
    rw [hvac0]
    refine ⟨fun hm => ⟨m.2, fun e' f' he' u hu hh => hm u hu ?_⟩, fun hm u hu hh => hm.2 e e he u hu (Or.inl hh)⟩
    obtain ⟨rfl, -⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e e he).2.2.2.1 e' f' he'
    rwa [h.1.2.1, or_self] at hh
  have hhyp : ∀ {V : HSp D} {β ι}, GrpChart V e σ π β ι → ∀ g, ι g ∈ hyp V P ↔
      g.1 ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.intL (LP D P)) := fun hι g =>
    ⟨fun hg => (hι.2.2.2 g).1 hg.1, fun hg => ⟨(hι.2.2.2 g).2 hg, e, e, he, hι.1 g⟩⟩
  have hone : ∀ (n : ℕ) (i j : Fin n), σ ((1 : Matrix (Fin n) (Fin n) (LP D P)) i j) = (1 : Matrix (Fin n) (Fin n) (LP D P)) j i :=
    fun n i j => by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, σ.map_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), σ.map_zero]
  refine ⟨ϖ, σ, q, δ, 1, 1, ψ', thetaSub ψ S T, ρ, ω, ιS, ιT,
    ⟨hU, odd_of_v_two hU h2, one_mem _, one_mem _, hone _, hone _, hδ, p1, p2, ?_, fun x y => ?_, ?_, fun g k x => ?_,
      fun g k hg hk s hs => ?_⟩,
    fun g => ⟨?_, gS.2.2.1 g⟩, fun g => ⟨?_, gT.2.2.1 g⟩, hhyp gS, hhyp gT, hω, fun f hf => hf.1, hvac⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [hρ, kap_zero, heisO_zero, Module.End.one_apply]
  · refine LinearMap.ext fun m => Subtype.ext ?_
    rw [Module.End.mul_apply, hρ, hρ, heisO_heisO, symplOH_kap h hS hT, LinearMap.smul_apply, Submodule.coe_smul, hρ, kap_add,
      locH, p3, inv_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  · refine span_vacua hψ h.1.1 h.1.2.1 (fun u hu hh => ?_) _ fun u hh s m hs hm => ?_
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      refine ⟨kap h βS βT c ((2⁻¹ : LP D P) • x), (hlat _).2 fun i j => mul_mem (mem_intL.2 ?_) ((hlat x).1 hu i j), ?_⟩
      · rw [map_inv₀, h2, inv_one]
      · rw [← kap_add, half_add_half]
    · obtain ⟨x, rfl⟩ := kap_surj (βS := βS) (βT := βT) h hc.1 hh
      exact Submodule.subset_span ⟨x, s, (hvac0 s).2 hs, Subtype.ext hm⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    show om (ιS g, ιT k) (heisO ψ S T (kap h βS βT c x) m) = heisO ψ S T (kap h βS βT c _) (om (ιS g, ιT k) m)
    rw [hW.om_heis _ _ _ _ m.2, actO_kap h gS gT]
  · exact Subtype.ext (hfix _ ((hvac s).1 hs) _ ((hhyp gS g).2 hg) _ ((hhyp gT k).2 hk))
  · rintro ⟨g, rfl⟩; exact gS.1 g
  · rintro ⟨g, rfl⟩; exact gT.1 g

end GlobalTheory.InertLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnramifiedLocalPairOfInertWeilDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramifiedLocalPair_of_inertWeilDatum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P = P → VacFix ψ om P → ∀ e, IsPrimeIdem P e e → ∃ (ϖ : P.adicCompletion D.host.E) (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (q : ℕ) (δ : P.adicCompletion D.host.E) (JS : GL (Fin S.rank) (P.adicCompletion D.host.E)) (JT : GL (Fin T.rank) (P.adicCompletion D.host.E)) (ψ' : AddChar (P.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (P.adicCompletion D.host.E) → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) × Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* Module.End ℂ M) (ιS : Formalism.UG.UJ σ (JS : Matrix (Fin S.rank) (Fin S.rank) (P.adicCompletion D.host.E)) →* GA D S) (ιT : Formalism.UG.UJ σ (JT : Matrix (Fin T.rank) (Fin T.rank) (P.adicCompletion D.host.E)) →* GA D T), LocPair ϖ σ q δ JS JT ψ' ρ ω ∧ (∀ g, g ∈ ιS.range ↔ SuppF S e g) ∧ (∀ g, g ∈ ιT.range ↔ SuppF T e g) ∧ (∀ g, ιS g ∈ hyp S P ↔ (g : GL (Fin S.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin S.rank) (Formalism.UG.intL _)) ∧ (∀ g, ιT g ∈ hyp T P ↔ (g : GL (Fin T.rank) (P.adicCompletion D.host.E)) ∈ Formalism.UG.GLint (Fin T.rank) (Formalism.UG.intL _)) ∧ (∀ g h (m : M), ((ω (g, h) m : M) : WO S T → ℂ) = om (ιS g, ιT h) m) ∧ (∀ f, IsVacAt ψ S T P f → f ∈ M) ∧ ∀ m : M, LocVac ρ m ↔ IsVacAt ψ S T P m := by
  first | exact @GlobalTheory.InertLoc.exists_locPair | exact GlobalTheory.InertLoc.exists_locPair | (intros; apply GlobalTheory.InertLoc.exists_locPair <;> assumption)
end
end
