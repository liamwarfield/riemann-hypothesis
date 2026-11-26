module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.TargetsCurveVertPointLength
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineSection
public import Development.WeilBound.CoreStatements.FlagImmersions.ExistsResDegree
public import Development.WeilBound.CoreStatements.FlagImmersions.ValNeOfIntegral
public import Development.WeilBound.CoreStatements.FlagImmersions.VertCloseStep
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HasReferenceOfSandwichAllPrimes
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM1Nef
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersProjectionFormulaDegree

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatible
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem pb_indep_cover : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  intro II hII K _ ι _ D σ _ S P Re K' _ ι' _ Ω _ _ y S' Re' κ v hbl hP hpull hdeg
  have hr0 : IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) ≠ 0 := by
    intro h
    have hd := Re'.deg_pos
    rw [hdeg, h, zero_mul] at hd
    exact lt_irrefl 0 hd
  have hr : ((IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hr0
  have harith : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (imageZ v (mCoordIdeal y)) (D + 1) := by
    rw [hP]
    exact Re.arith
  have key : ∀ w : Fin (D + 1) → σ, Re'.limNum II w = Re.limNum II w := by
    intro w
    have ht0 : 0 < S.t₀ := (S.reg (w 0)).1
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ S.t₀ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with t ht using ht.2.le
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have heq : (fun t => Re'.num II t w) =ᶠ[𝓝[>] (0 : ℝ)] (fun t => Re.num II t w) := by
      filter_upwards [hpull, hle, hpos] with t hpt hle' hpos'
      have hPF := hII.2.2.1 K ι K' ι' κ v Ω y (D + 1) (fun j => Re.line (w j) t)
        (fun j => Re'.line (w j) t) hbl Re'.arith harith
        (fun j => Re.line_smooth (w j) t hpos' hle') (fun j => hpt (w j))
      rw [hP] at hPF
      show (II K' ι' (mCoordIdeal y) (D + 1) fun j => Re'.line (w j) t) / (Re'.deg : ℝ)
        = (II K ι P (D + 1) fun j => Re.line (w j) t) / (Re.deg : ℝ)
      rw [hPF, hdeg]
      push_cast
      exact mul_div_mul_left _ _ hr
    unfold Realis.limNum Filter.limUnder
    rw [Filter.map_congr heq]
  unfold Realis.PB
  rw [show Re'.limNum II = Re.limNum II from funext key]

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPullbackCompatibleStatement
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_pullback_compatible : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k', ι' k') → Ω) (S' : AnSys D σ) (Re' : Realis S' (mCoordIdeal y)) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')), IsBlockMap κ v → imageZ v (mCoordIdeal y) = P → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ a, IsPullHerm κ v (Re.line a t) (Re'.line a t)) → Re'.deg = IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) * Re.deg → Re'.PB II = Re.PB II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | exact GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.pb_indep_cover <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.GeoNumOneLinear
noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter.PointVertical

theorem image_dim_le_one {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {F : Type} [Field F]
    {V : Ideal (MRingOver F ι')} (hV : IsProjVarF V 1) {e : ℕ} (he : IsProjVarF (imageVar F v V) e) : e ≤ 1 := by
  classical
  have h1 : FieldNumbers.relDim V = ((1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.relDim_eq_iff_hasRelDim V 1).mpr hV.2
  have h2 : FieldNumbers.relDim (FieldNumbers.contractPrime (Targets.ProjContract.emb hv) V) =
      ((e : ℕ) : WithBot (WithTop ℤ)) := by
    refine (FieldNumbers.relDim_eq_iff_hasRelDim _ e).mpr ?_
    show ringKrullDim _ = _
    rw [← Targets.ProjContract.ringKrullDim_imageVar hv]
    exact he.2
  have h3 := FieldNumbers.ContractRelDimLe.proof F K K' (Targets.ProjContract.emb hv) ι' V
    ((Bridge.isMultiProjPrime_iff V).mpr hV.1)
  rw [h1, h2] at h3
  exact_mod_cast h3

theorem geoNum_one_linear {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)) :
    ∃ w : K → ℤ, (∀ k, 0 ≤ w k) ∧ ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * w k := by
  by_cases h : IsRelevant W
  · refine ⟨fun k => ∑ᶠ V ∈ divSupp W (X ⟨k, (h k).choose⟩),
      (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) V : ℤ) * geoNum 0 V Fin.elim0, fun k => ?_, fun a => ?_⟩
    · refine finsum_nonneg fun V => finsum_nonneg fun _ => mul_nonneg (Int.natCast_nonneg _) ?_
      unfold geoNum
      split_ifs
      · exact Int.natCast_nonneg _
      · exact le_rfl
    · rw [geoNum, dite_eq_left h]
      rfl
  · refine ⟨0, fun _ => le_rfl, fun a => ?_⟩
    rw [geoNum, dite_eq_right h]
    simp

end SlopeTestRemainingChoices


open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter.PointVertical in
theorem nefAt_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {P : Ideal (MRing ι)}
    {P' : Ideal (MRing ι')} (hP : P ≤ imageZ v P') {p : ℕ} (hp : p.Prime) {a : K → ℤ} (h : PB.NefAt P p a) :
    PB.NefAt P' p (pullDeg κ a) := by
  intro W hWm hPW hch hWd
  have : Fact p.Prime := ⟨hp⟩
  have hpW : ((p : ℕ) : MRing ι') ∈ W := hch ▸ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.natCast_mem_of_charOf W
  have hWp : IsProjVarF (W.map (red p)) 1 :=
    ⟨isMultiProjPrime_red p hWm hpW, by rw [ringKrullDim_red p hpW, hWd]⟩
  have hImm : IsMultiProjPrime (imageZ v W) := isMultiProjPrime_imageZ hv hWm
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W := by
    show rename v ((p : ℕ) : MRing ι) ∈ W
    simpa using hpW
  have hVm := isMultiProjPrime_red p hImm hpI
  obtain ⟨D, hKD, hD⟩ := exists_dim_F p _ hVm
  have hVi : IsProjVarF (imageVar (ZMod p) v (W.map (red p))) (D - Fintype.card K) := by
    rw [imageVar_red p v hpW]
    refine ⟨hVm, ?_⟩
    rw [hD, Nat.sub_add_cancel hKD]
  have hle := image_dim_le_one hv hWp hVi
  obtain ⟨I', hI', -⟩ := Targets.ExistsUnique.full (ZMod p) ι'
  obtain ⟨I, hI, -⟩ := Targets.ExistsUnique.full (ZMod p) ι
  rw [geoNumStatement ι' p I' hI' W 1 _ hWm hpW hWp]
  rcases hle.lt_or_eq with hlt | heq
  · exact (Targets.ProjContract.full (ZMod p) K ι K' ι' I' hI' κ v _ 1 _ (fun _ => a) hv hWp hVi hlt).ge
  · rw [heq] at hVi
    choose i' hi' using hWp.1.2.2
    rw [Targets.ProjDeg.of_found AutoClose.FieldNumbers_ProjectionFormulaDegree Targets.FnDegRelDeg.proof (ZMod p) ι ι'
      I I' hI hI' κ v _ 1 (fun _ => a) i' hv hWp hVi hi']
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    rw [imageVar_red p v hpW] at hVi ⊢
    rw [← geoNumStatement ι p I hI (imageZ v W) 1 _ hImm hpI hVi]
    refine h _ hImm (hP.trans (Ideal.comap_mono hPW)) ?_ ?_
    · rw [← hch]
      have e : (imageZ v W).comap (C : ℤ →+* MRing ι) = W.comap (C : ℤ →+* MRing ι') := by
        ext n
        show rename v (C n) ∈ W ↔ C n ∈ W
        rw [rename_C]
      exact congrArg (fun J : Ideal ℤ => (Submodule.IsPrincipal.generator J).natAbs) e
    · rw [← ringKrullDim_red p hpI]
      exact hVi.2

theorem nefAt_of_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℕ)
    {a : K → ℤ} (ha : ∀ k, 0 ≤ a k) : PB.NefAt P p a := by
  intro W _ _ _ _
  obtain ⟨w, hw, e⟩ := geoNum_one_linear W
  rw [e]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hw k)

theorem nefAt_add {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {p : ℕ}
    {a b : K → ℤ} (ha : PB.NefAt P p a) (hb : PB.NefAt P p b) : PB.NefAt P p (a + b) := by
  intro W h1 h2 h3 h4
  have ha' := ha W h1 h2 h3 h4
  have hb' := hb W h1 h2 h3 h4
  obtain ⟨w, -, e⟩ := geoNum_one_linear W
  rw [e] at ha' hb' ⊢
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact add_nonneg ha' hb'

theorem nefAt_step {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (p : ℕ)
    (h : ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0) (τ : Ψ) (i : Fin N) :
    PB.NefAt M.P p (-∑ k ∈ Finset.Iic i, M.xdeg (τ, k)) := by
  intro W h1 h2 h3 h4
  let mu : Top.Wt Ψ N := fun σ k => if σ = τ ∧ k ≤ i then 1 else 0
  have hmu : Top.Dominant mu := by
    intro σ a b hab
    simp only [mu]
    split_ifs with c1 c2
    · exact le_rfl
    · exact absurd ⟨c1.1, hab.trans c1.2⟩ c2
    · exact zero_le_one
    · exact le_rfl
  have key := h mu hmu W ⟨h1, h2, h3, h4⟩
  obtain ⟨w, -, e⟩ := geoNum_one_linear W
  unfold Top.RootModel.curveDeg at key
  rw [Fintype.sum_option, Fintype.sum_prod_type] at key
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg] at key
  rw [Finset.sum_eq_single τ (fun σ _ hσ => by simp [mu, hσ]) (by simp)] at key
  have e2 : ∑ k : Fin N, -mu τ k * (geoNum 1 W (fun _ => M.xdeg (τ, k)) : ℝ) =
      ((-∑ k ∈ Finset.Iic i, geoNum 1 W (fun _ => M.xdeg (τ, k)) : ℤ) : ℝ) := by
    push_cast
    rw [← Finset.sum_neg_distrib, ← Finset.sum_subset (Finset.subset_univ (Finset.Iic i))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [mu, Finset.mem_Iic.1 hk]
    · intro k _ hk
      have : ¬ k ≤ i := fun c => hk (Finset.mem_Iic.2 c)
      simp [mu, this]
  rw [e2] at key
  have key' : 0 ≤ -∑ k ∈ Finset.Iic i, geoNum 1 W (fun _ => M.xdeg (τ, k)) := by exact_mod_cast key
  simp only [e] at key' ⊢
  convert key' using 1
  simp only [Pi.neg_apply, Finset.sum_apply, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

end RootFieldNumerics.Ref
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.InvNatCastMem
noncomputable section

namespace RootFieldNumerics.Ref

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Proj

open GlobalTheory.CompanionTheory.Ar.OrVert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_proj (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ)
    (hq : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) (hd : ((discr E : ℤ) : Ω)⁻¹ ∈ regAt 𝔐.ξ q) :
    ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = v) ∧ (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧
      ∀ e ∈ 𝔐.V s q, e ∈ 𝔐.M.lat q := by
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  obtain ⟨n, a, cc, hsum, heq⟩ := ScaledCasimir.exists_scaledCasimir E
  have hV : 𝔐.V s q = 𝔐.dR s q := Lat.patch_of_not S _ _ hq
  have hd0 : ((discr E : ℤ) : Ω) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
  have hσd : 𝔐.emb s (∑ m, cc m * a m) = ((discr E : ℤ) : Ω) := by rw [hsum, map_intCast]
  have mem_iff : ∀ x : 𝔐.Li, x ∈ eigSp 𝔐.ρ (𝔐.emb s) ↔ ∀ b, 𝔐.ρ b x = 𝔐.emb s b • x := fun x => by
    simp [eigSp, sub_eq_zero]
  let T : Module.End Ω 𝔐.Li := ((discr E : ℤ) : Ω)⁻¹ • ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m)
  have hT : ∀ x, T x = ((discr E : ℤ) : Ω)⁻¹ • ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m) x := fun x => by
    simp [T, LinearMap.sum_apply]
  refine ⟨T, fun v hv => ?_, fun e he => ?_, fun e he => ?_⟩
  · have h1 : ∑ m, 𝔐.emb s (cc m) • 𝔐.ρ (a m) v = 𝔐.emb s (∑ m, cc m * a m) • v := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [(mem_iff v).1 hv, smul_smul, map_sum, map_mul, Finset.sum_smul]
    rw [hT, h1, hσd, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  · rw [hV]
    refine ⟨?_, ?_⟩
    · rw [hT]
      refine (𝔐.M.lat q).smul_mem ⟨_, hd⟩ (Submodule.sum_mem _ fun m _ => ?_)
      exact (𝔐.M.lat q).smul_mem ⟨_, Sandwich.emb_mem 𝔐 s q (cc m)⟩ (Sandwich.lat_act 𝔐 q _ e he)
    · show T e ∈ eigSp 𝔐.ρ (𝔐.emb s)
      refine (mem_iff _).2 fun b => ?_
      rw [hT, map_smul, heq Ω 𝔐.Li 𝔐.ρ (𝔐.emb s) b e, smul_comm]
  · rw [hV] at he
    exact he.1

end Proj

theorem exists_dual {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b : Fin r → V}
    (hb : LinearIndependent Ω b) : ∃ φ : Fin r → Module.Dual Ω V, ∀ a j, φ a (b j) = if a = j then 1 else 0 := by
  have h := fun a : Fin r => LinearMap.exists_extend ((Finsupp.lapply a).comp hb.repr)
  choose φ hφ using h
  refine ⟨φ, fun a j => ?_⟩
  have h1 := congrArg (fun f => f ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩) (hφ a)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.lapply_apply] at h1
  rw [h1, hb.repr_eq_single j _ rfl, Finsupp.single_apply]
  simp [eq_comm]

theorem dual_mem {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ} {b : Fin r → V} (A : Subring Ω)
    (φ : Module.Dual Ω V) (hφ : ∀ j, φ (b j) ∈ A) {x : V} (hx : x ∈ Submodule.span A (Set.range b)) : φ x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact hφ j
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a x _ hx =>
    rw [Subring.smul_def, map_smul, smul_eq_mul]
    exact mul_mem a.2 hx

theorem ratio_mem {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {A A₀ t t₀ : Ω} {n : ℤ} (hn : n = 1 ∨ n = -1)
    (n1 : A / t ^ n ≠ 0) (n0 : A₀ / t₀ ^ n ≠ 0) (v1 : A / t ^ n ∈ W) (v2 : (A / t ^ n)⁻¹ ∈ W)
    (v3 : A₀ / t₀ ^ n ∈ W) (v4 : (A₀ / t₀ ^ n)⁻¹ ∈ W) (x1 : t₀ / t ∈ W) (x2 : t / t₀ ∈ W) :
    A₀ / A ∈ W ∧ A / A₀ ∈ W := by
  rcases hn with rfl | rfl
  · simp only [zpow_one] at v1 v2 v3 v4 n1 n0
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : A₀ ≠ 0 := fun h => n0 (by simp [h])
    have t1 : t₀ ≠ 0 := fun h => n0 (by simp [h])
    constructor
    · have e : A₀ / A = (A₀ / t₀) * (A / t)⁻¹ * (t₀ / t) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x1
    · have e : A / A₀ = (A / t) * (A₀ / t₀)⁻¹ * (t / t₀) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x2
  · simp only [zpow_neg_one] at v1 v2 v3 v4 n1 n0
    have a0 : A ≠ 0 := fun h => n1 (by simp [h])
    have t0 : t ≠ 0 := fun h => n1 (by simp [h])
    have a1 : A₀ ≠ 0 := fun h => n0 (by simp [h])
    have t1 : t₀ ≠ 0 := fun h => n0 (by simp [h])
    constructor
    · have e : A₀ / A = (A₀ / t₀⁻¹) * (A / t⁻¹)⁻¹ * (t / t₀) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v3 v2) x2
    · have e : A / A₀ = (A / t⁻¹) * (A₀ / t₀⁻¹)⁻¹ * (t₀ / t) := by field_simp
      rw [e]
      exact mul_mem (mul_mem v1 v4) x1

theorem inv_natCast_mem {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → (p : Ω)⁻¹ ∈ W) : (n : Ω)⁻¹ ∈ W := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul, mul_inv]
    exact mul_mem (ha fun p hp hd => h p hp (hd.mul_right b)) (hb fun p hp hd => h p hp (hd.mul_left a))

theorem inv_mem_of_ne {Ω : Type} [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (h : (p : Ω)⁻¹ ∉ W) : (r : Ω)⁻¹ ∈ W := by
  by_contra h'
  have key : ∀ n : ℕ, n ≠ 0 → (n : Ω)⁻¹ ∉ W → W.valuation (n : Ω) < 1 := by
    intro n hn hW
    have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
    by_contra hlt
    apply hW
    rw [← W.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ (not_lt.1 hlt)
  have h1 := key p hp.ne_zero h
  have h2 := key r hr.ne_zero h'
  have hco : IsCoprime (p : ℤ) (r : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hr).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  have e : (a : Ω) * p + b * r = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have ha : W.valuation (a : Ω) ≤ 1 := (W.valuation_le_one_iff _).2 (intCast_mem W a)
  have hb : W.valuation (b : Ω) ≤ 1 := (W.valuation_le_one_iff _).2 (intCast_mem W b)
  have h3 : W.valuation ((a : Ω) * p + b * r) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le h1
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le h2
  rw [e, map_one] at h3
  exact lt_irrefl _ h3

theorem exists_split (S : Finset ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ a b : ℕ, m = a * b ∧ (∀ p : ℕ, p.Prime → p ∣ a → p ∈ S) ∧ ∀ p : ℕ, p.Prime → p ∣ b → p ∉ S := by
  induction m using Nat.recOnMul with
  | zero => omega
  | one => exact ⟨1, 1, rfl, fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one,
      fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one⟩
  | prime r hr =>
    by_cases h : r ∈ S
    · exact ⟨r, 1, (mul_one r).symm, fun p hp hd => ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd) ▸ h,
        fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one⟩
    · exact ⟨1, r, (one_mul r).symm, fun p hp h => absurd (Nat.dvd_one.1 h) hp.ne_one,
        fun p hp hd => ((Nat.prime_dvd_prime_iff_eq hp hr).1 hd) ▸ h⟩
  | mul x y hx hy =>
    obtain ⟨a, b, e, h1, h2⟩ := hx (Nat.pos_of_mul_pos_right hm)
    obtain ⟨a', b', e', h1', h2'⟩ := hy (Nat.pos_of_mul_pos_left hm)
    refine ⟨a * a', b * b', by rw [e, e']; ring, fun p hp hd => ?_, fun p hp hd => ?_⟩
    · exact ((Nat.Prime.dvd_mul hp).1 hd).elim (h1 p hp) (h1' p hp)
    · exact ((Nat.Prime.dvd_mul hp).1 hd).elim (h2 p hp) (h2' p hp)


open GlobalTheory.CompanionTheory.Ar.OrVert Top HodgeCpt in
set_option maxHeartbeats 1000000 in
theorem unit_off (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx)
    (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx)
    (i : R.Ω →+* M.Ω) (hi : i.comp o₀.g = o.g) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S)
    (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω)
    (h1 : ∀ k, M.y ⟨k, cM k⟩ ≠ 0) (h2 : ∀ k, R.y ⟨k, cR k⟩ ≠ 0) (h3 : ∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W)
    (h4 : ∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) (hS : ∀ p ∈ S, (p : M.Ω)⁻¹ ∈ W) :
    i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) / ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) ∈ W ∧
      ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) / i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) ∈ W := by
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  haveI : CharZero R.Ω := Sandwich.charZero_of_hodgeCpt o₀.𝔐
  obtain ⟨q, hqc, hq⟩ := GlobalTheory.T.valuation_ring_centre_in_chart M.K M.ι M.Ω M.Ω M.y o.𝔐.X o.𝔐.ξ o.𝔐.all o.𝔐.tie (RingHom.id _) W cM h1 h3
  obtain ⟨q₀, hqc₀, hq₀⟩ := GlobalTheory.T.valuation_ring_centre_in_chart R.K R.ι R.Ω M.Ω R.y o₀.𝔐.X o₀.𝔐.ξ o₀.𝔐.all o₀.𝔐.tie i W cR h2 h4
  have hξ : o.𝔐.ξ ≫ o.𝔐.f = spMap i ≫ o₀.𝔐.ξ ≫ o₀.𝔐.f := by
    rw [o.g_over, o₀.g_over, ← hi, OrVert.spMap_comp', Category.assoc]
  have hy := GlobalTheory.T.hodge_comp_compare_generic E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 i hξ W q q₀ hq hq₀
  obtain ⟨ι, hext, hspan, hpt, hW⟩ :=
    GlobalTheory.T.hodge_comp_compare_flag E H D l Xo c Y S ∅ M.Ω R.Ω M.K R.K M.ι R.ι M.y R.y o.𝔐 o₀.𝔐 o₀.Fl i hξ
  have hsl := hext.1
  have hspanW := hW W.toSubring q q₀ hq.1 hq₀.1 hy
  have hFl : ∀ s j, o.Fl.b s j = ι (o₀.Fl.b s j) := fun s j => (hpt _ _).1 (by
    rw [o.g_flag, o₀.g_flag, ← hi, OrVert.dualMap_comp', OrVert.spMap_comp', Category.assoc])
  have hWq : ∀ a ∈ regAt o.𝔐.ξ q, a ∈ W := hq.1
  have hdW : ((discr E : ℤ) : M.Ω)⁻¹ ∈ W := by
    have h := inv_natCast_mem W (discr E).natAbs fun p hp hd => hS p (hdisc p hp (Int.natCast_dvd.2 hd))
    rcases Int.natAbs_eq (discr E) with e | e
    · rw [e, Int.cast_natCast]; exact h
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact neg_mem h
  have hdq : ((discr E : ℤ) : M.Ω)⁻¹ ∈ regAt o.𝔐.ξ q :=
    hq.2 _ (intCast_mem _ _) (Int.cast_ne_zero.2 (discr_ne_zero E)) hdW
  have hdq₀ : ((discr E : ℤ) : R.Ω)⁻¹ ∈ regAt o₀.𝔐.ξ q₀ :=
    hq₀.2 _ (intCast_mem _ _) (Int.cast_ne_zero.2 (discr_ne_zero E)) (by rw [map_intCast]; exact hdW)
  have hfib : ∀ p ∈ S, ¬ InFibre o.𝔐.ξ p q := fun p hp hin => by
    have hp0 : (p : M.Ω) ≠ 0 := Nat.cast_ne_zero.2 (o.𝔐.S_prime p hp).ne_zero
    exact hin ⟨hp0, natCast_mem _ p, hq.2 _ (natCast_mem _ p) hp0 (hS p hp)⟩
  have key : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk D s)), ∃ (b : Fin (labelRk D s) → o.𝔐.Li)
      (b₀ : Fin (labelRk D s) → o₀.𝔐.Li) (t : M.Ω) (t₀ : R.Ω),
      (∀ j, flagStep M.Ω b j = flagStep M.Ω (o.Fl.b s) j) ∧ (o.𝔐.V s).IsFrameAt b q ∧
      (∀ j, flagStep R.Ω b₀ j = flagStep R.Ω (o₀.Fl.b s) j) ∧ (o₀.𝔐.V s).IsFrameAt b₀ q₀ ∧
      b k - t • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k ∧ b₀ k - t₀ • o₀.Fl.b s k ∈ flagStep R.Ω (o₀.Fl.b s) k ∧
      i t₀ / t ∈ W ∧ t / i t₀ ∈ W := by
    intro s k
    obtain ⟨T, hTe, hTq, hVl⟩ := exists_proj o.𝔐 s q hfib hdq
    obtain ⟨T₀, hTe₀, hTq₀, hVl₀⟩ := exists_proj o₀.𝔐 s q₀ (fun p hp => absurd hp (Finset.notMem_empty p)) hdq₀
    obtain ⟨U₀, hU₀, b₀, hf₀, hfr₀⟩ := o₀.Fl.sub s q₀ (Set.mem_univ _)
    have hfr₀ := hfr₀ q₀ (Set.mem_univ _) hU₀
    obtain ⟨U, hU, b, hf, hfr⟩ := o.Fl.sub s q (Set.mem_univ _)
    have hfr := hfr q (Set.mem_univ _) hU
    obtain ⟨φ, hφ⟩ := exists_dual hfr₀.1
    have hbe₀ : ∀ j, b₀ j ∈ eigSp o₀.𝔐.ρ (o₀.𝔐.emb s) := fun j =>
      flag_mem_eig o₀.𝔐 o₀.Fl s (hf₀ _ ▸ top_flag b₀ j)
    have hbF : o.Fl.b s = fun a => ι (o₀.Fl.b s a) := funext (hFl s)
    have hf' : ∀ j, flagStep M.Ω (fun a => ι (b₀ a)) j = flagStep M.Ω (o.Fl.b s) j := by
      intro j
      rw [hbF]
      exact flagStep_map_eq hsl _ _ j (hf₀ j)
    have hbe : ∀ j, ι (b₀ j) ∈ eigSp o.𝔐.ρ (o.𝔐.emb s) := fun j =>
      flag_mem_eig o.𝔐 o.Fl s (hf' _ ▸ top_flag (fun a => ι (b₀ a)) j)
    have hbin : ∀ j, b j ∈ Submodule.span M.Ω (Set.range fun a => ι (b₀ a)) := fun j =>
      mem_span_of_flag _ (labelRk D s) (by rw [hf', ← hf]; exact top_flag b j)
    obtain ⟨C1, C2⟩ := GlobalTheory.T.lattice_span_projection_bound M.Ω R.Ω i _ _ ι hext hspan W.toSubring (o₀.𝔐.M.lat q₀ : Set o₀.𝔐.Li)
      (o.𝔐.M.lat q : Set o.𝔐.Li) _ b b₀ (fun a => (φ a).comp T₀) T 1 1 1 hspanW
      (fun e he => by
        have h := hTq e he
        rw [hfr.2] at h
        exact span_mono_ring hWq h)
      (fun j => by rw [one_smul]; exact hTe _ (hbe j))
      (fun j => by
        rw [one_smul]
        exact hVl₀ _ (by rw [hfr₀.2]; exact Submodule.subset_span ⟨j, rfl⟩))
      (fun a j => by rw [LinearMap.comp_apply, hTe₀ _ (hbe₀ j), hφ])
      (fun a e he => by
        rw [one_mul]
        refine hq₀.1 _ ?_
        have h := hTq₀ e he
        rw [hfr₀.2] at h
        refine dual_mem _ (φ a) (fun j => ?_) h
        rw [hφ]
        split_ifs
        · exact one_mem _
        · exact zero_mem _)
      (fun j => by
        rw [one_smul]
        exact hVl _ (by rw [hfr.2]; exact Submodule.subset_span ⟨j, rfl⟩)) hbin
    obtain ⟨t, ht⟩ := flag_coef b (o.Fl.b s) hf k
    obtain ⟨t₀, ht₀⟩ := flag_coef b₀ (o₀.Fl.b s) hf₀ k
    have ht' : ι (b₀ k) - i t₀ • o.Fl.b s k ∈ flagStep M.Ω (o.Fl.b s) k := by
      have h := mem_flagStep_map hsl (o₀.Fl.b s) k ht₀
      rw [map_sub, hsl] at h
      rw [hbF]
      exact h
    have c1 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) b (fun a => ι (b₀ a)) _ k t (i t₀) hfr.1 hf hf' C1 ht ht'
    have c2 := GlobalTheory.T.flag_coefficient_ratio_integral M.Ω _ W.toSubring _ (o.Fl.b s) (fun a => ι (b₀ a)) b _ k (i t₀) t
      (hext.2 _ b₀ hfr₀.1) hf' hf C2 ht' ht
    simp only [map_one, one_mul] at c1 c2
    exact ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, c1, c2⟩
  obtain ⟨b, b₀, t, t₀, hf, hfr, hf₀, hfr₀, ht, ht₀, x1, x2⟩ := key (rootIdx D r).1 (rootIdx D r).2
  have u1 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y S M.Ω M.K M.ι M.y o.𝔐 o.Fl M.xdeg o.e r q cM b t o.lines hqc hf hfr ht
  have u0 := GlobalTheory.T.root_lines_flag_degree E H D l Xo c Y ∅ R.Ω R.K R.ι R.y o₀.𝔐 o₀.Fl R.xdeg o₀.e r q₀ cR b₀ t₀ o₀.lines hqc₀ hf₀
    hfr₀ ht₀
  generalize (∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r = A at u1 ⊢
  generalize (∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r = A₀ at u0 ⊢
  have v3 : i (A₀ / t₀ ^ rootSgn D r) ∈ W := hq₀.1 _ u0.2.1
  have v4 : i ((A₀ / t₀ ^ rootSgn D r)⁻¹) ∈ W := hq₀.1 _ u0.2.2
  have hsg : rootSgn D r = 1 ∨ rootSgn D r = -1 := by
    unfold rootSgn
    split_ifs <;> simp
  rw [map_inv₀, map_div₀, map_zpow₀] at v4
  rw [map_div₀, map_zpow₀] at v3
  have n0' : i A₀ / i t₀ ^ rootSgn D r ≠ 0 := by
    rw [← map_zpow₀, ← map_div₀]
    exact (map_ne_zero i).2 u0.1
  exact ratio_mem W hsg u1.1 n0' (hWq _ u1.2.1) (hWq _ u1.2.2) v3 v4 x1 x2

theorem val_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o₀ : RootOrigin Y ∅ R Fx) :
    ∃ C₀ : ℝ, ∀ (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y S M Fx)
      (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) →
      (∀ p ∈ S, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich o.𝔐 p κ) →
      ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ (∀ p : ℕ, p.Prime → p ∣ m → p ∈ S) ∧
        Real.log m ≤ q * (C₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
        ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
          (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
          (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
          (m : M.Ω) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) /
            ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ^ q ∈ W ∧
          (m : M.Ω) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) /
            i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ^ q ∈ W := by
  obtain ⟨m₀, hm₀, hcore⟩ := OrVert.core E H D l Xo c Y Sys Fx R o₀
  refine ⟨Real.log m₀, ?_⟩
  intro S M o i hi hdisc hS
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  obtain ⟨q, m, hq, hm, hlog, hnum⟩ := GlobalTheory.T.log_denominator_bound_primes S m₀ o.𝔐.S_prime hm₀
  obtain ⟨a, b, e, ha, hb⟩ := exists_split S m hm
  have ha0 : 0 < a := Nat.pos_of_mul_pos_right (e ▸ hm)
  have hb0 : 0 < b := Nat.pos_of_mul_pos_left (e ▸ hm)
  have ham : a ≤ m := e ▸ Nat.le_mul_of_pos_right a hb0
  refine ⟨q, a, hq, ha0, ha, le_trans (Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast ham)) hlog, ?_⟩
  intro r cM cR W h1 h2 h3 h4
  by_cases hW : ∀ p ∈ S, (p : M.Ω)⁻¹ ∈ W
  · obtain ⟨u1, u2⟩ := unit_off E H D l Xo c Y Sys Fx R o₀ S M o i hi hdisc r cM cR W h1 h2 h3 h4 hW
    exact ⟨mul_mem (natCast_mem W a) (pow_mem u1 q), mul_mem (natCast_mem W a) (pow_mem u2 q)⟩
  · push Not at hW
    obtain ⟨p, hp, hpW⟩ := hW
    have hbW : (b : M.Ω)⁻¹ ∈ W := inv_natCast_mem W b fun p' hp' hd =>
      inv_mem_of_ne W (o.𝔐.S_prime p hp) hp' (fun h => hb p' hp' hd (h ▸ hp)) hpW
    have hb' : (b : M.Ω) ≠ 0 := Nat.cast_ne_zero.2 hb0.ne'
    have conv : ∀ x : M.Ω, (m : M.Ω) * x ∈ W → (a : M.Ω) * x ∈ W := fun x hx => by
      have e' : (a : M.Ω) * x = (b : M.Ω)⁻¹ * ((m : M.Ω) * x) := by
        rw [e]; push_cast; field_simp
      rw [e']
      exact mul_mem hbW hx
    obtain ⟨κ, hκ, a1, a2⟩ := hcore S M o i hi hS r cM cR W h1 h2 h3 h4
    exact ⟨conv _ (hnum M.Ω W κ hκ _ a1), conv _ (hnum M.Ω W κ hκ _ a2)⟩

end RootFieldNumerics.Ref
end
end

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Chg Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Top

theorem mem_ptsOver {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : z ∈ Small.ptsOver ℂ P :=
  ⟨hz.1, fun f hf => by
    have := hz.2 f hf
    rwa [MvPolynomial.eval_map, ← algebraMap_int_eq, ← aeval_def] at this⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
  {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {S : Finset ℕ} {M R : RootModel (CMType H) (D.p + D.q)}

theorem level (hRes : ResExistsStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y ∅ R Fx) {i : R.Ω →+* M.Ω} (hi : i.comp o₀.g = o.g)
    (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤) (hdeg : o₀.Fl.deg = 1)
    (hloc : ∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      (∀ j, Sys.A.HoloOn U fun y => lam y j) ∧ ∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y)
    {e L : ℕ} (s : Fin L → R.Ω) (hs : ∀ j, s j ∈ chartLatNm R.y (fun k => e * R.A.a k - 1) 1)
    (hs' : ∀ z ∈ Small.ptsOver ℂ (mCoordIdeal R.y),
      ∃ (j : Fin L) (val : ℂ), val ≠ 0 ∧ Small.HasVal R.y (fun k => e * R.A.a k - 1) (s j) z val)
    (n : ℕ) (hn : ∀ a k, -(o₀.Re.ref a).a k ≤ n)
    (hnef : ∀ p ∈ S, ∀ mu : Wt (CMType H) (D.p + D.q), Dominant mu → M.NefAt p mu 0)
    {q m : ℕ} (hq : 0 < q) (hm : 0 < m) (hmS : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ S)
    (hval : ∀ (r : RootIx D) (cM : (k : M.K) → M.ι k) (cR : (k : R.K) → R.ι k) (W : ValuationSubring M.Ω),
          (∀ k, M.y ⟨k, cM k⟩ ≠ 0) → (∀ k, R.y ⟨k, cR k⟩ ≠ 0) → (∀ k j, M.y ⟨k, j⟩ / M.y ⟨k, cM k⟩ ∈ W) →
          (∀ k j, i (R.y ⟨k, j⟩ / R.y ⟨k, cR k⟩) ∈ W) →
          (m : M.Ω) * (i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r) /
            ((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r)) ^ q ∈ W ∧
          (m : M.Ω) * (((∏ k, M.y ⟨k, cM k⟩ ^ M.xdeg r k) * o.e r) /
            i ((∏ k, R.y ⟨k, cR k⟩ ^ R.xdeg r k) * o₀.e r)) ^ q ∈ W) :
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (P : Ideal (MRing ι))
      (Re Re' : PB.Realis Sys P) (Hl : HermLine ι),
      Re.PB II = o.Re.PB II ∧ Re'.PB II = o₀.Re.PB II ∧ Re'.deg = Re.deg ∧ IsSmoothHerm Hl ∧
      PB.SamePot Re.R.A Set.univ (potOf Re.R Hl) (((Sys.th none).rsmul ((n : ℝ) * e)).pullback Re.π Re.holo.1) ∧
      (∀ a t, 0 < t → t ≤ Sys.t₀ → PB.VertClose P S (fun p => (padicValNat p (m ^ (D.p + D.q)) : ℝ) / q)
        (Re.line a t) (Re'.line a t)) ∧
      (∀ p ∈ S, PB.NefAt P p Hl.a ∧ ∀ a, PB.NefAt P p ((Re.ref a).a + Hl.a) ∧ PB.NefAt P p ((Re'.ref a).a + Hl.a)) := by
  classical
  haveI : CharZero M.Ω := Sandwich.charZero_of_hodgeCpt o.𝔐
  haveI : CharZero R.Ω := Sandwich.charZero_of_hodgeCpt o₀.𝔐
  let K : Type := (M.K ⊕ R.K) ⊕ Unit
  let ι : K → Type := Cmp.joinIdx (Cmp.joinIdx M.ι R.ι) fun _ : Unit => Fin L
  let y : (Σ k, ι k) → M.Ω := Cmp.joinVec (Ht.joinOf M R i) fun p => i (s p.2)
  let κ : M.K → K := fun k => Sum.inl (Sum.inl k)
  let κ₀ : R.K → K := fun k => Sum.inl (Sum.inr k)
  let v : (Σ k, M.ι k) → Σ k, ι k := blkV (J := ι) κ fun k => Equiv.refl _
  let v₀ : (Σ k, R.ι k) → Σ k, ι k := blkV (J := ι) κ₀ fun k => Equiv.refl _
  have hv : IsBlockMap κ v := isBlockMap_blkV _ (Sum.inl_injective.comp Sum.inl_injective)
  have hv₀ : IsBlockMap κ₀ v₀ := isBlockMap_blkV _ (Sum.inl_injective.comp Sum.inr_injective)
  have hy : ∀ p, y (v p) = M.y p := fun _ => rfl
  have hy₀ : ∀ p, y (v₀ p) = i (R.y p) := fun _ => rfl
  have hB : Birational y := birational_of_block hv hy M.birational
  have hne : ∀ k, ∃ a, y ⟨k, a⟩ ≠ 0 := by
    rintro ((k | k) | k)
    · exact ne_zero_of_arith M.arith k
    · obtain ⟨a, ha⟩ := ne_zero_of_arith R.arith k
      exact ⟨a, (map_ne_zero i).2 ha⟩
    · obtain ⟨z, hz, -⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts o₀.Re.arith o₀.Re.R.nondeg
      obtain ⟨j, val, hval0, dg, dh, g, h, hg, -, -, e1, e2, e3⟩ := hs' z (mem_ptsOver hz)
      refine ⟨j, (map_ne_zero i).2 fun h0 => ?_⟩
      have h0' : s j = 0 := h0
      rw [h0', zero_mul] at e1
      have := (mem_ptsOver hz).2 g (GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero R.y hg e1)
      rw [this] at e3
      exact mul_ne_zero hval0 e2 e3.symm
  have top : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω), (∀ k, ∃ a, y ⟨k, a⟩ ≠ 0) → Birational y → blockFnField y = ⊤ := by
    intro K _ ι _ Ω _ _ y h hB
    choose c hc using h
    exact GenFib.blockFnField_eq_top y c hc hB
  have tM := top M.y (ne_zero_of_arith M.arith) M.birational
  have tR := top R.y (ne_zero_of_arith R.arith) R.birational
  have ty := top y hne hB
  have hA : IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof M.K M.ι K ι M.Ω M.y y _ ⟨Sum.inr ()⟩ hne
      (tM.trans ty.symm) M.arith
  have hfin : letI := o.g.toAlgebra; 0 < Module.finrank Fx.Ωf M.Ω := by
    have := o.g_deg
    rw [this, ← o.Re_deg]
    exact o.Re.deg_pos
  obtain ⟨J, R', h, br, hh, ho, hπ, hd⟩ := exists_res_degree hRes M.y y hv hy M.arith hA M.birational hB hJ o.Re.R Sys.A
    o.Re.π o.Re.holo o.Re.deg_pos o.Re.degree Fx.yf Fx.generate o.g hfin o.k₀ o.ix o.y_eq Fx.pt o.π_pt hloc
  have him : imageZ v (mCoordIdeal y) = M.P := imageZ_restr (RingHom.id _) hv hy
  have him₀ : imageZ v₀ (mCoordIdeal y) = R.P := imageZ_restr i hv₀ hy₀
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_resProj hJ₀ o₀.Re.R R' hv₀ him₀.ge
  have eπ : o.Re.π ∘ h = o₀.Re.π ∘ h₀ := funext fun x =>
    pi_agree o o₀ hi hv hv₀ hy hy₀ (R'.mem x x (R'.mem_U x)) _ _ (ho x) (ho₀ x)
  let Re := pullRealis o.Re hA hv R' h hh ho _ hπ rfl _ o.Re.deg_pos br hd
  let Re' := pullRealis o₀.Re hA hv₀ R' h₀ hh₀ ho₀ _ hπ eπ _ o.Re.deg_pos br hd
  obtain ⟨Hl, hHs, hHa, hHp⟩ := exists_line R.y y i hv₀ hy₀ hA R.A R.A_smooth s hs hs' (Sum.inr ())
    (by rintro ⟨k, hk⟩; cases hk) (Equiv.refl _) (fun _ => rfl) n
  have hH0 : ∀ k, (n : ℤ) * pullDeg κ₀ 1 k ≤ Hl.a k := fun k => by
    rw [hHa]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, le_add_iff_nonneg_right]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hH1 : ∀ k, 0 ≤ Hl.a k := fun k =>
    (mul_nonneg (Nat.cast_nonneg _) (pullDeg_nonneg hv₀.1 (fun _ => zero_le_one) k)).trans (hH0 k)
  refine ⟨K, inferInstance, ι, inferInstance, mCoordIdeal y, Re, Re', Hl, ?_, ?_, rfl, hHs, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.realisation_pullback_compatible II hII M.K M.ι _ _ Sys M.P o.Re K ι M.Ω y Sys Re κ v hv him
      (Eventually.of_forall fun t a => ⟨rfl, fun _ => rfl⟩) ?_
    have : y ∘ v = M.y := funext hy
    rw [this, tM, ty, IntermediateField.relfinrank_self, one_mul]
    rfl
  · refine GlobalTheory.T.realisation_pullback_compatible II hII R.K R.ι _ _ Sys R.P o₀.Re K ι M.Ω y Sys Re' κ₀ v₀ hv₀ him₀
      (Eventually.of_forall fun t a => ⟨rfl, fun _ => rfl⟩) ?_
    rw [relfinrank_restr i hy₀ tR ty, o₀.Re_deg, hdeg, mul_one]
    have h1 := finrank_comp' o₀.g i
    rw [hi] at h1
    have h2 := o.g_deg
    have h3 := o₀.g_deg
    rw [h2, h3, hdeg, one_mul] at h1
    exact o.Re_deg.trans h1
  · refine samePot_trans_rsmul _ (hHp J R') (Re'.ref_pot none) fun x => ?_
    filter_upwards [(R'.isOpen_U x).mem_nhds (R'.mem_U x)] with w hw
    show Real.log (R.A.h fun p => R'.lift x w (v₀ p)) = Real.log ((o₀.Re.ref none).h fun p => R'.lift x w (v₀ p))
    rw [o₀.ref_none.2 _ (mem_mcPts_restr hv₀ him₀.ge (R'.mem x w hw))]
  · rintro (_ | r) t h0 h1
    · exact vertClose_none o o₀ hi hv hv₀ hy hy₀ hA hJ hJ₀ S _ (fun p => by positivity) h0 h1
    · exact vertClose_some o o₀ hi hv hv₀ hy hy₀ hA hJ hJ₀ hdeg hq hm hmS hval r h0 h1
  · intro p hp
    refine ⟨nefAt_of_nonneg _ _ hH1, fun a => ⟨nefAt_add ?_ (nefAt_of_nonneg _ _ hH1), nefAt_of_nonneg _ _ fun k => ?_⟩⟩
    · refine nefAt_pull hv him.ge (o.𝔐.S_prime p hp) ?_
      rcases a with _ | ⟨τ, j⟩
      · refine nefAt_of_nonneg _ _ fun k => ?_
        rw [o.ref_none.1]
        by_cases hk : k = o.k₀
        · rw [hk, o.A_deg.1]
          exact zero_le_one
        · rw [o.A_deg.2 k hk]
      · rw [o.fund_deg]
        exact nefAt_step M p (hnef p hp) τ j
    · have h1 := pullDeg_add_nonneg hv₀.1 (hn a) k
      have h2 := hH0 k
      show 0 ≤ pullDeg κ₀ (o₀.Re.ref a).a k + Hl.a k
      linarith

end RootFieldNumerics.Ref

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

open RootFieldNumerics.Ref in
theorem RootFieldNumerics.global_model_real_tower_smooth : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II hY hX hII hp hq
  have hFar : HT.FarguesHodgeTate := hG.2.2.2.2.2.2.1
  have hRes : ResExistsStatement := hG.2.2.2.2.2.2.2.2.2.1.resExists
  have hM1 := GlobalTheory.T.good_tower_M1_nef hG E H D Xo l c Y T o II hY hII hp hq
  choose C₀ hC₀ using fun a => val_bound E H D l (Xo l) c Y (o.Sys a) (o.Fx a) (o.R a) (o.refOr a)
  choose e L s hs hs' using o.ample
  have hn : ∀ a, ∃ n : ℕ, ∀ b k, -((o.refOr a).Re.ref b).a k ≤ n := fun a => by
    obtain ⟨x, hx⟩ := (Set.finite_range fun p : Option (RootIx D) × (o.R a).K =>
      (-((o.refOr a).Re.ref p.1).a p.2).toNat).bddAbove
    exact ⟨x, fun b k => (Int.self_le_toNat _).trans (by exact_mod_cast hx ⟨(b, k), rfl⟩)⟩
  choose n hn using hn
  obtain ⟨C₃, hC₃⟩ := OrRef.sum_bound o.toTowerOrigin
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := ∑ a, |C₀ a| with hC₁
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₁a : ∀ a, C₀ a ≤ C₁ := fun a => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun a => |C₀ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
  refine ⟨(D.p + D.q : ℕ) * (C₁ / Real.log 2 + C₃), fun a => ((o.Sys a).th none).rsmul ((n a : ℝ) * e a),
    fun a => (o.refOr a).Re.PBs II, fun a => ReciprocityTheory.AnForm.M.isPotentialRsmul _ _ _ ((o.Sys a).sing none).1,
    fun B hB a => ?_⟩
  obtain ⟨i, hi⟩ := OrRef.exists_comparison (o.refOr a) (o.ref_deg a) (o.Or B a)
  have hSp : ∀ p ∈ o.S B, p.Prime := (o.Or B a).𝔐.S_prime
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ o.S B := by
    intro p hp hd
    refine (o.S_iff B p).mpr ⟨hp, Or.inr ((o.bad_iff p).mpr ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  have hsand : ∀ p ∈ o.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (o.Or B a).𝔐 p κ := fun p hpS => by
    haveI : Fact p.Prime := ⟨hSp p hpS⟩
    exact GlobalTheory.T.exists_sandwich_of_hodge_tate_free hFar E H D l (Xo l) c _ _ Y _ _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)
  obtain ⟨q, m, hq0, hm0, hmS, hlog, hval⟩ := hC₀ a (o.S B) (T.M B a) (o.Or B a) i hi hdisc hsand
  obtain ⟨K, _, ι, _, P, Re, Re', Hl, h1, h2, h3, h4, h5, h6, h7⟩ := level hRes II hII (o.Or B a) (o.refOr a) hi
    (o.smooth B a).1 (o.ref_top a) (o.ref_deg a)
    (fun x => by
      obtain ⟨U, lam, a1, a2, a3, a4, -⟩ := hX.1 a x
      exact ⟨U, lam, a1, a2, a3, a4⟩)
    (s a) (hs a) (hs' a ℂ) (n a) (hn a) (fun p hpS => hM1 B a p ((o.S_iff B p).1 hpS)) hq0 hm0 hmS hval
  refine ⟨K, inferInstance, ι, inferInstance, P, Re, Re', o.S B, _, Hl, congrArg PB.toWtS h1, congrArg PB.toWtS h2, h3,
    fun p hpS => ⟨hSp p hpS, by positivity⟩, h4, h5, h6, h7, ?_⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
  have e1 : ∑ p ∈ o.S B, (padicValNat p (m ^ (D.p + D.q)) : ℝ) / q * Real.log p =
      (∑ p ∈ o.S B, (padicValNat p (m ^ (D.p + D.q)) : ℝ) * Real.log p) / q := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 := sum_padicValNat_log hSp (pow_pos hm0 (D.p + D.q))
  rw [Nat.cast_pow, Real.log_pow] at e2
  have hlB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have h₄ : C₁ ≤ C₁ / Real.log 2 * Real.log B := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hlB hC₁0
  have h₅ : ∑ p ∈ o.S B, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p ≤ C₃ * Real.log B := by
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (hC₃ B hB)
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hv : (0 : ℝ) ≤ 2 * padicValInt p (discr E) := by positivity
    nlinarith [mul_nonneg hv hl]
  have h₆ : Real.log m ≤ q * ((C₁ / Real.log 2 + C₃) * Real.log B) := by
    refine hlog.trans (mul_le_mul_of_nonneg_left ?_ hq'.le)
    have := hC₁a a
    nlinarith
  rw [e1, div_le_iff₀ hq']
  refine e2.trans ?_
  have := mul_le_mul_of_nonneg_left h₆ (Nat.cast_nonneg (D.p + D.q) : (0 : ℝ) ≤ _)
  refine this.trans (le_of_eq ?_)
  ring
