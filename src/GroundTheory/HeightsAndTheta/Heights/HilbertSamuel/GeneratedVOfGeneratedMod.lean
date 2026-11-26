module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenerationOfH1GenAmple

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chartExp (c : ∀ k, ι k) (n : K → ℕ) : (Σ k, ι k) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun q => if q.2 = c q.1 then n q.1 else 0

def chartMon (c : ∀ k, ι k) (n : K → ℕ) : MRingOver S ι :=
  monomial (chartExp c n) 1

theorem chartMon_homog (c : ∀ k, ι k) (n : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (chartMon (S := S) c n) n :=
  GenTwistGenerated.isMultiHomog_monomial _ _ _ fun k => by simp [chartExp]

theorem chartMon_mem {I : ∀ k, Finset (ι k)} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ I k) (n : K → ℕ) :
    chartMon (S := S) c n ∈ KH.cellMon S I := by
  unfold chartMon
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  refine Submonoid.prod_mem _ fun q hq => Submonoid.pow_mem _ (Submonoid.subset_closure ?_) _
  have hq' : q.2 = c q.1 := by
    by_contra h
    simp [chartExp, h] at hq
  obtain ⟨k, i⟩ := q
  simp only at hq'
  subst hq'
  exact ⟨k, c k, hc k, rfl⟩

variable {V : Ideal (MRingOver S ι)}

theorem smul_quot (f : MRingOver S ι) (m : MRingOver S ι ⧸ V) : f • m = Ideal.Quotient.mk V f * m := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

theorem smul_mul_eq_mul_smul {T : Submonoid (MRingOver S ι)} (p : MRingOver S ι)
    (x y : LocalizedModule T (MRingOver S ι ⧸ V)) : (p • x) * y = x * (p • y) := by
  induction x using LocalizedModule.induction_on with
  | h m t =>
    induction y using LocalizedModule.induction_on with
    | h m' t' =>
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_mul_mk, LocalizedModule.smul'_mk,
        LocalizedModule.mk_mul_mk, smul_mul_assoc, mul_smul_comm]

theorem generatedV_of_generatedMod {d : K → ℤ} (h : GeneratedMod S ι (KH.quotPart S V) d) :
    KH.GeneratedV S V d := by
  classical
  intro I
  let c : ∀ k, ι k := fun k => (I.2.1 k).choose
  have hc : ∀ k, c k ∈ I.1 k := fun k => (I.2.1 k).choose_spec
  let dp : K → ℕ := fun k => (d k).toNat
  let dm : K → ℕ := fun k => (-d k).toNat
  have hd : ∀ k, (dp k : ℤ) - dm k = d k := fun k => Int.toNat_sub_toNat_neg (d k)
  let P : MRingOver S ι := chartMon c dp
  let Q : MRingOver S ι := chartMon c dm
  have hP : P ∈ KH.cellMon S I.1 := chartMon_mem hc dp
  have hQ : Q ∈ KH.cellMon S I.1 := chartMon_mem hc dm
  have hpart : ∀ (f : MRingOver S ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a →
      Ideal.Quotient.mk V f ∈ KH.quotPart S V (fun k => (a k : ℤ)) := fun f a hf =>
    Submodule.subset_span ⟨f, ⟨fun k => Int.natCast_nonneg _, by simpa using hf⟩, rfl⟩
  let x : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V P) ⟨Q, hQ⟩
  have hx : x ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) d := by
    refine GenTwistGenerated.mk_mem_locPart _ _ dm (chartMon_homog c dm) ?_
    have e : (d + fun k => (dm k : ℤ)) = fun k => (dp k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact hpart P dp (chartMon_homog c dp)
  obtain ⟨t, a, r, p, z, ht, hta, hpa, hz, htx⟩ := h I x hx
  let w : LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V) :=
    LocalizedModule.mk (Ideal.Quotient.mk V Q) ⟨t * P, mul_mem ht hP⟩
  refine ⟨r, z, fun j => p j • w, hz, fun j => ?_, ?_⟩
  · have e0 : p j • Ideal.Quotient.mk V Q = Ideal.Quotient.mk V (p j * Q) := by
      rw [smul_quot, map_mul]
    have e1 : p j • w =
        LocalizedModule.mk (Ideal.Quotient.mk V (p j * Q)) ⟨t * P, mul_mem ht hP⟩ :=
      (LocalizedModule.smul'_mk ..).trans (congrArg (fun m => LocalizedModule.mk m _) e0)
    refine (congrArg (· ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-d)) e1).mpr ?_
    refine GenTwistGenerated.mk_mem_locPart _ _ (a + dp)
      (GenTwistGenerated.isMultiHomog_mul hta (chartMon_homog c dp)) ?_
    have e2 : (-d + fun k => ((a + dp) k : ℤ)) = fun k => ((a + dm) k : ℤ) := by
      funext k
      have := hd k
      simp only [Pi.add_apply, Pi.neg_apply, Nat.cast_add]
      omega
    rw [e2]
    exact hpart _ _ (GenTwistGenerated.isMultiHomog_mul (hpa j) (chartMon_homog c dm))
  · calc ∑ j, p j • w * z j I = ∑ j, w * (p j • z j I) :=
          Finset.sum_congr rfl fun j _ => smul_mul_eq_mul_smul (p j) w (z j I)
      _ = w * (t • x) := by rw [← Finset.mul_sum, htx]
      _ = 1 := by
        have e3 : Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P) =
            ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) • (1 : MRingOver S ι ⧸ V)) := by
          rw [Submonoid.smul_def, smul_quot, smul_quot, mul_one]
          simp only [Submonoid.coe_mul, map_mul]
          ring
        calc w * (t • x)
            = w * LocalizedModule.mk (t • Ideal.Quotient.mk V P) ⟨Q, hQ⟩ :=
              congrArg (w * ·) (LocalizedModule.smul'_mk ..)
          _ = LocalizedModule.mk (Ideal.Quotient.mk V Q * (t • Ideal.Quotient.mk V P))
                (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) := LocalizedModule.mk_mul_mk
          _ = LocalizedModule.mk ((⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩ : KH.cellMon S I.1) •
                (1 : MRingOver S ι ⧸ V)) (⟨t * P, mul_mem ht hP⟩ * ⟨Q, hQ⟩) :=
              congrArg (fun m => LocalizedModule.mk m _) e3
          _ = LocalizedModule.mk 1 1 := LocalizedModule.mk_cancel _ _
          _ = 1 := OreLocalization.one_def.symm

end GenerationOfH1GenAmple

theorem GenerationOfH1GenAmple.proof (hQ : QuotPartGraded.Statement) : GenerationOfH1GenAmple.Statement := by
  intro S _ K _ _ ι _ _ V N hV hH e
  have hann : V ≤ Module.annihilator (MRingOver S ι) (MRingOver S ι ⧸ V) := fun v hv =>
    Module.mem_annihilator.mpr fun m => by
      rw [GenerationOfH1GenAmple.smul_quot, Ideal.Quotient.eq_zero_iff_mem.mpr hv, zero_mul]
  obtain ⟨c₁, hc₁⟩ := hH (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance (hQ S K ι V hV) hann e
  exact ⟨c₁, fun c hc => GenerationOfH1GenAmple.generatedV_of_generatedMod (hc₁ c hc).2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegreeIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockResolutionDegreeIntegral

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem ratio_smul {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) :
    A₁.h (fun p => c p.1 * z p) / A₀.h (fun p => c p.1 * z p) = A₁.h z / A₀.h z := by
  have hp : (∏ k, ‖c k‖ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A₁.smul c z hc, A₀.smul c z hc, hdeg, mul_div_mul_left _ _ hp]

theorem smooth_logRatio (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) :
    d.R.A.Smooth (fun x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x))) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm := (contDiffOn_const (c := t)).mul
    ((AnResBridge.contDiffOn_potOf d.R h₁ ((d.R.A.chart j).symm y) j).sub
      (AnResBridge.contDiffOn_potOf d.R h₀ ((d.R.A.chart j).symm y) j))
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  have hz := (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2.2).1
  change t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) /
      A₀.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))) =
    t * (Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) -
      Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))))
  rw [hcy, ratio_smul hdeg c hc, Real.log_div (A₁.pos _ hz).ne' (A₀.pos _ hz).ne']

theorem mInt_blockInterpPot_eq (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (t : ℝ) (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) g =
      mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀ +
        LocPot.ofFun (fun x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x)))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2).1
  have h₀ := A₀.pos _ hz
  have h₁ := A₁.pos _ hz
  change (1 - t) * Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (A₀.h (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      t * Real.log (A₁.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) /
        A₀.h (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')))
  rw [hcy, ratio_smul hdeg c hc, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMBlockDatum D K ι Ω) {A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A₁.a = A₀.a)
    (h₀ : IsSmoothHerm A₀) (h₁ : IsSmoothHerm A₁) (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) =
      mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀) (fun _ => 1) := by
  rw [mInt_blockInterpPot_eq d hdeg t]
  exact massIndep d.R.A (fun _ => AnResBridge.potOf d.R A₀)
    (fun _ x => t * Real.log (A₁.h (blockPt d x) / A₀.h (blockPt d x)))
    (fun _ => AnResBridge.isPotential_potOf d.R h₀) (fun _ => smooth_logRatio d hdeg h₀ h₁ t)

theorem mass_potOf (hGG : GenDegGeomDeg.Statement) (d : HSMBlockDatum D K ι Ω) {A₀ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hdeg : A₀.a = unitDeg d.k₀) (h₀ : IsSmoothHerm A₀) :
    mInt d.R.A (fun _ => AnResBridge.potOf d.R A₀) (fun _ => 1) =
      (genDeg (mCoordIdeal d.y) D (unitDeg d.k₀) : ℝ) := by
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (fun _ => (-1 : ℝ)) (fun _ _ _ => rfl)
  have hB : IsSmoothHerm B := contDiffOn_const
  have hlog : logNorm B.inv 1 = fun _ => (1 : ℝ) := by
    funext z
    rw [logNorm_inv_one]
    simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 rfl
  have key := AnResBridge.bridge d.R hex.choose (fun _ => A₀) B.inv 1 d.arith hex.choose_spec
    (fun _ => h₀) (isSmoothHerm_inv hB) hsec
  simp only [hlog] at key
  have hg := hGG K ι Ω d.y D A₀ d.arith h₀
  rw [hdeg] at hg
  rw [← hg]
  unfold geomDeg ptsIntegral
  rw [dite_eq_left hex]
  exact key.symm

end BlockResolutionDegreeIntegral

theorem BlockResolutionDegreeIntegral.proof (hGG : GenDegGeomDeg.Statement) :
    BlockResolutionDegreeIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h0 h1 hs0 hs1 t _
  rw [BlockResolutionDegreeIntegral.mass_eq d (h1.trans h0.symm) hs0 hs1 t]
  exact BlockResolutionDegreeIntegral.mass_potOf hGG d h0 hs0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartSupBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric

noncomputable section

theorem ChartSupBound.proof : ChartSupBound.Statement := by
  intro D V K ψ ν hV hK hKV hψ hν hν0
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun n _ F _ w hw => by simp [hKe] at hw⟩
  obtain ⟨r, hr0, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  set S := cthickening r K with hS
  have hSc : IsCompact S := hK.cthickening
  have hSne : S.Nonempty := hKne.mono (self_subset_cthickening K)

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ M := by
    have h1 := hψ.fderiv_of_isOpen hV (m := 1) (by norm_num)
    exact hSc.exists_bound_of_continuousOn ((h1.continuousOn_fderiv_of_isOpen hV le_rfl).mono hrV)
  set M' := |M| with hM'

  obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hSne (hν.mono hrV)
  set ν₀ := ν x₀ with hν₀
  have hν₀pos : 0 < ν₀ := hν0 x₀ (hrV hx₀)
  set P : ℝ := (Real.pi * r ^ 2) ^ D with hP
  have hPpos : 0 < P := by positivity
  have hprod : ∏ _j : Fin D, gaussDiscMass 0 r = P := by
    rw [hP, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp [gaussDiscMass]
  refine ⟨Real.exp (M' * r ^ 2) / (ν₀ * P), fun n hn F hF w hw => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  set s := r / Real.sqrt n with hs
  have hs2 : (n : ℝ) * s ^ 2 = r ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hnpos.le]
    field_simp
  have hsr : s ≤ r := by
    rw [hs]
    refine div_le_self hr0.le ?_
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  set B := closedBall (0 : Fin D → ℂ) s with hB
  have hzS : ∀ z ∈ B, closedBall w ‖z‖ ⊆ S := fun z hz =>
    (closedBall_subset_closedBall ((mem_closedBall_zero_iff.1 hz).trans hsr)).trans
      (closedBall_subset_cthickening hw r)
  have hwzS : ∀ z ∈ B, w + z ∈ S := fun z hz => hzS z hz (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])

  set ℓ := fderiv ℝ ψ w with hℓ
  set lam : (Fin D → ℂ) →L[ℂ] ℂ := StrongDual.extendRCLike (𝕜 := ℂ) ℓ with hlam
  have hre : ∀ z, (lam z).re = ℓ z := fun z => by
    rw [hlam, StrongDual.extendRCLike_apply]
    simp
  set G : (Fin D → ℂ) → ℂ := fun z => F (w + z) * Complex.exp (((-(n : ℝ) / 2 : ℝ) : ℂ) * lam z)
    with hGdef
  have hG0 : G 0 = F w := by simp [hGdef]
  have hGan : AnalyticOnNhd ℂ G B := by
    intro z hz
    have haff : AnalyticAt ℂ (fun z : Fin D → ℂ => w + z) z := analyticAt_const.add analyticAt_id
    exact ((hF _ (hrV (hwzS z hz))).comp_of_eq haff rfl).mul
      ((analyticAt_const.mul (lam.analyticAt z)).cexp)
  have hPn := PolydiscSubmean.proof D n (fun _ => 0) r G (by omega) hr0 (fun _ => le_rfl) hGan
  simp only [zero_mul, Finset.sum_const_zero, mul_zero, Real.exp_zero, mul_one] at hPn
  rw [hG0, hprod] at hPn
  set k : ℝ := ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) with hk
  have hk0 : 0 ≤ k := by positivity

  have hpt : ∀ z ∈ B, ENNReal.ofReal (k * ‖G z‖ ^ 2) ≤
      ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z)) := by
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have hGz : ‖G z‖ ^ 2 = ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := by
      simp only [hGdef]
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, hre, mul_pow, sq (Real.exp _),
        ← Real.exp_add]
      congr 2
      ring
    have hT := ChartTaylorCover.taylor_le hV hψ ((hzS z hz).trans hrV)
      (fun x hx => (hM x (hzS z hz hx)).trans (le_abs_self M))
    have hz' : ‖z‖ ≤ s := mem_closedBall_zero_iff.1 hz
    have hnz : (n : ℝ) * (M' * ‖z‖ ^ 2) ≤ M' * r ^ 2 := by
      calc (n : ℝ) * (M' * ‖z‖ ^ 2) = M' * ((n : ℝ) * ‖z‖ ^ 2) := by ring
        _ ≤ M' * ((n : ℝ) * s ^ 2) := by gcongr
        _ = M' * r ^ 2 := by rw [hs2]
    have hexp : Real.exp (-(M' * r ^ 2)) * (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z)) ≤
        Real.exp (-(n : ℝ) * ψ (w + z)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hT hnpos.le
      nlinarith
    have hνz : ν₀ ≤ ν (w + z) := isMinOn_iff.1 hmin _ (hwzS z hz)
    rw [hGz, hk]
    have hF0 : 0 ≤ ‖F (w + z)‖ ^ 2 := by positivity
    calc ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
          (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z))
        = ‖F (w + z)‖ ^ 2 * (Real.exp (-(M' * r ^ 2)) *
            (Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(n : ℝ) * ℓ z))) * ν₀ := by ring
      _ ≤ ‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) * ν (w + z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hexp hF0) hνz hν₀pos.le (by positivity)

  have hΦ : MeasurePreserving (fun z : Fin D → ℂ => w + z) volume volume :=
    measurePreserving_add_left volume w
  have hemb : MeasurableEmbedding (fun z : Fin D → ℂ => w + z) :=
    (Homeomorph.addLeft w).isClosedEmbedding.measurableEmbedding
  have hint : ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) ≤ ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by
    calc _ ≤ ‖∫ z in B, ‖G z‖ ^ 2‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ z in B, ‖‖G z‖ ^ 2‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = _ := lintegral_congr fun z => Real.enorm_eq_ofReal (by positivity)
  have hmain : ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) ≤
      ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z) := by
    calc _ ≤ ENNReal.ofReal (k * ∫ z in B, ‖G z‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPn hk0)
      _ = ENNReal.ofReal k * ENNReal.ofReal (∫ z in B, ‖G z‖ ^ 2) := ENNReal.ofReal_mul hk0
      _ ≤ ENNReal.ofReal k * ∫⁻ z in B, ENNReal.ofReal (‖G z‖ ^ 2) := by gcongr
      _ = ∫⁻ z in B, ENNReal.ofReal k * ENNReal.ofReal (‖G z‖ ^ 2) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z in B, ENNReal.ofReal (k * ‖G z‖ ^ 2) :=
          lintegral_congr fun z => (ENNReal.ofReal_mul hk0).symm
      _ ≤ ∫⁻ z in B, ENNReal.ofReal (‖F (w + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ψ (w + z)) *
            ν (w + z)) :=
          setLIntegral_mono' isClosed_closedBall.measurableSet hpt
      _ = ∫⁻ y in (fun z : Fin D → ℂ => w + z) '' B,
            ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y) :=
          hΦ.setLIntegral_comp_emb hemb
            (fun y => ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ν y)) B
      _ ≤ _ := lintegral_mono_set (image_subset_iff.2 fun z hz => hrV (hwzS z hz))
  have hC0 : 0 ≤ Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D := by positivity
  have heq : Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D *
      (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
    have hnD : (n : ℝ) ^ D ≠ 0 := by positivity
    have he : Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hνP : ν₀ * P ≠ 0 := by positivity
    rw [hk, div_eq_mul_inv]
    calc Real.exp (M' * r ^ 2) * (ν₀ * P)⁻¹ * (n : ℝ) ^ D *
          (ν₀ * Real.exp (-(n : ℝ) * ψ w) * Real.exp (-(M' * r ^ 2)) *
            (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P))
        = (Real.exp (M' * r ^ 2) * Real.exp (-(M' * r ^ 2))) * ((n : ℝ) ^ D * ((n : ℝ) ^ D)⁻¹) *
            ((ν₀ * P) * (ν₀ * P)⁻¹) * (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) := by ring
      _ = ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
        rw [he, mul_inv_cancel₀ hnD, mul_inv_cancel₀ hνP]; ring
  calc ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w))
      = ENNReal.ofReal (Real.exp (M' * r ^ 2) / (ν₀ * P) * (n : ℝ) ^ D) *
          ENNReal.ofReal (k * (‖F w‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * P)) := by
        rw [← ENNReal.ofReal_mul hC0, heq]
    _ ≤ _ := by gcongr

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneRegularSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HyperplaneRegularSection

theorem exists_notMem_of_finite {V : Type*} [AddCommGroup V] [Module ℚ V] (S : Set (Submodule ℚ V))
    (hS : S.Finite) (htop : ∀ W ∈ S, W ≠ ⊤) : ∃ v : V, ∀ W ∈ S, v ∉ W := by
  have hne := Subspace.biUnion_ne_univ_of_top_notMem (k := ℚ) (E := V) (s := hS.toFinset)
    (by rw [Set.Finite.mem_toFinset]; exact fun h => htop ⊤ h rfl)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨v, fun W hW hvW => hv ?_⟩
  exact Set.mem_biUnion ((Set.Finite.mem_toFinset hS).mpr hW) hvW

theorem mem_span_of_mul_mem {A : Type*} [CommRing A] [IsNoetherianRing A] (f w u : A)
    (hw : ∀ p ∈ associatedPrimes A (A ⧸ Ideal.span {f}), w ∉ p) (h : w * u ∈ Ideal.span {f}) :
    u ∈ Ideal.span {f} := by
  by_contra hu
  have hx : (Ideal.Quotient.mk (Ideal.span {f}) u) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmem : w ∈ {r : A | ∃ x : A ⧸ Ideal.span {f}, x ≠ 0 ∧ r • x = 0} :=
    ⟨_, hx, by rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]; exact h⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors] at hmem
  obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hmem
  exact hw p hp hwp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem isNoetherianRing_chartRingQ (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) :
    IsNoetherianRing (chartRingQ y c') := by
  classical
  refine isNoetherianRing_of_fg ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rfl

def gen (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (i : ι k) : chartRingQ y c' :=
  ⟨y ⟨k, i⟩ / y ⟨k, c' k⟩, Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩⟩

def eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) : chartRingQ y c' :=
  ∏ k, gen y c' k (c k)

def avoidSub (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (k : K) (p : Ideal (chartRingQ y c')) :
    Submodule ℚ (ι k → ℚ) :=
  (p.restrictScalars ℚ).comap (Fintype.linearCombination ℚ (gen y c' k))

def twist (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_add (y : (Σ k, ι k) → Ω) {c' : ∀ k, ι k} (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) (a a' : K → ℤ) :
    twist y c' (a + a') = twist y c' a * twist y c' a' := by
  simp only [twist, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_add₀ (hc' k)]
  congr 1
  simp only [Pi.add_apply]
  ring


omit [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem twist_zero (y : (Σ k, ι k) → Ω) (c' : ∀ k, ι k) : twist y c' 0 = 1 := by
  simp [twist]


omit [∀ k, Fintype (ι k)] in
theorem coe_eqn (y : (Σ k, ι k) → Ω) (c c' : ∀ k, ι k) :
    (eqn y c c' : Ω) = (∏ k, y ⟨k, c k⟩) * twist y c' 1 := by
  simp only [eqn, gen, twist, Pi.one_apply]
  simp [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end HyperplaneRegularSection


set_option synthInstance.maxHeartbeats 400000 in
open HyperplaneRegularSection in
theorem HyperplaneRegularSection.proof : HyperplaneRegularSection.Statement := by
  intro K _ ι _ Ω _ _ y c e hc
  classical
  have hnoeth : ∀ c' : ∀ k, ι k, IsNoetherianRing (chartRingQ y c') := isNoetherianRing_chartRingQ y

  have hlam : ∀ k, ∃ v : ι k → ℚ, ∑ i, v i • y ⟨k, i⟩ ≠ 0 ∧
      ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
        ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}),
          Fintype.linearCombination ℚ (gen y c' k) v ∉ p := by
    intro k
    let S : Set (Submodule ℚ (ι k → ℚ)) :=
      {LinearMap.ker (Fintype.linearCombination ℚ fun i => y ⟨k, i⟩)} ∪
        ⋃ c' : {c' : ∀ k, ι k // ∀ k, y ⟨k, c' k⟩ ≠ 0},
          avoidSub y c'.1 k '' associatedPrimes (chartRingQ y c'.1)
            (chartRingQ y c'.1 ⧸ Ideal.span {eqn y c c'.1})
    have hS : S.Finite := (Set.finite_singleton _).union
      (Set.finite_iUnion fun c' => (associatedPrimes.finite _ _).image _)
    have htop : ∀ W ∈ S, W ≠ ⊤ := by
      intro W hW hWtop
      rcases hW with hW | hW
      · rw [Set.mem_singleton_iff] at hW
        have h1 : Pi.single (c k) (1 : ℚ) ∈ W := hWtop ▸ Submodule.mem_top
        rw [hW, LinearMap.mem_ker, Fintype.linearCombination_apply_single, one_smul] at h1
        exact hc k h1
      · obtain ⟨c', p, hp, rfl⟩ := Set.mem_iUnion.mp hW
        have h1 : Pi.single (c'.1 k) (1 : ℚ) ∈ avoidSub y c'.1 k p := hWtop ▸ Submodule.mem_top
        rw [avoidSub, Submodule.mem_comap, Submodule.restrictScalars_mem,
          Fintype.linearCombination_apply_single, one_smul,
          show gen y c'.1 k (c'.1 k) = 1 from Subtype.ext (div_self (c'.2 k))] at h1
        exact (IsAssociatedPrime.isPrime hp).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨v, hv⟩ := exists_notMem_of_finite S hS htop
    refine ⟨v, fun h0 => hv _ (Or.inl rfl) ?_, fun c' hc' p hp hvp =>
      hv _ (Or.inr (Set.mem_iUnion.mpr ⟨⟨c', hc'⟩, p, hp, rfl⟩)) hvp⟩
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact h0
  choose v hv0 hvp using hlam
  set m := ∏ k, y ⟨k, c k⟩ with hm_def
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  set l : K → Ω := fun k => ∑ i, v k i • y ⟨k, i⟩ with hl
  set σ : Ω := ∏ k, l k ^ e k with hσ

  have hφ : ∀ (c' : ∀ k, ι k) (k : K),
      ((Fintype.linearCombination ℚ (gen y c' k) (v k) : chartRingQ y c') : Ω) = l k / y ⟨k, c' k⟩ := by
    intro c' k
    simp [Fintype.linearCombination_apply, gen, hl, Finset.sum_div, smul_div_assoc]
  let w : ∀ c' : ∀ k, ι k, chartRingQ y c' := fun c' =>
    ∏ k, Fintype.linearCombination ℚ (gen y c' k) (v k) ^ e k
  have hw : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      (w c' : Ω) = σ * twist y c' (fun k => (e k : ℤ)) := by
    intro c' hc'
    simp only [w, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, hφ, twist, hσ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [div_pow, zpow_neg, Nat.cast_one, one_mul, zpow_natCast, div_eq_mul_inv]
  have hwp : ∀ c' : ∀ k, ι k, (∀ k, y ⟨k, c' k⟩ ≠ 0) →
      ∀ p ∈ associatedPrimes (chartRingQ y c') (chartRingQ y c' ⧸ Ideal.span {eqn y c c'}), w c' ∉ p := by
    intro c' hc' p hp hwp
    have := IsAssociatedPrime.isPrime hp
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := p)).mp hwp
    exact hvp k c' hc' p hp (this.mem_of_pow_mem _ hk)
  refine ⟨σ, Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hv0 k), ?_, ?_⟩
  · intro c' hc'
    show σ * twist y c' (fun k => (e k : ℤ)) ∈ chartRingQ y c'
    rw [← hw c' hc']
    exact (w c').2
  · intro b s hs h c' hc'
    have hnc := hnoeth c'
    have hT : twist y c' 1 * twist y c' (-1) = 1 := by
      rw [← twist_add y hc', add_neg_cancel, twist_zero]
    have hM : m * m⁻¹ = 1 := mul_inv_cancel₀ hm
    let u : chartRingQ y c' := ⟨s * twist y c' b, hs c' hc'⟩
    let u' : chartRingQ y c' :=
      ⟨σ * s / m * twist y c' (b + (fun k => (e k : ℤ)) - 1), h c' hc'⟩
    have key : w c' * u = eqn y c c' * u' := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, u, u']
      rw [hw c' hc', coe_eqn, ← hm_def, sub_eq_add_neg, twist_add y hc', twist_add y hc']
      linear_combination (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ)))) * hM +
        (-(σ * s * twist y c' b * twist y c' (fun k => (e k : ℤ))) * (m * m⁻¹)) * hT
    have hu : u ∈ Ideal.span {eqn y c c'} :=
      mem_span_of_mul_mem _ _ _ (hwp c' hc') (by
        rw [key]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hu
    have ha' : (a : Ω) * (m * twist y c' 1) = s * twist y c' b := by
      rw [← coe_eqn]
      exact congrArg Subtype.val ha
    show s / m * twist y c' (b - 1) ∈ chartRingQ y c'
    have heq : s / m * twist y c' (b - 1) = a := by
      rw [sub_eq_add_neg, twist_add y hc', div_eq_mul_inv]
      linear_combination (-(m⁻¹ * twist y c' (-1))) * ha' + ((a : Ω) * (twist y c' 1 * twist y c' (-1))) * hM +
        (a : Ω) * hT
    rw [heq]
    exact a.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionImageSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set Filter Topology

noncomputable section

namespace ResolutionImageSup

theorem analyticOnNhd_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} {V : Set E}
    {g : E → ι → ℂ} (hg : ∀ i, AnalyticOnNhd ℂ (fun w => g w i) V) (f : MvPolynomial ι ℂ) :
    AnalyticOnNhd ℂ (fun w => eval (g w) f) V := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : E => a) V)
  | add p q hp hq => exact fun w hw => by simpa using (hp w hw).fun_add (hq w hw)
  | mul_X p i hp => exact fun w hw => by simpa using (hp w hw).fun_mul (hg i w hw)

theorem sq_div_pow_eq {a r : ℝ} (hr : 0 < r) (n : ℕ) :
    (a / r ^ n) ^ 2 = a ^ 2 * Real.exp (-(n : ℝ) * (2 * Real.log r)) := by
  have h : Real.exp (-(n : ℝ) * (2 * Real.log r)) = ((r ^ n) ^ 2)⁻¹ := by
    rw [show -(n : ℝ) * (2 * Real.log r) = -Real.log ((r ^ n) ^ 2) by
      rw [Real.log_pow, Real.log_pow]; push_cast; ring, Real.exp_neg, Real.exp_log (by positivity)]
  rw [h, div_pow, div_eq_mul_inv]

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem lift_ne_zero (d : HSMDatum D Ω κ) {x y : d.R.X} (hy : y ∈ d.R.U x) : d.R.lift x y ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := (d.R.mem x y hy).1 ()
  exact hi (by rw [h]; rfl)

theorem ptNorm_resPt_eq (d : HSMDatum D Ω κ) {n : ℕ} {f : MvPolynomial (Ix κ) ℂ} (hf : f.IsHomogeneous n)
    {x y : d.R.X} (hy : y ∈ d.R.U x) :
    ptNorm d.m (RingHom.id ℂ) n f (resPt d y) = ptNorm d.m (RingHom.id ℂ) n f (d.R.lift x y) := by
  obtain ⟨c, hc, hcy⟩ := d.R.compat y x y ⟨d.R.mem_U y, hy⟩
  have h : resPt d y = c () • d.R.lift x y := by
    rw [resPt, hcy]
    rfl
  rw [h, ResolutionSupBound.ptNorm_smul d.m hf (hc ())]

theorem continuous_ptNorm_resPt (d : HSMDatum D Ω κ) {n : ℕ} {f : MvPolynomial (Ix κ) ℂ}
    (hf : f.IsHomogeneous n) : Continuous fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) := by
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨j, hj⟩ := d.R.A.cover y₀
  set e := d.R.A.chart j with he
  have hL : ContinuousAt (d.R.lift y₀) y₀ := by
    rw [continuousAt_pi]
    intro p
    have ha : AnalyticAt ℂ ((fun y => d.R.lift y₀ y p) ∘ e.symm) (e y₀) :=
      d.R.holo y₀ p j (e y₀) ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U y₀⟩
    refine (ha.continuousAt.comp (e.continuousAt hj)).congr ?_
    filter_upwards [e.open_source.mem_nhds hj] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hne := lift_ne_zero d (d.R.mem_U y₀)
  have hρ : ContinuousAt d.m.ρ (d.R.lift y₀ y₀) :=
    d.smooth.continuousOn.continuousAt (isOpen_ne.mem_nhds hne)
  have hcont : ContinuousAt (fun y => ptNorm d.m (RingHom.id ℂ) n f (d.R.lift y₀ y)) y₀ := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact (((MvPolynomial.continuous_eval f).continuousAt.comp hL).norm).div ((hρ.comp hL).pow n)
      (pow_pos (d.m.pos _ hne) n).ne'
  refine hcont.congr ?_
  filter_upwards [(d.R.isOpen_U y₀).mem_nhds (d.R.mem_U y₀)] with y hy
  exact (ptNorm_resPt_eq d hf hy).symm

theorem lintegral_chart_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {e : ℕ}
    (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (μ : Measure X) {ν : (Fin e → ℂ) → ℝ}
    (hν : ContinuousOn ν φ.target)
    (hμ : ∀ S : Set X, MeasurableSet S → S ⊆ φ.source →
      μ S = ∫⁻ y in φ.target ∩ φ.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {g : X → ENNReal} (hg : Measurable g) :
    ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z) ≤ ∫⁻ y, g y ∂μ := by
  have hT : MeasurableSet φ.target := φ.open_target.measurableSet
  have hs : AEMeasurable φ.symm (volume.restrict φ.target) := φ.continuousOn_symm.aemeasurable hT
  have hνm : AEMeasurable (fun z => ENNReal.ofReal (ν z)) (volume.restrict φ.target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hν.aemeasurable hT)
  have hs' : AEMeasurable φ.symm
      ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map φ.symm ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) =
      μ.restrict φ.source := by
    ext S hS
    have hset : φ.symm ⁻¹' S ∩ φ.target = φ.target ∩ φ.symm ⁻¹' (S ∩ φ.source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, φ.map_target h2⟩
      · rintro ⟨h2, h1, -⟩
        exact ⟨h1, h2⟩
    rw [Measure.map_apply_of_aemeasurable hs' hS, withDensity_apply' _ _, Measure.restrict_restrict' hT,
      Measure.restrict_apply hS, hμ _ (hS.inter φ.open_source.measurableSet) inter_subset_right, hset]
  calc ∫⁻ z in φ.target, ENNReal.ofReal (ν z) * g (φ.symm z)
      = ∫⁻ z, g (φ.symm z) ∂((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z)) :=
        (lintegral_withDensity_eq_lintegral_mul₀ hνm (hg.comp_aemeasurable hs)).symm
    _ = ∫⁻ y, g y ∂(Measure.map φ.symm
          ((volume.restrict φ.target).withDensity fun z => ENNReal.ofReal (ν z))) :=
        (lintegral_map' hg.aemeasurable hs').symm
    _ = ∫⁻ y in φ.source, g y ∂μ := by rw [hmap]
    _ ≤ ∫⁻ y, g y ∂μ := setLIntegral_le_lintegral _ _

theorem local_bound (hC : ChartSupBound.Statement) (d : HSMDatum D Ω κ) (x₀ : d.R.X) :
    ∃ N : Set d.R.X, IsOpen N ∧ x₀ ∈ N ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n → ∀ y ∈ N,
        ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ≤ C * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 := by
  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨j, hj⟩ := d.R.A.cover x₀
  set e := d.R.A.chart j with he
  obtain ⟨ν, hνs, hνpos, hνV⟩ := d.vol.2 j
  have hVo : IsOpen (e.target ∩ e.symm ⁻¹' d.R.U x₀) := e.isOpen_inter_preimage_symm (d.R.isOpen_U x₀)
  have hx₀V : e x₀ ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    ⟨e.map_source hj, by rw [mem_preimage, e.left_inv hj]; exact d.R.mem_U x₀⟩
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo _ hx₀V
  have hKV : Metric.closedBall (e x₀) (δ / 2) ⊆ e.target ∩ e.symm ⁻¹' d.R.U x₀ :=
    (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδV
  have hLa : ∀ p, AnalyticOnNhd ℂ (fun w => d.R.lift x₀ (e.symm w) p) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
    fun p => d.R.holo x₀ p j
  have hLne : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀, d.R.lift x₀ (e.symm w) ≠ 0 :=
    fun w hw => lift_ne_zero d hw.2
  have hψ : ContDiffOn ℝ 2 (fun w => 2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm w))))
      (e.target ∩ e.symm ⁻¹' d.R.U x₀) := by
    have hL2 : ContDiffOn ℝ 2 (fun w => d.R.lift x₀ (e.symm w)) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      contDiffOn_pi.2 fun p => ((hLa p).contDiffOn_of_completeSpace).restrict_scalars ℝ
    have hρ : ContDiffOn ℝ 2 (fun w => d.m.ρ (d.R.lift x₀ (e.symm w))) (e.target ∩ e.symm ⁻¹' d.R.U x₀) :=
      (d.smooth.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp hL2 fun w hw => hLne w hw
    exact contDiffOn_const.mul (hρ.log fun w hw => (d.m.pos _ (hLne w hw)).ne')
  obtain ⟨C₀, hC₀⟩ := hC D (e.target ∩ e.symm ⁻¹' d.R.U x₀) (Metric.closedBall (e x₀) (δ / 2)) _ ν hVo
    (isCompact_closedBall _ _) hKV hψ (hνs.continuousOn.mono inter_subset_left) fun z hz => hνpos z hz.1
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x₀) (δ / 2), e.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hj, Set.mem_preimage.mpr (Metric.mem_ball_self (half_pos hδ))⟩, max C₀ 0, le_max_right _ _, fun n hn f hf y hy => ?_⟩
  have hgc := (continuous_ptNorm_resPt d hf).pow 2
  have hgm : Measurable fun y => ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  have hgi : Integrable (fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) d.dV :=
    hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI0 : 0 ≤ ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  have hres : resolutionVolumeL2Complex d n f ^ 2 = ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV := by
    rw [resolutionVolumeL2Complex, Real.sq_sqrt hI0]
  have hid : ∀ w ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ‖eval (d.R.lift x₀ (e.symm w)) f‖ ^ 2 *
          Real.exp (-(n : ℝ) * (2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm w))))) =
        ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm w)) ^ 2 := by
    intro w hw
    rw [ptNorm_resPt_eq d hf hw.2]
    simp only [ptNorm, MvPolynomial.map_id]
    exact (sq_div_pow_eq (d.m.pos _ (hLne w hw)) n).symm
  have key := hC₀ n hn _ (analyticOnNhd_eval hLa f) (e y) (Metric.ball_subset_closedBall hy.2)
  have hyV : e y ∈ e.target ∩ e.symm ⁻¹' d.R.U x₀ := hKV (Metric.ball_subset_closedBall hy.2)
  rw [hid _ hyV, e.left_inv hy.1] at key
  have hint : ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀,
      ENNReal.ofReal (‖eval (d.R.lift x₀ (e.symm z)) f‖ ^ 2 *
        Real.exp (-(n : ℝ) * (2 * Real.log (d.m.ρ (d.R.lift x₀ (e.symm z))))) * ν z) ≤
      ENNReal.ofReal (resolutionVolumeL2Complex d n f ^ 2) := by
    rw [hres, ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun y => sq_nonneg _)]
    calc _ = ∫⁻ z in e.target ∩ e.symm ⁻¹' d.R.U x₀, ENNReal.ofReal (ν z) *
            ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm z)) ^ 2) := by
          refine setLIntegral_congr_fun hVo.measurableSet fun z hz => ?_
          rw [hid z hz, mul_comm, ENNReal.ofReal_mul (hνpos z hz.1).le]
      _ ≤ ∫⁻ z in e.target, ENNReal.ofReal (ν z) *
            ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d (e.symm z)) ^ 2) :=
          lintegral_mono_set inter_subset_left
      _ ≤ _ := lintegral_chart_le e d.dV hνs.continuousOn hνV hgm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ENNReal.ofReal (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) ≤
      ENNReal.ofReal (max C₀ 0 * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact key.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hn0)) hint)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end ResolutionImageSup


open ResolutionImageSup in
theorem ResolutionImageSup.proof (hC : ChartSupBound.Statement) : ResolutionImageSup.Statement := by
  intro D Ω _ _ κ _ d
  choose N hNo hxN C hC0 hCb using fun x => local_bound hC d x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hNo fun x _ => mem_iUnion.2 ⟨x, hxN x⟩
  refine ⟨Real.sqrt (∑ x ∈ t, C x), fun n hn f hf y => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
  have hS : C x ≤ ∑ x ∈ t, C x := Finset.single_le_sum (fun i _ => hC0 i) hxt
  have hS0 : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg fun i _ => hC0 i
  have hr0 : 0 ≤ resolutionVolumeL2Complex d n f := Real.sqrt_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ D := by positivity
  have h2 : ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ≤
      (∑ x ∈ t, C x) * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 :=
    (hCb x n hn f hf y hyx).trans (by gcongr)
  have hp : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f (resPt d y) :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.m.pos _ (lift_ne_zero d (d.R.mem_U y))).le n)
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  calc ptNorm d.m (RingHom.id ℂ) n f (resPt d y)
      = Real.sqrt (ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) := (Real.sqrt_sq hp).symm
    _ ≤ Real.sqrt ((∑ x ∈ t, C x) * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (∑ x ∈ t, C x) * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f := by
      rw [Real.sqrt_mul (mul_nonneg hS0 hn0), Real.sqrt_mul hS0, Real.sqrt_sq hr0, hpow]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
