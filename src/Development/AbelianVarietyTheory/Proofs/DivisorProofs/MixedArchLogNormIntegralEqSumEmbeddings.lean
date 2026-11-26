module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem intg_logSec_of_arithVar : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP k _ X _ _ p D hX σ L M s hs
  have := hX.isDomain
  have := hX.finite
  have hσ : Function.Injective σ := by
    have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
      ext n
      simp [Ideal.mem_comap, RingHom.mem_ker])
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hk
  let K := FractionRing k
  obtain ⟨τ, rfl⟩ : ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
    ⟨IsFractionRing.lift hσ, by ext a; simp⟩
  let G := Limits.pullback p (spMap (algebraMap k K))
  let j : G ⟶ X := Limits.pullback.fst _ _
  let q : G ⟶ Sp K := Limits.pullback.snd _ _
  have hp : IsPullback j q p (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, -, -⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp D hX
  obtain ⟨s', hs', -, -, hlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP K G q τ D hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ) s' hs'
  have h2 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ D hX L).2 (M.logSec s)).1
  refine h2.1 ?_
  have e : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hlog
  rwa [e] at h1

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_logNormSection_arithmeticVariety : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  first | exact @GlobalTheory.Mix.intg_logSec_of_arithVar | exact GlobalTheory.Mix.intg_logSec_of_arithVar | (intros; apply GlobalTheory.Mix.intg_logSec_of_arithVar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationTopChernDensityEqFactorialMixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDet
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PolDet

theorem det_sum_smul_eq {D : ℕ} (x : Fin D → ℂ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    (∑ i, x i • H i).det =
      ∑ m : Fin D → Fin D, (∏ l, x (m l)) * (Matrix.of fun j l => H (m l) j l).det := by
  simp only [Matrix.det_apply', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem coeff_eq {D : ℕ} (m : Fin D → Fin D) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      if Function.Surjective m then 1 else 0 := by
  classical
  set T := Finset.univ.image m with hT
  have h1 : ∀ S : Finset (Fin D), ∏ l, (if m l ∈ S then (-1 : ℂ) else 0) =
      (-1 : ℂ) ^ D * ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) := by
    intro S
    rw [Finset.prod_ite_zero, Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_ite, mul_one,
      mul_zero, Finset.mem_sdiff, Finset.mem_univ, true_and, hT, Finset.mem_image]
    congr 1
    apply propext
    constructor
    · rintro h i hi ⟨l, rfl⟩
      exact hi (h l trivial)
    · intro h l _
      by_contra hl
      exact h (m l) hl ⟨l, rfl⟩
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card *
      ∏ i ∈ Finset.univ \ S, (if i ∉ T then (1 : ℂ) else 0) =
      ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    simp [Finset.prod_const]
  have h3 : ∏ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) =
      if Function.Surjective m then (-1 : ℂ) ^ D else 0 := by
    have : ∀ i, ((-1 : ℂ) + if i ∉ T then (1 : ℂ) else 0) = if i ∈ T then (-1 : ℂ) else 0 := by
      intro i; by_cases hi : i ∈ T <;> simp [hi]
    simp_rw [this]
    rw [Finset.prod_ite_zero]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, true_implies,
      hT, Finset.mem_image, true_and]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [h1, mul_left_comm _ ((-1 : ℂ) ^ D), ← Finset.mul_sum, h2, h3]
  split_ifs <;> simp [← pow_add, ← two_mul, pow_mul]

theorem polarisation_det (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det =
      ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  classical
  simp_rw [det_sum_smul_eq, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coeff_eq, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun τ : Equiv.Perm (Fin D) => (τ : Fin D → Fin D)) ?_ ?_ ?_ ?_
  · intro τ _
    simpa using τ.surjective
  · intro τ _ σ _ h
    exact DFunLike.coe_injective h
  · intro m hm
    have hs : Function.Surjective m := by simpa using hm
    exact ⟨Equiv.ofBijective m ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, by simp, rfl⟩
  · intro τ _
    rfl

end GlobalTheory.PolDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det : ∀ (D : ℕ) (H : Fin D → Matrix (Fin D) (Fin D) ℂ), ∑ S : Finset (Fin D), (-1 : ℂ) ^ S.card * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := by
  first | exact @GlobalTheory.PolDet.polarisation_det | exact GlobalTheory.PolDet.polarisation_det | (intros; apply GlobalTheory.PolDet.polarisation_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationTopChernDensityEqFactorialMixed
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem pol_chernDens_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  intro k _ X p σ D L c y hy
  set H : Fin D → Matrix (Fin D) (Fin D) ℂ := fun j => MixDens.chernMat ((L j).φ σ) c y with hH
  have hc (n : Fin D → ℤ) : c.chernDens ((ArInt.comb L n).φ σ) y =
      D.factorial / Real.pi ^ D * (∑ j, (n j : ℂ) • H j).det.re := by
    rw [← MixDens.chernMat_comb k X p σ D (Fin D) L n c y hy]
    rfl
  have key := GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det D H
  simp only [FibreProj.pol, hc, dens, MLine.ofHerm]
  have e2 : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess ((L (τ l)).φ σ) (pick ((L (τ l)).φ σ).isLB y) y j l).det)
      = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := rfl
  rw [e2, ← key, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have : ((-1 : ℂ) ^ S.card) = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  trans (-1) ^ S.card * (D.factorial / Real.pi ^ D * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det.re)
  · simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_neg, Int.cast_one, Int.cast_zero]
  · ring

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationTopChernDensityEqFactorialMixedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_topChernDensity_eq_factorial_mixed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  first | exact @GlobalTheory.Mix.pol_chernDens_comb | exact GlobalTheory.Mix.pol_chernDens_comb | (intros; apply GlobalTheory.Mix.pol_chernDens_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddings
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixPolar

theorem injective_emb {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k] (σ : k →+* ℂ) :
    Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  change Ideal.comap (algebraMap ℤ k) (RingHom.ker σ) = ⊥
  rw [RingHom.comap_ker, (RingHom.ext_int _ (Int.castRingHom ℂ) : σ.comp (algebraMap ℤ k) = _)]
  exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem chernInt_eq (h : IsArithVar p D) (N M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s)
    (σ : k →+* ℂ) :
    (N.φ σ).chernInt D (offSupp p σ (M.div (isRatSec_ratOfSec s hs))) (logNorm (M.φ σ) (ratOfSec s hs)) =
      Mix.int (fun _ : Fin D => MLine.ofHerm N σ) ((MLine.ofHerm M σ).logSec s) := by
  have := h.isDomain
  have := h.finite
  have hnull (ε : ℤˣ) : (N.φ σ).chernPart D ε (ptsIn p σ (nonzeroLocus s))ᶜ = 0 := by
    have := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero k X p σ (injective_emb σ) h.isProjOver D (fun _ => MLine.ofHerm N σ) ε (nonzeroLocus s) hs
    rwa [part_const] at this
  have key (ε : ℤˣ) : ∫ y in offSupp p σ (M.div (isRatSec_ratOfSec s hs)), logNorm (M.φ σ) (ratOfSec s hs) y
      ∂(N.φ σ).chernPart D ε = ∫ y, (MLine.ofHerm M σ).logSec s y ∂(N.φ σ).chernPart D ε := by
    have hae : ∀ᵐ y ∂(N.φ σ).chernPart D ε, y ∈ ptsIn p σ (nonzeroLocus s) := ae_iff.2 (hnull ε)
    have e : offSupp p σ (M.div (isRatSec_ratOfSec s hs)) = ptsIn p σ (nonzeroLocus s) := offSupp_divOfSec
    rw [e, Measure.restrict_eq_self_of_ae_mem hae]
    exact integral_congr_ae (hae.mono fun y hy => logNorm_ratOfSec _ hy)
  rw [Weight.chernInt, key, key, Mix.int, part_const, part_const]
  rfl

end GlobalTheory.MixPolar

namespace GlobalTheory.MixPolar

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}

theorem pol_int (hP : GlobalTheory.Published.Principalisation) (h : IsArithVar p D) (L : Fin D → HermLB p) (M : HermLB p)
    (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (σ : k →+* ℂ) :
    FibreProj.pol (fun n => Mix.int (fun _ : Fin D => MLine.ofHerm (ArInt.comb L n) σ) ((MLine.ofHerm M σ).logSec s)) =
      D.factorial * Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  have e : ∀ F : (Fin D → ℤ) → ℝ,
      ∑ S : Finset (Fin D), (-1 : ℝ) ^ S.card * F (fun i => if i ∈ S then -1 else 0) = FibreProj.pol F := fun F => by
    unfold FibreProj.pol
    congr!
  let Lj : Option (Finset (Fin D)) → Fin D → MLine p σ := fun j =>
    j.elim (fun i => MLine.ofHerm (L i) σ) (fun S _ => MLine.ofHerm (ArInt.comb L (fun i => if i ∈ S then -1 else 0)) σ)
  let a : Option (Finset (Fin D)) → ℝ := fun j => j.elim (-(D.factorial : ℝ)) (fun S => (-1) ^ S.card)
  have hd : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ j, a j * dens (Lj j) c y = 0 := by
    intro c y hy
    have := GlobalTheory.T.polarisation_topChernDensity_eq_factorial_mixed k X p σ D L c y hy
    rw [← e] at this
    simp only [Fintype.sum_option, a, Lj, Option.elim, dens_const]
    beta_reduce at this
    simp only [MLine.ofHerm] at this ⊢
    linarith
  have hi : ∀ j, Intg (Lj j) ((MLine.ofHerm M σ).logSec s) := fun j =>
    GlobalTheory.T.integrable_logNormSection_arithmeticVariety hP k X p D h σ (Lj j) (MLine.ofHerm M σ) s hs
  have := GlobalTheory.T.linear_relation_mixed_densities_integrals k X p σ D _ a Lj hd _ hi
  simp only [Fintype.sum_option, a, Lj, Option.elim] at this
  rw [← e]
  beta_reduce
  linarith

end GlobalTheory.MixPolar


open GlobalTheory.MixPolar in
theorem GlobalTheory.MixPolar.mixArch_eq_sum : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → HermLB p) (M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), MixHt.mixArch L M (isRatSec_ratOfSec s hs) = ∑ᶠ σ : k →+* ℂ, Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  intro hP k _ X _ _ p D h L M s hs
  have := h.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [MixHt.mixArch, HermLB.archInt, finsum_eq_sum_of_fintype, chernInt_eq h]
  rw [FibreProj.pol_sum]
  simp only [pol_int hP h L M s hs]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by positivity)]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddingsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → HermLB p) (M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), MixHt.mixArch L M (isRatSec_ratOfSec s hs) = ∑ᶠ σ : k →+* ℂ, Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  first | exact @GlobalTheory.MixPolar.mixArch_eq_sum | exact GlobalTheory.MixPolar.mixArch_eq_sum | (intros; apply GlobalTheory.MixPolar.mixArch_eq_sum <;> assumption)
end
