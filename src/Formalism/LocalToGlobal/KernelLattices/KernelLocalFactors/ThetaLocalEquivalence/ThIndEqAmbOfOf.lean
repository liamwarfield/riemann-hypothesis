module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.VacEntire
noncomputable section

namespace PI.VacEntire

variable {ι : Type} [Fintype ι] {N N' : ℕ}

def Hf (A : ℝ) (z w : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

def al (d : ℕ) (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (Hf A x x).re))

def U (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf A z x - (Real.pi : ℂ) * Hf A x x / 2)

def Iop (d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) * U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z

def tensPow {n : Type} [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def IopEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] (N N' d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ), AnalyticOnNhd ℂ G Set.univ → AnalyticOnNhd ℂ (Iop d A La₁ La₂ G) Set.univ

def TensEntire : Prop :=
  ∀ (n : Type) [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ), AnalyticOnNhd ℂ θ Set.univ →
    AnalyticOnNhd ℂ (tensPow θ N N') Set.univ

def Target : Prop := IopEntire ∧ TensEntire

end PI.VacEntire
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.VacEntire
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft
noncomputable section

namespace PI.VacEntire.UnitaryGroupMassFormula

open PI.VacEntire

def coordL (ι : Type) [Fintype ι] (N N' : ℕ) (τ : ι) (i : Fin N') (j : Fin N) :
    (ι → Fin N' → Fin N → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => Fin N' → Fin N → ℂ) τ))

theorem analyticAt_coord {ι : Type} [Fintype ι] {N N' : ℕ} (τ : ι) (i : Fin N') (j : Fin N)
    (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z τ i j) c :=
  (coordL ι N N' τ i j).analyticAt c

theorem analyticAt_Hf_left {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (fun z => Hf A z x) c := by
  unfold Hf
  refine AnalyticAt.div_const ?_
  refine Finset.analyticAt_fun_sum _ (fun τ _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_sum _ (fun j _ => ?_)
  exact (analyticAt_coord τ i j c).mul analyticAt_const

theorem analyticAt_U {ι : Type} [Fintype ι] {N N' : ℕ} (A : ℝ)
    (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ G Set.univ) (c : ι → Fin N' → Fin N → ℂ) :
    AnalyticAt ℂ (U A x G) c := by
  unfold U
  refine AnalyticAt.mul ?_ ?_
  · have hshift : AnalyticAt ℂ (fun z : ι → Fin N' → Fin N → ℂ => z + x) c :=
      analyticAt_id.add analyticAt_const
    exact (hG (c + x) (Set.mem_univ _)).comp (f := fun z => z + x) hshift
  · refine AnalyticAt.cexp' ?_
    exact (analyticAt_const.mul (analyticAt_Hf_left A x c)).sub analyticAt_const

theorem iopEntire : IopEntire := by
  intro ι _ N N' d A La₁ La₂ G hG c _
  by_cases h0 : (La₁.addSubgroupOf La₂).index = 0
  · have hfun : Iop d A La₁ La₂ G = fun _ => (0 : ℂ) := by
      funext z
      simp [Iop, h0]
    rw [hfun]
    exact analyticAt_const
  · have : Finite (La₂ ⧸ La₁.addSubgroupOf La₂) :=
      (AddSubgroup.index_ne_zero_iff_finite).1 h0
    let _ : Fintype (La₂ ⧸ La₁.addSubgroupOf La₂) := Fintype.ofFinite _
    have hfun : Iop d A La₁ La₂ G = fun z =>
        ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
          ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
            al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) *
              U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z := by
      funext z
      simp only [Iop]
      rw [finsum_eq_sum_of_fintype]
    rw [hfun]
    refine analyticAt_const.mul ?_
    refine Finset.analyticAt_fun_sum _ (fun q _ => ?_)
    exact analyticAt_const.mul (analyticAt_U A _ G hG c)

def blockL (n : Type) [Fintype n] (N N' : ℕ) (i : Fin N') (j : Fin N) :
    (n → Fin N' → Fin N → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun τ => coordL n N N' τ i j

theorem tensEntire : TensEntire := by
  intro n _ θ N N' hθ c _
  unfold tensPow
  refine Finset.analyticAt_fun_prod _ (fun i _ => ?_)
  refine Finset.analyticAt_fun_prod _ (fun j _ => ?_)
  have he : (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) = ⇑(blockL n N N' i j) := by
    funext z τ
    rfl
  have hb : AnalyticAt ℂ (fun z : n → Fin N' → Fin N → ℂ => fun τ => z τ i j) c := by
    rw [he]
    exact (blockL n N N' i j).analyticAt c
  exact (hθ _ (Set.mem_univ _)).comp hb

end PI.VacEntire.UnitaryGroupMassFormula
end
end

theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPAmbOf
section -- merged from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ChiLawAmbOf
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section SeamU

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.matU {n : ℕ} (γ : UF X.E n) : Matrix (Fin n) (Fin n) D.host.E :=
  ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E).map s.iE

theorem Seam.vec_gmap {n : ℕ} (γ : UF X.E n) (x : Sp X.E n) : s.vec (γ.1 x) = (s.matU γ).mulVec (s.vec x) := by
  have h := toGLm_mulVec γ.1 x
  rw [← h]
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Seam.vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Seam.matU]
  rfl

theorem Seam.lat_gmap {n : ℕ} (γ : UF X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat (gmap γ.1 N) = SDLat.smulLat (s.matU γ) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  simp only [SDLat.smulLat, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact ⟨s.vec x0, (s.mem_lat N _).2 ⟨x0, hx0, rfl⟩, (s.vec_gmap γ x0).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    exact ⟨γ.1 x0, ⟨x0, hx0, rfl⟩, s.vec_gmap γ x0⟩

theorem Seam.matU_mem (hok : s.Ok) {n : ℕ} (γ : UF X.E n) :
    (letI := D.host.cmStar; s.matU γ ∈ Matrix.unitaryGroup (Fin n) D.host.E) := by
  let _ := D.host.cmStar
  have h : Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) * 1 *
      ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) = 1 := toGLm_mem_UJ γ
  rw [Matrix.mul_one] at h
  have key : star (s.matU γ) = (Formalism.UG.cT (starRingEnd X.E) ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)).map s.iE := by
    ext i j
    rw [Matrix.star_apply, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    simp only [Seam.matU, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply]
    rw [hok.2]
  rw [Matrix.mem_unitaryGroup_iff', key, Seam.matU, ← Matrix.map_mul, h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem Seam.det_matU {n : ℕ} (γ : UF X.E n) : (s.matU γ).det = s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) := by
  rw [← TE.det_ufGL]
  exact (RingHom.map_det s.iE.toRingHom _).symm

theorem Seam.prod_emb (hok : s.Ok) (z : X.E) : ∏ τ : X.Tau, X.embC s.σ₀ τ z = ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.iE z) :=
  Fintype.prod_equiv s.iT _ _ fun τ => hok.1 τ z

end SeamU

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem chiLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) :
    (ambOf s B χ cD : Amb X).ChiLaw a b := by
  obtain ⟨-, -, -, hχ, -, hok, -⟩ := hN
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN'
  show Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) = _ * _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  rw [s.lat_gmap, s.lat_gmap]
  have h := Formalism.L2.PairingIndexBounds.Eq.character_factor_unitary_action χ hχ (Formalism.L2.PairingIndexBounds.Eq.detSmul D) (Formalism.L2.PairingIndexBounds.Eq.norm_one_unit_ideal D) ha hb (s.lat N) (s.lat N')
    ⟨s.matU γ, s.matU_mem hok γ⟩ ⟨s.matU γ', s.matU_mem hok γ'⟩ (s.sd_lat hok hN) (s.sd_lat hok hN')
  simp only at h
  rw [h]
  have u1 := Matrix.det_of_mem_unitary (s.matU_mem hok γ)
  have p1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det) = (∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ := by
    rw [s.prod_emb hok, ← Finset.prod_inv_distrib, ← s.det_matU]
    exact Finset.prod_congr rfl fun τ _ => Formalism.L2.PairingIndexBounds.Eq.emb_star_unit τ _ (Unitary.mul_star_self_of_mem u1)
  have p2 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det = ∏ τ : X.Tau, X.embC s.σ₀ τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) := by
    rw [s.prod_emb hok, ← s.det_matU]
  show Base.chiFac χ a b (s.lat N) (s.lat N') * ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (s.matU γ).det)) ^ (b / 2) *
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (s.matU γ').det) ^ (a / 2)) = _
  rw [p1, p2, inv_pow, zpow_neg, zpow_natCast, zpow_natCast, mul_comm]
  rfl

end Chi

end Formalism.L2.Ker
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section An

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eNat_analytic (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hθ : AnalyticOnNhd ℂ B.thMM Set.univ) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AnalyticOnNhd ℂ (B.eNat χ N N' L L') Set.univ := by
  have hT := entireStatements_holds
  have h0 : AnalyticOnNhd ℂ (B.thZero N N') Set.univ := hT.2 _ B.thMM N N' hθ
  have h1 : AnalyticOnNhd ℂ (B.thHalf N N' L) Set.univ := hT.1 _ _ _ _ _ _ _ _ h0
  have h2 : AnalyticOnNhd ℂ (B.thMoved N N' L L') Set.univ := hT.1 _ _ _ _ _ _ _ _ h1
  intro z _
  exact analyticAt_const.mul (h2 z (Set.mem_univ _))

variable {X : Fields} (s : Seam D X) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem eOmega_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) (a b : ℕ) : (ambOf s B χ cD : Amb X).EOmega a b := by
  obtain ⟨hcc, hδ, -, -, -, -, -⟩ := hN
  intro N N' _ _
  have hA := eNat_analytic B χ (Formalism.L2.KerInert.AlgP.thMM_analytic B (B.stdOK hcc hδ)) a b (s.lat N) (s.lat N')
  have hc : ContDiff ℂ ⊤ (B.eNat χ a b (s.lat N) (s.lat N')) := hA.contDiff
  exact hc.comp (contDiff_pi.2 fun τ => contDiff_apply ℂ _ (s.iT.symm τ))

end An

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

end Main

end Formalism.L2.Ker
end
end

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions

section U

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem TE.ufGL_apply' (γ : UF E n) (i j : Fin n) : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = γ.1 (Pi.single j 1) i := by
  have h := TE.matT_apply (ι := Unit) (fun _ => RingHom.id E) γ () i j
  simpa [TE.matT] using h

theorem TE.ufInv_apply (γ : UF E n) (i k : Fin n) : γ.1.symm (Pi.single k 1) i = star (γ.1 (Pi.single i 1) k) := by
  have h : hStd E n (γ.1 (Pi.single i 1)) (γ.1 (γ.1.symm (Pi.single k 1))) = hStd E n (Pi.single i 1) (γ.1.symm (Pi.single k 1)) :=
    γ.2 _ _
  rw [LinearEquiv.apply_symm_apply, hStd_single_left] at h
  rw [← h, hStd_apply]
  simp [Pi.single_apply]

end U

section Eq

variable {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem ambOf_conj (hok : s.Ok) (τ : X.Tau) (x : X.E) : X.embC (ambOf s B χ cD).σ₀ τ (star x) = star (X.embC (ambOf s B χ cD).σ₀ τ x) := by
  let _ := D.host.cmStar
  show s.σ₀ (X.emb τ (star x)) = star (s.σ₀ (X.emb τ x))
  rw [hok.1, hok.1, hok.2, ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, Formalism.L2.PairingIndexBounds.Eq.embT_star']

theorem eqLaw_ambOf {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b) : (ambOf s B χ cD : Amb X).EqLaw a b := by
  obtain ⟨hcc, hδ, -, hχ, -, hok, -⟩ := hN
  let _ := D.host.cmStar
  intro γ γ' N N' hN hN' z
  have hE := (Formalism.L2.PairingIndexBounds.Eq.SqG.eqP_outright B hcc hδ (B.stdOK hcc hδ) χ hχ).1 a b ⟨s.lat N, s.sd_lat hok hN⟩
    ⟨s.lat N', s.sd_lat hok hN'⟩ ha hb ⟨s.matU γ, s.matU_mem hok γ⟩ ⟨s.matU γ', s.matU_mem hok γ'⟩
  show B.eNat χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) (fun τ => z (s.iT.symm τ)) =
    B.eNat χ a b (s.lat N) (s.lat N') (fun τ => (ambOf s B χ cD : Amb X).pullV a b γ.1 γ'.1 z (s.iT.symm τ))
  rw [s.lat_gmap, s.lat_gmap]
  have hE' := congrFun hE (fun τ => z (s.iT.symm τ))
  rw [← hE']
  unfold TaylorLogMetric.pull
  congr 1
  funext τ i j
  obtain ⟨τ', rfl⟩ := s.iT.surjective τ
  simp only [Equiv.symm_apply_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold Amb.pullV
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have e1 : ∀ y : X.E, TaylorLogMetric.embT D (s.iT τ') (s.iE y) = X.embC s.σ₀ τ' y := fun y => (hok.1 τ' y).symm
  have f1 : star ((B.tor).emb (s.iT τ') (s.matU γ' k i)) = X.embC s.σ₀ τ' (γ'.1.symm (Pi.single k 1) i) := by
    rw [TE.ufInv_apply, Seam.matU, Matrix.map_apply, TE.ufGL_apply']
    show star (TaylorLogMetric.embT D (s.iT τ') (s.iE _)) = _
    rw [← Formalism.L2.PairingIndexBounds.Eq.embT_star', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj, ← hok.2, e1]
  have f2 : (B.tor).emb (s.iT τ') (s.matU γ l j) = X.embC s.σ₀ τ' (γ.1 (Pi.single j 1) l) := by
    rw [Seam.matU, Matrix.map_apply, TE.ufGL_apply']
    exact e1 _
  rw [f1, f2]
  rfl

theorem thIndEq_ambOf_of (hT : ThIndOfEq) {σ₀ : X.K →+* ℂ} (hN : NatOk s cc δ χ cD σ₀) {a b : ℕ} (ha : Even a) (hb : Even b)
    (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) {D' : ℕ} (hD : 0 < D') (hLa : (ambOf s B χ cD : Amb X).LaHyp a b Sall) :
    (ambOf s B χ cD : Amb X).ThIndEq a b Sall D' :=
  hT X _ a b Sall D' (ambOf_conj s B χ cD hN.2.2.2.2.2.1) hD hLa (eqLaw_ambOf s B χ cD hN ha hb)

end Eq

end Formalism.L2.Ker
