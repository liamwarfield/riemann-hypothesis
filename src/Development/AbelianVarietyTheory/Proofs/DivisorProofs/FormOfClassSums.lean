module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicFourierSeriesOfSummableCoefficients
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem form_of_classSums {B X W I κ HV HW : Type} [MeasurableSpace B] [MeasurableSpace X] [Fintype I] [Fintype κ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup HV] [InnerProductSpace ℂ HV] [FiniteDimensional ℂ HV]
    [NormedAddCommGroup HW] [InnerProductSpace ℂ HW] [FiniteDimensional ℂ HW]
    (ν : Measure B) (𝓕 : Set B) (μ : Measure X) (𝓖 : Set X) (k : B → X → W → ℂ) (s : I → B) (wt : I → ℂ) (ev : HV → I → W)
    (F : HW → X → ℂ) (N : ℝ) (th : HV →ₗ[ℂ] HW) (Ψ : HW → B → W) (b : OrthonormalBasis κ ℂ W)
    (hV : ∀ x x', inner ℂ x x' = ∑ j, wt j * inner ℂ (ev x j) (ev x' j))
    (hW : ∀ U U', inner ℂ U U' = (N : ℂ) * l2 μ 𝓖 (F U') (F U))
    (hth : ∀ x g, F (th x) g = ∑ j, wt j * k (s j) g (ev x j))
    (hint : ∀ U w h, IntegrableOn (fun g => k h g w * starRingEnd ℂ (F U g)) 𝓖 μ)
    (hΨ : ∀ U h w, inner ℂ (Ψ U h) w = l2 μ 𝓖 (fun g => k h g w) (F U))
    (hex : ∀ U, ∃ a, ∀ j, ev a j = (N : ℂ) • Ψ U (s j)) (U₁ U₂ : HW)
    (hsum : ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν = ∑ j, wt j * inner ℂ (Ψ U₁ (s j)) (Ψ U₂ (s j)))
    (hi : ∀ a, IntegrableOn (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => k h g (b a)) (F U₂))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) := by
  have h1 : ∀ U j, ev (LinearMap.adjoint th U) j = (N : ℂ) • Ψ U (s j) := fun U => by
    obtain ⟨a, ha⟩ := hex U
    have : LinearMap.adjoint th U = a := by
      refine ext_inner_right ℂ fun x => ?_
      rw [LinearMap.adjoint_inner_left, hW, hV, l2_sum_eq_sum_norm_sq_of_orthogonal μ 𝓖 wt (fun j g => k (s j) g (ev x j)) _ _ (hth x) fun j => hint U _ _,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ha, inner_smul_left, Complex.conj_ofReal, hΨ, mul_left_comm]
    rwa [this]
  have e2 : ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) =
      ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν := by
    refine (integral_finsetSum _ fun a _ => hi a).symm.trans ?_
    congr 1
    funext h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hΨ, ← hΨ, inner_conj_symm]
  rw [e2, hsum, hV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, h1, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem inner_law {B W : Type} [Group B] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : B →* Module.End ℂ W)
    (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {z : ℂ} (hz : ‖z‖ = 1) (k : B) (a b : W) :
    inner ℂ (z • ρ k a) (z • ρ k b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, hρ, ← mul_assoc, Complex.conj_mul', hz]
  simp

section Adjoint

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)
  {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)} (HW : HMod (MMap M)) {N : ℝ}
  (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y))

include hW in
theorem pet_eq (y y' : HW.H) (v w : M.Vec) :
    l2 μ 𝓖 (HW.e y' w) (HW.e y v) = ipM M μ 𝓖 (HW.e y) (HW.e y') * ∏ τ, ⟪(v τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
  rw [← (isMultiplicityInner_of_model HW hW y y' v w).2, l2_eq_star]

include hW in
theorem inner_eq_pet (y y' : HW.H) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) :
    inner ℂ y y' = (N : ℂ) * l2 μ 𝓖 (HW.e y' v) (HW.e y v) := by
  rw [pet_eq HW hW, hW, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

variable {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
  {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
  (HV : HMod (Bridge.Gf V → c.W))
  (hV : HV.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (Bridge.adInner (Bridge.ratF V) (grpOf V β L) y))
  (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (th : HV.H →ₗ[ℂ] HW.H)
  (hth : ∀ x g, HW.e (th x) v g = ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext (HV.e x) h)) ∂ν)
  (hint : ∀ (U : HW.H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (HW.e U v g)) 𝓖 μ)

include hc in
theorem upVec_mem (Ψ : GA D V → c.W) (h2 : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) :
    (fun u => Ψ (finLift V u)) ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L) :=
  mem_adForms (finHom V).rangeRestrict (GQ V) c.ρ (finLift V) (finLift_spec V) (fun u => hc.1 _ (finLift_mem V u)) Ψ
      fun γ hγ k hk x => h2 γ hγ k ((mem_grpOf V β L k).1 hk) x


include hω hc hφ hinf hlev hW hν hy hV hv hth hint in
theorem form_eq_sum (U₁ U₂ : HW.H) {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W)
    (hi : ∀ k, IntegrableOn (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ k, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v))
        (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v)) := by
  have h0 := fun U => exists_upVec hω c hc β L φ hφ hinf hlev μ 𝓖 (HW.e U v) (hint U)
  have h1 := fun U => (h0 U).choose_spec.1
  have h2 := fun U => (h0 U).choose_spec.2
  refine form_of_classSums ν 𝓕 μ 𝓖 (fun h g w => Datum.thetaKO ω h g (φ w)) (fun j => finLift V (y j))
    (fun j => ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹) (fun x j => HV.e x (y j))
    (fun U => HW.e U v) N th (fun U => (h0 U).choose) b hV.2.2 (fun U U' => inner_eq_pet HW hW U U' v hv)
    (fun x g => ?_) hint h1 (fun U => ?_) U₁ U₂ ?_ hi
  · exact (hth x g).trans (theta_classSum hω c hc β L φ hφ hinf hlev hν hy (HMod_mem hV x) g)
  · exact (HMod_onto hV (Submodule.smul_mem _ (N : ℂ) (upVec_mem c hc β L _ (h2 U)))).imp fun a ha j => congrFun ha (y j)
  · refine integral_eq_classSum V β L hν hy _ fun γ hγ k hk x => ?_
    exact (congrArg₂ (inner ℂ) (h2 U₁ γ hγ k hk x) (h2 U₂ γ hγ k hk x)).trans
      (inner_law c.ρ hc.2.1 (norm_levChi β L k) _ _ _)

end Adjoint

theorem tsum_eval {Y : Type} (Z kf p : Y → ℂ) (C s : ℂ) (h1 : ∀ y, Z y = C * kf y * starRingEnd ℂ (p y))
    (h2 : HasSum (fun y => kf y * starRingEnd ℂ (p y)) s) : ∑' y, Z y = C * s := by
  simp only [h1, mul_assoc]
  exact (h2.mul_left C).tsum_eq

theorem integral_pi_eval {ι : Type} [Fintype ι] {X : ι → Type} [∀ ρ, MeasurableSpace (X ρ)] (m : ∀ ρ, Measure (X ρ))
    [∀ ρ, SigmaFinite (m ρ)] (a : ∀ ρ, X ρ → ℂ) (Φ : (∀ ρ, X ρ) → ℂ) (c0 z q : ℂ)
    (h : ∀ b, Φ b = c0 * (∏ ρ, a ρ (b ρ)) * 1 * (z * starRingEnd ℂ (q * ∏ ρ, a ρ (b ρ)))) :
    ∫ b, Φ b ∂(Measure.pi m) = c0 * z * starRingEnd ℂ q * ((∏ ρ, ∫ x, ‖a ρ x‖ ^ 2 ∂(m ρ) : ℝ) : ℂ) := by
  have e : ∀ b, Φ b = c0 * z * starRingEnd ℂ q * ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) := fun b => by
    have : ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) = (∏ ρ, a ρ (b ρ)) * starRingEnd ℂ (∏ ρ, a ρ (b ρ)) := by
      rw [Complex.mul_conj', norm_prod]
      push_cast
      rw [Finset.prod_pow]
    rw [h, this, map_mul]
    ring
  simp only [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_fintype_prod_eq_prod fun ρ x => ‖a ρ x‖ ^ 2]

theorem realMat_mem (i : Fin D.R.m) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) (ρ : D.what₂.Tau) (b : Upq (Wc D i) ρ) :
    realMat (Wc D i) Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ) := by
  refine GlobalTheory.AdelicScalar.conjFrame_mem_UH _ _ _ ((sig_add i ρ).trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm) _ _ (hFr ρ) ?_ b
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND (Wc D i)).2).isUnit

theorem rTr_mul (W : HSp D) (a b : GA D W) (F : GA D W → ℂ) : rTr W (a * b) F = rTr W a (rTr W b F) := by
  funext h
  simp only [rTr, mul_assoc]

theorem coef_translate {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ)
    (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (v : M.Vec) :
    ∃ w : M.Vec, rTr W (realElt θ W g) (HW.e U₁ v) = HW.e U₁ w ∧
      l2 μ 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
        ipM M μ 𝓖 (HW.e U₂) (HW.e U₁) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (g τ) (v τ : M.H τ)⟫_ℂ :=
  ⟨fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩,
    (GlobalTheory.RealEquiv.mult_realElt D W S θ M J χ _ hU g hg v _ fun _ => rfl).symm, pet_eq HW hW U₂ U₁ v _⟩

theorem eq_of_value {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (U₁ U₂ : HW.H) :
    inner ℂ U₁ U₂ = (N : ℂ) * starRingEnd ℂ (ipM M μ 𝓖 (HW.e U₂) (HW.e U₁)) := by
  rw [← inner_conj_symm, hW, map_mul, Complex.conj_ofReal]

end GlobalTheory.AdelicScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors
open GlobalTheory.TorusExt

private theorem sumF_mul_left {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x y : Ix → F} {s t : F} (a : F) (h : SumF I F x s)
    (hy : ∀ i, y i = a * x i) (ht : t = a * s) : SumF I F y t := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, happ⟩ := h
  let f : F →ₗ[R] F :=
    { toFun := fun u => a * u
      map_add' := fun u v => mul_add a u v
      map_smul' := fun r u => by
        change a * ((algebraMap R (FractionRing R) r) • u) = (algebraMap R (FractionRing R) r) • (a * u)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, ht.symm⟩, fun i => ⟨x i, hx i, (hy i).symm⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := happ n
  refine ⟨S, fun T hT => ?_⟩
  have hm := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at hm
  have e : f (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i := by
    change a * (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i
    rw [mul_sub, Finset.mul_sum, ht]
    simp only [hy]
  rw [e] at hm
  exact hm


attribute [local instance] gtGroup in
theorem exhaust_of_labels : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (C : Type) (g : C → GtPtF D.toPre (FractionRing R)) (x : C → (TFK (R := R) (FractionRing R) ⟶ A.A)), (∀ c, ∃ o, GtPtF.IsNsmul N (g c) o ∧ o.IsZero) → (∀ c c', g c = g c' → x c = x c') → (∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) N) (y : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) N p y → ∃ c, y.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left) → ∀ b : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ D.toPre.P.A, b ^ N = 1 → ∃ c, b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (g c).b.left := by
  intro hLL R _ _ _ I hI D A G _ _ hSA U N hN C g x htor hfun hcov b hb
  have hB : D.toPre.TauBimult := D.tau_bimult
  have hN0 : N ≠ 0 := by omega
  have hf : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap (FractionRing R) (FractionRing R)) = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) :=
    RingHom.ext fun _ => rfl
  obtain ⟨fT, hT⟩ := GlobalTheory.TorsionIso.torsion_eq hLL R I hI D A G hSA U (AlgebraicClosure (FractionRing R)) N hN
  obtain ⟨hT1, -, hT3, -⟩ := hT
  have hi : GtPtF.IsIota 0 (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))) := by
    have hz : (0 : GtPtF D.toPre (AlgebraicClosure (FractionRing R))).IsZero := (isZero_iff_eq _).2 rfl
    obtain ⟨hb, hv⟩ := (isZero_iff_val _).1 hz
    refine (isIota_iff_val _ _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (th D.toPre (T := TF (R := R) (AlgebraicClosure (FractionRing R))) y J) := isCub_cubV D.toPre.cub hJ
    have t := tau_mul (𝟙 (TF (R := R) (AlgebraicClosure (FractionRing R)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm
  let P : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → QkPt D.toPre (AlgebraicClosure (FractionRing R)) N :=
    fun h => ⟨0, h.1, N • h.1, (isNsmul_iff_eq _ _ _).2 rfl,
      h.2.symm ▸ hi⟩
  have hPy : ∀ h, (P h).y = 0 := fun _ => rfl
  have hPg : ∀ h, (P h).g = h.1 := fun _ => rfl
  have hEq : ∀ h h', QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (P h) (P h') → h = h' := by
    intro h h' e
    obtain ⟨z, hy, t, ht, hg⟩ := e
    change 0 = 0 + N • z at hy
    simp only [zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : N = 0) hN0
      · exact h3
    have ht0 : t = 0 := isIota_unique (hz ▸ ht) hi
    have hg := (isAdd_iff_eq _ _ _).1 hg
    rw [hPg, hPg, ht0, add_zero] at hg
    exact Subtype.ext hg.symm
  haveI : Finite {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} := by
    have hc := GlobalTheory.UT.card_qk hLL R I hI D (AlgebraicClosure (FractionRing R)) N hN
    haveI : Finite (Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N))) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hN0)
    refine Finite.of_injective (β := Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)))
      (fun h => Quot.mk (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)) (P h)) fun h h' e => hEq h h' ?_
    exact (equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact e)
  have hcx : ∀ h, ∃ c, (fT (P h)).left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left :=
    fun h => hcov (P h) (fT (P h)) (hPy h) ((hT1 _ _).2 rfl)
  choose c hc using hcx
  have hgc : ∀ c, N • g c = 0 := by
    intro c
    obtain ⟨o, ho, hz⟩ := htor c
    rw [isNsmul_iff_eq] at ho
    rw [isZero_iff_eq] at hz
    rw [← ho, hz]
  let Φ : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} :=
    fun h => ⟨gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)), by rw [← map_nsmul, hgc, map_zero]⟩
  have hΦ : Function.Injective Φ := by
    intro h h' e
    have e1 : g (c h) = g (c h') := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre (congrArg Subtype.val e)
    have e2 := hfun _ _ e1
    apply hEq
    apply (hT3 _ _).1
    apply Over.OverMorphism.ext
    rw [hc h, hc h', e2]
  obtain ⟨g', hg'b, hg'N⟩ :=
    exists_nsmul_eq_of_pow_eq (D := D.toPre) (F := (AlgebraicClosure (FractionRing R))) hN0 0 (hb.trans zero_b.symm)
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hΦ) ⟨g', hg'N⟩
  refine ⟨c h, ?_⟩
  have e1 : g' = gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)) := (congrArg Subtype.val hh).symm
  rw [← hg'b, e1, gtExt_b, Over.comp_left, extMap_left]

section Scale
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem exists_scale {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ z J, Good L z J →
      (val t' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val t (𝟙 _) z J).val := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom : F →* Γ(Spec (CommRingCat.of F), ⊤)) (Units.mk0 c hc)
  refine ⟨GlobalTheory.UU.scaleGen u t, GlobalTheory.UU.scaleGen_isGen u ht, fun z J hJ => ?_⟩
  rw [GlobalTheory.UU.val_scaleGen u t (𝟙 _) hJ, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u, ← CoefBasic.cst_eq]
  rfl

theorem coef_scale {D : DegPre R} {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (h : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val w (𝟙 _) z J).val)
    (s : Fam D F k) (χ : D.X) : coef s g w' χ = c * coef s g w χ := by
  apply CoefBasic.coef_eq
  intro z J hJ
  have hx := CoefBasic.isCoef_coef g hw χ s z J hJ
  rw [h z J hJ]
  rw [CoefBasic.cst_eq] at hx ⊢
  rw [map_mul]
  linear_combination (CoefBasic.cstH (R := R) z c) * hx

end Scale

theorem liesOver_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → LiesOver U w₀ g w x fr → ∀ c : F, c ≠ 0 → ∃ (w' : Frm D.toPre F 1 g.b) (fr' : FrAt x), w'.IsGen ∧ fr'.IsGen ∧ LiesOver U w₀ g w' x fr' ∧ (∀ (s : Fam D.toPre F 1) χ, c * coef s g w' χ = coef s g w χ) ∧ ∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val fr (𝟙 _) z J).val := by
  intro R _ _ I _ D A G _ _ U F _ _ w₀ g w x fr hw hfr hL c hc
  obtain ⟨w', hw', hw'v⟩ := exists_scale (R := R) (F := F) w hw (inv_ne_zero hc)
  obtain ⟨fr', hfr', hfr'v⟩ := exists_scale (R := R) (F := F) fr hfr hc
  refine ⟨w', fr', hw', hfr', ?_, ?_, ?_⟩
  · intro k hk wk hwk hwkg s s' v hexp hval
    have hck : c ^ k ≠ 0 := pow_ne_zero k hc
    obtain ⟨wk0, hwk0g, hwk0v⟩ := exists_scale (R := R) (F := F) wk hwkg hck
    have h1 : SumF I F (coef s' g wk0) (c ^ k * v) := by
      refine hL k hk wk0 ?_ hwk0g s s' (c ^ k * v) hexp ?_
      · intro z J hJ
        apply Units.ext
        have e : CoefBasic.cstH (R := R) z (c ^ k) * (CoefBasic.cstH (R := R) z c⁻¹) ^ k = 1 := by
          rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc, one_pow, map_one]
        rw [hwk0v z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw'v z J hJ]
        linear_combination ((val w (𝟙 _) z J).val) ^ k * e
      · intro z J hJ
        have hv := hval z J hJ
        rw [hv, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
          Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
            @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
        simp only [id, CoefBasic.cst_eq, map_mul, map_pow]
        ring
    have h2 : ∀ χ, coef s' g wk0 χ = c ^ k * coef s' g wk χ := fun χ => coef_scale g hwkg hwk0v s' χ
    exact sumF_mul_left (c ^ k)⁻¹ h1
      (fun χ => by rw [h2, ← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
      (by rw [← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
  · intro s χ
    rw [coef_scale g hw hw'v s χ, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul]
  · intro z J hJ
    rw [show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
    simp only [CoefBasic.cst_eq, id]

end GlobalTheory.Poinc.Tors
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFinrankLineBundleSectionsFiniteEtale
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LB GlobalTheory.CechPic GlobalTheory.TangentOrigin
open H0

theorem eq_zero_of_forall_algHom_eq_zero {E A : Type} (Ω : Type) [Field E] [CommRing A]
    [Algebra E A] [Algebra.Etale E A] [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] {a : A}
    (h : ∀ φ : A →ₐ[E] Ω, φ a = 0) : a = 0 := by
  have := Algebra.FormallyUnramified.finite_of_free E A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field E A
  have : IsArtinianRing A := .of_finite E A
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
  have hm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
  let := Ideal.Quotient.field J
  let ψ : (A ⧸ J) →ₐ[E] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have := h (ψ.comp (Ideal.Quotient.mkₐ E J))
  rw [AlgHom.comp_apply, map_eq_zero_iff ψ ψ.toRingHom.injective] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this

section Points

variable {k R : Type} [CommRing k] [CommRing R] {S : Scheme.{0}}

theorem evalPt_algX (q : S ⟶ Sp k) (x : Sp R ⟶ S) (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) :
    evalPt x U h (algX q U c) =
      evalPt (x ≫ q) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) :=
  congrArg (fun g => (g ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE x q ⊤ U ⊤ le_top h)

theorem evalPt_algX_of_eq (q : S ⟶ Sp k) (x : Sp R ⟶ S) {φ : k →+* R} (hx : x ≫ q = spMap φ)
    (U : S.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (c : k) : evalPt x U h (algX q U c) = φ c := by
  rw [evalPt_algX, hx, evalPt_spMap]

theorem H0.val_smul {q : S ⟶ Sp k} {N : LB S} {O : S.Opens} (x : Sp R ⟶ S) {φ : k →+* R}
    (hx : x ≫ q = spMap φ) (i : N.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ N.U i) (c : k)
    (f : H0 q N O) : val x i hO hi (c • f) = φ c * val x i hO hi f := by
  rw [base_smul, val_fun_smul, evalPt_algX_of_eq q x hx]


variable (R) in
abbrev PtsOver [Algebra k R] (q : S ⟶ Sp k) : Type :=
  {x : Sp R ⟶ S // x ≫ q = spMap (algebraMap k R)}

def ptsOverEquiv [Algebra k R] [IsAffine S] (q : S ⟶ Sp k) :
    letI := (algX q ⊤).toAlgebra
    PtsOver R q ≃ (Γ(S, ⊤) →ₐ[k] R) :=
  letI := (algX q ⊤).toAlgebra
  Equiv.ofBijective
    (fun x => ⟨evalPt x.1 ⊤ le_top, fun c => evalPt_algX_of_eq q x.1 x.2 ⊤ le_top c⟩)
    ⟨fun x y e => Subtype.ext (ext_evalPt (isAffineOpen_top S) le_top le_top
      (congrArg AlgHom.toRingHom e)), fun ψ => by
      obtain ⟨x, h, e⟩ := exists_evalPt_eq (isAffineOpen_top S) ψ.toRingHom
      refine ⟨⟨x, eq_spMap_of_evalPt _ _ fun c => ?_⟩, AlgHom.ext fun a => DFunLike.congr_fun e a⟩
      rw [← evalPt_algX q x ⊤ h, e]
      exact ψ.commutes c⟩

end Points

section FiniteEtale

variable {E : Type} [Field E] {S : Scheme.{0}} (q : S ⟶ Sp E)

theorem etale_algX [IsAffine S] [Etale q] : (algX q ⊤).Etale :=
  RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of E)).symm.commRingCatIsoToRingEquiv
    (HasRingHomProperty.appLE @Etale q ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ le_top)

variable {N : LB S}

theorem exists_generator [IsFinite q] [Etale q] (hN : N.IsLB) : ∃ e : H0 q N ⊤,
    (Function.Bijective fun a : Γ(S, ⊤) => a • e) ∧ ∀ i, IsUnit (e.loc i) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  have : IsArtinianRing Γ(S, ⊤) := .of_finite E _
  obtain ⟨t, ht⟩ := exists_isGen_of_subsingleton_pic_top hN
  refine ⟨H0.ofSec q ⊤ (DVR.genSec t ht), ?_, fun i => (Units.isUnit (t.s i)).map (resG S inf_le_right)⟩
  have := isQuasicoherent_toMod hN
  exact (isFrame_iff_bijective (isAffineOpen_top S) _).1 (isFrame_genSec hN ht ⊤)

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω] [IsFinite q] [Etale q]


omit [IsAlgClosed Ω] in
theorem finite_ptsOver : Finite (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  exact Finite.of_equiv _ (ptsOverEquiv q).symm

theorem finite_finrank_lineBundleSections_finiteEtale (hN : N.IsLB) :
    Module.Finite E (H0 q N ⊤) ∧ Module.finrank E (H0 q N ⊤) = Nat.card (PtsOver Ω q) := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  have := Algebra.FormallyUnramified.finite_of_free E Γ(S, ⊤)
  obtain ⟨e, he, -⟩ := exists_generator q hN
  let ψ : Γ(S, ⊤) →ₗ[E] H0 q N ⊤ :=
    { toFun a := a • e
      map_add' a b := add_smul a b e
      map_smul' c a := mul_smul (algX q ⊤ c) a e }
  let φ := LinearEquiv.ofBijective ψ he
  exact ⟨.equiv φ, by
    rw [← φ.finrank_eq, Nat.card_congr (ptsOverEquiv q), natCard_algHom_eq_finrank_of_etale]⟩

variable {q Ω}

theorem H0.eq_zero_of_forall_val_eq_zero (hN : N.IsLB) (i : PtsOver Ω q → N.ι)
    (hi : ∀ x : PtsOver Ω q, ⊤ ≤ x.1 ⁻¹ᵁ N.U (i x)) {g : H0 q N ⊤}
    (h : ∀ x : PtsOver Ω q, val x.1 (i x) le_top (hi x) g = 0) : g = 0 := by
  have : IsAffine S := isAffine_of_isAffineHom q
  let := (algX q ⊤).toAlgebra
  have : Algebra.Etale E Γ(S, ⊤) := etale_algX q
  obtain ⟨e, he, hu⟩ := exists_generator q hN
  obtain ⟨a, rfl⟩ := he.2 g
  have : a = 0 := eq_zero_of_forall_algHom_eq_zero (E := E) Ω fun ψ => by
    obtain ⟨x, rfl⟩ := (ptsOverEquiv q).surjective ψ
    have := (val_fun_smul x.1 (i x) le_top (hi x) a e).symm.trans (h x)
    exact (((hu (i x)).map (evalPt x.1 _ _)).mul_left_eq_zero).1 this
  simp only [this, zero_smul]

end FiniteEtale

section Subscheme

variable {E : Type} [Field E] {Y : Scheme.{0}} {p : Y ⟶ Sp E} {I : Y.IdealSheafData} {B : LB Y}

theorem exists_chart_of_field {F : Type} [Field F] (hB : B.IsLB) (x : Sp F ⟶ Y) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ B.U i := by
  obtain ⟨i, hi⟩ := exists_chart hB (x (default : PrimeSpectrum F))
  exact ⟨i, fun z _ => (Subsingleton.elim (α := PrimeSpectrum F) default z) ▸ hi⟩

theorem valOn_smul {k R : Type} [CommRing k] [CommRing R] {p : Y ⟶ Sp k}
    (x : Sp R ⟶ I.subscheme) {φ : k →+* R} (hx : x ≫ I.subschemeι ≫ p = spMap φ) (i : B.ι)
    (hi : ⊤ ≤ (x ≫ I.subschemeι) ⁻¹ᵁ B.U i) (c : k) (g : sectionsOnClosedSubscheme p B I) :
    valOn x i hi (c • g) = φ c * valOn x i hi g :=
  H0.val_smul x hx _ _ _ c g

variable [IsFinite (I.subschemeι ≫ p)] [Etale (I.subschemeι ≫ p)] (hB : B.IsLB)
  (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra E Ω]

include hB

theorem finite_H0On : Module.Finite E (sectionsOnClosedSubscheme p B I) :=
  (finite_finrank_lineBundleSections_finiteEtale _ (AlgebraicClosure E) (LB.isLB_pull hB _)).1

theorem finrank_H0On :
    Module.finrank E (sectionsOnClosedSubscheme p B I) = Nat.card (PtsOver Ω (I.subschemeι ≫ p)) :=
  (finite_finrank_lineBundleSections_finiteEtale _ Ω (LB.isLB_pull hB _)).2


variable {Ω} in
theorem eq_zero_of_forall_valOn_eq_zero (i : PtsOver Ω (I.subschemeι ≫ p) → B.ι)
    (hi : ∀ x : PtsOver Ω (I.subschemeι ≫ p), ⊤ ≤ (x.1 ≫ I.subschemeι) ⁻¹ᵁ B.U (i x))
    {g : sectionsOnClosedSubscheme p B I} (h : ∀ x : PtsOver Ω (I.subschemeι ≫ p), valOn x.1 (i x) (hi x) g = 0) : g = 0 :=
  H0.eq_zero_of_forall_val_eq_zero (LB.isLB_pull hB _) (fun x _ => i x) _ h

end Subscheme

end GlobalTheory.Vanishing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.PlaneBasis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem splitLat_induction (τ : E →ₐ[F] v.adicCompletion F) (L : Submodule (𝓞 E) (Fin n → E))
    {p : (Fin n → v.adicCompletion F) → Prop}
    (h1 : ∀ a ∈ v.adicCompletionIntegers F, ∀ z ∈ L, p (a • fun r => τ (z r)))
    (h0 : p 0) (hadd : ∀ u w, p u → p w → p (u + w)) (hneg : ∀ u, p u → p (-u))
    {u : Fin n → v.adicCompletion F} (hu : u ∈ splitLat τ L) : p u := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => p (splitVec τ y)) (fun a ha z hz => ?_) ?_ ?_ ?_ hy
  · convert h1 a ha z hz using 1
    funext r; simp [splitVec]
  · convert h0; funext r; simp [splitVec]
  · intro y z hy hz; rw [splitVec_add]; exact hadd _ _ hy hz
  · intro y hy; convert hneg _ hy using 1; funext r; simp [splitVec]

theorem tau_mem_splitLat (τ : E →ₐ[F] v.adicCompletion F) {L : Submodule (𝓞 E) (Fin n → E)}
    {z : Fin n → E} (hz : z ∈ L) : (fun r => τ (z r)) ∈ splitLat τ L :=
  ⟨fun i => (1 : v.adicCompletion F) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun r => by simp [splitVec]⟩

theorem smul_mem_int {S : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)}
    {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) {u : Fin n → v.adicCompletion F}
    (hu : u ∈ S) : a • u ∈ S := S.smul_mem ⟨a, ha⟩ hu

theorem mem_colSpan {M : Matrix (Fin n) (Fin n) (v.adicCompletion F)} {u : Fin n → v.adicCompletion F} :
    u ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) ↔
      ∃ w : Fin n → v.adicCompletion F, (∀ i, w i ∈ v.adicCompletionIntegers F) ∧ M *ᵥ w = u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => c i, fun i => (c i).2, ?_⟩
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

end GlobalTheory.PlaneBasis

noncomputable section

namespace GlobalTheory.PlaneBasis

def unskip (i₀ i₁ i : ℕ) : ℕ := if i < i₀ then i else if i < i₁ then i - 1 else i - 2

theorem skip_ne_left {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : skip i₀ i₁ j ≠ i₀ := by
  unfold skip; split_ifs <;> omega

theorem skip_ne_right {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : skip i₀ i₁ j ≠ i₁ := by
  unfold skip; split_ifs <;> omega

theorem skip_lt {i₀ i₁ n₁ : ℕ} {j : ℕ} (hj : j < n₁) : skip i₀ i₁ j < n₁ + 2 := by
  unfold skip; split_ifs <;> omega

theorem unskip_skip {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : unskip i₀ i₁ (skip i₀ i₁ j) = j := by
  unfold skip unskip; split_ifs <;> omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

def colMat {n n₁ : ℕ} (τ : E →ₐ[F] v.adicCompletion F) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : Matrix (Fin n₁) (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  fun r i => if i.1 = i₀ then τ (x r) else if i.1 = i₁ then τ (y r) else
    if h : unskip i₀ i₁ i.1 < n₁ then (ι.map τ * β₁) r ⟨_, h⟩ else 0

end GlobalTheory.PlaneBasis

namespace GlobalTheory.PlaneBasis

theorem exists_isSplitBasis_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ), n = n₁ + 2 → i₀ < i₁ → i₁ < n → L.IsFullLattice E →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ((∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1) →
    ((∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1) →
    IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁ →
    ∃ β : GL (Fin n) (v.adicCompletion F), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  intro F E _ _ _ _ _ σ _ v τ n n₁ L x y ι β₁ i₀ i₁ hn h01 h1n hL hdec hx hy hβ₁
  subst hn
  have hO : ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  set M := colMat τ x y ι β₁.1 i₀ i₁ with hM
  set P := Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) with hP
  have hsmul : ∀ (c : E) (z : Fin (n₁ + 2) → E), (fun r => τ ((c • z) r)) = τ c • fun r => τ (z r) :=
    fun c z => funext fun r => by simp
  have hτmul : ∀ u : Fin n₁ → E, (fun r => τ ((ι *ᵥ u) r)) = ι.map τ *ᵥ fun r => τ (u r) :=
    fun u => funext fun r => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc0 : (fun r => M r ⟨i₀, by omega⟩) = fun r => τ (x r) := funext fun r => by simp [hM, colMat]
  have hc1 : (fun r => M r ⟨i₁, h1n⟩) = fun r => τ (y r) := funext fun r => by
    simp [hM, colMat, h01.ne']
  have hcj : ∀ j : Fin n₁, (fun r => M r ⟨skip i₀ i₁ j, skip_lt j.2⟩) = fun r => (ι.map τ * β₁.1) r j :=
    fun j => funext fun r => by
      simp [hM, colMat, skip_ne_left h01, skip_ne_right h01, unskip_skip h01, j.2]
  have hPx : (fun r => τ (x r)) ∈ P := hc0 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPy : (fun r => τ (y r)) ∈ P := hc1 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPcol : ∀ j : Fin n₁, (fun r => (ι.map τ * β₁.1) r j) ∈ P := fun j =>
    hcj j ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (∀ j, w₁ j ∈ v.adicCompletionIntegers F) →
      (ι.map τ * β₁.1) *ᵥ w₁ ∈ P := by
    intro w₁ hw
    have : (ι.map τ * β₁.1) *ᵥ w₁ = ∑ j, w₁ j • (fun r => (ι.map τ * β₁.1) r j) := by
      funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact sum_mem fun j _ => smul_mem_int (hw j) (hPcol j)
  have hSub : ∀ z ∈ L, (fun r => τ (z r)) ∈ P := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hdec z hz
    have hu' : u ∈ L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) := hu
    have h1 := hβ₁.mem_iff.1 (tau_mem_splitLat τ hu')
    have e : (fun r => τ (u r)) = β₁.1 *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : (fun r => τ ((s • x + ι *ᵥ u + t • y) r)) = τ s • (fun r => τ (x r)) +
        (ι.map τ * β₁.1) *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) + τ t • fun r => τ (y r) := by
      rw [← Matrix.mulVec_mulVec, ← e, ← hτmul, ← hsmul, ← hsmul]; funext r; simp
    rw [this]
    exact add_mem (add_mem (smul_mem_int ((hO _).2 (hx.1 s hs)) hPx) (hPimg _ h1))
      (smul_mem_int ((hO _).2 (hy.1 t ht)) hPy)
  have hImg : ∀ u ∈ splitLat τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))),
      ι.map τ *ᵥ u ∈ splitLat τ L := fun u hu =>
    splitLat_induction τ _ (p := fun u => ι.map τ *ᵥ u ∈ splitLat τ L)
      (fun a ha z hz => by
        rw [Matrix.mulVec_smul, ← hτmul]; exact smul_mem_int ha (tau_mem_splitLat τ hz))
      (by rw [Matrix.mulVec_zero]; exact zero_mem _)
      (fun u w hu hw => by rw [Matrix.mulVec_add]; exact add_mem hu hw)
      (fun u hu => by rw [Matrix.mulVec_neg]; exact neg_mem hu) hu
  have hunit : ∀ z : Fin (n₁ + 2) → E, ((∀ c : E, c • z ∈ L → Valued.v (τ c) ≤ 1) ∧
      ∃ c : E, c • z ∈ L ∧ Valued.v (τ c) = 1) → (fun r => τ (z r)) ∈ splitLat τ L := by
    rintro z ⟨-, c, hc, hv⟩
    have hne : τ c ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have h2 := tau_mem_splitLat τ hc
    rw [hsmul] at h2
    have hinv : (τ c)⁻¹ ∈ v.adicCompletionIntegers F := (hO _).2 (by rw [map_inv₀, hv, inv_one])
    have := smul_mem_int hinv h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hColSL : ∀ i, (fun r => M r i) ∈ splitLat τ L := by
    intro i
    by_cases h0 : i.1 = i₀
    · convert hunit x hx using 1; funext r; simp [hM, colMat, h0]
    by_cases h1 : i.1 = i₁
    · convert hunit y hy using 1; funext r; simp only [hM, colMat, if_neg h0, if_pos h1]
    by_cases h2 : unskip i₀ i₁ i.1 < n₁
    · have : (fun r => M r i) = ι.map τ *ᵥ (β₁.1 *ᵥ Pi.single ⟨_, h2⟩ 1) := by
        funext r
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
        simp only [hM, colMat, if_neg h0, if_neg h1, dif_pos h2, Matrix.transpose_apply]
        rfl
      rw [this]
      refine hImg _ ((hβ₁ _).1 fun k => ?_)
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    · convert zero_mem (splitLat τ L) using 1; funext r; simp [hM, colMat, h0, h1, h2]
  have hPle : P ≤ splitLat τ L := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hColSL i)
  have hSLle : ∀ u ∈ splitLat τ L, u ∈ P := fun u hu =>
    splitLat_induction τ L (p := (· ∈ P)) (fun a ha z hz => smul_mem_int ha (hSub z hz)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hu
  have hR : ∀ z : Fin (n₁ + 2) → E, (fun r => τ (z r)) ∈ LinearMap.range M.mulVecLin := by
    intro z
    have hz : z ∈ Submodule.span E (L : Set (Fin (n₁ + 2) → E)) := by
      letI := hL
      rw [Submodule.IsFullLattice.span_eq_top]
      trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, -, hw⟩ := mem_colSpan.1 (hSub z hz)
      exact ⟨w, hw⟩
    | zero => convert zero_mem (LinearMap.range M.mulVecLin) using 1; funext r; simp
    | add a b _ _ ha hb =>
      convert add_mem ha hb using 1; funext r; simp
    | smul c a _ ha =>
      rw [hsmul]; exact Submodule.smul_mem _ _ ha
  have hsurj : Function.Surjective M.mulVec := by
    intro u
    have : u ∈ LinearMap.range M.mulVecLin := by
      rw [← Finset.univ_sum_single u]
      refine sum_mem fun k _ => ?_
      have e : Pi.single k (u k) = u k • fun r => τ ((Pi.single k (1 : E) : Fin (n₁ + 2) → E) r) := by
        funext r
        by_cases h : r = k
        · subst h; simp
        · simp [h]
      rw [e]
      exact Submodule.smul_mem _ _ (hR _)
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨hU.unit, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h]
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h, h01.ne']
  · intro j h r
    rw [IsUnit.unit_spec]
    have : i = ⟨skip i₀ i₁ j, skip_lt j.2⟩ := Fin.ext h
    subst this
    exact congrFun (hcj j) r
  · intro u
    rw [IsUnit.unit_spec]
    constructor
    · intro hu; exact hPle (mem_colSpan.2 ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨w, hw, e⟩ := mem_colSpan.1 (hSLle _ hu)
      have := Matrix.mulVec_injective_iff_isUnit.2 hU e
      rw [← this]; exact hw

end GlobalTheory.PlaneBasis
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodic
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem thV_invV_eq : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  intro F _ _ N _ ψ lam ν hC 𝓓 hD hD1 f hf hq hdec
  have hC' := hC
  obtain ⟨hTR, ⟨hψc, hψn, hψF, -⟩, -, -, -⟩ := hC'
  funext w
  obtain ⟨x, y⟩ := w
  let P : (Fin N → AF F) → ℂ := fun u => f (x, u) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ u)))
  have hPc : Continuous P := by
    refine (hf.comp (Continuous.prodMk continuous_const continuous_id)).mul (hψc.comp ?_)
    refine (continuous_const.mul ?_).neg
    fun_prop
  have hPper : ∀ (ξ : Fin N → F) u, P (rat ξ + u) = P u := fun ξ u => integrand_periodic hq x u ξ
  have hcoef : ∀ ξ : Fin N → F, ∫ u in 𝓓, P u * ψ (-(Bd (AF F) (half F N) u (rat ξ))) ∂(muV N ν) =
      invV ψ ν 𝓓 f (rat ξ + x) := by
    intro ξ
    unfold invV
    congr 1
    funext u
    have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
    have h := hq ξ 0 (x, u)
    rw [h0, Prod.mk_add_mk, zero_add] at h
    rw [h, Bd_half]
    simp only [P]
    rw [mul_assoc, ← AddChar.map_add_eq_mul, mul_comm (ψ _) (f _), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [symV, add_dotProduct, dotProduct_zero, sub_zero, dotProduct_comm u (rat ξ)]
    linear_combination two_mul_invOf (rat ξ ⬝ᵥ u)
  have hsum : Summable (fun ξ : Fin N → F => ‖invV ψ ν 𝓓 f (rat ξ + x)‖) :=
    (GlobalTheory.decay_integrable_periodise F N hTR _ hdec).2.1 x
  have hser := GlobalTheory.SWQ.FourierSeries.fourier_series F N ψ lam ν (half F N) hC 𝓓 hD hD1 P
    (fun ξ => invV ψ ν 𝓓 f (rat ξ + x)) hPc hPper hcoef hsum y
  have hfxy : f (x, y) = P y * ψ (⅟(2 : AF F) * (x ⬝ᵥ y)) := by
    simp only [P, mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, mul_one]
  rw [hfxy, hser, ← tsum_mul_right]
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  refine tsum_congr fun ξ => ?_
  show ψ (rat ξ ⬝ᵥ y + ⅟(2 : AF F) * (x ⬝ᵥ y)) * invV ψ ν 𝓓 f (rat ξ + x) = _
  rw [Bd_half, AddChar.map_add_eq_mul, dotProduct_comm y (rat ξ)]
  ring

end GlobalTheory.ThetaTransform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodicStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, Continuous f → QuasiV ψ f → Decay (invV ψ ν 𝓓 f) → thV ψ (invV ψ ν 𝓓 f) = f := by
  first | exact @GlobalTheory.ThetaTransform.thV_invV_eq | exact GlobalTheory.ThetaTransform.thV_invV_eq | (intros; apply GlobalTheory.ThetaTransform.thV_invV_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftUnitTimesCoord
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem unit_mul_logarithmic_lift (p : ℕ) {Kt : Type} [CommRing Kt] (At : Subring Kt)
    (F : Kt →+* Kt) (v v' t : Kt) (_hp : (p : Kt) * p = 0) (hv' : v' ∈ At) (hvv : v * v' = 1)
    (hF : ∃ w ∈ At, F v = v ^ p + p * w) (ht : F t = t ^ p) :
    ∃ w ∈ At, F (v * t) = (v * t) ^ p * (1 + p * w) := by
  obtain ⟨w, hw, hFv⟩ := hF
  refine ⟨v' ^ p * w, At.mul_mem (At.pow_mem hv' p) hw, ?_⟩
  have h1 : v ^ p * v' ^ p = 1 := by rw [← mul_pow, hvv, one_pow]
  rw [map_mul, hFv, ht, mul_pow]
  linear_combination (-(t ^ p * p * w)) * h1

end GlobalTheory.DI
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI


open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
end
