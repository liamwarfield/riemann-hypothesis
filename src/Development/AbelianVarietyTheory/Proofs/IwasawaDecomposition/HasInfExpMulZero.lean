module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentVacuumHyperspecialDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InnerSteps

variable {D : D7}

theorem hasInfQ_tauE {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => ?_⟩
  rw [h k]
  exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem hasInfExp_mul_zero {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ 0) : HasInfExp D (χ * η) τ a := by
  obtain ⟨n, hn, h1, h2⟩ := hχ
  obtain ⟨m, hm, -, h3⟩ := hη
  have hm0 : m = 0 := by exact_mod_cast hm.trans (mul_zero _)
  refine ⟨n, hn, h1, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h2 θ hθ x hx hτ, h3 θ hθ x hx hτ, hm0, zpow_zero, mul_one]

theorem exp_chrStep {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tauE (L.C.isMu0 k).inf) τ
  simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
  have h2 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
    (hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  haveI : IsTotallyComplex D.host.E := by infer_instance
  have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
    ⟨fun _ => 0, fun _ => by norm_num, fun x => by
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
  have h4 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hasInfExp_mul_zero h1 h3
  unfold Lift.chrStep
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, (exp_of_even hk τ).1, (exp_of_even hk τ).2]
    exact ⟨hasInfExp_div h4 h2, h4⟩
  · rw [if_neg (fun h => hk (by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using h)), (exp_of_odd hk τ).1,
      (exp_of_odd hk τ).2]
    exact ⟨h4, hasInfExp_div h4 h2⟩

theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem sum_mul_idem {R ι : Type} [CommRing R] (p : ι → R) (s : Finset ι) (h : ∀ i ∈ s, p i * p i = p i)
    (h0 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0) {i : ι} (hi : i ∈ s) : p i * (∑ i ∈ s, p i) = p i := by
  rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h0 i hi j hj hji) (fun h => absurd hi h), h i hi]

theorem resS_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hint, fun PP hP => ?_⟩
  obtain ⟨⟨es, hes, hsum⟩, hc⟩ := h
  have h1 : ∀ i ∈ P, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P h1 (hsum ▸ hc)
  have h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hcross i hi j hj) (hcross j hj i hi) hji
  have h3 : es PP * e = es PP := by
    rw [hsum]; exact sum_mul_idem (R := AE D) es P h1 h2 hP
  obtain ⟨h4, h5⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h6 : (⟨_, h4⟩ * ⟨_, hint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, h4⟩ :=
    Subtype.ext (by change toEAf D _ * toEAf D _ = toEAf D _; rw [← RingHom.map_mul, h3])
  have h7 := congrArg (resS D.host.F PP) h6
  rwa [map_mul, h5, one_mul] at h7

def rect (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rect {κ : Type} [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rect κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rect {κ : Type} [Zero κ] [One κ] {b a k : ℕ} (hb : k ≤ b) (ha : k ≤ a) : topL k (rect κ b a) = 1 := by
  ext i j
  unfold topL rect
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hb, lt_of_lt_of_le j.2 ha⟩, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_smul {R : Type} [CommRing R] {a b : ℕ} (p : GL (Fin a) R) (q : GL (Fin b) R) (c : R)
    (y z : Matrix (Fin b) (Fin a) R) (h : ∀ i j, z i j = c * (q.val * y * (p⁻¹).val) i j) (i : Fin b) (j : Fin a) :
    ((q⁻¹).val * z * p.val) i j = c * y i j := by
  have hz : z = c • (q.val * y * (p⁻¹).val) := Matrix.ext h
  rw [hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc q.val, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_rect (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D)) (βT : GL (Fin T.rank) (Datum.EAf D))
    {e : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rect _ _ _ := by
  obtain ⟨hi, hr⟩ := resS_idemSum h
  have he := GlobalTheory.PlaceDatum.idemSum_mul_self h
  choose s hs using toEAf_surjective (D := D)
  let x : Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    fun i j => e * s (HMul.hMul (HMul.hMul βT.val (rect (Datum.EAf D) T.rank S.rank)) (βS⁻¹).val i j)
  have hf : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := by
    intro i j
    refine (frame_smul βS βT (toEAf D e) (rect (Datum.EAf D) T.rank S.rank) (x.map (toEAf D)) (fun i j => ?_) i j).trans ?_
    · exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
    · rw [rect, mul_ite, mul_one, mul_zero]
  have hI : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hf]
    split_ifs
    · exact hi
    · exact zero_mem _
  refine ⟨x, fun i j => by simp only [x]; rw [← mul_assoc, he], hI, fun PP hP => ?_⟩
  ext i j
  refine (dif_pos (hI i j)).trans ?_
  unfold rect
  split_ifs with hij
  · rw [← hr PP hP]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_pos hij)))
  · rw [← map_zero (resS D.host.F PP)]
    exact congrArg _ (Subtype.ext ((hf i j).trans (if_neg hij)))

theorem omegaG_ne_zero {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ L.Pg, y PP = rect _ _ _) :
    omegaG L χ y ≠ 0 := by
  unfold omegaG
  split_ifs with h
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine absurd ⟨fun PP hP => ?_, fun _ => 1, fun PP => ?_, fun _ => one_mem _, ?_⟩ h
    · rw [hy PP hP]; exact lowZero_rect _ _ _
    · rw [hy PP.1 PP.2, topL_rect hab le_rfl, Units.val_one]
    · convert L.P.H.one_mem using 1
      funext PP
      exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_ne_zero {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hy : ∀ PP ∈ Q, y PP = rect _ _ _) :
    omegaQ Q r ξ k y ≠ 0 := by
  unfold omegaQ
  split_ifs with h
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · refine absurd (fun PP hP => ?_) h
    rw [hy PP hP, topL_rect hb ha, Matrix.det_one]
    exact ⟨lowZero_rect _ _ _, isUnit_one⟩

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (hr : S.rank ≤ T.rank) (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS dS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT dT) βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  obtain ⟨k1, k2⟩ := GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB
  rw [← hall Tm hTm] at k1 k2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 k1
  refine ⟨?_, k2 h0 fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2
  · obtain ⟨x, h1, h2, h3⟩ := exists_rect S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨h1, h2⟩] at this
    exact mul_ne_zero (omegaG_ne_zero hr L χ _ fun PP h => h3 PP ((hP PP).2 (Or.inl h)))
      (omegaQ_ne_zero L.hr (L.hr.trans hr) Q ξ 1 _ fun PP h => h3 PP ((hP PP).2 (Or.inr h))) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2

end GlobalTheory.InnerSteps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLift
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjDatumNe

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

def rectOne (R : Type) [Zero R] [One R] (b a : ℕ) : Matrix (Fin b) (Fin a) R :=
  fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rectOne (R : Type) [Zero R] [One R] (b a k : ℕ) : LowZero k (rectOne R b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rectOne (R : Type) [Zero R] [One R] {b a : ℕ} (h : a ≤ b) : topL a (rectOne R b a) = 1 := by
  ext i j
  have h1 : i.val < b ∧ j.val < a := ⟨by omega, j.2⟩
  unfold topL rectOne
  rw [dif_pos h1, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem sandwich_cancel' {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (c : R) (hA : A' * A = 1) (hG : G * G' = 1)
    (hB : B' * B = 1) (hH : H * H' = 1) : (A' * G') * (c • ((G * A) * N * (B' * H'))) * (H * B) = c • N := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have hH' : H' * H = 1 := mul_eq_one_comm.1 hH
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (A' * (G' * G) * A) * N * (B' * (H' * H) * B) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hG', hH', Matrix.mul_one, Matrix.mul_one, hA, hB, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add (f := _), hs, ht]⟩

theorem exists_half_frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (he : e * e = e) (I : Matrix (Fin S.rank) (Fin T.rank) (EAf D)) :
    ∃ x : WO S T, IsHalf (cA D e) x ∧ frMapAdj S T βS βT x = toEAf D e • I := by
  choose N hN using fun (i : Fin S.rank) (j : Fin T.rank) => toEAf_surjective
    (((S.gram.map (eToEAf D) * βS.val) * I * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) i j)
  refine ⟨Matrix.of fun j i => cA D (e * N i j), fun j i => ?_, ?_⟩
  · change cA D e * cA D (e * N i j) = cA D (e * N i j)
    rw [← RingHom.map_mul, ← mul_assoc, he]
  · rw [frMapAdj_eq, ← sandwich_cancel' _ _ _ _ _ _ _ _ I (toEAf D e) βS.inv_mul (gram_map_mul_inv S) βT.inv_mul
      (gram_map_mul_inv T)]
    congr 2
    refine Matrix.ext fun i j => ?_
    change cF D (toEAf D (cA D (e * N i j))) = toEAf D e * _
    rw [toEAf_cA, cF_cF_toEAf, RingHom.map_mul, hN]

theorem idemSum_res {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP ∈ P, Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := idemSum_mul_self h
  have hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hi, fun PP hPP => ?_⟩
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  have h3 : es PP * ∑ j ∈ P, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hPP
  rw [← h2] at h3
  obtain ⟨k, hk⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)
  have h4 : (⟨toEAf D (es PP), k⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D e, hi⟩ = ⟨toEAf D (es PP), k⟩ :=
    Subtype.ext (by change toEAf D (es PP) * toEAf D e = toEAf D (es PP); rw [← RingHom.map_mul, h3])
  have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
  rwa [RingHom.map_mul, hk, one_mul] at h5

theorem isIntM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b a : ℕ) :
    IsIntM (ε • rectOne (EAf D) b a) := by
  intro i j
  change ε * (if i.val = j.val then 1 else 0) ∈ _
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact zero_mem _

theorem redM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hi⟩ = 1) (b a : ℕ) :
    redM PP (ε • rectOne (EAf D) b a) = rectOne _ b a := by
  funext i j
  refine (dif_pos (isIntM_smul_rectOne hi b a i j)).trans ?_
  by_cases hij : i.val = j.val
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) (h.trans (if_pos hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = ε
    rw [if_pos hij, mul_one]
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) ((RingHom.map_zero _).trans (if_neg hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = 0
    rw [if_neg hij, mul_zero]

theorem exists_datum_ne_zero : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  intro D S T βS βT Pg Q P ξ e hr he hg hQ
  obtain ⟨x, hx, hx'⟩ := exists_half_frMapAdj S T βS βT (idemSum_mul_self he) (rectOne _ _ _)
  obtain ⟨hi, hres⟩ := idemSum_res he
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx']; exact isIntM_smul_rectOne hi _ _
  · have key : ∀ PP ∈ P, LowZero T.rank (redM PP (frMapAdj S T βS βT x)) ∧
        topL T.rank (redM PP (frMapAdj S T βS βT x)) = 1 := fun PP hPP => by
      rw [hx', redM_smul_rectOne hi PP (hres PP hPP)]
      exact ⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hr⟩
    refine mul_ne_zero ?_ ?_
    · unfold omegaK
      rw [if_pos fun PP hPP => key PP (hg PP hPP)]
      exact one_ne_zero
    · unfold omegaQ
      rw [dif_pos fun PP hPP => ⟨(key PP (hQ PP hPP)).1, by
        rw [(key PP (hQ PP hPP)).2, Matrix.det_one]; exact isUnit_one⟩]
      exact Finset.prod_ne_zero_iff.2 fun PP _ => zpow_ne_zero _ (Units.ne_zero _)

end GlobalTheory.AdjDatumNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonvanishingFiniteDatumDefiniteLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonvanishing_finite_datum_definite_lift : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  first | exact @GlobalTheory.AdjDatumNe.exists_datum_ne_zero | exact GlobalTheory.AdjDatumNe.exists_datum_ne_zero | (intros; apply GlobalTheory.AdjDatumNe.exists_datum_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelInj

theorem placeModel_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ hψ hS hT he hec hinf hTm hf hΦ h0 =>
    (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT he hec hinf hTm hΦ).2 hf h0

end GlobalTheory.PlaceModelInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerIntertwiner_injective_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → e * cA D e = 0 → infPart D e = 0 → IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → f₀ ≠ 0 → IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → Φ ≠ 0 → Tm Φ ≠ 0 := by
  first | exact @GlobalTheory.PlaceModelInj.placeModel_ne_zero | exact GlobalTheory.PlaceModelInj.placeModel_ne_zero | (intros; apply GlobalTheory.PlaceModelInj.placeModel_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActRep
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelMultiplicityFiniteGroupImage
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
  (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

abbrev MultP : Submodule ℂ (MMap M) := Mult θ M (levS V β (flag1L L)) (levChi V β (flag1L L))

variable {θ M β L}

theorem hasType {U : MMap M} (hU : U ∈ MultP θ M β L) (v : M.Vec) : HasType V β (flag1L L) (U v) :=
  fun κ hκ y => ((GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ U).1 hU).lev v κ hκ y

theorem isMultMap_translate {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T) {k : GA D V}
    (hk : k ∈ GfC V) : IsMultMap θ M ∅ χ (heckeOn M {k} T) := by
  have e : ∀ v, heckeOn M {k} T v = rTr V k (T v) := fun v => by
    funext g
    simp [heckeOn, postOn_apply, heckeLin_apply, rTr]
  refine ⟨fun v => ?_, fun v => ?_, fun v k hk => hk.elim, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
  · rw [e]
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V k hk _ (h.aut v)
  · rw [e]
    intro r C hC μ 𝓕 hμ h𝓕 g
    simp only [rTr, mul_assoc]
    exact h.cusp v r C hC μ 𝓕 hμ h𝓕 (g * k)
  · rw [e, e, h.equiv τ g hg v w hw]
    funext x
    unfold rTr
    rw [mul_assoc, mul_assoc, GlobalTheory.FinTranslate.comm_fin_real V hk (GlobalTheory.FinTranslate.atTau_mem θ V τ g)]
  · obtain ⟨ℓ, s, e'⟩ := h.cont τ v (x * k)
    exact ⟨ℓ, s, fun w => by rw [e, e']; rfl⟩

theorem exists_principalLevelMultiplicity_finiteGroup_image (g0 : G0 L.Pg L.r) (T : MMap M) (hT : T ∈ MultP θ M β L) :
    ∃ T' ∈ MultP θ M β L, ∀ v, T' v = actG0 V β L g0 (T v) := by
  by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hk.choose_spec
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT
    have hact : ∀ v, ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) v =
        actG0 V β L g0 (T v) := by
      intro v
      unfold actG0
      rw [dite_eq_left hk]
      funext g
      simp [heckeOn, postOn_apply, heckeLin_apply]
    have h0 : IsMultMap θ M ∅ (levChi V β (flag1L L))
        ((levChi V β (flagL L) hk.choose)⁻¹ • heckeOn M {hk.choose} T) := by
      rw [← GlobalTheory.MultMem.mem_mult_iff]
      exact Submodule.smul_mem _ _
        ((GlobalTheory.MultMem.mem_mult_iff ..).2 (isMultMap_translate hT hκ.1))
    refine ⟨_, Submodule.subset_span ⟨h0.aut, h0.cusp, fun v k hk' g => ?_, h0.equiv, h0.cont⟩, hact⟩
    rw [hact]
    exact GlobalTheory.FlagAction.act_hasType (fun k hk => hT.lev v k hk) hk k hk' g
  · refine ⟨0, Submodule.zero_mem _, fun v => ?_⟩
    unfold actG0
    rw [dite_eq_right hk]
    rfl

theorem act_mem (g : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L g) U ∈ MultP θ M β L := by
  obtain ⟨U', h1, h2⟩ := exists_principalLevelMultiplicity_finiteGroup_image g U hU
  have h : postOn M (actL V β L g) U = U' := MultilinearMap.ext fun v => (h2 v).symm
  rw [h]
  exact h1

theorem act_one {U : MMap M} (hU : U ∈ MultP θ M β L) : postOn M (actL V β L 1) U = U :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_one (hasType hU v)

theorem act_mul (hl : LiftsExist V β L) (g g' : G0 L.Pg L.r) {U : MMap M} (hU : U ∈ MultP θ M β L) :
    postOn M (actL V β L (g * g')) U = postOn M (actL V β L g) (postOn M (actL V β L g') U) :=
  MultilinearMap.ext fun v => GlobalTheory.FlagAction.act_mul (hasType hU v) (hl g) (hl g')

variable {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r)

theorem postOn_gaL (c : G → ℂ) (U : MMap M) :
    postOn M (gaL V β L eG c) U = ∑ g, c g • postOn M (actL V β L (eG g)) U := by
  refine MultilinearMap.ext fun v => ?_
  simp only [gaL, postOn, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compMultilinearMap_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply, MultilinearMap.smul_apply]

theorem gaL_act (hl : LiftsExist V β L) {c : G → ℂ} (hc : ∀ g a, c (g * a * g⁻¹) = c a) (g : G) {U : MMap M}
    (hU : U ∈ MultP θ M β L) :
    postOn M (gaL V β L eG c) (postOn M (actL V β L (eG g)) U) =
      postOn M (actL V β L (eG g)) (postOn M (gaL V β L eG c) U) := by
  have hm : ∀ a b : G, postOn M (actL V β L (eG a)) (postOn M (actL V β L (eG b)) U) =
      postOn M (actL V β L (eG (a * b))) U := fun a b => by
    rw [map_mul]
    exact (act_mul hl _ _ hU).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [postOn_gaL, postOn_gaL, map_sum]
  simp only [map_smul, hm]
  refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun a => ?_).symm
  show _ = c (g * a * g⁻¹) • postOn M (actL V β L (eG (g * a * g⁻¹ * g))) U
  rw [hc, inv_mul_cancel_right]


end GlobalTheory.MultAction

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultAction

theorem actRep : ∀ D : D7, ActRep D := by
  intro D V β L S θ M hl hP
  have e : Formalism.IndefR.Lev.flag1L L = L := by
    rw [flag1L, withP, ← hP]
  have hM : Mult θ M (levS V β L) (levChi V β L) = MultP θ M β L := by
    rw [MultP, e]
  rw [hM]
  refine ⟨fun g T hT => act_mem g hT, fun T hT => act_one hT, fun g h T hT => act_mul hl g h hT, ?_⟩
  intro G _ _ eG c hc g T hT
  have h := gaL_act eG hl (c := c) (fun a b => hc a b) (eG.symm g) hT
  rwa [MulEquiv.apply_symm_apply] at h

end GlobalTheory.MultAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinksInputs

theorem inputs_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  intro hW _ hH hC D
  obtain ⟨hcart, hsd, hsp, hdim, hpet, hsm⟩ := GlobalTheory.Mem.EasyInputs.easy_inputs D
  exact
    { weil := Formalism.IndefR.WeilFull.weilExistsFull_of (hW D) (GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places D) (GlobalTheory.T.weilDatum_realDerivative_fockVectors_all D)
      vac := GlobalTheory.Member.vacuum_oriented_exists D
      stepVec := GlobalTheory.PlaceDatum.stepVecExists D
      thPVec := GlobalTheory.PlaceVec.thPVecExists D
      ptStable := GlobalTheory.T.fockPolynomialVectors_of_smoothTheta_stable D
      cartan := hcart
      selfDual := hsd
      vecTheta := GlobalTheory.T.chainStepVectors_and_adjointVectors_areTheta D
      measFD := Formalism.IndefR.Eqv.measFDExists_holds D
      measDef := Formalism.IndefR.Eqv.measLevDefExists_holds D
      fund := Formalism.IndefR.Eqv.fundDomExists_holds D
      sp := hsp
      lev := GlobalTheory.Mem.LevelOK.levOK_all D
      hc := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
      schur := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
      pet := hpet
      sm := hsm
      dim := hdim
      act := GlobalTheory.MultAction.actRep D }

end GlobalTheory.LinksInputs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandraStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linksAnalyticHypotheses_of_weilRep_harishChandra : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, Inputs D := by
  first | exact @GlobalTheory.LinksInputs.inputs_of_hypotheses | exact GlobalTheory.LinksInputs.inputs_of_hypotheses | (intros; apply GlobalTheory.LinksInputs.inputs_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.LiftInertChi


open GlobalTheory.FinZeta.LevelOff in
theorem redFn_eq_one_of_locAt {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (x : Bridge.Gf V)
    (hS : Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∈ Formalism.L2.DIV.St β)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) :
    Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) = 1 := by
  classical
  set M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val with hM
  set Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)) := {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} with hSb
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  have hz : ∀ (i j : Fin V.rank), ∀ w ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w)
      (AlgHom.id D.host.F D.host.E) ((M - 1) i j) = 0 := by
    intro i j w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have h1 := congrFun (congrFun (hx ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) hPP) i) j
    rw [Matrix.map_apply] at h1
    rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hSb]
  · ext i j
    have h2 := one_sub_ind_tmul_mul Sb _ (hz i j)
    have e1 : ((Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).val - 1) i j =
        swapAE D ((M - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact (RingHom.map_one _).symm
      · exact (RingHom.map_zero _).symm
    rw [Matrix.smul_apply, smul_eq_mul, e1]
    show swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul, h2]

theorem locAt_of_isLocElt {D : D7} (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (x : Bridge.Gf V)
    (h : Formalism.IndefR.Links.IsLocElt V P x) : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (P.under (𝓞 D.host.F)) x := by
  obtain ⟨e, f, g, hpi, hg, hx, hs⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi
  have h1 := (GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp] at h1
  have h2 : GlobalTheory.HeckeRowsCompare.fin V g = x := Subtype.ext hx.symm
  rw [h2] at h1
  exact (GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1

theorem levChi_eq_one_of_isLocElt : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
  set Q0 : Formalism.L2.DIV.Pl X.toD7.host.E := (q.1.1 : PlI X.B px).1 with hQ0
  have e : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t))
      (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) := rfl
  have hm : Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1 ∈
      Formalism.L2.DIV.lev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (flag1L (L.datVt i t)) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := locAt_of_isLocElt (Vc X.toD7 i) _ _ hj

  have hoff : Q0 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    have h := q.1.2
    exact fun hm => h (Or.inr hm)
  have hconj : Formalism.DivisionValues.conjPl Q0 = Q0 := by
    rw [← GlobalTheory.PlaceDict.conjP_eq_conjPl X.toD7]
    exact (q.1.1 : PlI X.B px).2.1
  have hunder : ∀ PP : Formalism.L2.DIV.Pl X.toD7.host.E, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 →
      PP.under (𝓞 X.toD7.host.F) ≠ Q0.under (𝓞 X.toD7.host.F) := by
    intro PP hPP hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
    · exact hoff (h ▸ hPP)
    · exact hoff ((h.trans hconj) ▸ hPP)
  have hred : ∀ PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Formalism.L2.DIV.redFn (L.βV i) PP (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 :=
    fun PP hPP => redFn_eq_one_of_locAt _ _ hSt _ hloc PP (hunder PP hPP)
  have hPg : ∀ PP ∈ (flag1L (L.datVt i t)).Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L (L.datVt i t)).Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)
  have hr1 : Formalism.L2.DIV.rTup (L.βV i) (flag1L (L.datVt i t)) (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (hPg PP.1 PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (hQ PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (hPg PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

end GlobalTheory.Mem.R3.LiftInertChi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChar_eq_one_inert_prime_off_level : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  first | exact @GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | exact GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt | (intros; apply GlobalTheory.Mem.R3.LiftInertChi.levChi_eq_one_of_isLocElt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SphLoc

section Alg
variable {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

theorem fixed_ne_bot_of_mem_iSup {ι : Type} [Finite ι] {σ : Representation ℂ G V} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X}
    (hf : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap) (hf0 : f ≠ 0) (hK : ∀ k ∈ K, ρ k f = f) :
    GlobalTheory.PRep.fixed σ K ≠ ⊥ :=
  GlobalTheory.T.fixedVectors_ne_bot_of_mem_sum_intertwining_ranges hσ T K hf hf0 hK

end Alg

section Val
open ValuativeRel Filter Topology

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') := by
  refine (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun y hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push Not at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push Not at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

end Val

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_Umax_of_mem_KO (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hi : Continuous i) (x : GAf L n)
    (hx : TrivOutside {s.v} x)
    (hk : Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) ∈ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n)) :
    x ∈ Umax L n := by
  have key : ∀ y, ValuativeRel.valuation _ (i y) ≤ 1 → Valued.v y ≤ 1 := fun y hy =>
    (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (le_one_of_map i.toRingHom hi hy)
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hk
  refine GlobalTheory.TSetFin.mem_Umax_of_loc s x hx (fun a b => key _ (hk.1 a b)) (fun a b => key _ (by
    have h2 := hk.2 a b
    rw [← map_inv, ← map_inv] at h2
    exact h2))

theorem isSpherical_of_sphAt (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) (hs : π.SphAt s.v) :
    GlobalTheory.SmGL.IsSpherical σ.ρ := by
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose lift hlift using fun A => (hI.2.2 A).exists
  have huniq : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (hI.2.2 A).unique ⟨hx, e⟩ (hlift A)
  have hmul : ∀ A B, lift (A * B) = lift A * lift B := fun A B =>
    (huniq _ _ (GlobalTheory.TSetFin.triv_mul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm
  have htriv1 : TrivOutside {s.v} (1 : GAf L n) := by
    intro v _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hone : lift 1 = 1 := (huniq _ _ htriv1 (map_one _)).symm
  let e : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (lift (e g))) = g := fun g => by
    rw [(hlift _).2]
    exact Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let ρX : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → π.W) :=
    { toFun := fun g => NG.rt L n (lift (e g))
      map_one' := by
        simp only [map_one, hone]
        ext φ x
        simp [NG.rt]
      map_mul' := fun g h => by
        simp only [map_mul, hmul]
        ext φ x
        simp [NG.rt, mul_assoc] }
  have hiso : f ∈ NG.isoTyp π.ρ π.S := by
    unfold NG.isoTyp
    exact Submodule.mem_sSup_of_mem (show π.S ∈ {S' | NG.IsIrrRep π.ρ S' ∧ NG.IsoRep π.S S'} from
      ⟨π.irrS, LinearEquiv.refl ℂ _, fun _ _ _ e => e⟩) hf
  have h1 := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n π.toAlgWt π.S π.irrS s σ hσ i hi hic hiso
  rw [iSup_subtype', Submodule.mem_iSup_iff_exists_finset] at h1
  obtain ⟨t, ht⟩ := h1
  rw [iSup_subtype'] at ht
  let Tm : {j // j ∈ t} → σ.ρ.IntertwiningMap ρX := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => by
      have := j.1.2.2 (lift (e g)) (hlift _).1 a
      rw [hloc] at this
      exact this⟩
  refine fixed_ne_bot_of_mem_iSup σ.irr Tm (GlobalTheory.SplitWeil.KO _ (Fin n)) ht hf0 fun k hk => ?_
  show NG.rt L n (lift (e k)) f = f
  exact hfix _ (mem_Umax_of_mem_KO s i hi _ (hlift _).1 (by rw [hloc]; exact hk)) (hlift _).1

end

end GlobalTheory.SphLoc

end

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end
