module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.StepVac

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7}

theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem map_sum_mem {R R' ι : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Subring R') (p : ι → R) (s : Finset ι)
    (h : ∀ i ∈ s, f (p i) ∈ A) : f (∑ i ∈ s, p i) ∈ A := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]; exact sum_mem h

theorem res_ite {R κ : Type} [CommRing R] [CommRing κ] (A : Subring R) (f : A →+* κ) {c z : R} (hc : c ∈ A) (hz : z ∈ A)
    (h1 : f ⟨c, hc⟩ = 1) (p : Prop) [Decidable p] (h : z = if p then c else 0) : f ⟨z, hz⟩ = if p then 1 else 0 := by
  split_ifs at h ⊢
  · subst h; exact h1
  · subst h; exact f.map_zero

theorem res_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) :
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ P, resS D.host.F PP ⟨toEAf D e, h⟩ = 1 := by
  have hee := idemSum_mul_self he
  obtain ⟨⟨es, hes, hs⟩, hc⟩ := he
  choose hi h1 using fun PP hP => GlobalTheory.IdemRes.resS_idem_eq_one D (es PP) PP (hes PP hP)
  have h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hs]; exact map_sum_mem (toEAf D) _ es P hi
  refine ⟨h, fun PP hP => ?_⟩
  have hcross := cross_eq_zero (R := AE D) isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) (hs ▸ hc)
  have hm : e * es PP = es PP := by
    rw [hs, Finset.sum_mul, Finset.sum_eq_single PP (fun j hj hji =>
      idemAt_mul (hes j hj) (hes PP hP) (hcross j hj PP hP) (hcross PP hP j hj) hji.symm) (fun h => absurd hP h)]
    exact (hes PP hP).1.1
  have : (⟨toEAf D e, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D (es PP), hi PP hP⟩ =
      ⟨toEAf D (es PP), hi PP hP⟩ := Subtype.ext ((RingHom.map_mul _ _ _).symm.trans (congrArg _ hm))
  have h2 := congrArg (resS D.host.F PP) this
  rwa [RingHom.map_mul, h1 PP hP, mul_one] at h2

def rectOne (κ : Type) [Zero κ] [One κ] (b a : ℕ) : Matrix (Fin b) (Fin a) κ := fun i j => if i.val = j.val then 1 else 0

theorem lowZero_rectOne (κ : Type) [Zero κ] [One κ] (b a k : ℕ) : LowZero k (rectOne κ b a) :=
  fun i j hi hj => if_neg (by omega)

theorem topL_rectOne (κ : Type) [Zero κ] [One κ] {b a k : ℕ} (ha : k ≤ a) (hb : k ≤ b) : topL k (rectOne κ b a) = 1 := by
  ext i j
  rw [topL, dif_pos ⟨by omega, by omega⟩, rectOne, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem frame_cancel {A : Type} [CommRing A] {a b : ℕ} (βS : GL (Fin a) A) (βT : GL (Fin b) A) (c : A)
    (I : Matrix (Fin b) (Fin a) A) : (βT⁻¹).val * (c • (βT.val * I * (βS⁻¹).val)) * βS.val = c • I := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem exists_point (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {e : AE D}
    {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : ∃ x : WO S T, IsHalf e x ∧ IsIntM (frMapO S T βS βT x) ∧
      ∀ PP ∈ P, redM PP (frMapO S T βS βT x) = rectOne _ _ _ := by
  obtain ⟨h, h1⟩ := res_idemSum he
  choose s hs using toEAf_surjective (D := D)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin T.rank) (Fin S.rank) (EAf D), ∀ c : EAf D,
      HMul.hMul (HMul.hMul (βT⁻¹).val (c • M)) βS.val = c • rectOne (EAf D) T.rank S.rank := ⟨_, fun c => frame_cancel βS βT c _⟩
  let x : WO S T := fun i j => e * s (M i j)
  have hx : frMapO S T βS βT x = toEAf D e • rectOne (EAf D) T.rank S.rank := by
    rw [← hM]
    unfold frMapO
    congr 2
    ext i j
    exact (RingHom.map_mul _ _ _).trans (congrArg _ (hs _))
  have hx' : ∀ i j, frMapO S T βS βT x i j = if i.val = j.val then toEAf D e else 0 := fun i j => by
    rw [hx, Matrix.smul_apply, rectOne, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hi : IsIntM (frMapO S T βS βT x) := fun i j => by
    rw [hx']
    split_ifs
    exacts [h, zero_mem _]
  refine ⟨x, fun i j => by rw [← mul_assoc, idemSum_mul_self he], hi, fun PP hP => ?_⟩
  ext i j
  exact (dif_pos (hi i j)).trans (res_ite _ (resS D.host.F PP) h (hi i j) (h1 PP hP) _ (hx' i j))

theorem omegaG_rectOne {a b : ℕ} (hab : a ≤ b) (L : LevDat D.host.E ℂ a) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    omegaG L χj (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaG
  rw [dif_pos]
  · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) ?_
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
    · exact Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero (Units.ne_zero _)
  · refine ⟨fun PP _ => lowZero_rectOne _ _ _ _, fun _ => 1, fun PP => (topL_rectOne _ le_rfl hab).symm,
      fun PP => Subgroup.one_mem _, ?_⟩
    convert L.P.H.one_mem using 1
    funext PP
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem omegaQ_rectOne {a b r : ℕ} (ha : r ≤ a) (hb : r ≤ b) (Q : Finset (Pl D.host.E))
    (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) : omegaQ Q r ξ k (fun PP => rectOne (kP PP) b a) ≠ 0 := by
  unfold omegaQ
  rw [dif_pos]
  · exact Finset.prod_ne_zero_iff.2 fun _ _ => zpow_ne_zero _ (Units.ne_zero _)
  · intro PP _
    refine ⟨lowZero_rectOne _ _ _ _, ?_⟩
    rw [topL_rectOne _ ha hb, Matrix.det_one]
    exact isUnit_one

theorem stepVec_vac {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)} {LS : LevDat D.host.E ℂ S.rank}
    {χj ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hr : S.rank ≤ T.rank)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) :
    IsThetaFunO ψ S T f ∧ f ≠ 0 ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  classical
  obtain ⟨hf, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have hinf := infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) βS βT
  obtain ⟨h1, h2⟩ := placeModel_span_ne hf.1 hS hT (idemSum_mul_self he) he.2 hinf hTm
    (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ _
      (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
        rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
          omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
  rw [← hall Tm hTm] at h1 h2
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h1
  refine ⟨?_, h2 ?_ fun hz => ?_, fun τ => ?_⟩
  · rw [← hc]
    exact GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hf.1.1 f₀ hf.2.theta _ c.support Subtype.val c fun i _ => i.2
  · rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hf.2.norm
    have := h2 p hp
    simp [nrm2] at this
  · obtain ⟨x, a1, a2, a3⟩ := exists_point S T βS βT he
    have := congrFun hz x
    rw [if_pos ⟨a1, a2⟩, omegaG_congr LS χj _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_left _ hP), omegaQ_congr Q LS.r ξ 1 _ (fun PP => rectOne (kP PP) _ _) fun PP hP =>
      a3 PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (omegaG_rectOne hr LS χj) (omegaQ_rectOne LS.hr (LS.hr.trans hr) Q ξ 1) this
  · rw [← hc]
    exact GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hf.1.1 hf.2.inf f₀ hf.2.theta τ _ (hf.2.fock τ) _ c.support
      Subtype.val c fun i _ => i.2

theorem hasInfExp_mul {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ b) : HasInfExp D (χ * η) τ (a + b) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  obtain ⟨m, hm, -, h2⟩ := hη
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  have hu : θ τ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map (θ τ)).ne_zero
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hx', h2 θ hθ x hx hx',
    zpow_add₀ (div_ne_zero hu (by exact_mod_cast norm_ne_zero_iff.2 hu))]

theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := hχ
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hx' => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hx', zpow_neg]

theorem hasInfExp_of_order {θ : InfFam D} (hθ : IsInfFam θ) {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : ChrEq c χ) {n : ℕ} (hn : 0 < n) (ho : χ.OrderDvd n) (τ : D.what₂.Tau) : HasInfExp D c τ 0 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  refine ⟨0, by simp, ⟨θ, hθ⟩, fun θ _ x hx _ => ?_⟩
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [zpow_zero, map_pow, show c y ^ n = 1 from key y, Circle.coe_one]

theorem hasInfQ_tau {χ : Formalism.L2.Host.HChar D.host.E} {a : D.R.Psi → ℚ}
    (h : χ.HasInfQ (Formalism.L2.Host.embPsi D.host) a) : χ.HasInfQ (tauE D) fun τ => a (D.eTau τ) := by
  obtain ⟨n, hn, h⟩ := h
  exact ⟨fun τ => n (D.eTau τ), fun τ => hn _, fun k => (h k).trans (D.eTau.prod_comp _).symm⟩

theorem chrStep_exp {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {θ : InfFam D} (hθ : IsInfFam θ) (t : T)
    (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).1 τ (expS D k τ) ∧
      HasInfExp D (Lift.chrStep (L.mu t) L.eta ((k : ℕ) + 1)).2 τ (expT D k τ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := by
    have := hasInfExp_mul (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (hasInfQ_tau (L.C.isMu0 k).inf) τ)
      (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
    rwa [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  have h2 : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta (hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have h3 := hasInfExp_mul h1 (hasInfExp_inv h2)
  unfold Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem rank_Yc {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := by
  rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl

theorem stepsOK : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωY → R.chain_ωX → R.chain_vY → R.chain_vX → StepsOK R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hθ hωY hωX hvY hvX
  refine ⟨fun t k hk => ⟨⟨_, _, hωY t k hk, chrStep_exp hL hθ t k⟩, ?_⟩, fun t k hk => ⟨⟨_, _, hωX t, fun τ => ?_⟩, ?_⟩⟩
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY k k.2)) (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY _ hk))
      (by rw [rank_Yc k.2.le, rank_Yc hk.le]; nlinarith) (hvY t k hk)
    exact ⟨a, b, c⟩
  · have := chrStep_exp hL hθ t k τ
    rwa [show (k : ℕ) + 1 = D.R.m by have := k.2; omega] at this
  · obtain ⟨a, b, c⟩ := stepVec_vac (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY (D.R.m - 1) (hk ▸ k.2)))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX) (by
        rw [rank_Yc (Nat.sub_le _ _), D.sp.X'_rank]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _) (hvX t)
    exact ⟨a, b, c⟩

end GlobalTheory.Chain.StepVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipMatch

section Generic

def pairM {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) : k := ∑ i, ∑ j, X i j * Y i j

def chart {k k' A C A' C' : Type} [Field k] [Field k'] [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    (j : k ≃+* k') (eA : A ≃ A') (eC : C ≃ C') (g : GL A k') (h : GL C k') (X : Matrix A C k) : Matrix A' C' k' :=
  reindex eA eC (g.val * X.map j * h.val)

def IsLocIso {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    (j : k ≃+* k') : Prop :=
  Continuous j ∧ Continuous j.symm ∧ ∀ x, j x ∈ (ValuativeRel.valuation k').integer ↔ x ∈ (ValuativeRel.valuation k).integer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coX {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

def coY (σ : E →ₐ[F] E) {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (Y.J.map t)ᵀ * c.1)

def IsMixChart {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (A A' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    {k R C : Type} [Add k] [Zero k] (co tr mu : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix R C k) (P : Finset C) : Prop :=
  (∀ u ∈ A, At (evFin F v) u ∧ (∀ r, ∀ s ∈ P, tr u r s = 0) ∧ (∀ r, ∀ s ∉ P, mu u r s = 0) ∧ co u = tr u + mu u) ∧
    ∀ u ∈ A', At (evFin F v) u ∧ (∀ r, ∀ s ∉ P, tr u r s = 0) ∧ ∀ r, ∀ s ∈ P, mu u r s = 0

end Generic

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def mixHalfS {i j : ℕ} (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (spW₁ G i j) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCoS (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨i.2.le, j.2⟩ ⟨i.2.le, j.2.le⟩
      ((mulG (spW₁ G i j) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨i.2.le, j.2.le⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def colsEq (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E) :
    Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ (locGrid G t w).Cols i j :=
  e.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))


variable (G) in
theorem rankW (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW G i j).rank = (locGrid G t w).rank (i + 1, j + 1) := by
  rw [rank_vertex G t w (X := ((i : ℕ) + 1, (j : ℕ) + 1)) ⟨Nat.succ_le_of_lt i.2, Nat.succ_le_of_lt j.2⟩]


variable (G) in
theorem rankW₁ (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) : (spW₁ G i j).rank = (locGrid G t w).rank (i, j) := by
  rw [rank_vertex G t w (X := ((i : ℕ), (j : ℕ))) ⟨le_of_lt i.2, le_of_lt j.2⟩]

def IsPlaceIso {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (j : Fv D.host.F v ≃+* Kw w) : Prop :=
  ∀ a : AE D, j (piW τ a) = cpt w (toEAf D a)

def xiAt (w : Pl D.host.E) : Kw w := algebraMap D.host.E (Kw w) D.host.xi0

def basCols (B : Frames G) {i j : ℕ} (e : Num G i j) (w : Pl D.host.E) :
    Matrix (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
  GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val)

def IsDoublyCompatible (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  IsTied t i j e Bs Γ X ∧ Γ.V'.L = GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid i j))

end Grid

end GlobalTheory.FlipMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable section
namespace GlobalTheory.MovedDict
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {U : Set T}

def frS (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pS p).rank) D.host.E
  | .chi i j => N.fr (.grid (i + 1) j)
  | .mu _ i j => N.fr (.grid i j)
  | .core i => N.fr (.core (i + 1))
  | .top _ j => N.fr (.top j)

def frT (N : Std G U) : ∀ p : GlobalTheory.ChiGrid.Pair T, GL (Fin (G.pT p).rank) D.host.E
  | .chi i j => N.fr (.grid i j)
  | .mu _ i j => N.fr (.grid i (j + 1))
  | .core i => N.fr (.core i)
  | .top _ j => N.fr (.top (j + 1))

def inV {n : ℕ} (B : GL (Fin n) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  (B : Matrix (Fin n) (Fin n) D.host.E).mulVec '' (Λ : Set (Fin n → D.host.E))

end GlobalTheory.MovedDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjReading

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

private theorem tieIn_of_fwTie' (fw : FWTie T R κ v₀) : TieIn T R κ v₀ :=
  ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

private theorem pb_eq_of_omPins (hL : R.toLevCh.Is A.μ0) (fw : FWTie T R κ v₀) (i : Fin D.R.m)
    (hOi : OMPins T R κ v₀ O i) : T.pb = R.C.P.pb :=
  GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hL (hOi.2.tuple ()).half

private theorem jEvExists_and_jEvBar_of_isEmpty (hm : IsEmpty (Fin D.R.m)) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  constructor
  · intro i
    exact hm.elim i
  · intro i
    exact hm.elim i

theorem jEvExists_and_jEvBar (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ ∧ JEvBar T R κ := by
  rcases isEmpty_or_nonempty (Fin D.R.m) with hm | hne
  · exact jEvExists_and_jEvBar_of_isEmpty T R κ v₀ hm
  · obtain ⟨i⟩ := hne
    have htie := tieIn_of_fwTie' T R κ v₀ fw
    have hpb := pb_eq_of_omPins T R κ v₀ O hL fw i (hO i)
    exact GlobalTheory.CuspValues.jEvExists_and_jEvBar _ _ _ _ _ T R κ v₀ hL hM htie hpb

theorem jEvExists (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (fw : FWTie T R κ v₀)
    (hO : ∀ i, OMPins T R κ v₀ O i) : JEvExists T R κ v₀ := by
  obtain ⟨hJ, -⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hJ

theorem jEvBar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → R.IsModels → FWTie T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → JEvBar T R κ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hM fw hO
  obtain ⟨-, hB⟩ := jEvExists_and_jEvBar T R κ v₀ O hL hM fw hO
  exact hB

end GlobalTheory.ConjReading
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrMove

open GlobalTheory.SplitHecke GlobalTheory.AdelicLatMove

variable {D : D7} {S T : HSp D}

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  show _ * (x + y) * _ = _ * x * _ + _ * y * _
  rw [Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

private lemma isHalf_iff_smul_eq {e : AE D} (u : WO S T) : IsHalf e u ↔ e • u = u := by
  unfold IsHalf
  constructor
  · intro hu
    apply Matrix.ext
    intro i j
    change e * u i j = u i j
    exact hu i j
  · intro hu i j
    have h := congrFun (congrFun hu i) j
    change e * u i j = u i j at h
    exact h

private lemma isHalf_actO_twisted_operators {e : AE D} (g : GA D S) (h : GA D T) {u : WO S T} (hu : IsHalf e u) :
    IsHalf e (actO S T g h u) := by
  rw [isHalf_iff_smul_eq] at hu ⊢
  unfold actO
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hu]

private lemma actO_inv_actO_twisted_operators (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g⁻¹ h⁻¹ (actO S T g h u) = u := by
  unfold actO
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (u : WO S T) :
    IsHalf e (actO S T g h u) ↔ IsHalf e u := ⟨fun hu => by simpa only [actO_inv_actO_twisted_operators] using isHalf_actO_twisted_operators g⁻¹ h⁻¹ hu, isHalf_actO_twisted_operators g h⟩

theorem isSBHalf_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) :
    IsSBHalf e Λ fun t => Ψ (actO S T g h t) := by
  obtain ⟨hsupp, k, hk, hper, hden⟩ := hΨ
  refine ⟨fun t ht => (isHalf_actO_iff g h t).1 (hsupp _ ht), k, hk, ?_, fun t ht => ?_⟩
  · intro u hu hue t
    show Ψ (actO S T g h (t + k • u)) = Ψ (actO S T g h t)
    rw [actO_add, actO_nsmul]
    exact hper _ ((hΛ u).1 hu) ((isHalf_actO_iff g h u).2 hue) _
  · rw [hΛ, actO_nsmul]
    exact hden _ ht

theorem halfInd_comp {e : AE D} {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (t : WO S T) : halfInd e Λ (actO S T g h t) = halfInd e Λ t := by
  unfold halfInd
  have hc : (actO S T g h t ∈ Λ ∧ IsHalf e (actO S T g h t)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
    rw [← hΛ t, isHalf_actO_iff]
  by_cases ht : t ∈ Λ ∧ IsHalf e t
  · rw [if_pos (hc.2 ht), if_pos ht]
  · rw [if_neg (fun h' => ht (hc.1 h')), if_neg ht]

theorem heisO_smul' (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  unfold heisO
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_move {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {a : AE D}
    {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T} (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm)
    (hth : ∀ Ψ, IsSBHalf a Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) {c : ℂ} (hc : c ≠ 0) (h0 : om (g, h) f₀ = c • f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀
      (c⁻¹ • (om (g, h) ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (actO S T g h))) := by
  obtain ⟨htr, hmod, hvac⟩ := hTm
  have hSB : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf a Λ fun t => Φ (actO S T g h t) := fun Φ hΦ => isSBHalf_comp hΛ hΦ
  have hback : ∀ w : WO S T, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa only [inv_inv] using actO_inv_actO g⁻¹ h⁻¹ w
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · have hx' : IsHalf a (actO S T g⁻¹ h⁻¹ x) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hx)
    have e1 : Tm (fun s => Φ (actO S T g h s + x)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ x) (Tm fun s => Φ (actO S T g h s)) := by
      have := htr _ (hSB Φ hΦ) _ hx'
      simpa only [actO_add, hback] using this
    show c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s + x))) =
      heisO ψ S T x (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e1, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have hy' : IsHalf (cA D a) (actO S T g⁻¹ h⁻¹ y) := (isHalf_actO_iff g h _).1 (by rw [hback]; exact hy)
    have e2 : Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s)) =
        heisO ψ S T (actO S T g⁻¹ h⁻¹ y) (Tm fun s => Φ (actO S T g h s)) := by
      rw [← hmod _ (hSB Φ hΦ) _ hy']
      congr 1
      funext s
      rw [← symplO_actO S T g h s (actO S T g⁻¹ h⁻¹ y), hback]
    show c⁻¹ • om (g, h) (Tm (fun s => ψ (symplO S T (actO S T g h s) y) * Φ (actO S T g h s))) =
      heisO ψ S T y (c⁻¹ • om (g, h) (Tm (fun s => Φ (actO S T g h s))))
    rw [e2, hW.om_heis g h _ _ (hth _ (hSB Φ hΦ)), hback, heisO_smul']
  · have e3 : (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s)) = (1 : ℂ) • halfInd a Λ := by
      funext s
      simp only [Pi.smul_apply, halfInd_comp hΛ]
    show c⁻¹ • om (g, h) (Tm (fun s => ((1 : ℂ) • halfInd a Λ) (actO S T g h s))) = f₀
    rw [e3, hvac, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem smul_om_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT a ha ha0 g h hΛ f₀ Φ f c d hf₀ hth hc h0 hΦ
  obtain ⟨⟨Tm, hTm⟩, huniq⟩ := hth
  have hfT : f = Tm Φ := huniq Tm hTm
  have hthT := fun Ψ hΨ =>
    GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T ΛS ΛT hS hT a ha ha0 f₀ hf₀ Tm hTm Ψ hΨ
  have hf' := huniq _ (isPlaceModel_move hW hΛ hTm hthT hc h0)
  have hcomp : (fun x => Φ (actO S T g h x)) = d • Φ := by
    funext x
    simp only [hΦ, Pi.smul_apply, smul_eq_mul]
  have key : f = c⁻¹ • (d • om (g, h) f) := by
    refine hf'.trans ?_
    show c⁻¹ • om (g, h) (Tm (fun x => Φ (actO S T g h x))) = c⁻¹ • (d • om (g, h) f)
    rw [hcomp, map_smul, map_smul, ← hfT]
  calc d • om (g, h) f = c • (c⁻¹ • (d • om (g, h) f)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    _ = c • f := by rw [← key]

end GlobalTheory.SchrMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotentStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_schrodingerModel_finiteIdempotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ g h, (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ (f₀ Φ f : WO S T → ℂ) (c d : ℂ), IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f → c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g h x) = d * Φ x) → d • om (g, h) f = c • f := by
  first | exact @GlobalTheory.SchrMove.smul_om_eq | exact GlobalTheory.SchrMove.smul_om_eq | (intros; apply GlobalTheory.SchrMove.smul_om_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := by
    intro f g hf hg
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu hu0 => ?_⟩, hf.cont.add hg.cont,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)⟩
    · simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · funext w
      have e₁ := congrFun (h₁ u hu.1 hu0) w
      have e₂ := congrFun (h₂ u hu.2 hu0) w
      simp only [heisO, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  zero_mem' := ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun k L hL h0 w => contDiff_const⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U₁, hU₁, fun u hu hu0 => ?_⟩, hf.cont.const_smul c,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]; ring
    · funext w
      have e₁ := congrFun (h₁ u hu hu0) w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e₁ ⊢
      rw [← e₁]; ring


variable (t : T) in
def positionPair (m : ℕ) : Fin m ⊕ Fin m → Pair T
  | .inl j => .top t j
  | .inr i => .chi i m


variable (G) in
abbrev FactorFn (t : T) (a : Fin D.R.m ⊕ Fin D.R.m) : Type :=
  WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → ℂ

def vecOf (S : GridChoice W U) {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkV (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (a : FinPt G p.small) (b : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (a * S.N.u _) (b * S.N.u _)

def colV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairFn (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S v x) (rowV S v y)

theorem pairPts_eq_sum (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : pairPts S τ x y = τ.sum fun d c => c • pairFn S x y (vecOf S d) := rfl

def moved (S : GridChoice W U) (j : ℕ) (k : FinPt G (.grid (j + 1) D.R.m)) : GA D (G.V (.grid (j + 1) D.R.m)) :=
  ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))

def moveV (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (v (.inr ⟨j, by omega⟩)) : FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hj⟩)) : FactorFn G t (.inr ⟨j + 1, hj⟩))

end GlobalTheory.RowVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.NodePar

theorem goodPar_of_sigOK {D : D7} (N : GlobalTheory.Grid.Node D) (h : N.V.SigOK) (τ : D.what₂.Tau) :
    GoodPar N.V.rank (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 (N.S τ) := by
  have hm := GlobalTheory.TowerSplit.hasSignature_of_model N.M τ
  rw [GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ), GlobalTheory.TowerSplit.signCard_of_isEnum (N.M.enum τ)] at hm
  have hs : Formalism.UG.HasSignature (gramAt D N.V τ) (N.V.sig (tauE D τ)).1 (N.V.sig (tauE D τ)).2 := h (tauE D τ)
  obtain ⟨e1, e2⟩ := Formalism.UG.P.signature_unique _ _ _ _ _ _ hm hs
  exact ⟨N.M.lam τ, N.M.ε τ, N.M.enum τ,
    GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ), e1, e2⟩

end GlobalTheory.NodePar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem isDatum_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), IsDatum M ψ crd 0 0 ∧ ∀ (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ) (c : ℂ), IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + c • Φ') (f + c • f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd
  have hn : ∀ x, ‖ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  refine ⟨⟨Submodule.zero_mem _, fun u => ?_⟩, fun Φ Φ' f f' c h h' =>
    ⟨Submodule.add_mem _ h.1 (Submodule.smul_mem _ c h'.1), fun u => ?_⟩⟩
  · have e : M.co.rho ψ u (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := funext fun x => by
      simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    rw [e]
    simp [GlobalTheory.WeilM.thetaSum]
  · have s1 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h.1).1 (M.co.e u)
    have s2 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ' (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h'.1).1 (M.co.e u)
    have e : M.co.rho ψ u (Φ + c • Φ') = M.co.rho ψ u Φ + c • M.co.rho ψ u Φ' := funext fun x => by
      simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← h.2 u, ← h'.2 u]
    unfold GlobalTheory.WeilM.thetaSum
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [s1.tsum_add (s2.mul_left c), tsum_mul_left]

end GlobalTheory.SquareAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowShiftTheta
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

def thSub (W : G.Weil) (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ (G.pS p) (G.pT p) f}
  add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg


open Classical in
def toTh (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : thSub W p :=
  if h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f then ⟨f, h⟩ else 0

theorem coe_toTh (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) :
    (toTh W p f : WO (G.pS p) (G.pT p) → ℂ) = f := by
  simp [toTh, h]

def lastIx (D : D7) : Fin D.R.m := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩

theorem lastIx_succ (D : D7) : D.R.m = (lastIx D : ℕ) + 1 := by
  have := D.R.two_le_m
  simp only [lastIx]
  omega

variable {W : G.Weil}

def colMapV (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (fs ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (gs ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

theorem colMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (x : ∀ j, FinPt G (.top j)) :
    S.colMap d x = colMapV S (fun j => S.Z.vec (d.1 j)) x := rfl

theorem rowMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    S.rowMap d y = rowMapV S (fun i => S.Z.vec (d.2 i)) y := rfl

def topLast (g : FinPt G (.top D.R.m)) : FinPt G (.top ((lastIx D : ℕ) + 1)) := lastIx_succ D ▸ g

def gridLast (g : FinPt G (.grid D.R.m D.R.m)) : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m) := lastIx_succ D ▸ g

def colShift (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) :=
  W.om (.top t (lastIx D)) (G.toPair (.top t (lastIx D)) 1
    (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1)

def rowShift (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (lastIx D) D.R.m) (G.toPair (.chi (lastIx D) D.R.m) 1
    (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1)

end GlobalTheory.LastVertexInv

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inRange_top (t : T) (j : Fin D.R.m) : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := by
  have := j.2
  simp [Pair.InRange, Node.InRange]

theorem inRange_chi (i : Fin D.R.m) : (Pair.chi (i : ℕ) D.R.m : Pair T).InRange D.R.m := by
  have := i.2
  simp [Pair.InRange, Node.InRange]

theorem defPair_top (t : T) (j : Fin D.R.m) : DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) := by
  have := j.2
  simp [DefPair]

theorem defPair_chi (i : Fin D.R.m) : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := by
  have := i.2
  simp [DefPair]

theorem vec_theta (S : GridChoice W U) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m)
    (d : FinDatum G t p) (h : S.Z.HasVec d) : IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (S.Z.vac_is p hp).2.theta)

theorem colShift_theta (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    {f : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (colShift S t g f) :=
  (W.om_is _ (inRange_top t (lastIx D))).om_pres _ _ h

theorem rowShift_theta (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    {f : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (rowShift S k f) :=
  (W.om_is _ (inRange_chi (lastIx D))).om_pres _ _ h

end GlobalTheory.LastVertexInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.CoinvLine

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hψ : IsStdChar D ψ (-1)) [Nonempty D.what₂.Tau] {W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X) {Ψ : WO W₁ X → ℂ}
    (hΨ : Ψ ∈ algF ψ θ false A₁ B) : IsThetaFunO ψ W₁ X Ψ := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn false A₁) B hf).1 (Classical.arbitrary _) P
  | zero => exact Formalism.IndefR.Fock.CCR.theta_zero ψ W₁ X
  | add x y _ _ hx hy => exact Formalism.IndefR.Fock.CCR.theta_add hx hy
  | smul c x _ hx => exact Formalism.IndefR.Fock.CCR.theta_smul hx c

end GlobalTheory.CoinvLine
end
end
