module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrOfIsotropic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | exact GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj | (intros; apply GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VPEqSumHeisCore
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierCore

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.DatumFourier
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1600000 in
theorem thetaVector_eq_sum_heisenberg_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ R.Q t) → R.vP i t = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun t l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hR.thP.vP i t
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ R.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    GlobalTheory.PlaceVec.omegaK_congr _ fun PP h => hred PP (Or.inl h),
    GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ fun PP h => hred PP (Or.inr h), ← (hφ x).2, RingHom.id_apply, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslates
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.AdTh.MovedDatumCore
open GlobalTheory.AdTh.MovedDatum

theorem moved_datum_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hiso
  obtain ⟨δ, hδ⟩ := GlobalTheory.DatumFourierCore.thetaVector_eq_sum_heisenberg_core D G Pl0 T0 A Ks R F hR i hV H Dw ι hι hiso
  refine ⟨δ, fun t l φ hφ hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu => ?_⟩
  obtain ⟨e, he, -⟩ := id hφ
  obtain ⟨hp, -, a1, a2, a3, a4, a5⟩ := GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i t hV
  obtain ⟨hψ, hvac⟩ := (hR.thP.vP i t).1
  rw [hδ t l φ hφ hP e he, map_smul]
  by_cases hfin : Finite (Fin (Vc D i).rank → LevQ Dw l)
  swap
  · haveI := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, _root_.inv_zero, zero_smul, zero_smul]
  rw [map_finsum _ (Set.toFinite _)]
  congr 1
  refine finsum_congr fun q => ?_
  rw [map_smul]
  by_cases hq : hatC l φ q = 0
  · rw [hq, zero_smul, zero_smul]
  obtain ⟨c, hc, h1, h2⟩ := step R.ψ hψ (Vc D i) (Wc D i) hp.std (rank_Wc i) (R.ΛV i) (R.ΛW i) a1 a2 a3 a4 a5 l ι hι δ
    _ e he (fun PP hPP => ⟨(hP PP (Finset.mem_union.1 hPP)).1, fun h2 => (hP PP (Finset.mem_union.1 hPP)).2 (by
      obtain ⟨c, hc⟩ : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
      rw [hc, mul_assoc, mul_assoc, Nat.cast_mul, Nat.cast_ofNat]; exact Ideal.mul_mem_right _ _ h2)⟩)
    bad N h k Λ mk (fun PP hPP => hbad PP (Finset.mem_union.1 hPP)) hh hΛ hT hL hmk Y hY q
    (fun s hs => GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero D G Pl0 T0 A Ks R i H Dw ι t l φ hφ q hq s fun PP hPP => hs PP (Finset.mem_union.2 hPP))
    (γ q) (u q) (hu q).1 (hu q).2
  have h3 : heisO R.ψ (Vc D i) (Wc D i) (2 • actO (Vc D i) (Wc D i) h k c) (R.ωP i t (h, k) (R.vacP i)) =
      R.ωP i t (h, k) (R.vacP i) := by
    rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
  have h4 := GlobalTheory.PlaceModel.heisL_heisL (Vc D i) (Wc D i) R.ψ _ _ (R.ωP i t (h, k) (R.vacP i)) |>.trans
    (congrArg (· • _) h2)
  rw [one_smul, ← h1] at h4
  rw [hp.weil.om_heis h k _ _ hvac.theta]
  congr 1
  refine Eq.trans ?_ h4
  exact congrArg _ h3.symm

end GlobalTheory.AdTh.MovedDatumCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumEqSumRationalRootTranslatesStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedFiniteDatum_eq_sum_rational_root_translates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ (bad N : ℕ) (h : GA D (Vc D i)) (k : GA D (Wc D i)) (Λ : GenLat D.host.E (Vc D i).rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → SplitOffBad (Vc D i) bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ (Wc D i) (rank_Wc i) ι k mk → ∀ (Y : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Vc D i).rank) (Fin D.R.r) D.host.E) (γ : (Fin (Vc D i).rank → LevQ Dw l₂) → Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (u : (Fin (Vc D i).rank → LevQ Dw l₂) → WO (Vc D i) (Wc D i)), IsRoots l₂ (latR (rank_Wc i) (latG (Wc D i) k)) mk N Y → (∀ q, colsR (rank_Wc i) (γ q) = (δ : ℤ) • Y q ∧ IsFinOf (Vc D i) (Wc D i) (γ q) (u q)) → R.ωP i t (h, k) (R.vP i t) = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (u q) (R.ωP i t (h, k) (R.vacP i)) := by
  first | exact @GlobalTheory.AdTh.MovedDatumCore.moved_datum_core | exact GlobalTheory.AdTh.MovedDatumCore.moved_datum_core | (intros; apply GlobalTheory.AdTh.MovedDatumCore.moved_datum_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJet
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

def scaleCLM {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) : VC D N N' →L[ℂ] VC D N N' :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => c τ * Z τ i j
      map_add' := fun Z Z' => by funext τ i j; simp [mul_add]
      map_smul' := fun s Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem scaleCLM_apply {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (Z : VC D N N') :
    scaleCLM c Z = fun τ i j => c τ * Z τ i j := rfl

theorem scaleCLM_coordV {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (k : D.what₂.Tau × Fin N' × Fin N) :
    scaleCLM c (Formalism.MainNotions.TaylorLogMetric.coordV D k) = c k.1 • Formalism.MainNotions.TaylorLogMetric.coordV D k := by
  funext τ i j
  simp only [scaleCLM_apply, Formalism.MainNotions.TaylorLogMetric.coordV, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.1]
  · simp

theorem prod_toList_get {ι : Type} (m : ι →₀ ℕ) (g : ι → ℂ)
    (h : ∀ i : Fin (Finsupp.toMultiset m).card, (i : ℕ) < (Finsupp.toMultiset m).toList.length) :
    (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩)) =
      m.prod fun k e => g k ^ e := by
  have hl : (Finsupp.toMultiset m).card = (Finsupp.toMultiset m).toList.length := (Multiset.length_toList _).symm
  calc (∏ i : Fin (Finsupp.toMultiset m).card, g ((Finsupp.toMultiset m).toList.get ⟨i, h i⟩))
      = ∏ i : Fin (Finsupp.toMultiset m).toList.length, g ((Finsupp.toMultiset m).toList.get i) :=
        Fin.prod_congr' (fun i => g ((Finsupp.toMultiset m).toList.get i)) hl
    _ = ((Finsupp.toMultiset m).toList.map g).prod := Fin.prod_univ_fun_getElem _ g
    _ = (Multiset.map g (Finsupp.toMultiset m)).prod := by
        conv_rhs => rw [← Multiset.coe_toList (Finsupp.toMultiset m)]
        rw [Multiset.map_coe, Multiset.prod_coe]
    _ = m.prod fun k e => g k ^ e := by
        rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
          Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

theorem taylor_scale {D : D7} {N N' : ℕ} (c : D.what₂.Tau → ℂ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) α =
      (α.prod fun k e => c k.1 ^ e) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  have hfun : (fun Z : VC D N N' => G fun τ i j => c τ * Z τ i j) = G ∘ scaleCLM c := rfl
  have hGc : ContDiff ℂ ⊤ G := (GlobalTheory.SCV.analyticOnNhd_of_differentiable hG Set.univ).contDiff
  rw [Formalism.MainNotions.TaylorLogMetric.taylor, Formalism.MainNotions.TaylorLogMetric.taylor, hfun,
    (scaleCLM c).iteratedFDeriv_comp_right hGc 0 le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  simp only [scaleCLM_coordV]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_div_assoc]
  congr 1
  exact prod_toList_get α (fun k => c k.1) _

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

def placeWt (D : D7) (a d : ℕ) : Formalism.MainNotions.GL3Theta.Idx D a d → D.what₂.Tau → ℕ := fun k => Pi.single k.1 1

theorem prod_eq_prod_weight {D : D7} {a d : ℕ} (f : D.what₂.Tau → ℂ) (v : Formalism.MainNotions.GL3Theta.Idx D a d →₀ ℕ) :
    (v.prod fun k e => f k.1 ^ e) = ∏ τ, f τ ^ Finsupp.weight (placeWt D a d) v τ := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single k.1]
  · simp [placeWt]
  · intro τ _ hτ
    simp [placeWt, hτ]
  · simp

theorem minorPol_isWeightedHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (t : Tup D a d n) :
    (minorPol D t).IsWeightedHomogeneous (placeWt D a d) (fun τ => a * n τ) := by
  have hdet : ∀ τ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, (t τ j).1 i, i') :
      MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)).det.IsWeightedHomogeneous (placeWt D a d) (a • Pi.single τ 1) := by
    intro τ j
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule, Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i => (MvPolynomial.X (τ, (t τ j).1 (σ i), i) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ))
      (fun _ => (Pi.single τ 1 : D.what₂.Tau → ℕ))
      (fun i _ => MvPolynomial.isWeightedHomogeneous_X ℂ (placeWt D a d) (τ, (t τ j).1 (σ i), i))
    simpa using this
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun τ _ =>
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun j _ => hdet τ j
  have hdeg : (fun τ => a * n τ) = ∑ τ, ∑ _j : Fin (n τ), a • (Pi.single τ 1 : D.what₂.Tau → ℕ) := by
    funext τ'
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  rw [hdeg]
  exact h

end GlobalTheory.NormExact

namespace GlobalTheory.NormExact

theorem fock_minorPol_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  intro D ψ θ S T a d hS hT cc δ r hs G f hG hR n t
  subst hS hT
  have hren : MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D S.rank T.rank =>
      ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : FVar D T.rank S.rank)) (minorPol D t) = minorPol D t :=
    MvPolynomial.rename_id_apply _
  rw [hren]
  obtain ⟨hstd, hinf, hgS, hgT, hcrv, hsc⟩ := hs
  have hrd := (reads_iff hcrv hsc G f).1 hR
  have hΦ : Differentiable ℂ (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) :=
    hG.comp (scaleCLM (fun τ => δ * embT D τ r)).differentiable
  have hfr : ∀ m, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin m) D.host.E) = fun _ => 1 := fun m =>
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  have hon : ∀ V : HSp D, V.gram = 1 →
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : GL (Fin V.rank) D.host.E).1 * V.gram *
        (1 : GL (Fin V.rank) D.host.E).1 = 1 := by
    intro V hV
    simp [Formalism.UG.cT, hV]
  have hmono := GlobalTheory.FockPos.fock_monomial_zero_of_on ψ θ S T 1 1 hstd hinf (hon S hgS) (hon T hgT) f _ hΦ hrd.2
  rw [hfr, hfr] at hmono
  set P := minorPol D t with hPdef
  have hP : P = ∑ v ∈ P.support, AddMonoidAlgebra.coeff P v • MvPolynomial.monomial v (1 : ℂ) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    exact Finset.sum_congr rfl fun v _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [hP, map_sum, Finset.sum_apply]
  rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, hmono v]
  have happ : Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial v 1)
      (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) =
      (v.prod fun _ e => (e.factorial : ℂ)) *
        Formalism.MainNotions.TaylorLogMetric.taylor D (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) v := by
    rw [Formalism.MainNotions.GL3Theta.applyAt0, Finset.sum_subset MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, one_mul]
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul, zero_mul]
  rw [happ, taylor_scale (fun τ => δ * embT D τ r) G hG v]
  have hw : Finsupp.weight (placeWt D S.rank T.rank) v = fun τ => S.rank * n τ :=
    minorPol_isWeightedHomogeneous t (MvPolynomial.mem_support_iff.1 hv)
  have hper : (∏ τ, period D δ r τ ^ (S.rank * n τ)) =
      (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) ^ (v.sum fun _ e => e) *
        v.prod fun k e => (δ * embT D k.1 r) ^ e := by
    rw [← Finset.prod_congr rfl fun τ _ => congrArg (period D δ r τ ^ ·) (congrFun hw τ),
      ← prod_eq_prod_weight]
    simp only [period, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, ← mul_pow,
      div_eq_mul_inv]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [hper]
  ring

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJetStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  first | exact @GlobalTheory.NormExact.fock_minorPol_zero | exact GlobalTheory.NormExact.fock_minorPol_zero | (intros; apply GlobalTheory.NormExact.fock_minorPol_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDual
noncomputable section

open NumberField
open scoped Pointwise

namespace GlobalTheory.VacRead.SelfDual

open GlobalTheory.InertSign (IntE hE)

theorem intE_iff {D : Formalism.BasicNotions.D7} {e : D.host.E} : IntE D e ↔ e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := Iff.rfl

theorem intE_gen (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {α₁ α₂ γ₁ γ₂ : D.host.E} (hα₁ : α₁ ∈ cE D cc) (hα₂ : α₂ ∈ cE D cc)
    (hγ₁ : γ₁ ∈ cE D D.host.ccK) (hγ₂ : γ₂ ∈ cE D D.host.ccK) :
    IntE D (r * D.host.conj α₁ * γ₁ / (Ideal.absNorm cc : D.host.E) *
      D.host.conj (r * D.host.conj α₂ * γ₂ / (Ideal.absNorm cc : D.host.E))) := by
  obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α₁ hα₁ α₂ hα₂
  obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ₂ hγ₂ γ₁ hγ₁
  unfold GlobalTheory.NormExact.IsScale at hs
  refine ⟨o₁ * o₂, ?_⟩
  simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj]
  change (o₁ : D.host.E) * (o₂ : D.host.E) = _
  field_simp
  linear_combination (exp := 1) (-(r * D.host.conj r) * (D.host.conj γ₂ * γ₁)) * h₁ +
    (-(r * D.host.conj r) * (Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E)) * h₂ +
    (-((Ideal.absNorm cc : D.host.E) * (o₁ : D.host.E) * (o₂ : D.host.E))) * hs

def pairSpan (D : Formalism.BasicNotions.D7) (J : Submodule (𝓞 D.host.E) D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ u ∈ J, ∃ x ∈ J, t = u * D.host.conj x}

theorem conj_smul (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) (x : D.host.E) :
    D.host.conj (c • x) = D.host.conj (c : D.host.E) * D.host.conj x := by
  rw [Algebra.smul_def, map_mul]

theorem intE_coe (D : Formalism.BasicNotions.D7) (c : 𝓞 D.host.E) : IntE D (c : D.host.E) := ⟨c, rfl⟩

theorem intE_mul_conj (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hn : (Ideal.absNorm cc : D.host.E) ≠ 0)
    (hs : GlobalTheory.NormExact.IsScale D cc r) {u x : D.host.E} (hu : u ∈ bInv D cc r) (hx : x ∈ bInv D cc r) :
    IntE D (u * D.host.conj x) := by
  unfold bInv at hu hx
  induction hu using Submodule.span_induction generalizing x with
  | mem g hg =>
    obtain ⟨α₁, hα₁, γ₁, hγ₁, rfl⟩ := hg
    induction hx using Submodule.span_induction with
    | mem g' hg' =>
      obtain ⟨α₂, hα₂, γ₂, hγ₂, rfl⟩ := hg'
      exact intE_gen D cc r hn hs hα₁ hα₂ hγ₁ hγ₂
    | zero => rw [map_zero, mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [conj_smul, mul_left_comm]
      exact mul_mem (GlobalTheory.InertSign.IntE.conj (intE_coe D c)) hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => rw [add_mul]; exact add_mem (hy hx) (hz hx)
  | smul c y _ hy =>
    rw [Algebra.smul_def, mul_assoc]
    exact mul_mem (intE_coe D c) (hy hx)

theorem one_mem_pairSpan (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    (1 : D.host.E) ∈ pairSpan D (bInv D cc r) := by
  have h₁ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).2
  have h₂ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  have hm := Submodule.mul_mem_mul h₁ h₂
  rw [Submodule.span_mul_span] at hm
  set c : D.host.E := r * D.host.conj r / (Ideal.absNorm cc : D.host.E) ^ 2 with hc
  have hle : Submodule.span (𝓞 D.host.E) ({t | ∃ α ∈ cE D cc, ∃ β ∈ cE D cc, t = D.host.conj α * β} *
      {t | ∃ α ∈ cE D D.host.ccK, ∃ β ∈ cE D D.host.ccK, t = D.host.conj α * β}) ≤
      (pairSpan D (bInv D cc r)).comap (LinearMap.mulLeft (𝓞 D.host.E) c) := by
    rw [Submodule.span_le]
    rintro _ ⟨_, ⟨α, hα, β, hβ, rfl⟩, _, ⟨γ, hγ, ε, hε, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨r * D.host.conj α * ε / (Ideal.absNorm cc : D.host.E), ?_,
      r * D.host.conj β * γ / (Ideal.absNorm cc : D.host.E), ?_, ?_⟩
    · unfold bInv; exact Submodule.subset_span ⟨α, hα, ε, hε, rfl⟩
    · unfold bInv; exact Submodule.subset_span ⟨β, hβ, γ, hγ, rfl⟩
    · simp only [map_div₀, map_mul, map_natCast, GlobalTheory.InertSign.conj_conj, hc]
      field_simp
  have h := hle hm
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at h
  convert h using 1
  unfold GlobalTheory.NormExact.IsScale at hs
  rw [hc]
  field_simp
  linear_combination -hs

theorem mem_of_dual (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) {y : D.host.E}
    (hy : ∀ x ∈ bInv D cc r, IntE D (y * D.host.conj x)) : y ∈ bInv D cc r := by
  have hle : pairSpan D (bInv D cc r) ≤ (bInv D cc r).comap (LinearMap.mulLeft (𝓞 D.host.E) y) := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨o, ho⟩ := hy x hx
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have : y * (u * D.host.conj x) = o • u := by rw [Algebra.smul_def, ho]; ring
    rw [this]
    exact Submodule.smul_mem _ o hu
  have h := hle (one_mem_pairSpan D cc r hn hs)
  simpa only [Submodule.mem_comap, LinearMap.mulLeft_apply, mul_one] using h

theorem exists_ne_zero (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E)
    (hn : (Ideal.absNorm cc : D.host.E) ≠ 0) (hs : GlobalTheory.NormExact.IsScale D cc r) :
    ∃ x ∈ bInv D cc r, x ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hle : pairSpan D (bInv D cc r) ≤ ⊥ := by
    unfold pairSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, x, hx, rfl⟩
    simp [hne u hu]
  have h := hle (one_mem_pairSpan D cc r hn hs)
  rw [Submodule.mem_bot] at h
  exact one_ne_zero h

theorem lsB_sd (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) (hcc : cc ≠ ⊥)
    (hs : GlobalTheory.NormExact.IsScale D cc r) : Formalism.MainNotions.StandardLatticesGL3.SD D (lsB D cc r a) := by
  have hn : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hcc)
  have hsingle : ∀ (i : Fin a) (u : D.host.E), u ∈ bInv D cc r → (Pi.single i u : Fin a → D.host.E) ∈ lsB D cc r a := by
    intro i u hu
    rw [mem_lsB]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp only [Pi.single_apply, hj, if_false]; exact zero_mem _
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x₀, hx₀, hne⟩ := exists_ne_zero D cc r hn hs
    have hcne : D.host.conj x₀ ≠ 0 := (map_ne_zero_iff _ D.host.conj.injective).mpr hne
    let M := Submodule.span (𝓞 D.host.E)
      (Set.range fun i : Fin a => (Pi.single i (D.host.conj x₀)⁻¹ : Fin a → D.host.E))
    have hM : M.FG := Submodule.fg_span (Set.finite_range _)
    haveI := isNoetherian_of_fg_of_noetherian M hM
    refine Submodule.FG.of_le_of_isNoetherian (T := M) ?_
    intro y hy
    rw [mem_lsB] at hy
    rw [pi_eq_sum_univ' y]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨o, ho⟩ := intE_mul_conj D cc r hn hs (hy i) hx₀
    have he : y i • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) = o • Pi.single i (D.host.conj x₀)⁻¹ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Algebra.smul_def, ho]
        field_simp
      · simp [Pi.single_apply, hj]
    rw [he]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨i, rfl⟩)
  · rw [eq_top_iff]
    intro v _
    have he : ∀ i : Fin a, (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
        Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
      intro i
      have key : ∀ t ∈ pairSpan D (bInv D cc r), t • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) ∈
          Submodule.span D.host.E (lsB D cc r a : Set (Fin a → D.host.E)) := by
        intro t ht
        unfold pairSpan at ht
        induction ht using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨u, hu, x, hx, rfl⟩ := hg
          have hg' : (u * D.host.conj x) • (Pi.single i (1 : D.host.E) : Fin a → D.host.E) =
              D.host.conj x • Pi.single i u := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [mul_comm]
            · simp [Pi.single_apply, hj]
          rw [hg']
          exact Submodule.smul_mem _ _ (Submodule.subset_span (hsingle i u hu))
        | zero => rw [zero_smul]; exact zero_mem _
        | add s t _ _ hs' ht' => rw [add_smul]; exact add_mem hs' ht'
        | smul c t _ ht' => rw [smul_assoc]; exact Submodule.smul_of_tower_mem _ c ht'
      simpa using key 1 (one_mem_pairSpan D cc r hn hs)
    rw [pi_eq_sum_univ' v]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  · intro y
    rw [mem_lsB]
    constructor
    · intro hy x hx
      rw [mem_lsB] at hx
      rw [intE_iff]
      unfold hE
      exact Subring.sum_mem _ fun i _ => intE_mul_conj D cc r hn hs (hy i) (hx i)
    · intro h i
      refine mem_of_dual D cc r hn hs fun x hx => ?_
      have h' := h (Pi.single i x) (hsingle i x hx)
      unfold hE at h'
      rwa [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
        Pi.single_eq_same] at h'

end GlobalTheory.VacRead.SelfDual

theorem GlobalTheory.VacRead.lsB_selfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) :=
  fun D cc r a hcc hs => GlobalTheory.VacRead.SelfDual.lsB_sd D cc r a hcc hs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDifferentLatticeProductHermitianIsSelfDualStatement
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invDifferentLatticeProductHermitian_isSelfDual : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ), cc ≠ ⊥ → GlobalTheory.NormExact.IsScale D cc r → Formalism.MainNotions.StandardLatticesGL3.SD D (GlobalTheory.VacRead.lsB D cc r a) := by
  first | exact @GlobalTheory.VacRead.lsB_selfDual | exact GlobalTheory.VacRead.lsB_selfDual | (intros; apply GlobalTheory.VacRead.lsB_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRank
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdDefSpace

theorem exists_std_definite : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  intro D n
  refine ⟨Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n, rfl, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    rw [Matrix.one_apply]
    by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | rfl | exact h
  · exact Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n
  · exact fun _ => Or.inl rfl

end GlobalTheory.StdDefSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardPositiveDefiniteHermitianSpaceRankStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  first | exact @GlobalTheory.StdDefSpace.exists_std_definite | exact GlobalTheory.StdDefSpace.exists_std_definite | (intros; apply GlobalTheory.StdDefSpace.exists_std_definite <;> assumption)
end
end
