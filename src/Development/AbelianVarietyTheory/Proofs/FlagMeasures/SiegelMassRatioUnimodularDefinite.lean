module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrame
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualLatticeCompletionMaxOrder
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
namespace GlobalTheory.Mass

theorem siegelMassRatio_holds : Formalism.HermitianLatticesTheory.SiegelMassRatio :=
  Formalism.HermitianLattices.Ext.L3.siegelMassRatio_of_LI binary_hermitian_represents Formalism.HermitianLattices.Ext.L3.liStat

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefiniteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_massRatio_unimodular_definite : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  first | exact @GlobalTheory.Mass.siegelMassRatio_holds | exact GlobalTheory.Mass.siegelMassRatio_holds | (intros; apply GlobalTheory.Mass.siegelMassRatio_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WeylDimU

theorem prod_sub_eq_prod_factorial (k : ℕ) :
    ∏ a : Fin k, ∏ b ∈ Finset.univ.filter (fun b : Fin k => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  rcases k with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem finrank_space {k : ℕ} (lam : Formalism.BasicNotions.DomWeight k) (u : Fin k → ℝ)
    (hu : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ))) :
    (Module.finrank ℂ (GlobalTheory.DualWeyl.Space lam.natW) : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  have h := Formalism.L2.G.Model.weyl_dualWeyl ℂ k lam.natW (Formalism.BasicNotions.factNatW k lam).1
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_prod] at h2
  refine Eq.trans h2 ?_
  rw [← prod_sub_eq_prod_factorial, vand, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_div_distrib, Finset.prod_filter]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast
    congr 1
    linarith [hu a, hu b, GlobalTheory.NablaType.natW_add lam a, GlobalTheory.NablaType.natW_add lam b]
  · simp

theorem finrank_eq (k : ℕ) (u : Fin k → ℝ) (hu : IsHCParam u) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : IsHCTypeU k u π) :
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  obtain ⟨hs, hm⟩ := hu
  choose m hm using hm
  have hm' : StrictAnti m := fun a b hab => by
    have := hs hab
    have h2 : (m b : ℝ) < m a := by linarith [hm a, hm b]
    exact_mod_cast h2
  have hL : Antitone fun a : Fin k => m a + (a : ℕ) := by
    rcases k with _ | n
    · exact fun a => a.elim0
    rw [Fin.antitone_iff_succ_le]
    intro i
    have := hm' (Fin.castSucc_lt_succ (i := i))
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  let lam : Formalism.BasicNotions.DomWeight k := ⟨fun a => m a + (a : ℕ), hL⟩
  have hw : ∀ a, (lam.w a : ℝ) = u a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := fun a => by
    simp only [lam]
    push_cast
    linarith [hm a]
  have hK := GlobalTheory.NablaType.isKTypeOf_act lam
  have hT : IsHCTypeU k u (GlobalTheory.NablaType.act lam) := by
    refine ⟨?_, inferInstance, GlobalTheory.NablaType.isURepOn_act lam, ?_⟩
    · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
      exact ⟨v, 0, hv⟩
    · convert hK using 1
      funext a
      unfold allPos
      rw [GlobalTheory.DefiniteCheck.lowK_const, hw]
  obtain ⟨A, -⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU k u _ _ _ _ hπ hT
  rw [A.finrank_eq]
  exact finrank_space lam u hw

theorem weyl_dimension : ∀ (k : ℕ) (u : Fin k → ℝ), IsHCParam u → (∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π → (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ)) ∧ (dimPiU k u : ℝ) = vand u / ∏ i ∈ Finset.range k, (i.factorial : ℝ) := by
  intro k u hu
  refine ⟨fun H _ _ π hπ => finrank_eq k u hu H π hπ, ?_⟩
  obtain ⟨H, _, _, π, hπ⟩ := GlobalTheory.CompactDS.exists_isHCTypeU k u hu
  have hne : {d | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsHCTypeU k u π ∧ Module.finrank ℂ H = d}.Nonempty :=
    ⟨_, H, _, _, π, hπ, rfl⟩
  obtain ⟨H', _, _, π', hπ', e⟩ := Nat.sInf_mem hne
  rw [dimPiU, ← e]
  exact finrank_eq k u hu H' π' hπ'

end GlobalTheory.WeylDimU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem mem_mL_of_coprime_smul (I : AutInst) (g c : ℕ) (hc : Nat.Coprime c g) {v : VA I} (hv : v ∈ I.Lf)
    (hcv : (c : I.E ⊗[I.F] Af I.F) • v ∈ mL I g) : v ∈ mL I g := by
  have hb : ((c : ℤ) * Nat.gcdA c g + (g : ℤ) * Nat.gcdB c g) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  have hR1 : ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) * (c : I.E ⊗[I.F] Af I.F) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
    have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hb
    push_cast at this
    linear_combination this
  have e : v = ((Nat.gcdA c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((c : I.E ⊗[I.F] Af I.F) • v) +
      ((Nat.gcdB c g : ℤ) : I.E ⊗[I.F] Af I.F) • ((g : I.E ⊗[I.F] Af I.F) • v) := by
    rw [smul_smul, smul_smul, ← add_smul, hR1, one_smul]
  have hint : ∀ n : ℤ, ∀ w ∈ mL I g, ((n : I.E ⊗[I.F] Af I.F)) • w ∈ mL I g := fun n w hw =>
    (mL I g).smul_mem (⟨(n : I.E ⊗[I.F] Af I.F), intCast_mem _ n⟩ : IntAf I.F I.E) hw
  rw [e]
  exact add_mem (hint _ _ hcv) (hint _ _ (smul_mem_mL I hv))

theorem iota_symm_inv_g {D : D7} (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) =
      algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹) := by
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  have hG : D.host.g 0 * D.host.g 1 = X.B.g := X.g_eq.symm
  have h1 : algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹) * ((X.B.g : ℕ) : D.host.E ⊗[D.host.F] Ad D.host.F) = 1 := by
    rw [← hG, ← map_natCast (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (hG ▸ hg)), map_one]
  have ha : ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹)) * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
    rw [← map_natCast ιA.symm, ← map_mul, h1, map_one]
  have hb := inv_g X.B.I X.B.g hg
  set a := ιA.symm (algebraMap D.host.F (D.host.E ⊗[D.host.F] Ad D.host.F)
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)⁻¹))
  set b := algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((X.B.g : X.B.I.F)⁻¹)
  calc a = a * (b * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) := by rw [hb, mul_one]
    _ = (a * (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * b := by ring
    _ = b := by rw [ha, one_mul]

theorem hA_pair_cong (I : AutInst) (g : ℕ) (H : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hH : ∀ z ∈ mL I g, H *ᵥ z ∈ mL I g) (P P' Q Q' : VA I) (hPP : P - P' ∈ mL I g) (hQQ : Q - Q' ∈ mL I g)
    (hP' : P' ∈ I.Lf) (hHQ : H *ᵥ Q ∈ I.Lf) :
    ZMod' I g (hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q')) := by
  have e : hA I P (H *ᵥ Q) - hA I P' (H *ᵥ Q') = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ (Q - Q')) := by
    have e1 : hA I P (H *ᵥ Q) = hA I (P - P') (H *ᵥ Q) + hA I P' (H *ᵥ Q) := by
      rw [← hA_add_left, sub_add_cancel]
    rw [e1, Matrix.mulVec_sub, hA_sub_right]; ring
  rw [e]
  refine Z_add I g ?_ ?_
  · rw [hA_symm I (H *ᵥ Q)]
    exact Z_sig I g (mL_Qs I g hHQ hPP)
  · exact mL_Qs I g hP' (hH _ hQQ)

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem chi_link (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (Fr : FrQ D wt)
    (hL : FrLink X u wt ιA Fr)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) :
    X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) = Fr.chi y.1 := by
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  unfold AdFrame.chi
  rw [hpsi, map_mul, iota_symm_inv_g X ιA]
  rfl

end GlobalTheory.St.G.ColChar

namespace GlobalTheory.St.G.ColChar

open Formalism.L2.SG.Pf.unitaryCongruence

theorem psiK_eq_chi : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  intro D X u wt ιA hW hI hK Fr hL h y hRep hk
  obtain ⟨hlat, hform, -, -, -, hrep⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hpsi : ∀ a, Fr.psi a = X.psiEf (ιA.symm a) := hL.2.2.2
  have hg := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, hbb⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have he0 : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hz0 : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have hbw : ∀ i, X.bw i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).1
  have hbwd : ∀ i, X.bwd i ∈ X.B.I.Lf := fun i => (X.vectorsInLattice.2.2 i).2
  obtain ⟨κ, hκdef⟩ : ∃ κ : X.B.I.Gf, κ = (X.xu u)⁻¹ * (h : X.B.I.Gf) * X.xu u := ⟨_, rfl⟩
  have hκ : κ ∈ X.K2 := by rw [hκdef]; exact hk
  have hκK : κ ∈ X.B.I.Kset := hκ.1
  have hxK : X.xu u ∈ X.B.I.Kset := X.xu_K u
  have hxκ : X.xu u * κ = (h : X.B.I.Gf) * X.xu u := by rw [hκdef]; group
  have hhK : (h : X.B.I.Gf) ∈ X.B.I.Kset := by
    have e : (h : X.B.I.Gf) = X.xu u * κ * (X.xu u)⁻¹ := by rw [hκdef]; group
    rw [e]; exact K_mul _ (K_mul _ hxK hκK) (K_inv _ hxK)

  have hpres : ∀ x : X.B.I.Gf, x ∈ X.B.I.Kset → ∀ z ∈ mL X.B.I X.B.g, X.B.I.fmat x *ᵥ z ∈ mL X.B.I X.B.g :=
    fun x hx z hz => pres X.B.I hx X.B.g ∅ (mL X.B.I X.B.g) (by simp) (by simp) le_rfl z (mL_Mo X.B.I hz)
  have hpres1 : ∀ z ∈ mL X.B.I X.B.g, (X.B.I.fmat κ - 1) *ᵥ z ∈ mL X.B.I X.B.g :=
    fun z hz => pres1 X.B.I hκK X.B.g ∅ (mL X.B.I X.B.g) (by simp) le_rfl z (mL_Mo X.B.I hz)

  have hxinv : ∀ v : VA X.B.I, X.B.I.fmat (X.xu u) *ᵥ v = v → X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
    intro v hv
    calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec]
  have hfixE : ∀ b, X.B.I.fmat κ *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := by
    intro b
    have h1 : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) := (X.xu_fix u b).1
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u b)
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, hxinv _ h1]
  have hfixZ : X.B.I.fmat κ *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
      X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) := by
    have h2 := Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u h _ (Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u)
    have hxx : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = incl X.B.I (X.zR u) := by
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul_inv, Matrix.one_mulVec]
    rw [hκdef, fmat_mul, fmat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxx, h2]

  have key : ∀ v w : VA X.B.I, v ∈ X.B.I.Lf → X.B.I.fmat κ *ᵥ w = w →
      InAt X.B.I X.B.g X.B.g (v - w) → (X.B.I.fmat κ - 1) *ᵥ v ∈ mL X.B.I X.B.g := by
    intro v w hv hw hvw
    obtain ⟨c, hc, hcv⟩ := hvw
    refine mem_mL_of_coprime_smul X.B.I X.B.g c hc (K_sub_mv X.B.I hκK hv) ?_
    have hw0 : (X.B.I.fmat κ - 1) *ᵥ w = 0 := by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_self]
    have e : (X.B.I.fmat κ - 1) *ᵥ ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v - w)) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((X.B.I.fmat κ - 1) *ᵥ v) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hw0, sub_zero]
    rw [← e]; exact hpres1 _ hcv
  have hnxt : ∀ a, (X.B.I.fmat κ - 1) *ᵥ nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    intro a
    unfold nxt
    split_ifs with ha
    · exact key _ _ (he0 _) (hfixE _) (X.basisApprox _).1
    · refine key _ _ hz0 hfixZ ?_
      obtain ⟨c, hc, hcv⟩ := X.xu_z u
      refine ⟨c, hc, ?_⟩
      have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.z0 - X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) =
          -((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0)) := by
        rw [← smul_neg, neg_sub]
      rw [e]; exact neg_mem hcv

  have hterm : ∀ (i : Fin D.R.k) (hi : i.1 + 1 < D.R.k),
      ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) -
        ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩))) := by
    intro i hi
    generalize hj : (⟨i.1 + 1, hi⟩ : Fin D.R.k) = j
    have hT : ιA.symm (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
          (Fr.bd i) (y.1.1 *ᵥ Fr.b j)) =
        hA X.B.I (embA X wt ιA (Fr.bd i)) (X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA (Fr.b j)) := by
      rw [← hform, RingEquiv.symm_apply_apply, hrep h y hRep]
    have hT2 : hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j) =
        hA X.B.I (X.B.I.fmat (X.xu u) *ᵥ X.bwd i)
          (X.B.I.fmat (h : X.B.I.Gf) *ᵥ (X.B.I.fmat (X.xu u) *ᵥ X.bw j)) := by
      rw [← Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X (X.xu u) (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw j),
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← fmat_mul, ← fmat_mul, hxκ]
    rw [hT, hT2]
    refine hA_pair_cong X.B.I X.B.g _ (hpres _ hhK) _ _ _ _ ?_ ?_ ((hlat (Fr.bd i)).1 (Fr.bd_mem i))
      (K_mv X.B.I hhK (K_mv X.B.I hxK (hbw j)))
    · have := neg_mem (hL.2.2.1 i); rwa [neg_sub] at this
    · have := neg_mem (hL.2.1 j); rwa [neg_sub] at this

  have hZ : ZMod' X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
      ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
        Fr.b Fr.bd y.1.1) - 0) := by
    have e : Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ -
        ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
          Fr.b Fr.bd y.1.1) - 0 =
        (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) +
        ∑ i : Fin D.R.k, ((if hi : i.1 + 1 < D.R.k then
            hA X.B.I (X.bwd i) (X.B.I.fmat κ *ᵥ X.bw ⟨i.1 + 1, hi⟩) else 0) -
          ιA.symm (if hi : i.1 + 1 < D.R.k then
            hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)
              (Fr.bd i) (y.1.1 *ᵥ Fr.b ⟨i.1 + 1, hi⟩) else 0)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Afun, supSum, map_sum, Finset.sum_sub_distrib]; ring
    rw [e]
    refine Z_add X.B.I X.B.g (Z_sum X.B.I X.B.g _ _ fun a _ => ?_) (Z_sum X.B.I X.B.g _ _ fun i _ => ?_)
    · exact congruence_fixed_term X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 hfe hfz a)
        (mL_Qs X.B.I X.B.g (hf0 a) (hnxt a))
    · by_cases hi : i.1 + 1 < D.R.k
      · simp only [dif_pos hi]; exact hterm i hi
      · simp only [dif_neg hi, map_zero, sub_self]; exact Z_zero X.B.I X.B.g
  have h0 : X.psiEf (divN X.B.I X.B.g 0) = 1 := by
    rw [divN, mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  calc ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ)
      = X.psiEf (divN X.B.I X.B.g (Afun X.B.I X.e0 X.f0 X.z0 X.bw X.bwd κ)) := by rw [hκdef]; rfl
    _ = X.psiEf (divN X.B.I X.B.g (ιA.symm (supSum (hR (Formalism.L2.Forms.sigD D)
          (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)) Fr.b Fr.bd y.1.1))) := by
      have hE := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
      rw [h0, mul_one] at hE
      exact hE
    _ = Fr.chi y.1 := by
      exact chi_link D X u wt ιA Fr hL y

end GlobalTheory.St.G.ColChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacterStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columns_character_eq_linked_frame_character : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (hK : X.LevelSubgroupCharacter) (Fr : FrQ D wt), FrLink X u wt ιA Fr → ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ hk : h ∈ Ku X u hK, ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = Fr.chi y.1 := by
  first | exact @GlobalTheory.St.G.ColChar.psiK_eq_chi | exact GlobalTheory.St.G.ColChar.psiK_eq_chi | (intros; apply GlobalTheory.St.G.ColChar.psiK_eq_chi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTop
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal Pointwise

noncomputable section

namespace GlobalTheory.OrbitSumInt

theorem exists_compact_reach {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousSMul G X] (x0 : X) (hcl : IsClosed (MulAction.orbit G x0))
    (K : Set X) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0 := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set O) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have key : ∃ C : Set G, IsCompact C ∧ (Subtype.val ⁻¹' K : Set O) ⊆ (fun g : G => g • o0) '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set G, IsCompact C ∧ s ⊆ (fun g : G => g • o0) '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · rintro ⟨_, g, rfl⟩ -
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, h⟩ := key
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨c, hc, e⟩ := h (a := g • o0) hg
  exact ⟨c, hc, congrArg Subtype.val e⟩

theorem lintegral_count_lt_top {G H X S : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [MulAction G X]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (Δ : Subgroup H) [Countable Δ] (𝓕 : Set G) (𝓖 : Set H)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hG : IsFundamentalDomain Δ 𝓖 ν) (hfin : ν 𝓖 < ⊤)
    (φ : H →* G) (hφ : Continuous φ) (hinj : Function.Injective φ) (x0 : X)
    (hr : φ.range = MulAction.stabilizer G x0) (hΔ : ∀ δ ∈ Δ, φ δ ∈ Γ)
    (ι : S → X) (hι : Function.Injective ι) (γ : S → Γ) (hγ : ∀ s, (γ s : G) • x0 = ι s)
    (K : Set X) (C : Set G) (hC : IsCompact C) (hKC : ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0) :
    ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Δ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Δ ν
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : H)
  have hU0 : ν U ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hU1).ne'
  set D : Set G := (φ '' U)⁻¹ * C⁻¹ with hD
  have hDc : IsCompact D := (hU.image hφ).inv.mul hC.inv
  let f : G → ℝ≥0∞ := D.indicator 1
  have hf : Measurable f := measurable_one.indicator hDc.measurableSet
  let T : G → ℝ≥0∞ := fun g => ∫⁻ k in 𝓖, f ((φ k)⁻¹ * g) ∂ν
  have hm : Measurable fun p : G × H => f ((φ p.2)⁻¹ * p.1) :=
    hf.comp ((hφ.comp continuous_snd).inv.mul continuous_fst).measurable
  have hT : Measurable T := hm.lintegral_prod_right'
  have hfix : ∀ k, φ k • x0 = x0 := fun k => by
    have : φ k ∈ MulAction.stabilizer G x0 := hr ▸ ⟨k, rfl⟩
    exact this
  let j : S × Δ → Γ := fun p => γ p.1 * ⟨φ p.2, hΔ _ p.2.2⟩
  have hj : Function.Injective j := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have h1 : (γ s : G) * φ a = γ t * φ b := congrArg Subtype.val h
    have h2 : s = t := hι (by rw [← hγ, ← hγ, ← hfix a, ← mul_smul, h1, mul_smul, hfix, hfix])
    subst h2
    rw [Subtype.ext (hinj (mul_left_cancel h1))]
  have step : ∀ (h : G) (s : S), ν U * K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ≤
      ∑' δ : Δ, T ((j (s, δ))⁻¹ • h) := by
    intro h s
    by_cases hK : h⁻¹ • ι s ∈ K
    swap
    · simp [Set.indicator_of_notMem hK]
    rw [Set.indicator_of_mem hK, Pi.one_apply, mul_one]
    rw [← hγ, ← mul_smul] at hK
    obtain ⟨c, hc, e⟩ := hKC _ hK
    obtain ⟨k, hk⟩ : c⁻¹ * (h⁻¹ * γ s) ∈ φ.range := by
      rw [hr, MulAction.mem_stabilizer_iff, mul_smul, ← e, inv_smul_smul]
    have e1 := hG.lintegral_eq_tsum'' fun k' => f ((φ k')⁻¹ * ((γ s : G)⁻¹ * h))
    have e2 : ∀ δ : Δ, T ((j (s, δ))⁻¹ • h) =
        ∫⁻ k' in 𝓖, f ((φ (δ • k'))⁻¹ * ((γ s : G)⁻¹ * h)) ∂ν := fun δ => by
      refine lintegral_congr fun k' => ?_
      congr 1
      simp [j, Subgroup.smul_def, mul_assoc]
    simp only [e2]
    rw [← e1, ← measure_preimage_mul ν k U, ← lintegral_indicator_one
      ((measurable_const_mul k) hU.measurableSet)]
    refine lintegral_mono fun k' => ?_
    by_cases hk' : k' ∈ (fun x => k * x) ⁻¹' U
    swap
    · simp [Set.indicator_of_notMem hk']
    have : (φ k')⁻¹ * ((γ s : G)⁻¹ * h) ∈ D := by
      refine ⟨(φ (k * k'))⁻¹, Set.inv_mem_inv.2 ⟨_, hk', rfl⟩, c⁻¹, Set.inv_mem_inv.2 hc, ?_⟩
      simp [hk, mul_assoc]
    simp [f, Set.indicator_of_mem hk', Set.indicator_of_mem this]
  have main : ν U * ∫⁻ h in 𝓕, ∑' s, K.indicator (1 : X → ℝ≥0∞) (h⁻¹ • ι s) ∂μ ≤ μ D * ν 𝓖 := by
    rw [← lintegral_const_mul' _ _ hU.measure_lt_top.ne]
    calc _ ≤ ∫⁻ h in 𝓕, ∑' g : Γ, T (g⁻¹ • h) ∂μ := by
          refine lintegral_mono fun h => ?_
          rw [← ENNReal.tsum_mul_left]
          refine (ENNReal.tsum_le_tsum (step h)).trans ?_
          rw [← ENNReal.tsum_prod (f := fun s δ => T ((j (s, δ))⁻¹ • h))]
          exact ENNReal.tsum_comp_le_tsum_of_injective hj fun g => T (g⁻¹ • h)
      _ = ∫⁻ g, T g ∂μ := by
          rw [hF.lintegral_eq_tsum']
          exact lintegral_tsum fun g => (hT.comp (measurable_const_smul g⁻¹)).aemeasurable
      _ = ∫⁻ k in 𝓖, μ D ∂ν := by
          rw [lintegral_lintegral_swap hm.aemeasurable]
          refine lintegral_congr fun k => ?_
          rw [lintegral_mul_left_eq_self f, lintegral_indicator_one hDc.measurableSet]
      _ = μ D * ν 𝓖 := by simp
  by_contra htop
  rw [not_lt_top_iff.1 htop, ENNReal.mul_top hU0] at main
  exact (ENNReal.mul_lt_top hDc.measure_lt_top hfin).not_ge main


open GlobalTheory.GaugeEx in
theorem lintegral_orbitSum_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ β hβ Φ hΦ hK μ 𝓕 hμ h𝓕
  rcases isEmpty_or_nonempty {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β} with he | ⟨⟨x0, hx0⟩⟩
  · simp
  have hx0 : hE σ J (x0 0) (x0 0) = algebraMap F E β := hx0
  have hβ' : algebraMap F E β ≠ 0 := by simpa using hβ
  have hxx : hE σ J (x0 0) (x0 0) ≠ 0 := hx0 ▸ hβ'
  obtain _ | M := M
  · exact (hxx (by simp [hE, Formalism.UG.hform])).elim
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hθ : ∃ θ : E, IsUnit (θ - (σ : E →+* E) θ) := by
    by_contra hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hCM.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := by
      by_contra hz
      exact hc ⟨z, (sub_ne_zero.2 (Ne.symm hz)).isUnit⟩
    have := hCM.2.2.2 τ z
    rw [hz] at this
    exact this.symm
  obtain ⟨a, B, J', -, -, -, hxB, hBB, hJ'⟩ := GlobalTheory.AdelicStabUnimod.exists_stepData hCM hJ x0 hxx
  obtain ⟨φ, hφ, hinj, hr, -, hrat⟩ := GlobalTheory.StabiliserOfVector.exists_hom_range_stabiliser F E σ hCM (M + 1) M
    J J' B x0 rfl hJ hJ' hBB.symm hxB hxx
  let ν : Measure (HA (AF F) σ J') := Measure.haar
  have hν : ν.IsHaarMeasure := inferInstance
  obtain ⟨𝓖, h𝓖⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J' ν hν).1
  have hfin : ν 𝓖 < ⊤ := GlobalTheory.Mem.VolFin.finVol F E σ hCM M J' hJ' ν hν 𝓖 h𝓖
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hCM.2.2.1
  have horb : MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0) =
      {y | qR (AF F) σ J (y 0) = algebraMap F (AF F) β} := by
    ext y
    refine ⟨?_, fun hy => GlobalTheory.AdelicWitt.witt_adelic F E σ hCM _ J x0 β hJ hβ hx0 y hy⟩
    rintro ⟨g, rfl⟩
    rw [Set.mem_setOf_eq, ← GlobalTheory.AdelicWitt.qR_ratTup b (AF F) σ J x0 β hx0]
    exact congrArg (fun z => algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z)
      (GlobalTheory.StabOrbit.hR_act (AF F) σ J g _ _)
  have hcl : IsClosed (MulAction.orbit (HA (AF F) σ J) (ratTup (F := F) (AF F) x0)) := by
    rw [horb]
    refine isClosed_eq ?_ continuous_const
    have h1 : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap _
    have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
    unfold qR hR Formalism.UG.hform
    refine continuous_const.mul (h1.comp ?_)
    fun_prop
  obtain ⟨C, hC, hKC⟩ := exists_compact_reach _ hcl _ hK
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  let Δ : Subgroup (HA (AF F) σ J') := HFinIn (AF F) σ J'
  have : Countable Γ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have : Countable Δ := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J'
  have hγ : ∀ s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β},
      ∃ γ : Γ, (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) x0 = ratTup (F := F) (AF F) s.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, e⟩ := GlobalTheory.WittTransitivity.witt_transitive E (σ : E →+* E) hσ
      (fun a _ ha => ha.isUnit) two_ne_zero.isUnit three_ne_zero hθ _ J hJ.1 hJ.2.isUnit (x0 0) (x 0)
      (hx0.trans (Eq.symm hx)) hxx.isUnit
    have hm : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J := by
      have hg' : Formalism.UG.cT (σ : E →+* E) g.1 * J * g.1 = J := hg
      have h1 := congrArg (·.map (inclR (F := F) (AF F))) hg'
      simp only [Matrix.map_mul] at h1
      exact h1
    refine ⟨⟨(⟨_, hm⟩ : HR (AF F) σ J), ⟨g, hg, rfl⟩⟩, ?_⟩
    funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change _ = inclR (F := F) (AF F) (x 0 i)
    rw [← e, RingHom.map_mulVec]
    rfl
  choose γ hγ using hγ
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have hι : Function.Injective fun s : {x : Fin 1 → Fin (M + 1) → E | hE σ J (x 0) (x 0) = algebraMap F E β} =>
      ratTup (F := F) (AF F) s.1 := fun s t h => Subtype.ext (funext fun k => funext fun i =>
    (inclR (F := F) (E := E) (AF F)).injective (congrFun (congrFun h k) i))
  have key := lintegral_count_lt_top μ ν Γ Δ 𝓕 𝓖 h𝓕 h𝓖 hfin φ hφ hinj (ratTup (F := F) (AF F) x0) hr
    (fun δ hδ => (hrat δ).2 hδ) _ hι γ hγ (tsupport Φ) C hC hKC
  obtain ⟨A, hA⟩ := hΦ.bounded_above_of_compact_support hK
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := A)) key)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun s => ?_
  by_cases hs : h⁻¹ • ratTup (F := F) (AF F) s.1 ∈ tsupport Φ
  · rw [Set.indicator_of_mem hs, Pi.one_apply, mul_one, ← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hA _)
  · simp [image_eq_zero_of_notMem_tsupport hs]

end GlobalTheory.OrbitSumInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianOrbitSumFixedLengthLtTopStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hermitian_orbit_sum_fixed_length_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (β : F), β ≠ 0 → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), μ.IsHaarMeasure → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → ∫⁻ h in 𝓕, ∑' x : {x : Fin 1 → Fin M → E | hE σ J (x 0) (x 0) = algebraMap F E β}, ‖Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))‖ₑ ∂μ < ⊤ := by
  first | exact @GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | exact GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top | (intros; apply GlobalTheory.OrbitSumInt.lintegral_orbitSum_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeRatioEqSignatureIndex
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open GlobalTheory.RowLev GlobalTheory.RowLev.Inhab IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

namespace GlobalTheory.RowIndex

variable {I : AutInst}

theorem mem_mL {m : ℕ} {x : VA I} : x ∈ mL I m ↔ ∃ z ∈ I.Lf, x = (m : I.E ⊗[I.F] Af I.F) • z := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
  | smul a x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨a • z, Submodule.smul_mem _ a hz, smul_comm (a : I.E ⊗[I.F] Af I.F) _ z⟩


end GlobalTheory.RowIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

variable {k r : ℕ}

def rep (L : LocBessel k r) : BranchingSupport.Rep k r := ⟨L.Hs, L.σ⟩

def BeTK (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) : Prop :=
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def SmCW (L : LocBessel k r) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : L.Hs → V) : Prop :=
  (∀ v ∈ (rep L).sm, ∀ w ∈ (rep L).sm, l (v + w) = l v + l w) ∧ (∀ (a : ℂ), ∀ v ∈ (rep L).sm, l (a • v) = a • l v) ∧
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) L.σ l

def OneAt (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : Prop :=
  ∃ A : L.Wq →L[ℂ] L.Wp, ∀ F s, IsCoef (rep L) l l' F s → OrbInt L F g ν = s • A

theorem J_eq_orbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.J F g = OrbInt L F g (pairMeas L) := rfl

end GlobalTheory.AmpTK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRows
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRows
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.EvalBound

theorem tens_mem_VP (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hB : IsDSData B d) :
    B.tens B.w ∈ VP B 0 :=
  (tens_w_mem B hB 0).1

noncomputable def realRep (B : RowsAut) : B.I.Ginf →* (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) where
  toFun x := B.R (x, 1)
  map_one' := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).1
  map_mul' x y := by
    rw [← (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.1, Prod.mk_mul_mk, mul_one]

theorem exists_contRep_bound : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  intro hSL B d hB hn hg
  obtain ⟨hU, -, -, hw1, -⟩ := GlobalTheory.Dec.tensorRep B d hB
  obtain ⟨F, hF, hFc, hFeq⟩ :=
    GlobalTheory.StepAverage.exists_smooth_average hSL B d hB 0 _ (tens_mem_VP B d hB)
  set a : B.I.Ginf → ℂ := fun g => F (fun v i j => uMat (g v) i j) with ha
  have hemb := GlobalTheory.StepAverage.isClosedEmbedding_entries_inf B.I
  have hac : Continuous a := hF.continuous.comp hemb.continuous
  have haS : HasCompactSupport a := hFc.comp_isClosedEmbedding hemb
  have hsm : SmoothInf B.I a := fun x =>
    ⟨F, hF.contDiffAt, Filter.Eventually.of_forall fun _ => rfl⟩
  have hvi : Integrable (fun g => a g • B.σs g (B.tens B.w)) (muInf B.I) := by
    by_contra hni
    have h0 : B.tens B.w = 0 := by rw [hFeq]; exact integral_undef hni
    rw [h0, norm_zero] at hw1
    exact zero_ne_one hw1
  have hai : Integrable a (muInf B.I) := by
    refine hvi.norm.mono' hac.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hU.2.2.1, hw1, mul_one]
  obtain ⟨C, hC⟩ := GlobalTheory.T.convolutionSmoothL2_of_def B B.g hn hg a hsm haS
  refine ⟨C, fun A hA hK => ?_⟩
  have hRU := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.absOpInt B.I.Ginf (muInf B.I) (B.I.L2 B.μf B.fund) (realRep B)
    (fun g x => hRU.2.2.1 (g, 1) x)
    (fun x => (hRU.2.2.2.1 x).comp (continuous_id.prodMk continuous_const)) a hai
  have hA' : ∀ g, A.comp (B.σs g) = (B.R (g, 1)).comp A := hA
  have hPy : P (A (B.tens B.w)) = A (B.tens B.w) := by
    rw [hP1]
    symm
    calc A (B.tens B.w) = A (∫ g, a g • B.σs g (B.tens B.w) ∂(muInf B.I)) := congrArg A hFeq
      _ = ∫ g, A (a g • B.σs g (B.tens B.w)) ∂(muInf B.I) := (A.integral_comp_comm hvi).symm
      _ = ∫ g, a g • realRep B g (A (B.tens B.w)) ∂(muInf B.I) := by
        congr 1
        funext g
        rw [map_smul]
        congr 1
        exact congrArg (fun T => T (B.tens B.w)) (hA' g)
  obtain ⟨f, hsmg, hfc, hfb, hfae⟩ := hC (A (B.tens B.w)) hK P ⟨hai, fun x y => hP2 x y⟩
  refine ⟨f, ?_, hfb⟩
  rw [hPy] at hfae
  unfold IsSmoothMG at hsmg
  unfold IsContRep
  exact ⟨hfc, hsmg.1, hfae⟩

end GlobalTheory.EvalBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepBoundedEvaluationRowsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows : GlobalTheory.DSId.StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  first | exact @GlobalTheory.EvalBound.exists_contRep_bound | exact GlobalTheory.EvalBound.exists_contRep_bound | (intros; apply GlobalTheory.EvalBound.exists_contRep_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcExistsAll
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem hcExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), HcExists D F := by
  intro D F X u wt ιA h0 hW hA c
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u wt ιA hW hA (GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X ιA hA)
  exact ⟨Φ.symm ((F u).cls0.y c * h0⁻¹), (hΦ _ _).2 (Φ.apply_symm_apply _)⟩

end GlobalTheory.St.G
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffBlockEntriesBoundedNormalFormPairOfFlags
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffBlockEntriesBoundedNormalFormPairOfFlags
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NfOff

lemma exists_blockEnd {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

lemma minor_ne_zero {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

lemma Zr_mul_uEmb {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

lemma N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

theorem offBlock_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dite_eq_left hcb, dite_eq_left hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S z (nSubgroup k r).1) _ (N_sub_S z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end GlobalTheory.Amp.NfOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OffBlockEntriesBoundedNormalFormPairOfFlagsStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offBlock_entries_bounded_normalForm_pairOfFlags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  first | exact @GlobalTheory.Amp.NfOff.offBlock_le | exact GlobalTheory.Amp.NfOff.offBlock_le | (intros; apply GlobalTheory.Amp.NfOff.offBlock_le <;> assumption)
end
end
